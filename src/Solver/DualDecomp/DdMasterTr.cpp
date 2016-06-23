/*
 * DdMasterTr.cpp
 *
 *  Created on: Feb 12, 2016
 *      Author: kibaekkim
 */

/** COIN */
#include "CoinWarmStartBasis.hpp"

/** DSP */
#include "Solver/DualDecomp/DdMasterTr.h"
#include "SolverInterface/SolverInterfaceClp.h"
#include "SolverInterface/SolverInterfaceOoqp.h"
#include "SolverInterface/OoqpEps.h"

DdMasterTr::DdMasterTr(DspParams * par, DecModel * model, StoMessage * message, int nworkers, int maxnumsubprobs):
	DdMaster(par, model, message, nworkers, maxnumsubprobs),
	nthetas_(0), nlambdas_(0),
	stability_param_(0.0), stability_center_(NULL), trcnt_(0), numIters_(0),
	cputime_elapsed_(0.0), walltime_elapsed_(0.0), isSolved_(false),
	cuts_(NULL), ncuts_minor_(0), cutdel_param_(0.5),
	parTr_(true), parTrSize_(0.0), parTrDecrease_(true), parNumCutsPerIter_(1), parMasterAlgo_(IPM_Feasible), parLogLevel_(0) {}

DdMasterTr::~DdMasterTr()
{
	FREE_ARRAY_PTR(stability_center_);
	FREE_PTR(cuts_);
}

/** initialize */
STO_RTN_CODE DdMasterTr::init()
{
	BGN_TRY_CATCH

	DdMaster::init();

	/** read parameters */
	parTr_ = par_->getBoolParam("DD/TR");
	parTrSize_ = par_->getDblParam("DD/TR/SIZE");
	parTrDecrease_ = par_->getBoolParam("DD/TR/DECREASE");
	parNumCutsPerIter_ = par_->getIntParam("DD/NUM_CUTS_PER_ITER");
	parMasterAlgo_ = par_->getIntParam("DD/MASTER_ALGO");
	parLogLevel_ = par_->getIntParam("LOG_LEVEL");

	/** create problem */
	createProblem();

	/** clock */
	cputime_elapsed_  = CoinCpuTime();
	walltime_elapsed_ = CoinGetTimeOfDay();

	END_TRY_CATCH_RTN(;,STO_RTN_ERR)

	return STO_RTN_OK;
}

STO_RTN_CODE DdMasterTr::solve()
{
	BGN_TRY_CATCH

	double cputime  = CoinCpuTime();
	double walltime = CoinGetTimeOfDay();

	/** solve */
	si_->solve();

	/** mark as solved */
	isSolved_ = true;

	/** solver status */
	switch(si_->getStatus())
	{
	case STO_STAT_OPTIMAL:
	case STO_STAT_LIM_ITERorTIME:
	case STO_STAT_STOPPED_GAP:
	case STO_STAT_STOPPED_NODE:
	case STO_STAT_STOPPED_TIME:
	{
		/** get solution */
		CoinCopyN(si_->getSolution(), si_->getNumCols(), primsol_);
		primobj_ = si_->getPrimalBound();

		/** update statistics */
		s_statuses_.push_back(si_->getStatus());
		s_primobjs_.push_back(si_->getPrimalBound());
		s_dualobjs_.push_back(si_->getDualBound());
		double * s_primsol = new double [si_->getNumCols()];
		CoinCopyN(si_->getSolution(), si_->getNumCols(), s_primsol);
		s_primsols_.push_back(s_primsol);
		s_primsol = NULL;
		s_cputimes_.push_back(CoinCpuTime() - cputime);
		s_walltimes_.push_back(CoinGetTimeOfDay() - walltime);

		break;
	}
	default:
		status_ = STO_STAT_MW_STOP;
		message_->print(0, "Warning: master solution status is %d\n", si_->getStatus());
		break;
	}

	END_TRY_CATCH_RTN(;,STO_RTN_ERR)

	return STO_RTN_OK;
}

STO_RTN_CODE DdMasterTr::createProblem()
{
#define FREE_MEMORY        \
	FREE_ARRAY_PTR(ctype); \
	FREE_ARRAY_PTR(clbd);  \
	FREE_ARRAY_PTR(cubd);  \
	FREE_ARRAY_PTR(obj);   \
	FREE_ARRAY_PTR(rlbd);  \
	FREE_ARRAY_PTR(rubd);  \
	FREE_ARRAY_PTR(bgn);   \
	FREE_ARRAY_PTR(len);   \
	FREE_ARRAY_PTR(ind);   \
	FREE_ARRAY_PTR(elem);  \
	FREE_PTR(mat);

	int i, pos;
	int ncols, nrows, nzcnt;
	char * ctype = NULL;
	double * clbd = NULL;
	double * cubd = NULL;
	double * obj  = NULL;
	double * rlbd = NULL;
	double * rubd = NULL;
	CoinBigIndex * bgn = NULL;
	int * len = NULL;
	int * ind = NULL;
	double * elem = NULL;
	CoinPackedMatrix * mat = NULL;

	BGN_TRY_CATCH

	nthetas_  = model_->getNumSubproblems();//CoinMin(model_->getNumSubproblems(), parNumCutsPerIter_);
	nlambdas_ = model_->getNumCouplingRows();

	/** LP dimension */
	if (model_->nonanticipativity())
	{
		nrows = model_->getNumSubproblemCouplingCols(0); /** initial normalization constraint for nonanticipativity constraints */
		nzcnt = nrows * model_->getNumSubproblems();
	}
	else
	{
		nrows = 0;
		nzcnt = 0;
	}
	ncols = nthetas_ + nlambdas_;
	message_->print(999, "nrows %d ncols %d nzcnt %d nthetas_ %d nlambdas_ %d\n", nrows, ncols, nzcnt, nthetas_, nlambdas_);

	/** allocate memory */
	ctype = new char [ncols];
	clbd  = new double[ncols];
	cubd  = new double[ncols];
	obj   = new double[ncols];
	rlbd  = new double[nrows];
	rubd  = new double[nrows];
	bgn   = new CoinBigIndex[nrows + 1];
	len   = new int[nrows];
	ind   = new int[nzcnt];
	elem  = new double[nzcnt];

	/** all continuous variables */
	CoinFillN(ctype, ncols, 'C');

	/** c */
	CoinFillN(obj, nthetas_, 1.0);
	CoinZeroN(obj + nthetas_, nlambdas_);

	/** trust region */
	stability_param_ = parTr_ ? parTrSize_ : COIN_DBL_MAX;
	if (parTr_)
	{
		stability_center_ = new double [nlambdas_];
		CoinZeroN(stability_center_, nlambdas_);
	}

	/** bounds */
	CoinFillN(clbd, nthetas_, -COIN_DBL_MAX);
	CoinFillN(cubd, nthetas_, +COIN_DBL_MAX);

	/** trust region bound */
	CoinFillN(clbd + nthetas_, nlambdas_, -stability_param_);
	CoinFillN(cubd + nthetas_, nlambdas_, +stability_param_);

	/** nonnegative or nonpositive multipliers according to sense */
	for (i = 0; i < nlambdas_; i++)
	{
		if (model_->getSenseCouplingRow(i) == 'L')
			clbd[nthetas_ + i] = 0;
		else if (model_->getSenseCouplingRow(i) == 'G')
			cubd[nthetas_ + i] = 0;
	}

	if (model_->nonanticipativity())
	{
		/** row bounds */
		CoinZeroN(rlbd, nrows);
		CoinZeroN(rubd, nrows);

		/** for constraints */
		pos = 0;
		for (i = 0; i < nrows; ++i)
		{
			bgn[i] = pos;
			for (int j = 0; j < model_->getNumSubproblems(); ++j)
			{
				ind[pos] = nthetas_ + j * nrows + i;
				elem[pos] = 1.0;
				pos++;
			}
			len[i] = pos - bgn[i];
		}
		bgn[nrows] = pos;
		assert(pos == nzcnt);
	}

	/** constraint matrix */
	mat = new CoinPackedMatrix(false, ncols, nrows, nzcnt, elem, ind, bgn, len);
	//mat->verifyMtx(4);

	/** create solver interface */
	switch (parMasterAlgo_)
	{
	case Simplex:
		si_ = new SolverInterfaceClp(par_);
		break;
	case IPM:
		si_ = new SolverInterfaceOoqp(par_);
		break;
	case IPM_Feasible:
		si_ = new OoqpEps(par_);
		break;
	default:
		si_ = new OoqpEps(par_);
		break;
	}

	/** [MAX]imization */
	si_->setObjSense(-1);

	/** copy problem data */
	si_->loadProblem(mat, clbd, cubd, obj, ctype, rlbd, rubd);

	/** allocate memory for solution */
	primsol_ = new double [ncols];
	CoinFillN(primsol_, nthetas_, COIN_DBL_MAX);
	CoinZeroN(primsol_ + nthetas_, nlambdas_);

	/** initialize cut pool */
	cuts_ = new OsiCuts;

	/** set print level */
	si_->setPrintLevel(CoinMax(0, parLogLevel_ - 2));

	END_TRY_CATCH_RTN(FREE_MEMORY,STO_RTN_ERR)

	FREE_MEMORY;

	return STO_RTN_OK;
#undef FREE_MEMORY
}

STO_RTN_CODE DdMasterTr::updateProblem()
{
	BGN_TRY_CATCH

	int nCutsAdded = 0;
	double curprimobj = si_->getPrimalBound(); /** current primal objective value */

	/** calculate primal/dual objectives */
	double newprimal = 0.0;
	double newdual = 0.0;
	for (int s = 0; s < model_->getNumSubproblems(); ++s)
	{
		newprimal += subprimobj_[s];
		newdual += subdualobj_[s];
	}

	/** add cuts and re-optimize */
	nCutsAdded = addCuts();

	/** update trust region FIRST, because this does not change problem. */
	if (parTr_)
	{
		if (newdual >= bestdualobj_ + 1.0e-4 * (curprimobj - bestdualobj_))
		{
			message_->print(2, "  -> %s STEP: dual objective %e", isSolved_ ? "SERIOUS" : "INITIAL", newdual);

			/** reset minor cut counter */
			ncuts_minor_ = nCutsAdded;

			/** mark cuts not to be deleted */
			for (int i = cuts_->sizeCuts() - nCutsAdded; i < cuts_->sizeCuts(); ++i)
				possiblyDelete_[i] = false;

			if (isSolved_)
			{
				/** update proximal point */
				CoinCopyN(primsol_ + nthetas_, nlambdas_, stability_center_);
				message_->print(2, ", updated proximal point");

				/** possibly delete cuts */
				possiblyDeleteCuts(newprimal);

				/** is solution boundary? */
				if (isSolutionBoundary() &&
					/*primalBound - dual_bound < 0 ||*/
					newdual >= bestdualobj_ + 0.5 * (curprimobj - bestdualobj_))
				{
					/** increase trust region */
					stability_param_ = CoinMin(2. * stability_param_, 1.0e+4);
					message_->print(2, ", increased trust region size %e", stability_param_);
				}

				/** set trust region */
				setTrustRegion(stability_param_, stability_center_);
			}

			/** update dual bound */
			bestdualobj_ = newdual;
			trcnt_ = 0;
		}
		else
		{
			/** increase minor cut counter */
			ncuts_minor_ += nCutsAdded;

			/** null step */
			message_->print(1, "  -> null step: dual objective %e", newdual);

			if (curprimobj < bestdualobj_)
			{
				/** increase trust region */
				stability_param_ = CoinMin(2. * stability_param_, 1.0e+4);
				message_->print(1, ", increased trust region size %e", stability_param_);
				/** set trust region */
				setTrustRegion(stability_param_, stability_center_);
			}
			else if (parTrDecrease_)
			{
				/** The following rule is from Linderoth and Wright (2003) */
				double rho = CoinMin(1.0, stability_param_) * (bestdualobj_ - newdual) / (curprimobj - bestdualobj_);
				if (rho > 0) trcnt_++;
				if (rho >= 3 || (trcnt_ >= 3 && fabs(rho - 2.) < 1.0))
				{
					/** decrease trust region */
					stability_param_ *= 1.0 / CoinMin(rho, 4.);
					message_->print(1, ", decreased trust region size %e", stability_param_);
					trcnt_ = 0;

					/** set trust region */
					setTrustRegion(stability_param_, stability_center_);
				}
			}
		}
	}
	else
	{
		message_->print(1, "  dual objective %e", newdual);
		if (newdual >= bestdualobj_ + 1.0e-4 * (curprimobj - bestdualobj_))
			/** update dual bound */
			bestdualobj_ = newdual;
	}

	message_->print(1, ", master has %d rows and %d cols after adding %d cuts.",
				si_->getNumRows(), si_->getNumCols(), nCutsAdded);

	OoqpEps * ooqp = dynamic_cast<OoqpEps*>(si_);
	if (ooqp)
	{
		if (ooqp->hasOoqpStatus_ && isSolved_)
		{
			double epsilon = (si_->getPrimalBound() - newprimal + ooqp->getDualityGap()) / (1. + fabs(si_->getPrimalBound()));
			if (epsilon > 1.) epsilon = 1.;
			ooqp->setOoqpStatus(epsilon, -bestprimobj_, -bestdualobj_);
		}
	}

	message_->print(1, "\n");

	END_TRY_CATCH_RTN(;,STO_RTN_ERR)

	return STO_RTN_OK;
}

/** solver status */
STO_RTN_CODE DdMasterTr::getStatus()
{
	BGN_TRY_CATCH

	double time_elapsed = CoinGetTimeOfDay() - walltime_elapsed_;
	message_->print(1, "Iteration %3d: Dual Bound %e", numIters_++, bestdualobj_);

	message_->print(1, " Time Elapsed %.2f sec\n", time_elapsed);

	double absgap = primobj_ - bestdualobj_;
	double relgap = absgap / (1.e-10 + fabs(primobj_));
	bool terminate = (absgap > -1.0e-6 && relgap < par_->getDblParam("DD/STOP_TOL"));
	status_ = terminate ? STO_STAT_MW_STOP : STO_STAT_MW_CONTINUE;

	END_TRY_CATCH_RTN(;,STO_RTN_ERR)

	return status_;
}

/** is solution trust region boundary? */
bool DdMasterTr::isSolutionBoundary(double eps)
{
	double maxdiff = 0.0;
	double mindiff = COIN_DBL_MAX;

	BGN_TRY_CATCH

	const double * sol = primsol_;
	const double * clbd = si_->getColLower();
	const double * cubd = si_->getColUpper();
	int ncols = si_->getNumCols();

	for (int j = nthetas_; j < ncols; ++j)
	{
		double diff = CoinMin(cubd[j] - sol[j], sol[j] - clbd[j]);
		if (diff > maxdiff)
			maxdiff = diff;
		if (diff < mindiff)
			mindiff = diff;
	}

	END_TRY_CATCH(;)

	return fabs(maxdiff) < eps;
}

/** add cuts */
int DdMasterTr::addCuts(
		bool possiblyDel /**< possibly delete cuts*/)
{
#define FREE_MEMORY \
	FREE_2D_ARRAY_PTR(nthetas_, aggvec); \
	FREE_ARRAY_PTR(aggrhs);

	OsiCuts cuts;
	double ** aggvec = NULL;
	double *  aggrhs = NULL;
	CoinPackedVector cutvec; /**< cut body */
	double cutrhs;           /**< cut RHS */
	int nCutsAdded; /**< number of cuts added */

	BGN_TRY_CATCH

	/** allocate memory for dense cut */
	aggvec = new double * [nthetas_];
	aggrhs = new double [nthetas_];
	for (int i = 0; i < nthetas_; ++i)
	{
		aggvec[i] = new double [nthetas_ + nlambdas_];
		CoinZeroN(aggvec[i], nthetas_ + nlambdas_);
		aggrhs[i] = 0.0;
	}

	/** add row cuts by looping over each scenario */
	for (int s = 0; s < nsubprobs_; ++s)
	{
		assert(fabs(subprimobj_[s]) < 1.0e+20);

		/** cut index */
		int cutidx = s % nthetas_;

		/** construct cut */
 		aggrhs[cutidx] += subprimobj_[s];
		for (int i = 0; i < nlambdas_; i++)
		{
			/** evaluate solution on coupling constraints (if they are Hx = d, this is (Hx - d)_i) */
			double hx_d = model_->evalLhsCouplingRowSubprob(i, s, subsolution_[s]) - model_->getRhsCouplingRow(i);
			aggvec[cutidx][nthetas_ + i] -= hx_d; /** coefficients for lambda */
			if (isSolved_)
				aggrhs[cutidx] -= hx_d * primsol_[nthetas_ + i];
		}
	}

	for (int s = 0; s < nthetas_; ++s)
	{
		/** construct cut */
		cutvec.clear();

		/** set it as sparse */
		aggvec[s][s] = 1.0;
		for (int j = 0; j < nthetas_ + nlambdas_; ++j)
		{
			if (fabs(aggvec[s][j]) > 1E-10)
				cutvec.insert(j, aggvec[s][j]);
		}

		/** cut rhs */
		cutrhs = aggrhs[s];
		if (fabs(cutrhs) < 1E-10)
			cutrhs = 0.0;

		OsiRowCut * rc = new OsiRowCut;
		rc->setRow(cutvec);
		rc->setLb(-COIN_DBL_MAX);
		rc->setUb(cutrhs);
		rc->setEffectiveness(rc->violated(primsol_));

		if (rc->effectiveness() > 1.0e-6)
		{
			/** number of cuts before adding cut */
			int nCutsBefore = cuts_->sizeCuts();

			/** add cut if not duplicate */
			cuts_->insertIfNotDuplicate(*rc);

			if (nCutsBefore < cuts_->sizeCuts())
			{
				/** insertIfNotDuplicate does not set effectiveness */
				cuts_->rowCutPtr(nCutsBefore)->setEffectiveness(rc->effectiveness());
				cuts_age_.push_back(0);
				possiblyDelete_.push_back(possiblyDel);
				masterobjsAtCutAdd_.push_back(si_->getPrimalBound());
				cuts.insert(rc);
			}
		}
		else
			FREE_PTR(rc);
	}

	nCutsAdded = cuts.sizeCuts();
	if (nCutsAdded > 0)
		/** apply cuts */
		si_->addCuts(cuts);
	else
		/** recruit back some cuts if no cut is generated */
		recruiteCuts();

	END_TRY_CATCH(;)

	FREE_MEMORY

	return nCutsAdded;
#undef FREE_MEMORY
}

/** possibly delete cuts */
STO_RTN_CODE DdMasterTr::possiblyDeleteCuts(
		double subobjval /**< sum of subproblem objective values */)
{
	OsiCuts cuts;
	int nrows = model_->nonanticipativity() ? model_->getNumSubproblemCouplingCols(0) : 0;
	int ncuts = si_->getNumRows() - nrows;
	if (ncuts == 0)
		return STO_RTN_OK;

	BGN_TRY_CATCH

	SolverInterfaceOsi * osi = dynamic_cast<SolverInterfaceOsi*>(si_);
	SolverInterfaceOoqp * ooqp = dynamic_cast<SolverInterfaceOoqp*>(si_);
	if (osi)
	{
		const double * pi = osi->getOSI()->getRowPrice() + nrows;

		/** mark cuts that should not be deleted */
		for (int i = 0, i2 = 0; i < cuts_->sizeCuts(); ++i)
		{
			/** do not consider inactive cuts */
			if (cuts_age_[i] < 0) continue;

			/** consider only old cuts */
			if (cuts_age_[i] < 100)
			{
				possiblyDelete_[i] = false;
				continue;
			}

			/** aging cuts with (almost) zero Lagrangian multiplier values */
			if (fabs(pi[i2]) < 1.0e-10)
				possiblyDelete_[i] = false;
			/** do not delete cuts generated at minor iterations such that the following condition holds. */
			else if (i >= cuts_->sizeCuts() - ncuts_minor_ &&
					(si_->getPrimalBound() - subobjval) > cutdel_param_ * (masterobjsAtCutAdd_[i] - subobjval))
				possiblyDelete_[i] = false;

			i2++;
		}
	}
	else if (ooqp)
	{
		const double * lambda = ooqp->lambda();
		const double * pi = ooqp->pi();

		/** mark cuts that should not be deleted */
		int numPis = ooqp->getNumPis();
		int numLambdas = ooqp->getNumLambdas();
		for (int i = cuts_->sizeCuts() - 1; i >= 0; --i)
		{
			/** do not consider inactive cuts */
			if (cuts_age_[i] < 0) continue;

			/** consider only old cuts */
			if (cuts_age_[i] < 100)
			{
				possiblyDelete_[i] = false;
				continue;
			}

			OsiRowCut * rc = cuts_->rowCutPtr(i);
			assert(rc);
			if (rc->sense() == 'G')
			{
				numLambdas--;
				if (fabs(lambda[numLambdas]) < 1.0e-10)
					possiblyDelete_[i] = false;
				/** do not delete cuts generated at minor iterations such that the following condition holds. */
				else if (i >= cuts_->sizeCuts() - ncuts_minor_ &&
						(si_->getPrimalBound() - subobjval) > cutdel_param_ * (masterobjsAtCutAdd_[i] - subobjval))
					possiblyDelete_[i] = false;
			}
			else if (rc->sense() == 'L')
			{
				numPis--;
				if (fabs(pi[numPis]) < 1.0e-10)
					possiblyDelete_[i] = false;
				/** do not delete cuts generated at minor iterations such that the following condition holds. */
				else if (i >= cuts_->sizeCuts() - ncuts_minor_ &&
						(si_->getPrimalBound() - subobjval) > cutdel_param_ * (masterobjsAtCutAdd_[i] - subobjval))
					possiblyDelete_[i] = false;
			}
		}
	}

	/** get basis information */
	CoinWarmStartBasis * ws = NULL;
	if (osi) ws = dynamic_cast<CoinWarmStartBasis*>(osi->getWarmStart()->clone());

	vector<char> aStat; /**< status of artificial variables */

	/** mark as deleted; and construct temporary cut pool to be added */
	for (int i = 0, i2 = nrows; i < cuts_->sizeCuts(); ++i)
	{
		/** do not consider inactive cuts */
		if (cuts_age_[i] < 0) continue;

		if (possiblyDelete_[i])
			cuts_age_[i] = -1;
		else
		{
			OsiRowCut * rc = cuts_->rowCutPtr(i);
			if (rc)
			{
				rc->setEffectiveness(1.0);
				cuts.insert(*rc);
				if (osi)
					aStat.push_back(ws->getArtifStatus(i2));
			}
		}

		i2++;
	}

	/** number of cuts to delete */
	int nCutsToDelete = ncuts - cuts.sizeCuts();

	/** exit if no cut to delete */
	if (nCutsToDelete == 0)
		return STO_RTN_OK;

	/** remove all cuts from solver interface */
	removeAllCuts();

	/** apply cuts */
	si_->addCuts(cuts);

	if (osi)
	{
		/** create new basis */
		CoinWarmStartBasis * basis = new CoinWarmStartBasis(
				ws->getNumStructural(), ws->getNumArtificial(),
				ws->getStructuralStatus(), &aStat[0]);

		osi->setWarmStart(basis);
	}

	END_TRY_CATCH_RTN(;,STO_RTN_ERR)

	return STO_RTN_OK;
}

/** recruite cuts */
int DdMasterTr::recruiteCuts()
{
	int nRecruited = 0;
	OsiCuts cuts;

	CoinWarmStartBasis * ws = NULL;
	SolverInterfaceClp * clp = NULL;

	vector<char> aStat; /**< status of artificial variables */

	BGN_TRY_CATCH

	clp = dynamic_cast<SolverInterfaceClp*>(si_);

	if (clp)
	{
		/** get basis information */
		clp->setWarmStart(clp->getOSI()->getWarmStart());
		ws = dynamic_cast<CoinWarmStartBasis*>(clp->getWarmStart());
	}

	int irow = model_->nonanticipativity() ? model_->getNumSubproblemCouplingCols(0) : 0;
	for (int i = 0; i < cuts_->sizeCuts(); ++i)
	{
		/** retrieve row cut */
		OsiRowCut * rc = cuts_->rowCutPtr(i);
		assert(rc);

		if (cuts_age_[i] >= 0)
		{
			/** add cut */
			cuts.insert(*rc);
			if (clp)
			{
				/** set status of artificial variable */
				aStat.push_back(ws->getArtifStatus(irow++));
			}
		}
		else
		{
			/** set effectiveness */
			rc->setEffectiveness(rc->violated(primsol_));
			if (rc->effectiveness() > 1.0e-6)
			{
				nRecruited++;
				/** add cut */
				cuts.insert(*rc);
				if (clp)
				{
					/** set status of artificial variable */
					aStat.push_back(CoinWarmStartBasis::basic);
				}

				/** other cut info */
				cuts_age_[i] = 0;
				possiblyDelete_[i] = true;
			}
		}
	}

	if (cuts.sizeCuts() > 0)
	{
		/** remove all cuts from solver interface */
		removeAllCuts();

		/** apply cuts */
		si_->addCuts(cuts);

		if (clp)
		{
			/** create new basis */
			CoinWarmStartBasis * basis = new CoinWarmStartBasis(
					ws->getNumStructural(), ws->getNumArtificial(),
					ws->getStructuralStatus(), &aStat[0]);
			clp->setWarmStart(basis);
		}
	}

	END_TRY_CATCH(;)

	return 0;
}

/** remove all cuts */
STO_RTN_CODE DdMasterTr::removeAllCuts()
{
	BGN_TRY_CATCH

	SolverInterfaceClp * clp = dynamic_cast<SolverInterfaceClp*>(si_);
	SolverInterfaceOoqp * ooqp = dynamic_cast<SolverInterfaceOoqp*>(si_);
	if (clp)
	{
		int nrows = model_->nonanticipativity() ? model_->getNumSubproblemCouplingCols(0) : 0;
		int ncuts = si_->getNumRows() - nrows;

		/** row indices to delete */
		int * rowIndices = new int [ncuts];
		CoinIotaN(rowIndices, ncuts, nrows);

		/** delete */
		clp->getOSI()->deleteRows(ncuts, rowIndices);

		/** free memory */
		FREE_ARRAY_PTR(rowIndices);
	}
	else if (ooqp)
	{
		for (int i = 0; i < ooqp->cuts_.sizeCuts(); ++i)
			delete ooqp->cuts_.rowCutPtr(i);
		ooqp->cuts_.dumpCuts();
	}

	END_TRY_CATCH_RTN(;,STO_RTN_ERR)

	return STO_RTN_OK;
}

/** change trust region */
STO_RTN_CODE DdMasterTr::setTrustRegion(double stability_param, double * stability_center)
{
	BGN_TRY_CATCH

	int ncols = si_->getNumCols();
	for (int j = nthetas_; j < ncols; ++j)
	{
		double clbd = stability_center[j - nthetas_] - stability_param;
		double cubd = stability_center[j - nthetas_] + stability_param;
		if (model_->getSenseCouplingRow(j - nthetas_) == 'L')
			clbd = CoinMax((double) 0.0, clbd); /* lambda >= 0 */
		else if (model_->getSenseCouplingRow(j - nthetas_) == 'G')
			cubd = CoinMin((double) 0.0, cubd); /* lambda <= 0 */
		si_->setColBounds(j, clbd, cubd);
	}

	END_TRY_CATCH_RTN(;,STO_RTN_ERR)

	return STO_RTN_OK;
}