/*
 * DwBranchNonant.cpp
 *
 *  Created on: May 2, 2018
 *      Author: Kibaek Kim
 */

// #define DSP_DEBUG
#include "Solver/DantzigWolfe/DwBranchNonant.h"

DwBranchNonant::DwBranchNonant(DwModel* model) : DwBranch(model) {
	DecSolver* solver = model_->getSolver();
	master_ = dynamic_cast<DwMaster*>(solver);
	if (solver->getModelPtr()->isStochastic())
		tss_ = dynamic_cast<TssModel*>(solver->getModelPtr());
	DSPdebugMessage("Created DwBranchNonant\n");
}

bool DwBranchNonant::chooseBranchingObjects(
		std::vector<DspBranchObj*>& branchingObjs /**< [out] branching objects */) {

	if (tss_ == NULL) return false;

	int findPhase = 0;
	double maxdev = 0.0;
	bool branched = false;
	int branchingIndex = -1;
	double branchingValue, branchingDownValue, branchingUpValue;

	std::vector<double> refsol; // reference solution
	std::vector<double> devsol; // devations from the refsol
	std::vector<std::vector<double>> densesol; // dense solution vector

	DspBranchObj* branchingUp = NULL;
	DspBranchObj* branchingDn = NULL;

	BGN_TRY_CATCH

	/** retreive message object */
	DspMessage* message = model_->getSolver()->getMessagePtr();

	/** calculate reference solution */
	getRefSol(refsol);

	/** calculate variances from the reference solution */
	getDevSol(refsol, devsol);

#ifdef DSP_DEBUG
	printf("Reference Solution:\n");
	DspMessage::printArray(refsol.size(), &refsol[0]);
	printf("Deviations:\n");
	DspMessage::printArray(devsol.size(), &devsol[0]);
#endif

	findPhase = model_->getParPtr()->getBoolParam("DW/BRANCH/INTEGER_FIRST") ? 0 : 1;
	while (findPhase < 2 && branchingIndex < 0) {
		/** most fractional value */
		for (int j = 0; j < tss_->getNumCols(0); ++j) {
			if (findPhase == 0 && master_->ctype_orig_[j] == 'C')
				break;
			if (devsol[j] > CoinMax(epsilon_, maxdev)) {
				maxdev = devsol[j];
				branchingIndex = j;
				branchingValue = refsol[j];
				if (tss_->getCtypeCore(0)[j] == 'C') {
					branchingDownValue = refsol[j] - epsilonBB_;
					branchingUpValue = refsol[j] + epsilonBB_;
				} else {
					branchingDownValue = floor(refsol[j]);
					branchingUpValue = ceil(refsol[j]);
				}
			}
		}
		findPhase++;
	}
	DSPdebugMessage("maxdev %e\n", maxdev);

	if (branchingIndex > -1) {

		branched = true;

		message->print(2, "Creating branch objects on column %d (value %e, maxdev %e): [%e,%e] and [%e,%e]\n", 
			branchingIndex, branchingValue, maxdev, master_->clbd_node_[branchingIndex], branchingDownValue, branchingUpValue, master_->cubd_node_[branchingIndex]);

		/** creating branching objects */
		branchingUp = new DspBranchObj();
		branchingDn = new DspBranchObj();
		for (int j = 0; j < tss_->getNumCols(0) * tss_->getNumScenarios(); ++j) {
			if (branchingIndex == j % tss_->getNumCols(0)) {
				branchingUp->push_back(j, CoinMin(branchingUpValue, master_->cubd_node_[j]), master_->cubd_node_[j]);
				branchingDn->push_back(j, master_->clbd_node_[j], CoinMax(master_->clbd_node_[j], branchingDownValue));
			} else if (master_->clbd_node_[j] > master_->clbd_orig_[j] || master_->cubd_node_[j] < master_->cubd_orig_[j]) {
				/** store any bound changes made in parent nodes */
				//DSPdebugMessage("Adjusting bound change on column %d: [%e,%e]\n", j, master_->clbd_node_[j], master_->cubd_node_[j]);
				branchingUp->push_back(j, master_->clbd_node_[j], master_->cubd_node_[j]);
				branchingDn->push_back(j, master_->clbd_node_[j], master_->cubd_node_[j]);
			}
		}

		/** set best dual bounds */
		branchingUp->bestBound_ = master_->getBestDualObjective();
		branchingDn->bestBound_ = master_->getBestDualObjective();

		/** assign best dual solutions */
		branchingUp->dualsol_.assign(master_->getBestDualSolution(), master_->getBestDualSolution() + master_->nrows_);
		branchingDn->dualsol_.assign(master_->getBestDualSolution(), master_->getBestDualSolution() + master_->nrows_);

		/** set branching directions */
		branchingUp->direction_ = 1;
		branchingDn->direction_ = -1;

		branchingUp->solEstimate_ = maxdev;
		branchingDn->solEstimate_ = maxdev;

		/** add branching objects */
		if (branchingUpValue <= master_->cubd_node_[branchingIndex])
			branchingObjs.push_back(branchingUp);
		else
			FREE_PTR(branchingUp);
		if (master_->clbd_node_[branchingIndex] <= branchingDownValue)
			branchingObjs.push_back(branchingDn);
		else
			FREE_PTR(branchingDn);
	} else {
		DSPdebugMessage("No branch object is found.\n");
	}

	END_TRY_CATCH_RTN(;,false)

	return branched;
}

void DwBranchNonant::getRefSol(std::vector<double>& refsol) {
	refsol.resize(tss_->getNumCols(0), 0.0);
	for (int j = 0; j < tss_->getNumCols(0) * tss_->getNumScenarios(); ++j) {
		int s = j / tss_->getNumCols(0);
		refsol[j % tss_->getNumCols(0)] += model_->getPrimalSolution()[j] * tss_->getProbability()[s];
	}
}

void DwBranchNonant::getDevSol(std::vector<double>& refsol, std::vector<double>& devsol) {
	devsol.resize(tss_->getNumCols(0), 0.0);
//#define USE_TWONORM
#ifdef USE_TWONORM
	std::vector<double> diffsol(tss_->getNumCols(0), 0.0);
	/** use l2-norm */
	for (int j = 0; j < tss_->getNumCols(0) * tss_->getNumScenarios(); ++j) {
		int k = j % tss_->getNumCols(0);
		diffsol[k] += pow((*sol)[j] - refsol[k], 2.0) * tss_->getProbability()[s];
	}
	for (int k = 0; k < tss_->getNumCols(0); ++k)
		devsol[k] = diffsol[k] > 1.0e-10 ? sqrt(diffsol[k]) : 0.0;
#else
	std::vector<double> maxsol(tss_->getNumCols(0), -COIN_DBL_MAX);
	std::vector<double> minsol(tss_->getNumCols(0), +COIN_DBL_MAX);
	/** calculate max value first */
	for (int j = 0; j < tss_->getNumCols(0) * tss_->getNumScenarios(); ++j) {
		int k = j % tss_->getNumCols(0);
		maxsol[k] = CoinMax(maxsol[k], model_->getPrimalSolution()[j]);
		minsol[k] = CoinMin(minsol[k], model_->getPrimalSolution()[j]);
	}
	for (int k = 0; k < tss_->getNumCols(0); ++k) {
		DSPdebugMessage("k %d maxsol %e minsol %e\n", k, maxsol[k], minsol[k]);
		devsol[k] = CoinMax(maxsol[k] - minsol[k], 0.0);
	}
#endif
}

#undef USE_TWONORM
