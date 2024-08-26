/*
 * DecTssModel.cpp
 *
 *  Created on: Jun 17, 2015
 *      Author: ctjandra
 */

#include "Utility/DspMessage.h"
#include "Model/DecTssModel.h"

DecTssModel::DecTssModel() :
TssModel(),
master_col_indices_(NULL) {
	/** nothing to do */
}

/** copy constructor */
DecTssModel::DecTssModel(const DecTssModel & rhs) :
TssModel(rhs),
master_col_indices_(NULL) {
	/** nothing to do */
}

/** copy constructor */
DecTssModel::DecTssModel(const TssModel & rhs) :
TssModel(rhs),
master_col_indices_(NULL) {
	/** nothing to do */
}
DecTssModel::~DecTssModel() {
	FREE_ARRAY_PTR(master_col_indices_);
}

bool DecTssModel::isDistributed()
{
	bool is_distributed = false;
	for (int s = 0; s < nscen_; ++s)
		if (mat_scen_[s] == NULL)
		{
			is_distributed = true;
			break;
		}
	return is_distributed;
}

DSP_RTN_CODE DecTssModel::decompose(
	int size,				/**< [in] size of subproblem subset */
	int *scen,				/**< [in] subset of scenarios */
	int naux,				/**< [in] number of auxiliary columns */
	double *clbd_aux,		/**< [in] lower bounds for auxiliary columns */
	double *cubd_aux,		/**< [in] upper bounds for auxiliary columns */
	double *obj_aux,		/**< [in] objective coefficients for auxiliary columns */
	CoinPackedMatrix *&mat, /**< [out] constraint matrix */
	double *&clbd,			/**< [out] column lower bounds */
	double *&cubd,			/**< [out] column upper bounds */
	char *&ctype,			/**< [out] column types */
	double *&obj,			/**< [out] objective coefficients */
	double *&rlbd,			/**< [out] row lower bounds */
	double *&rubd,			/**< [out] row upper bounds */
	bool adjust_probability)
{
	assert(size >= 0);
	assert(nrows_);
	assert(ncols_);
	assert(naux >= 0);
	assert(mat == NULL);

	int s, i, j;
	int nrows = nrows_[0] + size * nrows_[1];
	int ncols = ncols_[0] + size * ncols_[1] + naux;
	DSPdebugMessage("nrows %d ncols %d\n", nrows, ncols);

	BGN_TRY_CATCH

	for (s = 0; s < size; ++s)
		if (mat_scen_[scen[s]] == NULL)
			throw "Invalid model data (mat_scen_)";

	/** allocate memory */
	clbd = new double [ncols];
	cubd = new double [ncols];
	ctype = new char [ncols];
	obj = new double [ncols];
	rlbd = new double [nrows];
	rubd = new double [nrows];

#ifdef DSP_TIMING
	double stime = CoinCpuTime();
#endif

	vector<int> rowIndices;
	vector<int> colIndices;
	vector<double> elements;
	// int * rowIndices = NULL;
	// int * colIndices = NULL;
	// double * elements = NULL;
	double * denserow = NULL;

	int nzcnt = 0;
	/** # of nonzeros in the first-stage matrix A */
	for (i = 0; i < nrows_[0]; ++i) {
		for (j = 0; j < rows_core_[i]->getNumElements(); ++j) {
			if (fabs(rows_core_[i]->getElements()[j]) > 1.e-10)
				nzcnt++;
		}
	}
	/** # of nonzeros in the technology and recourse matrices */
	for (s = 0; s < size; ++s)
	{
		if (fromSMPS_)
		{
			for (i = nrows_[0]; i < nrows_core_; ++i) {
				nzcnt += rows_core_[i]->getNumElements();
			}
		}
		else
			nzcnt += mat_scen_[scen[s]]->getNumElements();
	}
	DSPdebugMessage("nzcnt %d\n", nzcnt);

	/** allocate memory */
	rowIndices.reserve(nzcnt);
	colIndices.reserve(nzcnt);
	elements.reserve(nzcnt);
	// rowIndices = new int [nzcnt];
	// colIndices = new int [nzcnt];
	// elements = new double [nzcnt];
	if (fromSMPS_)
		denserow = new double [ncols_core_];

	/** construction */
	int pos = 0;
	int rownum = 0;
	for (i = 0; i < nrows_[0]; ++i)
	{
		for (j = 0; j < rows_core_[i]->getNumElements(); ++j) {
			if (fabs(rows_core_[i]->getElements()[j]) > 1.e-10) {
				rowIndices.push_back(rownum);
				colIndices.push_back(rows_core_[i]->getIndices()[j]);
				elements.push_back(rows_core_[i]->getElements()[j]);
				pos++;
			}
		}
		rownum++;
	}
	for (s = 0; s < size; ++s)
	{
		for (i = nrows_[0]; i < nrows_core_; ++i)
		{
			CoinBigIndex start = mat_scen_[scen[s]]->getVectorStarts()[i - nrows_[0]];
			int length = mat_scen_[scen[s]]->getVectorSize(i - nrows_[0]);

			if (fromSMPS_)
			{
				/** create dense row */
				CoinZeroN(denserow, ncols_core_);
				for (int j = 0; j < rows_core_[i]->getNumElements(); ++j)
					denserow[rows_core_[i]->getIndices()[j]] = rows_core_[i]->getElements()[j];
				for (int j = 0; j < length; ++j)
					denserow[mat_scen_[scen[s]]->getIndices()[start + j]] = mat_scen_[scen[s]]->getElements()[start + j];

				/** create sparse row */
				length = 0;
				for (int j = 0; j < ncols_core_; ++j)
				{
					if (fabs(denserow[j]) > 1.e-10)
					{
						rowIndices.push_back(rownum);
						colIndices.push_back(j);
						elements.push_back(denserow[j]);
						length++;
					}
				}
			}
			else /** from Julia */
			{
				for (j = 0; j < length; ++j) {
					rowIndices.push_back(rownum);
					colIndices.push_back(mat_scen_[scen[s]]->getIndices()[start + j]);
					elements.push_back(mat_scen_[scen[s]]->getElements()[start + j]);
				}
			}
			shiftVecIndices(length, &colIndices[0] + pos, s * ncols_[1], cstart_[1]);
			DSPdebugMessage("shift vector indices from %d by %d from %d\n", pos, s * ncols_[1], cstart_[1]);
			/*for (int k = 0, l = 0; l < length; ++l)
			{
				if (fabs(elements[pos+l]) < 1.0e-10) continue;
				if (k > 0 && k % 4 == 0) printf("\n");
				//printf("  [%5d,%4d,%4d] %+e", i, rowIndices[pos+l], mat_scen_[scen[s]]->getIndices()[start+l], mat_scen_[scen[s]]->getElements()[start+l]);
				//printf("  [%5d,%4d,%4d] %+e", i, rowIndices[pos+l], colIndices[pos+l], elements[pos+l]);
				k++;
			}
			printf("\n");*/
			pos += length;
			rownum++;
		}
	}
	nzcnt = rowIndices.size();
	DSPdebugMessage("rownum %d nzcnt %d pos %d\n", rownum, nzcnt, pos);  
	assert(nzcnt == pos);

	mat = new CoinPackedMatrix(false, &rowIndices[0], &colIndices[0], &elements[0], nzcnt);
	mat->setDimensions(nrows, ncols);
	DSPdebug(mat->verifyMtx(4));

	/** free memory */
	rowIndices.clear();
	colIndices.clear();
	elements.clear();
	FREE_ARRAY_PTR(denserow);

#ifdef DSP_TIMING
	printf("construct matrix %f seconds.\n", CoinCpuTime() - stime);
#endif

	/** all the other model data */
	copyCoreColLower(clbd, 0);
	copyCoreColUpper(cubd, 0);
	copyCoreColType(ctype, 0);
	copyCoreObjective(obj, 0);
	copyCoreRowLower(rlbd, 0);
	copyCoreRowUpper(rubd, 0);
	for (s = 0; s < size; ++s)
	{
		int sind = scen[s];

		/** column lower bounds */
		DSPdebugMessage("combining column lower bounds\n");
		copyCoreColLower(clbd + ncols_[0] + s * ncols_[1], 1);
		combineRandColLower(clbd + ncols_[0] + s * ncols_[1], 1, sind);

		/** column upper bounds */
		DSPdebugMessage("combining column upper bounds\n");
		copyCoreColUpper(cubd + ncols_[0] + s * ncols_[1], 1);
		combineRandColUpper(cubd + ncols_[0] + s * ncols_[1], 1, sind);

		/** column types */
		DSPdebugMessage("combining column types\n");
		copyCoreColType(ctype + ncols_[0] + s * ncols_[1], 1);

		/** objective coefficients */
		DSPdebugMessage("combining objective coefficients\n");
		copyCoreObjective(obj + ncols_[0] + s * ncols_[1], 1);
		combineRandObjective(obj + ncols_[0] + s * ncols_[1], 1, sind, adjust_probability);

		/** row lower bounds */
		DSPdebugMessage("combining row lower bounds\n");
		copyCoreRowLower(rlbd + nrows_[0] + s * nrows_[1], 1);
		combineRandRowLower(rlbd + nrows_[0] + s * nrows_[1], 1, sind);

		/** row upper bounds */
		DSPdebugMessage("combining row upper bounds\n");
		copyCoreRowUpper(rubd + nrows_[0] + s * nrows_[1], 1);
		combineRandRowUpper(rubd + nrows_[0] + s * nrows_[1], 1, sind);
	}
	//printf("nrows_core_ = %d, ncols_core_ = %d \n", nrows_core_, ncols_core_);
	/** auxiliary columns */
	CoinCopyN(clbd_aux, naux, clbd + ncols - naux);
	CoinCopyN(cubd_aux, naux, cubd + ncols - naux);
	CoinCopyN(obj_aux, naux, obj + ncols - naux);
	CoinFillN(ctype + ncols - naux, naux, 'C');

	END_TRY_CATCH_RTN(;,DSP_RTN_ERR)

	return DSP_RTN_OK;
}

DSP_RTN_CODE DecTssModel::decomposeCoupling(
	int size,                    /**< [in] size of subproblem subset */
	int * subprobs,              /**< [in] subset of subproblems */
	CoinPackedMatrix *& cpl_mat, /**< [out] coupling constraint matrix */
	int *& cpl_cols,             /**< [out] columns of cpl_mat involved in coupling rows */
	int & cpl_ncols              /**< [out] size of cpl_cols */)
{
	int ncols_first = getNumCols(0);
	int ncols = getNumCols(0) + size * getNumCols(1);

	/** cpl_mat is the identity matrix of size ncols: nonanticipativity is in form x = x_s,
	  * but with x implicitly eliminated, we only have x_s in each row. */
	double * elem = new double [ncols_first];
	int * ind = new int [ncols_first];
	int * start = new int [ncols_first+1];
	int * len = new int [ncols_first];
	for (int i = 0; i < ncols_first; i++)
	{
		ind[i] = i;
		start[i] = i;
		len[i] = 1;
		elem[i] = 1.0;
	}
	start[ncols_first] = ncols_first;
	cpl_mat = new CoinPackedMatrix(false, ncols, ncols_first, ncols_first, elem, ind, start, len);

	/** free memory */
	delete [] elem; elem = NULL;
	delete [] ind; ind = NULL;
	delete [] start; start = NULL;
	delete [] len; len = NULL;

	/** columns involved are the first ncols_first columns */
	cpl_ncols = ncols_first;
	cpl_cols = new int [cpl_ncols];
	for (int i = 0; i < cpl_ncols; i++)
		cpl_cols[i] = i;

	int k = 0;
	for (int s = 0; s < size; s++)
		k += getNumSubproblemCouplingCols(subprobs[s]);
	assert(k == cpl_ncols);

	return DSP_RTN_OK;
}

const int * DecTssModel::getSubproblemCouplingColIndices(int s) {
	if (!master_col_indices_) {
		master_col_indices_ = new int [getNumCols(0)];
		for (int j = 0; j < getNumCols(0); ++j)
			master_col_indices_[j] = j;
	}
	return master_col_indices_;
}

double DecTssModel::evalLhsCouplingRow(int row, double ** solutions)
{
	double val = 0;
	for (int s = 0; s < getNumSubproblems(); s++)
		val += evalLhsCouplingRowSubprob(row, s, solutions[s]);
	return val;
}

double DecTssModel::evalLhsCouplingRowSubprob(int row, int s, double * subprobSolution)
{
	/** recall solution is in the space of the coupling vars. of subproblem,
	 *  while row is from the master problem coupling matrix */
	if (row < s * getNumCols(0) || row >= (s + 1) * getNumCols(0))
		return 0;
	double sol = subprobSolution[row - s * getNumCols(0)];
	if (fabs(sol) <= 1E-10)
		return 0;
	return sol;
}

double DecTssModel::evalLhsCouplingRowAlternative(int row, double ** solutions)
{
	double val = 0;
//	for (int s = 0; s < getNumSubproblems(); s++)
//		if (row + 1 < getNumCols(0))
//			val += solutions[s][row] - solutions[s][row+1];
//		else
//			val += solutions[s][row] - solutions[s][0];
	int s = row / getNumCols(0);
	int i = row % getNumCols(0);
	val = solutions[s][i];
	if (s + 1 < getNumSubproblems())
		val -= solutions[s+1][i];
	else
		val -= solutions[0][i];
	return val;
}

void DecTssModel::convertLagrangianFromAlternative(double * multipliers, double *& newMultipliers)
{
	int ncols_first = getNumCols(0);
	int nsubprobs = getNumSubproblems();
	for (int s = 0; s < nsubprobs; ++s)
		for (int j = 0; j < ncols_first; ++j)
		{
			if (s == 0)
				newMultipliers[s * ncols_first + j] = multipliers[s * ncols_first + j] - multipliers[(nsubprobs - 1) * ncols_first + j];
			else
				newMultipliers[s * ncols_first + j] = multipliers[s * ncols_first + j] - multipliers[(s - 1) * ncols_first + j];
		}
}

DSP_RTN_CODE DecTssModel::getFullModel(
	CoinPackedMatrix *& mat, /**< [out] constraint matrix */
	double *& clbd,          /**< [out] column lower bounds */
	double *& cubd,          /**< [out] column upper bounds */
	char   *& ctype,         /**< [out] column types */
	double *& obj,           /**< [out] objective coefficients */
	double *& rlbd,          /**< [out] row lower bounds */
	double *& rubd           /**< [out] row upper bounds */)
{
	int nsubprobs = getNumSubproblems();
	int * subprobs = new int [nsubprobs];
	CoinIotaN(subprobs, nsubprobs, 0);

	DSP_RTN_CODE rtn = decompose(nsubprobs, subprobs, 0, NULL, NULL, NULL,
			mat, clbd, cubd, ctype, obj, rlbd, rubd);

	/** free array */
	FREE_ARRAY_PTR(subprobs);

	return rtn;
}

DSP_RTN_CODE DecTssModel::copySubprob(
		int subprob,             /**< [in] subproblem index */
		CoinPackedMatrix *& mat, /**< [out] constraint matrix [A^k B^k] */
		double *& clbd,          /**< [out] column lower bounds of y */
		double *& cubd,          /**< [out] column upper bounds of y */
		char   *& ctype,         /**< [out] column types of y */
		double *& obj,           /**< [out] objective coefficients for y */
		double *& rlbd,          /**< [out] row lower bounds */
		double *& rubd           /**< [out] row upper bounds */) {
#define FREE_MEMORY     \
	FREE_PTR(mat_reco); \
	FREE_ARRAY_PTR(clbd_reco); \
	FREE_ARRAY_PTR(cubd_reco); \
	FREE_ARRAY_PTR(obj_reco)

	CoinPackedMatrix *mat_reco = NULL;
	double* clbd_reco = NULL;
	double* cubd_reco = NULL;
	double* obj_reco = NULL;

	BGN_TRY_CATCH

	/** copy recourse problem */
	DSP_RTN_CHECK_RTN_CODE(copyRecoProb(subprob, mat,
				mat_reco, clbd_reco, cubd_reco, ctype, obj_reco, rlbd, rubd));

	/** merge matrix */
	mat->rightAppendPackedMatrix(*mat_reco);

	/** allocate memory */
	clbd = new double [ncols_core_];
	cubd = new double [ncols_core_];
	obj = new double [ncols_core_];

	/** copy objective coefficients */
	CoinCopyN(clbd_core_[0], ncols_[0], clbd);
	CoinCopyN(cubd_core_[0], ncols_[0], cubd);
	CoinCopyN(obj_core_[0], ncols_[0], obj);
	CoinCopyN(clbd_reco, ncols_[1], clbd + ncols_[0]);
	CoinCopyN(cubd_reco, ncols_[1], cubd + ncols_[0]);
	CoinCopyN(obj_reco, ncols_[1], obj + ncols_[0]);

	END_TRY_CATCH_RTN(FREE_MEMORY,DSP_RTN_ERR)

	FREE_MEMORY

	return DSP_RTN_OK;
#undef FREE_MEMORY
}

DSP_RTN_CODE DecTssModel::copyRecoProb(
		int scen,                     /**< [in] scenario index */
		CoinPackedMatrix *& mat_tech, /**< [out] technology matrix (A matrix) */
		CoinPackedMatrix *& mat_reco, /**< [out] recourse matrix (B matrix) */
		double *& clbd_reco,          /**< [out] column lower bounds of y */
		double *& cubd_reco,          /**< [out] column upper bounds of y */
		char   *& ctype_reco,         /**< [out] column types of y */
		double *& obj_reco,           /**< [out] objective coefficients for y */
		double *& rlbd_reco,          /**< [out] row lower bounds */
		double *& rubd_reco,          /**< [out] row upper bounds */
		bool adjust_probability       /**< [in] adjust probability */)
{
	assert(scen >= 0 && scen < nscen_);
	assert(nstgs_ > 1);
	assert(nrows_ != NULL);
	assert(ncols_ != NULL);
	assert(nrows_[0] >= 0);
	assert(ncols_[0] >= 0);
	assert(nrows_[1] >= 0);
	assert(ncols_[1] >= 0);

	int i;
	CoinPackedVector * row = NULL;

	BGN_TRY_CATCH

	/** allocate memory */
	mat_tech   = new CoinPackedMatrix(false, 0, 0);
	mat_reco   = new CoinPackedMatrix(false, 0, 0);
	clbd_reco  = new double [ncols_[1]];
	cubd_reco  = new double [ncols_[1]];
	ctype_reco = new char [ncols_[1]];
	rlbd_reco  = new double [nrows_[1]];
	rubd_reco  = new double [nrows_[1]];

	/** matrices */
	mat_tech->setDimensions(0, ncols_[0]);
	mat_reco->setDimensions(0, ncols_[1]);
	for (i = rstart_[1]; i < nrows_core_; ++i)
	{
		/** add row to tech */
		row = this->splitCoreRowVec(i, 0);
		combineRandRowVec(row, i - rstart_[1], 0, scen);
		mat_tech->appendRow(*row);
//		PRINT_COIN_PACKED_VECTOR_MSG((*row),"row_tech")
		FREE_PTR(row)

		/** add row to reco */
		row = this->splitCoreRowVec(i, 1);
		combineRandRowVec(row, i - rstart_[1], 1, scen);
		mat_reco->appendRow(*row);
		//PRINT_COIN_PACKED_VECTOR_MSG((*row),"row_reco")
		FREE_PTR(row)
	}

	/** column lower bounds */
	copyCoreColLower(clbd_reco, 1);
	combineRandColLower(clbd_reco, 1, scen);

	/** column upper bounds */
	copyCoreColUpper(cubd_reco, 1);
	combineRandColUpper(cubd_reco, 1, scen);

	/** column types */
	copyCoreColType(ctype_reco, 1);

	/** objective coefficients */
	copyRecoObj(scen, obj_reco, adjust_probability);

	/** row lower bounds */
	copyCoreRowLower(rlbd_reco, 1);
	combineRandRowLower(rlbd_reco, 1, scen);

	/** row upper bounds */
	copyCoreRowUpper(rubd_reco, 1);
	combineRandRowUpper(rubd_reco, 1, scen);

	END_TRY_CATCH_RTN(;,DSP_RTN_ERR)

	return DSP_RTN_OK;
}
