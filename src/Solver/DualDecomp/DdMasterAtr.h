/*
 * DdMasterAtr.h
 *
 *  Created on: Mar 22, 2016
 *      Author: kibaekkim
 */

#ifndef SRC_SOLVER_DUALDECOMP_DDMASTERATR_H_
#define SRC_SOLVER_DUALDECOMP_DDMASTERATR_H_

#include "Solver/DualDecomp/DdMasterTr.h"

/** A class for implementing the asynchronous trust-region master solver. */
class DdMasterAtr: public DdMasterTr {

	friend class DdMWAsync;

public:

	/** A default constructor. */
	DdMasterAtr(
			DecModel *   model,   /**< model pointer */
			DspParams *  par,     /**< parameter pointer */
			DspMessage * message, /**< message pointer */
			int nworkers          /**< number of workers */);

	/** A copy constructor. */
	DdMasterAtr(const DdMasterAtr& rhs);

	/** A default desctructor. */
	virtual ~DdMasterAtr();

	/** A clone function */
	virtual DdMasterAtr* clone() const {
		return new DdMasterAtr(*this);
	}

	/** A virtual member for initializing solver. */
	virtual DSP_RTN_CODE init();

	/** A virtual member for solving problem. */
	virtual DSP_RTN_CODE solve();

	/** update problem */
	virtual DSP_RTN_CODE updateProblem(
			double * primsol, /**< master primal solution at which newdual is obtained */
			double   newdual  /**< new dual objective value */);

	/** update trust region */
	DSP_RTN_CODE updateTrustRegion(
			const double * primsol /**< current master primal solution */);

	/** termination test */
	DSP_RTN_CODE terminationTest();

	/** clear subproblem data */
	DSP_RTN_CODE clearSubprobData();

	/** set primal solution to worker */
	DSP_RTN_CODE setPrimsolToWorker(
			int      worker_id, /**< worker ID */
			double * primsol    /**< primal solution assigned to worker */);

protected:

	/** add cuts */
	virtual int addCuts(
			bool possiblyDel = true /**< possibly delete cuts*/);

	/** change trust region */
	virtual DSP_RTN_CODE setTrustRegion(double stability_param, double * stability_center);

	int nworkers_; /**< number of workers */

	vector<int> worker_;
	vector<int> solution_key_;     /**< unique ID for master solution to be evaluated */
	vector<int> nsubprobs_;        /**< number of subproblems for the current worker */
	vector<int*> subindex_;        /**< array of subproblem indices */
	vector<double*> subprimobj_;   /**< subproblem primal objective values */
	vector<double*> subdualobj_;   /**< subproblem dual objective values */
	vector<double**> subsolution_; /**< subproblem solution */

	int * nlastcuts_;             /**< number of cuts generated at the last iteration */
	double ** primsol_to_worker_; /**< primal solution (theta and lambda) given to each worker */
	bool is_updated_;             /**< indicate if the model is updated after solve */
	bool * proved_optimality_;    /**< indicate if the optimality is proved for each worker */
};

#endif /* SRC_SOLVER_DUALDECOMP_DDMASTERATR_H_ */
