# BAG actual coupled strip energy

01ax. Dependency-closed paper and production Lean proof COMPLETE.
ChiCubicCoupledStripEnergy284lines/API1. Complete scratch27320PASS;
unusedparameter removed. Finalforeground production64537emptyPASS,
axiom74320standard3; index55017PASS/API1/importonce; scoped diffcheckPASS.
Lint69952terminal1: eight unrelatedunreachablemodules DeckCuspEigenvalueNonneg,
PluckerCovarianceSquareRootPurification,VerticalProgressionBumpSums,
VerticalProgressionCutoffSums,VerticalProgressionFirstMomentExpansion,
VerticalProgressionLatticeSums,VerticalProgressionMollifier,
HTGeometry.FrameOperatorPurity;362warnings,noownederror.
No full/umbrella build, numerical experiment or resource-limit override.

For every0<=s<3/2, oneCs>0 bounds
 integral_{|lambda*a|<=1/4} (1+|a|+|b|)^(2s)*|K_delta,h(a,b,lambdaab)|²
uniformly for everyrealcurvaturelambda, relativewidthdelta in(0,1/2),
and logarithmicparameterh in[0,1]. This integrand is integrable on the
whole strip. K is the FULL actual reciprocal kernel proved in
ChiCubicCoupledKernelDecay, with every Gaussian/log/cutoff/window factor.
Atlambda=0 the strip is the fullfrequencyplane. No source/energy premise.

Proof. Putw=|F|+|F'|, rho(P,Q)=w(P)w(Q). Actual mass/firstvariation budgets
boundintegralrho by a universalM. The audited coupled bound is
 |K(a,b,lambdaab)|<=C*integral_PQ rho(P,Q)*g(P,Q,a,b),
 g=1/((1+|a|)(1+|b|)(1+|aQ+bP+lambdaab|)).
The existing real weighted Cauchy–Schwarz theorem gives its square at
mostC²*(integralrho)*(integralrho*g²). Its admissions hold because rho
is continuous with compact support andg is continuous with positive
denominator. Multiply by(1+|a|+|b|)^(2s).

The existing U5 curved-frequency energy theorem bounds thefrequency
integral of this weightedg² uniformly forP,Q in[1,2]. Outside thatbox,
rho=0. The joint positive physical/frequency integrand is measurable;
its frequencyfibre integrals are bounded byCs*rho. Since rho is
integrable, integrable_prod_iff admits the fulljointintegral. Fubini and
the densitymass bound give totalenergy<=C²*M²*Cs. Kernelmeasurability
comes directly from its literal measurable integrand and threeparameter
integral measurability results, with no regularity assumption on an
unevaluatedparameterintegral.

Corpus basis: ChiCubicCoupledKernelDecay,
ChiCubicCurvedFrequencyEnergy, ChiCubicPhysicalAmplitudeBudgets,
HTGeometry.IntegralCauchySchwarz.sq_integral_weighted_le (actualnamespace
GaloisForLFunctions.HTGeometry); deepsearch1522 recorded in parentP1.

Next hard obligations: complementary highfrequencyenergy foractualN,
compactfrequency and stronglowerHs convergence, physicallog-coordinate
and Mellinline tails, lowergrowtharithmetic envelope, moving signed
transfer, entiresharpaction bridge, growingmoments/cofactors and
commonheightselfreturn. RH remains open.
