# Next audit: coherent repairs on a common translation lattice

Status: FORMALIZED in cycle 13 as WeilWorkExposingRayLatticeMass.lean. Stronger exact defect identity, one-half-pole specialization, weighted stability and sampled-sign classification all pass Lean. Original proposal/audit trail follows. Main opposite-ray conjecture remains open.

Fix the actual Fejer profile psi with correlation R and lattice spacing X>=4. For finite complex coefficient vectors c_i on 0,...,m, form f_i(u)=sum_j c_ij psi(u-jX), with nonnegative mixture weights alpha_i. Require each f_i to be polar. Write b_d=sum_i alpha_i sum_j c_i,j+d conj(c_ij). Let n_d=ceil(exp(dX)), d=1,...,m. The proposed rounding estimate is eta_d=log(n_d)-dX in [0,1/4], and all other correlation windows are disjoint from this sample.

Candidate exact mass law:

sum_{d=1}^m cosh(dX/2)*atomTrace(n_d)/R(eta_d) = -b_0,

where atomTrace=sum_i alpha_i atomCoeff(f_i), and b_0=sum_i alpha_i sum_j |c_ij|^2. The normalization uses atomCoeff without its outer dual factor 2*pi.

Mechanism: autocorrelation expansion isolates atomTrace(n_d)=2 Re(b_d) R(eta_d). Evaluating the finite autocorrelation polynomial at the two polar points gives b_0+2 sum_d Re(b_d)cosh(dX/2)=0. R(eta_d)>0 follows from the already verified actual-profile bounds.

If correct, complete zero trace forces every active coefficient vector to vanish. Further, a nontrivial polar family cannot be repaired to zero by adding nonnegative mixtures of polar tests on the same common-profile lattice, regardless of energy budget or number of added lattice sites. This is narrower than arbitrary coherent repair: different profiles, overlapping windows and nonlattice centres remain outside.

Positive survivor is the exact sampled mass identity, not only the nonexistence statement. Before Lean work: inspect finite packet and polar moment corpus for this identity; check complex conjugation and the role of both polar constraints; audit arbitrary lattice length and all missing integer samples. Current deep search returned partial=true (retrieval interrupted/deadline); inspected hits included GramPackets and comb autocorrelation, not an applicable exact sampled mass identity. This is not an absence or novelty proof.


Parent identity located during the audit: `integral_weilTestEvenPart_mul_cosh_eq_zero` in `WeilPositivityConstantShiftRigidity.lean:48` already proves continuous polar cancellation. Therefore the new content, if worthwhile after attack, must be exact finite recovery of this moment from integer samples in the specified common-profile class; the polar identity itself is prior knowledge. No novelty claim or Lean implementation yet.

## Cycle 12 re-audit and next exact target

The local-seed capacity audit shows why a full spectral variance completion cannot attain zero total energy for the literal Riemann source. Return to discrete integer matching, retaining the above quantitative mass identity as the candidate, rather than claiming a generic cancellation receiver.

Fresh deep search completed non-partial with a complete 68,469-file inventory, but mostly pending/stale compiler metadata and incomplete background refresh. All candidate lemmas and source arguments inspected. Direct source audit found the existing `WeilWorkDeficitGeometricRadicalObstruction.logValue_geometric_radical_eq_zero_iff`: arbitrary finite coherent mixtures of sufficiently broad truncated Riemann kernels translated on j*log(b), integer b>=2, already have injective complete power-sampled trace. Its positive survivor is the outer convolution coefficient identity. That is prior research, not this task's contribution.

The proposed Fejer statement differs in two exact obligations: arbitrary real X>=4 with rounded integer samples ceil(exp(dX)), and an identity recovering the complete coefficient mass, not only detecting a nonzero outer coefficient. Before formalizing, verify every correlation-window isolation, the two complex polar moments, positivity of every R(eta_d), and all finite indexing/normalizations. Test whether the existing outer-support argument subsumes its useful consequence; if so, classify the no-go as rediscovered and retain only a genuinely stronger quantitative source law. No conclusion about nonlattice or overlapping-profile repairs follows.
