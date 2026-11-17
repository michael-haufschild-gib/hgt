# Five applications of probe and character calculus

- **Stage:** 1-in-progress
- **Type:** CANDIDATE

## Results

| Programme | Mathematical result | Lean declaration |
|---|---|---|
| ECS | Every nonzero polynomial filter of the actual state's tail moments retains square tests of both signs | [`riemannHypothesis_or_indefinite_polynomial_tail_filters`](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/PolynomialTailFilters.lean) |
| ECS | Exact Chebyshev norm loss; equality precisely at return to the probe span | [`ProbeWalk.chebyshev_leakage_identity`, `ProbeWalk.chebyshev_norm_eq_iff_return`](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Pick/ChebyshevLeakage.lean) |
| ECS | Actual Weil matrix $K=G_+-G_-$, ordinary Gram matrix $G=G_++G_-$, and $G\pm K\succeq0$ | [`ProbeWalk.probeGram_eq_sector_difference`, `ProbeWalk.hilbertProbeGram_sub_probeGram_posSemidef`](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Pick/ProbeSectorGrams.lean) |
| OSM | Three-channel polynomial calculus for cubic unit rotation; signed pairing multiplier $p(z^2)$ | [`unitRotation_polynomial`, `finite_row_sum_rotation_polynomial`](../../../../formal/GaloisForLFunctions/OrderSixMetaplecticTheory/CharacterChannels/CubicRotationCalculus.lean) |
| OSM | Unique minimum-norm class vector carrying a given signed pairing, with exact residual energy | [`coherentClassVector_minimum_eq_iff`, `finite_row_sum_phase_energy`](../../../../formal/GaloisForLFunctions/OrderSixMetaplecticTheory/CharacterChannels/MinimumEnergyPhaseCarrier.lean) |

## Proofs

1. The moment filter $s_k\mapsto\sum_jq_js_{k+j}$ multiplies the damped state
   density by $q(e^{u+T})$. Bounded-coordinate square tests detect its sign
   almost everywhere. A nonzero polynomial has finitely many roots, so
   $q(e^{u+T})$ has a fixed strict sign on some deeper tail. Nonnegative
   filtered density would make the state one-signed there, contradicting
   its sign law. Applying the same argument to $-q$ gives the opposite test.
2. With probe projection $Q$ and isometric reflection walk $W$, compression
   gives $T_n(QRQ)x=QW^nx$ for $x\in\operatorname{ran}Q$. Pythagoras gives
   $\|T_n(QRQ)x\|^2+\|(1-Q)W^nx\|^2=\|x\|^2$; equality in the contraction
   bound is equivalent to zero residual, hence return to the probe span.
3. The self-adjoint involution $R$ splits each probe into $(v+Rv)/2$ and
   $(v-Rv)/2$. Their Gram matrices are positive. Expanding the inner products
   gives $G=G_++G_-$ and $K=G_+-G_-$, hence $G+K=2G_+$ and $G-K=2G_-$.
4. For $a^3=1$, $E_a=(I+aU+a^2U^2)/3$ is idempotent and $UE_a=a^2E_a$.
   The actual phase $z=\chi_2(\omega)$ satisfies $z^3=1$, $z\ne1$;
   $E_1+E_z+E_{z^2}=I$. Polynomial induction gives the full calculus.
   The arithmetic identity $W(Uf)=z^2W(f)$ gives $W(p(U)f)=p(z^2)W(f)$.
   Cancellation is exactly $p(z^2)=0$ or $W(f)=0$.
5. In the finite class Hilbert space, $v=\overline{\mathrm{phase}}$ satisfies
   $\langle v,f\rangle=W(f)$ and $v\ne0$ because $\mathrm{phase}(1)=1$.
   Projection onto $\mathbb Cv$ is $W(f)v/C$, $C=\|v\|^2>0$. The residual
   has zero pairing. Pythagoras gives
   $|W(f)|^2+C\|f-W(f)v/C\|^2=C\|f\|^2$ and uniqueness of the minimum.
   Substitution of the actual Gauss class masses gives the finite-row identity.

## Polynomial-filter obstruction and positive survivor

Finite polynomial filtering cannot restore positivity of a critical-state tail.
The exact surviving classification is
`filteredTailMoment_square_nonnegative_iff`: all filtered square tests are
nonnegative iff $q(e^{u+T})F(u)\ge0$ almost everywhere on that tail.
Both the obstruction and this positive classification have dependency-closed
proofs and Lean formalizations. The unconditional ECS conclusion is an RH/state
dichotomy; no critical-state existence premise is added.
