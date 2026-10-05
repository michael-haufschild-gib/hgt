# Integral--nuclear boundary-scale germ Pythagorean law

- **ID:** `ULF-INBSG-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-POINH-001`, `ULF-PSH-001`, P-G94, P-G98, P-G102
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN INPUTS PROVED] [LEAN CAPSTONE OPEN] [NOT RH]`
- **Lean status:** all corpus inputs are Lean-proved; this synthesis was found during a read-only
  Lean audit, so no capstone module was written

## What was wrong first

The strict source bound `||T||<1` from `ULF-POINH-001` does **not** survive the completion already
forced by the corpus.  P-G98 does not give a bounded unital channel carrying `T` to a horizon.  It
gives the singular boundary transfer

\[
 E_\varepsilon(T)=T(\varepsilon I+T)^{-1}.                 \tag{INBSG.1}
\]

For positive injective `T`, the corpus proves `E_eps(T) -> I` strongly while
`||E_eps(T)-I||=1` for every `eps>0`.  Hence the proposed inequality
`||Phi(T)||<=||T||<1` used the wrong category.  Strong topology forgets the entire obstruction;
ordinary norm convergence does not exist.

The surviving datum is the **norm germ of the open regularization history**, before its strong
observer is closed.

## Big-picture law aimed at

One fixed pre-divisor operator carries integral homotopy charge, literal prime mixing, and an
infinite nuclear tail.  Completion does not transport its pointwise norm.  It scans that tail by a
shrinking aperture `eps`.  Multiplicative polarization is therefore not another operator or
coefficient ledger: it is a translation of the aperture history

\[
 E_\varepsilon(cT)=E_{\varepsilon/c}(T).                  \tag{INBSG.2}
\]

Closing the history strongly sends every translation to `I`.  Keeping its norm germ records the
translation by one exact bounded contrast.  The additive Poisson half-density history records the
complementary visibility.  Their sum-of-squares law is forced:

\[
 \boxed{\text{open nuclear scale memory}^{,2}
       +\text{closed Poisson overlap}=1.}                 \tag{INBSG.3}
\]

This is not a Lorentzian analogy imposed on the corpus.  The hyperbolic coordinate is derived from
the actual singular completion and the accumulation of nuclear spectrum at zero.

## Corpus audit before the theorem

`scripts/formal_tools.py research` was run for scaled positive boundary transfer, strong versus
norm convergence, compact approximation blindness, Poisson scale history, Cayley contrast,
visibility, rapidity, Burnol holonomy, and Gamma-six paired curvature.  Exact inputs are:

- `ULF-POINH-001`: the one fixed operator
  `T=gammaSewnCriticalPhysicalPluckerSpectralOperator/tau` is positive, injective, compact,
  Schatten one, prime/depth mixed, and recovered from an index-minus-one theta first exit;
- `positiveBoundaryTransfer`, `positiveBoundaryTransfer_tendsto_id`, and
  `norm_positiveBoundaryTransfer_sub_id`: equation `(INBSG.1)`, strong recovery, and maximal
  failure of operator-norm recovery;
- `RouteRStrongCompactApproximationBlindness`: strong compact approximation alone cannot
  distinguish any bounded target;
- `ULF-PSH-001` / `PoissonScaleHistoryFrame`: the literal normalized Poisson histories satisfy
  `<psi_t,psi_u>=4tu/(t+u)^2`;
- `burnolXiPrimeCayleyCoordinate_eq_character_ratio` and
  `burnolCoPoissonNormalizedHolonomy_eq_four_mul_cayley_div_one_sub_sq`;
- `sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq`: the paired Gamma-six defect is
  `2(cosh r-1)`;
- the likelihood/conditioning modules already prove `tanh`, `sech`, Einstein addition, and
  `artanh` formulas, but do not derive them from a completion topology.

No searched corpus theorem gives the scaled-transfer germ norm below or its exact Pythagorean
fusion with the literal Poisson history.

## 1. One integral--nuclear prime-mixed defect

Let `H=ell2(N_depth x N_primeIndex)` and let `T` be the `ULF-POINH-001` operator

\[
 T=\tau^{-1}\sum_{z,s}|a_{z,s}\rangle\langle a_{z,s}|.    \tag{INBSG.4}
\]

It is constructed before any zero or divisor and satisfies

\[
 T\ge0,\quad \ker T=0,\quad T\in S_1(H),\quad
 \operatorname{Tr}T=\|T\|_1=1,
 \quad -\operatorname{index}C=\operatorname{Tr}T=1.      \tag{INBSG.5}
\]

Every local packet has a nonzero cross-prime block, and all depths and adjacent-prime edges occur
in `(INBSG.4)`.  Thus `T` is the requested pre-divisor, prime-mixed, integral--nuclear homotopy
defect.  The theorem below adds the missing completion law; it does not replace `T` by a family.

## 2. Minimal boundary-history quotient

Let

\[
 \mathcal B=C_b((0,1],\mathcal K(H)),\qquad
 \mathcal I=C_0((0,1],\mathcal K(H)),\qquad
 \mathcal Q=\mathcal B/\mathcal I.                       \tag{INBSG.6}
\]

Here `I` consists exactly of norm histories vanishing as `eps downarrow 0`.  For
`F in B`, a cutoff at a small positive aperture proves

\[
 \|[F]\|_{\mathcal Q}=\limsup_{\varepsilon\downarrow0}
                         \|F(\varepsilon)\|.             \tag{INBSG.7}
\]

For `c>0` define the scale-orbit germ of the one operator `T` by

\[
 \mathfrak e_T(c)
   =[\varepsilon\mapsto E_\varepsilon(cT)]\in\mathcal Q. \tag{INBSG.8}
\]

Each value is compact because its scalar functional-calculus function vanishes at spectral zero.
Equation `(INBSG.2)` shows that `c` only translates the open aperture clock.  No source
normalization, trace, or homotopy charge is changed.

## 3. Exact scaled-transfer germ theorem

**Theorem INBSG-A.**  Let `T` be any positive compact injective operator on an
infinite-dimensional Hilbert space.  For all `c,d>0`,

\[
 \boxed{
 \|\mathfrak e_T(c)-\mathfrak e_T(d)\|_{\mathcal Q}
 =\frac{|\sqrt c-\sqrt d|}{\sqrt c+\sqrt d}.}             \tag{INBSG.9}
\]

The right side is independent of every eigenvalue and eigenvector of `T`.  Operator order supplies
the orientation, so define

\[
 \kappa(c,d)=\frac{\sqrt c-\sqrt d}{\sqrt c+\sqrt d}.
                                                                    \tag{INBSG.10}
\]

**Proof.**  Compact positivity and injectivity give eigenvalues `lambda_n>0` with
`lambda_n -> 0`.  On the `lambda` eigenspace, the difference of the two transfers is

\[
 h_{\varepsilon,c,d}(\lambda)
 =\frac{c\lambda}{\varepsilon+c\lambda}
  -\frac{d\lambda}{\varepsilon+d\lambda}
 =\frac{(c-d)\varepsilon\lambda}
        {(\varepsilon+c\lambda)(\varepsilon+d\lambda)}. \tag{INBSG.11}
\]

Put `x=eps/lambda`.  Elementary differentiation gives

\[
 \sup_{x>0}\frac{|c-d|x}{(x+c)(x+d)}
 =\frac{|\sqrt c-\sqrt d|}{\sqrt c+\sqrt d},             \tag{INBSG.12}
\]

with equality at `x=sqrt(cd)`.  Functional calculus and `(INBSG.12)` give the upper bound for
every `eps`.  Choose `eps_n=sqrt(cd) lambda_n`.  Then `eps_n -> 0`, and the `lambda_n` eigenvector
attains the right side exactly, giving the matching limsup lower bound.  Apply `(INBSG.7)`. QED.

Three consequences are immediate:

\[
 \begin{aligned}
 \kappa(c^{-1},d^{-1})&=-\kappa(c,d),\\
 \kappa(cd,1)&=\frac{\kappa(c,1)+\kappa(d,1)}
                     {1+\kappa(c,1)\kappa(d,1)},\\
 \operatorname{artanh}\kappa(c,d)&=\tfrac14(\log c-\log d).
 \end{aligned}                                          \tag{INBSG.13}
\]

Thus reflection, multiplicative formation, Einstein addition, and additive rapidity are all
shadows of translation on the singular-completion aperture.  They are not four independent laws.

## 4. Exact Poisson--nuclear conservation

Let `psi_t` be the corpus's literal unit Poisson half-density history and put

\[
 P(t,u)=\langle\psi_t,\psi_u\rangle=\frac{4tu}{(t+u)^2}. \tag{INBSG.14}
\]

Apply `(INBSG.9)` with `c=t^2`, `d=u^2`.  Then

\[
 \boxed{
 \|\mathfrak e_T(t^2)-\mathfrak e_T(u^2)\|_{\mathcal Q}^{,2}
 +P(t,u)=1.}                                            \tag{INBSG.15}
\]

**Proof.**  The left side is

\[
 \frac{(t-u)^2}{(t+u)^2}+\frac{4tu}{(t+u)^2}=1.\qquad\Box
\]

This is a genuine identity between two independently constructed organs:

- nuclear/Pluecker formation enters through the prime-mixed integral defect `T`;
- singular completion reads its open scale germ;
- additive Poisson self-duality reads the complementary closed overlap.

The equality is route-independent: every faithful positive compact `T` gives the same law, while
the HGT corpus supplies one literal pre-divisor `T` and one literal Poisson frame.

## 5. Fourth-organ predictions and reconstruction

Let `A>0`, set `c=A^2,d=1`, and orient the germ distance:

\[
 C=\kappa(A^2,1)=\frac{A-1}{A+1},\qquad
 G=P(A,1)=1-C^2.                                        \tag{INBSG.16}
\]

The germ theorem predicts, without using the definitions of those route reporters,

\[
 \begin{aligned}
 \text{Burnol normalized holonomy}&=A-A^{-1}=\frac{4C}{G},\\
 \text{Gamma paired curvature}&=2(\cosh(\log A)-1)=\frac{4C^2}{G},\\
 \text{Poisson visibility}&=\sqrt G=\operatorname{sech}(\tfrac12\log A),\\
 \text{rapidity}&=\operatorname{artanh}C=\tfrac12\log A.
 \end{aligned}                                          \tag{INBSG.17}
\]

All four equalities follow algebraically from `(INBSG.16)` and match separately Lean-proved
corpus organs.  In particular, the completion germ reconstructs them from only its oriented norm
coordinate and the conservation identity `(INBSG.15)`.

For an Euler horizontal grade `a` and prime `p`, take `A=p^a`.  Then

\[
 C=\tanh\!\left(\frac{a\log p}{2}\right)
   =\frac{p^a-1}{p^a+1},                                \tag{INBSG.18}
\]

exactly `burnolXiPrimeCayleyCoordinate`.  Functional-equation reflection `a -> -a` reverses the
open germ orientation `C -> -C`, fixes closed visibility `G`, and leaves curvature even.

There is also a falsifiable topology prediction.  If the source carrier has a spectral gap at
zero (in particular, finite nonzero rank), then

\[
 \|E_\varepsilon(cT)-E_\varepsilon(dT)\|\longrightarrow0.
                                                                    \tag{INBSG.19}
\]

Therefore a nonzero likelihood/Burnol contrast cannot arise from a finite packet or gapped
completion.  It requires the faithful compact tail accumulating at zero.  This identifies the
source of noncompact completion behavior exactly: not hypertranscendence as a slogan, but spectral
accumulation scanned at the moving scale `lambda approximately eps/sqrt(cd)`.

## 6. Exact surviving RH edge

For `a in R` and one prime `p>1`, use the direct/reflected scales

\[
 c_{p,a}=p^a,\qquad d_{p,a}=p^{-a}.                     \tag{INBSG.20}
\]

Theorem INBSG-A gives the unconditional classifier

\[
 \mathfrak e_T(c_{p,a})=\mathfrak e_T(d_{p,a})
 \quad\Longleftrightarrow\quad c_{p,a}=d_{p,a}
 \quad\Longleftrightarrow\quad a=0.                    \tag{INBSG.21}
\]

Thus one source theorem would close the horizontal selection edge:

> After subtraction of the already identified universal metric anomaly, literal integer/Poisson
> self-duality identifies the direct and reflected translations of the **same** boundary-transfer
> history modulo `C_0`.

Specializing that pre-divisor identity to any completed Xi copy makes the left equality of
`(INBSG.21)` hold with `a=2 Re(rho)-1`; hence `a=0`, so `Re(rho)=1/2`.

This identification is not proved here and is not to be postulated.  Its advantage over the old
same-boundary landing is precision:

- strong equality is automatic for every `a` and therefore useless;
- pointwise norm convergence is impossible;
- a bounded positive-unital map is the wrong completion;
- coefficientwise positive cofinal damping is already RH-equivalent;
- equality in the minimal norm-germ quotient is exactly the remaining source-completion claim.

The missing theorem must be derived before a zero or divisor is supplied, from the literal Poisson
translation frame and anomaly subtraction.  After divisor specialization, `(INBSG.21)` is a
classifier, not a producer.

`ULF-PBTIA-001` sharpens “anomaly subtraction”: it computes the canonical defect of commuting
singular completion with closure of `T`'s purification.  If each scale may subtract its own defect,
all residual boundaries agree and selection is void.  The viable requirement is equality with one
anomaly germ fixed by theta before polarization.

## Hostile review

- `[CORRECTION]` `ULF-POINH-001`'s bounded-channel norm-gap proposal is dead.  P-G98 singular
  flattening erases `||T||<1` at the strong endpoint.
- `[ABSTRACTLY STANDARD]` Functional calculus, `C_b/C_0` corona quotients, projective metrics on
  positive cones, and hyperbolic identities are known mathematics.
- `[NEW CORPUS LAW]` The exact quotient-norm formula `(INBSG.9)` derives the corpus contrast from
  its actual singular completion and needs no spectral distribution.  Its fusion with the literal
  Poisson frame gives the cross-organ conservation law `(INBSG.15)`.
- `[SIGNIFICANCE]` One scalar germ reconstructs four independently developed route reporters and
  proves that infinite nuclear tail, rather than finite packet geometry, is necessary for their
  nontriviality.
- `[GENERICITY LIMIT]` Because `(INBSG.9)` is independent of `T`, it explains the common geometry
  but supplies no arithmetic producer by itself.  Source leverage must constrain which anomaly
  germ completion is allowed to use; `ULF-PBTIA-001` isolates that operation-order question.
- `[NOT RH]` Equality of direct/reflected germs is unproved.  Merely naming it “admissibility” or
  asserting it at Xi fibres is the old receiver problem.
- `[FALSIFIERS]` `(INBSG.9)` fails without positivity/normality or without spectral accumulation at
  zero.  `(INBSG.15)` fails if completion aperture and Poisson clock are not related by the forced
  square `c=t^2`.  Both conditions are explicit audit targets.

## Literature boundary

Hilbert projective metrics on positive cones and their quantum-information contractivity are
standard (Reeb--Kastoryano--Wolf, <https://arxiv.org/abs/1102.5170>).  Thompson geometry and
Karcher means on positive operators provide another established scale geometry
(Lim--Palfia, <https://arxiv.org/abs/1703.04292>).  Geodesically convex operator scaling is also
known (Allen-Zhu--Garg--Li--Oliveira--Wigderson, <https://arxiv.org/abs/1804.01076>).
No checked source states `(INBSG.9)` as the norm-corona distance of singular boundary-transfer
histories or joins it to the literal Poisson half-density overlap by `(INBSG.15)`.  Novelty is not
needed for the theorem's validity; this boundary only prevents confusing the derived mechanism
with generic positive-cone geometry.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.SingularBoundaryTransferScaleGerm`, `GaloisForLFunctions.HTGeometry.BoundaryHistoryCorona`, `GaloisForLFunctions.RHTower.PhysicalPluckerIntegralNuclearDensity`, `GaloisForLFunctions.RHTower.PhysicalPluckerThetaLift`, `GaloisForLFunctions.RHTower.IntegralNuclearScaleGermOrgans`, `GaloisForLFunctions.RHTower.PositiveInjectiveBoundaryTransfer`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.SingularBoundaryTransferScaleGerm`,
`GaloisForLFunctions.HTGeometry.BoundaryHistoryCorona`,
`GaloisForLFunctions.RHTower.PhysicalPluckerIntegralNuclearDensity`,
`GaloisForLFunctions.RHTower.PhysicalPluckerThetaLift` and
`GaloisForLFunctions.RHTower.IntegralNuclearScaleGermOrgans` (new), on the corpus core
`GaloisForLFunctions.RHTower.PositiveInjectiveBoundaryTransfer`; all `lake env lean` clean, built,
axiom audit `[propext, Classical.choice, Quot.sound]` only.  `T = normalizedPhysicalPluckerOperator`,
`E_ε = positiveBoundaryTransfer`, `κ = germContrast`, `𝔢_T = scaleGerm` / `pluckerScaleGerm`.

| Claim | Lean declaration |
|-|-|
| (INBSG.1) `E_ε(T) = T(εI+T)⁻¹` | corpus `positiveBoundaryTransfer` |
| (INBSG.2) `E_ε(cT) = E_{ε/c}(T)` | `positiveBoundaryTransfer_smul` |
| (INBSG.4) `T = τ⁻¹∑∣a⟩⟨a∣` (frame/Gram form) | `normalizedPhysicalPluckerOperator`, `normalizedPhysicalPluckerOperator_eq_frameOperator`, `normalizedPhysicalPluckerOperator_eq_leftGram` |
| (INBSG.5) `T ≥ 0`, `ker T = 0`, `T ∈ S₁`, `Tr T = ‖T‖₁ = 1`, `-ind C = Tr T = 1`; nonzero cross-prime blocks | `normalizedPhysicalPluckerOperator_isPositive`, `normalizedPhysicalPluckerOperator_injective`, `normalizedPhysicalPluckerOperator_memSchattenClass_one`, `opTrace_normalizedPhysicalPluckerOperator`, `traceNorm_normalizedPhysicalPluckerOperator`, `thetaLift_conservation`, `exists_crossPrime_spectralBlock_ne_zero`, `exists_crossPrime_ray` |
| (INBSG.6) `𝒬 = C_b((0,1],𝒦(H))/C_0` | `CompactOps`, `ApertureHistory`, `vanishingHistories`, `BoundaryCorona` |
| (INBSG.7) `‖[F]‖ = limsup ‖F(ε)‖` | `norm_boundaryCorona_mk` |
| (INBSG.8) scale germ; values compact | `transferHistory`, `scaleGerm`, `isCompactOperator_positiveBoundaryTransfer` |
| Theorem INBSG-A, (INBSG.9) `‖𝔢_T(c)-𝔢_T(d)‖ = ∣√c-√d∣/(√c+√d)` (any positive compact injective `T`, `dim H = ∞`) | `norm_scaleGerm_sub`, `limsup_norm_scaledTransfer_sub`; for the physical `T`: `norm_pluckerScaleGerm_sub` |
| (INBSG.10)–(INBSG.12) symbol, supremum bound, resonance at `x = √(cd)` | `germContrast`, `scaledTransferSymbol`, `scaledTransferSymbol_eq`, `abs_scaledTransferSymbol_le`, `scaledTransferSymbol_resonance`, `norm_scaledTransfer_sub_le`, `le_norm_scaledTransfer_sub_of_mem_spectrum` |
| (INBSG.13) reflection, Einstein addition, rapidity `artanh κ = (log c - log d)/4` | `germContrast_inv`, `germContrast_mul_einstein`, `artanh_germContrast` |
| (INBSG.14)–(INBSG.15) `‖𝔢_T(t²)-𝔢_T(u²)‖² + P(t,u) = 1` | corpus `poissonScaleHistoryGram_eq`; `norm_sq_pluckerScaleGerm_add_poisson` |
| (INBSG.16)–(INBSG.17) four organs from `C`, `G = 1 - C²`; matched to corpus Burnol and Gamma-six organs | `germContrast_sq_one`, `poissonScaleHistoryGram_one`, `germContrast_four_organs`, `burnolCoPoissonNormalizedHolonomy_eq_germ`, `sourceHorizontalGammaSixCurvature_eq_germ` |
| (INBSG.18) `C = tanh(a log p/2) = (pᵃ-1)/(pᵃ+1)` = Burnol–Cayley coordinate; reflection reverses `C`, fixes `G`, curvature even | `germContrast_prime_rpow`, `germContrast_eq_burnolXiPrimeCayleyCoordinate`, `germContrast_prime_reflection` |
| (INBSG.19) spectral gap ⇒ contrast → 0; finite rank and finite-dimensional carriers are gapped | `tendsto_norm_scaledTransfer_sub_of_gap`, `exists_gap_of_finite_nonzero`, `exists_spectral_gap_of_hasRankLE`, `exists_spectral_gap_of_finiteDimensional`, `tendsto_norm_scaledTransfer_sub_of_hasRankLE`, `tendsto_norm_scaledTransfer_sub_of_finiteDimensional` |
| (INBSG.20)–(INBSG.21) `𝔢_T(pᵃ) = 𝔢_T(p⁻ᵃ) ⟺ a = 0` | `pluckerScaleGerm_prime_eq_iff`, `germContrast_eq_zero_iff` |

§6's pre-divisor same-history identification is stated in the card as not proved and not postulated;
it is not claimed.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
