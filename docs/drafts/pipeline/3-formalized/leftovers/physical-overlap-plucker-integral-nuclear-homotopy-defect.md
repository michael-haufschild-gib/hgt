# Physical-overlap Pluecker integral--nuclear homotopy defect

- **ID:** `ULF-POINH-001`
- **Stage:** `3-formalized`
- **Type:** unconditional pre-divisor five-organ fusion theorem
- **Parents:** `ULF-TM6H-001`, `ULF-POSGND-001`, P-G92, P-G94, P-G95, P-G99
- **Status:** `[PAPER-PROVED] [LEAN INPUTS PROVED] [LEAN CAPSTONE OPEN] [NOT RH]`
- **Lean status:** source ingredients are Lean-proved; this synthesis was developed under a
  read-only Lean audit, so the normalized capstone itself is not yet formalized

## Big-picture law

Do not polarize away local Pluecker nullity.  Glue the literal packet covariances on the shared
prime--depth lattice first.  Their local null lines then fail to produce an `ell2` global zero
mode, while their positive nuclear mass remains spread over several independent source rays.
Normalize only the total mass.  The result is a faithful density, never a pure state:

```text
local rank-three formation
  + physical overlap
  + trace normalization
  = integral nuclear mass with strict sub-unit concentration.
```

Theta first-exit supplies a canonical index-one open history whose two observer closures recover
this density exactly.  Thus local gauge non-descent, prime mixing, nuclearity, and integral
homotopy charge are four shadows of one operator rather than four analogies.

The important reversal is:

> failure of the local null gauge to descend is not a defect to remove; after physical gluing it
> is what makes the normalized source state faithful, while local rank three prevents its unit
> trace from concentrating in one completed direction.

No zero, divisor, ordinate, or completed-Xi response enters the construction.

## Corpus audit before construction

`scripts/formal_tools.py research` was run for the physical Pluecker operator, its trace,
faithfulness, rank-three blocks, shared-prime transport, theta first exit, and existing integral
defects.  Exact inputs are:

- `gammaSewnCriticalPhysicalPluckerSpectralOperator`: literal P-G94 operator on
  `ell2(N x N)`, the shared depth/adjacent-prime lattice;
- `..._memSchattenClass_one`, `..._isPositive`, `..._isCompact`: positive nuclearity;
- `gammaSewnCriticalPhysicalPluckerSourceTrace_eq_nuclearTraceMass` and
  `...SourceTrace_pos`: exact positive source trace;
- `gammaSewnCriticalPhysicalPluckerSpectralOperator_injective`: physical overlap kills every
  normalizable global null mode;
- `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three` and
  `..._ker_eq_span`: every local packet has exactly one common-mode null line;
- `gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_*_overlap_*`: packet labels glue on the
  actual prime--depth cells;
- `primeHodgeHistorySurvivalShiftIndex_eq_neg_one` and the theta first-exit reconstruction:
  the Mellin-six survival law has one integral Fredholm boundary unit;
- `primeHodgeHistoryIntegralNuclearHomotopyDefect_closed`: the older separable prime--history
  defect already satisfies the requested words, but does not contain the full physical rank-three
  Pluecker operator;
- `riemannHypothesis_iff_xiReflectionIncidenceTraceOnePositiveCofinalRegularizationLanding`:
  every coefficient-recovering positive cofinal trace-one regularization is already equivalent to
  RH; normalization cannot turn that closed search class into a producer;
- `frankensteinPluckerReporterTransport_metricNorm`: local reporter motion can be trivialized by
  a variable metric.  Therefore a strict bound obtained by comparing raw depth frames is not
  intrinsic.

## 1. Literal physical source operator

Let

```text
H = ell2(N_depth x N_primeIndex).
```

For a packet `z=(e,j)` and selected pair `s in Fin 6`, let `v_(z,s) in H` be the corpus's
physical centered Pluecker vector.  Its four coordinates are the two consecutive depth cells of
the adjacent primes `p_j,p_(j+1)`.  Put

```text
c_(z,s) = b_z pi_z(s) > 0,
a_(z,s) = sqrt(c_(z,s)) v_(z,s),                    (POINH.1)
A = sum_(z,s) |a_(z,s)><a_(z,s)|.                  (POINH.2)
```

Here `b_z` is the normalized P-G84 block mass and `pi_z` is the literal six-minor probability.
Equation `(POINH.2)` is definitionally
`gammaSewnCriticalPhysicalPluckerSpectralOperator`.  The corpus proves absolute operator-norm
summability, positivity, Schatten-one membership, and compactness.

Its trace is the completely explicit source scalar

```text
tau = Tr(A)
    = sum_(z,s) c_(z,s) ||v_(z,s)||^2
    = gammaSewnCriticalPhysicalPluckerNuclearTraceMass > 0.     (POINH.3)
```

Define the single normalized operator

```text
T = A/tau.                                             (POINH.4)
```

This normalization introduces no fitted target constant: `tau` is the literal total mass of the
same source expansion.

## 2. Prime mixing is intrinsic inside each packet

Split one packet into its two prime planes

```text
C^4 = C^2_p directSum C^2_q.
```

Let `M_z` be its rank-three spectral covariance.  Its common-mode vector spans the kernel.  The
cross-prime `2 x 2` block of `M_z` cannot vanish.  If it did, `M_z` would be block diagonal.  Since
the proved kernel vector has two nonzero coordinates in each prime plane, each diagonal block
would kill its corresponding two-coordinate restriction.  Extending these two restrictions by
zero gives two independent null vectors.  The total kernel would then have dimension at least
two, contradicting `rank(M_z)=3`.

Equivalently, for every `z`, at least one canonical source ray `a_(z,s)` has nonzero components in
both prime planes.  Thus prime mixing is present in the positive source decomposition before any
observer sum; it cannot be an off-diagonal cancellation manufactured after completion.

## 3. Integral nuclear theorem and strict sub-unit bound

Set

```text
alpha_i = a_i/sqrt(tau),       i=(z,s).
```

Then

```text
T = sum_i |alpha_i><alpha_i|,
sum_i ||alpha_i||^2 = 1.                              (POINH.5)
```

**Theorem POINH-A.** `T` is positive, compact, Schatten one, and faithful, with

```text
Tr(T)=||T||_1=1,
0 < ||T|| < 1.                                       (POINH.6)
```

It obeys the exact source-dispersion identity

```text
1-Tr(T^2)
 = sum_(i,k) [||alpha_i||^2 ||alpha_k||^2
              - |<alpha_i,alpha_k>|^2]
 = sum_(i,k) ||alpha_i wedge alpha_k||^2
 > 0.                                                (POINH.7)
```

**Proof.** Positivity, compactness, and Schatten-one membership survive multiplication by
`tau^-1>0`.  Linearity of operator trace and `(POINH.3)` give `Tr(T)=1`; positivity gives
`||T||_1=Tr(T)`.

Absolute nuclear convergence permits multiplication and trace term by term:

```text
Tr(T^2)=sum_(i,k)|<alpha_i,alpha_k>|^2.
```

Squaring the second identity of `(POINH.5)` and subtracting proves `(POINH.7)`.  Its summands are
Gram determinants and hence nonnegative.  They do not all vanish: one packet covariance has rank
three, so its positive rays span a three-dimensional space and at least two of them are not
collinear.  Therefore `Tr(T^2)<1`.  Since `T` is positive,

```text
0 < ||T||^2 <= Tr(T^2) < 1.
```

The left strict inequality follows from `Tr(T)=1`.  Faithfulness follows from corpus theorem
`gammaSewnCriticalPhysicalPluckerSpectralOperator_injective`. QED.

This proof compares no two packet frames.  Formula `(POINH.7)` is invariant under every common
unitary change of physical frame, and its strictness is already witnessed inside one packet, so
the source-derived local metric transports cannot erase it.

## 4. Exact homotopy lift

Let `I=((N x N) x Fin 6)` and form the canonical source purification

```text
Psi = sum_i delta_i tensor alpha_i in ell2(I) tensor H.          (POINH.8)
```

Equation `(POINH.5)` gives `||Psi||=1`, and closing the source-record observer gives

```text
Tr_(ell2(I)) |Psi><Psi| = T.                         (POINH.9)
```

Now use theta's already forced Mellin-six survival tail `m_n`, ratio
`r_n=m_(n+1)/m_n`, and exit mass `w_n=m_n(1-r_n)`.  In

```text
ell2(N_theta) tensor ell2(I) tensor H
```

put `epsilon_n=delta_n tensor Psi` and define the weighted unilateral shift

```text
C epsilon_n = sqrt(r_n) epsilon_(n+1).               (POINH.10)
```

The corpus's survival theorem applies verbatim on the marked ray span:

```text
index(C)=-1,
Tr(C*C-CC*)=1,
firstExit(C*C-CC*)
  = Dhat = sum_n w_n |epsilon_n><epsilon_n|.          (POINH.11)
```

Close first theta history and then the source record.  Because `sum_n w_n=1`,

```text
Tr_I (Tr_theta Dhat)
 = Tr_I |Psi><Psi|
 = T.                                                (POINH.12)
```

Therefore the one operator `(POINH.4)` is exactly the closed image of an integral homotopy
boundary, not merely a trace-one covariance.  The joint conservation law is

```text
-index(C)
 = Tr(C*C-CC*)
 = sum_n w_n
 = Tr(Dhat)
 = Tr(T)
 = 1.                                                (POINH.13)
```

For the two-sided horizontal wall define

```text
T_t = sign(t) T.                                     (POINH.14)
```

Then `T_(-t)=-T_t`, `Tr(T_t)=sign(t)`, and
`||T_t||_1=|sign(t)|`.  This supplies the reflection-odd integral grading without using a zero.

## 5. What the construction changes

The earlier `ULF-PCPOS-001` strict gap came from comparing normalized covariances at two depths in
one fixed packet presentation.  Independent source-forced fibre transports can change that
comparison.  It is therefore a valid fixed-frame theorem but not an intrinsic completion bound.

`T` fixes that failure:

- one physical Hilbert space is used from the start;
- shared cells are literally identified before normalization;
- strictness is witnessed by rank three inside one packet, not by motion between frames;
- all prime edges and depths enter one absolutely nuclear source sum;
- the theta index lifts and reconstructs the same operator exactly.

The operation order is forced:

```text
literal packet formation
 -> physical overlap
 -> positive nuclear sum
 -> normalize conserved source trace
 -> purify
 -> theta first-exit lift
 -> close observers.
```

Moving normalization or observer closure before physical overlap returns to the separable or
frame-dependent objects already present in the corpus.

### 5.1 Exact Euler non-insertion theorem

There is one tempting but impossible use of `T`: make it the internal multiplicity of every local
Euler factor.  If `z=p^(-s)` and one replaces the scalar factor by

```text
det(1-zT)^(-1),
```

then its logarithm near `z=0` is

```text
sum_(k>=1) Tr(T^k) z^k/k.                              (POINH.14a)
```

The literal Euler factor has logarithm `sum_(k>=1) z^k/k`.  Equality of the two germs therefore
forces `Tr(T^k)=1` for every `k`; already the quadratic coefficient forces

```text
Tr(T^2)=1.                                             (POINH.14b)
```

This contradicts the strict source-dispersion identity `(POINH.7)`.  Hence:

> **POINH-B.** No Fredholm-determinant insertion of the prime-mixed density `T` can preserve the
> literal unsquared Euler coefficients.  The only trace-one positive density that can reproduce a
> scalar Euler factor this way is a pure rank-one state, precisely the case excluded by physical
> Pluecker rank three.

The theorem fixes `T`'s role.  It may govern relations among prime packets, completion histories,
observer closures, or relative shorting, but it may not replace the one-dimensional local Euler
atom.  Prime mixing must occur **between** formation and completion, never inside the local Euler
factor.

## 6. Corrected completion edge

The first proposed use of `(POINH.6)` was wrong.  The corpus's actual P-G98 completion is not a
bounded positive-unital channel `Phi` carrying `T` to a rank-one horizon.  It is the singular
boundary transfer

```text
E_eps(T)=T(eps I+T)^(-1).
```

For positive injective `T`, Lean proves `E_eps(T) -> I` strongly and
`||E_eps(T)-I||=1` for every positive `eps`.  Consequently the strict source norm `||T||<1` is not
transported to the boundary, and the earlier contractivity contradiction is unavailable.

The positive survivor is `ULF-INBSG-001`: retain the norm germ of the open regularization history.
For `c,d>0` it proves

```text
limsup_(eps -> 0+) ||E_eps(cT)-E_eps(dT)||
  = |sqrt(c)-sqrt(d)|/(sqrt(c)+sqrt(d)).               (POINH.15)
```

Thus `T` still removes three excuses from the gate--lack of an integral source unit, lack of
literal prime mixing, and frame dependence--but selection must be a source-derived equality of
direct/reflected boundary **germs**, not a bounded landing of `T` itself.

The trace-one regularization no-go further fixes the type of the missing map.  `Phi` cannot arise
by multiplying ordinary-prime coefficients by positive recovering weights, even along a cofinal
subsequence: existence of that repair is already equivalent to RH.  Any viable completion must
act on the noncommutative Pluecker/Kraus relation before coefficient extraction--for example by a
relative quotient or shorting after anomaly subtraction--rather than regularize its scalar trace
ledger.

## 7. Exact cone-extension location of the integral charge

`ULF-SACWHT-001` identifies the algebra generated by the scale histories of this `T`.  In the
norm-history corona, every `E_eps(cT)` is a fractional-linear function of `E_eps(T)` and

```text
C*( [E_(bullet)(cT)] : c>0 ) ~= C_0((0,1]).
```

The differences of two scales form the suspension ideal `C_0((0,1))`, and closing the strong
observer is endpoint evaluation.  The connecting map of

```text
0 -> C_0((0,1)) -> C_0((0,1]) -> C -> 0
```

sends the closed unit to the winding-one class represented by `t |-> exp(2 pi i t)`.  This is the
topological location of the integral homotopy unit recovered in `(POINH.13)`.  It also proves that
the unit is common to every positive scale lift: it cannot be bounded by the strict sub-unit norm
between two lifts.  Grade-sensitive integrality must come from a prime-marked twist of the
extension, not from `T`'s positive functional calculus alone.

## Hostile review

- `[REDISCOVERED ABSTRACT LAW]` Normalizing a positive trace-class operator and the identity
  `(POINH.7)` are standard density-operator/Gram geometry.
- `[CORPUS COLLISION]` P-G94 already constructed `A`; P-G95 already proved faithfulness; theta
  first exit already supplies the index.  The new result is their exact normalization--purification
  fusion, not a new ingredient.
- `[REAL ADVANCE]` Unlike `ULF-PCPOS-001`, strictness survives all allowed frame changes because it
  is detected by same-packet rank three on the literal physical-overlap carrier.
- `[FAILED USE]` The strict norm gap does not survive P-G98 singular boundary flattening.  A
  positive-unital landing argument uses the wrong completion category.
- `[EXACT NO-GO]` Local Fredholm insertion of `T` changes the `p^(-2s)` coefficient from one to
  `Tr(T^2)<1`; preserving literal Euler factors would collapse `T` to rank one and erase the source
  geometry that defines it.
- `[POSITIVE SURVIVOR]` `ULF-INBSG-001` proves that translated regularization histories retain an
  exact scale contrast in the norm-corona germ even though their strong endpoints coincide.
- `[LIMIT]` `T` is not completed Xi.  Any direct/reflected germ equality not derived from Poisson
  self-duality before divisor specialization is theatre.
- `[NO-GO INTERFACE]` Positive coefficientwise cofinal damping is forbidden by the Lean-proved
  trace-one regularization equivalence.  The next map must transform relations, not weights.
- `[FALSIFIER]` The construction fails if `tau=0`, if every packet covariance has rank one, or if
  the P-G94 series is not Schatten one.  Corpus Lean theorems respectively exclude all three.

## Literature boundary

Density operators, Kraus purifications, Gram determinants, and trace/index homotopy are standard.
Carey--Kaad's homological index framework gives a broad abstract setting for trace-class
self-commutator charges (<https://arxiv.org/abs/1402.0475>).  No checked source contains the
source-specific fusion of the physical-overlap Pluecker operator, theta Mellin-six first exit,
and the exact strict-concentration law `(POINH.7)--(POINH.13)`.

## Lean certificate (2026-10-09)

| Card claim | Lean declaration (namespace `RHTower.HedenmalmThetaSource`) |
|-|-|
| `T = A/τ` positive, compact, Schatten one, faithful; `Tr T = ‖T‖₁ = 1`; `0 < ‖T‖ < 1` (POINH-A, POINH.6) | `normalizedPhysicalPluckerOperator_isPositive`, `_memSchattenClass_one`, `_isCompact`, `_injective`, `opTrace_normalizedPhysicalPluckerOperator`, `traceNorm_normalizedPhysicalPluckerOperator`, `norm_normalizedPhysicalPluckerOperator_lt_one` |
| `T = Σ |α_i⟩⟨α_i|`, `Σ ‖α_i‖² = 1` (POINH.5) | `normalizedPhysicalPluckerOperator_eq_frameOperator`, `hasSum_norm_sq_normalizedPluckerRay` |
| Source-dispersion identity and strictness (POINH.7) | `opTrace_normalizedPhysicalPluckerOperator_sq`, `one_sub_pluckerPurity`, `gramDeterminant_nonneg`, `exists_gramDeterminant_pos`, `pluckerPurity_lt_one` |
| Prime mixing inside every packet (§2) | `exists_crossPrime_spectralBlock_ne_zero`, `exists_crossPrime_ray` |
| Purification `Ψ`, `‖Ψ‖ = 1`, partial trace `T` (POINH.8–9) | `pluckerPurification`, `norm_pluckerPurification`, `pluckerPurification_isPartialTrace` |
| Weighted shift on marked rays, index `-1`, commutator trace `1`, first-exit defect (POINH.10–11) | `thetaMarkedShift_ray`, `thetaMarkedShift_comp_embedding`, `survivalShift_selfCommutator_eq`, `opTrace_survivalShift_selfCommutator`, `survivalShift_firstExit_weight`, `thetaFirstExitDefect` |
| Double observer closure and conservation law (POINH.12–13) | `thetaFirstExit_double_closure`, `thetaLift_conservation` |
| Signed wall `T_t = sign(t) T` (POINH.14) | `signedPhysicalPluckerWall_neg`, `opTrace_signedPhysicalPluckerWall`, `traceNorm_signedPhysicalPluckerWall` |
| Euler non-insertion (POINH-B, POINH.14a–b) | `opTrace_pow_eq_one_of_detOneSub_normalized_eq_euler`, `taylorCoeff_two_detOneSub_normalizedPhysicalPluckerOperator`, `not_eventually_detOneSub_eq_euler`, `normalizedPhysicalPluckerOperator_ne_rankOne` |
| Singular boundary transfer: `E_ε(T) → I` strongly, `‖E_ε(T) − I‖ = 1`, germ contrast (POINH.15) | `tendsto_boundaryTransfer_normalizedPhysicalPluckerOperator`, `norm_boundaryTransfer_normalizedPhysicalPluckerOperator_sub_id`, `limsup_scaledBoundaryTransfer_normalizedPhysicalPluckerOperator` |
| §7 cone: `C*(e_c) = C*(e_1) ≅ C_0((0,1])`, suspension ideal, endpoint sequence | `physicalPlucker_scaleGerm_cone`, `physicalPlucker_endpoint_exact_sequence` |
| §7 connecting map sends the closed unit to the winding-one class of `exp(2πit)`; the unit is common to all scale lifts | `physicalPlucker_connectingMap`, `physicalPlucker_directSubunit_noGo` |

Formal reading of §7.  The boundary map is the exponential map `n ↦ [exp(2πi n e_1)]` into path
classes of unitaries `λ + j`, `j ∈ J_T`, of the unitization; these classes are classified by
winding number (`openK₁Winding` is a bijection onto `ℤ`).

Audit.
- `lake env lean` passes with no diagnostics on `RHTower/{PhysicalPluckerConeExtension,
  PhysicalPluckerIntegralNuclearDensity, PhysicalPluckerEulerNonInsertion, PhysicalPluckerThetaLift}`
  and `HTGeometry/{BoundaryCoronaCStarAlgebra, ApertureConeCalculus, ApertureOpenHistoryIdeal,
  ApertureConeWinding, ApertureLogTranslation}`.
- Axiom audit over every declaration of these modules: 350 declarations, only `propext`,
  `Classical.choice`, `Quot.sound`.
- All modules wired once (the five aperture modules newly wired into `HTGeometry.lean`).

## Log (promotion)

- 2026-10-09: §7 instantiated for the physical density (`PhysicalPluckerConeExtension`), aperture
  modules wired, full audit; promoted to stage 3.
