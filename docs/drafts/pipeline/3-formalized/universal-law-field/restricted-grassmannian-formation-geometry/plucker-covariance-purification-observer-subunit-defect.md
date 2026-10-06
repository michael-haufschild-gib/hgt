# Pluecker covariance purification and closed-observer subunit defect

- **ID:** `ULF-PCPOS-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-PHIN-001`, `ULF-PHSF-001`, `ULF-CCRHD-001`, `ULF-MPNLIH-001`,
  `FR-PIC-1`
- **Status:** `[PAPER-PROVED] [FRAME-DEPENDENT BRIDGE] [NOT RH SELECTION] [LEAN-PROVED]`
- **Lean status:** Fully formalized, unconditionally: see the Lean certificate below.

## What was wrong first

The requested object already exists in Lean:
`primeHodgeHistoryIntegralNuclearHomotopyDefect`.  It is pre-divisor, prime-mixed,
Schatten-one, reflection-odd, and has trace `sign(t)`.  First-exit transgression reconstructs it
exactly, and its survival shift has index `-1`.  Reconstructing another tensor product
`diag(w_n) tensor A_form` would add nothing.

Two real defects remain in that object.

1. Its prime polarization is fixed at every history grade, so history and prime formation are
   separable.
2. It does not retain the full moving rank-three physical Pluecker covariance.  The fixed-edge
   object `ULF-MPNLIH-001` retains the moving null line but loses the rank-three quotient.

The construction below retains both.  Its key operation is not another producer: it purifies the
entire physical covariance before closing the history observer.  Open history keeps the integral
index.  Closing history mixes genuinely distinct Pluecker polarizations and forces operator norm
strictly below one.

## Corpus audit before formulation

`scripts/formal_tools.py research` was run for the existing integral--nuclear defect, first-exit
transgression, physical Pluecker covariance, rectangular covariance square roots, observer
closure, Bures fidelity, and direct-subunit anchors.  Exact inputs are:

- `primeHodgeHistoryIntegralNuclearHomotopyDefect_closed`: the prior global signed defect;
- `primeHodgeHistoryCurvatureFirstExitHomotopyDefect_closed`: its exact nonlinear first-exit
  reconstruction;
- `primeHodgeHistorySurvivalShiftIndex_eq_neg_one`: its open-history Fredholm charge;
- `gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three` and
  `..._ker_eq_span`: every physical packet is positive rank three with one explicit null line;
- `gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_depth_overlap`: the null lines glue
  through shared physical depth cells but move with depth;
- `summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight` and its total-mass-one theorem:
  every prime edge and depth has positive normalized source mass;
- `sum_frankensteinPluckerPacketFeature_ofReal_norm_sq_eq_spectralCovariance`: the corpus already
  has a coefficient-faithful rectangular square root of the full covariance;
- `ULF-CCRHD-001`: a different Cayley-collision state already gives a nonseparable subunit
  history record, but not the complete physical rank-three Pluecker packet;
- `ULF-DSA-003`: source subunit versus target unit is not selection until a same-boundary,
  pre-divisor completion law is proved.

Generic purification, partial trace, density-matrix purity, weighted shifts, and Fredholm index
are standard.  No novelty is claimed for those abstractions.  The corpus-specific content is that
literal full Pluecker covariances move enough to make the closed integral defect strictly subunit
while their open lift retains the already forced theta index.

## 1. Full physical covariance at one history grade

Let `j` index adjacent prime edges and let

```text
M_(n,j) in M_4(C)
```

be the literal physical Pluecker spectral matrix on packet

```text
(p_j,n), (p_j,n+1), (p_(j+1),n), (p_(j+1),n+1).
```

Let `b_(n,j)>0` be its globally normalized P-G84 block weight.  On the packet-presentation
Hilbert space

```text
P = directSum_(j>=0) C^4
```

define

```text
B_n = directSum_(j>=0) b_(n,j) M_(n,j),
tau_n = Tr(B_n),
A_n = B_n/tau_n.                                      (PCPOS.1)
```

Each `M_(n,j)` is positive rank three.  Its diagonal is bounded uniformly by the reciprocal-node
bound and the unit covariance bound.  Since `sum_j b_(n,j)<=sum_(n,j)b_(n,j)=1`, `B_n` is positive
trace class.  At least one block is nonzero, hence

```text
0<tau_n<infinity,
A_n>=0,
A_n in S_1,
Tr(A_n)=1.                                           (PCPOS.2)
```

Nothing has been averaged inside a packet: `A_n` retains all six physical minor probabilities,
the reciprocal-gap congruence, every adjacent-prime label, and the full rank-three quotient.
The direct sum is the formation presentation before shared-cell quotient, exactly where the
corpus says coefficient provenance must be kept.

## 2. Canonical purification

Let

```text
E=S_2(P)
```

be the Hilbert space of Hilbert--Schmidt operators on `P`, with inner product
`<X,Y>=Tr(X*Y)`.  Define the canonical positive square-root vector

```text
u_n=sqrt(A_n) in E.                                   (PCPOS.3)
```

Then

```text
||u_n||_2^2=Tr(A_n)=1.                               (PCPOS.4)
```

Under the canonical vectorization `S_2(P)=P tensor conjugate(P)`, the rank-one projector
`|u_n><u_n|` has reduced density

```text
Tr_(conjugate(P)) |u_n><u_n| = u_n u_n*=A_n.         (PCPOS.5)
```

Thus positivity is a phase quotient in this exact carrier, not as a universal slogan: the
purified ray loses one global phase, while partial trace reconstructs the entire positive
Pluecker covariance.  No scalar Schur statistic is substituted for it.

Every edge block of `u_n` is nonzero.  Hence `|u_n><u_n|` has nonzero cross terms between some
Hilbert--Schmidt coordinate of any two adjacent-prime edge blocks.  Prime mixing occurs before
history is closed; it is not an external tensor label.

## 3. The polarizations genuinely move

The normalized covariances at depths zero and one are distinct:

```text
A_0 != A_1.                                          (PCPOS.6)
```

Indeed, equality would imply equality of the kernels of the restrictions to every positive edge
block.  On any fixed edge `p<q`, the kernel lines of `M_(0,j)` and `M_(1,j)` are spanned by

```text
(I_p,2I_p,I_q,2I_q),
(2I_p,3I_p,2I_q,3I_q),                               (PCPOS.7)
```

where `I_r>0` is the critical Stokes inverse tilt.  The ratio of the second coordinate to the
first is respectively `2` and `3/2`, so the lines differ.  Positive rescaling by `b_(n,j)/tau_n`
does not change a kernel.  This contradicts equality and proves `(PCPOS.6)`.

Consequently the unit Hilbert--Schmidt vectors `u_0,u_1` are not collinear.  If
`u_0=c u_1`, positivity makes `c>=0`, norms make `c=1`, and squaring gives `A_0=A_1`.

## 4. One open history and one closed observer

Let theta's exact first-exit weights be

```text
w_n=630/((2n+3)(2n+5)(2n+7)(2n+9)),
sum_n w_n=1,
w_0=2/3,
w_1=2/11.                                            (PCPOS.8)
```

The coherent open-history vector is

```text
Omega=sum_(n>=0) sqrt(w_n) delta_n tensor u_n
      in ell2(N) tensor E.                            (PCPOS.9)
```

Equation `(PCPOS.4)` and `sum w_n=1` give `||Omega||=1`.  Close only the history observer:

```text
T = Tr_history |Omega><Omega|
  = sum_(n>=0) w_n |u_n><u_n|  on E.                 (PCPOS.10)
```

This is the promised single object.  It is formed before any divisor, mixes every prime edge,
and retains the full covariance through the marked purification `(PCPOS.5)`.

## Theorem PCPOS

The operator `T` satisfies

```text
T>=0,
T in S_1,
Tr(T)=||T||_1=1,
||T||<1.                                             (PCPOS.11)
```

More sharply, with

```text
F_01=|Tr(sqrt(A_0)sqrt(A_1))|=|<u_0,u_1>|<1,
```

one has

```text
||T|| <= sqrt(1-(8/33)(1-F_01^2)) < 1.              (PCPOS.12)
```

Define the signed wall family

```text
T(t)=0                         if t=0,
T(t)=sign(t) T                 otherwise.            (PCPOS.13)
```

Then

```text
T(-t)=-T(t),
T(t) in S_1,
Tr(T(t))=sign(t),
||T(t)||_1=|sign(t)|.                                (PCPOS.14)
```

### Proof of nuclearity and strict subunit norm

Every summand in `(PCPOS.10)` is positive rank one with trace norm `w_n`.  Their trace-norm sum is
one, proving convergence, positivity, nuclearity, and `Tr(T)=||T||_1=1`.

The purity is

```text
Tr(T^2)=sum_(n,k) w_n w_k |<u_n,u_k>|^2.             (PCPOS.15)
```

All overlaps have modulus at most one.  Keeping the strict loss only in the ordered pairs
`(0,1)` and `(1,0)` gives

```text
Tr(T^2)
 <= (sum_n w_n)^2-2w_0w_1(1-F_01^2)
 =1-(8/33)(1-F_01^2)<1.                              (PCPOS.16)
```

For a positive Hilbert--Schmidt operator, the square of its largest spectral value is at most the
sum of all squared spectral values, so `||T||^2<=Tr(T^2)`.  This proves `(PCPOS.12)` and the strict
part of `(PCPOS.11)`.  Equations `(PCPOS.13)--(PCPOS.14)` are immediate. QED.

The argument contains a stronger exact conservation identity.  Write

```text
Delta_(n,k)=1-|<u_n,u_k>|^2
           =det([[<u_n,u_n>,<u_n,u_k>],
                  [<u_k,u_n>,<u_k,u_k>]])
           =||u_n wedge u_k||^2.                     (PCPOS.16a)
```

Then

```text
boxed: 1-Tr(T^2)=sum_(n,k) w_n w_k Delta_(n,k).      (PCPOS.16b)
```

So observer anti-concentration is exactly total two-history Pluecker mass of the moving purified
formation.  It vanishes exactly when all positive-weight rays coincide, which is precisely the
old fixed-polarization/separable model.  This is not a curvature metaphor: both sides are named,
finite, nonnegative quantities and determine each other exactly.

## 5. Why this is a homotopy defect, not only a density

Retain the marked rays

```text
epsilon_n=delta_n tensor u_n.
```

They are orthonormal because the history coordinates are orthogonal.  On their closed span define

```text
C epsilon_n=sqrt(r_n) epsilon_(n+1),
r_n=m_(n+1)/m_n=(2n+3)/(2n+9).                       (PCPOS.17)
```

This is unitarily equivalent to the already formalized theta survival shift.  Therefore it is
Fredholm with index `-1`, and

```text
C*C-CC*=sum_n k_n |epsilon_n><epsilon_n|>=0,
Tr(C*C-CC*)=1=-index(C),                             (PCPOS.18)
```

where `k_0=r_0` and `k_n=r_n-r_(n-1)` for `n>0`.  The first-exit law reconstructs

```text
r_n=sum_(j<=n)k_j,
m_n=product_(j<n)r_j,
w_n=m_n(1-r_n).                                      (PCPOS.19)
```

Applying `(PCPOS.19)` gradewise to `(PCPOS.18)` gives the marked exit defect

```text
T_hat=sum_n w_n |epsilon_n><epsilon_n|.              (PCPOS.20)
```

History closure sends `T_hat` to `T`.  Hence one exact chain carries all five readings:

```text
theta Mellin-six loss
 = nonlinear first-exit of moving self-commutator
 = Fredholm boundary unit
 = open-history nuclear trace
 = closed-observer integral trace,
```

while strict subunit norm is created only at the final observer closure because the `u_n` are not
collinear.  This is the mechanism: index is conserved; concentration is not.

## 6. Exact RH consequence and remaining theorem

Let `P_q` be the rank-one completed escape horizon of a strict-right Xi copy.  Any positive unital
map `Phi` between the corresponding operator systems is operator-norm contractive.  Therefore

```text
Phi(T)=P_q
```

is impossible, because `(PCPOS.12)` gives `||T||<1` while `||P_q||=1`.  This is an unconditional
selection lemma for the concrete full-covariance source object, not a claim that the required map
has been constructed.

The exact RH-closing theorem is now:

```text
literal integer/Poisson completion, after the proved metric-anomaly subtraction,
commutes with Pluecker purification and history closure on Omega,
is positive and unital on the generated operator system,
and its strict-right specialization is the completed escape horizon.             (PCPOS.21)
```

If `(PCPOS.21)` is proved before supplying a divisor, no strict-right copy exists; functional
equation symmetry then gives RH.  The new object removes the previous coefficient-completeness
excuse: source side now retains full rank-three covariance, moving null lines, all prime edges,
theta history, and the integral index simultaneously.

It does not remove the same-boundary requirement.  `ULF-DSA-003` proves that merely asserting the
last line of `(PCPOS.21)` is RH-strength.  Future work must derive commutation with purification
and history closure from literal Poisson self-duality, not declare it.

## Hostile review

- `[REDISCOVERED]` Canonical purification by `sqrt(A)`, partial trace, purity formulae, and strict
  convex mixing are standard quantum information/operator theory.
- `[CORPUS COLLISION]` Pairwise dispersion/fidelity and complex Gram--Pluecker identities already
  exist abstractly in `ProjectiveWeightedCoherence` and `ComplexGramPlucker`.  New content of
  `(PCPOS.16b)` is only their application to the literal moving full-covariance Euler/theta
  history, not the algebraic identity itself.
- `[REDISCOVERED]` The weighted-shift index and self-commutator trace are classical and already in
  the corpus.
- `[CORPUS COLLISION]` `ULF-CCRHD-001` already builds a nonseparable subunit collision history.
  PCPOS differs only by retaining the complete physical Pluecker covariance and proving strictness
  from its moving kernel.
- `[FRAME AUDIT FAILURE]` The theorem does not solve `MUST-174` intrinsically.  Its overlap
  `Tr(sqrt(A_0)sqrt(A_1))` compares two depth covariances in one fixed packet presentation.
  Source-derived depth-dependent fibre transports can change that overlap and can align arbitrary
  purifications.  The bound is invariant under one common unitary, not under the full local gauge
  freedom already proved by `frankensteinPluckerReporterTransport_metricNorm`.
- `[POSITIVE SURVIVOR]` Full rank-three covariance and integral history coexist without losing
  trace conservation in a declared fixed presentation.  The coordinate-free replacement is
  `ULF-POINH-001`: normalize the already-glued physical-overlap operator and derive strictness
  from same-packet rank three, so no cross-depth frame comparison occurs.
- `[LIMIT]` No ordinary normal channel, trace preservation, scalar moment match, or zero Schur
  short can turn `(PCPOS.11)` into selection.  Only source-derived unital-positive same-boundary
  descent can use the norm gap.
- `[FALSIFIER]` If normalized Pluecker covariances at depths zero and one had the same fixed-edge
  kernel, `(PCPOS.6)` would fail.  The exact kernel vectors `(PCPOS.7)` rule this out.

## Literature boundary

Square-root-density/Fisher sphere geometry, purifications, Toeplitz index theory, and trace-class
commutator formulae are established subjects.  Relevant primary sources include Holbrook--Lan--
Streets--Shahbaba on square-root density geometry (<https://arxiv.org/abs/1707.03117>),
Gesztesy--Latushkin--Makarov--Sukochev--Tomilov on relative trace-class index
(<https://arxiv.org/abs/1004.1582>), and Berkani on commutator trace formulae
(<https://arxiv.org/abs/1609.01695>).  No checked source gives the source-specific Pluecker/theta
fusion `(PCPOS.1)--(PCPOS.20)`.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.FrameOperatorPurity`, `GaloisForLFunctions.RHTower.PluckerCovarianceSquareRootPurification`, `GaloisForLFunctions.RHTower.PluckerCovarianceObserverSubunitDefect`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.FrameOperatorPurity` (frame-operator purity, Gram
determinants, the positive square root), `GaloisForLFunctions.RHTower.PluckerCovarianceSquareRootPurification`
(§1–§3) and `GaloisForLFunctions.RHTower.PluckerCovarianceObserverSubunitDefect` (§4–§6).  The
physical objects are the corpus ones: the spectral blocks `gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock`
(positive semidefinite, rank three, explicit one-dimensional kernel), the block weights
`gammaSewnCriticalAdjacentPrime_PluckerBlockWeight` (positive, total mass one), their rank-one
decomposition into centered node features, the theta first-exit weights `PrimeHodgeHistory.w`, the
survival shift `primeHodgeHistorySurvivalShift` (index `-1`) and its relative curvature operator.
The packet presentation is `P = ℓ²(ℕ × Fin 4) = ⊕_j ℂ⁴`; `S₂(P)` is realized by columns as
`ℓ²(ℕ × Fin 4; P)` with `⟨u, v⟩ = ∑_k ⟨u e_k, v e_k⟩ = Tr(u* v)`.  Names with the
prefix `HedenmalmThetaSource.` live in that namespace under RHTower; unprefixed names are the
generic frame-operator lemmas of the HTGeometry namespace.

| Claim | Lean declaration |
|-|-|
| (PCPOS.1) `M_{n,j}`, `b_{n,j}`, `B_n = ⊕_j b_{n,j} M_{n,j}` (frame operator of the rays `√(b π) F`, block formula) | `HedenmalmThetaSource.packetBlock`, `HedenmalmThetaSource.packetWeight`, `HedenmalmThetaSource.packetProbability`, `HedenmalmThetaSource.packetFeature`, `HedenmalmThetaSource.packetBlock_eq`, `HedenmalmThetaSource.packetBlockFeature`, `HedenmalmThetaSource.packetBlockFeature_apply`, `HedenmalmThetaSource.packetRay`, `HedenmalmThetaSource.packetCovariance`, `HedenmalmThetaSource.packetCovariance_apply` |
| (PCPOS.1)–(PCPOS.2) every block positive rank three with bounded diagonal; `B_n ≥ 0`, trace class, `τ_n = Tr B_n = ∑_j b_{n,j} Tr M_{n,j} > 0` | `HedenmalmThetaSource.gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three`, `HedenmalmThetaSource.packetBlock_diag_le`, `HedenmalmThetaSource.sum_norm_sq_packetRay`, `HedenmalmThetaSource.summable_norm_sq_packetRay`, `HedenmalmThetaSource.exists_packetRay_ne_zero`, `HedenmalmThetaSource.packetTraceMass`, `HedenmalmThetaSource.packetTraceMass_pos`, `HedenmalmThetaSource.packetCovariance_traceClass` |
| (PCPOS.1)–(PCPOS.2) `A_n = B_n/τ_n ≥ 0`, `A_n ∈ S₁`, `Tr A_n = 1`, block formula | `HedenmalmThetaSource.normalizedPacketRay`, `HedenmalmThetaSource.normalizedPacketCovariance`, `HedenmalmThetaSource.normalizedPacketCovariance_eq`, `HedenmalmThetaSource.normalizedPacketCovariance_apply`, `HedenmalmThetaSource.normalizedPacketCovariance_density`, `HedenmalmThetaSource.tsum_norm_sq_normalizedPacketRay` |
| (PCPOS.3) `u_n = √A_n ∈ S₂(P)` | `positiveSqrt`, `HedenmalmThetaSource.sqrtPacketCovariance`, `HedenmalmThetaSource.sqrtPacketCovariance_isPositive`, `HedenmalmThetaSource.sqrtPacketCovariance_mul_self`, `HedenmalmThetaSource.adjoint_sqrtPacketCovariance`, `HedenmalmThetaSource.PacketHilbertSchmidt`, `HedenmalmThetaSource.purifiedCovariance`, `HedenmalmThetaSource.inner_purifiedCovariance` |
| (PCPOS.4) `‖u_n‖₂² = Tr A_n = 1` | `HedenmalmThetaSource.norm_sq_sqrtPacketCovariance_apply`, `HedenmalmThetaSource.summable_norm_sq_sqrtPacketCovariance_basis`, `HedenmalmThetaSource.tsum_norm_sq_sqrtPacketCovariance_basis`, `HedenmalmThetaSource.norm_purifiedCovariance` |
| (PCPOS.5) partial trace of `|u_n⟩⟨u_n|` over the column factor is `u_n u_n* = A_n` | `frameOperator_columns`, `purifiedCovariance_isPartialTrace` |
| §2 every edge block of `u_n` is nonzero; `|u_n⟩⟨u_n|` couples any two adjacent-prime edge blocks | `exists_purifiedCovariance_edge_ne_zero`, `exists_purified_crossEdge_coefficient_ne_zero` |
| (PCPOS.6)–(PCPOS.7) kernel lines `(I, 2I, …)` at depth 0 and `(2I, 3I, …)` at depth 1 differ; `A_0 ≠ A_1` | `HedenmalmThetaSource.packetKernelVector_apply`, `HedenmalmThetaSource.packetKernelVector_depth_zero_one`, `HedenmalmThetaSource.packetKernelVector_not_proportional`, `HedenmalmThetaSource.normalizedPacketCovariance_zero_ne_one` |
| §3 `u_0, u_1` not collinear; `F₀₁ = |⟨u_0, u_1⟩| < 1` | `sqrtPacketCovariance_eq_of_purified`, `purifiedCovariance_not_collinear`, `fidelity_lt_one`, `pluckerFidelity` |
| (PCPOS.8) `w_n = 630/((2n+3)(2n+5)(2n+7)(2n+9))`, `∑ w_n = 1`, `w_0 = 2/3`, `w_1 = 2/11` | `PrimeHodgeHistory.w_formula`, `PrimeHodgeHistory.tsum_w`, `PrimeHodgeHistory.w_zero`, `HedenmalmThetaSource.thetaWeight_one` |
| (PCPOS.9) `Ω = ∑ √w_n δ_n ⊗ u_n`, `‖Ω‖ = 1` | `HedenmalmThetaSource.observerRay`, `HedenmalmThetaSource.norm_sq_observerRay`, `HedenmalmThetaSource.openHistory`, `HedenmalmThetaSource.norm_openHistory` |
| (PCPOS.10) `T = Tr_history |Ω⟩⟨Ω| = ∑ w_n |u_n⟩⟨u_n|` | `closedObserverDefect`, `closedObserverDefect_eq_tsum`, `closedObserverDefect_isPartialTrace` |
| Theorem PCPOS, (PCPOS.11) `T ≥ 0`, `T ∈ S₁`, `Tr T = ‖T‖₁ = 1`, `‖T‖ < 1` | `HedenmalmThetaSource.closedObserverDefect_density`, `HedenmalmThetaSource.norm_closedObserverDefect_lt_one`, `frameOperator_isPositive`, `opTrace_frameOperator`, `traceNorm_frameOperator` |
| (PCPOS.12), (PCPOS.15)–(PCPOS.16) `Tr T² = ∑ w_n w_k |⟨u_n,u_k⟩|² ≤ 1 - (8/33)(1 - F₀₁²)`, `‖T‖² ≤ Tr T²`, `‖T‖ ≤ √(1 - (8/33)(1 - F₀₁²)) < 1` | `observerPurity`, `opTrace_closedObserverDefect_sq`, `inner_observerRay`, `norm_inner_observerRay_sq`, `observerPurity_le`, `norm_closedObserverDefect_le`, `opTrace_frameOperator_sq`, `norm_frameOperator_sq_le` |
| (PCPOS.13)–(PCPOS.14) signed wall: odd, `T(0) = 0`, `S₁`, `Tr T(t) = sign t`, `‖T(t)‖₁ = |sign t|` | `signedObserverWall`, `signedObserverWall_laws` |
| (PCPOS.16a) `Δ_{n,k} = 1 - |⟨u_n,u_k⟩|²` is the `2×2` Gram determinant | `historyDispersion`, `historyDispersion_eq_gram`, `frameGramDeterminant`, `frameGramDeterminant_eq_det` |
| (PCPOS.16b) `1 - Tr T² = ∑ w_n w_k Δ_{n,k}`; it vanishes iff all `Δ_{n,k} = 0` iff the rays coincide; here it is positive | `HedenmalmThetaSource.one_sub_observerPurity`, `one_sub_framePurity`, `HedenmalmThetaSource.one_sub_observerPurity_eq_zero_iff`, `HedenmalmThetaSource.historyDispersion_eq_zero_iff` |
| (PCPOS.17) marked rays `ε_n = δ_n ⊗ u_n` orthonormal; `C = J C_θ J*`, `C ε_n = √r_n ε_{n+1}`, `r_n = (2n+3)/(2n+9)`, `C J = J C_θ`, `ind C_θ = -1` | `HedenmalmThetaSource.markedRay`, `HedenmalmThetaSource.markedRay_orthonormal`, `HedenmalmThetaSource.markedEmbedding`, `HedenmalmThetaSource.markedEmbedding_single`, `HedenmalmThetaSource.adjoint_markedEmbedding_comp`, `HedenmalmThetaSource.markedShift`, `HedenmalmThetaSource.markedShift_comp_embedding`, `HedenmalmThetaSource.markedShift_ray`, `primeHodgeHistorySurvivalShiftIndex_eq_neg_one` |
| (PCPOS.18) `C*C - CC* = ∑ k_n |ε_n⟩⟨ε_n| ≥ 0`, trace class, `Tr = 1 = -ind` | `relativeCurvatureOperator_apply`, `markedSelfCommutatorRecord`, `markedShift_selfCommutator`, `markedSelfCommutator_traceClass` |
| (PCPOS.19) `r_n = ∑_{j≤n} k_j`, `m_n = ∏_{j<n} r_j`, `w_n = m_n(1 - r_n)` | `HedenmalmThetaSource.firstExit_reconstruction` |
| (PCPOS.20) `T̂ = ∑ w_n |ε_n⟩⟨ε_n|`: positive, `S₁`, `Tr T̂ = 1`, `T̂ ε_n = w_n ε_n`, history closure sends `T̂` to `T` | `markedExitDefect`, `markedExitDefect_laws`, `recordOp_eq_frameOperator`, `recordOp_isPartialTrace` |
| §6 a positive unital map on an operator system is contractive on positive elements and never sends `T` to an operator of norm one | `HedenmalmThetaSource.norm_le_of_positive_unital`, `HedenmalmThetaSource.positive_unital_ne_of_norm_eq_one` |

The opening audit, (PCPOS.21) (the open same-boundary completion theorem, stated as the remaining
target and not claimed), the hostile review and the literature boundary are commentary.

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
