# Zero-distance / infinite-action formation defect

- **ID:** ULF-ZDIA-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-CAGC-001`, `ULF-OCSE-001`
- **Purpose:** locate the atomic--continuum distinction after ordinary output distance has
  collapsed.  Literal Euler atoms are approximable by continuum synthesis but require continuum
  source norm tending to infinity.

## 1. Big-picture reversal

The completed Burnol Hilbert space does not see Euler formation as a positive residual subspace.
The continuum synthesis is dense, so that residual is zero.  It sees Euler formation as a
**singular inverse-completion action**: a discrete Laplace measure can be approximated by
absolutely continuous measures after synthesis, but never represented by one with finite source
energy.

Thus the missing relative completion is not a quotient metric.  It is the renormalized graph norm
of an unbounded inverse to a compact dense-range formation map.

## 2. Source synthesis

Fix `x,c>0` and put

```text
m(lambda)
  = exp(-pi*x*exp(2*lambda)/2)
      *(1-exp(-2*c*lambda))^(3/2),
f_lambda(r)=r exp(-lambda*r).
```

Let

```text
A_0 : L2((0,infinity),d lambda) -> H_B,
(A_0 b)(r)=integral b(lambda)m(lambda)f_lambda(r)d lambda. (ZDIA.1)
```

`ULF-CAGC-001` proves `A_0` Hilbert--Schmidt.  `ULF-OCSE-001` proves it has dense range.

The multiplier `m` is strictly positive on `(0,infinity)` and belongs to `L2`: near zero it is
`O(lambda^(3/2))`, and at infinity it has double-exponential decay.

## 3. Theorem ZDIA-A: compact, injective, dense, nonsurjective

`A_0` is compact, injective, has dense range, and is not surjective.

**Proof.** Hilbert--Schmidt operators are compact, and density was proved in `ULF-OCSE-001`.
If `A_0 b=0`, divide `(ZDIA.1)` by `r>0`.  Since `b*m` belongs to `L1` by
Cauchy--Schwarz, the Laplace transform of the finite complex measure

```text
b(lambda)m(lambda)d lambda
```

vanishes on every positive `r`.  Laplace uniqueness gives `b*m=0` almost everywhere.  Strict
positivity of `m` gives `b=0`, so `A_0` is injective.

It cannot be surjective: a compact surjection between Banach spaces is open, which would make the
unit ball of the infinite-dimensional `H_B` relatively compact.  QED.

Consequently the inverse

```text
G_0=A_0^(-1) : Ran(A_0) subset H_B -> L2(d lambda)     (ZDIA.2)
```

is a closed, densely defined, unbounded operator.  This is the continuum completion graph.

## 4. Theorem ZDIA-B: Euler atoms are outside the actual range

For every active integer label `n>=2` with `Lambda(n)>0`, let

```text
y_n=a_(n,x,c) f_(log n),
a_(n,x,c)
  = sqrt(Lambda(n)/n)*exp(-pi*x*n^2/2)
      *(1-n^(-2*c))^(3/2).
```

More generally, if `F` is a finite set of active labels and not all `z_n` vanish, then

```text
y_F=sum_(n in F) z_n y_n notin Ran(A_0).              (ZDIA.3)
```

**Proof.** If `y_F=A_0b`, division by `r` identifies Laplace transforms of the finite complex
measures

```text
b(lambda)m(lambda)d lambda
  and
sum_(n in F) z_n a_(n,x,c) delta_(log n).             (ZDIA.4)
```

Laplace uniqueness makes these measures equal.  The first is absolutely continuous; the second
is supported on finitely many points.  Mutual singularity forces both to vanish.  Since `m>0`
almost everywhere and each active `a_n>0`, `b=0` and every `z_n=0`, contradiction.  QED.

Together with dense range, `(ZDIA.3)` says

```text
dist(y_F,Ran(A_0))=0 but y_F notin Ran(A_0).           (ZDIA.5)
```

## 5. Theorem ZDIA-C: every approximating lift has infinite action

Let `y notin Ran(A_0)`.  If

```text
A_0 b_j -> y in H_B,
```

then

```text
||b_j|| -> infinity.                                  (ZDIA.6)
```

**Proof.** Otherwise some subsequence has bounded norm.  Hilbert reflexivity supplies a weakly
convergent subsubsequence `b_j -> b`.  Compactness of `A_0` upgrades this to
`A_0 b_j -> A_0 b` in norm.  The assumed norm limit is `y`, hence `y=A_0b`, contradiction.  QED.

Equivalently, define the approximation action

```text
L_epsilon(y)
  = inf {||b||^2 : ||A_0 b-y||<=epsilon}.              (ZDIA.7)
```

Dense range makes `L_epsilon(y)` finite for every `epsilon>0`; for every nonzero finite Euler
packet,

```text
L_epsilon(y_F) -> infinity as epsilon downarrow 0.     (ZDIA.8)
```

This divergence is intrinsic: no choice of approximating continuum packet removes it.

## 6. Canonical nuclear regularization

Let

```text
K_0=A_0 A_0*,
C_epsilon=A_E* (K_0+epsilon*I)^(-1) A_E.              (ZDIA.9)
```

For every `epsilon>0`, `C_epsilon` is a positive trace-class operator on the complete Euler label
space and

```text
Tr C_epsilon
  <= epsilon^(-1) ||A_E||_HS^2
  <= epsilon^(-1) B_base.                             (ZDIA.10)
```

It is matrix-complete: the `(n,m)` entry is

```text
<y_n,(K_0+epsilon*I)^(-1)y_m>,                         (ZDIA.11)
```

so regularization occurs after the full atomic family has interacted with one continuum
covariance, not prime by prime.

By the spectral theorem and `Ran(K_0^(1/2))=Ran(A_0)`, every active diagonal diverges:

```text
<y_n,(K_0+epsilon*I)^(-1)y_n> -> infinity.             (ZDIA.12)
```

Thus `C_epsilon` is the canonical pre-divisor, prime-mixed **nuclear lift-action family**.  Its
divergence, not an orthogonal residual, is what a relative completion must renormalize.

## 7. Corpus interpretation

This theorem explains four previously separate shadows:

1. `continuousL2Mul_operatorFamiliesDisjoint_of_mutuallySingular`: atomic and continuum label
   representations are disjoint before completion.
2. `continuousBoundaryReporter_eq_zero_of_cyclicDenseRange`: ordinary continuous completed
   reporters erase the distinction.
3. `twoSidedSingular_iff_hasProperClosedBiDenseSubspace`: a proper defect can remain bi-dense only
   as singular graph data, not as a closed output summand.
4. `sourceHorizontalEulerGammaCubicNegativeRenormalizedChannel_producer`: the corpus already has
   a literal coefficientwise Wold subtraction of a divergent cubic Euler current, leaving a
   summable defect.  That is exactly the shape required to renormalize `(ZDIA.9)`.

## 8. Exact remaining law after the orientation audit

The proved family `(ZDIA.9)` is positive and nuclear for each regulator, but its finite part has
not been identified.  A theta-forced, coefficientwise counterterm `W_epsilon` derived from
integer/Poisson self-duality may still produce

```text
C_epsilon-W_epsilon -> C_rel in S_1,                  (ZDIA.13)
```

but `ULF-CFPO-001` proves that `C_rel` is necessarily orientation-even if the counterterm is
constructed from covariance alone.  Therefore the former proposed equation

```text
Ch_3(C_rel)=mathsf T_D
```

is retired: an even metric datum cannot produce the odd winding index.

The surviving theorem must have a second, independently source-derived input.  Let `j_EG` denote
the literal reflection-odd prime--Gamma/Maurer--Cartan current, before any divisor.  Required is a
bivariant boundary law

```text
Theta_D(C_rel,j_EG)=mathsf T_D,                        (ZDIA.14)
```

followed by positive finite-part domination

```text
0<=Tr mathsf T_D<=Tr K_E<B_base<1.                   (ZDIA.15)
```

`(ZDIA.13)` is not allowed to use one prime-independent scalar counterterm: corpus ghost rigidity
already makes that RH-equivalent.  It must be the operator-valued Wold/Poisson subtraction forced
on the common label-measure cone.

## Hostile audit

1. Density alone does not produce a source lift; it produces divergent lift action.
2. Mutual singularity proves range exclusion only for nonzero finite active Euler packets here;
   no claim is made for every infinite `ell2` packet.
3. `C_epsilon` is not integral and cannot generate orientation.  Integrality belongs to the
   bivariant boundary pairing with a source-native odd current.
4. Subtracting an arbitrary divergent diagonal would be renormalization theatre.  Counterterm and
   finite-part positivity remain open.

## Status

Paper proof dependency-closed.  `[LEAN-PROVED]`: §§2–6, including the parent density of `Ran A₀`, certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity`, `GaloisForLFunctions.HTGeometry.ContinuumFormationDefect`, `GaloisForLFunctions.HTGeometry.CubicApertureGaugedSynthesis`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules: `GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity` (Laplace rigidity of an `L¹` density against finitely many
atoms; Laplace continuity and uniqueness on `L¹`) and `GaloisForLFunctions.HTGeometry.ContinuumFormationDefect` (all theorems
of §§2–6), on top of the corpus cubic-gauged synthesis `GaloisForLFunctions.HTGeometry.CubicApertureGaugedSynthesis`
(`continuumSynthesis` = `A₀`, `atomicSynthesis` = `A_E`, `cubicGaugeWeight` = `m`, Hilbert–Schmidt proofs). Every module is clean
under `lake env lean`, builds as a module, and the axiom audit shows only `[propext, Classical.choice, Quot.sound]`.
The density of `Ran A₀` (the parent claim of `ULF-OCSE-001`, previously unformalized) is proved here: the columns `r e^{-λr}`
are total by Laplace uniqueness, so `A₀*` is injective. Laplace uniqueness for finite measures is the corpus
`measure_eq_of_laplace_eq`; the atomic/continuous separation splits positive and negative parts into two finite measures
and evaluates on and off the atoms. The `(K₀+ε)⁻¹` resolvent is `Ring.inverse`, with invertibility from the Fredholm
alternative for the compact positive `K₀ = A₀A₀*`; its positivity and the divergence (ZDIA.12) come from the Tikhonov identity
`Re⟪y,(K₀+ε)⁻¹y⟫ = ‖A₀*u‖² + ε‖u‖²`, `A₀(A₀*u) - y = -εu`.

| Claim | Lean declaration |
|-|-|
| (ZDIA.1) `A₀ b = r ↦ r ∫ b(s)m(s)e^{-sr} ds`; `m > 0`, `m ∈ L²`, `bm ∈ L¹` | `labelDensity`, `labelLaplace`, `continuumSynthesis_coeFn`, `memLp_gauge`, `cubicGaugeWeight_sq_le_exp`, `integrable_labelDensity`, `integrableOn_labelDensity`, `continuousOn_labelLaplace`, `radialLp`, `memLp_burnolRadial`, `radialLp_coeFn` |
| Laplace rigidity: `L¹` density vs finitely many atoms; Laplace continuity and uniqueness on `L¹` | `laplaceSplitMeasure`, `laplace_atomic_rigidity_real`, `laplace_atomic_rigidity`, `integrableOn_mul_exp`, `continuousOn_laplace`, `ae_eq_zero_of_laplace_ae_eq_zero` |
| Theorem ZDIA-A: injective | `continuumSynthesis_eq_atoms`, `continuumSynthesis_injective` |
| Theorem ZDIA-A: dense range (OCSE-A totality of `f_λ`, `A₀*` injective) | `radialPairing`, `inner_radialLp`, `eq_zero_of_radialPairing_ae_eq_zero`, `adjoint_continuumSynthesis_coeFn`, `denseRange_continuumSynthesis` |
| Theorem ZDIA-A: compact, not surjective | `isCompactOperator_continuumSynthesis`, `not_surjective_continuumSynthesis`, `two_mem_active` |
| (ZDIA.2) `G₀ = A₀⁻¹` closed, densely defined, unbounded | `continuumInverse`, `continuumInverse_closed_dense_unbounded` |
| Theorem ZDIA-B (ZDIA.3)–(ZDIA.4) nonzero finite active Euler packets are outside `Ran A₀` | `eulerColumn`, `log_injOn_atomLabel`, `continuumSynthesis_eq_atoms`, `eulerPacket_not_mem_range` |
| (ZDIA.5) `dist(y_F, Ran A₀) = 0` | `infDist_range_eq_zero` |
| Theorem ZDIA-C (ZDIA.6) `A₀b_j → y ∉ Ran A₀` forces `‖b_j‖ → ∞` | `tendsto_norm_atTop_of_tendsto_not_mem_range` |
| (ZDIA.7)–(ZDIA.8) approximation action finite for `ε > 0`, divergent as `ε ↓ 0` on Euler packets | `liftAction`, `liftAction_spec`, `tendsto_liftAction`, `tendsto_liftAction_eulerPacket` |
| (ZDIA.9) `C_ε = A_E*(K₀+ε)⁻¹A_E` positive and a product of Hilbert–Schmidt operators | `isUnit_add_smul_one_of_compact`, `isUnit_continuumCovariance_add`, `isPositive_resolvent`, `nuclearLiftAction`, `nuclearLiftAction_spec` |
| (ZDIA.10) `0 ≤ Tr C_ε ≤ ε⁻¹‖A_E‖²_HS ≤ ε⁻¹ B_base` | `norm_shiftedResolvent_le`, `re_inner_self_complex`, `im_inner_self_complex`, `nuclearLiftAction_spec` |
| (ZDIA.11) entries `⟪y_n,(K₀+ε)⁻¹y_m⟫`, `A_E e_n = y_n` | `labelBasisVec`, `atomicSynthesis_labelBasisVec`, `inner_nuclearLiftAction` |
| (ZDIA.12) every active diagonal diverges | `tikhonov_identity`, `tendsto_resolventPairing`, `tendsto_nuclearLiftAction_diag` |

§7 is corpus interpretation; §8 states open laws (ZDIA.13)–(ZDIA.15), not claims of this card.

## Log

- 2026-10-03 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
