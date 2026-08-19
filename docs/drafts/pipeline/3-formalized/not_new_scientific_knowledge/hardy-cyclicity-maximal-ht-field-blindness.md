# Hardy cyclicity blindness inside one maximal HT power pro-field

- **ID:** `hardy-cyclicity-maximal-ht-field-blindness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; Hardy cyclicity; Nyman--Beurling boundary
- **Statement:** A bounded outer carrier with a maximally free parabolic differential orbit and all
  of its finite Blaschke multiples have exactly the same differential-orbit field and complete
  power pro-field, while their Hardy cyclicity defects attain every finite dimension.

## Goal

Test whether maximal hypertranscendence, strengthened by the entire algebraic power hierarchy, can
intrinsically determine Hardy cyclicity.  The theorem gives an exact negative answer.  It constructs
actual functions in one fixed `H^2(D)`, not abstract isomorphic fields, for which every recorded HT
field is literally equal while the cyclic subspace has arbitrary finite codimension.

## Setup

Let `m` be a positive Herglotz function supplied by the full-translation theorem in
`herglotz-full-translation-ht-krein-index-orthogonality.md`: `m` is holomorphic on the upper
half-plane, `Im m(z)>0` there, and

`{m(z+h):h in C}`

is differentially algebraically independent over `C(z)`.  Define

`phi(w)=i(1+w)/(1-w)`,

`c(x)=(x-i)/(x+i)`,

`sigma(w)=c(m(phi(w)))`,

`O(w)=exp(sigma(w))`.                                           (1)

For real `t`, put

`tau_t=phi^(-1) o (z |-> z+t) o phi`.                           (2)

Thus `tau_t` is a rational disk automorphism and

`phi(tau_t(w))=phi(w)+t`.                                       (3)

Let `B` be a finite Blaschke product of degree `k`, with the constant unimodular product allowed
when `k=0`, and set

`G_B=B O`.                                                      (4)

All differential fields below use `D=d/dw` and base field `K=C(w)`.  Define the full parabolic
orbit fields and their power levels by

`P_N(f)=K< (f o tau_t)^N : t in R >`, `N>=1`.                  (5)

The angle brackets denote differential-field generation.

## Theorem `[PROVED HERE]`

For the carrier `O` in (1):

1. `O,O^(-1) in H^infinity(D)`, and `O` is outer and cyclic in `H^2(D)`.
2. The family `{O o tau_t:t in R}` is differentially algebraically independent over `K`.
3. For every finite Blaschke product `B` and every `N>=1`,

   `P_N(G_B)=P_N(O)`                                           (6)

   as literal differential subfields of the meromorphic functions on `D`.  These equalities
   commute with all transition inclusions, so the complete inverse power systems are identical.
4. If `[f]` denotes the closed polynomial cyclic subspace of `f` in `H^2(D)`, then

   `[O]=H^2(D)`, ` [G_B]=B H^2(D)`,

   `dim(H^2(D) minus [G_B])=k`.                                (7)

Consequently one and the same unpointed maximal-HT power pro-field is compatible with Hardy
cyclicity defect `0,1,2,...`.

## Proof

### 1. The bounded outer carrier

Every summand of the positive Cauchy-atom construction of `m` has strictly positive imaginary part
on the upper half-plane.  Hence `Im m(z)>0`.  The Cayley transform maps the upper half-plane into
the open unit disk, so

`|sigma(w)|<1` for `w in D`.                                   (8)

In particular,

`exp(-1)<|O(w)|<exp(1)`.                                       (9)

Thus `O` and `O^(-1)` belong to `H^infinity(D)`.  Moreover `O=exp(sigma)` with bounded analytic
`sigma`.  The real part of `sigma` is the Poisson extension of its essentially bounded boundary
values, so the standard exponential representation for outer functions shows that `O` is outer,
up to its harmless unimodular constant.  Equivalently, an invertible `H^infinity` function has no
nonconstant inner factor.  Beurling's cyclicity theorem then gives `[O]=H^2(D)`.

### 2. Parabolic maximal hypertranscendence

Take distinct real numbers `t_1,...,t_r`.  The corresponding functions

`m(phi(w)+t_j)`                                                (10)

are differentially algebraically independent over `K`.  Indeed, the original full complex
translation theorem applies to the distinct shifts `t_j`.  Rational substitution `z=phi(w)` is an
isomorphism of differential-rational function fields after transporting the derivation: repeated
`w`-derivatives and repeated `z`-derivatives are related by an invertible triangular chain-rule
matrix whose order-`n` diagonal coefficient is `phi'(w)^n`.  A differential relation after
substitution would therefore pull back to one among the original translates.

By (3),

`sigma o tau_(t_j)=c(m(phi(w)+t_j))`.                           (11)

The codomain Cayley map `c` is invertible rationally.  Hence the finite family in (11) is also
differentially algebraically independent.  Its derivative family

`{D(sigma o tau_(t_j)):1<=j<=r}`                               (12)

is differentially algebraically independent as well: any differential-polynomial relation among
the derivatives is already a differential-polynomial relation among the original functions, using
only positive-order jets.

Write `O_j=O o tau_(t_j)`.  Logarithmic differentiation gives

`D O_j/O_j=D(sigma o tau_(t_j))`.                              (13)

Therefore `K<O_1,...,O_r>` contains the `r` differentially algebraically independent elements in
(12), and its differential transcendence degree is at least `r`.  A differential field generated
by `r` elements has differential transcendence degree at most `r`; equality follows.  Thus the
`O_j` are differentially algebraically independent.  Since the finite real shift set was arbitrary,
the full parabolic orbit is differentially algebraically independent.

### 3. Equality of every power level

Because both `B` and `tau_t` are rational,

`q_t=B o tau_t in K^*`.                                       (14)

For every `N>=1`,

`(G_B o tau_t)^N=q_t^N (O o tau_t)^N`.                         (15)

The multiplier `q_t^N` and its inverse lie in the base field.  Thus each generator on either side
of (6) belongs to the field generated by the other side, proving literal equality.  Since this is
termwise equality inside one ambient differential field, it respects every divisibility transition
`P_M(f) subset P_N(f)` when `N|M`.  It also makes all intersections, logarithmic-derivative
residues, differential matroids, and finite or infinite collections of power levels identical.

### 4. Exact cyclicity defect

Multiplication by the inner function `B` is an isometry of `H^2(D)` onto the closed subspace
`B H^2(D)`.  Using the cyclicity of `O`,

`[G_B]=closure{p B O:p polynomial}`

`     =B closure{p O:p polynomial}`

`     =B H^2(D)`.                                              (16)

The orthogonal complement `K_B=H^2(D) minus B H^2(D)` is the finite model space of `B`.  A finite
Blaschke product of degree `k` has exactly `k` zeros counted with multiplicity, and the corresponding
reproducing kernels, with derivative kernels for repeated zeros, form a basis of `K_B`.  Hence
`dim K_B=k`, which proves (7) and the theorem. `QED`

## Law extracted

**Hardy gauge-blindness law.**  Maximal differential freedom and the entire algebraic power
normalization hierarchy are invariant under rational inner gauge, whereas Hardy cyclicity records
the inner divisor exactly.  Therefore cyclicity is not an intrinsic invariant of the unpointed HT
power pro-field, even when that pro-field is realized by bounded analytic functions in one fixed
Hardy space and carries the full real parabolic orbit.

The law is stronger than the bare observation that multiplication by a rational function preserves
a differential field: it keeps every power level and maximal orbit independence simultaneously,
while the analytic defect is exact and unbounded.  Its proof mechanism is nevertheless a direct
assembly of classical parent theories, so it is a bridge rather than new scientific knowledge.

## RH-route consequence

The theorem rules out the following implementation claim:

> A Nyman--Beurling, Mellin--Hardy, or shift-cyclicity selector can be recovered canonically from an
> unpointed maximal-HT differential orbit field, from all of its algebraic power levels, or from the
> complete inverse system and its logarithmic-derivative residue.

Such data cannot distinguish defect `0` from defect `k` for any finite `k`.  The result does **not**
refute the Nyman--Beurling criterion and does not prove that a distinguished zeta multiplier is
noncyclic.  The classical criterion carries a pointed arithmetic vector, Mellin normalization, and
Euler/source information.  Any viable RH application must use one of those markings, or another
structure that is not functorially reconstructible from the unpointed HT power pro-field.

## Parent-theory and novelty verdict

- `[SEARCH]` Beurling's invariant-subspace theorem identifies cyclic vectors of the unilateral
  shift on `H^2(D)` with outer functions.  A modern extension explicitly states the same
  cyclic-vector/outer-function corollary: `https://arxiv.org/abs/1606.09143`.
- `[SEARCH]` Finite Blaschke products and their degree are classical; see Garcia--Mashreghi--Ross,
  `https://arxiv.org/abs/1512.05444`.
- `[SEARCH]` Burnol's quantitative Nyman formulation confirms that the actual RH criterion is a
  closure/projection statement for a distinguished arithmetic subspace, not an unpointed field
  invariant: `https://arxiv.org/abs/math/9910055`.
- `[BRIDGE]` The maximal parabolic HT carrier is transported from the separately proved Herglotz
  full-translation theorem.  Rational gauge invariance then makes (6) immediate at every level.

The exact combination is useful for route exclusion, but the proof introduces no mechanism beyond
the Herglotz carrier theorem, rational gauge, and classical inner--outer/model-space theory.  It
therefore fails the parent-theory and anti-theatre novelty gates and is not new scientific knowledge.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/CayleySchur.lean` proves the pointwise Herglotz-to-Schur Cayley bound,
its strict upper-half-plane version, finite Blaschke boundedness, and finite Szego-kernel positivity.
The repository does not define analytic `H^2(D)`, boundary inner--outer factorization, closed cyclic
subspaces, Beurling's theorem, model spaces, or maximal differential independence under rational
change of variable.  Those missing layers carry the theorem.  No partial formalization is promoted,
and stage 3 remains unavailable until the complete unconditional statement is formalized in Lean.

## Gates

- [x] 0 -> 1: exact Hardy model, proof route, and RH boundary isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] 2 -> 3: complete unconditional theorem formalized in Lean (2026-08-19)
- [ ] 3 -> 4: optional bridge publication/integration

## Log

- 2026-07-11 -- Chosen after nonlinear prime-source isolation and Beurling generalized-prime fakes
  were found to occupy existing lanes.  This card targets actual Hardy cyclicity.
- 2026-07-11 -- Proved bounded outerness, parabolic-orbit differential independence, equality of
  every power level under finite Blaschke gauge, and exact model-space codimension.
- 2026-07-11 -- Downgraded after the novelty attack: the Hardy defect mechanism is classical
  Beurling/inner--outer theory, so the exact HT coupling is a route-exclusion bridge rather than new
  scientific knowledge.

## Lean status update (2026-08-19) — statements 1 and 4 are formalized

The "Lean status" section above is superseded.  An analytic `H²(D)` layer has been built from
scratch and statements `1` and `4` (equations `(16)` and `(7)`) are now unconditional Lean
theorems.  All new declarations `#print axioms` to `propext, Classical.choice, Quot.sound` only.
Modules (all in `formal/GaloisForLFunctions/HTGeometry/`, wired into the `HTGeometry` umbrella):

- `HardyDiskGutzmer.lean` — `hasSum_circleAverage_normSq`: **Gutzmer's identity** on every ball,
  by passing to the limit in the corpus's `circleAverage_normSq_partialSum`.
- `HardyDiskSpace.lean` — `diskCoeff` (canonical Taylor coefficients at `0`),
  `coeff_eq_diskCoeff`, `hasSum_circleAverage_normSq_diskCoeffOn`, the `H²` criterion
  `summable_diskCoeff_sq_of_circleAverage_le`, the coefficient model
  `HardyDisk = lp (fun _ : ℕ => ℂ) 2`, `hardyFun`, `hardySeries`, `diskCoeff_hardyFun`,
  `differentiableOn_hardyFun`, `circleAverage_hardyFun_le`.
- `HardyDiskMultiplier.lean` — `diskCoeff_congr`, `hardyDisk_ext`, `DiskMultiplier`,
  `circleAverage_mul_le`, and `hardyMul`: **multiplication by a bounded analytic function is a
  bounded operator on `H²(D)` of norm at most the sup bound**, with `hardyFun_hardyMul`,
  `hardyMul_mul`, `hardyMul_one`, `hardyMul_comm`, `hardyMul_congr`.
- `HardyDiskCyclic.lean` — `hardyOne`, `hardyOf`, `polyMultiples`, `cyclicSubspace`,
  `cyclicSubspace_hardyOne = ⊤`, `hardyMul_surjective`, `polyMultiples_map`, and
  **`cyclicSubspace_hardyOf_eq_top`: an invertible bounded analytic function is cyclic.**
  (No Beurling factorization is needed: multiplication by an invertible `H^∞` function is a
  topological isomorphism of `H²`, so it carries a dense set to a dense set.)
- `HardyDiskBlaschke.lean` — `blaschkeFactor`, `blaschkeProd`, `FiniteBlaschke` (analytic on a ball
  of radius `2 − bound > 1`), boundedness via the corpus's `finite_blaschke_schur`,
  `norm_fn_eq_one` (unimodular on the circle), and **`norm_hardyMul_blaschke`: multiplication by a
  finite Blaschke product is an isometry of `H²(D)`** (Gutzmer at `r = 1` on polynomials, extended
  by continuity).
- `HardyDiskModelSpace.lean` — the Szegő kernel `hardyKernel` with its reproducing property,
  **`range_hardyMul_singleBlaschke : range M_{b_a} = (ℂ ∙ k_a)ᗮ`** (the hard inclusion via
  `dslope` and the `H²` criterion), `finrank_orthogonal_range_singleBlaschke = 1`, and
  **`cyclicSubspace_blaschke_mul`: `[B·O] = B·H²(D)` for cyclic `O`** — equation `(16)`.
- `HardyDiskModelDimension.lean` — `orthogonal_map_eq_sup` (the orthogonal splitting
  `(T V)ᗮ = (range T)ᗮ ⊕ T(Vᗮ)` for an isometry `T`), `finrank_orthogonal_map_add`, and
  **`finrank_orthogonal_range_blaschkeOf : dim (H² ⊖ B·H²) = deg B`** — equation `(7)`, with
  multiplicities, by peeling one Blaschke factor at a time.
- `HardyCyclicityGaugeBlindness.lean` — `expMultiplier` (the carrier `O = exp σ` for `‖σ‖ < 1`,
  with `O⁻¹ = exp(−σ)` also bounded), `cyclicSubspace_expCarrier` (statement `1`), and the
  capstone **`hardyCyclicityDefect`**: `[O] = H²(D)`, `[B·O] = B·H²(D)`, and
  `dim (H²(D) ⊖ [B·O]) = k` — statement `4` in full.

REMAINING for 2 -> 3:
- statement `2`, differential algebraic independence of the parabolic orbit `{O ∘ τ_t}`: transport
  of the corpus's `HerglotzFullTranslationFreeness` through the rational substitution `φ`, the
  Cayley map, and `exp`;
- statement `3`, `P_N(G_B) = P_N(O)` at every power level: the general theorem
  `differentialAdjoin_range_pow_baseGauge_eq` is already proved (in
  `HTGeometry/KreinIndexEscapeStratification.lean`); what remains is the concrete realization of
  the disk translates and the rational gauge `B ∘ τ_t` inside the corpus's differential-field
  framework (via the coordinate `z = φ(w)`, where `τ_t` becomes `z ↦ z + t` and `B ∘ τ_t` becomes
  a rational function of `z`).

## Lean status update (2026-08-19b) — statements 2 and 3 are formalized; the card is complete

All four statements of the theorem are now unconditional Lean theorems, and a single capstone
asserts all four for one and the same concrete carrier.  Every new declaration `#print axioms` to
`propext, Classical.choice, Quot.sound` only.

- `formal/GaloisForLFunctions/HTGeometry/HardyCyclicityOrbitFreeness.lean` — **statement 2**.
  `realShiftConfiguration` and `mem_commonUpperTranslationDomain_of_im_pos` (for real translations
  the common upper domain is the whole open upper half plane); `cayleyToUpper_eq_mobius`
  (`φ(w) = i(1+w)/(1−w)` in Mobius normal form, coefficients `(i, i, −1, 1)`, determinant `2i`);
  `not_familyDifferentiallyAlgebraicOn_parabolicOrbit` (transport of the half-plane translation
  freeness through the change of variable `z = φ(w)`); and the capstone
  `outerCarrier_parabolicOrbitFreeness_denseResidual`: for every infinite-support base measure and
  strictly positive integrable density, a dense residual set of bounded exponential parameters
  makes every finite family of distinct real parabolic translates `{O ∘ τ_t}` differentially
  algebraically independent over `ℂ(w)`.

- `formal/GaloisForLFunctions/HTGeometry/HardyCyclicityPowerFieldInvariance.lean` — **statement 3**,
  equation `(6)`.  The disc is set up as an analytic chart (`isPreconnected_openDisc`,
  `openDisc_nonempty`, `openDisc_infinite`); `analyticMero` realizes an analytic function as an
  element of the meromorphic differential field of the chart, and
  `analyticMero_eq_ratfuncToMero` identifies an analytic function satisfying `Q·f = P` with the
  image of `P/Q ∈ ℂ(w)`.  The parabolic automorphism is put in Mobius normal form,
  `parabolicAut_eq_div : τ_t(w) = ((2i − t)w + t)/(−t w + (2i + t))`, and one Blaschke factor
  composed with it is `(N_t − a D_t)/(D_t − conj a · N_t)`; the numerator factor is nonzero because
  its vanishing would force `a = 1`.  The gauge `q_t = B ∘ τ_t` is therefore a nonzero element of
  the base field, and `differentialAdjoin_range_pow_baseGauge_eq` gives
  `gaugedOrbit_differentialAdjoin_pow_eq : P_N(G_B) = P_N(O)` for every finite Blaschke product `B`
  and every `N`, together with `gaugedOrbit_differentialIndependent_iff`.

- `formal/GaloisForLFunctions/HTGeometry/HardyCyclicityCarrierCapstone.lean` — the unified
  statement.  `carrierExponent`, `differentiableOn_carrierExponent`, `norm_carrierExponent_lt_one`
  and `carrierMultiplier` realize `O = exp σ` with `‖σ‖ < 1` as a bounded analytic multiplier of
  `H²(D)`; `expWeightedMeasure_ne_zero` supplies the strict positivity of `Im m`.  The capstone
  `hardyCyclicityGaugeBlindness_carrier` states, for a dense residual set of exponential
  parameters and one and the same carrier `O`:
  statement `1` (`[O] = H²(D)`), statement `2` (maximal parabolic differential freeness),
  statement `3` (`P_N(B·O) = P_N(O)` for every `B` and every `N`), and statement `4`
  (`[B·O] = B·H²(D)` with cyclicity defect exactly `deg B`).

Nothing in the theorem is left unformalized.

## Gates (updated 2026-08-19)

- [x] 2 -> 3: complete unconditional theorem formalized in Lean
