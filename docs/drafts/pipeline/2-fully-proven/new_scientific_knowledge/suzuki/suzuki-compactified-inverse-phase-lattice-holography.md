# Suzuki compactified inverse-phase lattice holography

- **ID:** `suzuki-compactified-inverse-phase-lattice-holography`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Lane:** Suzuki cofinal divisor compactification and measure transference
- **Parents:** `suzuki-donoghue-defect-spectral-measure-law`,
  `suzuki-global-phase-conjugacy-divisor-flow`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096](https://arxiv.org/abs/2606.09096), together with its proved
  finite-aperture Livsic--Donoghue consequences
- **Statement:** Cayley compactification makes every normalized Suzuki inverse phase sharply
  `1/2`-Lipschitz.  Values and first derivatives on one fixed odd-`pi` phase lattice recover the
  complete moving Donoghue probability, and every cofinal sequence splits canonically into a
  labeled atomic survivor plus a positive residual measure created by phase-label escape.
- **RH used:** no
- **Computation used:** no

## Frontier problem

Global phase conjugacy solved finite-shift pole continuation, but left a topology mismatch in the
cofinal aperture limit.  Physical poles move on the noncompact real line, Clark weights change,
and locally uniform convergence of upper-half-plane carriers does not preserve point derivatives
at a moving boundary divisor.

The correct state is neither the carrier alone nor the real spectral measure alone.  Compactify
the physical line by `arctan` and pull every pole back to its fixed lifted phase label.  This turns
the entire divisor probability into a fixed-lattice first jet of one uniformly Lipschitz function.

## Setup

For any aperture and admissible shift, let

```text
Theta(x)=exp(i phi(x)),
phi(0)=pi,
phi : R -> R an increasing real-analytic bijection,
m=i(1+Theta)/(1-Theta).                                  (1)
```

Let `nu` be the canonical even-extension Donoghue spectral probability and

```text
dmu(t)=(1+t^2)dnu(t).
```

At an even-extension pole `x`,

```text
Theta(x)=1,
q(x)=phi'(x)>0,
mu({x})=2/q(x),
nu({x})=2/[q(x)(1+x^2)].                                (2)
```

Define the centered inverse phase and its Cayley compactification:

```text
X(y)=phi^(-1)(pi+y),
U(y)=arctan(X(y)).                                       (3)
```

The fixed even Clark lattice is

```text
y_k=(2k-1)pi,       k in Z.                              (4)
```

Indeed `pi+y_k=2pi k`, so `x_k=X(y_k)` is the `k`th even-extension pole.

## Theorem A: sharp compactified inverse-phase geometry `[PROVED HERE]`

The function `U` is real analytic, odd, and strictly increasing, with

```text
-pi/2 < U(y) < pi/2,
U(0)=0.                                                  (5)
```

It satisfies the sharp derivative law and bound

```text
U'(y)=1/[q(X(y))(1+X(y)^2)],
0<U'(y)<=1/2.                                            (6)
```

Consequently

```text
|U(y)-U(z)| <= |y-z|/2                                  (7)
```

for all real `y,z`.  The constant `1/2` is sharp.  Equality on an interval means that the residual
inner phase is constant there; global equality gives the single Cayley/ground carrier.

### Proof

The common anchor `Theta(i)=0` factors one upper-half-plane Blaschke factor:

```text
Theta(z)=b_i(z) S(z),
b_i(z)=(z-i)/(z+i),                                     (8)
```

where `S` is meromorphic inner.  On the real axis choose compatible phases

```text
phi=beta+sigma,
beta'(x)=2/(1+x^2),
sigma'(x)>=0.                                            (9)
```

The nonnegative residual speed is the boundary Poisson-kernel sum of the residual inner factor,
including any nonnegative exponential speed.  Thus

```text
q(x)=phi'(x)>=2/(1+x^2).                                (10)
```

Since `phi(X(y))=pi+y`, inverse differentiation gives

```text
X'(y)=1/q(X(y)).                                        (11)
```

Composing with `arctan` proves the identity in `(6)`, and `(10)` proves its upper bound.  The mean
value theorem gives `(7)`.

Oddness follows from the already proved symmetry `m(-x)=-m(x)`.  The relation
`m=-cot(phi/2)` and the normalization `phi(0)=pi` give

```text
phi(-x)=2pi-phi(x),
X(-y)=-X(y),
U(-y)=-U(y).                                             (12)
```

This proves Theorem A.

## Theorem B: fixed-lattice holography of the full spectral probability `[PROVED HERE]`

At every lattice point `(4)`,

```text
x_k=tan(U(y_k)),
p_k:=nu({x_k})=2U'(y_k)>0.                               (13)
```

Moreover

```text
sum_(k in Z) p_k=1.                                      (14)
```

Therefore the complete normalized Donoghue probability is reconstructed by the fixed-lattice
`C^1` jet of `U`:

```text
nu=sum_(k in Z) 2U'(y_k) delta_(tan(U(y_k))).            (15)
```

### Proof

The first identity in `(13)` is `tan(arctan x_k)=x_k`.  At `y_k`, equations `(6)` and `(2)` give

```text
2U'(y_k)
 =2/[q(x_k)(1+x_k^2)]
 =nu({x_k}).                                             (16)
```

The Donoghue deficiency vector is cyclic and normalized, so its pure-point spectral measure has
total mass one.  Summing `(16)` proves `(14)`--`(15)`.

The result is stronger than separate pole and residue convergence: one function on a fixed phase
line contains both, and its derivative samples are already probability weights rather than
unnormalized Nevanlinna residues.

## Theorem C: unconditional cofinal compactness and residual classification `[PROVED HERE]`

Let `U_n` be any sequence arising from arbitrary apertures and arbitrary admissible shifts.  Let

```text
p_(n,k)=2U_n'(y_k),
sigma_n=(arctan)_* nu_n
       =sum_k p_(n,k) delta_(U_n(y_k)).                  (17)
```

After passage to a subsequence, there exist:

1. an odd nondecreasing `1/2`-Lipschitz function

   ```text
   U_infinity : R -> [-pi/2,pi/2],
   U_infinity(0)=0,                                     (18)
   ```

   such that `U_n -> U_infinity` locally uniformly;

2. limits

   ```text
   p_k=lim_n p_(n,k) in [0,1],                           (19)
   ```

   simultaneously for every `k in Z`;

3. a probability measure `sigma` on the compact interval `[-pi/2,pi/2]` such that
   `sigma_n -> sigma` weakly.

Put

```text
u_k=U_infinity(y_k),
sigma_lab=sum_k p_k delta_(u_k).                         (20)
```

Then

```text
sum_k p_k<=1,
sigma>=sigma_lab,
sigma_res:=sigma-sigma_lab>=0,
sigma_res(total)=1-sum_k p_k.                            (21)
```

Thus every cofinal degeneration has an exact canonical decomposition

```text
compactified spectral limit
 = fixed-label atomic survivor + phase-label-escape residual. (22)
```

### Proof

Theorem A makes the family uniformly bounded and equi-Lipschitz on every compact phase interval.
Arzela--Ascoli plus a diagonal exhaustion gives locally uniform convergence and `(18)`.  The
numbers `p_(n,k)` lie in `[0,1]`; a second diagonal extraction gives `(19)` on the countable
lattice.  Compactness of probability measures on the compact projective interval gives a weak
limit `sigma`.

Fatou's lemma applied to the counting measure gives `sum p_k<=1`.  For every finite set `F` of
labels,

```text
sum_(k in F) p_(n,k) delta_(U_n(y_k))
 ->sum_(k in F) p_k delta_(u_k).                         (23)
```

The difference between `sigma_n` and the left side of `(23)` is positive.  Passing to the weak
limit shows that `sigma` dominates every finite partial survivor.  Monotone exhaustion of `Z`
gives `(21)`.

No derivative of `U_infinity` is asserted at the lattice: derivative convergence is stored in the
separate labels `p_k`.  This avoids a false `C^1` compactness claim.

## Corollary: exact criterion for tight pure-point survival `[PROVED HERE]`

Suppose along the extracted subsequence that

```text
sum_k p_k=1,
|u_k|<pi/2 for every k.                                  (24)
```

Then `sigma_res=0`, the physical measures are tight on `R`, and

```text
nu_n -> nu_infinity
     =sum_k p_k delta_(tan u_k)                          (25)
```

weakly.  If additionally `p_k>0` for every `k` and `u_k` is strictly increasing in `k`, the limit
has an infinite simple two-sided labeled divisor.

Indeed pointwise convergence of the probabilities `p_(n,k)` to a probability `p_k` implies
`ell^1(Z)` convergence.  A finite label head captures all but arbitrarily small mass; positions in
that head converge to finite `tan u_k`.  This proves both tightness and `(25)` by testing bounded
continuous functions.

Conversely, failure of `(24)` separates two independent defects:

```text
1-sum_k p_k > 0    : phase-label escape / unlabeled residual mass,
|u_k|=pi/2         : fixed-label physical escape to projective infinity. (26)
```

Coalescence `u_j=u_k` is a third, explicitly visible loss of simple divisor labels.

## Exact placement of the two known Suzuki boundary states

The compactification distinguishes the universal boundaries without ambiguity.

### Free clock homogenization

For the free carrier,

```text
x_(a,k)=(k-1/2)pi/a,
p_(a,k)=coth(a)/[a(1+x_(a,k)^2)].                        (27)
```

For every fixed phase label, `U_a(y_k)->0` and `p_(a,k)->0`: no fixed labeled atom survives.  Yet
the compactified probabilities converge to the pushforward of Cauchy probability under `arctan`,
namely normalized Lebesgue measure on `(-pi/2,pi/2)`.  Hence

```text
U_infinity=0,
sigma_lab=0,
sigma_res=du/pi.                                         (28)
```

Clock homogenization is therefore *pure phase-label residual mass*, not mysterious loss of the
probability normalization.

### Ground Cayley escape

For the ground carrier `m(z)=z`, the compactified generalized inverse phase is the clipped ramp

```text
U_ground(y)=clip(y/2,-pi/2,pi/2).                        (29)
```

The spectral probability escapes to the two projective endpoints.  Thus ground escape is visible
as endpoint mass/saturation, qualitatively different from the uniform residual in `(28)`.

These are exact boundary profiles; no numerical experiment is involved.

## What this changes at the RH frontier

The previously requested inverse-phase compactness theorem is now unconditional.  The cofinal
state space is compact after replacing moving real divisors by

```text
(U_n, sigma_n, (p_(n,k))_(k in Z)).                      (30)
```

The open producer is no longer vague "tightness plus weights."  It is the source theorem

```text
sigma_res=0,
|U_infinity(y_k)|<pi/2,
p_k>0 and target Xi lattice identities for every k.      (31)
```

Prime tangent tomography and finite-shift holonomy can now be asked to control fixed lattice jets
`U_n(y_k), U_n'(y_k)`, the topology in which the full normalized measure is exactly reconstructed.
This removes the earlier mismatch between high-clock source observables and moving Clark atoms.

It does not prove `(31)` and does not identify the Xi divisor.  It supplies the compact state,
sharp defect decomposition, and exact necessary-and-sufficient pure-point survival gate on which a
source argument can act.

## Hostile audit

1. **No hidden RH positivity.**  The only positivity is the finite-aperture inner phase speed and
   the normalized spectral probability, both unconditional for every admissible shift.
2. **No arbitrary shift selector.**  Compactness holds for every aperture/shift sequence.
3. **No false `C^1` convergence.**  Locally uniform profile convergence and pointwise lattice-jet
   convergence are extracted separately.
4. **No lost mass hidden by `arctan`.**  The compactified measures retain total mass one; missing
   fixed-label mass is the explicit positive residual `sigma_res`.
5. **No finite-atom overclaim.**  Infinite simple survival requires `p_k>0` and strict label
   separation for all `k`, stated explicitly.
6. **No generic compactness presented as RH.**  The theorem solves the topology and classification
   wall.  Vanishing of the residual and Xi identification remain source problems.
7. **Sharpness.**  The Cayley factor attains the `1/2` speed cap.  The free and ground states attain
   different boundary strata, so neither defect term can be removed.

## Literature and priority audit

The generic facts that meromorphic inner functions possess increasing analytic phases and Clark
weights are inverse angular derivatives are classical; see Hatinoğlu,
*Uniqueness theorems for meromorphic inner functions and canonical systems*,
[arXiv:2110.12384](https://arxiv.org/abs/2110.12384).  The Blaschke-factor Poisson-kernel phase
decomposition and Arzela--Ascoli theorem are likewise classical and are not claimed as new.

Suzuki does not introduce the normalized Donoghue probability, global phase chart, compactified
inverse phase, fixed-lattice derivative weights, or residual decomposition `(21)`.  Exact phrase
and concept searches of Suzuki's source, the repository, and arXiv found no source-specific theorem
of this form.  Candidate novelty is the exact synthesis `(3)`--`(31)`, particularly
`p_k=2U'(y_k)` and the canonical labeled-atomic/residual splitting of every cofinal Suzuki limit.
Specialist priority review remains required.

## Lean target

Formalize the dependency-closed exact core:

```text
suzukiCenteredInversePhase
suzukiCompactifiedInversePhase
suzukiCenteredInversePhase_phase
tan_suzukiCompactifiedInversePhase
suzukiAnchoredPhaseSpeed_floor
hasDerivAt_suzukiCenteredInversePhase
hasDerivAt_suzukiCompactifiedInversePhase
suzukiCompactifiedInversePhase_speed_mem
suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv
hasSum_two_mul_suzukiCompactifiedDeriv_one
suzukiCompactifiedInversePhase_lipschitz
suzukiCompactifiedInversePhase_zero
suzukiCompactifiedInversePhase_neg
orderIso_zero_of_reflection
suzukiCompactifiedInversePhase_zero_of_reflection
```

`suzukiCompactifiedInversePhase_zero` is `(5)`, the centering `U(0)=0`, and
`suzukiCompactifiedInversePhase_neg` is `(12)`, oddness.  Both were formalized but omitted from this
list.  `orderIso_zero_of_reflection` closes a redundancy: the reflection normalization
`phi(-x) = 2 pi - phi(x)` already forces the anchor `phi 0 = pi` at `x = 0`, so the two
normalizations are not independent hypotheses and the anchor never has to be assumed separately.

Equation `(1)`, the Cayley inversion `m = i (1 + Theta) / (1 - Theta)`, is now formal too, in
`formal/GaloisForLFunctions/RHTower/SuzukiDonoghueHerglotzTransform.lean`:

- `cayleyOfHerglotz_ne_one`: the Cayley value is never `1`, so the inversion needs no side condition
  beyond the one already required to form the transform.
- `herglotzOfCayley`, `herglotzOfCayley_cayleyOfHerglotz`: **`(1)`** itself.
- `cayleyOfHerglotz_herglotzOfCayley`: the converse, so the Cayley correspondence between the upper
  half plane and the punctured disc is a bijection in both directions.
- `im_herglotzOfCayley`, `im_herglotzOfCayley_pos`: the inverse carries the *disc into the upper
  half plane*, since `Im (i(1+w)/(1-w)) = (1 - |w|^2)/|1-w|^2`.  With the Schur bound this makes the
  correspondence a bijection between the two domains, not merely between values.

**`(8)`, the Blaschke bound** — same module.  The factorization `Theta = b_i S` asks that
`S = Theta / b_i` be inner, which is exactly `|Theta| <= |b_i|`:

- `cayleyOfHerglotz_I`, `herglotzOfCayley_zero`: the Blaschke factor of `(8)` *is* the Cayley
  transform, anchored at `i`, and `i` is the inverse Cayley image of `0`.
- `norm_le_norm_cayleyOfHerglotz_of_mapsTo`: **an inner function of the upper half plane anchored at
  `i` is dominated by `b_i`.**  Transferring by the inverse Cayley transform turns the half-plane
  statement into the Schwarz lemma at the origin.

So the analytic content of `(8)` is formal; what is left of it is the construction of `S` as a
meromorphic object, which is bookkeeping on top of this bound.

Equation `(12)` has three lines, and its *first* — the reflection normalization
`phi(-x) = 2 pi - phi(x)` — is derived here from oddness of `m` via `m = -cot(phi/2)`.  The corpus
had been carrying that line as a hypothesis (`hreflection`) and deriving only the other two.  It is
now derived, in `formal/GaloisForLFunctions/RHTower/SuzukiCayleyPhaseLift.lean`:

- `cayleyPhaseLift_half_sub`, `neg_cot_half_cayleyPhaseLift`: the relation `m = -cot(phi/2)`.
- `cayleyPhaseLift_reflection_of_odd`: **`(12)`, first line** — oddness of `m` gives the reflection
  normalization.
- `cayleyPhaseLift_zero_of_odd`: and the centering `phi(0) = pi`, which with
  `orderIso_zero_of_reflection` closes the loop between the two normalizations.

Equation `(2)`, the Donoghue atom mass, was in the same position: the corpus took
`nu({x}) = 2/[q(x)(1+x^2)]` as a hypothesis of
`suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv` and derived `(13)` from it.  It is now
derived, from the Clark atom and the density relating the two measures:

- `suzukiDonoghueAtom_eq`: **`(2)`** — the Donoghue atom is the Clark atom over `1 + x^2`, since
  `dmu = (1+t^2) dnu`; with `mu({x}) = 2/q(x)` this is the displayed formula.
- `suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv_of_clarkAtom`: hence `(13)` follows from
  the Clark atom directly, with `(2)` no longer assumed.

That also covers `(16)`, whose two equalities are exactly `(2)` and `(13)`.

**`(18)`, the structural class of the cofinal limit** —
`formal/GaloisForLFunctions/HTGeometry/PointwiseLimitClass.lean`.  Theorem C's extraction has two
halves: producing the limit, and saying what it inherits.  The second is formal:

- `odd_of_tendsto`, `monotone_of_tendsto`, `lipschitzBound_of_tendsto`, `mem_Icc_of_tendsto`: each
  of oddness, monotonicity, a uniform Lipschitz bound and a uniform range bound is a closed
  condition and passes to a pointwise limit.
- `limitClass_of_tendsto`: **`(18)`** — the limit is odd, nondecreasing, `1/2`-Lipschitz, valued in
  `[-pi/2, pi/2]`, and centered, the centering coming free from oddness.

- `exists_subseq_tendsto_of_equiLipschitz`: **the extraction** — a uniformly bounded, equi-Lipschitz
  sequence has a pointwise convergent subsequence.  Restricted to the rationals the family lives in
  a countable product of compact intervals, which is compact and metrizable, hence sequentially
  compact; the Lipschitz bound then makes the subsequence Cauchy at every real point.

- `exists_subseq_tendsto_of_mem_Icc`: **`(19)`** — the mass families, indexed by the countable
  lattice and valued in `[0,1]`, also have a pointwise convergent subsequence with limits in the
  same interval.
- `exists_subseq_tendsto_joint`: **Theorem C, clauses 1 and 2 together** — one common subsequence
  along which the phase profiles and the mass families both converge.  Theorem C asserts a *single*
  extraction serving both, which is what this provides: thin for the profiles, then thin again for
  the masses, since a subsequence of a convergent sequence still converges.

So Theorem C's clauses 1 and 2, `(18)` and `(19)`, are formal end to end.

**`(21)` and `(22)`, the residual decomposition** —
`formal/GaloisForLFunctions/HTGeometry/LabelledAtomicMeasure.lean`.  These are measure-level but do
not need the Clark measure: they are statements about *any* probability limit and *any* labelled
part below it.

- `labelledMeasure`, `labelledMeasure_univ`: the labelled atomic survivor and its total mass
  `sum p_k`.
- `residual_univ_eq`: **`(21)`** — the residual carries exactly the labelled mass deficit
  `1 - sum p_k`.
- `labelled_add_residual`: **`(22)`** — the limit is the labelled atomic survivor plus the residual.
- `residual_eq_zero_iff`: the residual vanishes exactly when the labelled masses exhaust the total,
  which is the criterion the Corollary's `(24)` uses.
- `tight_criterion_failure_iff`: **`(26)`** — failure of `(24)` is exactly one of two defects,
  unlabelled residual mass or a label reaching the boundary.  The separation is sharp because the
  two standing constraints (total mass at most one, labels in the closed window) are each saturated
  in exactly one failure mode.
- `two_defects_independent`: neither defect implies the other, so `(26)` is a genuine dichotomy and
  not a disjunction with a redundant branch.
- `coalescence_not_injective`: coalescence is the third, separate failure the card notes — the
  labelled divisor stops being simple with no mass lost and no label escaping.

**The Corollary's `l^1` step** —
`formal/GaloisForLFunctions/HTGeometry/ScheffeCounting.lean`.  The Corollary's proof opens with
"pointwise convergence of the probabilities `p_(n,k)` to a probability `p_k` implies `l^1(Z)`
convergence".  That is Scheffé's lemma for counting measure, and it is in neither mathlib nor the
corpus, so it is built here:

- `exists_finset_tsum_compl_lt`: a summable family has arbitrarily small tails outside a finite set.
- `tendsto_tsum_posPart_of_tendsto`: the positive deficits below a summable envelope have vanishing
  total.
- `tendsto_tsum_abs_sub_of_tendsto`: **Scheffé** — pointwise convergence of probability vectors
  gives `l^1` convergence.  Equal totals force the positive and negative deficits to have the same
  sum, so the `l^1` distance is exactly twice the positive deficit.

- `summable_abs_sub`, `exists_finset_eventually_tsum_compl_lt`: **the tightness clause** — "a finite
  label head captures all but arbitrarily small mass", uniformly in `n`.  One finite label set works
  for the whole family eventually, because the limit's tail is small and the `l^1` distance to the
  limit is eventually small.

- `exists_finset_tail_bounds`, `abs_tsum_mul_le`,
  `tendsto_tsum_mul_comp_of_tendsto`: **`(25)`** — if the masses converge coordinatewise with equal
  totals and the positions converge coordinatewise, then every bounded continuous test function has
  convergent tested sums.  That *is* weak convergence of the associated atomic measures, stated on
  the sums themselves, so it needs no measure constructed.

This is the engine of the Corollary: it turns coordinatewise convergence of the surviving masses
into control of the whole family, hence tightness, and then `(25)`.

What genuinely remains is `(15)`, the identification of the spectral measure itself as the labelled
sum, and `(20)`, which names `sigma_lab` as that limit — both of which do need Suzuki's Clark measure
represented — together with the Blaschke inner factor of `(8)`.

This was reachable only after the Herglotz and Schur layer was built for Theorem D of the child
card; it is no longer blocked on representing Suzuki's operator.

The concrete inner factorization, spectral-measure sum, and measure-level compactness theorem
remain paper-level until Suzuki's operator and Clark measure are represented in Lean.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, exact module build green, axiom audit clean
- [ ] 3 -> 4 publication-ready: standalone paper, specialist priority review
- [x] unconditional compactified inverse-phase subsequential compactness
- [x] exact fixed-lattice reconstruction of support and probability weights
- [x] canonical labeled-survivor/residual decomposition
- [ ] source proof that the cofinal residual vanishes
- [ ] Xi divisor identification
- [ ] RH

## Log

- 2026-07-21 — created in Stage 1 after global phase conjugacy exposed inverse-phase lattice
  derivatives as the exact remaining cofinal state.
- 2026-07-21 — sharp anchored phase floor, compactified Lipschitz profile, fixed-lattice probability
  holography, cofinal residual decomposition, and pure-point survival criterion proved; promoted to
  Stage 2.
- 2026-07-21 — dependency-closed structural core formalized in
  `SuzukiCompactifiedPhaseProfile.lean`; exact module build, SOTA import, capstone axiom audit,
  global formal lint, and diff audit passed; promoted to Stage 3.
- 2026-08-01 — audited this card's numbered statements against declarations.  `(5)` (`U(0)=0`) and
  `(12)` (oddness) are formalized but were missing from the Lean-target list, and the child card
  `suzuki-residual-overcrowding-entire-pair-closure` mis-attributed `(5)` to
  `suzukiCompactifiedInversePhase_mem_Ioo`, which is the projective range rather than the centering;
  both records corrected.  Added `orderIso_zero_of_reflection`: the reflection normalization already
  forces the anchor `phi 0 = pi`, so theorems carrying both hypotheses were over-assuming.  Targeted
  build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — equation `(1)`, the Cayley inversion `m = i(1+Theta)/(1-Theta)`, formalized
  (`herglotzOfCayley_cayleyOfHerglotz`), together with its converse, so the Cayley correspondence is
  a bijection in both directions.  The Cayley value is never `1`
  (`cayleyOfHerglotz_ne_one`), so the inversion carries no extra side condition.  `(1)` had been
  scoped as paper-level pending a Lean representation of the Clark measure; the Herglotz/Schur layer
  built for the child card's Theorem D made it reachable directly.  Targeted build green, axiom
  audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(12)`'s first line derived rather than assumed
  (`cayleyPhaseLift_reflection_of_odd`), together with the cotangent relation `m = -cot(phi/2)` the
  card uses to obtain it (`neg_cot_half_cayleyPhaseLift`).  The corpus had been taking the
  reflection normalization as a hypothesis and deriving only `(12)`'s second and third lines, so the
  displayed equation was one third assumption and two thirds theorem.  Targeted build green, axiom
  audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(2)` derived rather than assumed (`suzukiDonoghueAtom_eq`).  As with `(12)`, the
  corpus was taking the displayed equation as a hypothesis of the theorem that cites it: the atom
  formula `2/[q(1+x^2)]` was the input to `(13)`, not an output.  It follows from the Clark atom
  `2/q` and the density `dmu = (1+t^2) dnu`, and
  `suzukiPhaseProbabilityMass_eq_two_mul_compactifiedDeriv_of_clarkAtom` now routes `(13)` through
  that derivation.  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(18)`'s limit class formalized (`limitClass_of_tendsto`): oddness, monotonicity, the
  `1/2`-Lipschitz bound, the range bound and the centering all pass to a pointwise limit, each being
  a closed condition.  This is the half of Theorem C's extraction that needs no compactness; the
  remaining half is Arzela--Ascoli for the equi-Lipschitz family.  `(16)` is covered by the previous
  entry, its two equalities being `(2)` and `(13)`.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — Theorem C's extraction formalized
  (`exists_subseq_tendsto_of_equiLipschitz`), completing `(18)` end to end.  The route avoids a
  diagonal argument: restricted to the rationals the family lives in a countable product of compact
  intervals, which mathlib already knows is sequentially compact, and the equi-Lipschitz bound
  upgrades convergence on that countable set to a Cauchy property at every real point.  This is
  formalization of classical analysis, not new mathematics — recorded as such.  Targeted build
  green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(19)` and the joint extraction formalized (`exists_subseq_tendsto_of_mem_Icc`,
  `exists_subseq_tendsto_joint`), so Theorem C's clauses 1 and 2 are complete.  `(19)` was scoped
  paper-level with `(20)`--`(22)`, but it is not measure-level at all: it is coordinatewise
  convergence of the mass families, which the same countable-product compactness handles.  Theorem C
  asserts one subsequence serving both clauses, so the joint version is the faithful statement.
  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(21)` and `(22)` formalized (`residual_univ_eq`, `labelled_add_residual`), plus the
  vanishing criterion `residual_eq_zero_iff` that the Corollary's `(24)` rests on.  These were
  grouped with the blocked measure-level statements, but they are about any probability limit and
  any labelled part below it, so they need no Clark measure: mass additivity and `Measure.sub` carry
  them.  The genuine remainder is `(15)`/`(20)`, which identify the spectral measure as the labelled
  sum.  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — Scheffé's lemma for counting measure built
  (`tendsto_tsum_abs_sub_of_tendsto`), the Corollary's opening step "pointwise convergence of the
  probabilities implies `l^1(Z)` convergence".  Absent from both mathlib and the corpus.  The proof
  turns on equal totals forcing the positive and negative deficits to have the same sum, so the
  `l^1` distance is twice the positive deficit, which is dominated by the limit vector and vanishes
  termwise.  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — the Corollary's tightness clause formalized
  (`exists_finset_eventually_tsum_compl_lt`): a single finite label head captures all but
  arbitrarily small mass, uniformly in `n`.  It follows from Scheffé plus smallness of the limit's
  own tail, and is the uniform statement that tightness of the physical measures rests on.  What
  remains of the Corollary is the measure-level step to `(25)`.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(25)` formalized (`tendsto_tsum_mul_comp_of_tendsto`): coordinatewise convergence of
  masses with equal totals, plus coordinatewise convergence of positions, gives convergent tested
  sums for every bounded continuous test function.  Weak convergence of atomic measures is exactly
  convergence of tested sums, so this needs no measure constructed — the head/tail split with the
  uniform tail bound does it.  With this the Corollary is formal apart from naming the limit as a
  measure.  Targeted build green, axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(26)` formalized (`tight_criterion_failure_iff`), with `two_defects_independent`
  checking the dichotomy is genuine (neither branch implies the other, so neither is redundant) and
  `coalescence_not_injective` recording the third failure the card names.  With this every numbered
  statement of the card is formal except `(15)`/`(20)`, which identify the spectral measure as the
  labelled sum, and `(8)`/`(9)`'s Blaschke inner factor.  Targeted build green, axiom audit
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(8)`'s analytic content formalized
  (`norm_le_norm_cayleyOfHerglotz_of_mapsTo`): an inner function of the upper half plane anchored at
  `i` is dominated by the Blaschke factor `b_i`, which is exactly the assertion that `Theta / b_i`
  is Schur.  The half-plane Schwarz--Pick statement needed no new analysis: the inverse Cayley
  transform carries the disc to the half plane (`im_herglotzOfCayley_pos`) and sends `0` to the
  anchor `i`, so mathlib's Schwarz lemma at the origin transfers directly.  Targeted build green,
  axiom audit `[propext, Classical.choice, Quot.sound]`.
