# Angular energy quantization

Status: in progress (core law proved in Lean; the threshold bound is the open core)

## The move

The transverse-equilibrium chain ended at a *maximum* principle, and a maximum principle needs a
maximum: an attainment hypothesis `∃ρ₀ ∀ρ, Re ρ ≤ Re ρ₀` that nothing known supplies, and that the
ledger has independently identified as the intrinsic blind spot of every averaging argument.

The move is to stop using a maximum principle. Replace the extremal functional by an energy, which
has no extremal structure to attain.

For two distinct zeros put

    cos²θ(ρ,ρ') = (Re ρ − Re ρ')² / |ρ − ρ'|²,

the squared cosine of the angle of the segment joining them, measured from the real axis. Define the
**angular energy of a zero**

    E(ρ) = Σ_{ρ' ≠ ρ} cos²θ(ρ,ρ').

Every term lies in `[0,1]`. The sum converges for every `ρ`, because real parts are confined to the
critical strip, so `cos²θ ≤ 1/|ρ−ρ'|²`, and the zero network is locally finite.

The hypothesis holds exactly when every pair of zeros is joined by a vertical segment, i.e. when
`E ≡ 0`. That much is a restatement. The content is what follows.

## The quantum

Let `σρ = 1 − ρ̄` be the functional-equation partner. The segment from `ρ` to `σρ` is exactly
horizontal, of length `|2 Re ρ − 1|`. Its conductance `1/|ρ − σρ|²` and its squared displacement
`(2 Re ρ − 1)²` are reciprocal. Their product is

    cos²θ(ρ, σρ) = 1

for **every** off-line zero, independent of how close `Re ρ` is to `1/2`. Hence

    E(ρ) ≥ 1 whenever Re ρ ≠ 1/2,
    E(ρ) = 0 for all ρ when the hypothesis holds.

The energy is therefore quantized at the threshold: the family of angular energies never lies
entirely inside the open interval `(0,1)`. Either every zero sees every other zero vertically, or
some zero carries a full unit.

## Three consequences

1. **No attainment is used.** The chain `E < 1 ⟹ RH` quantifies over all zeros with a strict
   inequality. There is no maximum, no limit, no extremal zero, no escape-to-infinity case. The
   attainment obstruction was an artifact of the maximum principle, not a feature of the problem.

2. **The hypothesis is a threshold, not an equality.** Previous equivalents in this lane were exact
   identities — `Re(ξ''(ρ)/ξ'(ρ)) = 0`, vanishing Galois norm, slice cardinality `≤ 1`. Those are
   rigid: nothing weaker than the identity implies them. `E(ρ) < 1` is an inequality with a margin,
   and an unconditional upper bound anywhere below `1` would suffice. This is the first form of the
   hypothesis in this lane that an analytic estimate could in principle discharge.

3. **Deformation arguments provably cannot see it.** The partner term is `1` for every off-line `ρ`
   and `0` on the line. As a zero drifts toward the critical line its angular energy does not decay;
   it stays at least `1` and jumps to `0` only in the limit. Any argument whose functional is
   continuous under a motion of the zeros — the de Bruijn–Newman flow, `Λ → 0` continuity, any
   perturbative expansion in the off-line displacement — is measuring a quantity that is blind to
   this jump. That is an object-level reason, not an analogy, for the criticality wall already
   recorded in this field.

## Why the displacement cancels

The cancellation is exact because both the conductance and the displacement are homogeneous of
degree `−2` and `+2` in the off-line distance. The Cauchy kernel `1/|ρ−ρ'|²` carries conformal
weight zero against a squared length. Nothing in the geometry of the divisor is being used except
the functional equation, which forces the partner to lie *horizontally* opposite — and horizontal is
exactly the direction the kernel is scale-blind in. A zero at `Re ρ = 0.5001` and one at
`Re ρ = 0.9` are, in this energy, the same size.

## Open core

`[OPEN CORE]` An unconditional bound `E(ρ) < 1` for all zeros, or for even a single zero.

The difficulty is genuine and identifiable. Write

    cos²θ = 1/2 + (1/2) Re(Δ/Δ̄),   Δ = ρ − ρ'.

The second summand is not holomorphic in either zero, so the whole holomorphic toolkit of this
lane — Hadamard products, `ξ''/ξ'`, log-derivative expansions, the closed form
`Σ_{ρ'≠ρ} (ρ−ρ')⁻² = ξ''(ρ)²/(4ξ'(ρ)²) − ξ'''(ρ)/(3ξ'(ρ))` — computes `Σ Δ⁻²` and never `Σ Δ/Δ̄`.
The angular energy is a genuinely real-analytic functional of the divisor. This is a concrete
explanation for the saturation of the analytic toolkit recorded elsewhere: the missing object is not
a lemma but a non-holomorphic pairing.

## Lean

`formal/GaloisForLFunctions/RHTower/AngularEnergyQuantization.lean`, built on the locally-finite
network of `ZeroNetworkConductance`. Unconditional and axiom-clean.

## Relation to the rest of the lane

- The clock-degeneracy count `#slice = #fixed + 2·#left` is the cardinality shadow of this energy;
  the energy refines it by weighting each off-line pair by exactly one.
- The two-torsion reading (`RH = triviality of a ℤ/2-action`) says the free orbits are invisible to
  reflection-even readers. The angular energy is the first reader in this lane that is *odd enough*
  to see a free orbit and still converges: it reads each free orbit as the integer `1`.
- `TransverseAttainment.lean` retains the honest dichotomy from the maximum-principle route
  (identity + finite off-line set ⟹ hypothesis) as the record of what that route could reach.

---

# Part II: the critical-line potential, and mass blindness

## Moving the base point

The angular energy is only defined at zeros. Put the base point on the critical line instead. For
real `t`,

    U(t) = Σ_ρ δ_ρ² / (δ_ρ² + (t − Im ρ)²),     δ_ρ = Re ρ − 1/2.

The sum converges at every `t`: displacements are bounded by one half, so each summand is at most
twice a fixed Cauchy weight, and the ordinates are locally finite.

Written in scale-invariant form, each summand is

    1 / (1 + ((t − Im ρ)/δ_ρ)²)  —  a bump of height exactly 1 and width exactly |δ_ρ|.

On-line zeros contribute nothing. So `U ≡ 0` under the hypothesis, and `U(Im ρ) ≥ 1` for any off-line
zero, since that zero's own bump is at its peak there. Hence

    RH  ⟺  U(t) < 1 for all real t,

a uniform strict bound on one explicit function of one real variable. This is strictly better than
the version at zeros: the criterion now ranges over a continuum, still uses no attainment, and the
quantum is unchanged.

The superlevel set of one bump at height `λ` is the interval of half-width `|δ| √((1−λ)/λ)` about the
zero's ordinate. **Detecting a zero at displacement `δ` requires resolution of order `δ`.**

## Mass blindness

The mass of one bump over the symmetric window of half-width `R` is exactly

    ∫ = 2 δ arctan(R/δ)  <  π δ   for every R.

So the two norms of the same object are decoupled at every scale:

| | height | mass |
|-|-|-|
| one bump at displacement `δ` | `1`, always | `< π δ → 0` |

Every unconditional handle this field has on the off-line divisor is a mass. The density integral
`∫_{1/2}^{1} N(σ,T) dσ` is exactly half the total displacement mass `Σ_ρ |δ_ρ|`; Littlewood's lemma
expresses it through a logarithmic mean on the critical line; mollified moments and smoothed counting
functions are of the same kind. The theorem proved here is that **no such bound constrains the
height**: for every amplification constant `C` and every tolerance `ε` there is a displacement whose
bump mass, multiplied by `C`, stays below `ε` on every window, while the bump still attains height
one.

This is a no-go with an exact mechanism, not an impression. It accounts in one line for the family of
results in this field that stall a fixed factor short of their target — the mollified mean-square
floor, the Littlewood/Jensen slope obstruction, the density constants — and it says what a producer
must do instead: **control a supremum at unknown resolution, not an average at fixed resolution.**
It is the quantitative form of the earlier finding that the hypothesis is a separation target rather
than a resolution target.

## What is now open

`[OPEN CORE]` unchanged in shape but sharper in kind: an unconditional bound `U(t) < 1`.

By the above it cannot come from any average of the divisor. By the non-holomorphy of the angular
kernel it cannot come from the Hadamard/logarithmic-derivative machinery alone. What the holomorphic
side does supply, and the corpus already owns, is `deriv (logDeriv Xi) z = −Σ_ρ (z − ρ)⁻²`, which
gives the exactly computable combination

    Σ_ρ (δ_ρ² − (t − Im ρ)²)/|1/2 + it − ρ|⁴ = −Re (logDeriv ξ)'(1/2 + it),

so that `Σ_ρ δ_ρ²/|1/2+it−ρ|⁴ = ½[C(t) − Re (logDeriv ξ)'(1/2+it)]` with `C(t) = Σ_ρ |1/2+it−ρ|^{-2}`.
The single non-holomorphic quantity in the whole picture is `C`, the self-energy of the divisor. That
is the precise object the next step has to reach.

## Lean

`formal/GaloisForLFunctions/RHTower/CriticalLinePoissonPotential.lean` and
`formal/GaloisForLFunctions/RHTower/DisplacementMassBlindness.lean`. Unconditional, axiom-clean.

---

# Part III: the discriminant law, and where the obstruction actually is

## The orbit quadratic

For each zero put `Q_ρ(s) = (s − ρ)(s − (1 − ρ̄))`, the monic quadratic cutting out its
functional-equation orbit. Write `a = s − ρ`, `b = s − (1 − ρ̄)` and `s = 1/2 + it`. Then

    a + b = 2i(t − Im ρ),        b − a = 2 Re ρ − 1,
    a·b   = −[(Re ρ − 1/2)² + (t − Im ρ)²]        (real and ≤ 0),
    disc(Q_ρ) = (b − a)² = (2 Re ρ − 1)²          (a constant, independent of s).

Therefore

    bump_ρ(t) = −disc(Q_ρ) / (4 Q_ρ(1/2 + it)),

equivalently `bump_ρ = 1 − Q_ρ'(s)²/(4 Q_ρ(s))`. Two things follow immediately.

## The hypothesis is squareness

`disc(Q_ρ) = 0` exactly when `Re ρ = 1/2`, and `Q_ρ` is a perfect square exactly then. So

    RH  ⟺  every orbit discriminant vanishes  ⟺  every orbit quadratic is a perfect square,

i.e. **the divisor of ξ is a square for the functional-equation involution**, and the critical-line
potential is the generating function of the discriminants. This is the hypothesis as a statement of
pure algebra about the divisor, with the analysis confined to the kernel that sums the discriminants.

## Where the obstruction actually is

Every ingredient of `−disc(Q_ρ)/(4 Q_ρ(s))` is a holomorphic function of `s`. The summand of the
critical-weight reader is therefore **not** intrinsically non-holomorphic, which is what Part II left
open. The only non-holomorphic datum is the **matching** `ρ ↦ 1 − ρ̄` — a factorisation of the divisor
into functional-equation orbits, i.e. a half-divisor.

That is the same object the twin-rigidity and symplectic-descent work in this field already isolated
and failed to construct canonically. So the analytic obstruction and the arithmetic obstruction
coincide. It is also the same object as ordinate separation: the partner of `ρ` is the other zero at
its ordinate, so the matching is available exactly when the ordinate slices are understood.

Three lanes that looked independent — the critical-weight reader, the half-divisor, ordinate
separation — are one lane.

## The threshold improves to two

The partner shares the ordinate of `ρ` (`supportPartner` reflects the real part and fixes the
imaginary part). At `t = Im ρ` both bumps are at full height, so

    RH  ⟺  U(t) < 2 for all t.

A factor of two of room — the first quantitative slack in this field for a statement equivalent to
the hypothesis.

## The weight trichotomy

A reader weighting a zero by `δ²/(δ² + τ²)^k` receives `δ^{2−2k}` from that zero at its own ordinate:

| `k` | signal | lane |
|-|-|-|
| 0 | `δ²` → 0 | mass / density / Littlewood–Jensen / mollified moments — blind (Part II) |
| 1 | `1`, scale-free | **the potential** |
| 2 | `1/δ²` → ∞ | Laguerre expression — divergence must cancel against an unbounded sum; circular |

The two retired lanes are the two ways of missing the middle exponent. That is a single explanation
for two independent closures, and it says the surviving weight is unique.

## Lean

`formal/GaloisForLFunctions/RHTower/OrbitQuadraticDiscriminant.lean`. Unconditional, axiom-clean.
Headlines: `poissonBumpTerm_eq_discriminant_ratio`,
`riemannHypothesis_iff_forall_xiOrbitQuadratic_eq_sq`,
`riemannHypothesis_iff_forall_poissonPotential_lt_two`.

## Next

The open core is now: **produce the functional-equation matching, or a substitute that supplies the
discriminants without it.** Note that the sum of all discriminants is not what is needed — that is a
mass and is blind. What is needed is each discriminant attached to its own quadratic.

---

# Part IV: the matching is free — correction to Part III

## What was wrong

Part III named the missing datum the *matching* `ρ ↦ 1 − ρ̄`, and identified it with the half-divisor
obstruction. That identification is withdrawn.

In the spectral coordinate `z_ρ = (ρ − 1/2)(−i)` the partner is the **complex conjugate**:

    z_{σρ} = z̄_ρ.

So the matching is the pairing of the non-real zeros of a real entire function with their
conjugates. It requires no choice, there is nothing to construct, and it is unrelated to the failure
to build a canonical square root of the divisor. The corpus in fact already owned the copy-level
version of this (`xiSpectralPoint_lineConj`). Part III's first conclusion — the hypothesis is
squareness of the divisor under the involution — stands. Its second is false.

## What the matching buys: a linear form

Attach to each zero its Blaschke factor at a real point,

    B_ρ(t) = (t − z̄_ρ)/(t − z_ρ).

It is unimodular on ℝ, equals `1` exactly when `ρ` is on the critical line, and `B_{σρ} = conj B_ρ`.
Then

    bump_ρ(t) = ‖1 − B_ρ(t)‖² / 4 = (1 − Re B_ρ(t)) / 2,
    (1 − B_ρ) + (1 − B_{σρ}) = 4 bump_ρ,     hence     Σ_ρ (1 − B_ρ(t)) = 2 U(t).

**The potential is linear in the Blaschke defects, not quadratic.** That is a real simplification: a
statement about a sum of unimodular defects rather than a sum of squares.

## Where the difficulty actually sits

    1 − B_ρ(t) = 2i (Re ρ − 1/2) / (t − z_ρ).

The defect is **the resolvent at the zero, weighted by its displacement**. The holomorphic data of
`Ξ` deliver the unweighted power sums

    p_k(t) = Σ_ρ (t − z_ρ)^{-k} = (−1)^{k−1}/(k−1)! · (d/dt)^{k−1} (Ξ'/Ξ)(t),    k ≥ 1,

and nothing else of this shape. No combination of them attaches the displacement to its own
resolvent, because the displacement is the imaginary part of the point while the power sums are
conjugation-symmetric — the odd-in-displacement part cancels between a zero and its partner, and
what survives is even, with the wrong power of the modulus (the weight trichotomy of Part III).

So the open core is now sharp and standard-shaped:

`[OPEN CORE]` **weight the resolvent by the displacement** — produce `Σ_ρ δ_ρ /(t − z_ρ)` from
`Ξ`, or bound its imaginary part below `2` in absolute value.

## A lead, honestly flagged

The power sums `p_k(t)` are exactly the data of Hermite's real-root criterion: all `z_ρ` real implies
the Hankel form `(p_{i+j+2})_{i,j}` is positive semidefinite, since it equals `Σ_ρ P(u_ρ)²` for
`u_ρ = 1/(t − z_ρ)` and `P` the real polynomial with those coefficients. That is a *computable*
positivity hierarchy implied by the hypothesis, localised at every real base point `t`.

This is the same circle of ideas as Jensen polynomials, Turán inequalities and hyperbolicity, which
this field has already worked and which are global at one base point. The new element would be the
localisation to every `t`, which is what the weight analysis says is required — an averaged or
single-base criterion is exactly what fails. Before pursuing it, the corpus's real-rootedness and
Jensen assets must be audited for the localised form; it should not be built twice.

## Lean

`formal/GaloisForLFunctions/RHTower/SpectralBlaschkeMatching.lean`. Unconditional, axiom-clean.
Headlines: `xiSpectralPointSupport_supportPartner`, `one_sub_xiBlaschke`,
`poissonBumpTerm_eq_normSq_one_sub_xiBlaschke`, `one_sub_xiBlaschke_add_partner`.

---

# Part V: localised Hermite positivity

## Corpus audit first

| asset | what it gives | where it is anchored |
|-|-|-|
| `secularHankel_posSemidef` | finite real spectrum ⟹ PSD Hankel of power sums | finite, abstract |
| `finiteMatrix_unweightedTraceHankel_nonneg_implies_schur_real` | finite Hermite–Sylvester **converse** | finite matrices |
| `jensenPoly`, `JensenQuarticXi`, `GammaRenormalizedTuranWindow` | Jensen/Turán hyperbolicity for Ξ | **one base point** |

All of it is either finite-dimensional or anchored at a single base point. Part II showed that a
criterion at a fixed anchor cannot see a near-line zero: the signal has height 1 but width `|δ|`, and
it sits at the ordinate of the zero. So the missing shape is not a new inequality — it is the same
inequality **anchored everywhere**.

## The construction

Fix real `t` off the spectral divisor, `u_q = (t − z_q)^{-1}`.

**Separation** (`exists_spectral_separation`). A point off the divisor stays a positive distance from
all of it: only finitely many spectral points lie within a unit of `t` (local finiteness), each at
positive distance; the rest are at distance ≥ 1. Hence `‖u_q‖` is bounded and `Σ‖u_q‖²` converges,
dominated by the fixed Cauchy weight.

**Power sums.** `p_k(t) = Σ_q u_q^k` converges for `k ≥ 2`, and
`p_2(t) = −(logDeriv Ξ)'(t)` (`spectralPowerSum_two`, via the corpus's Mittag-Leffler
differentiation). These are holomorphic data.

**The identity** (`hermiteForm_eq_tsum_sq`), unconditional:

    Σ_{i,j} c_i c_j p_{i+j+2}(t) = Σ_q P(u_q)²,     P(x) = Σ_i c_i x^{i+1}.

**Positivity** (`hermiteForm_re_nonneg_of_riemannHypothesis`). Under the hypothesis every `u_q` is
real, so the right side is a sum of squares of reals: the form is a nonnegative real at **every**
base point and **every** real test vector.

**Falsifiability** (`not_riemannHypothesis_of_hermiteForm_re_neg`). One negative value refutes.

**Where negativity lives** (`hermiteTestValue_lineConj`). The line conjugation acts on the localised
resolvent as complex conjugation, so a zero and its partner contribute `P(u)²` and its conjugate: an
orbit contributes `2 Re P(u)²`. On-line zeros contribute squares of reals, which are `≥ 0`. So the
only possible source of a negative value is an off-line orbit — and that is exactly the object the
whole lane is trying to detect.

## What this is and is not

It **is** the first criterion in this lane anchored at every base point rather than one, which is the
shape the weight analysis demanded, and it is falsifiable by a single evaluation.

It is **not** yet a criterion for the hypothesis. The converse needs the negative contribution of one
orbit to outweigh the positive contributions of all the on-line zeros, i.e. a comparison against the
local clustering `Σ 1/(t−γ_k)²` — the same uncontrolled quantity that made the inner-band route
circular. The corpus's finite Hermite–Sylvester converse does not transfer to an infinite divisor.

`[OPEN CORE]` a choice of test vector `P` for which the on-line contribution is controlled — for
instance one concentrated so that `P(u)` is small on the real `u`'s and large with argument near
`π/2` on a complex pair. The localisation is what makes such a choice conceivable: `t` can be placed
at the ordinate where the pair sits.

## Lean

`formal/GaloisForLFunctions/RHTower/LocalHermitePositivity.lean`. Unconditional, axiom-clean.

---

# Part VI: the test vector

Part V left one thing open: a test vector making the on-line contribution small. It is the **high odd
monomial, anchored at the ordinate of the suspected zero**.

    P(x) = x^{2n+1},   base point t = Im ρ,   test vector supported on the single index 2n.

The Hermite form then collapses to one power sum:

    Σ_{i,j} c_i c_j p_{i+j+2}(t) = p_{4n+2}(t).

## Why the sign is automatic

At `t = Im ρ` the spectral point of `ρ` sits directly above or below the base point:
`t − z_ρ = iδ`. So the resolvent is **purely imaginary**, `u_ρ = −i/δ`, and the partner's is `+i/δ`.
A purely imaginary number raised to an exponent `≡ 2 mod 4` is a *negative real*:

    (±i/δ)^{4n+2} = −δ^{-(4n+2)}.

So the off-line orbit contributes `−2/δ^{4n+2}` — negative for **every** `n`, with no cancellation
and no coefficient tuning. The anchoring is what buys this: only at the zero's own ordinate is the
resolvent exactly imaginary.

## Why the on-line contribution is suppressed

If every other zero satisfies `|t − z| ≥ δ'` with `δ' > δ`, then each other resolvent has modulus
`≤ 1/δ'`, and

    |u|^{4n+2} ≤ (1/δ')^{4n} · |u|²,

so the whole rest of the divisor is bounded by `(1/δ')^{4n} · S` with `S = Σ‖u‖²` finite. Meanwhile
the off-line term carries `(1/δ)^{4n}`. The ratio is `(δ/δ')^{4n} → 0`, so for `n` large the negative
term wins by any margin. Formally: choose `N` with `(δ/δ')^N < |A| / (Sδ² + 1)`; then `n = N` works.

## The detection theorem

**An off-line zero strictly closer to the critical line than to any other zero, in the localised
metric at its own ordinate, is refuted by a single evaluation of a single derivative of
`(logDeriv Ξ)`.** (`exists_monomial_hermite_witness`, `not_riemannHypothesis_of_monomial_witness`.)

The degree `n` is not a parameter to optimise — it only has to clear a fixed geometric ratio against
a fixed constant.

## What this does and does not settle

**Settled:** every off-line configuration in which the offending zero is *isolated at the scale of
its own displacement*. For those, the hypothesis is decided by one number.

**Not settled:** the clustered regime, where a zero's displacement exceeds its distance to a
neighbour's ordinate. That is the same local-clustering obstruction that made the inner-band route
circular — and the reason is now visible: **the retired inner-band computation is the case `n = 0` of
this family**, the one member with no geometric suppression at all. Every `n ≥ 1` is strictly
stronger, and the family only fails where clustering defeats the suppression.

`[OPEN CORE]` a configuration-independent lower bound on the separation `δ'/δ`, or a second test
family that handles clusters — for instance anchoring between two clustered zeros rather than at one
of them, so that the cluster contributes coherently rather than competitively.

## Lean

`formal/GaloisForLFunctions/RHTower/HermiteMonomialWitness.lean`. Unconditional, axiom-clean.

---

# Part VII: stepping back — the gap is a homogeneity degree

## The standing diagnosis, corrected

The usual statement is: we control mass, frequency, energy; we need height; no conversion law
connects them. The first two clauses are right. The third is wrong, and the correction is the useful
part.

**Conversion laws from averages to heights are not missing.** Sobolev embedding, Bernstein, and
Landau–Kolmogorov all do exactly that. The last is even *sharp* on our family: for one bump,

    ‖b‖_∞² ≍ ‖b‖_{L¹} · ‖b'‖_{L^∞},      πδ · (c/δ) = πc,

with `δ` cancelling exactly. So the conversion exists and is tight. It is useless here because it
needs `‖b'‖_∞ ~ 1/δ` — a scale, and the only scale in the problem is `δ`, the unknown. **Every
conversion law is available and every one is vacuous**, which is a stronger and more precise
statement than "no conversion law exists".

## The dimensional fact

The bump family is one profile acted on by the scaling group (`bumpKernel_scaling`):

    bump(c·d, c·g, c·t) = bump(d, g, t).

So every functional of the family is graded by homogeneity degree, and the grading is a complete
obstruction:

| functional | degree | decides RH? | computable from ξ? |
|-|-|-|-|
| peak / sup | **0** | yes | no |
| total variation | **0** | yes | no |
| count of bumps | **0** | yes | no |
| every `∫ F(bump)`: all `L^p` (p<∞), mollified moments, smoothed counts, any nonlinear average | **1** | no | yes |

`comp_bumpKernel_peak` — `F(bump(d,g,g)) = F(1)` for every `F` and every `d ≠ 0`.
`integral_comp_bumpKernel` — `∫ F(bump) = d · (profile integral)` for every `F` and every window;
the factor `d` is exactly the Jacobian.

That second one strictly generalises Part II's mass blindness, which was the case `F = id`. It rules
out not just `L¹` but **every pointwise-nonlinear average**, at one stroke.

## Consequences

**Negative.** No functional built by "apply something pointwise, then integrate" can reach the
hypothesis. Not a deficiency of any particular estimate — a dimensional impossibility.

**Positive, and this is the useful half.** The degree-zero class is *not* just the sup. Total
variation is degree zero (a bump rises once `0 → 1` and falls once back, so `TV = 2` whatever its
width), and so is the count. All three decide the hypothesis. The target is wider than it looked, and
`‖f‖_∞ ≤ ½ TV(f)` is a *free* conversion inside the degree-zero class.

**What a producer must do.** No conversion changes the degree. A producer must **supply a scale**,
and the only intrinsic scale in the zero distribution is the ordinate spacing. That is the single
reason the mollified floor, the Littlewood/Jensen slope obstruction, the inner band, and the
clustered regime of the monomial witness are all *the same wall*. They are not four problems.

`[OPEN CORE]` an unconditional scale: a lower bound on the local ordinate spacing, or a substitute
for one. Everything in this lane now reduces to that single object.

## Lean

`formal/GaloisForLFunctions/RHTower/ScalingDegreeLaw.lean`. (The `TV = 2` observation is elementary
reasoning, stated here, not Lean-certified — the Lean content is the scaling covariance, the
degree-zero peak, and the degree-one law for all `F`.)

---

# Part VIII: the zeros are a count, not a quantity

## Three claims, and their status here

**(a) "You cannot produce a function that creates the zeros."** This is a theorem in this field, and
Part VII named its cause. The deciding invariant is degree zero, and the degree-zero class contains an
**integer-valued** member — the count. Every analytic functional of `ξ` is continuous; the count is
not. So no limit of measurements produces it. That is exactly the deformation blindness recorded as
CANNOT-422, now with its mechanism identified rather than observed.

**(b) "The zeros are a property of the ambient geometry, not of ζ."** Already a theorem here, in
`FiniteDivisorPrefixNonselection`: the class of functional-equation-symmetric sources with arbitrary
finite Euler heads admits **both** a fixed-orbit extension by a new critical-line pair **and** a
free-orbit extension at an arbitrary generic off-line point of the strip, each preserving every
prescribed multiplicity. The local data of the zeta function therefore do not select the orbit type.
Orbit type is a property of the symmetric ambient class.

**(c) "Rational versus complex."** Exact, not metaphorical. The involution whose free orbits are being
counted is `σ = (functional equation) ∘ (complex conjugation)`: `ρ ↦ 1 − ρ̄`. The first factor is
arithmetic, the second archimedean. `riemannHypothesis_iff_supportPartner_eq_id` says the hypothesis
is precisely that **these two involutions agree on the divisor** — the arithmetic symmetry and the
archimedean symmetry are the same symmetry there.

## The conversion inside degree zero

What was missing was the link between the two degree-zero descriptions developed separately in this
lane: the *count* of free orbits per slice, and the *analytic* potential. It is now proved.

At the ordinate `t`, every off-line point of that ordinate sits directly above or below the base
point, so its bump is at full height and contributes exactly `1`:

    #(free part of the slice at t) ≤ U(t),      #(free part) = 2 · #(left half-slice).

So one free orbit forces `U(t) ≥ 2` — the threshold recovered from the **count**, not from the pair.
And `RH ⟺ the free-orbit count vanishes at every ordinate`.

The potential is therefore not a quantity that happens to detect zeros. **It is an upper envelope of
a count.** The object being decided is the number of free orbits of an involution acting on a divisor
— a property of the symmetry, qualitative and integer-valued. The analysis enters only to bound that
count from above, which is the one direction the degree law leaves open.

## What this says about the producer

Not: manufacture the zeros from the source. That is blocked by (a) and (b).

Instead: **constrain the symmetric ambient geometry so that free orbits cannot occur in it.** The
target object is `#(free σ-orbits) = 0` — an equivariant statement about a ℤ/2-action, which is where
the torsion reading of this lane (`divisorNorm`, the 𝔽₂ Galois norm, the Tate-cohomological form)
already pointed. Part VII explains *why* that is the right home: equivariant invariants are
scale-invariant by construction, hence degree zero, hence the only kind that can decide this.

`[OPEN CORE]` unchanged in substance and clearer in shape: an upper bound on the free-orbit count.
The degree law says it cannot come from an average; (a) says it cannot come from a continuous
deformation; (b) says it cannot come from the source's local data. What remains is a rigidity of the
ambient symmetric class itself.

## Lean

`formal/GaloisForLFunctions/RHTower/FreeOrbitCountBound.lean`. Unconditional, axiom-clean.

---

# Part IX: attacking the ambient rigidity — the answer is negative, and sharp

Part VIII said a producer must constrain the ambient symmetric class so that free orbits cannot
occur, and pointed at the equivariant/torsion reading as the natural home. This part attacks that and
finds it cannot work — for a reason that is worth more than the attempt.

## The computation

Over `𝔽₂` the norm of the reflection is `N f = f + f∘σ`, with `N ∘ N = 0`. The left half of the strip
is a **canonical section** of the involution: `σ` exchanges the halves and fixes the line, so
`1_{Re < 1/2}` picks exactly one point of each free orbit, with no choice. Hence

    N (f · 1_{Re < 1/2}) = f

for every invariant `f` vanishing on the fixed locus (`divisorNorm_leftSection`). So the coboundary
is **surjective onto the cochains vanishing on the critical line**, and

    Tate cohomology of the divisor = functions on the critical line alone.

**The free orbits are exactly what the cohomology discards.**

## The sharp form: one cochain

    N (1_{Re < 1/2}) = 1_{Re ≠ 1/2}          (`divisorNorm_leftSection_one`)

The coboundary of the left-half indicator is the characteristic function of the off-line part. So

    RH ⟺ the coboundary of one explicit cochain vanishes.

## What this settles

**Negative, and this is the point.** No equivariant invariant, localisation or completion can produce
the hypothesis. All of them compute *cohomology*, and the hypothesis is **not a cohomology class** —
it is the statement that a *coboundary* vanishes. Passing to cohomology is precisely the operation
that throws it away.

That is the cause of the localisation blindness recorded long ago in this field, and it explains why
the two-torsion reading — correct as a *description* of RH — can never be a *producer*. The
description and the mechanism were being conflated.

**Positive redirection.** The object to control is `im(N)`, which is the characteristic function of
the free part — the boundary map itself, not any quotient in which it has been divided out. That is
a strictly smaller and more concrete target than "an equivariant rigidity", and it is consistent with
everything else in this lane: `im(N) = 0` is the free-orbit count vanishing (Part VIII), which is the
degree-zero invariant (Part VII), which the potential envelopes (Part VIII).

So the four descriptions — `sup U < 2`, free-orbit count zero, `N(1_{Re<1/2}) = 0`, ordinate
injectivity — are one statement, and the obstruction to each is the same: **none of them is reachable
by an averaged, continuous, or cohomological functional.** Every standard machine is now excluded by
a named theorem rather than by repeated failure.

`[OPEN CORE]` control of `im(divisorNorm)`, equivalently an upper bound on the free-orbit count. The
excluded routes are now: averages (Part II, VII), continuous deformations (Part III), the source's
local data (Part VIII), and cohomology (this part).

## Lean

`formal/GaloisForLFunctions/RHTower/DivisorTateCohomology.lean`. Unconditional, axiom-clean.

---

# Part X: the boundary map

Part IX said: stop looking at cohomology, control `im(N)`. This part describes it completely.

## The image, exactly

    ∃g, N g = f   ⟺   f∘σ = f  and  f vanishes on the critical line

(`mem_range_divisorNorm_iff`). Forward is immediate; backward is the canonical left-half section of
Part IX. So the image is an **explicit subspace** — no quotient taken anywhere — and a coboundary is
freely determined by **one bit per free orbit**, its values on the left half-slices, unconstrained
(`divisorNorm_leftSection_of_mem_range`).

`im N = 0` is the hypothesis. The free orbits are a basis of the image.

## What the rank counts

The reflection preserves ordinates, so `N` is **fibred over the ordinate map** and

    rank N = Σ_t (free-orbit count of the slice at t).

Each slice is at most one critical-line point plus free orbits in pairs, so over any finite set of
ordinates (`sum_ncard_xiSlice`):

    (total zero count) = (critical-line count) + 2 · (free-orbit count)

and (`riemannHypothesis_iff_window_counts_agree`)

    RH ⟺ the two counts agree on every window.

**That is the classical relation between `N(T)` and `N₀(T)`, in exact finite form.**

## The unification, stated plainly

This lane and the classical count of critical-line zeros **decide the same integer**. They are not
competing routes and should not have been treated as such. What differs is the *access*:

| | reaches the deficiency by | verdict |
|-|-|-|
| classical (Levinson, mollified moments) | averaging over a window | forbidden by the scaling degree law (Part VII) — averages are degree 1 |
| boundary map | fibrewise, one ordinate at a time | the resolution the degree law requires |

So the entire gain of this lane over the classical one is **locality**, and that is exactly the
property Part II proved to be necessary. This also retroactively explains the mollified-moment
terminus: it is a degree-1 tool aimed at a degree-0 integer.

## Where this leaves the problem

Nothing here bounds the rank. What is now established:

- the target is completely explicit (`im N`, an honest subspace);
- it is a **sum of local integers**, one per ordinate;
- it coincides with the classical deficiency `(N − N₀)/2`;
- no quotient, average, deformation or cohomology is concealing it.

`[OPEN CORE]` **an upper bound for that sum of local integers.** That is the single remaining object
in this entire field. Every other formulation in Parts I–X is equivalent to it, and every standard
machine has been excluded by a named theorem.

## Lean

`formal/GaloisForLFunctions/RHTower/BoundaryMapImage.lean`. Unconditional, axiom-clean.

---

# Part XI: bounding the local integers

A bound on `Σ_t #(free orbits at t)` **is** the hypothesis. None is proved here. What is proved is
the shape any bound must have, and it turns out to be very restrictive.

## The unconditional bound that does exist

    #(free orbits at t)  ≤  Σ_ρ 1/(1 + (t − Im ρ)²)

(`ncard_xiSliceLeft_le_cauchyWeight`), via `2·#(free) ≤ U(t) ≤ 2·Σ_ρ 1/(1+(t−Im ρ)²)`. The right-hand
side is the standard Cauchy-weighted local zero density — of size `≍ log(height)`. This is the
natural estimate, and it is useless. The next result says why, and why *every* estimate of its shape
is useless.

## No lossy bound is of any use

The free-orbit count is an **integer** and `2·#(free) ≤ U(t)`. Hence:

- `U(t) < 2`  ⟹  `#(free orbits at t) = 0`   (`xiSliceLeft_eq_empty_of_poissonPotential_lt_two`)
- `U(t) ≤ B` with `B ≥ 2`  ⟹  **nothing at all**

The threshold is exactly `2` and carries no slack. So:

> **The required estimate is uniform in the height — an absolute constant.** Every analytic estimate
> in this field grows with the height.

That is the difficulty in its final form. It is *not* that the available bounds are weak. It is that
they have the wrong **dependence on the height**, and the target admits no lossy version. An estimate
losing a constant factor, or a factor of `log`, is not a partial result — it is no result.

## The cause: integrality removes the slack

This is the quantisation of Part I coming back as the final obstruction. Against a **real-valued**
target, an estimate within a constant factor is progress. Against an **integer**, only an estimate
crossing a fixed threshold is of any use. Every approximation method produces the first kind; the
problem requires the second.

## The diagnostic arc, closed

| the hypothesis is | the apparatus produces |
|-|-|
| integer-valued | real-valued |
| scale-invariant (degree 0) | degree 1 |
| fibrewise / local | averaged over windows |
| uniform in height | growing in height |

Four mismatches, each now carrying a named theorem rather than an impression. Everything in Parts
I–XI is one statement seen from eleven sides, and the reason each standard machine fails is no longer
an observation but a proof.

`[OPEN CORE]` an absolute-constant, height-uniform bound `U(t) < 2`. There is nothing else left in
this lane, and no weaker version of it is worth proving.

## Lean

`formal/GaloisForLFunctions/RHTower/LocalCountBound.lean`. Unconditional, axiom-clean.

---

# Part XII: the shape

Parts I–XI drove the problem to "bound an integer below an absolute threshold". That is a **size**
statement, it admits no lossy version, and it is a dead end. It is also the wrong reading of the
object.

## What the object actually is

The hypothesis says: **an involution on a discrete set has no free orbits.** Every point is fixed.
That is not a size statement at all.

Over a base field this shape has a name. A finite real algebra is `ℝ^r × ℂ^s`; its complex points
pair under conjugation; "no free orbits" is `s = 0`. So

> **RH is the statement that the divisor algebra is totally real.**

## Totally-real statements are decided by signatures

The trace form of `ℝ^r × ℂ^s` has signature `(r + s, s)`: each real factor gives a positive
direction, **each complex pair gives one positive and one negative direction**. Hence

    s = 0  ⟺  the trace form is positive semidefinite,     s = the negative index.

That trace form is exactly the localised Hermite form of Part V. So the target is not an estimate —
**it is a signature computation.** The orbit decomposition confirms the identification:

| | contribution to the form | |
|-|-|-|
| a zero and its partner | `w²` and its conjugate, i.e. `2·Re(w²)` | one real direction per orbit (`orbitTraceContribution`) |
| fixed orbit | square of a real number | never negative (`orbitTraceContribution_nonneg_of_real`) |
| free orbit | strictly negative for the monomial anchored at its own ordinate, every degree | genuinely indefinite (`orbitTraceContribution_neg_of_offLine`) |

## The shadow that is classically accessible

For a real algebra, `sign(disc) = (−1)^s`. So a **discriminant detects the parity of `s` and nothing
more** — which is precisely the parity law this lane already had (`odd_ncard_xiSlice_iff`), and
exactly as much as a single determinant can see.

So two findings that looked independent are one: **the parity law is the determinant of the trace
form; the counting problem is its signature.**

And signatures are computed from **sign patterns of principal minors** — here, minors of the Hankel
matrices whose entries are the localised power sums `p_k(t)`, each an explicit derivative of
`logDeriv Ξ`. That is a concrete object, not a bound.

## Where else this shape appears

- **Lehmer's conjecture.** Either the trivial value or a gap bounded away by an absolute constant,
  uniform in the degree; lossy bounds (Dobrowolski) exist and do not suffice; and the hard case is
  the *reciprocal*, i.e. self-symmetric, one. Same structure, same reason for difficulty: the
  symmetry.
- **Totally real fields / positive-definite trace forms.** The direct classical home.
- **Index and signature theorems.** An integer target; analytic tools produce approximations; the
  integer is reached by a localisation formula, not an estimate.
- **Wall-crossing.** The count is locally constant off a discriminant locus; the hypothesis says we
  sit on the empty side.

## What changes

The question stops being "how do we get the constant down to 2" and becomes **"what computes this
signature?"** Signatures come from localisation formulas, from Sturm sequences, from spectral
decompositions — not from sharper averages. That is a different search, and it is the one consistent
with every no-go in Parts I–XI.

`[OPEN CORE]` a computation of the negative index of the localised trace form. The entries are
explicit; the minors are explicit; what is missing is a reason for their signs.

## Lean

`formal/GaloisForLFunctions/RHTower/TraceFormSignature.lean`. Unconditional, axiom-clean.

---

# Part XIII: what computes the signature — a sign

Part XII turned the target into a signature. Signatures of *this* kind — "a real entire function has
only real zeros" — have a classical computer: the **Hermite–Biehler / Nevanlinna** criterion. Such a
function has only real zeros exactly when its logarithmic derivative maps the upper half-plane into
the lower.

## Termwise

The logarithmic derivative is a sum of resolvents, and

    −Im (z − z_ρ)^{-1} = (Im z − Im z_ρ) / |z − z_ρ|²          (`nevanlinnaTerm_eq_neg_im_inv`)

- **on-line zero** → real spectral point → term positive throughout the open upper half-plane
  (`nevanlinnaTerm_pos_of_im_eq_zero`);
- **off-line zero** → its orbit has a member of positive spectral height `c`, and directly beneath
  it at height `c/2` the term is exactly `−2/c` (`nevanlinnaTerm_witness_value`).

Hence `RH ⟺ every term is positive at every point of the open upper half-plane`
(`riemannHypothesis_iff_forall_nevanlinnaTerm_pos`).

## RETRACTION — this is not a new route

I framed this as opening technology the no-gos don't reach. That was wrong, and a corpus search I
should have run first shows it:

| already in the corpus | content |
|-|-|
| `StrictHermiteBiehlerGivesRH` | **strict** Hermite–Biehler for `XiC + i·XiC'` gives RH outright; the known gap is *strictness, not semidefiniteness* |
| `SuzukiLagariasMeromorphicInner` | Lagarias–Suzuki (2006) Thm 4, specialised to ξ |
| `SuzukiFiniteApertureHermiteBiehler`, `DeBrangesFiniteOrderRigidity`, `DeBrangesGaugeInvariance` | a developed de Branges lane |
| `SuzukiCoalescingHalfPlaneUniqueness` | positive-real-part source on ℂ₊ forces RH |
| `PrimeDelayHerglotzNoGo` | a no-go on the naive Herglotz construction |

So the reformulation is classical (Pólya), and the corpus holds it in **stronger** form with the gap
already localised.

**And the technology claim fails on its own terms.** `−Im(Ξ'/Ξ)` is harmonic on ℂ₊ *minus the
non-real zeros*. A maximum principle on the half-plane needs the singularity set — which is exactly
the unknown. The argument is circular, and I should have seen that before writing the claim rather
than after.

**What survives:** the termwise computation is correct and the Lean is sound — the exact witness value
`−2/c`, and the equivalence. It is a small clean artifact, not a new lane.

**The general constraint this instance illustrates**, which is the real output: *a reformulation that
has a classical computer has already been attempted.* 150 years of work has exhausted the classical
computers. Novelty has to live in the **computer**, not in the reformulation. Parts XII and XIII both
reformulated; neither produced a new computer.

## Lean

`formal/GaloisForLFunctions/RHTower/NevanlinnaSignCriterion.lean`. Unconditional, axiom-clean.
