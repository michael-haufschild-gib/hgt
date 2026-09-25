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
