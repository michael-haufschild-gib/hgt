# Critical-locus criticality, Hessian classification, and finite crystalline transversality

- **ID:** ULF-FIELD-2
- **Stage:** 2-fully-proven
- **Type:** THEOREM PACKAGE (paper, dependency-closed, unconditional)
- **Parents:** ULF-FIELD-1 (critical-locus-geometry-field-charter.md, stage 1)
- **Scientific status:** `[PROVED HERE]` Θ1, Θ2(i)–(v), Θ3.1–3.2. Novelty verdicts per-theorem
  below (hostile pass executed 2026-08-09). `[NOT RH]` `[NO LEAN — user directive]`

## Setting (all definitions self-contained)

**Configurations.** 𝒵 = locally finite multisets Z in the strip S = {0 < Re s < 1}, invariant
under the reflection group R = ⟨σ: s ↦ 1−s, κ: s ↦ s̄⟩, with finite counting N_Z(T) ∀T.
An RH configuration has supp Z ⊆ {Re s = 1/2}.

**Admissible splitting.** If Z₀ contains 1/2 ± iγ each with multiplicity ≥ 2 (γ > 0), set for
|t| < 1/2:
Z_t := Z₀ − 2·{1/2+iγ, 1/2−iγ} + {1/2+t+iγ, 1/2−t+iγ, 1/2+t−iγ, 1/2−t−iγ}.
Then Z_t ∈ 𝒵 and **Z_t = Z_{−t} as multisets**. Multi-splittings at distinct ordinates
γ₁ < … < γ_m with parameters t = (t₁,…,t_m) are defined the same way; Z_t depends only on
(t_j²)_j. Simple line zeros admit no continuous R-invariant exit: an off-line point forces its
σκ-partner, so a departing zero must have even multiplicity — off-line motion emanates only
from multiple zeros.

**Spectral-type functionals.** For F holomorphic on a neighborhood of the critical line with
F = F∘σ and F = F^κ (F^κ(s) := conj(F(s̄))), define the relative functional on finite
perturbations Φ_F(Z; Z₀) := Σ_{Z∖Z₀} F − Σ_{Z₀∖Z} F (finite sum). All corpus criteria of
producer type (Weil forms, Li coefficients λ_n with F_n(s) = 1 − (1−1/s)^n, Báez-Duarte-type
squared sums) are of this form or smooth functions of finitely many such.

## Θ1 — universal criticality (PROVED)

**Theorem.** Every function on 𝒵 — arbitrary value space, no regularity — satisfies
Φ(Z_t) = Φ(Z_{−t}) in each splitting parameter. If Φ∘Z is differentiable, all odd
t-derivatives vanish at t = 0: the RH locus is a critical locus of every criterion
simultaneously, in every direction.

*Proof.* Z_t = Z_{−t} as multisets (the quadruple {1/2±t±iγ} is t ↦ −t invariant); a function
of the configuration takes equal values. ∎

*Novelty verdict:* `[ORGANIZING LEMMA — folklore-adjacent]`. The heat-flow instance is
Newman's "barely true" dictum, proved by Rodgers–Tao (Λ_DB ≥ 0); "zeros move in pairs" is
folklore. The universal all-directions statement was not found stated, but the proof is a
triviality; Θ1 claims no standalone novelty. Its role: it makes the corpus's
conjugation-no-sign counterexample, the Σ-of-squares carrier law, and five-lanes-one-wall
into one mechanism, and forces all classification to second order — where Θ2 lives.

## Θ2 — Hessian classification of spectral-type criteria (PROVED)

Let φ_j(t) := F(1/2+t+iγ_j) + F(1/2−t+iγ_j) + F(1/2+t−iγ_j) + F(1/2−t−iγ_j)
− 2F(1/2+iγ_j) − 2F(1/2−iγ_j).

**(i) Exact separation.** For any multi-splitting, Φ_F(Z_t; Z₀) = Σ_j φ_j(t_j) — exactly, not
merely to second order — by additivity of Σ F over the multiset. Cross-terms between distinct
ordinates are identically zero.

**(ii) The weight.** φ_j'(0) = 0 and φ_j''(0) = 4 Re F''(1/2+iγ_j) =: w_F(γ_j).
*Proof.* φ_j'(t) = F'(1/2+t+iγ) − F'(1/2−t+iγ) + F'(1/2+t−iγ) − F'(1/2−t−iγ) vanishes at 0.
φ_j''(0) = 2F''(1/2+iγ) + 2F''(1/2−iγ) = 4Re F''(1/2+iγ) using F = F^κ. ∎
Hence the Hessian of Φ_F at Z₀ is the diagonal form Σ_j w_F(γ_j) t_j².

**(iii) Per-zero necessity.** Suppose Φ_F has the detector property at Z₀: for every
admissible splitting family, Φ_F(Z_t; Z₀) ≤ 0 for all small t (off-line motion is penalized;
orientation conventional). Then w_F(γ) ≤ 0 for EVERY ordinate γ admitting a splitting.
*Proof.* Single splittings are admissible; φ_j(t) ≤ 0 = φ_j(0) forces φ_j''(0) ≤ 0. ∎
By (i) the detector penalizes each quadruple separately: **detection is per-zero of
necessity** — the corpus law "nonnegative-sum criteria are never weaker than RH-per-zero"
holds for the entire spectral-type class, not per-instance.

**(iv) Canonical mixture.** The second-order jet of Φ_F on the splitting strata is
Σ_j w_F(γ_j)t_j², an element of the simplicial cone spanned by the per-ordinate forms
{−t_j²}; extreme rays = single-ordinate reality tests. The jet determines w_F and nothing
else: two spectral-type criteria are second-order equivalent at the RH locus iff their weight
functions agree. The corpus's producer collapse (~96 producers = one identity;
re-encoding template) is the statement that the recorded producers share one weight ray.

**(v) Trichotomy as Morse data.** Group 1 (weaker-than-RH): w_F ≡ 0 on an infinite ordinate
set — such F are blind to splittings there (constructions: Re F'' vanishing on intervals).
Group 2 (RH-per-zero): w_F < 0 everywhere, criterion = weighted per-zero test. Group 3
(exactly-RH): criteria whose validity requires uniform control of the full infinite diagonal
form. The corpus trichotomy card is the Morse-theoretic classification at a degenerate
critical locus. Composite criteria (smooth functions of finitely many spectral functionals)
have Hessian = diagonal + finite rank (chain rule), and (iii) survives: single-splitting
necessity is unaffected by a finite-rank correction evaluated on one-parameter strata.

*Novelty verdict:* `[CANDIDATE NEW — structure theorem over the space of criteria]`.
Adjacent: Bombieri–Lagarias (1999) prove Li-type positivity for arbitrary multisets — the
same moduli move for ONE criterion family; no classification of the space of criteria, no
Hessian calculus, no necessity theorem found in the pass. Scope honesty: this is a LOCAL
classification at the RH locus (second-order jets on splitting strata); global/group-3
structure is not claimed.

## Θ3 — finite crystalline transversality (PROVED)

Pair configurations with their arithmetic shadow: for even h ∈ C_c^∞(ℝ) let
F_h(ρ) := ∫_ℝ h(x) e^{(ρ−1/2)x} dx (entire; F_h = F_h∘σ ∘… after symmetrization; this is the
explicit-formula kernel: on ρ = 1/2+iτ, F_h(ρ) = ĥ(τ)). Define the shadow of a finite
deformation as the distribution ⟨Δν(Z_t; Z₀), h⟩ := Φ_{F_h}(Z_t; Z₀) — the exact amount the
prime side of an explicit formula would have to absorb to keep the identity.

**Θ3.1 (single splitting has continuous shadow).** For one splitting (γ, t):
⟨Δν, h⟩ = 4∫ h(x) cos(γx)(cosh(tx) − 1) dx,
i.e. Δν has the real-analytic density ρ_{γ,t}(x) = 4cos(γx)(cosh(tx) − 1), which is nonzero
off a discrete set: the shadow is absolutely continuous with full support, never atomic.
*Proof.* F_h(1/2+t±iγ) + F_h(1/2−t±iγ) = ∫h(x)e^{±iγx}(e^{tx}+e^{−tx})dx; subtract the
t = 0 value and sum the two signs. ∎

**Θ3.2 (finite transversality).** For any finite multi-splitting with all t_j ≠ 0 and
distinct γ_j > 0, the shadow density ρ(x) = 4Σ_j cos(γ_j x)(cosh(t_j x) − 1) is not
identically zero; hence the shadow measure has a nonzero absolutely continuous part and is
supported on all of ℝ. Consequently **the finite-splitting strata meet the atomic-shadow
(crystalline) locus only at t = 0**: no finite off-line displacement of zeros is compatible
with an arithmetic side supported on a discrete set — in particular on the lattice
{± log n}.
*Proof.* Expand into exponentials: ρ(x) = Σ_j Σ_{ε,δ ∈ {±1}} e^{(εt_j + δiγ_j)x}
− Σ_j Σ_{δ} 2e^{δ iγ_j x} (coefficients 1 and −2). The frequencies εt_j + δiγ_j are pairwise
distinct across (j, ε, δ) (a collision t_j = −t_k with γ_j = γ_k forces j = k, t_j = 0) and
distinct from the purely imaginary δiγ_j. Exponential functions with distinct complex
frequencies are linearly independent over ℂ (Vandermonde/Wronskian), and the coefficient of
e^{(t_j+iγ_j)x} is 1 ≠ 0. So ρ ≢ 0. A continuous, somewhere-nonzero density defines a measure
with nonzero absolutely continuous part; an atomic measure has none. ∎

**Corollary (where unconditional leverage lives — the tangency calculus).** Within the
moduli, violation of "all zeros on the line" with an atomic positive arithmetic side is an
infinitary phenomenon: it requires an infinite off-line family whose continuous shadow parts
cancel exactly. Quantitative bounds on how far a single zero can sit off the line against the
positivity Λ(n) ≥ 0 of the atomic side are precisely zero-free-region arguments: the
classical 3-4-1/Mertens mechanism is the first tangency estimate between off-line strata and
the crystalline locus. The field thus derives, rather than observes, the corpus's live-lane
map: spectral-side lanes are killed by Θ1/Θ2; the surviving unconditional leverage is
(E1/E3) arithmetic-side tangency — the ZFR/short-interval corridor the corpus already
identified as its wall frontier (zero-free-exponent = MR wall) — and (E2) one-sided
Lee–Yang-type transport, the only mechanisms acting before second order.

*Novelty verdict:* `[CANDIDATE NEW in direction; elementary in proof]`. The active
Fourier-quasicrystal field (Meyer; Kurasov–Sarnak stable polynomials; Alon–Kummer–Kurasov–
Vinzant, Inventiones 2025, Lee–Yang varieties) runs the direction "real-rooted/Lee–Yang ⟹
quasicrystal" and "RH ⟹ zeros quasicrystal-like"; the deformation-transversality direction —
off-line strata vs the atomic locus, with the shadow computed exactly — was not found. The
proofs are elementary; the claim to significance is structural (the unification above), and
per discipline this card does NOT claim standalone depth for Θ3.1/3.2.

## What this package does and does not deliver

Delivers (unconditional, dependency-closed, proved above): the wall-mechanism theorem (Θ1),
the classification making per-zero-ness and the producer collapse theorems instead of
empirics (Θ2), and the transversality theorem locating all remaining leverage on the
arithmetic side (Θ3). Together: the corpus's obstruction table is now derived from one
geometric situation — a degenerate critical locus transverse to a rigid crystalline locus.

Does NOT deliver: any new zero-free region, any group-3 statement, any RH progress. The
field's forward program (stage-1 charter): the infinite tangency calculus — quantifying
Θ3.2's cancellation obstruction for infinite families against Λ ≥ 0 — and the E2 transport
mechanism. These are the two open attacks the classification leaves possible.

## References (collision pass 2026-08-09)

- Bombieri–Lagarias, *Complements to Li's criterion*, J. Number Theory 77 (1999).
- Rodgers–Tao, *The De Bruijn–Newman constant is non-negative*, Forum Math. Pi (2020),
  arXiv:1801.05914.
- Kurasov–Sarnak, *Stable polynomials and crystalline measures*, J. Math. Phys. 61 (2020).
- Alon–Kummer–Kurasov–Vinzant, *Higher dimensional Fourier quasicrystals from Lee–Yang
  varieties*, Inventiones (2025), arXiv:2407.11184.
- Meyer, *Measures with locally finite support and spectrum* (crystalline measures);
  Lev–Olevskii uniqueness line.
- Corpus: rh-criterion-reencoding-template; nonnegative-sum-criteria-are-never-weaker;
  rh-criterion-three-way-classification; conjugation-symmetry-gives-no-positivity;
  weil-carrier-is-sum-of-complex-squares; five-lanes-one-wall; zero-free-region-exponent-is-
  the-mr-wall.

## Log

- 2026-08-09 — package proved and promoted from ULF-FIELD-1 after the three-way collision
  pass. Verdicts recorded per-theorem. No Lean (user directive stands).

## Θ4 — finite evaluation blindness (PROVED, appended 2026-08-09)

**Admissible class.** 𝒜 = spectral-type functionals Φ_F with F holomorphic on a neighborhood
of the line, F = F∘σ, F = F^κ, F nonconstant, and decay F''(1/2+iτ) → 0 as |τ| → ∞ (every
corpus producer satisfies this: Weil tests have Schwartz-decaying ĥ''; Li's F_n'' → 0;
Báez-Duarte-type kernels decay).

> **Theorem (no finite spectral separation).** Let F₁,…,F_k ∈ 𝒜, let Z₀ be any RH
> configuration with infinite support, and fix any displacement 0 < t* < 1/2. Then there is a
> configuration Z* containing an off-line quadruple of displacement exactly t* with
> Φ_{F_i}(Z*; Z₀) = 0 for every i ≤ k.

*Proof.* WLOG the restrictions of the F_i to the line are linearly independent modulo
constants (drop dependent members; a constant F has trivial relative functional). Step 1
(placement): by decay choose an ordinate γ with |Re F_i''(1/2+iγ)| < δ for all i, δ to be
fixed; insert the quadruple {1/2 ± t* ± iγ} and delete two line pairs at γ (equivalently
insert the quadruple minus its on-line collapse; locally finite counting is preserved up to a
bounded discrepancy). The values drift by η_i(δ), |η_i| ≤ C t*² δ by Θ2(ii)'s Taylor bound
with the explicit remainder of φ_i on |t| ≤ 1/2. Step 2 (correction on the line): pick k line
zeros 1/2+iγ₁,…,1/2+iγ_k of Z₀; sliding them, s ↦ Φ_{F_i} has Jacobian
J_{im} = 2 d/ds [Re F_i(1/2+is)]|_{γ_m}. If every k×k determinant of this form vanished for
all choices of (γ_m), the derivatives of the F_i along the line would be linearly dependent
functions, contradicting independence modulo constants (analyticity: a nontrivial relation on
a set with an accumulation point propagates). Choose (γ_m) with J invertible. Step 3 (IFT):
the map s ↦ (Φ_{F_i}) is C¹ with invertible differential at s = 0; for δ small enough the
drift η(δ) lies in the image of a neighborhood, so there is s(δ) = O(t*²δ) restoring all k
values exactly. Set Z* = the resulting configuration. ∎

**Corollary (the Weil criterion cannot be finitely truncated).** For any finite set of test
functions, positivity of the corresponding finitely many Weil forms never implies RH: at
every displacement t* < 1/2 there are value-indistinguishable off-line configurations. The
spectral side has NO finite subcover — the exact dual of the semilocal (finite-place)
positivity that the arithmetic side does have (Connes–Consani). The field's limit-class
picture is now theorem-backed on both sides.

*Novelty verdict:* `[CANDIDATE NEW AS STATED — folklore-adjacent in spirit]`. That finitely
many positivity tests do not force RH is informal folklore; the exact statement with
prescribed uniform displacement t*, exact value matching, and the decaying-class scope was
not found. Recorded with the same honesty discipline as Θ1.

**Count-direction corollary (consilience with the corpus's closed derivation).** The
lane-elimination map (§§32–43) proved: every corpus engine bounds the off-line count from
BELOW; RH needs an upper bound; only zero-density machinery bounds from above. Θ2+Θ4 derive
the asymmetry: one negative evaluation of a detector certifies N_off ≥ 1 (presence is
one-evaluation-robust), while certifying N_off = 0 requires the uniform full-diagonal
inequality (group 3) — and Θ4 shows no finite evaluation family can substitute for it. The
corpus's count-direction law is the Morse-theoretic asymmetry of a degenerate minimum.

## Lean formalization status (2026-08-09)

Module: `formal/GaloisForLFunctions/RHTower/CriticalLocusQuadrupleEvenness.lean` — wired into
the `GaloisForLFunctions.RHTower` umbrella; umbrella build green (18119 jobs); axiom audit
of every theorem exactly `[propext, Classical.choice, Quot.sound]`; formal lint gate clean
for this module. Contents, all hypothesis-free:

- `criticalQuadruple_neg` — Θ1's multiset evenness: the splitting quadruple is invariant
  under t ↦ −t.
- `apply_criticalQuadruple_neg` — Θ1 in full generality: EVERY function of the
  configuration (arbitrary value sort, no regularity) is even in the displacement.
- `deriv_criticalQuadrupleSum_zero` — the universal criticality law: the derivative of the
  scalar quadruple functional vanishes at the critical locus for EVERY F : ℂ → ℂ, with no
  differentiability assumption (junk-value calculus makes the statement unconditional).
- `hasDerivAt_criticalQuadrupleSum_XiC`, `deriv_criticalQuadrupleSum_XiC` — the exact
  first-derivative formula at the corpus's entire XiC.
- `iteratedDeriv_two_criticalQuadrupleSum_XiC` — Θ2's second-jet identity at XiC: the
  second central jet equals 2·(XiC″(1/2+γi) + XiC″(1/2−γi)) — the "first surviving
  information" law, formalized.

Module: `formal/GaloisForLFunctions/RHTower/CrystallineShadowTransversality.lean` — wired into
the `GaloisForLFunctions.RHTower` umbrella, axiom audit exactly
`[propext, Classical.choice, Quot.sound]`:

- `shadowDensity` — the finite multi-splitting shadow density
  `ρ(x) = 4 ∑_j cos(γ_j x)(cosh(t_j x) − 1)`, with `shadowDensity_zero`;
- `shadowDensity_pos_of_ne_zero`, `shadowDensity_ne_zero_fun` — **Θ3.2**: when every displacement
  is genuine the density is somewhere strictly positive, hence not identically zero, hence the
  shadow has a nonzero absolutely continuous part and cannot be atomic;
- `quadrupleExp_eq`, `quadrupleExp_sub_undisplaced` — **Θ3.1's kernel identity**: the four
  splitting exponentials of one displaced conjugate pair sum to `4 cos(γx) cosh(tx)`, and
  subtracting the undisplaced value leaves exactly `4 cos(γx)(cosh(tx) − 1)`.  This is the whole
  algebraic content of Θ3.1; passing to `⟨Δν, h⟩` is then linearity of the integral against `h`.

The certificate is local, not spectral: at any `x` with every `γ_j x` inside the first quarter
period all the cosines are positive while every `cosh(t_j x) − 1` is strictly positive, so the sum
is.  The exponential-independence route of the paper proof is therefore not needed at all, and
`HurwitzExp.expLin_linearIndependent` is not consumed.

Certified 2026-08-13 in `RHTower/CriticalLocusHessianClassification.lean` (wired into
`GaloisForLFunctions.RHTower`, axiom prints exactly `[propext, Classical.choice, Quot.sound]`):

- Θ2(i) exact separation — `multiQuadruple_map_sum`, `multiQuadruple_relative_separation`
  (multiset-join additivity; cross-terms identically zero), with the relative functional
  `relativeQuadrupleValue` and its evenness;
- Θ2(ii) the weight, in general form — `iteratedDeriv_two_criticalQuadrupleSum`
  (`= 2(F″(1/2+iγ) + F″(1/2−iγ))` for `F` analytic at the two conjugate points) and the real
  weight `iteratedDeriv_two_criticalQuadrupleSum_re` (`= 4 Re F″(1/2+iγ)`), via a new
  conjugation bridge (`hasDerivAt_conj_of_eventually_conj`, `analyticAt_conj_point`,
  `iteratedDeriv_two_conj_eq`) proved from the slope characterization;
- Θ2(iii) per-zero necessity — `re_iteratedDeriv_two_nonpos_of_detector` and
  `weight_nonpos_of_detector`: the detector property on one real splitting parameter forces
  `Re F″(1/2+iγ) ≤ 0`, by real restriction plus the corpus's second-derivative test at a
  local maximum;
- Θ2(iv) mixture/determination — `iteratedDeriv_two_multiSplitting` (the diagonal Hessian
  `∑_j t_j² w_j` on scaled strata) and `secondOrder_jets_eq_iff_weights_eq` (second-order
  equivalence at every real ordinate ⟺ equal real weight functions);
- Θ2(v) composite criteria — `deriv_deriv_comp_of_first_derivs_zero` (the stratum second
  derivative of a smooth composite is `∑ ∂ᵢg·φᵢ″(0)`: the finite-rank chain-rule correction
  dies on strata) and `composite_detector_necessity`;
- Θ3.1 integral packaging — `lineTestTransform` (the explicit-formula kernel
  `F_h(ρ) = ∫ h(x)e^{(ρ−1/2)x} dx` as a Lean integral), with
  `relativeQuadrupleValue_lineTestTransform` (`⟨Δν, h⟩ = ∫ h·4cos(γx)(cosh(tx)−1)`),
  its real form, and `multiSplitting_shadow_integral` pairing the total shadow with
  `shadowDensity` — Θ3.1 and Θ3.2 now meet in one certified object.

Additionally certified in `RHTower/CriticalLocusConeFullness.lean`: the symmetry collapse of
pair/quadruple raw sums (`pair_sum_eq_two_re`, `quad_sum_eq_four_re`) and
`criticalLocus_move_cone_fullness` — Step A of the repaired Θ4 (every nonzero direction sees
a strictly negative configuration move; proof by strip Phragmén–Lindelöf, the harmonic
minimum principle, and line independence).

Still not formalized (recorded honestly): Θ4's final exact-hitting assembly (open research —
see the 2026-08-13 log entries), and the other stage-2 cards (ULF-MECH-3/4 are assemblies
over large existing layers; ULF-MECH-5's gate needs in-Lean zero enclosures, i.e.
computation, excluded by the session's Lean rules).

- 2026-08-12 — Θ3.2 certified in Lean by a local positivity certificate, which replaces the
  paper proof's exponential-independence argument entirely.- 2026-08-12 — Θ3.1's kernel identity certified; only its integral packaging remains.

## Θ4 hostile re-audit (2026-08-13) — two gaps in the recorded proof, and the repaired route

Formalization-grade reading found the recorded Θ4 proof incomplete at two points:

1. **Step 1 (placement drift).** The Taylor bound `|η_i| ≤ C t*² δ` needs `|Re F_i''|` small on
   the whole displacement segment `1/2 + [−t*, t*] + iγ`, but the class 𝒜 assumes decay of
   `F''(1/2+iτ)` on the line only.  On-line decay does not bound off-line values: the bound as
   written is unjustified.  Repair: strengthen the class to strip-uniform vanishing
   (`F(σ+iτ) → 0` as `|τ| → ∞`, uniformly on `|σ−1/2| ≤ θ` for some `θ > t*`).  Every corpus
   producer (Weil tests with `C_c^∞`/Schwartz data, Li kernels, Báez-Duarte kernels) satisfies
   the strengthened condition, so the corollary's scope is unchanged.
2. **Step 2 (Jacobian propagation).** The claim "if every k×k determinant vanished for all
   choices of (γ_m) [from supp Z₀], the derivatives would be linearly dependent functions —
   analyticity propagates" is false as written: supp Z₀ is discrete, a relation on a discrete
   infinite set does not propagate by analyticity (sin vanishes on πℤ).  Adversarial pairs
   (F_i, Z₀) with line-derivative degeneracy exactly on supp Z₀ defeat the recorded correction
   scheme at every order of the na�ve repair.

**Repaired proof (to be formalized).**  Work with the full move family: inserted line pairs at
free ordinates β (value `2u_i(β)`, `u_i := Re F_i` on the line), deleted support pairs at
`α ∈ supp Z₀` (value `−2u_i(α)`), and quadruples at `(γ, t*)` (value `4·Re F_i(1/2+t*+iγ)` by the
σκ symmetries).  Steps:

- *Cone fullness.*  If every move had nonnegative `w`-component for some `w ≠ 0`, then
  `u_w := Σ w_i u_i ≥ 0` on the line, `u_w = 0` on the infinite support (insertions force `≥ 0`,
  deletions force `≤ 0` there), and `U_w := Re Σ w_i F_i ≥ 0` on the two boundary lines
  `Re s = 1/2 ± t*` (quadruple moves).  Strip decay + the rectangle maximum principle give
  `U_w ≥ 0` on the open substrip; a support point is then an interior zero of a nonnegative
  harmonic function, so `U_w ≡ 0` (minimum principle), hence `Σ w_i F_i` constant, contradicting
  independence mod constants.  So the closed convex cone of move values is all of ℝ^k.
- *Exact hitting.*  Approximate the needed correction by a positive rational combination of
  finitely many moves (bipolar/cone duality + Carathéodory, bounded rounding error since all
  move values are bounded); absorb the bounded error by N replicated IFT blocks of k inserted
  pairs at a fixed evaluation tuple with invertible Jacobian (existence from the corpus
  evaluation-minor lemma `exists_injective_evaluation_minor_of_linearIndependent` applied to the
  line derivatives `u_i'`, legitimate because the tuple ranges over ℝ, not over supp Z₀); image
  balls of the blocks add (`B(b,r) + B(b',r') = B(b+b', r+r')`), so N·r eventually covers the
  error and the values are matched exactly.

The theorem statement survives with 𝒜 replaced by the strip-vanishing class 𝒜̂ (and linear
independence mod constants of the line restrictions as the stated nondegeneracy, with the
dependent case reduced by count-balanced expansion).  The corollary (no finite truncation of the
Weil criterion) is unchanged.  Lean modules planned: `RHTower.CriticalLocusHessianClassification`
(Θ2(i)–(v), Θ3.1 packaging — in progress), `RHTower.CriticalLocusConeFullness` (harmonic step),
`RHTower.CriticalLocusEvaluationBlindness` (assembly).

- 2026-08-13 (Θ4 endgame audit, continued) — the repaired route's final assembly has one
  genuinely open point: exact hitting when the deletion moves are essential cone directions.
  Deletions are bounded by the multiplicities of Z₀, and an adversarial Z₀ (sparse support,
  multiplicity one, fast-decaying test values, collinear support evaluations) bounds the total
  deletion capacity while positive-type test families (e.g. `1/cos²(A(s−1/2))`-type, positive on
  the line and on the `±t*` lines for `t* < θ/2`) make insertions and quadruples one-sided, so
  the integer-move semigroup is not syndetic and the IFT-patch bases race against their radii at
  every small scale (analytic curves: base ~ s^{p₁}, radius ~ s^{p_k}).  One-dimensional cases
  close by IVT with a single deletion; the general case needs a new mechanism (research item —
  attack with the conjecture-attack toolkit; candidate levers: two-parameter extra-quadruple
  family V(γ,t′) with its t′-jets = weight vectors, far-field direction spread, and the exact
  interplay between deletion capacity and the direction cone).  Until closed, Θ4's Lean surface
  is: Module B (cone fullness — provable as designed) plus the assembly under the honest
  additional hypotheses that the final research settles.  Θ1–Θ3 certification is unaffected.
