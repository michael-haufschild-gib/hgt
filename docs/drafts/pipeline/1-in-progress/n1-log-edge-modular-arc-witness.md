# (N1) holds at the logarithmic edge: exact positive blind multipliers from the modular bottom arc

- **ID:** n1-log-edge-modular-arc-witness
- **Stage:** 1-in-progress (Theorem A fully formalized; open core C191 keeps the card in progress)
- **Type:** THEOREM (paper, complete) + CONJECTURE (decay class)
- **Source:** producer-loop-opus-2026-10-12 rows 190–191; HF route (N1) = `XiDivisibleBlindTest`;
  line model of card `n1-voronoi-maass-interpolation` (row 1015).

## Statement
Let `A = {e^{iα} : π/3 ≤ α ≤ 2π/3}` be the bottom arc of the standard fundamental domain of `SL₂(ℤ)`. Write
`W_n(z) = √y K₀(2π|n|y) e^{2πinu}` (`z = u + iy`) and `φ_z(x) = (y/|x − z|²)^{1/2}`.

**Theorem A (log-edge witness).** There is a probability measure `μ` on `A`, invariant under `z ↦ −z̄`
(on `A` this is `S: z ↦ −1/z`), with `∫_A W_n dμ = 0` for every `n ≠ 0`. The function
`h(x) = ∫_A φ_z(x) dμ(z)` then has the following properties:
1. `h` is even and `S`-invariant: `h(x) = |x|^{−1} h(1/x)`.
2. `B(v) = e^{v/2} h(e^v)` is strictly positive definite: `B̂(t) > 0` for every real `t`.
3. `ĥ(n) = 2∫ W_{−n} dμ = 0` for every integer `n ≠ 0`, so the periodization of `h` is constant.
4. `h(x) = c/|x| + O(|x|^{−2})` with `c = ∫√y dμ > 0`.

In multiplier language, `R(½+it) := B̂(t)/|G(½+it)|²` with `G = s(s−1)Γ_ℝ(s)/2` has these properties:
- `R(½+it) > 0` and `R` is even;
- `R` is analytic on `|Im t| < ½ + δ` except for double poles at `t = ±i/2` (that is, at `s = 0, 1`);
- `R = O(e^{(π/6)|t|})` up to powers;
- the ζ-free kernel `Ψ_R = 𝓜^{−1}[G²R]` vanishes at every integer `n ≥ 1`.

So `Ξ²R` is a nonnegative Ξ-divisible symbol whose ζ-free kernel is blind at every `n ≥ 1`. Its defect is the
class: the double pole at `s = 1`, i.e. a tail `e^{−|x|/2}`.

**Correction (row 200).** Because of that pole, the ζ-free blindness does *not* give A-blindness. Shifting
`a(x) = (1/2πi)∫_{(½)} ξ²R x^{−s} ds` to `Re s > 1` crosses the double pole of `R` at `s = 1`. So the
autocorrelation of `Ξ²R` at `log n` is the residue `(ρ₂ log n − ρ₁)/√n`, with `ρ₂ ∝ c > 0`, not `0`. The two
notions agree only in the decay class (`logNode_blind_iff_certKernel_vanishes`).

The pole is also forced: a nonnegative decay-class `R` with `Ψ_R(n) = 0` for all `n ≥ 1` has
`∫Ξ²R ∝ Ψ_R(1) = 0` (`integral_xi_sq_eq_certKernel_one`), hence `R = 0`. So full ζ-free blindness holds exactly
at the log edge.

## Proof (dependency-closed)
**Step 1 (no nonnegative decaying ¼-combination on `A`).** Let `P = Σ_{0<|n|≤N} c_n W_n` be real and
`P ≥ 0` on `A`. Then `P ≡ 0`.
- `ΔP = −¼P` for the hyperbolic Laplacian `Δ = y²(∂_u² + ∂_y²)`. With `v = P/√y` this becomes
  `L v := y(v_uu + v_yy) + v_y = 0`; checked mode by mode from `K₀'' + K₀'/x − K₀ = 0`.
- Let `Ω_Y` be the part of the cylinder `ℝ/ℤ × (0,∞)` between `A` and `y = Y`. `L` has the strict
  subsolution `w = e^{y}`, since `Lw = (y + 1)e^y > 0`. At an interior minimum of a `C²` function `f`,
  `Lf ≥ 0`. Hence `f = v − εw` (with `Lf < 0`) has its minimum on `∂Ω_Y = A ∪ {y = Y}`.
- `v ≥ 0` on `A` and `|v| ≤ η_Y → 0` on `y = Y` (`K₀` decays). Letting `ε → 0` and then `Y → ∞` gives
  `v ≥ 0` above `A`.
- On the horocycle `y = 2`, which lies above `A`, `∫_0^1 v(u + 2i) du = 0` because there is no zero mode. So
  `v ≡ 0` there, every `c_n K₀(4π|n|) = 0`, hence `c_n = 0`.

**Step 2 (Farkas + compactness).** Apply finite-dimensional separation to the real functions
`Re W_n, Im W_n` (`1 ≤ n ≤ N`) on the compact set `A`. By Step 1 no real combination is `> 0` on `A`, so
`0` lies in the convex hull of `{(W_n(a))_{n≤N} : a ∈ A}`. This gives a probability `μ_N` on `A` with
`∫W_n dμ_N = 0` for `1 ≤ |n| ≤ N`. A weak-* limit point `μ` annihilates every `W_n` with `n ≠ 0`.
Symmetrize under `R: z ↦ −z̄`: since `W_n ∘ R = W_{−n}`, the result is still annihilating, and on `A`,
`R = S`.

**Step 3 (Fourier coefficients).** `∫_ℝ (x² + y²)^{−1/2} e^{−2πiξx} dx = 2K₀(2π|ξ|y)`. Hence
`φ̂_z(ξ) = 2√y K₀(2π|ξ|y) e^{−2πiξu}` and `ĥ(n) = 2∫W_{−n} dμ = 0`.

**Step 4 (S-invariance).** `φ_{Sz}(x) = (Im z/|xz + 1|²)^{1/2} = |x|^{−1} φ_z(−1/x)`. Together with evenness
this gives `h(x) = |x|^{−1} h(1/x)`.

**Step 5 (positive definiteness, Mehler–Dirichlet).** For `z = e^{iα}`,
`e^{v/2} φ_z(e^v) = (sin α/2)^{1/2} (cosh v − cos α)^{−1/2}`, and for `θ ∈ [0, π)`:
- `(cosh v + cos θ)^{−1/2} = (2/π) ∫_0^θ k_φ(v) (cos φ − cos θ)^{−1/2} dφ`, where
  `k_φ(v) = cosh(v/2) cos(φ/2)/(cosh v + cos φ)`. Proof: substitute `c = cos φ` and use
  `∫_a^1 dc/((X+c)√((c−a)(1−c))) = π/√((X+a)(X+1))`.
- `cos(φ/2) k_φ(v) = ½ Re sech((v + iφ)/2)`, so `k̂_φ(t) = π cosh(tφ)/(cos(φ/2) cosh(πt)) > 0`.
- Hence `B̂(t) = ∫ (sin α/2)^{1/2} FT[(cosh v − cos α)^{−1/2}](t) dμ > 0`.

**Step 6 (multiplier form).** `B̂` is meromorphic on `|Im t| < π/3` with simple poles at `±i/2`, from
`1/cosh πt`; the residue is `∝ ∫√(sin α) dμ`. `G(s)G(1−s)` has simple zeros at `s = 0, 1`. Hence `R` has
double poles there. The integer kernel is `Ψ_R(n) ∝ n^{−1/2} ĥ(n) = 0` (line-model dictionary,
card `n1-voronoi-maass-interpolation`, derivation steps 1–3). The decay comes from `Π_α(t) ≍ e^{−t·min(α, π−α)}`
with `α ∈ [π/3, 2π/3]`.

## Consequences
- **No absolutely convergent Farkas certificate.** If `Σ|c_n| n^{−1/2} < ∞` and `Re(e^{2iθ}D(½+it)) ≥ 0`
  with `D = Σ_{n≥2} c_n n^{−s}`, then `∫ B̂ Re(e^{2iθ}D) dt = Σ c_n Ψ_R(n) = 0` and `B̂ > 0`, so the real part
  vanishes a.e. Every obstruction to decay-class (N1) must therefore pass through the pole at `s = 1`, as the
  corpus certificates `Z² Re Q` do via their residue terms (rows 1022, 1027, 1030).
- **The decay class is a codimension-2 slice.** Decay-class (N1) means the blind PD cone meets
  `{ℓ₁ = ℓ₂ = 0}`, where `ℓ₁` is the double-pole coefficient (`∝ ∫√y dμ`, the `1/|x|` tail) and `ℓ₂` the
  simple-pole coefficient (`∝ ∫√y log y dμ`, i.e. `Ψ(0)`). Positive measures always have `ℓ₁ > 0`, so the
  witness must be built from a signed representation.
- **Bottom-arc rigidity (paper, Green's identity).** Blind measures on `A` are fluxes `∂_n g` of
  threshold solutions vanishing on `A`. The even sector is spanned by `ν₀` (zero mode `√y(a₀ + log y)`) and
  `ν₁` (growing mode `√y I₀(2πy) cos 2πu`). The two decay conditions cut this 2-dimensional space to `{0}`
  unless `a₁ = a₀ b₁`. So decay-class witnesses must leave the unit circle, where positive definiteness is no
  longer automatic.
- **Torsion.** The Dirichlet problem on `A` cannot be solved automorphically: `S`-odd plus `T`-even is
  impossible since `(ST)³ = 1` (corpus no-relations lemma). The witness is genuinely non-automorphic.
- **Angle π/6.** The `R` growth exponent `π/2 − π/3 = π/6` is the critical angle found in the rotated-`K₀`
  harmonic-measure model (row 190). The corners `ρ, ρ²` of the fundamental domain carry it.

## Conjecture C191 (pole removal)
Decay-class (N1) holds iff some signed `S`-invariant measure `m` on `ℍ` exists with:
- `π_*m` annihilating all `W_n`, `|n| ≥ 2`;
- `∫√y dm = ∫√y log y dm = 0`;
- `∫ Q_t dm ≥ 0` for `Q_t(z) = ⟨φ_z, |x|^{−1/2+it}⟩`.

`[OPEN CORE]`: whether the blind PD cone contains elements with `ℓ₁ ≤ 0`.

## Lean programme
- [x] L1 Step 1 [L]: `HTGeometry/ModularArcMinimumPrinciple.nonneg_of_nonneg_on_modularArc` and
  `RHTower/ModularArcWhittakerPositivity.whittakerArc_coeff_eq_zero` (corpus `BesselKZero.kMoment`).
- [x] L2 Step 2 [L]: `RHTower/ModularArcAnnihilatingMeasure.exists_probabilityMeasure_arc_annihilating`
  (Hahn–Banach `geometric_hahn_banach_point_closed` + Prokhorov compactness of `ProbabilityMeasure I`).
- [x] L3 [L]: `HTGeometry/SymmetricCoshKernelPositiveDefinite.integral_cos_mul_symCoshKernel_pos`
  (proof by even binomial series with `C(−½,2j) > 0` and the corpus Fourier transform of `cosh^{−s}`; no Mehler–Dirichlet needed).
- [x] L4 [L]: `RHTower/PoissonVectorFourierWhittaker.integral_mul_rpow_sin_eq_kMoment`
  (`∫x(x²+y²)^{−3/2} sin(kx) dx = 2kK₀(ky)`, the derivative form of Basset).
- [x] L6 [L]: `RHTower/ModularArcLineModelBlind.exists_arcLineWitness`, the line-model form. `h'` is integrable with zero
  Fourier coefficients at every `2π(n+1)`; `h` is even; `h(1/x) = |x|h(x)`; `e^{v/2}h(e^v)` is strictly PD.
- [x] L5 [L]: `RHTower/ModularArcLogEdgeWitness.exists_arcWitness`. It gives a nonzero finite `ν` on the arc that is
  `u ↦ −u` symmetric, annihilates every `√y K₀(2π(n+1)y)·{cos,sin}(2π(n+1)u)`, and has strictly positive
  definite log-scale Poisson profile.

## Log
- 2026-10-13 — created (rows 190–191). Paper proof complete for Theorem A.
- 2026-10-13 — rows 192–193: L1, L2 formalized; standard axioms; lake --old audits clean; wired.
- 2026-10-13 — row 194: L3, L5 formalized. Theorem A is in Lean modulo the classical Basset dictionary (L4).
- 2026-10-13 — row 195: L4 and L6 formalized. Theorem A is complete in Lean in line-model form.

## Theorem B (paper, row 196): finite-level decay witnesses
For every `N` there is a nonzero decay-class (analytic in the strip, `R > 0` on ℝ), strictly positive-definite,
self-dual multiplier whose chirp moments `∫B̂(t)cos(2θ(t) − t log n)dt` vanish for `2 ≤ n ≤ N`.
- Proof:
  - (i) The decay cone is uniformly dense in positive spectra on ℝ, via the multipliers
    `f_K = 1 − (1+K(t²+¼))e^{−K(t²+¼)}`.
  - (ii) Theorem A gives a positive spectrum annihilating every chirp, so no nonzero chirp polynomial is `≥ 0`.
  - (iii) Hence the finite moment cone has dual `{0}` and equals the whole space.
- The full (N1) is the `N → ∞` limit. The condition `B̂(±i/2) = 0` is analytic and is not stable under real-line weak
  limits, so the open core is uniform separation of the witnesses from the log edge.

## Theorem B′ (row 201): finite-level decay witnesses, fully in Lean
`RHTower/FiniteLevelDecayWitness.exists_decayClass_lineWitness`: for every `N` there is `h` with:
- `h` is `C¹`, with `h, h' ∈ L¹`;
- `h` is even, with `h(1/x) = |x|h(x)`;
- `∫h = 0` and `|e^{v/2}h(e^v)| ≤ Ce^{−3|v|/2}` (decay class);
- `∫h'(x) sin(2πmx) dx = 0` for `2 ≤ m ≤ N+1`;
- `e^{v/2}h(e^v)` is strictly positive definite.

Standard axioms; `lake --old` clean; wired.

Generators are pole-filtered arc pairs `h_{K,u} = ψ_u − ∫ǧ_K(w)e^{−w/2}ψ_u(xe^{−w})dw`, with
`ǧ_K = 2e^{−K/4}g_K − e^{−K/2}g_{2K}` and spectrum `(1 − e^{−K(τ²+¼)})² Q̂_u`. The dual step is L1 alone, through
density of the Whittaker cone and a signed-basis perturbation at one large `K`. Modules:
- `GaussianPoleFilter`
- `FilteredArcGenerator`: strict positive definiteness, symmetries.
- `FilteredArcGeneratorDecay`: rate `3/2`, `∫h = 0` via `λ → ½`, `h' ∈ L¹`.
- `FilteredArcGeneratorMoments`: `√r K₀(r) ≤ √(π/2)`, uniform error `4√(π/2)√c (2e^{−K/4}+e^{−K/2})`.
- `FiniteLevelDecayWitness`

The open core (C191) is the `N → ∞` limit. The filter's moment error at `n` is log-normal in `n`, while the arc
Whittaker moments decay like `e^{−π√3 n}`.

## C208 (row 202): finite-point dichotomy, fully in Lean
- `FinitePoissonDecayWitness.exists_finitePoisson_decayWitness`: every finite level is achieved by finitely many
  Poisson points, using two-atom pole filters with weights δ−2c+c⋆c on dilations 0, ±b, ±2b.
- `FinitePoissonBlindRigidity.eq_zero_of_finitePoisson_blind`: no finite superposition is blind at all large integers.
  The proof is lowest-height domination plus the discrete exponential-sum lemma.
- Consequence: exact decay witnesses must be infinite Poisson superpositions.
- Compactness reduction: C191 ⟸ GL1 for a fixed compact family of pole filters. GL1 is open for continuous-radius
  families; for lattice families certificates likely exist.
