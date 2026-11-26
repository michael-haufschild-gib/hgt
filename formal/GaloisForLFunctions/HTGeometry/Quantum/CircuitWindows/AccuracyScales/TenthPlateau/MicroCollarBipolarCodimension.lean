import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.SaddleTurnMultiplicity
import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualTube

/-! # Micro-collar bipolar switching codimension and rotating-direction anti-concentration at 1/10

This module analyzes simultaneous opposite-sign active saddles inside the `2^{-Θ(N²)}` micro-collar
at `e = 1 / 10` along `1`D lines and multi-parameter Gaussian subspaces, keeping every spectral,
norm, and measure-theoretic operator parameterized over abstract index types `{ι : Type*}` and
explicit eigenframes `(V : UGroup N) (E : Config N → ℝ)`:

1. **`1`D bipolar-free collar excursion packing dichotomy:**
   - `lipschitz_collar_bipolarFree_diam_or_sep`: on any convex domain `I ⊆ ℝ`, if `g` is
     `L`-Lipschitz on `I` (`0 < L`) and locally sign-coherent inside the padded collar
     `Ioo (e₀ - η_pad) (e₀ + δ + η_pad)` (`c > 0`, `η_pad > 0`), then **every** pair of visits
     `t₁, t₂ ∈ I` to `[e₀, e₀ + δ]` satisfies the dichotomy
     `|t₂ - t₁| ≤ δ / c ∨ 2 * η_pad / L ≤ |t₂ - t₁|`.
   - `gaussian_bipolarFree_collar_anticoncentration`: partitioning `[-R, R]` into
     `⌊L * R / η_pad⌋₊ + 1` subintervals of width `< 2 * η_pad / L` bounds the product-Gaussian
     slice mass of `{x ∈ Ω | F x ∈ (e₀, e₀ + δ]}` by
     `γ(|t| > R) + (⌊L * R / η_pad⌋₊ + 1) * δ / (√(2 π) * c)` even when global `1`D lines undergo
     `2^(N - 1)` avoided crossings outside the micro-collar.
2. **`2`D determinant coercivity, `SO(ι)`-rotating-direction Gaussian charts, and tie avoidance:**
   - `twoDim_shared_coercive_unit_of_det`: exact characterization of antiparallel `2`D slope pairs
     together with the quantitative bisector lower bound
     `|det(ξ₁, ξ₂)| / (2 * ‖ξ_{3 - i}‖₂) ≤ ⟨ξ_i, ŵ⟩` for nonzero `ξ₁, ξ₂ ∈ ℝ²`.
   - `gaussian_rotatingDirection_chart_anticoncentration` and
     `fixed_tenth_locking_of_rotatingDirection_charts`: Householder reflections on
     `EuclideanSpace ℝ ι` preserve `Measure.pi (fun _ : ι => gaussianReal 0 1)` via
     `stdGaussian_eq_withDensity`, converting `J` convex charts with chart-dependent coercive unit
     directions `w_r` into Gaussian anti-concentration `≤ J * δ / (√(2 π) * c)` and fixed-`1 / 10`
     zero-drop locking `m_{1/10 + δ} = m_{1/10}`.
   - `generic_parallel_lines_avoid_collar_ties`: transverse `i₂`-variation across a finite family
     `P_idx` of branch pairs confines intra-collar ties to Gaussian measure
     `≤ P_idx.card * (δ + 2 * η_pad) / (√(2 π) * c₂)`.
3. **Exact Kato off-diagonal sensitivity, antiparallel rigidity, and `2`-local blind spots:**
   - `spectralProjective_diffProjector_diag_zero` and `exists_basisKatoGenerator_eq_diffProjector`:
     for every `(V : UGroup N)` and injective `E : Config N → ℝ`, the rank-`2` difference projector
     `Δρ(U_θ, ψ) = |U_θ ψ⟩⟨U_θ ψ| - |ψ⟩⟨ψ|` has identically zero `V`-diagonal and is realized
     **exactly** by `basisKatoGenerator V E P_⋆` for `P_⋆ = i [Δρ(U_θ, ψ), V diag(E) V*]`, attaining
     Kato slope `2 * (1 - ‖⟨ψ, U_θ ψ⟩‖²)`.
   - `kato_bipolar_antiparallel_iff_diffProjector`, `no_bipolar_antiparallel_same_state`, and
     `multiSaddle_kato_coercive_ball`: two saddles have antiparallel Kato gradients across
     `selfAdjoint (Register N)` iff `Δρ₁ + λ • Δρ₂ = 0` (impossible when `ψ₁ = ψ₂` and
     `‖⟨ψ, U₁ ψ⟩‖ < 1`), while any shared coercive direction remains `≥ c₀ / 2`-coercive on a ball
     of radius `c₀ * Δ² / (4 * 2^N * ‖P‖²)`.
   - `chainPauli_kato_blindSpot_hammingThree`: for `n ≥ 1` (`N = n + 2 ≥ 3`), an explicit
     Hamming-distance-`3` cat-state saddle mode with `⟨ψ_cat, U_θ ψ_cat⟩ = 0` has identically zero
     first-order Kato slope across all `12 N - 9` local chain Pauli couplings simultaneously. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ
private abbrev StateSpace (N : ℕ) := EuclideanSpace ℂ (Config N)

/-! ## Section 1: Abstract `1`D bipolar-free collar excursion packing dichotomy -/

private theorem gaussianReal_le_inv_sqrt_two_pi_vol (S : Set ℝ) :
    (gaussianReal 0 1) S ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume S := by
  rw [gaussianReal_apply 0 (by norm_num) S, ← setLIntegral_const]
  refine setLIntegral_mono_ae (by fun_prop) ?_
  filter_upwards with t _
  rw [gaussianPDF]
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))

/-- Bipolar-free collar excursion dichotomy on a convex `1`D domain `I ⊆ ℝ`: if `g` is
`L`-Lipschitz on `I` (`0 < L`) and around every `t ∈ I` with
`g t ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)` there is an open neighborhood on which either `+g` or
`-g` has right Dini slope `≥ c > 0`, then any two visits `t₁, t₂ ∈ I` to `[e₀, e₀ + δ]` satisfy
`|t₂ - t₁| ≤ δ / c ∨ 2 * η_pad / L ≤ |t₂ - t₁|`. -/
theorem lipschitz_collar_bipolarFree_diam_or_sep {I : Set ℝ} (hI : Convex ℝ I)
    {g : ℝ → ℝ} {L : ℝ≥0} (hL_pos : 0 < (L : ℝ)) (hg_lip : LipschitzOnWith L g I)
    {c e₀ δ η_pad : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (_hη_pad : 0 < η_pad)
    (hloc : ∀ t ∈ I, g t ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad) →
      ∃ r > 0, ∃ sgn : Bool,
        ∀ s ∈ Ioo (t - r) (t + r) ∩ I, ∀ b ∈ Ioo (t - r) (t + r) ∩ I, s < b →
          ∀ ε > 0, ∃ h ∈ Ioc (0 : ℝ) (b - s),
            (c - ε) * h ≤ (if sgn then 1 else -1) * (g (s + h) - g s))
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ I) (ht₂ : t₂ ∈ I)
    (hg₁ : g t₁ ∈ Icc e₀ (e₀ + δ)) (hg₂ : g t₂ ∈ Icc e₀ (e₀ + δ)) :
    |t₂ - t₁| ≤ δ / c ∨ 2 * η_pad / (L : ℝ) ≤ |t₂ - t₁| := by
  have hg_cont : ContinuousOn g I := hg_lip.continuousOn
  have hord : ∀ {a b : ℝ}, a ∈ I → b ∈ I → a ≤ b →
      g a ∈ Icc e₀ (e₀ + δ) → g b ∈ Icc e₀ (e₀ + δ) →
      b - a ≤ δ / c ∨ 2 * η_pad / (L : ℝ) ≤ b - a := by
    intro a b ha hb hab hga hgb
    rcases eq_or_lt_of_le hab with rfl | hlt
    · left; rw [sub_self]; exact div_nonneg hδ hc.le
    have hsub_I : Icc a b ⊆ I := hI.ordConnected.out ha hb
    by_cases hstay : ∀ s ∈ Icc a b, g s ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)
    · left
      let U : Bool → Set ℝ := fun sgn =>
        {x : ℝ | ∃ r > 0,
          ∀ s ∈ Ioo (x - r) (x + r) ∩ I, ∀ y ∈ Ioo (x - r) (x + r) ∩ I, s < y →
            ∀ ε > 0, ∃ h ∈ Ioc (0 : ℝ) (y - s),
              (c - ε) * h ≤ (if sgn then 1 else -1) * (g (s + h) - g s)}
      have hopen (sgn : Bool) : IsOpen (U sgn) := by
        rw [Metric.isOpen_iff]
        rintro x ⟨r, hr, hxr⟩
        refine ⟨r / 2, half_pos hr, fun y hy => ⟨r / 2, half_pos hr, fun s hs z hz hsz ε hε => ?_⟩⟩
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hy_abs := abs_lt.mp hy
        have hsub_ball : Ioo (y - r / 2) (y + r / 2) ⊆ Ioo (x - r) (x + r) := fun u hu =>
          ⟨by linarith only [hu.1, hy_abs.1], by linarith only [hu.2, hy_abs.2]⟩
        exact hxr s ⟨hsub_ball hs.1, hs.2⟩ z ⟨hsub_ball hz.1, hz.2⟩ hsz ε hε
      have hcov : Icc a b ⊆ U true ∪ U false := by
        intro t ht
        obtain ⟨r, hr, sgn, hsgn⟩ := hloc t (hsub_I ht) (hstay t ht)
        cases sgn
        · exact Or.inr ⟨r, hr, hsgn⟩
        · exact Or.inl ⟨r, hr, hsgn⟩
      have hdisj : ¬ (Icc a b ∩ (U true ∩ U false)).Nonempty := by
        rintro ⟨x, hxIcc, ⟨r₁, hr₁, hx₁⟩, ⟨r₂, hr₂, hx₂⟩⟩
        let r := min r₁ r₂
        have hr_pos : 0 < r := lt_min hr₁ hr₂
        let u₁ := max a (x - r / 2)
        let u₂ := min b (x + r / 2)
        have hu₁_lt_u₂ : u₁ < u₂ := by
          dsimp only [u₁, u₂]
          exact max_lt (lt_min hlt (by linarith only [hxIcc.1, hr_pos]))
            (lt_min (by linarith only [hxIcc.2, hr_pos]) (by linarith only [hr_pos]))
        have hu_sub_ab : Icc u₁ u₂ ⊆ Icc a b := fun s hs =>
          ⟨(le_max_left _ _).trans hs.1, hs.2.trans (min_le_left _ _)⟩
        have hu_sub_r₁ : Icc u₁ u₂ ⊆ Ioo (x - r₁) (x + r₁) := fun s hs => by
          have hr_le : r ≤ r₁ := min_le_left _ _
          have hlo : x - r / 2 ≤ s := (le_max_right _ _).trans hs.1
          have hhi : s ≤ x + r / 2 := hs.2.trans (min_le_right _ _)
          exact ⟨by linarith only [hlo, hr_pos, hr_le], by linarith only [hhi, hr_pos, hr_le]⟩
        have hu_sub_r₂ : Icc u₁ u₂ ⊆ Ioo (x - r₂) (x + r₂) := fun s hs => by
          have hr_le : r ≤ r₂ := min_le_right _ _
          have hlo : x - r / 2 ≤ s := (le_max_right _ _).trans hs.1
          have hhi : s ≤ x + r / 2 := hs.2.trans (min_le_right _ _)
          exact ⟨by linarith only [hlo, hr_pos, hr_le], by linarith only [hhi, hr_pos, hr_le]⟩
        have hd_pos : c * (u₂ - u₁) ≤ g u₂ - g u₁ :=
          dini_mul_sub_le_sub (g := g) (c := c) hu₁_lt_u₂.le (hg_cont.mono (hu_sub_ab.trans hsub_I))
            fun s hs ε hε => by
              obtain ⟨h, hh_mem, hh_le⟩ := hx₁ s
                ⟨hu_sub_r₁ ⟨hs.1, hs.2.le⟩, hsub_I (hu_sub_ab ⟨hs.1, hs.2.le⟩)⟩
                u₂ ⟨hu_sub_r₁ ⟨hu₁_lt_u₂.le, le_rfl⟩, hsub_I (hu_sub_ab ⟨hu₁_lt_u₂.le, le_rfl⟩)⟩
                hs.2 ε hε
              exact ⟨h, hh_mem, by simpa using hh_le⟩
        have hd_neg : c * (u₂ - u₁) ≤ -g u₂ - -g u₁ :=
          dini_mul_sub_le_sub (g := fun t => -g t) (c := c) hu₁_lt_u₂.le
            (hg_cont.neg.mono (hu_sub_ab.trans hsub_I)) fun s hs ε hε => by
              obtain ⟨h, hh_mem, hh_le⟩ := hx₂ s
                ⟨hu_sub_r₂ ⟨hs.1, hs.2.le⟩, hsub_I (hu_sub_ab ⟨hs.1, hs.2.le⟩)⟩
                u₂ ⟨hu_sub_r₂ ⟨hu₁_lt_u₂.le, le_rfl⟩, hsub_I (hu_sub_ab ⟨hu₁_lt_u₂.le, le_rfl⟩)⟩
                hs.2 ε hε
              simp only [Bool.false_eq_true, ↓reduceIte] at hh_le
              exact ⟨h, hh_mem, by linarith only [hh_le]⟩
        nlinarith only [hc, hu₁_lt_u₂, hd_pos, hd_neg]
      by_cases hneg_ne : (Icc a b ∩ U false).Nonempty
      · have hpos_emp : ¬ (Icc a b ∩ U true).Nonempty := fun hpos_ne =>
          hdisj (isPreconnected_Icc (U true) (U false) (hopen true) (hopen false)
            hcov hpos_ne hneg_ne)
        have hall_neg : ∀ s ∈ Icc a b, s ∈ U false := fun s hs => by
          rcases hcov hs with h1 | h2
          · exact (hpos_emp ⟨s, hs, h1⟩).elim
          · exact h2
        have hd : c * (b - a) ≤ -g b - -g a :=
          dini_mul_sub_le_sub (g := fun t => -g t) (c := c) hlt.le
            (hg_cont.neg.mono hsub_I) fun s hs ε hε => by
              obtain ⟨r, hr, hsr⟩ := hall_neg s ⟨hs.1, hs.2.le⟩
              let y := min b (s + r / 2)
              have hsy : s < y := lt_min hs.2 (by linarith only [hr])
              have hy_ab : y ∈ Icc a b := ⟨hs.1.trans hsy.le, min_le_left _ _⟩
              have hy_ball : y ∈ Ioo (s - r) (s + r) :=
                ⟨by linarith only [hsy, hr], (min_le_right b (s + r / 2)).trans_lt (by linarith only [hr])⟩
              obtain ⟨h, hh_mem, hh_le⟩ := hsr s
                ⟨⟨by linarith only [hr], by linarith only [hr]⟩, hsub_I ⟨hs.1, hs.2.le⟩⟩
                y ⟨hy_ball, hsub_I hy_ab⟩ hsy ε hε
              simp only [Bool.false_eq_true, ↓reduceIte] at hh_le
              exact ⟨h, ⟨hh_mem.1, hh_mem.2.trans (sub_le_sub_right (min_le_left b _) s)⟩,
                by linarith only [hh_le]⟩
        exact (le_div_iff₀ hc).mpr (by rw [mul_comm]; linarith only [hd, hga.2, hgb.1])
      · have hall_pos : ∀ s ∈ Icc a b, s ∈ U true := fun s hs => by
          rcases hcov hs with h1 | h2
          · exact h1
          · exact (hneg_ne ⟨s, hs, h2⟩).elim
        have hd : c * (b - a) ≤ g b - g a :=
          dini_mul_sub_le_sub (g := g) (c := c) hlt.le (hg_cont.mono hsub_I) fun s hs ε hε => by
            obtain ⟨r, hr, hsr⟩ := hall_pos s ⟨hs.1, hs.2.le⟩
            let y := min b (s + r / 2)
            have hsy : s < y := lt_min hs.2 (by linarith only [hr])
            have hy_ab : y ∈ Icc a b := ⟨hs.1.trans hsy.le, min_le_left _ _⟩
            have hy_ball : y ∈ Ioo (s - r) (s + r) :=
              ⟨by linarith only [hsy, hr], (min_le_right b (s + r / 2)).trans_lt (by linarith only [hr])⟩
            obtain ⟨h, hh_mem, hh_le⟩ := hsr s
              ⟨⟨by linarith only [hr], by linarith only [hr]⟩, hsub_I ⟨hs.1, hs.2.le⟩⟩
              y ⟨hy_ball, hsub_I hy_ab⟩ hsy ε hε
            exact ⟨h, ⟨hh_mem.1, hh_mem.2.trans (sub_le_sub_right (min_le_left b _) s)⟩,
              by simpa using hh_le⟩
        exact (le_div_iff₀ hc).mpr (by rw [mul_comm]; linarith only [hd, hga.1, hgb.2])
    · right
      push Not at hstay
      obtain ⟨s, hs_ab, hs_out⟩ := hstay
      have hs_I : s ∈ I := hsub_I hs_ab
      have hgap₁ : η_pad ≤ |g s - g a| := by
        by_cases hlo : e₀ - η_pad < g s
        · have hhi : e₀ + δ + η_pad ≤ g s := by
            by_contra hlt_hi; exact hs_out ⟨hlo, not_le.mp hlt_hi⟩
          exact (by linarith only [hhi, hga.2] : η_pad ≤ g s - g a).trans (le_abs_self _)
        · exact (by linarith only [hlo, hga.1] : η_pad ≤ -(g s - g a)).trans (neg_le_abs _)
      have hgap₂ : η_pad ≤ |g b - g s| := by
        by_cases hlo : e₀ - η_pad < g s
        · have hhi : e₀ + δ + η_pad ≤ g s := by
            by_contra hlt_hi; exact hs_out ⟨hlo, not_le.mp hlt_hi⟩
          exact (by linarith only [hhi, hgb.2] : η_pad ≤ -(g b - g s)).trans (neg_le_abs _)
        · exact (by linarith only [hlo, hgb.1] : η_pad ≤ g b - g s).trans (le_abs_self _)
      have hlip₁ : |g s - g a| ≤ (L : ℝ) * (s - a) := by
        have h := hg_lip.dist_le_mul s hs_I a ha
        rwa [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs_ab.1)] at h
      have hlip₂ : |g b - g s| ≤ (L : ℝ) * (b - s) := by
        have h := hg_lip.dist_le_mul b hb s hs_I
        rwa [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs_ab.2)] at h
      exact (div_le_iff₀ hL_pos).mpr (by linarith only [hgap₁, hgap₂, hlip₁, hlip₂])
  rcases le_total t₁ t₂ with h12 | h21
  · rw [abs_of_nonneg (sub_nonneg.mpr h12)]
    exact hord ht₁ ht₂ h12 hg₁ hg₂
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h21)]
    exact hord ht₂ ht₁ h21 hg₂ hg₁

/-- Product-Gaussian anti-concentration along `1`D fibers free of intra-collar opposite-sign saddle
collisions: even if `F` undergoes arbitrarily many avoided crossings outside
`Ioo (e₀ - η_pad) (e₀ + δ + η_pad)`, packing excursions inside `[-R, R]` caps the Gaussian mass of
`{x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)}` by
`γ(|t| > R) + (⌊L * R / η_pad⌋₊ + 1) * δ / (√(2 π) * c)`. -/
theorem gaussian_bipolarFree_collar_anticoncentration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (hΩ : MeasurableSet Ω)
    {L : ℝ≥0} (hL_pos : 0 < (L : ℝ))
    {c e₀ δ η_pad R : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hη_pad : 0 < η_pad) (hR : 0 < R)
    (hfib : ∀ y : ι → ℝ,
      let I_y := {t : ℝ | Function.update y i₀ t ∈ Ω}
      Convex ℝ I_y ∧
      LipschitzOnWith L (fun t => F (Function.update y i₀ t)) I_y ∧
      ∀ t ∈ I_y, F (Function.update y i₀ t) ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad) →
        ∃ r > 0, ∃ sgn : Bool,
          ∀ s ∈ Ioo (t - r) (t + r) ∩ I_y, ∀ b ∈ Ioo (t - r) (t + r) ∩ I_y, s < b →
            ∀ ε > 0, ∃ h ∈ Ioc (0 : ℝ) (b - s),
              (c - ε) * h ≤ (if sgn then 1 else -1) *
                (F (Function.update y i₀ (s + h)) - F (Function.update y i₀ s))) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      (gaussianReal 0 1).real {t : ℝ | R < |t|} +
        ((⌊(L : ℝ) * R / η_pad⌋₊ + 1 : ℕ) : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
  let γ := gaussianReal 0 1
  let γ_pi := Measure.pi fun _ : ι => γ
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  let M : ℕ := ⌊(L : ℝ) * R / η_pad⌋₊ + 1
  have hM_pos : (0 : ℝ) < (M : ℝ) := by dsimp only [M]; positivity
  let w : ℝ := 2 * R / (M : ℝ)
  have hw_lt : w < 2 * η_pad / (L : ℝ) := by
    have hgt : (L : ℝ) * R / η_pad < (M : ℝ) := by
      dsimp only [M]; exact_mod_cast Nat.lt_floor_add_one ((L : ℝ) * R / η_pad)
    have h1 : (L : ℝ) * R < (M : ℝ) * η_pad := (div_lt_iff₀ hη_pad).mp hgt
    dsimp only [w]
    rw [div_lt_div_iff₀ hM_pos hL_pos]
    nlinarith only [h1]
  let Tail : Set (ι → ℝ) := {x | R < |x i₀|}
  let Ω_tr : Set (ι → ℝ) := Ω ∩ {x | |x i₀| ≤ R}
  have hΩ_tr_meas : MeasurableSet Ω_tr :=
    hΩ.inter (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply i₀)) measurable_const)
  let Core : Set (ι → ℝ) := {x ∈ Ω_tr | F x ∈ Ioc e₀ (e₀ + δ)}
  have hCore_meas : MeasurableSet Core := hΩ_tr_meas.inter (hF measurableSet_Ioc)
  have hsub_split : {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ⊆ Tail ∪ Core := by
    rintro x ⟨hxΩ, hxF⟩
    rcases lt_or_ge R |x i₀| with hgt | hle
    · exact Or.inl hgt
    · exact Or.inr ⟨⟨hxΩ, hle⟩, hxF⟩
  have hmp_eval : MeasurePreserving (fun x : ι → ℝ => x i₀) γ_pi γ :=
    measurePreserving_eval (fun _ : ι => γ) i₀
  have hTail_eq : γ_pi.real Tail = γ.real {t : ℝ | R < |t|} := by
    have hmeas_t : MeasurableSet {t : ℝ | R < |t|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    exact congrArg ENNReal.toReal (hmp_eval.measure_preimage hmeas_t.nullMeasurableSet)
  have h1d (y : ι → ℝ) :
      γ {t : ℝ | Function.update y i₀ t ∈ Core} ≤
        ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    obtain ⟨hconv, hlip, hloc⟩ := hfib y
    let I_y := {t : ℝ | Function.update y i₀ t ∈ Ω}
    let g : ℝ → ℝ := fun t => F (Function.update y i₀ t)
    let K_seg (m : Fin M) : Set ℝ :=
      Icc (-R + (m.val : ℝ) * w) (-R + ((m.val : ℝ) + 1) * w)
    have hcov_R : Icc (-R) R ⊆ ⋃ m : Fin M, K_seg m := by
      intro t ht
      have hw_pos : 0 < w := div_pos (by linarith only [hR]) hM_pos
      by_cases htop : t = R
      · subst t
        let m_last : Fin M := ⟨M - 1, by dsimp [M]; omega⟩
        refine mem_iUnion.mpr ⟨m_last, ?_⟩
        have hm_eq : ((m_last.val : ℝ) + 1) * w = 2 * R := by
          have hcast : (m_last.val : ℝ) + 1 = (M : ℝ) := by
            have h1 : m_last.val + 1 = M := Nat.sub_add_cancel (by dsimp [M]; omega)
            exact_mod_cast h1
          rw [hcast]; dsimp only [w]; exact mul_div_cancel₀ (2 * R) hM_pos.ne'
        exact ⟨by change -R + (m_last.val : ℝ) * w ≤ R; linarith only [hm_eq, hw_pos],
               by change R ≤ -R + ((m_last.val : ℝ) + 1) * w; linarith only [hm_eq]⟩
      · have ht_lt : t < R := lt_of_le_of_ne ht.2 htop
        have hdiv_nn : 0 ≤ (t + R) / w := div_nonneg (by linarith only [ht.1]) hw_pos.le
        let idx := ⌊(t + R) / w⌋₊
        have hidx_lt : idx < M := by
          have hdiv_lt : (t + R) / w < (M : ℝ) := by
            rw [div_lt_iff₀ hw_pos]
            have hMw : (M : ℝ) * w = 2 * R := mul_div_cancel₀ (2 * R) hM_pos.ne'
            linarith only [ht_lt, hMw]
          exact (Nat.floor_lt hdiv_nn).mpr hdiv_lt
        refine mem_iUnion.mpr ⟨⟨idx, hidx_lt⟩, ?_⟩
        have hlo : (idx : ℝ) * w ≤ t + R := (le_div_iff₀ hw_pos).mp (Nat.floor_le hdiv_nn)
        have hhi : t + R < ((idx : ℝ) + 1) * w := (div_lt_iff₀ hw_pos).mp (Nat.lt_floor_add_one ((t + R) / w))
        exact ⟨by change -R + (idx : ℝ) * w ≤ t; linarith only [hlo],
               by change t ≤ -R + ((idx : ℝ) + 1) * w; linarith only [hhi]⟩
    have hseg_box (m : Fin M) : ∃ a_m : ℝ,
        (I_y ∩ K_seg m) ∩ {t | g t ∈ Ioc e₀ (e₀ + δ)} ⊆ Icc a_m (a_m + δ / c) := by
      let A_m := (I_y ∩ K_seg m) ∩ {t | g t ∈ Ioc e₀ (e₀ + δ)}
      by_cases hA_emp : A_m = ∅
      · refine ⟨0, ?_⟩; change A_m ⊆ _; rw [hA_emp]; exact empty_subset _
      · obtain ⟨t₀, ht₀⟩ := nonempty_iff_ne_empty.mpr hA_emp
        have hdiam : ∀ t₁ ∈ A_m, ∀ t₂ ∈ A_m, t₁ ≤ t₂ → t₂ - t₁ ≤ δ / c := by
          intro t₁ ht₁ t₂ ht₂ h12
          have h1 : -R + (m.val : ℝ) * w ≤ t₁ := ht₁.1.2.1
          have h2 : t₂ ≤ -R + ((m.val : ℝ) + 1) * w := ht₂.1.2.2
          have hw_seg : t₂ - t₁ ≤ w := by linarith only [h1, h2]
          rcases lipschitz_collar_bipolarFree_diam_or_sep hconv hL_pos hlip hc hδ hη_pad hloc
              ht₁.1.1 ht₂.1.1 ⟨ht₁.2.1.le, ht₁.2.2⟩ ⟨ht₂.2.1.le, ht₂.2.2⟩ with hle | hge
          · rwa [abs_of_nonneg (sub_nonneg.mpr h12)] at hle
          · rw [abs_of_nonneg (sub_nonneg.mpr h12)] at hge
            linarith only [hw_seg, hw_lt, hge]
        have hA_bdd : BddBelow A_m := ⟨t₀ - δ / c, fun t ht => by
          rcases le_total t t₀ with hle | hge
          · linarith only [hdiam t ht t₀ ht₀ hle]
          · linarith only [hge, div_nonneg hδ hc.le]⟩
        let a_m := sInf A_m
        refine ⟨a_m, fun t ht => ⟨csInf_le hA_bdd ht, ?_⟩⟩
        have hlb : t - δ / c ≤ a_m := le_csInf ⟨t₀, ht₀⟩ fun u hu => by
          rcases le_total u t with hut | htu
          · linarith only [hdiam u hu t ht hut]
          · linarith only [htu, div_nonneg hδ hc.le]
        linarith only [hlb]
    choose a_m ha_m using hseg_box
    have hsub_union : {t : ℝ | Function.update y i₀ t ∈ Core} ⊆
        ⋃ m : Fin M, Icc (a_m m) (a_m m + δ / c) := by
      rintro t ⟨⟨htΩ, htR⟩, htF⟩
      change |Function.update y i₀ t i₀| ≤ R at htR
      rw [Function.update_self] at htR
      obtain ⟨m, hm⟩ := mem_iUnion.mp (hcov_R (abs_le.mp htR))
      exact mem_iUnion.mpr ⟨m, ha_m m ⟨⟨htΩ, hm⟩, htF⟩⟩
    calc γ {t : ℝ | Function.update y i₀ t ∈ Core}
        ≤ γ (⋃ m : Fin M, Icc (a_m m) (a_m m + δ / c)) := measure_mono hsub_union
      _ ≤ ∑ m : Fin M, γ (Icc (a_m m) (a_m m + δ / c)) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _m : Fin M, ENNReal.ofReal (δ / (Real.sqrt (2 * Real.pi) * c)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          refine (gaussianReal_le_inv_sqrt_two_pi_vol _).trans ?_
          rw [Real.volume_Icc, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
      _ = ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M), mul_div_assoc]
  let p_i₀ : ι → Prop := fun i => i = i₀
  let e_split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p_i₀
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => γ) p_i₀
  let μ_one := @Measure.pi (Subtype p_i₀) (fun _ => ℝ) (Subtype.fintype p_i₀) _ (fun _ => γ)
  let μ_rest := @Measure.pi {i : ι // ¬ p_i₀ i} (fun _ => ℝ)
    (Subtype.fintype fun i => ¬ p_i₀ i) _ (fun _ => γ)
  have hCore_eq : γ_pi Core = (μ_one.prod μ_rest) (e_split.symm ⁻¹' Core) := by
    rw [← hmp.measure_preimage (e_split.symm.measurable hCore_meas).nullMeasurableSet]
    congr 1; ext x; change x ∈ Core ↔ e_split.symm (e_split x) ∈ Core; rw [e_split.symm_apply_apply]
  have hprod_eval : (μ_one.prod μ_rest) (e_split.symm ⁻¹' Core) =
      ∫⁻ z, μ_one {w_sub : Subtype p_i₀ → ℝ | e_split.symm (w_sub, z) ∈ Core} ∂μ_rest :=
    Measure.prod_apply_symm (e_split.symm.measurable hCore_meas)
  have hsec_le : ∀ z : {i : ι // ¬ p_i₀ i} → ℝ,
      μ_one {w_sub : Subtype p_i₀ → ℝ | e_split.symm (w_sub, z) ∈ Core} ≤
        ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    intro z
    let y : ι → ℝ := e_split.symm (0, z)
    let j₀ : Subtype p_i₀ := ⟨i₀, rfl⟩
    have hupd_eq (w_sub : Subtype p_i₀ → ℝ) :
        e_split.symm (w_sub, z) = Function.update y i₀ (w_sub j₀) := by
      funext i
      by_cases hi : i = i₀
      · subst hi; simp [e_split, y, j₀, p_i₀, MeasurableEquiv.piEquivPiSubtypeProd]
      · simp [e_split, y, hi, p_i₀, MeasurableEquiv.piEquivPiSubtypeProd]
    have hset_eq : {w_sub : Subtype p_i₀ → ℝ | e_split.symm (w_sub, z) ∈ Core} =
        Set.univ.pi (fun _ : Subtype p_i₀ => {t : ℝ | Function.update y i₀ t ∈ Core}) := by
      ext w_sub
      simp only [mem_setOf_eq, mem_univ_pi, hupd_eq]
      exact ⟨fun hw ⟨j, hj⟩ => (Subtype.ext hj : (⟨j, hj⟩ : Subtype p_i₀) = j₀) ▸ hw,
             fun hw => hw j₀⟩
    rw [hset_eq]
    have hpi : μ_one (Set.univ.pi fun _ : Subtype p_i₀ => {t : ℝ | Function.update y i₀ t ∈ Core}) =
        γ {t : ℝ | Function.update y i₀ t ∈ Core} := by
      dsimp only [μ_one]
      rw [@Measure.pi_pi (Subtype p_i₀) (fun _ => ℝ) (Subtype.fintype p_i₀) _ (fun _ => γ)]
      refine Finset.prod_eq_single j₀ ?_ ?_
      · rintro ⟨j, hj⟩ _ hne; exact (hne (Subtype.ext hj)).elim
      · intro h; exact (h (@Finset.mem_univ (Subtype p_i₀) (Subtype.fintype p_i₀) j₀)).elim
    rw [hpi]; exact h1d y
  have hCore_real : γ_pi.real Core ≤ (M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
    have htot : γ_pi Core ≤ ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
      rw [hCore_eq, hprod_eval]
      refine (lintegral_mono hsec_le).trans ?_
      haveI : IsProbabilityMeasure μ_rest := by dsimp only [μ_rest]; infer_instance
      rw [lintegral_const, measure_univ, mul_one]
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) htot
  calc γ_pi.real {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)}
      ≤ γ_pi.real (Tail ∪ Core) := measureReal_mono hsub_split (measure_ne_top _ _)
    _ ≤ γ_pi.real Tail + γ_pi.real Core := measureReal_union_le Tail Core
    _ ≤ γ.real {t : ℝ | R < |t|} +
          ((⌊(L : ℝ) * R / η_pad⌋₊ + 1 : ℕ) : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
        rw [hTail_eq]; exact add_le_add le_rfl hCore_real

/-! ## Section 2: `2`D determinant coercivity, `SO(ι)`-rotating-direction charts, and tie avoidance -/

/-- Every linear isometry equivalence `L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι` preserves
the product Gaussian measure `Measure.pi (fun _ : ι => gaussianReal 0 1)` on `ι → ℝ`. -/
theorem measurePreserving_pi_gaussian_linearIsometryEquiv {ι : Type*} [Fintype ι]
    (L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving (fun x : ι → ℝ => (L (WithLp.toLp 2 x)).ofLp)
      (Measure.pi fun _ : ι => gaussianReal 0 1)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let e_lp : (ι → ℝ) ≃ᵐ EuclideanSpace ℝ ι := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hdens_meas : Measurable
      (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (euclideanGaussianDensityReal x)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold euclideanGaussianDensityReal
    exact measurable_const.mul (Real.continuous_exp.measurable.comp
      (((continuous_norm.pow 2).neg.div_const 2).measurable))
  have hmp_std : MeasurePreserving L
      (stdGaussian (EuclideanSpace ℝ ι)) (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine ⟨L.toMeasurableEquiv.measurable, ?_⟩
    change (stdGaussian (EuclideanSpace ℝ ι)).map L.toMeasurableEquiv = _
    rw [stdGaussian_eq_withDensity,
      map_withDensity_measurableEquiv _ L.toMeasurableEquiv hdens_meas]
    have hvol : (volume : Measure (EuclideanSpace ℝ ι)).map L.toMeasurableEquiv = volume :=
      L.measurePreserving.map_eq
    rw [hvol]
    congr 1; funext y; congr 1
    unfold euclideanGaussianDensityReal
    rw [LinearIsometryEquiv.coe_symm_toMeasurableEquiv, L.symm.norm_map]
  have hmp_to : MeasurePreserving e_lp
      (Measure.pi fun _ : ι => gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨e_lp.measurable, by simpa only [e_lp, MeasurableEquiv.coe_toLp] using map_pi_eq_stdGaussian⟩
  have hmp_from : MeasurePreserving e_lp.symm
      (stdGaussian (EuclideanSpace ℝ ι)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    refine ⟨e_lp.symm.measurable, ?_⟩
    rw [← hmp_to.map_eq, Measure.map_map e_lp.symm.measurable e_lp.measurable]
    simp
  exact (hmp_from.comp hmp_std).comp hmp_to

/-- Explicit Householder linear isometry equivalence sending `EuclideanSpace.single i₀ 1` to any
prescribed unit vector `w : EuclideanSpace ℝ ι` (`‖w‖ = 1`). -/
theorem exists_linearIsometryEquiv_single_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {w : EuclideanSpace ℝ ι} (hw : ‖w‖ = 1) :
    ∃ L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι,
      L (EuclideanSpace.single i₀ 1) = w := by
  let e₀ : EuclideanSpace ℝ ι := EuclideanSpace.single i₀ 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  by_cases hwe : w = e₀
  · exact ⟨LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ ι), hwe.symm⟩
  · let v : EuclideanSpace ℝ ι := e₀ - w
    have hv_ne : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hwe)
    have hv_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv_ne)
    let f : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
      { toFun := fun x => x - (2 * inner ℝ v x / ‖v‖ ^ 2) • v
        map_add' := fun x y => by
          rw [inner_add_right]
          have h : 2 * (inner ℝ v x + inner ℝ v y) / ‖v‖ ^ 2 =
              2 * inner ℝ v x / ‖v‖ ^ 2 + 2 * inner ℝ v y / ‖v‖ ^ 2 := by ring
          rw [h, add_smul]; abel
        map_smul' := fun r x => by
          rw [inner_smul_right]
          simp only [RingHom.id_apply, smul_sub, smul_smul]
          congr 2; ring }
    have hfv : f v = -v := by
      change v - (2 * inner ℝ v v / ‖v‖ ^ 2) • v = -v
      rw [real_inner_self_eq_norm_sq, mul_div_cancel_right₀ 2 hv_sq_pos.ne']
      calc v - (2 : ℝ) • v = ((1 : ℝ) - 2) • v := by rw [sub_smul, one_smul]
        _ = -v := by norm_num
    have hinv (x : EuclideanSpace ℝ ι) : f (f x) = x := by
      have h1 : f (f x) = f x - (2 * inner ℝ v x / ‖v‖ ^ 2) • f v := by
        change f (x - (2 * inner ℝ v x / ‖v‖ ^ 2) • v) = _
        rw [map_sub, map_smul]
      rw [h1, hfv, smul_neg, sub_neg_eq_add]
      change (x - (2 * inner ℝ v x / ‖v‖ ^ 2) • v) + (2 * inner ℝ v x / ‖v‖ ^ 2) • v = x
      abel
    have hnorm (x : EuclideanSpace ℝ ι) : ‖f x‖ = ‖x‖ := by
      let α := 2 * inner ℝ v x / ‖v‖ ^ 2
      have hsq : ‖x - α • v‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          real_inner_comm v x]
        dsimp only [α]
        field_simp [hv_sq_pos.ne']
        ring
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    let L : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
      { f with
        invFun := f
        left_inv := hinv
        right_inv := hinv
        norm_map' := hnorm }
    refine ⟨L, ?_⟩
    change e₀ - (2 * inner ℝ v e₀ / ‖v‖ ^ 2) • v = w
    have hv_sq_eq : ‖v‖ ^ 2 = 2 * inner ℝ v e₀ := by
      dsimp only [v]
      rw [norm_sub_sq_real, he₀, hw, inner_sub_left, real_inner_self_eq_norm_sq, he₀,
        real_inner_comm e₀ w]
      ring
    have hcoef : 2 * inner ℝ v e₀ / ‖v‖ ^ 2 = 1 := by
      rw [← hv_sq_eq]; exact div_self hv_sq_pos.ne'
    rw [hcoef, one_smul]
    dsimp only [v]; abel

/-- Exact `2`D co-directional coercivity and antiparallel characterization:
1. Two vectors `ξ₁, ξ₂ ∈ ℝ²` fail to admit a strictly co-positive direction `w ∈ ℝ²` if and only if
   one vanishes or `ξ₁ + λ • ξ₂ = 0` for some `λ > 0`.
2. Whenever `ξ₁ ≠ (0, 0)` and `ξ₂ ≠ (0, 0)`, there exists a unit vector `w ∈ ℝ²`
   (`w.1² + w.2² = 1`) satisfying simultaneously
   `|ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1| / (2 * √(ξ₂.1² + ξ₂.2²)) ≤ ξ₁.1 * w.1 + ξ₁.2 * w.2` and
   `|ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1| / (2 * √(ξ₁.1² + ξ₁.2²)) ≤ ξ₂.1 * w.1 + ξ₂.2 * w.2`. -/
theorem twoDim_shared_coercive_unit_of_det (ξ₁ ξ₂ : ℝ × ℝ) :
    ((∀ w : ℝ × ℝ, min (ξ₁.1 * w.1 + ξ₁.2 * w.2) (ξ₂.1 * w.1 + ξ₂.2 * w.2) ≤ 0) ↔
      (ξ₁ = (0, 0) ∨ ξ₂ = (0, 0) ∨ ∃ lam > 0, ξ₁.1 + lam * ξ₂.1 = 0 ∧ ξ₁.2 + lam * ξ₂.2 = 0)) ∧
    (ξ₁ ≠ (0, 0) → ξ₂ ≠ (0, 0) →
      ∃ w : ℝ × ℝ, w.1 ^ 2 + w.2 ^ 2 = 1 ∧
        |ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1| / (2 * Real.sqrt (ξ₂.1 ^ 2 + ξ₂.2 ^ 2)) ≤
          ξ₁.1 * w.1 + ξ₁.2 * w.2 ∧
        |ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1| / (2 * Real.sqrt (ξ₁.1 ^ 2 + ξ₁.2 ^ 2)) ≤
          ξ₂.1 * w.1 + ξ₂.2 * w.2) := by
  have hnorm_pos {v : ℝ × ℝ} (hv : v ≠ (0, 0)) : 0 < v.1 ^ 2 + v.2 ^ 2 := by
    by_contra hle
    have h1 : v.1 = 0 := by nlinarith only [hle, sq_nonneg v.1, sq_nonneg v.2]
    have h2 : v.2 = 0 := by nlinarith only [hle, sq_nonneg v.1, sq_nonneg v.2]
    exact hv (Prod.ext h1 h2)
  have hbisector : ∀ (h₁ : ξ₁ ≠ (0, 0)) (h₂ : ξ₂ ≠ (0, 0)),
      (∃ lam > 0, ξ₁.1 + lam * ξ₂.1 = 0 ∧ ξ₁.2 + lam * ξ₂.2 = 0) ∨
      (∃ w : ℝ × ℝ, w.1 ^ 2 + w.2 ^ 2 = 1 ∧
        0 < ξ₁.1 * w.1 + ξ₁.2 * w.2 ∧ 0 < ξ₂.1 * w.1 + ξ₂.2 * w.2 ∧
        |ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1| / (2 * Real.sqrt (ξ₂.1 ^ 2 + ξ₂.2 ^ 2)) ≤
          ξ₁.1 * w.1 + ξ₁.2 * w.2 ∧
        |ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1| / (2 * Real.sqrt (ξ₁.1 ^ 2 + ξ₁.2 ^ 2)) ≤
          ξ₂.1 * w.1 + ξ₂.2 * w.2) := by
    intro h₁ h₂
    let r₁ := Real.sqrt (ξ₁.1 ^ 2 + ξ₁.2 ^ 2)
    let r₂ := Real.sqrt (ξ₂.1 ^ 2 + ξ₂.2 ^ 2)
    have hr₁ : 0 < r₁ := Real.sqrt_pos.mpr (hnorm_pos h₁)
    have hr₂ : 0 < r₂ := Real.sqrt_pos.mpr (hnorm_pos h₂)
    have hr₁_sq : r₁ ^ 2 = ξ₁.1 ^ 2 + ξ₁.2 ^ 2 := Real.sq_sqrt (hnorm_pos h₁).le
    have hr₂_sq : r₂ ^ 2 = ξ₂.1 ^ 2 + ξ₂.2 ^ 2 := Real.sq_sqrt (hnorm_pos h₂).le
    let u₁ : ℝ × ℝ := (ξ₁.1 / r₁, ξ₁.2 / r₁)
    let u₂ : ℝ × ℝ := (ξ₂.1 / r₂, ξ₂.2 / r₂)
    have hu₁_sq : u₁.1 ^ 2 + u₁.2 ^ 2 = 1 := by
      dsimp only [u₁]; field_simp [hr₁.ne']; linarith only [hr₁_sq]
    have hu₂_sq : u₂.1 ^ 2 + u₂.2 ^ 2 = 1 := by
      dsimp only [u₂]; field_simp [hr₂.ne']; linarith only [hr₂_sq]
    by_cases hsum : (u₁.1 + u₂.1, u₁.2 + u₂.2) = (0, 0)
    · left
      obtain ⟨hs1, hs2⟩ := Prod.mk.inj hsum
      dsimp only [u₁, u₂] at hs1 hs2
      refine ⟨r₁ / r₂, div_pos hr₁ hr₂, ?_, ?_⟩
      · have h : (ξ₁.1 / r₁ + ξ₂.1 / r₂) * r₁ = 0 * r₁ := congrArg (fun z => z * r₁) hs1
        field_simp [hr₁.ne', hr₂.ne'] at h ⊢
        linarith only [h]
      · have h : (ξ₁.2 / r₁ + ξ₂.2 / r₂) * r₁ = 0 * r₁ := congrArg (fun z => z * r₁) hs2
        field_simp [hr₁.ne', hr₂.ne'] at h ⊢
        linarith only [h]
    · right
      have hs_pos_sq : 0 < (u₁.1 + u₂.1) ^ 2 + (u₁.2 + u₂.2) ^ 2 := hnorm_pos hsum
      let s := Real.sqrt ((u₁.1 + u₂.1) ^ 2 + (u₁.2 + u₂.2) ^ 2)
      have hs_pos : 0 < s := Real.sqrt_pos.mpr hs_pos_sq
      have hs_sq : s ^ 2 = (u₁.1 + u₂.1) ^ 2 + (u₁.2 + u₂.2) ^ 2 := Real.sq_sqrt hs_pos_sq.le
      let w : ℝ × ℝ := ((u₁.1 + u₂.1) / s, (u₁.2 + u₂.2) / s)
      have hw_unit : w.1 ^ 2 + w.2 ^ 2 = 1 := by
        dsimp only [w]; field_simp [hs_pos.ne']; linarith only [hs_sq]
      have hdot_u₁ : u₁.1 * w.1 + u₁.2 * w.2 = s / 2 := by
        dsimp only [w]; field_simp [hs_pos.ne']; nlinarith only [hs_sq, hu₁_sq, hu₂_sq]
      have hdot_u₂ : u₂.1 * w.1 + u₂.2 * w.2 = s / 2 := by
        dsimp only [w]; field_simp [hs_pos.ne']; nlinarith only [hs_sq, hu₁_sq, hu₂_sq]
      have hdot_ξ₁ : ξ₁.1 * w.1 + ξ₁.2 * w.2 = r₁ * (s / 2) := by
        have h1 : ξ₁.1 = r₁ * u₁.1 := by dsimp [u₁]; exact (mul_div_cancel₀ _ hr₁.ne').symm
        have h2 : ξ₁.2 = r₁ * u₁.2 := by dsimp [u₁]; exact (mul_div_cancel₀ _ hr₁.ne').symm
        rw [h1, h2]
        calc r₁ * u₁.1 * w.1 + r₁ * u₁.2 * w.2
            = r₁ * (u₁.1 * w.1 + u₁.2 * w.2) := by ring
          _ = r₁ * (s / 2) := by rw [hdot_u₁]
      have hdot_ξ₂ : ξ₂.1 * w.1 + ξ₂.2 * w.2 = r₂ * (s / 2) := by
        have h1 : ξ₂.1 = r₂ * u₂.1 := by dsimp [u₂]; exact (mul_div_cancel₀ _ hr₂.ne').symm
        have h2 : ξ₂.2 = r₂ * u₂.2 := by dsimp [u₂]; exact (mul_div_cancel₀ _ hr₂.ne').symm
        rw [h1, h2]
        calc r₂ * u₂.1 * w.1 + r₂ * u₂.2 * w.2
            = r₂ * (u₂.1 * w.1 + u₂.2 * w.2) := by ring
          _ = r₂ * (s / 2) := by rw [hdot_u₂]
      have hdet_u_le : |u₁.1 * u₂.2 - u₁.2 * u₂.1| ≤ s := by
        have hsq_le : (u₁.1 * u₂.2 - u₁.2 * u₂.1) ^ 2 ≤ s ^ 2 := by
          have hlagrange : (u₁.1 ^ 2 + u₁.2 ^ 2) * (u₂.1 ^ 2 + u₂.2 ^ 2) -
              (u₁.1 * u₂.1 + u₁.2 * u₂.2) ^ 2 = (u₁.1 * u₂.2 - u₁.2 * u₂.1) ^ 2 := by ring
          have hsum_exp : (u₁.1 + u₂.1) ^ 2 + (u₁.2 + u₂.2) ^ 2 =
              (u₁.1 ^ 2 + u₁.2 ^ 2) + (u₂.1 ^ 2 + u₂.2 ^ 2) +
                2 * (u₁.1 * u₂.1 + u₁.2 * u₂.2) := by ring
          have h1_minus_d : 1 - (u₁.1 * u₂.1 + u₁.2 * u₂.2) ≤ 2 := by
            linarith only [hs_pos_sq.le, hsum_exp, hu₁_sq, hu₂_sq]
          have h1_plus_d : 0 ≤ 1 + (u₁.1 * u₂.1 + u₁.2 * u₂.2) := by
            linarith only [hs_pos_sq.le, hsum_exp, hu₁_sq, hu₂_sq]
          rw [hu₁_sq, hu₂_sq, one_mul] at hlagrange
          have hs_eq : s ^ 2 = 2 * (1 + (u₁.1 * u₂.1 + u₁.2 * u₂.2)) := by
            linarith only [hs_sq, hsum_exp, hu₁_sq, hu₂_sq]
          nlinarith only [hlagrange, h1_minus_d, h1_plus_d, hs_eq]
        rw [← sq_abs] at hsq_le
        exact (sq_le_sq₀ (abs_nonneg _) hs_pos.le).mp hsq_le
      have hdet_eq : |ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1| = r₁ * r₂ * |u₁.1 * u₂.2 - u₁.2 * u₂.1| := by
        have hid : ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1 = r₁ * r₂ * (u₁.1 * u₂.2 - u₁.2 * u₂.1) := by
          dsimp only [u₁, u₂]; field_simp [hr₁.ne', hr₂.ne']
        rw [hid, abs_mul, abs_of_pos (mul_pos hr₁ hr₂)]
      refine ⟨w, hw_unit, ?_, ?_, ?_, ?_⟩
      · rw [hdot_ξ₁]; positivity
      · rw [hdot_ξ₂]; positivity
      · rw [hdet_eq, hdot_ξ₁]
        have hdiv : r₁ * r₂ * |u₁.1 * u₂.2 - u₁.2 * u₂.1| / (2 * r₂) =
            r₁ * (|u₁.1 * u₂.2 - u₁.2 * u₂.1| / 2) := by field_simp [hr₂.ne']
        rw [hdiv]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet_u_le two_pos.le) hr₁.le
      · rw [hdet_eq, hdot_ξ₂]
        have hdiv : r₁ * r₂ * |u₁.1 * u₂.2 - u₁.2 * u₂.1| / (2 * r₁) =
            r₂ * (|u₁.1 * u₂.2 - u₁.2 * u₂.1| / 2) := by field_simp [hr₁.ne']
        rw [hdiv]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet_u_le two_pos.le) hr₂.le
  refine ⟨⟨?_, ?_⟩, fun h₁ h₂ => ?_⟩
  · intro hall
    by_cases h₁ : ξ₁ = (0, 0)
    · exact Or.inl h₁
    by_cases h₂ : ξ₂ = (0, 0)
    · exact Or.inr (Or.inl h₂)
    rcases hbisector h₁ h₂ with hanti | ⟨w, _, hw1, hw2, _, _⟩
    · exact Or.inr (Or.inr hanti)
    · exfalso; exact (lt_min hw1 hw2).not_ge (hall w)
  · rintro (rfl | rfl | ⟨lam, hlam, h1, h2⟩) w
    · simp
    · simp
    · have hrel : (ξ₁.1 * w.1 + ξ₁.2 * w.2) + lam * (ξ₂.1 * w.1 + ξ₂.2 * w.2) = 0 := by
        linear_combination w.1 * h1 + w.2 * h2
      by_cases hw2 : ξ₂.1 * w.1 + ξ₂.2 * w.2 ≤ 0
      · exact (min_le_right _ _).trans hw2
      · push Not at hw2
        exact (min_le_left _ _).trans (by nlinarith only [hrel, hlam, hw2])
  · rcases hbisector h₁ h₂ with ⟨lam, hlam, hanti1, hanti2⟩ | ⟨w, hw, _, _, hle1, hle2⟩
    · have hdet0 : ξ₁.1 * ξ₂.2 - ξ₁.2 * ξ₂.1 = 0 := by
        linear_combination ξ₂.2 * hanti1 - ξ₂.1 * hanti2
      let r₁ := Real.sqrt (ξ₁.1 ^ 2 + ξ₁.2 ^ 2)
      have hr₁ : 0 < r₁ := Real.sqrt_pos.mpr (hnorm_pos h₁)
      have hr₁_sq : r₁ ^ 2 = ξ₁.1 ^ 2 + ξ₁.2 ^ 2 := Real.sq_sqrt (hnorm_pos h₁).le
      let w : ℝ × ℝ := (-ξ₁.2 / r₁, ξ₁.1 / r₁)
      have hw_unit : w.1 ^ 2 + w.2 ^ 2 = 1 := by
        dsimp only [w]; field_simp [hr₁.ne']; linarith only [hr₁_sq]
      have hw1_zero : ξ₁.1 * w.1 + ξ₁.2 * w.2 = 0 := by dsimp [w]; ring
      have hw2_zero : ξ₂.1 * w.1 + ξ₂.2 * w.2 = 0 := by
        have h : lam * (ξ₂.1 * w.1 + ξ₂.2 * w.2) = 0 := by
          linear_combination w.1 * hanti1 + w.2 * hanti2 - hw1_zero
        exact (mul_eq_zero.mp h).resolve_left hlam.ne'
      refine ⟨w, hw_unit, ?_, ?_⟩ <;> simp [hdet0, hw1_zero, hw2_zero]
    · exact ⟨w, hw, hle1, hle2⟩

/-- `SO(ι)`-invariant rotating-direction Gaussian chart anti-concentration: if `Ω` is covered by
`J` measurable convex charts `U r` on each of which `±F` has directional right Dini slope `≥ c > 0`
along a chart-dependent unit direction `w r : EuclideanSpace ℝ ι` (`‖w r‖ = 1`) inside
`Ioo (e₀ - η_pad) (e₀ + δ + η_pad)`, then
`ℙ(x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)) ≤ J * δ / (√(2 π) * c)`. -/
theorem gaussian_rotatingDirection_chart_anticoncentration
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (_hΩ : MeasurableSet Ω)
    {J : ℕ} (U : Fin J → Set (ι → ℝ)) (hU_meas : ∀ r, MeasurableSet (U r))
    (hU_conv : ∀ r, Convex ℝ (U r)) (hcov : Ω ⊆ ⋃ r : Fin J, U r)
    (w : Fin J → EuclideanSpace ℝ ι) (hw : ∀ r, ‖w r‖ = 1) (sgn : Fin J → Bool)
    {c e₀ δ η_pad : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hη_pad : 0 < η_pad)
    (hcont : ∀ r, ContinuousOn F (U r))
    (hdini : ∀ r : Fin J, ∀ x ∈ U r, F x ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad) →
      ∀ b > 0, x + b • (w r).ofLp ∈ U r → ∀ ε > 0,
        ∃ h ∈ Ioc (0 : ℝ) b,
          (c - ε) * h ≤ (if sgn r then 1 else -1) * (F (x + h • (w r).ofLp) - F x)) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      (J : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hchart (r : Fin J) :
      γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} ≤ δ / (Real.sqrt (2 * Real.pi) * c) := by
    obtain ⟨L, hL_single⟩ := exists_linearIsometryEquiv_single_eq i₀ (hw r)
    let φ : (ι → ℝ) → (ι → ℝ) := fun z => (L (WithLp.toLp 2 z)).ofLp
    have hmp_φ : MeasurePreserving φ γ_pi γ_pi := measurePreserving_pi_gaussian_linearIsometryEquiv L
    have hφ_add (z₁ z₂ : ι → ℝ) : φ (z₁ + z₂) = φ z₁ + φ z₂ := by
      change (L (WithLp.toLp 2 z₁ + WithLp.toLp 2 z₂)).ofLp = _
      rw [map_add]; rfl
    have hφ_smul (t : ℝ) (z : ι → ℝ) : φ (t • z) = t • φ z := by
      change (L (t • WithLp.toLp 2 z)).ofLp = _
      rw [map_smul]; rfl
    have hφ_e₀ : φ ((EuclideanSpace.single i₀ (1 : ℝ)).ofLp) = (w r).ofLp := by
      change (L (EuclideanSpace.single i₀ 1)).ofLp = (w r).ofLp
      rw [hL_single]
    have hφ_upd (y : ι → ℝ) (t : ℝ) :
        φ (Function.update y i₀ t) = φ (Function.update y i₀ 0) + t • (w r).ofLp := by
      have hdec : Function.update y i₀ t =
          Function.update y i₀ 0 + t • (EuclideanSpace.single i₀ (1 : ℝ)).ofLp := by
        funext i
        by_cases hi : i = i₀
        · subst hi; simp
        · simp [hi]
      rw [hdec, hφ_add, hφ_smul, hφ_e₀]
    let U' : Set (ι → ℝ) := φ ⁻¹' U r
    let F' : (ι → ℝ) → ℝ := F ∘ φ
    have hU'_meas : MeasurableSet U' := hmp_φ.measurable (hU_meas r)
    have hF'_meas : Measurable F' := hF.comp hmp_φ.measurable
    have hset_meas : MeasurableSet {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} :=
      (hU_meas r).inter (hF measurableSet_Ioc)
    have hpre_eq : γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} =
        γ_pi.real {z ∈ U' | F' z ∈ Ioc e₀ (e₀ + δ)} := by
      have h1 := congrArg ENNReal.toReal (hmp_φ.measure_preimage hset_meas.nullMeasurableSet)
      exact h1.symm
    rw [hpre_eq]
    have h1 := gaussian_levelBand_dini_anticoncentration i₀ hF'_meas hU'_meas 1 hc hδ hη_pad
      (e₀ := e₀) fun y => by
        let I_y : Set ℝ := {t : ℝ | Function.update y i₀ t ∈ U'}
        refine ⟨fun _ => I_y, fun _ => sgn r, fun t ht => mem_iUnion.mpr ⟨0, ht⟩, fun _ => ?_⟩
        have hconv_Iy : Convex ℝ I_y := by
          intro t₁ ht₁ t₂ ht₂ a b ha hb hab
          change φ (Function.update y i₀ (a * t₁ + b * t₂)) ∈ U r
          have hlin : φ (Function.update y i₀ (a * t₁ + b * t₂)) =
              a • φ (Function.update y i₀ t₁) + b • φ (Function.update y i₀ t₂) := by
            rw [hφ_upd y (a * t₁ + b * t₂), hφ_upd y t₁, hφ_upd y t₂]
            funext i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            linear_combination (φ (Function.update y i₀ 0) i) * hab.symm
          rw [hlin]
          exact (hU_conv r) ht₁ ht₂ ha hb hab
        have hcont_Iy : ContinuousOn (fun t => F' (Function.update y i₀ t)) I_y := by
          have h_aff : Continuous (fun t : ℝ => φ (Function.update y i₀ t)) := by
            rw [show (fun t : ℝ => φ (Function.update y i₀ t)) =
                fun t : ℝ => φ (Function.update y i₀ 0) + t • (w r).ofLp from funext (hφ_upd y)]
            exact continuous_const.add (continuous_id.smul continuous_const)
          exact (hcont r).comp h_aff.continuousOn (fun _ ht => ht)
        refine ⟨hconv_Iy, hcont_Iy, fun t₁ ht₁ hF₁ t₂ ht₂ h12 ε hε => ?_⟩
        have hstep_b : φ (Function.update y i₀ t₁) + (t₂ - t₁) • (w r).ofLp =
            φ (Function.update y i₀ t₂) := by
          rw [hφ_upd y t₁, hφ_upd y t₂]
          funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        obtain ⟨h, hh_mem, hh_le⟩ := hdini r (φ (Function.update y i₀ t₁)) ht₁ hF₁ (t₂ - t₁)
          (sub_pos.mpr h12) (hstep_b.symm ▸ ht₂) ε hε
        have hstep_h : φ (Function.update y i₀ t₁) + h • (w r).ofLp =
            φ (Function.update y i₀ (t₁ + h)) := by
          rw [hφ_upd y t₁, hφ_upd y (t₁ + h)]
          funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
        refine ⟨h, hh_mem, ?_⟩
        simpa only [F', Function.comp_apply, hstep_h] using hh_le
    simpa only [Nat.cast_one, one_mul] using h1
  have hsub_u : {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ⊆
      ⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} := by
    rintro x ⟨hxΩ, hxF⟩
    obtain ⟨r, hr⟩ := mem_iUnion.mp (hcov hxΩ)
    exact mem_iUnion₂.mpr ⟨r, Finset.mem_univ r, hr, hxF⟩
  calc γ_pi.real {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)}
      ≤ γ_pi.real (⋃ r ∈ (Finset.univ : Finset (Fin J)), {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)}) :=
          measureReal_mono hsub_u (measure_ne_top _ _)
    _ ≤ ∑ r ∈ (Finset.univ : Finset (Fin J)), γ_pi.real {x ∈ U r | F x ∈ Ioc e₀ (e₀ + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ (Finset.univ : Finset (Fin J)), δ / (Real.sqrt (2 * Real.pi) * c) :=
          Finset.sum_le_sum fun r _ => hchart r
    _ = (J : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_div_assoc]

/-- Direct transfer of `J` rotating-direction coercive charts across active circuit budgets
`j < (4 N + 1)(2 N + 2)(2^N)²` to fixed-`1 / 10` zero-drop locking `m_{1/10 + δ} = m_{1/10}`. -/
theorem fixed_tenth_locking_of_rotatingDirection_charts
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N : ℕ} (hN : 2 ≤ N)
    (H : (ι → ℝ) → selfAdjoint (Register N))
    (hH_meas : ∀ j : ℕ, Measurable fun x => criticalHeight (H x) j)
    {Ω : ℕ → Set (ι → ℝ)} (hΩ_meas : ∀ j, MeasurableSet (Ω j))
    (J : ℕ) {c δ η_pad : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ) (hη_pad : 0 < η_pad)
    (hcharts : ∀ j < (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2,
      ∃ (U : Fin J → Set (ι → ℝ)) (w : Fin J → EuclideanSpace ℝ ι) (sgn : Fin J → Bool),
        (∀ r, MeasurableSet (U r)) ∧ (∀ r, Convex ℝ (U r)) ∧ Ω j ⊆ (⋃ r : Fin J, U r) ∧
        (∀ r, ‖w r‖ = 1) ∧
        (∀ r, ContinuousOn (fun x => criticalHeight (H x) j) (U r)) ∧
        (∀ r : Fin J, ∀ x ∈ U r,
          criticalHeight (H x) j ∈ Ioo (1 / 10 - η_pad) (1 / 10 + δ + η_pad) →
          ∀ b > 0, x + b • (w r).ofLp ∈ U r → ∀ ε > 0,
            ∃ h ∈ Ioc (0 : ℝ) b,
              (c - ε) * h ≤ (if sgn r then 1 else -1) *
                (criticalHeight (H (x + h • (w r).ofLp)) j - criticalHeight (H x) j))) :
    let Q := (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2
    let Ω_all := ⋂ j ∈ Finset.range Q, Ω j
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω_all | ∃ m₁ m₂ : ℕ,
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂} ≤
      (Q : ℝ) * ((J : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
  intro Q Ω_all
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  let Bad := {x : ι → ℝ | x ∈ Ω_all ∧ ∃ m₁ m₂ : ℕ,
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂}
  have hsub : Bad ⊆ ⋃ j ∈ Finset.range Q,
      {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} := by
    rintro x ⟨hxΩ, m₁, m₂, hm₁, hm₂, hne⟩
    have hnot_clear : ¬ (1 / 10 : ℝ) ∉ jumpTolerances (H x) δ := fun hclear =>
      hne ((maximum_eq_iff_criticalHeight_clearance hN (H x) (by norm_num) hδ hm₁ hm₂).2.mpr hclear)
    rw [not_not] at hnot_clear
    obtain ⟨j, _, hj_mem⟩ := hnot_clear
    have hj_lt_Q : j < Q := by
      by_contra hge
      have h0 := criticalHeight_eq_zero_of_exact_cap hN (H x) (Nat.le_of_not_lt hge)
      rw [h0] at hj_mem; linarith only [hj_mem.1]
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj_lt_Q,
      (mem_iInter₂.mp hxΩ) j (Finset.mem_range.mpr hj_lt_Q), hj_mem⟩
  calc γ_pi.real Bad
      ≤ γ_pi.real (⋃ j ∈ Finset.range Q,
          {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)}) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range Q,
          γ_pi.real {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range Q, (J : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨U, w, sgn, hUm, hUc, hcov, hw, hcont, hdini⟩ :=
            hcharts j (Finset.mem_range.mp hj)
          exact gaussian_rotatingDirection_chart_anticoncentration (hH_meas j) (hΩ_meas j)
            U hUm hUc hcov w hw sgn hc hδ hη_pad hcont hdini
    _ = (Q : ℝ) * ((J : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Generic parallel-line avoidance of intra-collar branch ties: if each branch pair `p ∈ P_idx`
has tie height `h_tie p` satisfying right Dini coercivity `≥ c₂ > 0` along a transverse coordinate
`i₂` inside `Ioo (e₀ - 3 * η_pad / 2) (e₀ + δ + 3 * η_pad / 2)`, then the Gaussian measure of
points encountering an intra-collar tie `h_tie p x ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)` across
`P_idx` is bounded by `P_idx.card * (δ + 2 * η_pad) / (√(2 π) * c₂)`. -/
theorem generic_parallel_lines_avoid_collar_ties
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (i₂ : ι) (P_idx : Finset α)
    (U_tie : α → Set (ι → ℝ)) (hU_meas : ∀ p ∈ P_idx, MeasurableSet (U_tie p))
    (h_tie : α → (ι → ℝ) → ℝ) (hh_meas : ∀ p ∈ P_idx, Measurable (h_tie p))
    {c₂ e₀ δ η_pad : ℝ} (hc₂ : 0 < c₂) (hδ : 0 ≤ δ) (hη_pad : 0 < η_pad)
    (htrans : ∀ p ∈ P_idx, ∀ y : ι → ℝ, ∃ sgn : Bool,
      let I_p := {u₂ : ℝ | Function.update y i₂ u₂ ∈ U_tie p}
      Convex ℝ I_p ∧
      ContinuousOn (fun u₂ => h_tie p (Function.update y i₂ u₂)) I_p ∧
      ∀ u₁ ∈ I_p,
        h_tie p (Function.update y i₂ u₁) ∈
          Ioo (e₀ - 3 * η_pad / 2) (e₀ + δ + 3 * η_pad / 2) →
        ∀ u₂ ∈ I_p, u₁ < u₂ → ∀ ε > 0,
          ∃ h ∈ Ioc (0 : ℝ) (u₂ - u₁),
            (c₂ - ε) * h ≤ (if sgn then 1 else -1) *
              (h_tie p (Function.update y i₂ (u₁ + h)) - h_tie p (Function.update y i₂ u₁))) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      (⋃ p ∈ P_idx, {x ∈ U_tie p | h_tie p x ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)}) ≤
      (P_idx.card : ℝ) * (δ + 2 * η_pad) / (Real.sqrt (2 * Real.pi) * c₂) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  have hpair (p : α) (hp : p ∈ P_idx) :
      γ_pi.real {x ∈ U_tie p | h_tie p x ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)} ≤
        (δ + 2 * η_pad) / (Real.sqrt (2 * Real.pi) * c₂) := by
    have hsub_band : {x ∈ U_tie p | h_tie p x ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)} ⊆
        {x ∈ U_tie p | h_tie p x ∈ Ioc (e₀ - η_pad) ((e₀ - η_pad) + (δ + 2 * η_pad))} := by
      rintro x ⟨hxU, hlo, hhi⟩
      exact ⟨hxU, hlo, by linarith only [hhi]⟩
    have h1 := gaussian_levelBand_dini_anticoncentration i₂ (hh_meas p hp) (hU_meas p hp) 1
      hc₂ (by linarith only [hδ, hη_pad] : 0 ≤ δ + 2 * η_pad) (half_pos hη_pad)
      (e₀ := e₀ - η_pad) fun y => by
        obtain ⟨sgn, hconv, hcont, hdini⟩ := htrans p hp y
        refine ⟨fun _ => {u₂ : ℝ | Function.update y i₂ u₂ ∈ U_tie p}, fun _ => sgn,
          fun u hu => mem_iUnion.mpr ⟨0, hu⟩, fun _ => ⟨hconv, hcont, ?_⟩⟩
        intro u₁ hu₁ hmem u₂ hu₂ h12 ε hε
        have hmem' : h_tie p (Function.update y i₂ u₁) ∈
            Ioo (e₀ - 3 * η_pad / 2) (e₀ + δ + 3 * η_pad / 2) :=
          ⟨by linarith only [hmem.1], by linarith only [hmem.2]⟩
        exact hdini u₁ hu₁ hmem' u₂ hu₂ h12 ε hε
    refine (measureReal_mono hsub_band (measure_ne_top _ _)).trans ?_
    simpa only [Nat.cast_one, one_mul] using h1
  calc γ_pi.real (⋃ p ∈ P_idx, {x ∈ U_tie p | h_tie p x ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)})
      ≤ ∑ p ∈ P_idx, γ_pi.real {x ∈ U_tie p | h_tie p x ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ P_idx, (δ + 2 * η_pad) / (Real.sqrt (2 * Real.pi) * c₂) :=
          Finset.sum_le_sum hpair
    _ = (P_idx.card : ℝ) * (δ + 2 * η_pad) / (Real.sqrt (2 * Real.pi) * c₂) := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]

/-! ## Section 3: Exact Kato sensitivity `Δρ(U_θ, ψ)`, antiparallel rigidity, and `2`-local blind spots -/

private theorem matAct_eq_clm_mc {N : ℕ} (A : Register N) (ψ : StateSpace N) :
    matAct A ψ = Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A ψ :=
  WithLp.ofLp_injective 2 (Matrix.ofLp_toEuclideanCLM A ψ).symm

private theorem matAct_mul_mc {N : ℕ} (A B : Register N) (ψ : StateSpace N) :
    matAct (A * B) ψ = matAct A (matAct B ψ) := by
  ext i; simp [matAct, Matrix.mulVec_mulVec]

private theorem inner_matAct_star_left_mc {N : ℕ} (A : Register N) (x y : StateSpace N) :
    inner ℂ (matAct (star A) x) y = inner ℂ x (matAct A y) := by
  rw [matAct_eq_clm_mc, matAct_eq_clm_mc,
    show Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) (star A) =
      ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A) from
      map_star Matrix.toEuclideanCLM A,
    ContinuousLinearMap.adjoint_inner_left]

private theorem norm_matAct_unitary_mc {N : ℕ} {U : Register N} (hU : U ∈ unitary (Register N))
    (ψ : StateSpace N) : ‖matAct U ψ‖ = ‖ψ‖ := by
  have h1 : inner ℂ (matAct U ψ) (matAct U ψ) = inner ℂ ψ ψ := by
    rw [← inner_matAct_star_left_mc, ← matAct_mul_mc, (Unitary.mem_iff.mp hU).1]
    have hone : matAct 1 ψ = ψ := by ext i; simp [matAct]
    rw [hone]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have hsq : ‖matAct U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := Complex.ofReal_injective (by simpa using h1)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem fourier_one_norm_eq_one (z : UnitAddCircle) : ‖(fourier 1 z : ℂ)‖ = 1 := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective z
  rw [← hr, fourier_coe_apply, Complex.norm_exp]
  have h1 : (2 : ℂ) * ↑Real.pi * Complex.I * ↑(1 : ℤ) * ↑r / ↑(1 : ℝ) =
      ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero]

private theorem projectiveSpectralMatrix_mem_unitary_mc {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V : UGroup N) (θ : Fin d → UnitAddCircle) :
    projectiveSpectralMatrix e V θ ∈ unitary (Register N) := by
  unfold projectiveSpectralMatrix
  refine mul_mem (mul_mem V.2 ?_) (Unitary.star_mem V.2)
  rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  constructor <;> ext a b <;> by_cases hab : a = b
  · subst hab
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply]
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      fourier_one_norm_eq_one, one_pow, Complex.ofReal_one]
  · simp [hab]
  · subst hab
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply]
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      fourier_one_norm_eq_one, one_pow, Complex.ofReal_one]
  · simp [hab]

/-- Off-diagonal Kato core in an explicit eigenbasis `(V, E)`. -/
def basisOffDiagCore {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (P : selfAdjoint (Register N)) : Register N :=
  let P_tilde : Register N := star V.val * P.val * V.val
  fun a b => if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)

/-- Self-adjoint off-diagonal Kato generator parameterized directly by `(V, E)`. -/
def basisKatoGenerator {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (P : selfAdjoint (Register N)) : selfAdjoint (Register N) :=
  ⟨V.val * basisOffDiagCore V E P * star V.val, by
    let P_tilde : Register N := star V.val * P.val * V.val
    have hP_sa : star P_tilde = P_tilde := by
      dsimp [P_tilde]; rw [star_mul, star_mul, star_star, P.2.star_eq, mul_assoc]
    have hK_sa : star (basisOffDiagCore V E P) = basisOffDiagCore V E P := by
      ext a b
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
      change star (if E a = E b then 0 else -Complex.I * P_tilde b a / ((E a - E b : ℝ) : ℂ)) =
        if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)
      by_cases h : E a = E b
      · rw [if_pos h, if_pos h.symm, star_zero]
      · have hba : ¬ E b = E a := fun heq => h heq.symm
        rw [if_neg h, if_neg hba]
        have hP_entry : star (P_tilde b a) = P_tilde a b := by
          have h1 := congrArg (fun M : Register N => M a b) hP_sa
          simpa [Matrix.star_eq_conjTranspose] using h1
        rw [Complex.star_def, map_div₀, map_mul, map_neg, Complex.conj_I, neg_neg,
          ← Complex.star_def, hP_entry, Complex.star_def, Complex.conj_ofReal]
        have hden : ((E a - E b : ℝ) : ℂ) = -((E b - E a : ℝ) : ℂ) := by push_cast; ring
        rw [hden, div_neg, neg_mul]; ring
    rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, hK_sa, mul_assoc]⟩

theorem katoOffDiagGenerator_eq_basisKatoGenerator {N : ℕ} (H P : selfAdjoint (Register N)) :
    katoOffDiagGenerator H P =
      basisKatoGenerator (hermitianEigenbasisUnitary H.2.isHermitian)
        H.2.isHermitian.eigenvalues P := rfl

/-- Directional Kato expectation-shift functional for a saddle pair `(U, ψ)` in frame `(V, E)`. -/
def katoModeSlope {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (P : selfAdjoint (Register N)) (U : Register N) (ψ : StateSpace N) : ℝ :=
  let K := (basisKatoGenerator V E P).val
  (inner ℂ (matAct U ψ) (matAct K (matAct U ψ))).re - (inner ℂ ψ (matAct K ψ)).re

/-- Outer-product projector `|u⟩⟨u|` on `Register N`. -/
def rankOneProj {N : ℕ} (u : StateSpace N) : Register N :=
  fun a b => u.ofLp a * star (u.ofLp b)

private theorem rankOneProj_isSelfAdjoint {N : ℕ} (u : StateSpace N) :
    IsSelfAdjoint (rankOneProj u) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext a b
  simp [rankOneProj, Matrix.conjTranspose_apply, mul_comm]

/-- Self-adjoint saddle sensitivity operator `Δρ(u, v) = |u⟩⟨u| - |v⟩⟨v|`. -/
def diffProjector {N : ℕ} (u v : StateSpace N) : selfAdjoint (Register N) :=
  ⟨rankOneProj u - rankOneProj v, (rankOneProj_isSelfAdjoint u).sub (rankOneProj_isSelfAdjoint v)⟩

private def addRealSmulSelfAdjoint {N : ℕ} (A B : selfAdjoint (Register N)) (lam : ℝ) :
    selfAdjoint (Register N) :=
  ⟨A.val + (lam : ℂ) • B.val, by
    rw [selfAdjoint.mem_iff, star_add, star_smul, A.2.star_eq, B.2.star_eq]
    simp⟩

private def spectralModelHamiltonian {N : ℕ} (V : UGroup N) (E : Config N → ℝ) :
    selfAdjoint (Register N) :=
  ⟨V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val, by
    rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star]
    have hd : star (Matrix.diagonal (Complex.ofReal ∘ E)) = Matrix.diagonal (Complex.ofReal ∘ E) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      congr 1; funext a; simp
    rw [hd, mul_assoc]⟩

private def commutatorSelfAdjoint {N : ℕ} (S H : selfAdjoint (Register N)) :
    selfAdjoint (Register N) :=
  ⟨Complex.I • (S.val * H.val - H.val * S.val), by
    rw [selfAdjoint.mem_iff, star_smul, star_sub, star_mul, star_mul, S.2.star_eq, H.2.star_eq]
    simp only [Complex.star_def, Complex.conj_I, neg_smul, smul_sub]
    abel⟩

private theorem selfAdjoint_entry_symm {N : ℕ} (M : selfAdjoint (Register N)) (a b : Config N) :
    M.val b a = star (M.val a b) := by
  have h := congrArg (fun X : Register N => X b a) M.2.star_eq
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using h.symm

private theorem matAct_rankOneProj {N : ℕ} (u ψ : StateSpace N) :
    matAct (rankOneProj u) ψ = (inner ℂ u ψ) • u := by
  ext a
  simp only [matAct, Matrix.mulVec, dotProduct, rankOneProj, WithLp.ofLp_toLp,
    PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply, Complex.star_def]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

private theorem inner_matAct_eq_trace_mul_rankOneProj {N : ℕ} (K : Register N) (u : StateSpace N) :
    inner ℂ u (matAct K u) = Matrix.trace (K * rankOneProj u) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, matAct, Matrix.mulVec,
    dotProduct, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOneProj, Complex.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  change (∑ b : Config N, K a b * u.ofLp b) * (starRingEnd ℂ) (u.ofLp a) =
    ∑ b : Config N, K a b * (u.ofLp b * (starRingEnd ℂ) (u.ofLp a))
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

private theorem trace_mul_diffProjector_eq {N : ℕ} (K : Register N) (u v : StateSpace N) :
    Matrix.trace (K * (diffProjector u v).val) =
      inner ℂ u (matAct K u) - inner ℂ v (matAct K v) := by
  change Matrix.trace (K * (rankOneProj u - rankOneProj v)) = _
  rw [Matrix.mul_sub, Matrix.trace_sub, inner_matAct_eq_trace_mul_rankOneProj,
    inner_matAct_eq_trace_mul_rankOneProj]

private theorem conj_rankOneProj {N : ℕ} (V : UGroup N) (u : StateSpace N) :
    star V.val * rankOneProj u * V.val = rankOneProj (matAct (star V.val) u) := by
  ext a b
  simp only [Matrix.mul_apply, rankOneProj, matAct, Matrix.mulVec, dotProduct,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  change (∑ d : Config N, (∑ c : Config N, star (V.val c a) * (u.ofLp c * star (u.ofLp d))) * V.val d b) =
    (∑ c : Config N, star (V.val c a) * u.ofLp c) *
      star (∑ d : Config N, star (V.val d b) * u.ofLp d)
  rw [star_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [star_mul', star_star]
  ring

/-- Every projective spectral unitary `U_θ = projectiveSpectralMatrix e V θ` produces a saddle
sensitivity operator `Δρ(U_θ ψ, ψ)` whose `V`-diagonal entries vanish identically. -/
theorem spectralProjective_diffProjector_diag_zero {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (θ : Fin d → UnitAddCircle)
    (ψ : StateSpace N) (a : Config N) :
    let U_θ := projectiveSpectralMatrix e V θ
    (star V.val * (diffProjector (matAct U_θ ψ) ψ).val * V.val) a a = 0 := by
  intro U_θ
  let d_fn : Config N → ℂ := fun q => fourier 1 (RHTower.zeroAnchoredPhase d θ (e q))
  have hd_norm (q : Config N) : ‖d_fn q‖ = 1 := fourier_one_norm_eq_one _
  have hU_eq : U_θ = V.val * Matrix.diagonal d_fn * star V.val := rfl
  let φ₀ := matAct (star V.val) ψ
  have hφ₁ : matAct (star V.val) (matAct U_θ ψ) = matAct (Matrix.diagonal d_fn) φ₀ := by
    rw [← matAct_mul_mc]
    have hmul : star V.val * U_θ = Matrix.diagonal d_fn * star V.val := by
      rw [hU_eq]
      calc star V.val * (V.val * Matrix.diagonal d_fn * star V.val)
          = (star V.val * V.val) * Matrix.diagonal d_fn * star V.val := by simp only [mul_assoc]
        _ = Matrix.diagonal d_fn * star V.val := by rw [(Unitary.mem_iff.mp V.2).1, one_mul]
    rw [hmul, matAct_mul_mc]
  change (star V.val * (rankOneProj (matAct U_θ ψ) - rankOneProj ψ) * V.val) a a = 0
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, conj_rankOneProj, conj_rankOneProj, hφ₁]
  have hphi_eq : (matAct (star V.val) ψ).ofLp a = φ₀.ofLp a := rfl
  rw [rankOneProj, rankOneProj, hphi_eq]
  have hdiag_act : (matAct (Matrix.diagonal d_fn) φ₀).ofLp a = d_fn a * φ₀.ofLp a :=
    Matrix.mulVec_diagonal d_fn φ₀.ofLp a
  rw [hdiag_act, star_mul']
  have h1 : d_fn a * star (d_fn a) = 1 := by
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      hd_norm a, one_pow, Complex.ofReal_one]
  linear_combination (φ₀.ofLp a * star (φ₀.ofLp a)) * h1

private theorem basisKatoGenerator_commutator_realizes {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (hsimple : Function.Injective E) (S : selfAdjoint (Register N))
    (hdiag0 : ∀ a : Config N, (star V.val * S.val * V.val) a a = 0) :
    let H_VE := spectralModelHamiltonian V E
    basisKatoGenerator V E (commutatorSelfAdjoint S H_VE) = S := by
  intro H_VE
  refine Subtype.ext ?_
  have hV1 : star V.val * V.val = 1 := (Unitary.mem_iff.mp V.2).1
  have hV2 : V.val * star V.val = 1 := (Unitary.mem_iff.mp V.2).2
  let S_tilde : Register N := star V.val * S.val * V.val
  let D_E : Register N := Matrix.diagonal (Complex.ofReal ∘ E)
  have hP_tilde : star V.val * (commutatorSelfAdjoint S H_VE).val * V.val =
      Complex.I • (S_tilde * D_E - D_E * S_tilde) := by
    change star V.val * (Complex.I • (S.val * (V.val * D_E * star V.val) -
      (V.val * D_E * star V.val) * S.val)) * V.val = _
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    have hterm1 : star V.val * (S.val * (V.val * D_E * star V.val)) * V.val = S_tilde * D_E := by
      calc star V.val * (S.val * (V.val * D_E * star V.val)) * V.val
          = (star V.val * S.val * V.val) * D_E * (star V.val * V.val) := by simp only [mul_assoc]
        _ = S_tilde * D_E := by rw [hV1, mul_one]
    have hterm2 : star V.val * ((V.val * D_E * star V.val) * S.val) * V.val = D_E * S_tilde := by
      calc star V.val * ((V.val * D_E * star V.val) * S.val) * V.val
          = (star V.val * V.val) * D_E * (star V.val * S.val * V.val) := by simp only [mul_assoc]
        _ = D_E * S_tilde := by rw [hV1, one_mul]
    rw [hterm1, hterm2]
  have hcore : basisOffDiagCore V E (commutatorSelfAdjoint S H_VE) = S_tilde := by
    ext a b
    change (if E b = E a then 0
      else -Complex.I * (star V.val * (commutatorSelfAdjoint S H_VE).val * V.val) a b /
        ((E b - E a : ℝ) : ℂ)) = S_tilde a b
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl]; exact (hdiag0 a).symm
    · have hE_ne : E b ≠ E a := fun heq => hab (hsimple heq.symm)
      have hdiff_ne : ((E b - E a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hE_ne
      rw [if_neg hE_ne, hP_tilde]
      simp only [D_E, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Function.comp_apply, smul_eq_mul]
      calc -Complex.I * (Complex.I * (S_tilde a b * (E b : ℂ) - (E a : ℂ) * S_tilde a b)) /
              ((E b - E a : ℝ) : ℂ)
          = -(Complex.I * Complex.I) * S_tilde a b *
              (((E b : ℂ) - (E a : ℂ)) / ((E b - E a : ℝ) : ℂ)) := by ring
        _ = S_tilde a b := by
            rw [Complex.I_mul_I,
              show (E b : ℂ) - (E a : ℂ) = ((E b - E a : ℝ) : ℂ) by push_cast; ring,
              div_self hdiff_ne]
            ring
  change V.val * basisOffDiagCore V E (commutatorSelfAdjoint S H_VE) * star V.val = S.val
  rw [hcore]
  calc V.val * (star V.val * S.val * V.val) * star V.val
      = (V.val * star V.val) * S.val * (V.val * star V.val) := by simp only [mul_assoc]
    _ = S.val := by rw [hV2, one_mul, mul_one]

/-- Exact Riesz realization of `Δρ(U_θ ψ, ψ)` as a Kato off-diagonal generator under simple
spectrum: `P_⋆ = i [Δρ(U_θ ψ, ψ), V diag(E) V*]` satisfies
`basisKatoGenerator V E P_⋆ = Δρ(U_θ ψ, ψ)` and achieves Kato slope
`2 * (1 - ‖⟨ψ, U_θ ψ⟩‖²)` for every unit state `ψ`. -/
theorem exists_basisKatoGenerator_eq_diffProjector {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (E : Config N → ℝ)
    (hsimple : Function.Injective E) (θ : Fin d → UnitAddCircle)
    {ψ : StateSpace N} (hψ : ‖ψ‖ = 1) :
    let U_θ := projectiveSpectralMatrix e V θ
    let H_VE : Register N := V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val
    ∃ P_star : selfAdjoint (Register N),
      P_star.val = Complex.I • ((diffProjector (matAct U_θ ψ) ψ).val * H_VE -
        H_VE * (diffProjector (matAct U_θ ψ) ψ).val) ∧
      basisKatoGenerator V E P_star = diffProjector (matAct U_θ ψ) ψ ∧
      katoModeSlope V E P_star U_θ ψ = 2 * (1 - ‖inner ℂ ψ (matAct U_θ ψ)‖ ^ 2) := by
  intro U_θ H_VE
  let P_star := commutatorSelfAdjoint (diffProjector (matAct U_θ ψ) ψ) (spectralModelHamiltonian V E)
  have hK_eq : basisKatoGenerator V E P_star = diffProjector (matAct U_θ ψ) ψ :=
    basisKatoGenerator_commutator_realizes V E hsimple (diffProjector (matAct U_θ ψ) ψ)
      (spectralProjective_diffProjector_diag_zero e V θ ψ)
  refine ⟨P_star, rfl, hK_eq, ?_⟩
  unfold katoModeSlope
  rw [hK_eq]
  let u := matAct U_θ ψ
  have hu_norm : ‖u‖ = 1 :=
    (norm_matAct_unitary_mc (projectiveSpectralMatrix_mem_unitary_mc e V θ) ψ).trans hψ
  have hu_inner : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu_norm]; simp
  have hψ_inner : inner ℂ ψ ψ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hsub_act (x : StateSpace N) :
      matAct (diffProjector u ψ).val x = (inner ℂ u x) • u - (inner ℂ ψ x) • ψ := by
    change matAct (rankOneProj u - rankOneProj ψ) x = _
    have h1 : matAct (rankOneProj u - rankOneProj ψ) x =
        matAct (rankOneProj u) x - matAct (rankOneProj ψ) x := by
      ext a; simp [matAct, Matrix.sub_mulVec]
    rw [h1, matAct_rankOneProj, matAct_rankOneProj]
  have hprod_norm : inner ℂ ψ u * inner ℂ u ψ = ((‖inner ℂ ψ u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm u ψ, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have term₁ : inner ℂ u (matAct (diffProjector u ψ).val u) =
      1 - ((‖inner ℂ ψ u‖ ^ 2 : ℝ) : ℂ) := by
    rw [hsub_act u, inner_sub_right, inner_smul_right, inner_smul_right, hu_inner, mul_one,
      hprod_norm]
  have term₂ : inner ℂ ψ (matAct (diffProjector u ψ).val ψ) =
      ((‖inner ℂ ψ u‖ ^ 2 : ℝ) : ℂ) - 1 := by
    rw [hsub_act ψ, inner_sub_right, inner_smul_right, inner_smul_right, hψ_inner, mul_one,
      mul_comm, hprod_norm]
  change (inner ℂ u (matAct (diffProjector u ψ).val u)).re -
    (inner ℂ ψ (matAct (diffProjector u ψ).val ψ)).re = 2 * (1 - ‖inner ℂ ψ u‖ ^ 2)
  rw [term₁, term₂]
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  ring

/-- Exact operator characterization of antiparallel Kato saddle slopes across full
`selfAdjoint (Register N)`: under simple spectrum of `E`, two projective spectral saddles
`(U₁, ψ₁)` and `(U₂, ψ₂)` satisfy `ℓ₁(P) + λ * ℓ₂(P) = 0` for all `P` (`λ > 0`) if and only if
`Δρ(U₁ ψ₁, ψ₁) + λ • Δρ(U₂ ψ₂, ψ₂) = 0`. -/
theorem kato_bipolar_antiparallel_iff_diffProjector {N d : ℕ}
    (e : Config N ≃ Fin (d + 1)) (V : UGroup N) (E : Config N → ℝ)
    (hsimple : Function.Injective E)
    (θ₁ θ₂ : Fin d → UnitAddCircle) (ψ₁ ψ₂ : StateSpace N)
    {lam : ℝ} (_hlam : 0 < lam) :
    let U₁ := projectiveSpectralMatrix e V θ₁
    let U₂ := projectiveSpectralMatrix e V θ₂
    (∀ P : selfAdjoint (Register N),
      katoModeSlope V E P U₁ ψ₁ + lam * katoModeSlope V E P U₂ ψ₂ = 0) ↔
    (diffProjector (matAct U₁ ψ₁) ψ₁).val +
      (lam : ℂ) • (diffProjector (matAct U₂ ψ₂) ψ₂).val = 0 := by
  intro U₁ U₂
  let Δ₁ := diffProjector (matAct U₁ ψ₁) ψ₁
  let Δ₂ := diffProjector (matAct U₂ ψ₂) ψ₂
  let S := addRealSmulSelfAdjoint Δ₁ Δ₂ lam
  have hS_val : S.val = Δ₁.val + (lam : ℂ) • Δ₂.val := rfl
  have htrace_comb (P : selfAdjoint (Register N)) :
      katoModeSlope V E P U₁ ψ₁ + lam * katoModeSlope V E P U₂ ψ₂ =
        (Matrix.trace ((basisKatoGenerator V E P).val * S.val)).re := by
    rw [hS_val, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      trace_mul_diffProjector_eq, trace_mul_diffProjector_eq]
    simp only [katoModeSlope, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, smul_eq_mul]
  constructor
  · intro hall
    have hdiagS (a : Config N) : (star V.val * S.val * V.val) a a = 0 := by
      rw [hS_val, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.add_apply, Matrix.smul_apply,
        spectralProjective_diffProjector_diag_zero e V θ₁ ψ₁ a,
        spectralProjective_diffProjector_diag_zero e V θ₂ ψ₂ a]
      simp
    let P_S := commutatorSelfAdjoint S (spectralModelHamiltonian V E)
    have hK_S : basisKatoGenerator V E P_S = S :=
      basisKatoGenerator_commutator_realizes V E hsimple S hdiagS
    have htr0 : (Matrix.trace (S.val * S.val)).re = 0 := by
      have h := hall P_S
      rw [htrace_comb P_S, hK_S] at h
      exact h
    have hhs : (Matrix.trace (S.val * S.val)).re =
        ∑ a : Config N, ∑ b : Config N, ‖S.val a b‖ ^ 2 := by
      rw [Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [selfAdjoint_entry_symm S a b, mul_comm, Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hhs] at htr0
    have hall_a := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg ‖S.val a b‖)).mp htr0
    rw [← hS_val]
    ext a b
    have hall_b := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖S.val a b‖)).mp
      (hall_a a (Finset.mem_univ a)) b (Finset.mem_univ b)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hall_b)
  · intro hzero P
    rw [htrace_comb P, hS_val, hzero, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

/-- Two saddles sharing the same singular vector `ψ` (`‖ψ‖ = 1`) cannot have antiparallel Kato
sensitivity operators unless both are stationary eigenmodes (`‖⟨ψ, U₁ ψ⟩‖ = ‖⟨ψ, U₂ ψ⟩‖ = 1`). -/
theorem no_bipolar_antiparallel_same_state {N : ℕ}
    {U₁ U₂ : Register N} (hU₁ : U₁ ∈ unitary (Register N)) (hU₂ : U₂ ∈ unitary (Register N))
    {ψ : StateSpace N} (hψ : ‖ψ‖ = 1) {lam : ℝ} (hlam : 0 < lam)
    (hanti : (diffProjector (matAct U₁ ψ) ψ).val +
      (lam : ℂ) • (diffProjector (matAct U₂ ψ) ψ).val = 0) :
    ‖inner ℂ ψ (matAct U₁ ψ)‖ = 1 ∧ ‖inner ℂ ψ (matAct U₂ ψ)‖ = 1 := by
  have hunorm₁ : ‖matAct U₁ ψ‖ = 1 := (norm_matAct_unitary_mc hU₁ ψ).trans hψ
  have hunorm₂ : ‖matAct U₂ ψ‖ = 1 := (norm_matAct_unitary_mc hU₂ ψ).trans hψ
  have hle₁ : ‖inner ℂ ψ (matAct U₁ ψ)‖ ^ 2 ≤ 1 := by
    have h := (norm_inner_le_norm (𝕜 := ℂ) ψ (matAct U₁ ψ)).trans_eq (by rw [hψ, hunorm₁, one_mul])
    nlinarith only [h, norm_nonneg (inner ℂ ψ (matAct U₁ ψ))]
  have hle₂ : ‖inner ℂ ψ (matAct U₂ ψ)‖ ^ 2 ≤ 1 := by
    have h := (norm_inner_le_norm (𝕜 := ℂ) ψ (matAct U₂ ψ)).trans_eq (by rw [hψ, hunorm₂, one_mul])
    nlinarith only [h, norm_nonneg (inner ℂ ψ (matAct U₂ ψ))]
  have hψ_inner : inner ℂ ψ ψ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hexp {U : Register N} :
      inner ℂ ψ (matAct (diffProjector (matAct U ψ) ψ).val ψ) =
        ((‖inner ℂ ψ (matAct U ψ)‖ ^ 2 : ℝ) : ℂ) - 1 := by
    have hsub : matAct (diffProjector (matAct U ψ) ψ).val ψ =
        (inner ℂ (matAct U ψ) ψ) • matAct U ψ - (inner ℂ ψ ψ) • ψ := by
      change matAct (rankOneProj (matAct U ψ) - rankOneProj ψ) ψ = _
      have h1 : matAct (rankOneProj (matAct U ψ) - rankOneProj ψ) ψ =
          matAct (rankOneProj (matAct U ψ)) ψ - matAct (rankOneProj ψ) ψ := by
        ext a; simp [matAct, Matrix.sub_mulVec]
      rw [h1, matAct_rankOneProj, matAct_rankOneProj]
    rw [hsub, inner_sub_right, inner_smul_right, inner_smul_right, hψ_inner, mul_one,
      ← inner_conj_symm (matAct U ψ) ψ, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have hact0 : inner ℂ ψ (matAct ((diffProjector (matAct U₁ ψ) ψ).val +
      (lam : ℂ) • (diffProjector (matAct U₂ ψ) ψ).val) ψ) = 0 := by
    rw [hanti]
    have hz : matAct (0 : Register N) ψ = 0 := by ext a; simp [matAct]
    rw [hz, inner_zero_right]
  have hact_split : matAct ((diffProjector (matAct U₁ ψ) ψ).val +
      (lam : ℂ) • (diffProjector (matAct U₂ ψ) ψ).val) ψ =
      matAct (diffProjector (matAct U₁ ψ) ψ).val ψ +
        (lam : ℂ) • matAct (diffProjector (matAct U₂ ψ) ψ).val ψ := by
    ext a; simp [matAct, Matrix.add_mulVec, Matrix.smul_mulVec]
  rw [hact_split, inner_add_right, inner_smul_right, hexp, hexp] at hact0
  have hre0 := congrArg Complex.re hact0
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at hre0
  have heq₁ : ‖inner ℂ ψ (matAct U₁ ψ)‖ ^ 2 = 1 := by nlinarith only [hle₁, hle₂, hlam, hre0]
  have heq₂ : ‖inner ℂ ψ (matAct U₂ ψ)‖ ^ 2 = 1 := by nlinarith only [hle₁, hle₂, hlam, hre0]
  exact ⟨by nlinarith only [heq₁, norm_nonneg (inner ℂ ψ (matAct U₁ ψ))],
         by nlinarith only [heq₂, norm_nonneg (inner ℂ ψ (matAct U₂ ψ))]⟩

private theorem norm_basisKatoGenerator_le {N : ℕ} (V : UGroup N) (E : Config N → ℝ)
    (P : selfAdjoint (Register N)) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ a b : Config N, a ≠ b → Δ ≤ |E b - E a|) :
    ‖(basisKatoGenerator V E P).val‖ ≤ Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ := by
  let P_tilde : Register N := star V.val * P.val * V.val
  let K_tilde : Register N := basisOffDiagCore V E P
  have hP_norm : ‖P_tilde‖ = ‖P.val‖ := by
    have h1 := l2_opNorm_unitary_conj_eq (V := star V.val) (Unitary.star_mem V.2) P.val
    simpa only [star_star] using h1
  have hK_norm : ‖(basisKatoGenerator V E P).val‖ = ‖K_tilde‖ :=
    l2_opNorm_unitary_conj_eq (V := V.val) V.2 K_tilde
  rw [hK_norm]
  have hrow_sq (a : Config N) (ψ : StateSpace N) :
      ‖(matAct K_tilde ψ).ofLp a‖ ^ 2 ≤ (∑ b : Config N, ‖K_tilde a b‖ ^ 2) * ‖ψ‖ ^ 2 := by
    have hact : (matAct K_tilde ψ).ofLp a = ∑ b : Config N, K_tilde a b * ψ.ofLp b := by
      simp [matAct, Matrix.mulVec, dotProduct]
    rw [hact, EuclideanSpace.norm_sq_eq]
    calc ‖∑ b : Config N, K_tilde a b * ψ.ofLp b‖ ^ 2
        ≤ (∑ b : Config N, ‖K_tilde a b * ψ.ofLp b‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = (∑ b : Config N, ‖K_tilde a b‖ * ‖ψ.ofLp b‖) ^ 2 := by simp_rw [norm_mul]
      _ ≤ (∑ b : Config N, ‖K_tilde a b‖ ^ 2) * (∑ b : Config N, ‖ψ.ofLp b‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hcol_sum : (∑ a : Config N, ∑ b : Config N, ‖K_tilde a b‖ ^ 2) ≤
      ((2 : ℝ) ^ N * ‖P.val‖ ^ 2) / Δ ^ 2 := by
    have hpt (a b : Config N) : ‖K_tilde a b‖ ^ 2 ≤ ‖P_tilde a b‖ ^ 2 / Δ ^ 2 := by
      change ‖if E b = E a then 0 else -Complex.I * P_tilde a b / ((E b - E a : ℝ) : ℂ)‖ ^ 2 ≤ _
      by_cases hE : E b = E a
      · rw [if_pos hE, norm_zero, zero_pow two_pos.ne']
        exact div_nonneg (sq_nonneg _) (sq_nonneg _)
      · have hab : a ≠ b := fun heq => hE (congrArg E heq.symm)
        rw [if_neg hE, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, div_pow]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hΔ 2)
          (pow_le_pow_left₀ hΔ.le (hgap a b hab) 2)
    have hhs_P : (∑ a : Config N, ∑ b : Config N, ‖P_tilde a b‖ ^ 2) ≤
        (2 : ℝ) ^ N * ‖P.val‖ ^ 2 := by
      rw [Finset.sum_comm]
      have hcol (b : Config N) : (∑ a : Config N, ‖P_tilde a b‖ ^ 2) ≤ ‖P.val‖ ^ 2 := by
        let e_b : StateSpace N := EuclideanSpace.single b 1
        have he_norm : ‖e_b‖ = 1 := by simp [e_b]
        have hle_act : ‖matAct P_tilde e_b‖ ≤ ‖P_tilde‖ * ‖e_b‖ := by
          rw [matAct_eq_clm_mc]
          simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
            (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) P_tilde).le_opNorm e_b
        have h1 := pow_le_pow_left₀ (norm_nonneg _) hle_act 2
        rw [hP_norm, he_norm, mul_one, EuclideanSpace.norm_sq_eq] at h1
        refine (le_of_eq ?_).trans h1
        refine Finset.sum_congr rfl fun a _ => ?_
        have happ : (matAct P_tilde e_b).ofLp a = P_tilde a b := by simp [matAct, e_b]
        rw [happ]
      calc (∑ b : Config N, ∑ a : Config N, ‖P_tilde a b‖ ^ 2)
          ≤ ∑ _b : Config N, ‖P.val‖ ^ 2 := Finset.sum_le_sum fun b _ => hcol b
        _ = (2 : ℝ) ^ N * ‖P.val‖ ^ 2 := by simp [Config, Finset.sum_const, nsmul_eq_mul]
    calc (∑ a : Config N, ∑ b : Config N, ‖K_tilde a b‖ ^ 2)
        ≤ ∑ a : Config N, ∑ b : Config N, ‖P_tilde a b‖ ^ 2 / Δ ^ 2 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = (∑ a : Config N, ∑ b : Config N, ‖P_tilde a b‖ ^ 2) / Δ ^ 2 := by
          simp_rw [← Finset.sum_div]
      _ ≤ ((2 : ℝ) ^ N * ‖P.val‖ ^ 2) / Δ ^ 2 := div_le_div_of_nonneg_right hhs_P (sq_nonneg Δ)
  have hC_nn : 0 ≤ Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hΔ.le
  rw [← Matrix.l2_opNorm_toEuclideanCLM (n := Config N) (𝕜 := ℂ)]
  refine (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) K_tilde).opNorm_le_bound hC_nn fun ψ => ?_
  rw [← matAct_eq_clm_mc]
  have hsq : ‖matAct K_tilde ψ‖ ^ 2 ≤ (Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ * ‖ψ‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc (∑ a : Config N, ‖(matAct K_tilde ψ).ofLp a‖ ^ 2)
        ≤ ∑ a : Config N, (∑ b : Config N, ‖K_tilde a b‖ ^ 2) * ‖ψ‖ ^ 2 :=
          Finset.sum_le_sum fun a _ => hrow_sq a ψ
      _ = (∑ a : Config N, ∑ b : Config N, ‖K_tilde a b‖ ^ 2) * ‖ψ‖ ^ 2 :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (((2 : ℝ) ^ N * ‖P.val‖ ^ 2) / Δ ^ 2) * ‖ψ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcol_sum (sq_nonneg _)
      _ = (Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ * ‖ψ‖) ^ 2 := by
          rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (pow_nonneg two_pos.le N), mul_div_right_comm]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC_nn (norm_nonneg _))).mp hsq

/-- Multi-saddle Kato coercive stability ball: if a perturbation `P` (`P ≠ 0`) achieves uniform
signed Kato slope `≥ c₀ > 0` across a finite family `(U₀ m, ψ m)` (`m : Fin S`) at spectral gap
`min_{a ≠ b} |E b - E a| ≥ Δ > 0`, then every rotated saddle along `e^{-i u K}` retains slope
`≥ c₀ / 2` for all `|u| ≤ c₀ * Δ² / (4 * 2^N * ‖P‖²)`. -/
theorem multiSaddle_kato_coercive_ball {N S : ℕ} (V : UGroup N) (E : Config N → ℝ)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgap : ∀ a b : Config N, a ≠ b → Δ ≤ |E b - E a|)
    (P : selfAdjoint (Register N)) (hP_ne : P.val ≠ 0)
    (U₀ : Fin S → Register N) (hU₀ : ∀ m, ‖U₀ m‖ ≤ 1)
    (ψ : Fin S → StateSpace N) (hψ : ∀ m, ‖ψ m‖ ≤ 1)
    (sgn : Bool) {c₀ : ℝ} (_hc₀ : 0 < c₀)
    (hinit : ∀ m : Fin S, c₀ ≤ (if sgn then 1 else -1) * katoModeSlope V E P (U₀ m) (ψ m))
    {u : ℝ} (hu : |u| ≤ c₀ * Δ ^ 2 / (4 * (2 : ℝ) ^ N * ‖P.val‖ ^ 2)) (m : Fin S) :
    let K := basisKatoGenerator V E P
    let U_u := unitaryEvolution K.val u * U₀ m * star (unitaryEvolution K.val u)
    c₀ / 2 ≤ (if sgn then 1 else -1) *
      ((inner ℂ (matAct U_u (ψ m)) (matAct K.val (matAct U_u (ψ m)))).re -
        (inner ℂ (ψ m) (matAct K.val (ψ m))).re) := by
  intro K U_u
  have hP_pos : 0 < ‖P.val‖ := norm_pos_iff.mpr hP_ne
  have hK_le : ‖K.val‖ ≤ Real.sqrt ((2 : ℝ) ^ N) * ‖P.val‖ / Δ :=
    norm_basisKatoGenerator_le V E P hΔ hgap
  have hK_sq : ‖K.val‖ ^ 2 ≤ (2 : ℝ) ^ N * ‖P.val‖ ^ 2 / Δ ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg K.val) hK_le 2
    rw [div_pow, mul_pow, Real.sq_sqrt (pow_nonneg two_pos.le N)] at h1
    exact h1
  have hdrift_le : 2 * ‖K.val‖ ^ 2 * |u| ≤ c₀ / 2 := by
    calc 2 * ‖K.val‖ ^ 2 * |u|
        ≤ 2 * ((2 : ℝ) ^ N * ‖P.val‖ ^ 2 / Δ ^ 2) *
            (c₀ * Δ ^ 2 / (4 * (2 : ℝ) ^ N * ‖P.val‖ ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hK_sq two_pos.le) hu (abs_nonneg u) (by positivity)
      _ = c₀ / 2 := by field_simp [hΔ.ne', hP_pos.ne']; ring
  have hlip := transverse_mode_slope_lipschitz (hU₀ m) K (hψ m) u
  change |((inner ℂ (matAct U_u (ψ m)) (matAct K.val (matAct U_u (ψ m)))).re -
      (inner ℂ (ψ m) (matAct K.val (ψ m))).re) - katoModeSlope V E P (U₀ m) (ψ m)| ≤
    2 * ‖K.val‖ ^ 2 * |u| at hlip
  have hbd := abs_le.mp (hlip.trans hdrift_le)
  have hm0 := hinit m
  cases sgn
  · simp only [Bool.false_eq_true, ↓reduceIte] at hm0 ⊢
    linarith only [hm0, hbd.2]
  · simp only [↓reduceIte] at hm0 ⊢
    linarith only [hm0, hbd.1]

/-- First-order `2`-local Kato blind spot at Hamming distance `3` on the `(12 N - 9)`-dimensional
chain space (`n ≥ 1`, `N = n + 2 ≥ 3`): for an explicit simple-spectrum diagonal base `H₀`
(`V = 1`) and Hamming-distance-`3` cat state `ψ_cat = (|x₀⟩ + |x₁⟩) / √2`, there is a projective
spectral unitary `U_cat` with `⟨ψ_cat, U_cat ψ_cat⟩ = 0` (`‖⟨ψ_cat, U_cat ψ_cat⟩‖ = 0 < 1`) whose
first-order Kato mode slope vanishes identically across **every** `1`D chain Hamiltonian
`pathHamiltonian u` (`u : PathShell n`). -/
theorem chainPauli_kato_blindSpot_hammingThree {n : ℕ} (hn : 1 ≤ n) :
    let N := n + 2
    let E_diag : Config N → ℝ := fun x => ((Fintype.equivFin (Config N) x).val : ℝ)
    let V_id : UGroup N := 1
    let x₀ : Config N := fun _ => false
    let x₁ : Config N := fun s => decide (s.val < 3)
    let ψ_cat : StateSpace N :=
      ((1 / Real.sqrt 2 : ℝ) : ℂ) • (EuclideanSpace.single x₀ 1 + EuclideanSpace.single x₁ 1)
    Function.Injective E_diag ∧
    (Finset.univ.filter fun s : Fin N => x₀ s ≠ x₁ s).card = 3 ∧
    ‖ψ_cat‖ = 1 ∧
    ∃ (e_enum : Config N ≃ Fin ((2 ^ N - 1) + 1)) (θ_cat : Fin (2 ^ N - 1) → UnitAddCircle),
      let U_cat := projectiveSpectralMatrix e_enum V_id θ_cat
      inner ℂ ψ_cat (matAct U_cat ψ_cat) = 0 ∧
      ∀ u : PathShell n,
        let P_u : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        katoModeSlope V_id E_diag P_u U_cat ψ_cat = 0 := by
  intro N E_diag V_id x₀ x₁ ψ_cat
  have hN3 : 3 ≤ N := by dsimp [N]; omega
  have hinj_E : Function.Injective E_diag :=
    fun x y h => (Fintype.equivFin (Config N)).injective (Fin.ext (Nat.cast_injective h))
  let s₀ : Fin N := ⟨0, by omega⟩
  let s₁ : Fin N := ⟨1, by omega⟩
  let s₂ : Fin N := ⟨2, by omega⟩
  have hfilter_eq : (Finset.univ.filter fun s : Fin N => x₀ s ≠ x₁ s) = {s₀, s₁, s₂} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, x₀, x₁]
    constructor
    · intro hne
      have hlt : s.val < 3 := by
        by_contra hge
        exact hne (by simp [hge])
      rcases (show s.val = 0 ∨ s.val = 1 ∨ s.val = 2 by omega) with h0 | h1 | h2
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Or.inl (Fin.ext h1))
      · exact Or.inr (Or.inr (Fin.ext h2))
    · rintro (rfl | rfl | rfl) <;> simp [s₀, s₁, s₂]
  have hcard3 : (Finset.univ.filter fun s : Fin N => x₀ s ≠ x₁ s).card = 3 := by
    rw [hfilter_eq]
    have h01 : s₀ ≠ s₁ := fun h => by have hv : (0 : ℕ) = 1 := congrArg Fin.val h; omega
    have h02 : s₀ ≠ s₂ := fun h => by have hv : (0 : ℕ) = 2 := congrArg Fin.val h; omega
    have h12 : s₁ ≠ s₂ := fun h => by have hv : (1 : ℕ) = 2 := congrArg Fin.val h; omega
    simp [h01, h02, h12]
  have hx₀₁_ne : x₀ ≠ x₁ := fun h => by
    have hs := congrFun h s₀
    simp [x₀, x₁, s₀] at hs
  have hψ_norm : ‖ψ_cat‖ = 1 := by
    have hsq : ‖ψ_cat‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hsum : (∑ x : Config N, ‖ψ_cat.ofLp x‖ ^ 2) =
          ‖ψ_cat.ofLp x₀‖ ^ 2 + ‖ψ_cat.ofLp x₁‖ ^ 2 := by
        rw [← Finset.sum_subset (Finset.subset_univ ({x₀, x₁} : Finset (Config N))),
          Finset.sum_pair hx₀₁_ne]
        intro x _ hx
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        simp [ψ_cat, hx.1, hx.2]
      rw [hsum]
      have hv0 : ψ_cat.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_cat, hx₀₁_ne]
      have hv1 : ψ_cat.ofLp x₁ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_cat, hx₀₁_ne.symm]
      rw [hv0, hv1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_pow, one_pow, Real.sq_sqrt two_pos.le]
      norm_num
    nlinarith only [hsq, norm_nonneg ψ_cat]
  let d := 2 ^ N - 1
  have hd_card : Fintype.card (Config N) = d + 1 := by
    simp only [Config, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hp : 0 < 2 ^ N := Nat.two_pow_pos N
    dsimp [d]; omega
  let e_raw : Config N ≃ Fin (d + 1) := (Fintype.equivFin (Config N)).trans (finCongr hd_card)
  let e_enum : Config N ≃ Fin (d + 1) := e_raw.trans (Equiv.swap (e_raw x₀) 0)
  have he_x₀ : e_enum x₀ = 0 := by simp [e_enum]
  have he_x₁_ne0 : e_enum x₁ ≠ 0 := fun h => hx₀₁_ne (e_enum.injective (he_x₀.trans h.symm))
  let θ_cat : Fin d → UnitAddCircle :=
    fun k => if e_enum.symm k.succ = x₁ then ((1 / 2 : ℝ) : UnitAddCircle) else 0
  let U_cat := projectiveSpectralMatrix e_enum V_id θ_cat
  have hdiag_U : U_cat = Matrix.diagonal
      (fun q => fourier 1 (RHTower.zeroAnchoredPhase d θ_cat (e_enum q))) := by
    change V_id.val * Matrix.diagonal _ * (V_id⁻¹).val = _
    have hV1 : V_id.val = 1 := rfl
    have hVinv1 : (V_id⁻¹).val = 1 := by simp [V_id]
    rw [hV1, hVinv1, one_mul, mul_one]
  have hd_x₀ : (fourier 1 (RHTower.zeroAnchoredPhase d θ_cat (e_enum x₀)) : ℂ) = 1 := by
    rw [he_x₀]
    change (fourier 1 (0 : UnitAddCircle) : ℂ) = 1
    rw [← QuotientAddGroup.mk_zero, fourier_coe_apply]
    simp
  have hd_x₁ : (fourier 1 (RHTower.zeroAnchoredPhase d θ_cat (e_enum x₁)) : ℂ) = -1 := by
    obtain ⟨k₁, hk₁⟩ := Fin.eq_succ_of_ne_zero he_x₁_ne0
    rw [hk₁]
    change (fourier 1 (θ_cat k₁) : ℂ) = -1
    have hsymm : e_enum.symm k₁.succ = x₁ := e_enum.injective (by rw [Equiv.apply_symm_apply, hk₁])
    dsimp only [θ_cat]
    rw [if_pos hsymm, fourier_coe_apply]
    have harg : 2 * ↑Real.pi * Complex.I * ↑(1 : ℤ) * ↑(1 / 2 : ℝ) / ↑(1 : ℝ) =
        ↑Real.pi * Complex.I := by push_cast; ring
    rw [harg, Complex.exp_pi_mul_I]
  let ψ_minus : StateSpace N :=
    ((1 / Real.sqrt 2 : ℝ) : ℂ) • (EuclideanSpace.single x₀ 1 - EuclideanSpace.single x₁ 1)
  have hact_cat : matAct U_cat ψ_cat = ψ_minus := by
    ext q
    rw [hdiag_U]
    simp only [matAct, Matrix.mulVec_diagonal]
    by_cases hq0 : q = x₀
    · subst hq0; simp [ψ_cat, ψ_minus, hx₀₁_ne, hd_x₀]
    · by_cases hq1 : q = x₁
      · subst hq1; simp [ψ_cat, ψ_minus, hx₀₁_ne.symm, hd_x₁]
      · simp [ψ_cat, ψ_minus, hq0, hq1]
  have hinner_zero : inner ℂ ψ_cat (matAct U_cat ψ_cat) = 0 := by
    rw [hact_cat]
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    rw [← Finset.sum_subset (Finset.subset_univ ({x₀, x₁} : Finset (Config N))),
      Finset.sum_pair hx₀₁_ne]
    · have hc0 : ψ_cat.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_cat, hx₀₁_ne]
      have hc1 : ψ_cat.ofLp x₁ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_cat, hx₀₁_ne.symm]
      have hm0 : ψ_minus.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_minus, hx₀₁_ne]
      have hm1 : ψ_minus.ofLp x₁ = -((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_minus, hx₀₁_ne.symm]
      rw [hc0, hc1, hm0, hm1]
      ring
    · intro q _ hq
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      simp [ψ_cat, hq.1, hq.2]
  have hpauli_zero (l : PathLabel n) (a b : Config N)
      (hab : (a = x₀ ∧ b = x₁) ∨ (a = x₁ ∧ b = x₀)) :
      finitePauliMatrix (pathWord l) a b = 0 := by
    have hdiff_s (s : Fin N) (hs : s.val < 3) : a s ≠ b s := by
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [x₀, x₁, hs]
    obtain ⟨t, ht_lt3, ht_none⟩ : ∃ t : Fin N, t.val < 3 ∧ pathWord l t = none := by
      rcases l with ⟨s, q⟩ | ⟨e, pq⟩
      · by_cases hs0 : s.val = 0
        · refine ⟨s₁, show (1 : ℕ) < 3 by omega, ?_⟩
          have hne : s₁ ≠ s := fun h => by
            have hv : (1 : ℕ) = s.val := congrArg Fin.val h; omega
          simp [pathWord, onsiteWord, hne]
        · refine ⟨s₀, show (0 : ℕ) < 3 by omega, ?_⟩
          have hne : s₀ ≠ s := fun h => by
            have hv : (0 : ℕ) = s.val := congrArg Fin.val h; omega
          simp [pathWord, onsiteWord, hne]
      · by_cases he0 : e.val = 0
        · refine ⟨s₂, show (2 : ℕ) < 3 by omega, ?_⟩
          have h1 : s₂ ≠ e.castSucc := fun h => by
            have hv : (2 : ℕ) = e.val := congrArg Fin.val h; omega
          have h2 : s₂ ≠ e.succ := fun h => by
            have hv : (2 : ℕ) = e.val + 1 := congrArg Fin.val h; omega
          simp [pathWord, couplingWord, h1, h2]
        · refine ⟨s₀, show (0 : ℕ) < 3 by omega, ?_⟩
          have h1 : s₀ ≠ e.castSucc := fun h => by
            have hv : (0 : ℕ) = e.val := congrArg Fin.val h; omega
          have h2 : s₀ ≠ e.succ := fun h => by
            have hv : (0 : ℕ) = e.val + 1 := congrArg Fin.val h; omega
          simp [pathWord, couplingWord, h1, h2]
    unfold finitePauliMatrix
    refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
    rw [ht_none]
    simp [boolPauliOptionEntry, boolPauliOption, hdiff_s t ht_lt3]
  refine ⟨hinj_E, hcard3, hψ_norm, e_enum, θ_cat, hinner_zero, fun u => ?_⟩
  let P_u : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  have hPu_zero (a b : Config N) (hab : (a = x₀ ∧ b = x₁) ∨ (a = x₁ ∧ b = x₀)) :
      P_u.val a b = 0 := by
    change pathHamiltonian u a b = 0
    rw [pathHamiltonian_eq_sum, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.smul_apply, hpauli_zero l a b hab, smul_zero]
  let K := (basisKatoGenerator V_id E_diag P_u).val
  have hK_zero (a b : Config N) (hab : (a = x₀ ∧ b = x₁) ∨ (a = x₁ ∧ b = x₀)) :
      K a b = 0 := by
    have hV1 : V_id.val = 1 := rfl
    have hK_eq : K = basisOffDiagCore V_id E_diag P_u := by
      change V_id.val * basisOffDiagCore V_id E_diag P_u * star V_id.val = _
      rw [hV1, star_one, one_mul, mul_one]
    rw [hK_eq]
    change (if E_diag b = E_diag a then 0
      else -Complex.I * (star V_id.val * P_u.val * V_id.val) a b /
        ((E_diag b - E_diag a : ℝ) : ℂ)) = 0
    rw [hV1, star_one, one_mul, mul_one, hPu_zero a b hab]
    split_ifs <;> simp
  unfold katoModeSlope
  have hre_eq : (inner ℂ (matAct U_cat ψ_cat) (matAct K (matAct U_cat ψ_cat))).re -
      (inner ℂ ψ_cat (matAct K ψ_cat)).re =
      (Matrix.trace (K * (diffProjector (matAct U_cat ψ_cat) ψ_cat).val)).re := by
    rw [trace_mul_diffProjector_eq, Complex.sub_re]
  change (inner ℂ (matAct U_cat ψ_cat) (matAct K (matAct U_cat ψ_cat))).re -
    (inner ℂ ψ_cat (matAct K ψ_cat)).re = 0
  rw [hre_eq, hact_cat]
  have htr_zero : Matrix.trace (K * (diffProjector ψ_minus ψ_cat).val) = 0 := by
    rw [Matrix.trace]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    change K a b * (rankOneProj ψ_minus b a - rankOneProj ψ_cat b a) = 0
    by_cases hb0 : b = x₀
    · subst hb0
      by_cases ha0 : a = x₀
      · subst ha0
        have hm0 : ψ_minus.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_minus, hx₀₁_ne]
        have hc0 : ψ_cat.ofLp x₀ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by simp [ψ_cat, hx₀₁_ne]
        simp [rankOneProj, hm0, hc0]
      · by_cases ha1 : a = x₁
        · subst ha1; rw [hK_zero x₁ x₀ (Or.inr ⟨rfl, rfl⟩), zero_mul]
        · simp [rankOneProj, ψ_minus, ψ_cat, ha0, ha1]
    · by_cases hb1 : b = x₁
      · subst hb1
        by_cases ha1 : a = x₁
        · subst ha1
          have hm1 : ψ_minus.ofLp x₁ = -((1 / Real.sqrt 2 : ℝ) : ℂ) := by
            simp [ψ_minus, hx₀₁_ne.symm]
          have hc1 : ψ_cat.ofLp x₁ = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
            simp [ψ_cat, hx₀₁_ne.symm]
          simp [rankOneProj, hm1, hc1]
        · by_cases ha0 : a = x₀
          · subst ha0; rw [hK_zero x₀ x₁ (Or.inl ⟨rfl, rfl⟩), zero_mul]
          · simp [rankOneProj, ψ_minus, ψ_cat, ha0, ha1]
      · simp [rankOneProj, ψ_minus, ψ_cat, hb0, hb1]
  rw [htr_zero, Complex.zero_re]

#print axioms lipschitz_collar_bipolarFree_diam_or_sep
#print axioms gaussian_bipolarFree_collar_anticoncentration
#print axioms measurePreserving_pi_gaussian_linearIsometryEquiv
#print axioms exists_linearIsometryEquiv_single_eq
#print axioms twoDim_shared_coercive_unit_of_det
#print axioms gaussian_rotatingDirection_chart_anticoncentration
#print axioms fixed_tenth_locking_of_rotatingDirection_charts
#print axioms generic_parallel_lines_avoid_collar_ties
#print axioms spectralProjective_diffProjector_diag_zero
#print axioms exists_basisKatoGenerator_eq_diffProjector
#print axioms kato_bipolar_antiparallel_iff_diffProjector
#print axioms no_bipolar_antiparallel_same_state
#print axioms multiSaddle_kato_coercive_ball
#print axioms chainPauli_kato_blindSpot_hammingThree

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau