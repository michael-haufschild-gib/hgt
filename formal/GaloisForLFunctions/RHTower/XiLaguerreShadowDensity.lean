import GaloisForLFunctions.RHTower.XiLaguerreShadow
import GaloisForLFunctions.RHTower.ZetaOffLineMomentExplicit
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# `Ξ` is Laguerre-positive and vertically monotone on more than half of the real line

The first Laguerre inequality `Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0` and the monotonicity of `y ↦ |Ξ(x+iy)|`
on `y ≥ 0` hold at every real `x` outside the shadow `S` of the off-line zeros
(`monotoneOn_laguerre_of_not_mem_xiShadow`).  A zero `ζ` of `Ξ` and its conjugate cast the same
shadow `(Re ζ − |Im ζ|, Re ζ + |Im ζ|)`, and by evenness a zero with `Re ζ < 0` shadows `[0, ∞)`
no more than its reflection does; so each off-line zero `ρ = ½ + iζ` of `ξ` with `Re ρ > ½` is
counted once, and

  `vol(S ∩ [0, V]) ≤ 2 Σ_{0 ≤ Im ρ ≤ V + ½} m(ρ)(Re ρ − ½)`   (`volume_xiShadow_inter_Icc_le_offLineMoment`).

An off-line moment bound `Σ_{0 < Im ρ ≤ V} m(ρ)(Re ρ − ½) ≤ μ V` gives, for all large `V`,

  `vol{x ∈ [0, V] : Laguerre and vertical monotonicity hold at x} ≥ (1 − 2μ) V − μ`

(`eventually_volume_laguerre_monotone_ge_of_moment`); with `μ = 21/100` this is `(29/50) V − 21/100`
(`eventually_volume_laguerre_monotone_ge`).  This is a density version of the Laguerre–Pólya
receiver, whose full form (`S = ∅`) is the Riemann hypothesis.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower.DeBruijn

noncomputable section

/-- A zero of `ξ` has multiplicity at least one. -/
theorem one_le_toNat_analyticOrderAt_xi {ρ : ℂ} (hρ : xi ρ = 0) :
    1 ≤ (analyticOrderAt xi ρ).toNat := by
  have hf := RHTower.xi_analyticOnNhd Set.univ
  have hf0 : xi 0 ≠ 0 := by simpa using xi_ne_zero_of_real 0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ne_top_of_ne_zero hf hf0 ρ)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact ((hf ρ (mem_univ _)).analyticOrderAt_eq_zero.mp (by rw [← hn]; rfl)) hρ
  rw [← hn, ENat.toNat_coe]
  omega

/-- Every point of the shadow in `[0, V]` lies in the shadow `(Im ρ − (Re ρ − ½), Im ρ + (Re ρ − ½))`
of a zero `ρ` of `ξ` with `½ < Re ρ < 1`, `0 ≤ Im ρ ≤ V + ½`. -/
theorem exists_boxZero_of_mem_xiShadow {V x : ℝ} (hx : x ∈ xiShadow ∩ Icc 0 V) :
    ∃ ρ ∈ boxFinsetLe (V + 1 / 2),
      x ∈ Ioo (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2)) := by
  obtain ⟨⟨ζ, hζ, hlt⟩, hx0, hxV⟩ := hx
  -- reflect to `Re ζ ≥ 0`
  obtain ⟨ζ₁, hζ₁, hlt₁, hre₁⟩ : ∃ ζ₁ : ℂ, riemannHeat 0 ζ₁ = 0 ∧
      (ζ₁.re - x) ^ 2 < ζ₁.im ^ 2 ∧ 0 ≤ ζ₁.re := by
    by_cases h : 0 ≤ ζ.re
    · exact ⟨ζ, hζ, hlt, h⟩
    · rw [not_le] at h
      refine ⟨-(starRingEnd ℂ ζ), ?_, ?_, ?_⟩
      · rw [riemannHeat_neg le_rfl, riemannHeat_conj le_rfl, hζ, map_zero]
      · simp only [Complex.neg_re, Complex.conj_re, Complex.neg_im, Complex.conj_im, neg_neg]
        have : (-ζ.re - x) ^ 2 ≤ (ζ.re - x) ^ 2 := by nlinarith
        linarith
      · simp only [Complex.neg_re, Complex.conj_re]
        linarith
  -- conjugate to `Im ζ < 0`
  obtain ⟨ζ₂, hζ₂, hlt₂, hre₂, him₂⟩ : ∃ ζ₂ : ℂ, riemannHeat 0 ζ₂ = 0 ∧
      (ζ₂.re - x) ^ 2 < ζ₂.im ^ 2 ∧ 0 ≤ ζ₂.re ∧ ζ₂.im < 0 := by
    have hne : ζ₁.im ≠ 0 := by
      intro h
      rw [h] at hlt₁
      nlinarith [sq_nonneg (ζ₁.re - x)]
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨ζ₁, hζ₁, hlt₁, hre₁, h⟩
    · refine ⟨starRingEnd ℂ ζ₁, ?_, ?_, ?_, ?_⟩
      · rw [riemannHeat_conj le_rfl, hζ₁, map_zero]
      · simpa using hlt₁
      · simpa using hre₁
      · simp only [Complex.conj_im]
        linarith
  have him2 : ζ₂.im ^ 2 ≤ 1 / 4 := by
    have h0 : cosTransform riemannKernelReal ζ₂ = 0 := by
      rw [cosTransform_riemannKernel, ← riemannHeat_zero]; exact hζ₂
    exact riemannKernel_zeros_im_sq_le ζ₂ h0
  have him2' : -(1 / 2) ≤ ζ₂.im := by nlinarith
  have h := sq_lt_sq.mp hlt₂
  rw [abs_of_neg him₂] at h
  have h' := abs_lt.mp h
  have hρ : xi (1 / 2 + I * ζ₂) = 0 := by rw [← riemannHeat_zero]; exact hζ₂
  have hρre : (1 / 2 + I * ζ₂).re = 1 / 2 - ζ₂.im := by simp; ring
  have hρim : (1 / 2 + I * ζ₂).im = ζ₂.re := by simp
  refine ⟨1 / 2 + I * ζ₂, ?_, ?_⟩
  · rw [mem_boxFinsetLe]
    refine ⟨by rw [hρre]; linarith, ?_, by rw [hρim]; exact hre₂, ?_, hρ⟩
    · by_contra hge
      exact xi_ne_zero_of_one_le_re (not_lt.mp hge) hρ
    · rw [hρim]
      linarith [h'.1, h'.2]
  · rw [hρre, hρim]
    constructor <;> linarith [h'.1, h'.2]

/-- **The shadow against the off-line first moment.** Each conjugate pair of off-line zeros is
counted once: `vol(S ∩ [0, V]) ≤ 2 Σ_{0 ≤ Im ρ ≤ V + ½} m(ρ)(Re ρ − ½)`. -/
theorem volume_xiShadow_inter_Icc_le_offLineMoment (V : ℝ) :
    volume (xiShadow ∩ Icc 0 V) ≤ ENNReal.ofReal (2 * offLineMoment (V + 1 / 2)) := by
  classical
  set B := boxFinsetLe (V + 1 / 2)
  have hsub : xiShadow ∩ Icc 0 V ⊆
      ⋃ ρ ∈ B, Ioo (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2)) := by
    intro x hx
    obtain ⟨ρ, hρ, hxρ⟩ := exists_boxZero_of_mem_xiShadow hx
    exact mem_iUnion₂.mpr ⟨ρ, hρ, hxρ⟩
  have hB : ∀ ρ ∈ B, 1 / 2 < ρ.re ∧ xi ρ = 0 := by
    intro ρ hρ
    rw [mem_boxFinsetLe] at hρ
    exact ⟨hρ.1, hρ.2.2.2.2⟩
  calc volume (xiShadow ∩ Icc 0 V)
      ≤ volume (⋃ ρ ∈ B, Ioo (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2))) := measure_mono hsub
    _ ≤ ∑ ρ ∈ B, volume (Ioo (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2))) :=
        measure_biUnion_finset_le _ _
    _ = ∑ ρ ∈ B, ENNReal.ofReal (2 * (ρ.re - 1 / 2)) := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Real.volume_Ioo]
        congr 1
        ring
    _ = ENNReal.ofReal (∑ ρ ∈ B, 2 * (ρ.re - 1 / 2)) :=
        (ENNReal.ofReal_sum_of_nonneg fun ρ hρ => by linarith [(hB ρ hρ).1]).symm
    _ ≤ ENNReal.ofReal (2 * offLineMoment (V + 1 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        unfold offLineMoment
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have h1 := one_le_toNat_analyticOrderAt_xi (hB ρ hρ).2
        have h1' : (1 : ℝ) ≤ ((analyticOrderAt xi ρ).toNat : ℝ) := by exact_mod_cast h1
        have hpos : 0 ≤ ρ.re - 1 / 2 := by linarith [(hB ρ hρ).1]
        nlinarith

/-- From an off-line moment bound `Σ m(ρ)(Re ρ − ½) ≤ μ V`, for all large `V` the shadow occupies
at most `2μ V + μ` of `[0, V]`. -/
theorem eventually_volume_xiShadow_inter_Icc_le_of_moment {μ : ℝ}
    (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    ∀ᶠ V in atTop, volume (xiShadow ∩ Icc 0 V) ≤ ENNReal.ofReal (2 * μ * V + μ) := by
  have h := (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_id).eventually hmom
  filter_upwards [h] with V hV
  refine (volume_xiShadow_inter_Icc_le_offLineMoment V).trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [id] at hV
  linarith

/-- For all large `V` the shadow occupies at most `(21/50) V + 21/100` of `[0, V]`. -/
theorem eventually_volume_xiShadow_inter_Icc_le :
    ∀ᶠ V in atTop, volume (xiShadow ∩ Icc 0 V) ≤ ENNReal.ofReal (21 / 50 * V + 21 / 100) :=
  (eventually_volume_xiShadow_inter_Icc_le_of_moment
    ZetaGateProductAFE.eventually_offLineMoment_le).mono fun V h =>
      h.trans_eq (by congr 1; ring)

/-- A property holding at every real point outside the shadow holds on measure at least
`V − c` of `[0, V]` once the shadow occupies at most `c ≥ 0` of `[0, V]`. -/
theorem ofReal_sub_le_volume_of_not_mem_xiShadow {P : ℝ → Prop}
    (hP : ∀ x : ℝ, x ∉ xiShadow → P x) {V c : ℝ} (hc : 0 ≤ c)
    (hV : volume (xiShadow ∩ Icc 0 V) ≤ ENNReal.ofReal c) :
    ENNReal.ofReal (V - c) ≤ volume {x ∈ Icc (0 : ℝ) V | P x} := by
  have hsub : Icc 0 V \ (xiShadow ∩ Icc 0 V) ⊆ {x ∈ Icc (0 : ℝ) V | P x} :=
    fun x hx => ⟨hx.1, hP x fun h => hx.2 ⟨h, hx.1⟩⟩
  calc ENNReal.ofReal (V - c) = ENNReal.ofReal V - ENNReal.ofReal c := ENNReal.ofReal_sub _ hc
    _ ≤ volume (Icc (0 : ℝ) V) - volume (xiShadow ∩ Icc 0 V) := by
        rw [Real.volume_Icc, sub_zero]
        exact tsub_le_tsub_left hV _
    _ ≤ volume (Icc (0 : ℝ) V \ (xiShadow ∩ Icc 0 V)) := le_measure_sdiff
    _ ≤ _ := measure_mono hsub

/-- **Laguerre positivity and vertical monotonicity from an off-line moment bound.** If
`Σ m(ρ)(Re ρ − ½) ≤ μ V` for all large `V`, `μ ≥ 0`, then for all large `V` the set of
`x ∈ [0, V]` with `Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0` and `y ↦ |Ξ(x+iy)|` nondecreasing on `y ≥ 0` has measure
at least `(1 − 2μ) V − μ`. -/
theorem eventually_volume_laguerre_monotone_ge_of_moment {μ : ℝ} (hμ : 0 ≤ μ)
    (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    ∀ᶠ V in atTop, ENNReal.ofReal ((1 - 2 * μ) * V - μ) ≤
      volume {x ∈ Icc (0 : ℝ) V |
        MonotoneOn (fun y : ℝ => ‖riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
        0 ≤ (deriv (riemannHeat 0) x ^ 2 - riemannHeat 0 x * deriv (deriv (riemannHeat 0)) x).re} := by
  filter_upwards [eventually_volume_xiShadow_inter_Icc_le_of_moment hmom, eventually_ge_atTop 0]
    with V hV hV0
  have h := ofReal_sub_le_volume_of_not_mem_xiShadow
    (fun x hx => monotoneOn_laguerre_of_not_mem_xiShadow hx) (by positivity) hV
  rwa [show V - (2 * μ * V + μ) = (1 - 2 * μ) * V - μ by ring] at h

/-- **`Ξ` is Laguerre-positive and vertically monotone on more than half of the real line.** For
all large `V` the set of `x ∈ [0, V]` with `Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0` and `y ↦ |Ξ(x+iy)|`
nondecreasing on `y ≥ 0` has measure at least `(29/50) V − 21/100`. -/
theorem eventually_volume_laguerre_monotone_ge :
    ∀ᶠ V in atTop, ENNReal.ofReal (29 / 50 * V - 21 / 100) ≤
      volume {x ∈ Icc (0 : ℝ) V |
        MonotoneOn (fun y : ℝ => ‖riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
        0 ≤ (deriv (riemannHeat 0) x ^ 2 - riemannHeat 0 x * deriv (deriv (riemannHeat 0)) x).re} :=
  (eventually_volume_laguerre_monotone_ge_of_moment (by norm_num)
    ZetaGateProductAFE.eventually_offLineMoment_le).mono fun V h =>
      le_trans (le_of_eq (by congr 1; ring)) h

end

end RHTower.DeBruijn
