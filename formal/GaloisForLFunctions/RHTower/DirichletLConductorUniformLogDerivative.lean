import GaloisForLFunctions.RHTower.DirichletLUniformZeroFreeRegion
import GaloisForLFunctions.RHTower.SiegelZeroFree
import GaloisForLFunctions.RHTower.DirichletCharacterPerronBounds

/-!
# Conductor-uniform logarithmic derivatives on Perron rectangles

The uniform zero-free region and the real-character zero exclusion provide
one rectangle width for all characters of a growing modulus. Local partial
fractions retain multiplicities and replace bounded-height compactness by
quantitative zero distances.
-/

noncomputable section

set_option autoImplicit false

open Complex Metric Finset

namespace RHTower

/-- A single conductor-dependent gap excludes all zeros near a Perron rectangle,
including real zeros of quadratic characters. -/
theorem exists_conductor_uniform_character_zero_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 8 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ T : ℝ, 0 ≤ T → ∀ ρ : ℂ, χ.LFunction ρ = 0 → |ρ.im| ≤ T + 2 →
          4 * (a * (q : ℝ) ^ (-ε) / Real.log ((q : ℝ) * (T + 5)) ^ 2) ≤ 1 - ρ.re := by
  obtain ⟨c, hc, hnonreal⟩ := uniform_zero_free_region
  obtain ⟨d, hd, hreal⟩ := siegel_zero_free hε
  let a := min (c / 4) (min (d / 4) (1 / 8))
  have ha : 0 < a := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hac : 4 * a ≤ c := by
    have h : a ≤ c / 4 := min_le_left _ _
    linarith only [h]
  have had : 4 * a ≤ d := by
    have h : a ≤ d / 4 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [h]
  refine ⟨a, ha, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro q _ χ hχ T hT ρ hρ hheight
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hp0 : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hq0 _
  have hp1 : (q : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith only [hε])
  have hL1 : 1 ≤ Real.log ((q : ℝ) * (T + 5)) := by
    apply one_lt_log_three.le.trans
    apply Real.log_le_log (by norm_num)
    nlinarith only [hq1, hT, mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ T + 5 by linarith)]
  have hLsq : 1 ≤ Real.log ((q : ℝ) * (T + 5)) ^ 2 := one_le_pow₀ hL1
  have hρlog0 : 0 < Real.log ((q : ℝ) * (|ρ.im| + 3)) :=
    zero_lt_one.trans_le (one_le_log_conductor (q := q) ρ.im)
  have hlogs : Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤
      Real.log ((q : ℝ) * (T + 5)) := by
    apply Real.log_le_log (mul_pos hq0 (by positivity))
    exact mul_le_mul_of_nonneg_left (by linarith only [hheight]) hq0.le
  have hz : χ.LFunction ((ρ.re : ℂ) + ρ.im * I) = 0 := by
    simpa only [Complex.re_add_im] using hρ
  rcases hnonreal q χ hχ ρ.re ρ.im hz with hquad | hgap
  · have hzreal : χ.LFunction (ρ.re : ℂ) = 0 := by
      simpa only [hquad.2, Complex.ofReal_zero, zero_mul, add_zero] using hz
    have hgap : ρ.re ≤ 1 - d * (q : ℝ) ^ (-ε) := by
      by_contra h
      exact hreal q χ hquad.1 hχ ρ.re (lt_of_not_ge h) hzreal
    have hsmall : a * (q : ℝ) ^ (-ε) /
        Real.log ((q : ℝ) * (T + 5)) ^ 2 ≤ a * (q : ℝ) ^ (-ε) :=
      div_le_self (mul_nonneg ha.le hp0.le) hLsq
    have hscale := mul_le_mul_of_nonneg_right had hp0.le
    nlinarith only [hsmall, hscale, hgap]
  · calc
      4 * (a * (q : ℝ) ^ (-ε) / Real.log ((q : ℝ) * (T + 5)) ^ 2) =
          (4 * a * (q : ℝ) ^ (-ε)) / Real.log ((q : ℝ) * (T + 5)) ^ 2 := by ring
      _ ≤ c / Real.log ((q : ℝ) * (T + 5)) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact (mul_le_of_le_one_right (by positivity) hp1).trans hac
      _ ≤ c / Real.log ((q : ℝ) * (|ρ.im| + 3)) ^ 2 :=
        div_le_div_of_nonneg_left hc.le (sq_pos_of_pos hρlog0)
          (pow_le_pow_left₀ hρlog0.le hlogs 2)
      _ ≤ 1 - ρ.re := by linarith only [hgap]

/-- The local partial fraction has logarithmically bounded total multiplicity.
Its real part on `Re s=2` pays every zero in the local disc. -/
theorem L_partial_fraction_with_multiplicity_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (t : ℝ) :
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ ∈ closedBall (2 + t * I) (22 / 25 * (91 / 50)) |
        χ.LFunction ρ = 0}) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
        4 * (8 + pfConst * Real.log ((q : ℝ) * (|t| + 3))) ∧
      ∀ s ∈ closedBall (2 + t * I) (3 / 2), χ.LFunction s ≠ 0 →
        ‖logDeriv χ.LFunction s -
          ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ ≤
            pfConst * Real.log ((q : ℝ) * (|t| + 3)) := by
  obtain ⟨Z, hZ, hpf⟩ := L_logDeriv_partial_fraction_all hχ t
  let z : ℂ := 2 + t * I
  have hzeros : ∀ ρ ∈ Z, χ.LFunction ρ = 0 ∧
      ρ ∈ closedBall z (22 / 25 * (91 / 50)) := by
    intro ρ hρ
    have h : ρ ∈ (Z : Set ℂ) := hρ
    rw [hZ] at h
    exact ⟨h.2, h.1⟩
  have hne : χ.LFunction z ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simp [z])
  have hr : ‖logDeriv χ.LFunction z‖ ≤ 8 := by
    rw [logDeriv_apply]
    have h := norm_character_logDeriv_le_line χ (s := z) (by simp [z]) (by simp [z])
    norm_num only [show z.re = 2 by simp [z]] at h
    exact h
  have he := hpf z (by change dist z z ≤ (3 / 2 : ℝ); norm_num) hne
  have hinv : ∀ ρ ∈ Z, (1 / 4 : ℝ) ≤ ((z - ρ)⁻¹).re := by
    intro ρ hρ
    have hβ := re_lt_one_of_LFunction_eq_zero hχ (hzeros ρ hρ).1
    have hreal : 1 ≤ (z - ρ).re := by
      have hzre : z.re = 2 := by simp [z]
      rw [Complex.sub_re, hzre]
      linarith only [hβ]
    have hd0 : z - ρ ≠ 0 := by
      intro hd
      rw [hd, zero_re] at hreal
      norm_num at hreal
    have hd : ‖z - ρ‖ ≤ 2 := by
      calc
        ‖z - ρ‖ = ‖ρ - z‖ := norm_sub_rev _ _
        _ ≤ 22 / 25 * (91 / 50) := by
          simpa only [mem_closedBall, Complex.dist_eq] using (hzeros ρ hρ).2
        _ ≤ 2 := by norm_num
    have hs0 : 0 < normSq (z - ρ) := by
      rw [Complex.normSq_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hd0)
    have hs4 : normSq (z - ρ) ≤ 4 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith only [hd, norm_nonneg (z - ρ)]
    rw [Complex.inv_re]
    apply (le_div_iff₀ hs0).mpr
    nlinarith only [hs4, hreal]
  have hcount : (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      4 * (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (z - ρ)).re := by
    rw [Complex.re_sum, mul_sum]
    refine sum_le_sum fun ρ hρ => ?_
    have h := mul_le_mul_of_nonneg_left (hinv ρ hρ)
      (Nat.cast_nonneg (analyticOrderNatAt χ.LFunction ρ) :
        (0 : ℝ) ≤ analyticOrderNatAt χ.LFunction ρ)
    rw [div_eq_mul_inv,
      show (analyticOrderNatAt χ.LFunction ρ : ℂ) =
        ((analyticOrderNatAt χ.LFunction ρ : ℝ) : ℂ) by norm_cast,
      Complex.re_ofReal_mul]
    nlinarith only [h]
  have hrealSum :
      (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (z - ρ)).re ≤
        8 + pfConst * Real.log ((q : ℝ) * (|t| + 3)) := by
    have hdiff := Complex.re_le_norm
      ((∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (z - ρ)) -
        logDeriv χ.LFunction z)
    rw [Complex.sub_re, norm_sub_rev] at hdiff
    have hmain := Complex.re_le_norm (logDeriv χ.LFunction z)
    linarith only [hdiff, hmain, he, hr]
  exact ⟨Z, hZ, hcount.trans (mul_le_mul_of_nonneg_left hrealSum (by norm_num)), hpf⟩

/-- Actual nonprincipal Dirichlet functions have conductor-uniform nonvanishing
and logarithmic derivative bounds on complete Perron rectangles. -/
theorem exists_conductor_uniform_character_logDeriv {ε : ℝ} (hε : 0 < ε) :
    ∃ a B : ℝ, 0 < a ∧ 0 < B ∧ a ≤ 1 / 8 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ T : ℝ, 0 ≤ T → ∀ s : ℂ,
          |s.re - 1| ≤ a * (q : ℝ) ^ (-ε) / Real.log ((q : ℝ) * (T + 5)) ^ 2 →
          |s.im| ≤ T → χ.LFunction s ≠ 0 ∧
            ‖logDeriv χ.LFunction s‖ ≤
              B * (q : ℝ) ^ ε * Real.log ((q : ℝ) * (T + 5)) ^ 3 := by
  obtain ⟨a, ha, ha8, hgap⟩ := exists_conductor_uniform_character_zero_gap hε
  let B := (32 + 5 * pfConst) / a
  have hB : 0 < B := div_pos (by nlinarith only [pfConst_pos]) ha
  refine ⟨a, B, ha, hB, ha8, ?_⟩
  intro q _ χ hχ T hT s hσ ht
  let L := Real.log ((q : ℝ) * (T + 5))
  let δ := a * (q : ℝ) ^ (-ε) / L ^ 2
  change |s.re - 1| ≤ δ at hσ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hp0 : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hq0 _
  have hp1 : (q : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith only [hε])
  have hL1 : 1 ≤ L := by
    apply one_lt_log_three.le.trans
    apply Real.log_le_log (by norm_num)
    nlinarith only [hq1, hT, mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ T + 5 by linarith)]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hδ0 : 0 < δ := div_pos (mul_pos ha hp0) (sq_pos_of_pos hL0)
  have hδa : δ ≤ a :=
    (div_le_self (mul_nonneg ha.le hp0.le) (one_le_pow₀ hL1)).trans
      (mul_le_of_le_one_right ha.le hp1)
  have hδ8 : δ ≤ 1 / 8 := hδa.trans ha8
  have hslo : 1 - δ ≤ s.re := by
    have h := (abs_le.mp hσ).1
    linarith only [h]
  have hshi : s.re ≤ 1 + δ := by
    have h := (abs_le.mp hσ).2
    linarith only [h]
  have hne : χ.LFunction s ≠ 0 := by
    intro hz
    have h := hgap q χ hχ T hT s hz (by linarith only [ht])
    change 4 * δ ≤ 1 - s.re at h
    linarith only [h, hslo, hδ0]
  refine ⟨hne, ?_⟩
  obtain ⟨Z, hZ, hmass, hpf⟩ := L_partial_fraction_with_multiplicity_bound hχ s.im
  let z : ℂ := 2 + s.im * I
  have hsball : s ∈ closedBall z (3 / 2) := by
    rw [mem_closedBall, Complex.dist_eq]
    have heq : s - z = ((s.re - 2 : ℝ) : ℂ) := by
      dsimp only [z]
      apply Complex.ext <;> simp
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [hslo, hshi, hδ8]
  have hlogs : Real.log ((q : ℝ) * (|s.im| + 3)) ≤ L := by
    apply Real.log_le_log (mul_pos hq0 (by positivity))
    exact mul_le_mul_of_nonneg_left (by linarith only [ht]) hq0.le
  have he : ‖logDeriv χ.LFunction s -
      ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ ≤ pfConst * L :=
    (hpf s hsball hne).trans (mul_le_mul_of_nonneg_left hlogs pfConst_pos.le)
  have hmass' : (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      (32 + 4 * pfConst) * L := by
    have h := mul_le_mul_of_nonneg_left hlogs pfConst_pos.le
    nlinarith only [hmass, h, hL1]
  have hdist : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
    intro ρ hρ
    have h : ρ ∈ (Z : Set ℂ) := hρ
    rw [hZ] at h
    have hn : ‖ρ - z‖ ≤ 22 / 25 * (91 / 50) := by
      simpa only [mem_closedBall, Complex.dist_eq] using h.1
    have him := Complex.abs_im_le_norm (ρ - z)
    have him' : |ρ.im - s.im| ≤ ‖ρ - z‖ := by simpa [z] using him
    have htri := abs_sub_abs_le_abs_sub ρ.im s.im
    have hheight : |ρ.im| ≤ T + 2 := by
      linarith only [hn, him', htri, ht]
    have hzero := hgap q χ hχ T hT ρ h.2 hheight
    change 4 * δ ≤ 1 - ρ.re at hzero
    have hre : δ ≤ (s - ρ).re := by
      rw [Complex.sub_re]
      linarith only [hzero, hslo, hδ0]
    exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hsum : ‖∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ ≤
      ((32 + 4 * pfConst) * L) / δ := by
    calc
      _ ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ) / δ := by
        refine sum_le_sum fun ρ hρ => ?_
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ0 (hdist ρ hρ)
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) / δ := by rw [sum_div]
      _ ≤ ((32 + 4 * pfConst) * L) / δ :=
        div_le_div_of_nonneg_right hmass' hδ0.le
  have herr : pfConst * L ≤ (pfConst * L) / δ := by
    apply (le_div_iff₀ hδ0).mpr
    exact mul_le_of_le_one_right (mul_nonneg pfConst_pos.le hL0.le)
      (by linarith only [hδ8])
  have htriangle := norm_sub_norm_le (logDeriv χ.LFunction s)
    (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ))
  have hbound : ‖logDeriv χ.LFunction s‖ ≤ ((32 + 5 * pfConst) * L) / δ := by
    calc
      _ ≤ ‖∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ +
          ‖logDeriv χ.LFunction s -
            ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖ := by
        linarith only [htriangle]
      _ ≤ ((32 + 4 * pfConst) * L) / δ + (pfConst * L) / δ :=
        add_le_add hsum (he.trans herr)
      _ = ((32 + 5 * pfConst) * L) / δ := by ring
  have heq : ((32 + 5 * pfConst) * L) / δ = B * (q : ℝ) ^ ε * L ^ 3 := by
    dsimp only [δ, B]
    rw [Real.rpow_neg hq0.le]
    field_simp [ha.ne', hL0.ne', (Real.rpow_pos_of_pos hq0 ε).ne']
  exact hbound.trans_eq heq

#print axioms exists_conductor_uniform_character_zero_gap
#print axioms L_partial_fraction_with_multiplicity_bound
#print axioms exists_conductor_uniform_character_logDeriv

end RHTower
