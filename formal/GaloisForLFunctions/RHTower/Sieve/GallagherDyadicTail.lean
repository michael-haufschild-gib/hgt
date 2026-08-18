import GaloisForLFunctions.RHTower.Sieve.GallagherMeanValue
import GaloisForLFunctions.RHTower.Sieve.GallagherTail

/-!
# Gallagher's far tail, paid dyadically by the mean value theorem

`gallagher_split_integral` bounds the frequencies beyond `W` by the coefficients' ℓ¹ mass times
the weight's tail mass `2/(π²W)`, which forces the frequency range to the square of the inverse
window.  The Gallagher weight, however, decays quadratically.  Cutting the far range into dyadic
annuli and paying each annulus by a mean-square bound over the doubled symmetric range replaces
the ℓ¹ mass entirely: under an affine majorant `α·T + β` for the symmetric frequency mean square
— the shape the mean value theorem supplies — the far tail costs exactly

    4α/(π²W) + 4β/(3π²W²).

At `W` of the order of the inverse window both terms are harmless, so the quadratic frequency
requirement disappears and the whole passage is paid by mean squares.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform

/-- A dyadic annulus of frequencies above a threshold. -/
def dyadicAnnulus (W : ℝ) (k : ℕ) : Set ℝ :=
  {w : ℝ | 2 ^ k * W ≤ |w| ∧ |w| < 2 ^ (k + 1) * W}

theorem measurableSet_dyadicAnnulus (W : ℝ) (k : ℕ) :
    MeasurableSet (dyadicAnnulus W k) :=
  (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

/-- Annuli of increasing index are disjoint. -/
theorem dyadicAnnulus_disjoint_of_lt {W : ℝ} (hW : 0 < W) {k l : ℕ} (hkl : k < l) :
    Disjoint (dyadicAnnulus W k) (dyadicAnnulus W l) := by
  rw [Set.disjoint_left]
  intro w hwk hwl
  have h1 : |w| < 2 ^ (k + 1) * W := hwk.2
  have h2 : 2 ^ l * W ≤ |w| := hwl.1
  have hpow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ l := pow_le_pow_right₀ one_le_two hkl
  have hmul := mul_le_mul_of_nonneg_right hpow hW.le
  linarith

theorem pairwise_disjoint_dyadicAnnulus {W : ℝ} (hW : 0 < W) :
    Pairwise (Function.onFun Disjoint (dyadicAnnulus W)) := by
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact dyadicAnnulus_disjoint_of_lt hW h
  · exact (dyadicAnnulus_disjoint_of_lt hW h).symm

/-- Every magnitude above the threshold lies at exactly one dyadic scale. -/
theorem exists_dyadic_scale {W x : ℝ} (hW : 0 < W) (hx : W ≤ x) :
    ∃ k : ℕ, 2 ^ k * W ≤ x ∧ x < 2 ^ (k + 1) * W := by
  classical
  have hex : ∃ m : ℕ, x / W < 2 ^ m := pow_unbounded_of_one_lt (x / W) one_lt_two
  have hmspec : x / W < 2 ^ Nat.find hex := Nat.find_spec hex
  have hone : (1 : ℝ) ≤ x / W := (one_le_div hW).mpr hx
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hmspec
    linarith
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨k, ?_, ?_⟩
  · have hnot : ¬ x / W < 2 ^ k := Nat.find_min hex (by omega)
    rw [not_lt] at hnot
    calc 2 ^ k * W ≤ x / W * W := mul_le_mul_of_nonneg_right hnot hW.le
      _ = x := div_mul_cancel₀ x hW.ne'
  · have hlt : x / W < 2 ^ (k + 1) := by rw [← hk]; exact hmspec
    calc x = x / W * W := (div_mul_cancel₀ x hW.ne').symm
      _ < 2 ^ (k + 1) * W := mul_lt_mul_of_pos_right hlt hW

/-- The annuli tile the far range exactly. -/
theorem iUnion_dyadicAnnulus {W : ℝ} (hW : 0 < W) :
    (⋃ k : ℕ, dyadicAnnulus W k) = {w : ℝ | W ≤ |w|} := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, dyadicAnnulus]
  constructor
  · rintro ⟨k, hk1, _⟩
    have h1 : (1 : ℝ) ≤ 2 ^ k := by
      simpa using pow_le_pow_right₀ (one_le_two (α := ℝ)) (Nat.zero_le k)
    calc W = 1 * W := (one_mul W).symm
      _ ≤ 2 ^ k * W := mul_le_mul_of_nonneg_right h1 hW.le
      _ ≤ |w| := hk1
  · intro hw
    exact exists_dyadic_scale hW hw

/-- **Gallagher's far tail, paid dyadically.**  Under an affine symmetric mean-square majorant
`α·T + β` above the cut, the frequencies past the cut cost `4α/(π²W) + 4β/(3π²W²)`. -/
theorem gallagher_farTail_dyadic_le (a : ℕ → ℂ) (s : Finset ℕ) {δ W α β : ℝ}
    (hδ : 0 < δ) (hW : 0 < W)
    (hG : ∀ T : ℝ, W ≤ T → (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ 2) ≤ α * T + β) :
    (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
      ≤ 4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2) := by
  have hpi := Real.pi_pos
  have hF : Integrable fun w : ℝ => (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 :=
    integrable_gallagher_weight_mul hδ a s
  have hcont : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ 2 :=
    ((continuous_logPoly a s).norm).pow 2
  have hnnw : ∀ w : ℝ, 0 ≤ (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 := fun w =>
    mul_nonneg (fourier_triC_re_nonneg hδ w) (by positivity)
  have hfar : (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
      ≤ 4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2) := by
    have hsub : (Set.Icc (-W) W)ᶜ ⊆ {w : ℝ | W ≤ |w|} := by
      intro w hw
      rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or] at hw
      rw [Set.mem_setOf_eq]
      rcases hw with h | h
      · rw [not_le] at h
        have hw0 : w < 0 := lt_of_lt_of_le h (by linarith)
        rw [abs_of_neg hw0]
        linarith
      · rw [not_le] at h
        have hw0 : 0 < w := lt_trans hW h
        rw [abs_of_pos hw0]
        linarith
    have hmono : (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in {w : ℝ | W ≤ |w|}, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 :=
      setIntegral_mono_set hF.integrableOn
        (Filter.Eventually.of_forall fun w => hnnw w) hsub.eventuallyLE
    have hHasSum : HasSum
        (fun k : ℕ => ∫ w in dyadicAnnulus W k,
          (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        (∫ w in ⋃ k : ℕ, dyadicAnnulus W k,
          (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2) :=
      MeasureTheory.hasSum_integral_iUnion (fun k => measurableSet_dyadicAnnulus W k)
        (pairwise_disjoint_dyadicAnnulus hW) hF.integrableOn
    have hblock : ∀ k : ℕ,
        (∫ w in dyadicAnnulus W k, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
          ≤ 2 * α / (Real.pi ^ 2 * W) * ((1 : ℝ) / 2) ^ k
            + β / (Real.pi ^ 2 * W ^ 2) * ((1 : ℝ) / 4) ^ k := by
      intro k
      have hc : (0 : ℝ) < 2 ^ k * W := by positivity
      have hsubIcc : dyadicAnnulus W k
          ⊆ Set.Icc (-(2 ^ (k + 1) * W)) (2 ^ (k + 1) * W) := by
        intro w hw
        rw [Set.mem_Icc]
        constructor
        · linarith [neg_abs_le w, hw.2]
        · linarith [le_abs_self w, hw.2]
      have hIccInt : IntegrableOn
          (fun w => 1 / (Real.pi ^ 2 * (2 ^ k * W) ^ 2) * ‖logPoly a s w‖ ^ 2)
          (dyadicAnnulus W k) :=
        ((hcont.const_mul _).integrableOn_Icc).mono_set hsubIcc
      have h1 : (∫ w in dyadicAnnulus W k, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
          ≤ ∫ w in dyadicAnnulus W k,
              1 / (Real.pi ^ 2 * (2 ^ k * W) ^ 2) * ‖logPoly a s w‖ ^ 2 := by
        refine setIntegral_mono_on hF.integrableOn hIccInt
          (measurableSet_dyadicAnnulus W k) fun w hw => ?_
        have hw0 : w ≠ 0 := by
          intro h0
          have h1' : 2 ^ k * W ≤ |w| := hw.1
          rw [h0, abs_zero] at h1'
          exact absurd h1' (not_le.mpr hc)
        have hdecay := fourier_triC_re_le_inv_sq hδ hw0
        have hcw : (2 ^ k * W) ^ 2 ≤ w ^ 2 := by
          have h := pow_le_pow_left₀ hc.le hw.1 2
          rwa [sq_abs] at h
        have hmonole : 1 / (Real.pi ^ 2 * w ^ 2)
            ≤ 1 / (Real.pi ^ 2 * (2 ^ k * W) ^ 2) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          nlinarith [sq_nonneg Real.pi]
        exact mul_le_mul_of_nonneg_right (le_trans hdecay hmonole) (by positivity)
      have h3 : (∫ w in dyadicAnnulus W k, ‖logPoly a s w‖ ^ 2)
          ≤ ∫ w in Set.Icc (-(2 ^ (k + 1) * W)) (2 ^ (k + 1) * W), ‖logPoly a s w‖ ^ 2 :=
        setIntegral_mono_set hcont.integrableOn_Icc
          (Filter.Eventually.of_forall fun w => by positivity) hsubIcc.eventuallyLE
      have hWT : W ≤ 2 ^ (k + 1) * W := by
        have h1' : (1 : ℝ) ≤ 2 ^ (k + 1) := by
          simpa using pow_le_pow_right₀ (one_le_two (α := ℝ)) (Nat.zero_le (k + 1))
        nlinarith
      have h4 := hG (2 ^ (k + 1) * W) hWT
      have hchain : (∫ w in dyadicAnnulus W k, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
          ≤ 1 / (Real.pi ^ 2 * (2 ^ k * W) ^ 2) * (α * (2 ^ (k + 1) * W) + β) := by
        refine le_trans h1 ?_
        rw [MeasureTheory.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (le_trans h3 h4) (by positivity)
      refine le_trans hchain (le_of_eq ?_)
      have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
      have hWne : W ≠ 0 := hW.ne'
      have hpine : Real.pi ≠ 0 := hpi.ne'
      have hhalf : ((1 : ℝ) / 2) ^ k = ((2 : ℝ) ^ k)⁻¹ := by
        rw [one_div, inv_pow]
      have hquarter : ((1 : ℝ) / 4) ^ k = (((2 : ℝ) ^ k) ^ 2)⁻¹ := by
        rw [one_div, inv_pow]
        congr 1
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm 2 k]
      rw [hhalf, hquarter, pow_succ]
      field_simp
      ring
    have hsummb : Summable (fun k : ℕ =>
        2 * α / (Real.pi ^ 2 * W) * ((1 : ℝ) / 2) ^ k
          + β / (Real.pi ^ 2 * W ^ 2) * ((1 : ℝ) / 4) ^ k) := by
      refine Summable.add ?_ ?_
      · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have htsum_le :
        (∑' k : ℕ, ∫ w in dyadicAnnulus W k,
            (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
          ≤ ∑' k : ℕ, (2 * α / (Real.pi ^ 2 * W) * ((1 : ℝ) / 2) ^ k
              + β / (Real.pi ^ 2 * W ^ 2) * ((1 : ℝ) / 4) ^ k) :=
      hHasSum.summable.tsum_le_tsum hblock hsummb
    have htsum_eval :
        (∑' k : ℕ, (2 * α / (Real.pi ^ 2 * W) * ((1 : ℝ) / 2) ^ k
            + β / (Real.pi ^ 2 * W ^ 2) * ((1 : ℝ) / 4) ^ k))
          = 4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2) := by
      rw [Summable.tsum_add
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _),
        tsum_mul_left, tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num) (by norm_num),
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      have h12 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
      have h14 : ((1 : ℝ) - 1 / 4)⁻¹ = 4 / 3 := by norm_num
      rw [h12, h14]
      ring
    calc (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in {w : ℝ | W ≤ |w|}, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 := hmono
      _ = ∫ w in ⋃ k : ℕ, dyadicAnnulus W k,
            (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 := by
          rw [iUnion_dyadicAnnulus hW]
      _ = ∑' k : ℕ, ∫ w in dyadicAnnulus W k,
            (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 := hHasSum.tsum_eq.symm
      _ ≤ ∑' k : ℕ, (2 * α / (Real.pi ^ 2 * W) * ((1 : ℝ) / 2) ^ k
            + β / (Real.pi ^ 2 * W ^ 2) * ((1 : ℝ) / 4) ^ k) := htsum_le
      _ = 4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2) := htsum_eval
  exact hfar

/-- **Gallagher's identity with a dyadically paid far tail.**  Under an affine symmetric
mean-square majorant `α·T + β`, every frequency is paid by a mean square: the good range costs
`2δ²(αW + β)` and the far tail `4α/(π²W) + 4β/(3π²W²)`.  No ℓ¹ coefficient mass occurs. -/
theorem gallagher_split_integral_dyadic (a : ℕ → ℂ) (s : Finset ℕ) {δ W α β : ℝ}
    (hδ : 0 < δ) (hW : 0 < W)
    (hG : ∀ T : ℝ, W ≤ T → (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ 2) ≤ α * T + β) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      ≤ 2 * δ ^ 2 * (α * W + β)
        + (4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2)) := by
  have hF : Integrable fun w : ℝ => (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 :=
    integrable_gallagher_weight_mul hδ a s
  have hcont : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ 2 :=
    ((continuous_logPoly a s).norm).pow 2
  rw [gallagher_identity a s hδ]
  rw [← integral_add_compl (measurableSet_Icc (a := -W) (b := W)) hF]
  have hin : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
      ≤ 2 * δ ^ 2 * (α * W + β) := by
    have hstep : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in Set.Icc (-W) W, 2 * δ ^ 2 * ‖logPoly a s w‖ ^ 2 := by
      refine setIntegral_mono_on hF.integrableOn
        ((hcont.const_mul (2 * δ ^ 2)).integrableOn_Icc) measurableSet_Icc fun w _ => ?_
      exact mul_le_mul_of_nonneg_right (fourier_triC_re_le_two_sq hδ w) (by positivity)
    refine le_trans hstep ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hG W le_rfl) (by positivity)
  have hfar := gallagher_farTail_dyadic_le a s hδ hW hG
  linarith

/-- **Gallagher's identity with the head paid separately.**  The mean value theorem is sharp at the
diagonal, so using it below the cut reproduces the trivial bound; a genuine estimate `β₀` for the
frequencies below the cut must be supplied on its own, and the affine majorant used only above. -/
theorem gallagher_split_integral_dyadic_head (a : ℕ → ℂ) (s : Finset ℕ) {δ W α β β₀ : ℝ}
    (hδ : 0 < δ) (hW : 0 < W)
    (hHead : (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2) ≤ β₀)
    (hG : ∀ T : ℝ, W ≤ T → (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ 2) ≤ α * T + β) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      ≤ 2 * δ ^ 2 * β₀
        + (4 * α / (Real.pi ^ 2 * W) + 4 * β / (3 * Real.pi ^ 2 * W ^ 2)) := by
  have hF : Integrable fun w : ℝ => (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 :=
    integrable_gallagher_weight_mul hδ a s
  have hcont : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ 2 :=
    ((continuous_logPoly a s).norm).pow 2
  rw [gallagher_identity a s hδ]
  rw [← integral_add_compl (measurableSet_Icc (a := -W) (b := W)) hF]
  have hin : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
      ≤ 2 * δ ^ 2 * β₀ := by
    have hstep : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in Set.Icc (-W) W, 2 * δ ^ 2 * ‖logPoly a s w‖ ^ 2 := by
      refine setIntegral_mono_on hF.integrableOn
        ((hcont.const_mul (2 * δ ^ 2)).integrableOn_Icc) measurableSet_Icc fun w _ => ?_
      exact mul_le_mul_of_nonneg_right (fourier_triC_re_le_two_sq hδ w) (by positivity)
    refine le_trans hstep ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hHead (by positivity)
  have hfar := gallagher_farTail_dyadic_le a s hδ hW hG
  linarith

/-- **The short-interval mean square, all frequencies paid by the mean value theorem.**  The far
tail carries the mean-square coefficient mass `∑‖a‖²`, not the ℓ¹ mass `(∑‖a‖)²`. -/
theorem gallagher_meanValue_dyadic_le (a : ℕ → ℂ) (N : ℕ) {δ W : ℝ} (hδ : 0 < δ)
    (hW : 0 < W) :
    (∫ u : ℝ, ‖logWindowSum a (Finset.Icc 1 N) δ u‖ ^ 2)
      ≤ 2 * δ ^ 2 * (2 * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2) * W
            + 4 * (N : ℝ) * (1 + Real.log N) / Real.pi
              * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2))
        + (4 * (2 * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2)) / (Real.pi ^ 2 * W)
            + 4 * (4 * (N : ℝ) * (1 + Real.log N) / Real.pi
                * (∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ 2)) / (3 * Real.pi ^ 2 * W ^ 2)) := by
  have hpi := Real.pi_pos
  refine gallagher_split_integral_dyadic a (Finset.Icc 1 N) hδ hW ?_
  intro T hT
  have h := integral_Icc_normSq_logPoly_le a N (W := T) (le_trans hW.le hT)
  refine le_trans h (le_of_eq ?_)
  have hpine : Real.pi ≠ 0 := hpi.ne'
  field_simp

end RHTower.Sieve
