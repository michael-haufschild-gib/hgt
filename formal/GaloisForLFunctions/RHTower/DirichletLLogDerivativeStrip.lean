import GaloisForLFunctions.RHTower.DirichletLZeroFreeLogStrip

/-!
# Actual character reciprocal and logarithmic derivative control

The character 3-4-1 product and horizontal derivative estimate give a strictly
positive lower bound for the actual L-function throughout a closed logarithmic
strip. This constructs reciprocal control without assuming a lower bound.

At high heights the result holds for every character of the fixed modulus,
including principal and imprimitive characters. Compactness supplies bounded
heights for each nonprincipal character. The resulting full-height logarithmic
derivative estimate is the analytic input for the BAG character Perron contour.
-/

noncomputable section
open Filter Topology Finset Complex Set
namespace RHTower
variable {Q : ℕ} [NeZero Q]

/-- A width on which the character product supplies a quantitative reciprocal bound. -/
def characterPerronWidth (Q : ℕ) : ℝ :=
  1 / (4 * 32 ^ (4 : ℕ) * characterLogStripConstant Q ^ (8 : ℕ))

theorem characterPerronWidth_pos (Q : ℕ) : 0 < characterPerronWidth Q := by
  have hK : 0 < characterLogStripConstant Q := lt_of_lt_of_le zero_lt_one
    (one_le_characterLogStripConstant Q)
  unfold characterPerronWidth
  positivity

private theorem characterPerronWidth_le_half (Q : ℕ) : characterPerronWidth Q ≤ 1 / 2 := by
  have hK1 := one_le_characterLogStripConstant Q
  have hK : 0 < characterLogStripConstant Q := by linarith
  have hK8 : (1 : ℝ) ≤ characterLogStripConstant Q ^ (8 : ℕ) := one_le_pow₀ hK1
  unfold characterPerronWidth
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

omit [NeZero Q] in
private theorem characterPerronWidth_geometry {t : ℝ} (ht : 9 ≤ |t|) :
    0 < characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) ∧
    characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) ≤ 1 / 2 ∧
    characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) ≤ 1 / (4 * Real.log |t|) := by
  have hL2 : 2 < Real.log |t| := by
    have h := Real.log_lt_log (Real.exp_pos 2)
      (lt_of_lt_of_le exp_two_lt_eight (by linarith : 8 ≤ |t|))
    rwa [Real.log_exp] at h
  have hL : 0 < Real.log |t| := by linarith
  have ha := characterPerronWidth_pos Q
  have hah := characterPerronWidth_le_half Q
  refine ⟨by positivity, ?_, ?_⟩
  · exact (div_le_self ha.le (one_le_pow₀ (by linarith) : (1 : ℝ) ≤ Real.log |t| ^ (9 : ℕ))).trans hah
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hL8 : (2 : ℝ) ^ (8 : ℕ) ≤ Real.log |t| ^ (8 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hL2.le 8
    have hpow : Real.log |t| ^ (9 : ℕ) = Real.log |t| ^ (8 : ℕ) * Real.log |t| := by ring
    have haL : characterPerronWidth Q * (4 * Real.log |t|) ≤ 2 * Real.log |t| := by nlinarith
    nlinarith

/-- The actual character 3-4-1 product gives a positive floor throughout the strip,
including its left edge. No reciprocal bound is assumed. -/
theorem norm_LFunction_lower_log_strip (χ : DirichletCharacter ℂ Q)
    {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) ≤ σ)
    (hσu : σ ≤ 1 + characterPerronWidth Q / Real.log |t| ^ (9 : ℕ)) :
    16 * characterLogStripConstant Q * characterPerronWidth Q / Real.log |t| ^ (7 : ℕ) <
      ‖DirichletCharacter.LFunction χ (σ + t * I)‖ := by
  let K := characterLogStripConstant Q
  let a := characterPerronWidth Q
  let L := Real.log |t|
  let η := a / L ^ (9 : ℕ)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (one_le_characterLogStripConstant Q)
  have ha : 0 < a := characterPerronWidth_pos Q
  have hL : 0 < L := Real.log_pos (by linarith)
  obtain ⟨hη, hηhalf, hηfloor⟩ := characterPerronWidth_geometry (Q := Q) ht
  change 0 < η at hη
  change η ≤ 1 / 2 at hηhalf
  change η ≤ 1 / (4 * L) at hηfloor
  change 1 - η ≤ σ at hσl
  change σ ≤ 1 + η at hσu
  change 16 * K * a / L ^ (7 : ℕ) < _
  by_contra! hsmall
  have hfloor : 16 * K * a / L ^ (7 : ℕ) = 16 * K * η * L ^ (2 : ℕ) := by
    dsimp only [η]
    field_simp [hL.ne']
  have hmid : ‖DirichletCharacter.LFunction χ (((1 + η : ℝ) : ℂ) + t * I)‖ ≤
      32 * K * η * L ^ (2 : ℕ) := by
    have hd := norm_LFunction_sub_le_segment χ ht
      (show 1 - 1 / (4 * Real.log |t|) ≤ σ by change 1 - 1 / (4 * L) ≤ σ; linarith)
      hσu (show 1 + η ≤ 3 / 2 by linarith)
    change ‖DirichletCharacter.LFunction χ (((1 + η : ℝ) : ℂ) + t * I) -
      DirichletCharacter.LFunction χ (σ + t * I)‖ ≤ 8 * K * L ^ (2 : ℕ) * (1 + η - σ) at hd
    have htri := norm_le_norm_add_norm_sub'
      (DirichletCharacter.LFunction χ (((1 + η : ℝ) : ℂ) + t * I))
      (DirichletCharacter.LFunction χ (σ + t * I))
    rw [hfloor] at hsmall
    have hmul : 8 * K * L ^ (2 : ℕ) * (1 + η - σ) ≤
        8 * K * L ^ (2 : ℕ) * (2 * η) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hpole : ‖DirichletCharacter.LFunctionTrivChar Q (1 + (η : ℂ))‖ ≤ K / η :=
    norm_LFunctionTrivChar_one_add_le hη (by linarith)
  have hhigh : ‖DirichletCharacter.LFunction (χ ^ 2)
      (((1 + η : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ 2 * K * L := by
    have h2t : 8 ≤ |2 * t| := by rw [abs_mul, abs_two]; linarith
    have hlog2 : 0 < Real.log |2 * t| := Real.log_pos (by rw [abs_mul, abs_two]; linarith)
    have h := norm_LFunction_le_log (χ ^ 2) h2t
      (show 1 - 1 / Real.log |2 * t| ≤ 1 + η by
        have hinv : 0 < 1 / Real.log |2 * t| := by positivity
        linarith)
      (show 1 + η ≤ 2 by linarith)
    have hlog : Real.log |2 * t| ≤ 2 * L := by
      have hsq : |2 * t| ≤ |t| ^ (2 : ℕ) := by rw [abs_mul, abs_two]; nlinarith
      have he := Real.log_le_log (by rw [abs_mul, abs_two]; positivity : 0 < |2 * t|) hsq
      simpa only [Real.log_pow, Nat.cast_ofNat] using he
    change _ ≤ K * Real.log |2 * t| at h
    nlinarith
  have hprod := χ.norm_LFunction_product_ge_one hη t
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
  have harg2 : (1 : ℂ) + η + I * t = ((1 + η : ℝ) : ℂ) + t * I := by push_cast; ring
  have harg3 : (1 : ℂ) + η + 2 * I * t = ((1 + η : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg2, harg3] at hprod
  have hchain : ‖DirichletCharacter.LFunctionTrivChar Q (1 + (η : ℂ))‖ ^ (3 : ℕ) *
      ‖DirichletCharacter.LFunction χ (((1 + η : ℝ) : ℂ) + t * I)‖ ^ (4 : ℕ) *
      ‖DirichletCharacter.LFunction (χ ^ 2) (((1 + η : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤
      (K / η) ^ (3 : ℕ) * (32 * K * η * L ^ (2 : ℕ)) ^ (4 : ℕ) * (2 * K * L) := by
    exact mul_le_mul
      (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hpole 3)
        (pow_le_pow_left₀ (norm_nonneg _) hmid 4) (by positivity) (by positivity))
      hhigh (norm_nonneg _) (by positivity)
  have hcollapse : (K / η) ^ (3 : ℕ) * (32 * K * η * L ^ (2 : ℕ)) ^ (4 : ℕ) *
      (2 * K * L) = 1 / 2 := by
    dsimp only [η, a, characterPerronWidth]
    change (K / (1 / (4 * 32 ^ (4 : ℕ) * K ^ (8 : ℕ)) / L ^ (9 : ℕ))) ^ (3 : ℕ) *
      (32 * K * (1 / (4 * 32 ^ (4 : ℕ) * K ^ (8 : ℕ)) / L ^ (9 : ℕ)) * L ^ (2 : ℕ)) ^ (4 : ℕ) *
      (2 * K * L) = 1 / 2
    field_simp [hK.ne', hL.ne']
    ring
  rw [hcollapse] at hchain
  linarith

/-- Quantitative reciprocal control for every actual character on the full closed strip. -/
theorem norm_inv_LFunction_le_log_strip (χ : DirichletCharacter ℂ Q)
    {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) ≤ σ)
    (hσu : σ ≤ 1 + characterPerronWidth Q / Real.log |t| ^ (9 : ℕ)) :
    ‖(DirichletCharacter.LFunction χ (σ + t * I))⁻¹‖ ≤
      Real.log |t| ^ (7 : ℕ) / (16 * characterLogStripConstant Q * characterPerronWidth Q) := by
  have hK : 0 < characterLogStripConstant Q := lt_of_lt_of_le zero_lt_one
    (one_le_characterLogStripConstant Q)
  have ha := characterPerronWidth_pos Q
  have hL : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hf := norm_LFunction_lower_log_strip χ ht hσl hσu
  have hfloor : 0 < 16 * characterLogStripConstant Q * characterPerronWidth Q /
      Real.log |t| ^ (7 : ℕ) := by positivity
  have hnorm : 0 < ‖DirichletCharacter.LFunction χ (σ + t * I)‖ := hfloor.trans hf
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ hnorm]
  have hmul := mul_le_mul_of_nonneg_left hf.le
    (show 0 ≤ Real.log |t| ^ (7 : ℕ) /
      (16 * characterLogStripConstant Q * characterPerronWidth Q) by positivity)
  have hcancel : (Real.log |t| ^ (7 : ℕ) /
      (16 * characterLogStripConstant Q * characterPerronWidth Q)) *
      (16 * characterLogStripConstant Q * characterPerronWidth Q /
        Real.log |t| ^ (7 : ℕ)) = 1 := by field_simp
  linarith

/-- The actual logarithmic derivative has the polynomial-log control required by the
character Perron contour, with no lower-bound hypothesis. -/
theorem norm_deriv_div_LFunction_le_log_strip (χ : DirichletCharacter ℂ Q)
    {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσl : 1 - characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) ≤ σ)
    (hσu : σ ≤ 1 + characterPerronWidth Q / Real.log |t| ^ (9 : ℕ)) :
    ‖deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
        DirichletCharacter.LFunction χ (σ + t * I)‖ ≤
      Real.log |t| ^ (9 : ℕ) / (2 * characterPerronWidth Q) := by
  obtain ⟨_, hηhalf, hηfloor⟩ := characterPerronWidth_geometry (Q := Q) ht
  have hK : 0 < characterLogStripConstant Q := lt_of_lt_of_le zero_lt_one
    (one_le_characterLogStripConstant Q)
  have ha := characterPerronWidth_pos Q
  have hd := norm_deriv_LFunction_le_sq_log χ (σ := σ) ht (by linarith) (by linarith)
  have hi := norm_inv_LFunction_le_log_strip χ ht hσl hσu
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (8 * characterLogStripConstant Q * Real.log |t| ^ (2 : ℕ)) *
        (Real.log |t| ^ (7 : ℕ) / (16 * characterLogStripConstant Q * characterPerronWidth Q)) :=
      mul_le_mul hd hi (norm_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

private theorem exists_nonprincipal_character_logDeriv_bounded_height
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∀ σ t : ℝ, |t| ≤ 9 → |σ - 1| ≤ δ →
      DirichletCharacter.LFunction χ (σ + t * I) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
        DirichletCharacter.LFunction χ (σ + t * I)‖ ≤ B := by
  obtain ⟨c, hc, hzero⟩ := exists_nonprincipal_character_zero_free_log_strip hχ
  let δ := c / (2 * Real.log 12 ^ (9 : ℕ))
  have hlog12 : 0 < Real.log (12 : ℝ) := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let S : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) ''
    (Set.Icc (1 - δ) (1 + δ) ×ˢ Set.Icc (-9) 9)
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hnonzero : ∀ s ∈ S, DirichletCharacter.LFunction χ s ≠ 0 := by
    rintro _ ⟨⟨σ, t⟩, ⟨hσ, ht⟩, rfl⟩
    apply hzero σ t
    have ht9 : |t| ≤ 9 := abs_le.mpr ht
    have hlog : 0 < Real.log (3 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
    have hlogs : Real.log (3 + |t|) ≤ Real.log 12 :=
      Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hpow := pow_le_pow_left₀ hlog.le hlogs 9
    have hratio : 2 * δ ≤ c / Real.log (3 + |t|) ^ (9 : ℕ) := by
      calc
        2 * δ = c / Real.log 12 ^ (9 : ℕ) := by dsimp [δ]; ring
        _ ≤ _ := div_le_div_of_nonneg_left hc.le (by positivity) hpow
    have hslo : 1 - δ ≤ σ := hσ.1
    linarith
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have hcont : ContinuousOn (fun s => ‖deriv (DirichletCharacter.LFunction χ) s /
      DirichletCharacter.LFunction χ s‖) S :=
    ((hd.contDiff.continuous_deriv le_rfl).continuousOn.div
      hd.continuous.continuousOn hnonzero).norm
  obtain ⟨B, hB⟩ := hS.bddAbove_image hcont
  refine ⟨δ, max B 1, hδ, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun σ t ht hσ => ?_⟩
  have hs : (σ + t * I : ℂ) ∈ S := by
    refine ⟨(σ, t), ⟨?_, abs_le.mp ht⟩, rfl⟩
    obtain ⟨hl, hu⟩ := abs_le.mp hσ
    exact ⟨by linarith, by linarith⟩
  exact ⟨hnonzero _ hs, (hB ⟨_, hs, rfl⟩).trans (le_max_left _ _)⟩

/-- Every actual nonprincipal character has polynomial-log logarithmic derivative
control on a closed zero-free strip at every height. The constants are constructed
from the character, with no analytic or prime-distribution premise. -/
theorem exists_nonprincipal_character_logDeriv_log_strip
    {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ ∀ σ t : ℝ,
      |σ - 1| ≤ c / Real.log (3 + |t|) ^ (9 : ℕ) →
      DirichletCharacter.LFunction χ (σ + t * I) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
        DirichletCharacter.LFunction χ (σ + t * I)‖ ≤
        B * Real.log (3 + |t|) ^ (9 : ℕ) := by
  obtain ⟨δ, M, hδ, hM, hlow⟩ := exists_nonprincipal_character_logDeriv_bounded_height hχ
  let A : ℝ := Real.log 3 ^ (9 : ℕ)
  let a := characterPerronWidth Q
  let c := min a (δ * A)
  let B := max (1 / (2 * a)) (M / A)
  have ha : 0 < a := characterPerronWidth_pos Q
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 < A := pow_pos hlog3 _
  have hc : 0 < c := lt_min ha (mul_pos hδ hA)
  have hB : 0 < B := lt_of_lt_of_le (by positivity : 0 < 1 / (2 * a)) (le_max_left _ _)
  refine ⟨c, B, hc, hB, fun σ t hσ => ?_⟩
  have hL : 0 < Real.log (3 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
  have hden : 0 < Real.log (3 + |t|) ^ (9 : ℕ) := by positivity
  by_cases ht : 9 ≤ |t|
  · have hsmall : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlogs : Real.log |t| ≤ Real.log (3 + |t|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hpow := pow_le_pow_left₀ hsmall.le hlogs 9
    have hratio : c / Real.log (3 + |t|) ^ (9 : ℕ) ≤ a / Real.log |t| ^ (9 : ℕ) :=
      (div_le_div_of_nonneg_right (min_le_left _ _) hden.le).trans
        (div_le_div_of_nonneg_left ha.le (by positivity) hpow)
    have hs : |σ - 1| ≤ a / Real.log |t| ^ (9 : ℕ) := hσ.trans hratio
    obtain ⟨hsl, hsu⟩ := abs_le.mp hs
    have hl : 1 - characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) ≤ σ := by linarith
    have hu : σ ≤ 1 + characterPerronWidth Q / Real.log |t| ^ (9 : ℕ) := by linarith
    have hK : 0 < characterLogStripConstant Q :=
      lt_of_lt_of_le zero_lt_one (one_le_characterLogStripConstant Q)
    have hf := norm_LFunction_lower_log_strip χ ht hl hu
    have hfloor : 0 < 16 * characterLogStripConstant Q * characterPerronWidth Q /
        Real.log |t| ^ (7 : ℕ) := by positivity
    refine ⟨norm_pos_iff.mp (hfloor.trans hf), ?_⟩
    calc
      _ ≤ Real.log |t| ^ (9 : ℕ) / (2 * a) :=
        norm_deriv_div_LFunction_le_log_strip χ ht hl hu
      _ ≤ Real.log (3 + |t|) ^ (9 : ℕ) / (2 * a) :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ B * Real.log (3 + |t|) ^ (9 : ℕ) := by
        rw [div_eq_mul_inv, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [one_div] using (show 1 / (2 * a) ≤ B from le_max_left _ _)) hden.le
  · have hlogs : Real.log 3 ≤ Real.log (3 + |t|) :=
      Real.log_le_log (by norm_num) (le_add_of_nonneg_right (abs_nonneg t))
    have hpow : A ≤ Real.log (3 + |t|) ^ (9 : ℕ) := pow_le_pow_left₀ hlog3.le hlogs 9
    have hratio : c / Real.log (3 + |t|) ^ (9 : ℕ) ≤ δ := by
      apply (div_le_iff₀ hden).mpr
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hpow hδ.le)
    obtain ⟨hz, hb⟩ := hlow σ t (by linarith) (hσ.trans hratio)
    refine ⟨hz, hb.trans ?_⟩
    calc
      M = (M / A) * A := by field_simp
      _ ≤ (M / A) * Real.log (3 + |t|) ^ (9 : ℕ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ B * Real.log (3 + |t|) ^ (9 : ℕ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hden.le

end RHTower
