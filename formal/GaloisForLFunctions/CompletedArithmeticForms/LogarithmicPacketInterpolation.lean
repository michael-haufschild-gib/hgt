import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds

/-!
# Weighted interpolation for conductor packets

A linear bound on every conductor prefix gains one logarithmic power when
measured in the coefficients' logarithmic energy. Splitting at successive
powers of two gives a constant independent of the number of conductors.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory

universe u v

private theorem norm_add_sq_le_two {E : Type u} [NormedAddCommGroup E]
    (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have ht := norm_add_le x y
  nlinarith only [ht, norm_nonneg (x + y), norm_nonneg x, norm_nonneg y,
    sq_nonneg (‖x‖ - ‖y‖)]

/-- Prefix norm control lifts to weighted coefficient energy with one power of the largest weight. -/
theorem linear_packet_sq_le_weighted_of_prefix_bound
    {ι : Type u} [Fintype ι] {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : (ι → ℝ) →ₗ[ℝ] E) (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i) (C : ℝ)
    (hT : ∀ t : ℝ, 1 ≤ t → ∀ a : ι → ℝ, (∀ i, t < w i → a i = 0) →
      ‖T a‖ ^ 2 ≤ C ^ 2 * t ^ 2 * ∑ i, a i ^ 2)
    {H : ℝ} (hH : 1 ≤ H) (hmax : ∀ i, w i ≤ H) (a : ι → ℝ) :
    ‖T a‖ ^ 2 ≤ 8 * C ^ 2 * H * ∑ i, w i * a i ^ 2 := by
  have hdyadic : ∀ j : ℕ, ∀ b : ι → ℝ,
      (∀ i, (2 : ℝ) ^ j < w i → b i = 0) →
      ‖T b‖ ^ 2 ≤ 4 * C ^ 2 * (2 : ℝ) ^ j * ∑ i, w i * b i ^ 2 := by
    intro j
    induction j with
    | zero =>
      intro b hb
      have hs := hT 1 le_rfl b (by simpa only [pow_zero] using hb)
      have hm : (∑ i, b i ^ 2) ≤ ∑ i, w i * b i ^ 2 :=
        sum_le_sum fun i _ => by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i) (sq_nonneg (b i))
      have hG : 0 ≤ ∑ i, w i * b i ^ 2 :=
        sum_nonneg fun i _ => mul_nonneg (zero_le_one.trans (hw i)) (sq_nonneg _)
      simp only [pow_zero, one_pow, mul_one] at hs ⊢
      have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg C)
      have hCG : 0 ≤ C ^ 2 * ∑ i, w i * b i ^ 2 := mul_nonneg (sq_nonneg C) hG
      linarith only [hs, hh, hCG]
    | succ j ih =>
      intro b hb
      let lo : ι → ℝ := fun i => if w i ≤ (2 : ℝ) ^ j then b i else 0
      let hi : ι → ℝ := fun i => if w i ≤ (2 : ℝ) ^ j then 0 else b i
      have hsplit : b = lo + hi := by
        funext i
        dsimp only [lo, hi, Pi.add_apply]
        split_ifs <;> ring
      have hlo_support : ∀ i, (2 : ℝ) ^ j < w i → lo i = 0 := fun i hi =>
        if_neg (not_le.mpr hi)
      have hhi_support : ∀ i, (2 : ℝ) ^ (j + 1) < w i → hi i = 0 := by
        intro i hiw
        dsimp only [hi]
        split_ifs
        · rfl
        · exact hb i hiw
      have hlo := ih lo hlo_support
      have hhi0 := hT ((2 : ℝ) ^ (j + 1)) (one_le_pow₀ (by norm_num)) hi hhi_support
      have hmass_hi : (2 : ℝ) ^ j * (∑ i, hi i ^ 2) ≤ ∑ i, w i * hi i ^ 2 := by
        rw [mul_sum]
        apply sum_le_sum
        intro i _
        by_cases hh : w i ≤ (2 : ℝ) ^ j
        · simp only [hi, if_pos hh, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
        · exact mul_le_mul_of_nonneg_right (le_of_not_ge hh) (sq_nonneg _)
      have hhi : ‖T hi‖ ^ 2 ≤ 4 * C ^ 2 * (2 : ℝ) ^ j * ∑ i, w i * hi i ^ 2 := by
        calc
          _ ≤ C ^ 2 * ((2 : ℝ) ^ (j + 1)) ^ 2 * ∑ i, hi i ^ 2 := hhi0
          _ = (4 * C ^ 2 * (2 : ℝ) ^ j) * ((2 : ℝ) ^ j * ∑ i, hi i ^ 2) := by
            rw [pow_succ]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hmass_hi (by positivity)
      have henergy : (∑ i, w i * lo i ^ 2) + (∑ i, w i * hi i ^ 2) =
          ∑ i, w i * b i ^ 2 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        dsimp only [lo, hi]
        split_ifs <;> ring
      calc
        ‖T b‖ ^ 2 = ‖T lo + T hi‖ ^ 2 := by rw [hsplit, map_add]
        _ ≤ 2 * (‖T lo‖ ^ 2 + ‖T hi‖ ^ 2) := norm_add_sq_le_two _ _
        _ ≤ 2 * ((4 * C ^ 2 * (2 : ℝ) ^ j * ∑ i, w i * lo i ^ 2) +
            (4 * C ^ 2 * (2 : ℝ) ^ j * ∑ i, w i * hi i ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hlo hhi) zero_le_two
        _ = 4 * C ^ 2 * (2 : ℝ) ^ (j + 1) * ∑ i, w i * b i ^ 2 := by
          rw [← mul_add, henergy, pow_succ]
          ring
  obtain ⟨j, hj, hJ⟩ := exists_nat_pow_near hH (by norm_num : (1 : ℝ) < 2)
  have hs := hdyadic (j + 1) a (fun i hi => False.elim (not_lt_of_ge (hmax i) (hJ.trans hi)))
  have hG : 0 ≤ ∑ i, w i * a i ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (zero_le_one.trans (hw i)) (sq_nonneg _)
  calc
    _ ≤ 4 * C ^ 2 * (2 : ℝ) ^ (j + 1) * ∑ i, w i * a i ^ 2 := hs
    _ = 8 * C ^ 2 * (2 : ℝ) ^ j * ∑ i, w i * a i ^ 2 := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hj (by positivity)) hG

/-- Logarithmic prefix bounds retain the individual conductor weights in a full packet. -/
theorem conductor_packet_sq_le_logarithmic_weight
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R N : ℕ} (hR : 2 ≤ R) (T : EuclideanSpace ℝ (PrimeHorizonIndex N) →ₗ[ℝ] E)
    (C : ℝ)
    (hT : ∀ M : ℕ, 2 ≤ M → M ≤ R → ∀ b : ℕ → ℝ,
      ‖T (∑ m ∈ Icc 1 M, b m • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
        C ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b m ^ 2)
    (a : ℕ → ℝ) :
    ‖T (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
      32 * C ^ 2 * (1 + Real.log R) *
        ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 := by
  let f : (↥(Icc 1 R) → ℝ) →ₗ[ℝ] E :=
    { toFun := fun b => ∑ i : ↥(Icc 1 R), b i • T (normalizedRamanujanHorizonVector i N)
      map_add' := by intro b d; simp only [Pi.add_apply, add_smul, sum_add_distrib]
      map_smul' := by intro s b; simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum, RingHom.id_apply] }
  let w : ↥(Icc 1 R) → ℝ := fun i => 1 + Real.log (i : ℕ)
  have hw : ∀ i, 1 ≤ w i := fun i => by
    dsimp only [w]
    linarith only [Real.log_natCast_nonneg (i : ℕ)]
  have hF : ∀ t : ℝ, 1 ≤ t → ∀ b : ↥(Icc 1 R) → ℝ,
      (∀ i, t < w i → b i = 0) →
      ‖f b‖ ^ 2 ≤ (2 * C) ^ 2 * t ^ 2 * ∑ i, b i ^ 2 := by
    intro t ht b hb
    let b' : ℕ → ℝ := fun m => if hm : m ∈ Icc 1 R then b ⟨m, hm⟩ else 0
    have hb' (m : ℕ) (hm : m ∈ Icc 1 R) : b' m = b ⟨m, hm⟩ := dif_pos hm
    have hmap : f b = T (∑ m ∈ Icc 1 R, b' m • normalizedRamanujanHorizonVector m N) := by
      simp only [map_sum, map_smul]
      rw [← sum_coe_sort (Icc 1 R) (fun m => b' m • T (normalizedRamanujanHorizonVector m N))]
      change (∑ i : ↥(Icc 1 R), b i • T (normalizedRamanujanHorizonVector i N)) = _
      exact sum_congr rfl fun i _ => by rw [hb' i i.property]
    have hmass : (∑ m ∈ Icc 1 R, b' m ^ 2) = ∑ i, b i ^ 2 := by
      rw [← sum_coe_sort (Icc 1 R) (fun m => b' m ^ 2)]
      exact sum_congr rfl fun i _ => by rw [hb' i i.property]
    let S := (Icc 1 R).filter (fun m => b' m ≠ 0)
    by_cases hS : S.Nonempty
    · let M := max 2 (S.max' hS)
      have hM2 : 2 ≤ M := le_max_left _ _
      have htop : S.max' hS ∈ Icc 1 R := (mem_filter.mp (S.max'_mem hS)).1
      have hMR : M ≤ R := max_le hR (mem_Icc.mp htop).2
      have hzero (m : ℕ) (hm : m ∈ Icc 1 R) (hmM : m ∉ Icc 1 M) : b' m = 0 := by
        by_contra hz
        have hs : m ∈ S := mem_filter.mpr ⟨hm, hz⟩
        have hle : m ≤ M := (Finset.le_max' S m hs).trans (le_max_right _ _)
        exact hmM (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hle⟩)
      have hpacket : (∑ m ∈ Icc 1 R, b' m • normalizedRamanujanHorizonVector m N) =
          ∑ m ∈ Icc 1 M, b' m • normalizedRamanujanHorizonVector m N := by
        symm
        apply sum_subset (Icc_subset_Icc le_rfl hMR)
        intro m hm hmM
        rw [hzero m hm hmM, zero_smul]
      have hHM : 1 + Real.log M ≤ 2 * t := by
        by_cases htop2 : S.max' hS ≤ 2
        · have hMeq : M = 2 := max_eq_left htop2
          rw [hMeq]
          have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          simp only [Nat.cast_ofNat]
          linarith only [hl, ht]
        · have hMeq : M = S.max' hS := max_eq_right (le_of_not_ge htop2)
          have hbound : 1 + Real.log (S.max' hS) ≤ t := by
            by_contra h
            have hz := hb ⟨S.max' hS, htop⟩ (lt_of_not_ge h)
            have hnz := (mem_filter.mp (S.max'_mem hS)).2
            rw [hb' (S.max' hS) htop, hz] at hnz
            exact hnz rfl
          rw [hMeq]
          linarith only [hbound, ht]
      have hm : (∑ m ∈ Icc 1 M, b' m ^ 2) ≤ ∑ i, b i ^ 2 := by
        rw [← hmass]
        exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMR) fun _ _ _ => sq_nonneg _
      rw [hmap, hpacket]
      calc
        _ ≤ C ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b' m ^ 2 := hT M hM2 hMR b'
        _ ≤ C ^ 2 * (2 * t) ^ 2 * ∑ i, b i ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hHM 2) (sq_nonneg C)) hm
            (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = _ := by ring
    · have hb0 : ∀ i, b i = 0 := by
        intro i
        by_contra hi
        apply hS
        exact ⟨i, mem_filter.mpr ⟨i.property, by rwa [hb' i i.property]⟩⟩
      have hzero : b = 0 := funext hb0
      rw [hzero, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hH : 1 ≤ 1 + Real.log R := by linarith only [Real.log_natCast_nonneg R]
  have hmax : ∀ i, w i ≤ 1 + Real.log R := by
    intro i
    have hi0 : (0 : ℝ) < (i : ℕ) := by exact_mod_cast (mem_Icc.mp i.property).1
    have hiR : ((i : ℕ) : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp i.property).2
    dsimp only [w]
    linarith only [Real.log_le_log hi0 hiR]
  have hh := linear_packet_sq_le_weighted_of_prefix_bound f w hw (2 * C) hF hH hmax
    (fun i => a i)
  have hmap : f (fun i => a i) =
      T (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
    simp only [map_sum, map_smul]
    exact sum_coe_sort (Icc 1 R) (fun m => a m • T (normalizedRamanujanHorizonVector m N))
  have henergy : (∑ i : ↥(Icc 1 R), w i * a i ^ 2) =
      ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_coe_sort (Icc 1 R) (fun m => (1 + Real.log m) * a m ^ 2)
  rw [hmap, henergy] at hh
  exact hh.trans_eq (by ring)

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.linear_packet_sq_le_weighted_of_prefix_bound
#print axioms GaloisForLFunctions.CompletedArithmeticForms.conductor_packet_sq_le_logarithmic_weight
