import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.ProportionalSavingIsAHeavyFirstReturn

/-!
# Absolute large values force heavy returns

A large complex modulus aligns phases around an arbitrary common angle.
A bounded integer dilation returns that angle to zero. The resulting defect
bound and the measure transfer have constants independent of the number of
frequencies and of the nonnegative weights.
-/

open Real Finset MeasureTheory

namespace GaloisForLFunctions.CollectiveDiophantineGeometry

open TailArithmeticOfThePrimeOrbit

noncomputable section

variable {ι : Type*}

/-- The complex column with nonnegative arithmetic weights. -/
def phaseSum (s : Finset ι) (a ℓ : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ s, (a i : ℂ) * Complex.exp ((t * ℓ i : ℝ) * Complex.I)

private theorem phaseSum_re (s : Finset ι) (a ℓ : ι → ℝ) (t : ℝ) :
    (phaseSum s a ℓ t).re = ∑ i ∈ s, a i * cos (t * ℓ i) := by
  simp [phaseSum, Complex.mul_re, Complex.exp_re]

private theorem phaseSum_im (s : Finset ι) (a ℓ : ι → ℝ) (t : ℝ) :
    (phaseSum s a ℓ t).im = ∑ i ∈ s, a i * sin (t * ℓ i) := by
  simp [phaseSum, Complex.mul_im, Complex.exp_im]

/-- Reversing height conjugates the column, since all weights and frequencies are real. -/
theorem phaseSum_neg (s : Finset ι) (a ℓ : ι → ℝ) (t : ℝ) :
    phaseSum s a ℓ (-t) = (starRingEnd ℂ) (phaseSum s a ℓ t) := by
  apply Complex.ext
  · simp only [phaseSum_re, Complex.conj_re, neg_mul, cos_neg]
  · simp only [phaseSum_im, Complex.conj_im, neg_mul, sin_neg, mul_neg,
      Finset.sum_neg_distrib]

/-- Both signs in the Dirichlet-polynomial convention have the same modulus. -/
theorem phaseSum_norm_neg (s : Finset ι) (a ℓ : ι → ℝ) (t : ℝ) :
    ‖phaseSum s a ℓ (-t)‖ = ‖phaseSum s a ℓ t‖ := by
  rw [phaseSum_neg, Complex.norm_conj]

/-- The modulus never exceeds the total weight. -/
theorem phaseSum_norm_le {s : Finset ι} {a ℓ : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (t : ℝ) :
    ‖phaseSum s a ℓ t‖ ≤ weightedSize s a := by
  unfold phaseSum weightedSize
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i hi), Complex.norm_exp]
  simp

private theorem rotated_column (s : Finset ι) (a ℓ : ι → ℝ) (t : ℝ) :
    (∑ i ∈ s, a i * cos (t * ℓ i - (phaseSum s a ℓ t).arg)) =
      ‖phaseSum s a ℓ t‖ := by
  calc
    _ = (∑ i ∈ s, a i * cos (t * ℓ i)) * cos (phaseSum s a ℓ t).arg +
        (∑ i ∈ s, a i * sin (t * ℓ i)) * sin (phaseSum s a ℓ t).arg := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [cos_sub]
      ring
    _ = ‖phaseSum s a ℓ t‖ *
        (sin (phaseSum s a ℓ t).arg ^ 2 + cos (phaseSum s a ℓ t).arg ^ 2) := by
      rw [← phaseSum_re, ← phaseSum_im,
        ← Complex.norm_mul_cos_arg (phaseSum s a ℓ t),
        ← Complex.norm_mul_sin_arg (phaseSum s a ℓ t)]
      ring
    _ = _ := by rw [sin_sq_add_cos_sq, mul_one]

/-- Rotation by the column's argument turns its modulus deficit into an exact
weighted cosine defect, including when the column vanishes. -/
theorem rotated_defect (s : Finset ι) (a ℓ : ι → ℝ) (t : ℝ) :
    (∑ i ∈ s, a i * (1 - cos (t * ℓ i - (phaseSum s a ℓ t).arg))) =
      weightedSize s a - ‖phaseSum s a ℓ t‖ := by
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, rotated_column, weightedSize]

private theorem one_sub_cos_add_bound (x y : ℝ) :
    1 - cos (x + y) ≤ 2 * (1 - cos x) + 2 * (1 - cos y) := by
  have h := pow_le_pow_left₀ (sqrt_nonneg _) (sqrt_one_sub_cos_add_le x y) 2
  have hx : 0 ≤ 1 - cos x := sub_nonneg.mpr (cos_le_one x)
  have hy : 0 ≤ 1 - cos y := sub_nonneg.mpr (cos_le_one y)
  have hxy : 0 ≤ 1 - cos (x + y) := sub_nonneg.mpr (cos_le_one (x + y))
  rw [sq_sqrt hxy] at h
  nlinarith only [h, sq_sqrt hx, sq_sqrt hy,
    sq_nonneg (sqrt (1 - cos x) - sqrt (1 - cos y))]

private theorem one_sub_cos_nat_mul_bound (m : ℕ) (x : ℝ) :
    1 - cos (m * x) ≤ (m : ℝ) ^ 2 * (1 - cos x) := by
  have h : IsReturn ({()} : Finset Unit) (fun _ => x) (1 - cos x) 1 := by
    simp [IsReturn]
  have hn := h.nat_mul (sub_nonneg.mpr (cos_le_one x)) m
  simpa using hn () (by simp)

private theorem one_sub_cos_mul_split (m : ℕ) (x θ : ℝ) :
    1 - cos (m * x) ≤
      2 * (m : ℝ) ^ 2 * (1 - cos (x - θ)) + 2 * (1 - cos (m * θ)) := by
  have h := one_sub_cos_add_bound (m * (x - θ)) (m * θ)
  rw [show (m : ℝ) * (x - θ) + m * θ = m * x by ring] at h
  calc
    _ ≤ 2 * (1 - cos (m * (x - θ))) + 2 * (1 - cos (m * θ)) := h
    _ ≤ _ := by
      have hn := mul_le_mul_of_nonneg_left (one_sub_cos_nat_mul_bound m (x - θ))
        (show (0 : ℝ) ≤ 2 by norm_num)
      simpa only [mul_assoc] using add_le_add hn (le_refl (2 * (1 - cos (m * θ))))

/-- Some bounded integer dilation has a small defect. Only the common angle
needs Dirichlet approximation, so the loss is independent of dimension. -/
theorem exists_dilation_defect_le {s : Finset ι} {a ℓ : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {Q : ℕ} (hQ : 1 ≤ Q) (t : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ Q ∧
      weightedDefect s a ℓ (m * t) ≤
        2 * (Q : ℝ) ^ 2 * (weightedSize s a - ‖phaseSum s a ℓ t‖) +
          (4 * π ^ 2 / (Q : ℝ) ^ 2) * weightedSize s a := by
  obtain ⟨m, hm1, hmQ, hm⟩ := HTGeometry.exists_dirichlet_phase
    (fun _ : Unit => (phaseSum s a ℓ t).arg) 1 Q hQ
  simp only [Fintype.card_unit, pow_one] at hmQ
  have hangle : 1 - cos ((m : ℝ) * (phaseSum s a ℓ t).arg) ≤
      2 * π ^ 2 / (Q : ℝ) ^ 2 := by
    have h := (hm ()).1
    simp only [mul_one] at h
    rw [mul_comm (phaseSum s a ℓ t).arg (m : ℝ)] at h
    linarith only [h]
  have hS : 0 ≤ weightedSize s a := Finset.sum_nonneg ha
  have hE : 0 ≤ weightedSize s a - ‖phaseSum s a ℓ t‖ :=
    sub_nonneg.mpr (phaseSum_norm_le ha t)
  have hmq : (m : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hmQ) 2
  refine ⟨m, hm1, hmQ, ?_⟩
  have hs := Finset.sum_le_sum (s := s) (fun i hi =>
    mul_le_mul_of_nonneg_left
      (one_sub_cos_mul_split m (t * ℓ i) (phaseSum s a ℓ t).arg) (ha i hi))
  have hsum :
      (∑ i ∈ s, a i * (2 * (m : ℝ) ^ 2 *
        (1 - cos (t * ℓ i - (phaseSum s a ℓ t).arg)) +
          2 * (1 - cos ((m : ℝ) * (phaseSum s a ℓ t).arg)))) =
        2 * (m : ℝ) ^ 2 * (weightedSize s a - ‖phaseSum s a ℓ t‖) +
          2 * (1 - cos ((m : ℝ) * (phaseSum s a ℓ t).arg)) * weightedSize s a := by
    rw [← rotated_defect s a ℓ t]
    simp only [weightedSize, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum] at hs
  have hleft : (∑ i ∈ s, a i * (1 - cos ((m : ℝ) * (t * ℓ i)))) =
      weightedDefect s a ℓ (m * t) := by simp only [weightedDefect, mul_assoc]
  rw [hleft] at hs
  refine hs.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmq (by norm_num)) hE
  · apply mul_le_mul_of_nonneg_right _ hS
    calc
      2 * (1 - cos ((m : ℝ) * (phaseSum s a ℓ t).arg)) ≤
          2 * (2 * π ^ 2 / (Q : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hangle (by norm_num)
      _ = 4 * π ^ 2 / (Q : ℝ) ^ 2 := by ring

/-- Defect loss when the common phase is returned by a dilation at most `Q`. -/
def dilationLoss (Q : ℕ) (c : ℝ) : ℝ :=
  2 * (Q : ℝ) ^ 2 * c + 4 * π ^ 2 / (Q : ℝ) ^ 2

/-- Heights whose complex column loses less than the fraction `c` of its size. -/
def absoluteLargeSet (s : Finset ι) (a ℓ : ι → ℝ) (c : ℝ) : Set ℝ :=
  {t | (1 - c) * weightedSize s a < ‖phaseSum s a ℓ t‖}

/-- Heights returning a subset with more than the fraction `1-κ` of the weight.
The phase precision `η` is measured by `1-cos`, not in radians. -/
def heavyReturnSet (s : Finset ι) (a ℓ : ι → ℝ) (η κ : ℝ) : Set ℝ :=
  {t | ∃ H ⊆ s, IsReturn H ℓ η t ∧
    (1 - κ) * weightedSize s a < ∑ i ∈ H, a i}

/-- Absolute large values form an open set of heights. -/
theorem isOpen_absoluteLargeSet (s : Finset ι) (a ℓ : ι → ℝ) (c : ℝ) :
    IsOpen (absoluteLargeSet s a ℓ c) := by
  apply isOpen_lt continuous_const
  unfold phaseSum
  fun_prop

/-- A heavy-return event is a finite union of closed phase-condition sets. -/
theorem isClosed_heavyReturnSet (s : Finset ι) (a ℓ : ι → ℝ) (η κ : ℝ) :
    IsClosed (heavyReturnSet s a ℓ η κ) := by
  classical
  have heq : heavyReturnSet s a ℓ η κ =
      ⋃ H ∈ s.powerset.filter (fun H =>
        (1 - κ) * weightedSize s a < ∑ i ∈ H, a i), {t | IsReturn H ℓ η t} := by
    ext t
    simp only [heavyReturnSet, Set.mem_setOf_eq, Set.mem_iUnion, mem_filter, mem_powerset]
    aesop
  rw [heq]
  apply isClosed_biUnion_finset
  intro H hH
  simp only [IsReturn, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun hi =>
    isClosed_le (continuous_const.sub (continuous_cos.comp
      (continuous_id.mul continuous_const))) continuous_const

/-- The large-modulus event is covered by bounded dilation preimages of actual
heavy returns. No arithmetic return estimate is assumed. -/
theorem absoluteLargeSet_subset_dilated_returns {s : Finset ι} {a ℓ : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {Q : ℕ} (hQ : 1 ≤ Q) {η : ℝ} (hη : 0 < η) (c : ℝ) :
    absoluteLargeSet s a ℓ c ⊆
      ⋃ m ∈ Icc 1 Q, (fun t : ℝ => (m : ℝ) * t) ⁻¹'
        heavyReturnSet s a ℓ η (dilationLoss Q c / η) := by
  classical
  intro t ht
  obtain ⟨m, hm1, hmQ, hD⟩ := exists_dilation_defect_le ha hQ t
  have hE : weightedSize s a - ‖phaseSum s a ℓ t‖ < c * weightedSize s a := by
    have hlarge : (1 - c) * weightedSize s a < ‖phaseSum s a ℓ t‖ := ht
    nlinarith only [hlarge]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hstrict : weightedDefect s a ℓ (m * t) < dilationLoss Q c * weightedSize s a := by
    calc
      _ ≤ 2 * (Q : ℝ) ^ 2 * (weightedSize s a - ‖phaseSum s a ℓ t‖) +
          (4 * π ^ 2 / (Q : ℝ) ^ 2) * weightedSize s a := hD
      _ < 2 * (Q : ℝ) ^ 2 * (c * weightedSize s a) +
          (4 * π ^ 2 / (Q : ℝ) ^ 2) * weightedSize s a :=
        add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hE (show 0 < 2 * (Q : ℝ) ^ 2 by positivity)) le_rfl
      _ = _ := by unfold dilationLoss; ring
  obtain ⟨H, hHs, hret, hmass⟩ := exists_heavy_return_of_defect_lt ha hη hstrict
  exact Set.mem_iUnion₂.mpr ⟨m, mem_Icc.mpr ⟨hm1, hmQ⟩, H, hHs, hret, hmass⟩

/-- Return measure controls the measure of absolute large values. The interval
expands by `Q`, while the measure cost is only the harmonic sum `Σ_{m≤Q}1/m`.
Both costs are independent of the number of prime coordinates. -/
theorem absoluteLargeSet_measure_le_returns {s : Finset ι} {a ℓ : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {Q : ℕ} (hQ : 1 ≤ Q) {η : ℝ} (hη : 0 < η)
    (c : ℝ) {A B : ℝ} (hA : 0 ≤ A) :
    volume (Set.Icc A B ∩ absoluteLargeSet s a ℓ c) ≤
      ENNReal.ofReal (∑ m ∈ Icc 1 Q, (m : ℝ)⁻¹) *
        volume (Set.Icc A ((Q : ℝ) * B) ∩
          heavyReturnSet s a ℓ η (dilationLoss Q c / η)) := by
  have hcover : Set.Icc A B ∩ absoluteLargeSet s a ℓ c ⊆
      ⋃ m ∈ Icc 1 Q, (fun t : ℝ => (m : ℝ) * t) ⁻¹'
        (Set.Icc A ((Q : ℝ) * B) ∩ heavyReturnSet s a ℓ η (dilationLoss Q c / η)) := by
    intro t ht
    obtain ⟨m, hm, hret⟩ := Set.mem_iUnion₂.mp
      (absoluteLargeSet_subset_dilated_returns ha hQ hη c ht.2)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have ht0 : 0 ≤ t := hA.trans ht.1.1
    have hB0 : 0 ≤ B := ht0.trans ht.1.2
    refine Set.mem_iUnion₂.mpr ⟨m, hm, ⟨⟨?_, ?_⟩, hret⟩⟩
    · exact ht.1.1.trans (le_mul_of_one_le_left ht0 hm1)
    · exact (mul_le_mul_of_nonneg_left ht.1.2 hm0).trans
        (mul_le_mul_of_nonneg_right hmQ hB0)
  calc
    _ ≤ volume (⋃ m ∈ Icc 1 Q, (fun t : ℝ => (m : ℝ) * t) ⁻¹'
        (Set.Icc A ((Q : ℝ) * B) ∩ heavyReturnSet s a ℓ η (dilationLoss Q c / η))) :=
      measure_mono hcover
    _ ≤ ∑ m ∈ Icc 1 Q, volume ((fun t : ℝ => (m : ℝ) * t) ⁻¹'
        (Set.Icc A ((Q : ℝ) * B) ∩ heavyReturnSet s a ℓ η (dilationLoss Q c / η))) :=
      measure_biUnion_finset_le _ _
    _ = ∑ m ∈ Icc 1 Q, ENNReal.ofReal ((m : ℝ)⁻¹) *
        volume (Set.Icc A ((Q : ℝ) * B) ∩
          heavyReturnSet s a ℓ η (dilationLoss Q c / η)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
      rw [Real.volume_preimage_mul_left hm0.ne', abs_of_pos (inv_pos.mpr hm0)]
    _ = _ := by
      rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun m hm => by positivity)]

/-- Dilation range sufficient for prescribed cosine precision and missing mass. -/
def returnDilation (η κ : ℝ) : ℕ := ⌈sqrt (8 * π ^ 2 / (κ * η))⌉₊ + 1

/-- Absolute-modulus saving corresponding to the prescribed heavy-return parameters. -/
def modulusSaving (η κ : ℝ) : ℝ :=
  κ * η / (4 * (returnDilation η κ : ℝ) ^ 2)

theorem one_le_returnDilation (η κ : ℝ) : 1 ≤ returnDilation η κ := by
  unfold returnDilation
  omega

private theorem returnDilation_pos (η κ : ℝ) : 0 < (returnDilation η κ : ℝ) := by
  exact_mod_cast one_le_returnDilation η κ

private theorem returnDilation_budget {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    8 * π ^ 2 ≤ κ * η * (returnDilation η κ : ℝ) ^ 2 := by
  have hr : sqrt (8 * π ^ 2 / (κ * η)) < (returnDilation η κ : ℝ) := by
    unfold returnDilation
    push_cast
    exact (Nat.le_ceil _).trans_lt (lt_add_one _)
  have hs := pow_le_pow_left₀ (sqrt_nonneg _) hr.le 2
  rw [sq_sqrt (by positivity)] at hs
  have h := (div_le_iff₀ (mul_pos hκ hη)).mp hs
  nlinarith only [h]

/-- A positive saving, uniform in every frequency family and every choice of weights. -/
theorem modulusSaving_pos {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    0 < modulusSaving η κ := by
  unfold modulusSaving
  have hQ := returnDilation_pos η κ
  positivity

private theorem prescribed_dilation_loss {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    dilationLoss (returnDilation η κ) (modulusSaving η κ) / η ≤ κ := by
  have hQ := returnDilation_pos η κ
  have hb := returnDilation_budget hη hκ
  have hangle : 4 * π ^ 2 / (returnDilation η κ : ℝ) ^ 2 ≤ κ * η / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hQ)).mpr
    nlinarith only [hb]
  have hspread : 2 * (returnDilation η κ : ℝ) ^ 2 * modulusSaving η κ = κ * η / 2 := by
    unfold modulusSaving
    field_simp [hQ.ne']
    norm_num
  apply (div_le_iff₀ hη).mpr
  rw [dilationLoss, hspread]
  linarith only [hangle]

private theorem heavyReturnSet_mono {s : Finset ι} {a ℓ : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (η : ℝ) {κ₁ κ₂ : ℝ} (hκ : κ₁ ≤ κ₂) :
    heavyReturnSet s a ℓ η κ₁ ⊆ heavyReturnSet s a ℓ η κ₂ := by
  rintro t ⟨H, hHs, hret, hmass⟩
  refine ⟨H, hHs, hret, lt_of_le_of_lt ?_ hmass⟩
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left hκ 1) (Finset.sum_nonneg ha)

/-- Prescribed precision and missing mass give a dimension-independent positive
modulus saving and a bounded dilation cover of its large-value event. -/
theorem absoluteLargeSet_subset_heavy_dilations {s : Finset ι} {a ℓ : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    absoluteLargeSet s a ℓ (modulusSaving η κ) ⊆
      ⋃ m ∈ Icc 1 (returnDilation η κ), (fun t : ℝ => (m : ℝ) * t) ⁻¹'
        heavyReturnSet s a ℓ η κ := by
  have hcover := absoluteLargeSet_subset_dilated_returns (s := s) (a := a) (ℓ := ℓ)
    ha (one_le_returnDilation η κ) hη (modulusSaving η κ)
  have hmono : heavyReturnSet s a ℓ η
      (dilationLoss (returnDilation η κ) (modulusSaving η κ) / η) ⊆
        heavyReturnSet s a ℓ η κ :=
    heavyReturnSet_mono (s := s) (a := a) (ℓ := ℓ) ha η
      (prescribed_dilation_loss hη hκ)
  intro t ht
  obtain ⟨m, hm, hret⟩ := Set.mem_iUnion₂.mp (hcover ht)
  exact Set.mem_iUnion₂.mpr ⟨m, hm, hmono hret⟩

/-- A return-measure bound at any prescribed positive precision and missing-mass
fraction controls absolute large values with explicit constants uniform in dimension. -/
theorem absoluteLargeSet_measure_le_heavy_returns {s : Finset ι} {a ℓ : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ)
    {A B : ℝ} (hA : 0 ≤ A) :
    volume (Set.Icc A B ∩ absoluteLargeSet s a ℓ (modulusSaving η κ)) ≤
      ENNReal.ofReal (∑ m ∈ Icc 1 (returnDilation η κ), (m : ℝ)⁻¹) *
        volume (Set.Icc A ((returnDilation η κ : ℝ) * B) ∩ heavyReturnSet s a ℓ η κ) := by
  refine (absoluteLargeSet_measure_le_returns ha (one_le_returnDilation η κ)
    hη (modulusSaving η κ) hA).trans ?_
  apply mul_le_mul_right
  apply measure_mono
  exact Set.inter_subset_inter_right _
    (heavyReturnSet_mono (s := s) (a := a) (ℓ := ℓ) ha η (prescribed_dilation_loss hη hκ))

/-- At every cutoff and height, the logarithmically weighted prime polynomial
has a fixed proportional modulus saving, or a bounded multiple of the height
returns more than the prescribed fraction of the actual prime mass. -/
theorem prime_modulus_or_heavy_return (y : ℕ) {η κ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (t : ℝ) :
    ‖∑ p ∈ Nat.primesLE y, (log p : ℂ) *
        Complex.exp (-((t * log p : ℝ) : ℂ) * Complex.I)‖ ≤
        (1 - modulusSaving η κ) * Chebyshev.theta y ∨
      ∃ m ∈ Icc 1 (returnDilation η κ), ∃ H ⊆ Nat.primesLE y,
        IsReturn H (fun p => log p) η ((m : ℝ) * t) ∧
          (1 - κ) * Chebyshev.theta y < ∑ p ∈ H, log p := by
  have ha : ∀ p ∈ Nat.primesLE y, 0 ≤ log (p : ℝ) := by
    intro p hp
    apply log_nonneg
    exact_mod_cast (Nat.one_lt_of_mem_primesLE hp).le
  have htheta : weightedSize (Nat.primesLE y) (fun p => log p) = Chebyshev.theta y :=
    (Chebyshev.theta_eq_sum_primesLE_log y).symm
  have hnorm :
      ‖∑ p ∈ Nat.primesLE y, (log p : ℂ) *
        Complex.exp (-((t * log p : ℝ) : ℂ) * Complex.I)‖ =
      ‖phaseSum (Nat.primesLE y) (fun p => log p) (fun p => log p) t‖ := by
    rw [← phaseSum_norm_neg]
    simp only [phaseSum, neg_mul, Complex.ofReal_neg]
  by_cases hs : ‖phaseSum (Nat.primesLE y) (fun p => log p) (fun p => log p) t‖ ≤
      (1 - modulusSaving η κ) * weightedSize (Nat.primesLE y) (fun p => log p)
  · exact Or.inl (by simpa only [hnorm, htheta] using hs)
  · have hlarge : t ∈ absoluteLargeSet (Nat.primesLE y)
        (fun p => log p) (fun p => log p) (modulusSaving η κ) := lt_of_not_ge hs
    obtain ⟨m, hm, H, hHs, hret, hmass⟩ := Set.mem_iUnion₂.mp
      (absoluteLargeSet_subset_heavy_dilations ha hη hκ hlarge)
    exact Or.inr ⟨m, hm, H, hHs, hret, by simpa only [htheta] using hmass⟩

end
end GaloisForLFunctions.CollectiveDiophantineGeometry
