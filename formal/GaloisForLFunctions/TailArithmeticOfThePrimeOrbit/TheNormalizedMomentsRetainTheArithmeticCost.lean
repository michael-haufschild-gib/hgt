import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PrimitiveLogarithmicSeparation
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheSmoothHeadNeedsNoDyadicRestriction
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanIntervalMeanSquare

/-!
# Normalize arithmetic tail moments by actual head mass

The reduced ratio height of a finite positive support gives logarithmic
separation. The Montgomery–Vaughan inequality therefore bounds actual
head mass below by `(2*T - 52*H)*R₂`, uniformly in the interval center.
At `T ≥ 52*H`, this mass is at least `T*R₂`.

Dividing the arithmetic prime-tail moments by this positive head mass
retains their explicit primitive collision cost. The same ratio height
bounds that cost by `2*Z*(Z+H)*R₁²`. The resulting normalized moment and
large-tail bounds include the full smooth head and prime tail.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.HTGeometry

/-- Reduced ratio height controls the full weighted primitive collision cost. -/
theorem primitiveHeadCost_le_supportHeight (A : Finset ℕ) (r : ℕ → ℂ) (Z : ℕ) :
    primitiveHeadCost A r Z ≤
      2 * (Z : ℝ) * (Z + primitiveSupportHeight A) * (∑ m ∈ A, ‖r m‖) ^ 2 := by
  calc
    _ ≤ ∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
        (2 * (Z : ℝ) * (Z + primitiveSupportHeight A)) :=
      sum_le_sum fun m hm => sum_le_sum fun n hn =>
        mul_le_mul_of_nonneg_left (primitiveProductCost_le_supportHeight hm hn Z)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [← sum_mul, ← mul_sum]
      ring

private def shiftedHeadCoefficient (r : ℕ → ℂ) (U : ℝ) (m : ℕ) : ℂ :=
  r m * Complex.exp (((U * Real.log m : ℝ) : ℂ) * Complex.I)

private theorem norm_shiftedHeadCoefficient (r : ℕ → ℂ) (U : ℝ) (m : ℕ) :
    ‖shiftedHeadCoefficient r U m‖ = ‖r m‖ := by
  rw [shiftedHeadCoefficient, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem mvExp_log (m : ℕ) (t : ℝ) :
    mvExp (Real.log m / (2 * Real.pi)) t =
      Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I) := by
  unfold mvExp
  congr 1
  push_cast
  field_simp

private theorem shiftedHead_sum (A : Finset ℕ) (r : ℕ → ℂ) (U t : ℝ) :
    (∑ m : A, shiftedHeadCoefficient r U m * mvExp (Real.log (m : ℕ) / (2 * Real.pi)) t) =
      headPoly A r (U+t) := by
  rw [Finset.sum_coe_sort A (fun m : ℕ =>
    shiftedHeadCoefficient r U m * mvExp (Real.log m / (2 * Real.pi)) t)]
  unfold headPoly
  apply sum_congr rfl
  intro m _
  rw [mvExp_log]
  dsimp only [shiftedHeadCoefficient]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The actual head mass has a lower bound at its reduced ratio scale, uniformly in the center. -/
theorem integral_head_sq_ge_primitiveSupportHeight {A : Finset ℕ}
    (hA : ∀ m ∈ A, 0 < m) (r : ℕ → ℂ) (U : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (2 * T - 52 * primitiveSupportHeight A) * (∑ m ∈ A, ‖r m‖ ^ 2) ≤
      ∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 := by
  classical
  let H := primitiveSupportHeight A
  have hH : (0 : ℝ) < H := by exact_mod_cast primitiveSupportHeight_pos A
  have hpi : 0 < 2 * Real.pi := by positivity
  have hD : 0 < 1 / (2 * Real.pi * H) := by positivity
  have hsep (m n : A) (hne : m ≠ n) :
      1 / (2 * Real.pi * H) ≤
        |Real.log (m : ℕ) / (2 * Real.pi) - Real.log (n : ℕ) / (2 * Real.pi)| := by
    have hmn : (m : ℕ) ≠ n := fun he => hne (Subtype.ext he)
    have hg := inv_primitiveSupportHeight_le_abs_log_sub_log hA m.property n.property hmn
    rw [← sub_div, abs_div, abs_of_pos hpi]
    have he : 1 / (2 * Real.pi * H) = (H : ℝ)⁻¹ / (2 * Real.pi) := by ring
    rw [he]
    exact div_le_div_of_nonneg_right hg hpi.le
  have h := interval_integral_normSq_expSum_ge
    (fun m : A => Real.log (m : ℕ) / (2 * Real.pi))
    (fun m : A => shiftedHeadCoefficient r U m)
    (a := -T) (ℓ := 2*T) hD hsep
  have he : 26 / (Real.pi * (1 / (2 * Real.pi * H))) = 52 * (H : ℝ) := by
    field_simp [Real.pi_ne_zero, hH.ne']; ring
  have ht : -T + 2*T = T := by ring
  simp only [he, ht, norm_shiftedHeadCoefficient, shiftedHead_sum] at h
  rw [Finset.sum_coe_sort A (fun m : ℕ => ‖r m‖ ^ 2)] at h
  rw [intervalIntegral.integral_of_le (by linarith only [hT] : -T ≤ T)] at h
  rw [← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- Above the explicit ratio threshold, head mass dominates its coefficient energy times height. -/
theorem integral_head_sq_ge_height_energy {A : Finset ℕ}
    (hA : ∀ m ∈ A, 0 < m) (r : ℕ → ℂ) (U : ℝ) {T : ℝ}
    (hT : 52 * (primitiveSupportHeight A : ℝ) ≤ T) :
    T * (∑ m ∈ A, ‖r m‖ ^ 2) ≤
      ∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 := by
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ 52 * (primitiveSupportHeight A : ℝ)).trans hT
  have h := integral_head_sq_ge_primitiveSupportHeight hA r U hT0
  have hE : 0 ≤ ∑ m ∈ A, ‖r m‖ ^ 2 := sum_nonneg fun m _ => sq_nonneg _
  exact (mul_le_mul_of_nonneg_right (by linarith only [hT]) hE).trans h

/-- The intrinsic head cost is nonnegative. -/
theorem primitiveHeadCost_nonneg (A : Finset ℕ) (r : ℕ → ℂ) (Z : ℕ) :
    0 ≤ primitiveHeadCost A r Z := by
  unfold primitiveHeadCost
  exact sum_nonneg fun m _ => sum_nonneg fun n _ => by
    unfold primitiveProductCost
    positivity

/-- Actual head normalization retains the explicit arithmetic error in every prime-tail moment. -/
theorem normalized_prime_tail_moment_le_primitive {y Y : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (hE : 0 < ∑ m ∈ A, ‖r m‖ ^ 2) (U : ℝ) {T : ℝ}
    (hT : 52 * (primitiveSupportHeight A : ℝ) ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 * ‖headPoly B b (U+t)‖ ^ (2*k)) /
        (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2) ≤
      (5 * Real.pi / 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k +
        primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2 /
          (T * ∑ m ∈ A, ‖r m‖ ^ 2)) := by
  have hH : (0 : ℝ) < primitiveSupportHeight A := by exact_mod_cast primitiveSupportHeight_pos A
  have hT0 : 0 < T := (by positivity : 0 < 52 * (primitiveSupportHeight A : ℝ)).trans_le hT
  have hfloor := integral_head_sq_ge_height_energy
    (fun m hm => Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hA m hm))) r U hT
  have hden := (mul_pos hT0 hE).trans_le hfloor
  have hC := primitiveHeadCost_nonneg A r (Y ^ k)
  have hbnd := integral_smooth_head_prime_tail_pow_le_primitive hA hB hY r b hb k U hT0
  calc
    _ ≤ ((5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2)) /
        (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2) :=
      div_le_div_of_nonneg_right hbnd hden.le
    _ ≤ ((5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2)) /
        (T * ∑ m ∈ A, ‖r m‖ ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hT0 hE) hfloor
    _ = _ := by field_simp [hT0.ne', hE.ne']

/-- Reduced support height gives a coefficient-only normalized moment bound. -/
theorem normalized_prime_tail_moment_le_supportHeight {y Y : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (hE : 0 < ∑ m ∈ A, ‖r m‖ ^ 2) (U : ℝ) {T : ℝ}
    (hT : 52 * (primitiveSupportHeight A : ℝ) ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 * ‖headPoly B b (U+t)‖ ^ (2*k)) /
        (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2) ≤
      (5 * Real.pi / 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k +
        2 * (Y : ℝ) ^ k * ((Y : ℝ) ^ k + primitiveSupportHeight A) *
          (∑ m ∈ A, ‖r m‖) ^ 2 * (k.factorial : ℝ) ^ 2 /
            (T * ∑ m ∈ A, ‖r m‖ ^ 2)) := by
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ 52 * (primitiveSupportHeight A : ℝ)).trans hT
  apply (normalized_prime_tail_moment_le_primitive hA hB hY r b hb k hE U hT).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  have h := primitiveHeadCost_le_supportHeight A r (Y ^ k)
  simp only [Nat.cast_pow] at h
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (sq_nonneg _)) (mul_nonneg hT0 hE.le)

/-- Normalized large-tail mass is controlled by the same intrinsic finite-moment error. -/
theorem normalized_large_prime_tail_mass_le {y Y : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (hE : 0 < ∑ m ∈ A, ‖r m‖ ^ 2) (U : ℝ) {T V : ℝ}
    (hT : 52 * (primitiveSupportHeight A : ℝ) ≤ T) (hV : 0 < V) :
    (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖headPoly B b (U+t)‖}, ‖headPoly A r (U+t)‖ ^ 2) /
        (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2) ≤
      ((5 * Real.pi / 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k +
        primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2 /
          (T * ∑ m ∈ A, ‖r m‖ ^ 2))) / V ^ (2*k) := by
  have hH : (0 : ℝ) < primitiveSupportHeight A := by exact_mod_cast primitiveSupportHeight_pos A
  have hT0 : 0 < T := (by positivity : 0 < 52 * (primitiveSupportHeight A : ℝ)).trans_le hT
  have hfloor := integral_head_sq_ge_height_energy
    (fun m hm => Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hA m hm))) r U hT
  have hden := (mul_pos hT0 hE).trans_le hfloor
  have hC := primitiveHeadCost_nonneg A r (Y ^ k)
  have hbnd := setIntegral_smooth_head_on_large_prime_tail_le hA hB hY r b hb k U hT0 hV
  calc
    _ ≤ (((5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2)) / V ^ (2*k)) /
        (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2) :=
      div_le_div_of_nonneg_right hbnd hden.le
    _ ≤ (((5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2)) / V ^ (2*k)) /
        (T * ∑ m ∈ A, ‖r m‖ ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hT0 hE) hfloor
    _ = _ := by field_simp [hT0.ne', hE.ne', hV.ne']

/-- The full smooth head and prime tail have an explicit normalized finite-moment bound. -/
theorem normalized_full_smooth_prime_tail_moment_le {M : ℕ} (hM : 1 ≤ M)
    (y Y k : ℕ) (U : ℝ) {T : ℝ} (hT : 52 * (M : ℝ) ≤ T) :
    let A := (Icc 1 M).filter fun m => m ∈ Nat.smoothNumbers y
    let B := (Icc y Y).filter Nat.Prime
    (∫ t in Set.Icc (-T) T, ‖headPoly A (fun _ => 1) (U+t)‖ ^ 2 *
        ‖headPoly B (fun _ => 1) (U+t)‖ ^ (2*k)) /
      (∫ t in Set.Icc (-T) T, ‖headPoly A (fun _ => 1) (U+t)‖ ^ 2) ≤
      (5 * Real.pi / 2) * ((k.factorial : ℝ) * (B.card : ℝ) ^ k +
        2 * (Y : ℝ) ^ k * ((Y : ℝ) ^ k + M) * A.card * (k.factorial : ℝ) ^ 2 / T) := by
  dsimp only
  let A := (Icc 1 M).filter fun m => m ∈ Nat.smoothNumbers y
  let B := (Icc y Y).filter Nat.Prime
  have hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y := fun m hm => (mem_filter.mp hm).2
  have hB : ∀ p ∈ B, p.Prime ∧ y ≤ p := fun p hp =>
    ⟨(mem_filter.mp hp).2, (mem_Icc.mp (mem_filter.mp hp).1).1⟩
  have hY : ∀ p ∈ B, p ≤ Y := fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2
  have hH : primitiveSupportHeight A ≤ M :=
    primitiveSupportHeight_le hM (fun m hm => (mem_Icc.mp (mem_filter.mp hm).1).2)
  have hHR : (primitiveSupportHeight A : ℝ) ≤ M := by exact_mod_cast hH
  have hcut : 52 * (primitiveSupportHeight A : ℝ) ≤ T :=
    (mul_le_mul_of_nonneg_left hHR (by norm_num)).trans hT
  have hcard : 0 < A.card := card_pos.mpr ⟨1, by simp [A, hM, Nat.smoothNumbers]⟩
  have hcardR : (0 : ℝ) < A.card := by exact_mod_cast hcard
  have hE : 0 < ∑ m ∈ A, ‖(1 : ℂ)‖ ^ 2 := by
    simpa only [norm_one, one_pow, sum_const, nsmul_eq_mul, mul_one] using hcardR
  have hT0 : 0 < T := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith only [hT, hMR]
  have h := normalized_prime_tail_moment_le_supportHeight hA hB hY
    (fun _ => 1) (fun _ => 1) (by intro p hp; simp) k hE U hcut
  simp only [norm_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
  have he : 2 * (Y : ℝ) ^ k * ((Y : ℝ) ^ k + primitiveSupportHeight A) *
        (A.card : ℝ) ^ 2 * (k.factorial : ℝ) ^ 2 / (T * A.card) =
      2 * (Y : ℝ) ^ k * ((Y : ℝ) ^ k + primitiveSupportHeight A) *
        A.card * (k.factorial : ℝ) ^ 2 / T := by
    field_simp [hT0.ne', hcardR.ne']
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ hT0.le
  have hh : 2 * (Y : ℝ) ^ k * ((Y : ℝ) ^ k + primitiveSupportHeight A) ≤
      2 * (Y : ℝ) ^ k * ((Y : ℝ) ^ k + M) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hHR) (by positivity)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg A.card)) (sq_nonneg _)

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
