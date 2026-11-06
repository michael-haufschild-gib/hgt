import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanMomentCounts
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Differential and quadratic structure of the reciprocal torus locus

On the hyperplane `∑ xᵢ = 0`, the reciprocal equation is critical precisely when
the squares of the nonzero coordinates agree. Normalization makes these squares
one. Its quadratic pairing then has exactly the scaling direction as radical;
fixing the normalized coordinate removes that radical.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {K ι : Type*} [Field K] [Fintype ι]

/-- A covector vanishes on the sum-zero hyperplane exactly when it is constant. -/
theorem sum_zero_annihilator_iff (a : ι → K) (i₀ : ι) :
    (∀ v : ι → K, (∑ i, v i) = 0 → (∑ i, a i * v i) = 0) ↔
      ∀ i, a i = a i₀ := by
  classical
  constructor
  · intro h i
    have hv := h (fun j => (if j = i then 1 else 0) - (if j = i₀ then 1 else 0))
      (by simp [sum_sub_distrib])
    exact sub_eq_zero.mp (by simpa [mul_sub, mul_ite, sum_sub_distrib] using hv)
  · intro h v hv
    simp only [h, ← mul_sum, hv, mul_zero]

/-- The linear coefficient of the reciprocal equation along a line. -/
def reciprocalLinear (x v : ι → K) : K := -∑ i, (x i ^ 2)⁻¹ * v i

/-- The reciprocal differential is proportional to the hyperplane differential
exactly when all squared coordinates agree. -/
theorem reciprocal_critical_iff (x : ι → K) (i₀ : ι) :
    (∀ v : ι → K, (∑ i, v i) = 0 → reciprocalLinear x v = 0) ↔
      ∀ i, x i ^ 2 = x i₀ ^ 2 := by
  simp only [reciprocalLinear, neg_eq_zero]
  rw [sum_zero_annihilator_iff _ i₀]
  simp only [inv_inj]

/-- With one coordinate fixed to one, every critical coordinate is a sign. -/
theorem reciprocal_normalized_critical_iff (x : ι → K) (i₀ : ι) (h₀ : x i₀ = 1) :
    (∀ v : ι → K, (∑ i, v i) = 0 → reciprocalLinear x v = 0) ↔
      ∀ i, x i = 1 ∨ x i = -1 := by
  rw [reciprocal_critical_iff x i₀, h₀, one_pow]
  simp only [sq_eq_one_iff]

theorem reciprocalLinear_sub_scaling (x v w : ι → K) (c : K) :
    reciprocalLinear x (fun i => v i - c * w i) =
      reciprocalLinear x v - c * reciprocalLinear x w := by
  have h : (∑ i, (x i ^ 2)⁻¹ * (c * w i)) = c * ∑ i, (x i ^ 2)⁻¹ * w i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  simp only [reciprocalLinear, mul_sub, sum_sub_distrib, h]
  ring

/-- Euler's identity for the reciprocal equation in the radial direction. -/
theorem reciprocalLinear_radial (x : ι → K) (hx : ∀ i, x i ≠ 0) :
    reciprocalLinear x x = -∑ i, (x i)⁻¹ := by
  unfold reciprocalLinear
  congr 1
  apply sum_congr rfl
  intro i _
  rw [← inv_pow, pow_two, mul_assoc, inv_mul_cancel₀ (hx i), mul_one]

/-- On the double-zero locus, criticality in a normalized projective chart is
equivalent to all coordinates being signs. Euler's identity restores the radial direction. -/
theorem reciprocal_projective_critical_iff (x : ι → K) (i₀ : ι)
    (hx : ∀ i, x i ≠ 0) (h₀ : x i₀ = 1)
    (hs : (∑ i, x i) = 0) (hr : (∑ i, (x i)⁻¹) = 0) :
    (∀ v : ι → K, (∑ i, v i) = 0 → v i₀ = 0 → reciprocalLinear x v = 0) ↔
      ∀ i, x i = 1 ∨ x i = -1 := by
  constructor
  · intro h
    apply (reciprocal_normalized_critical_iff x i₀ h₀).mp
    intro v hv
    have ht := h (fun i => v i - v i₀ * x i)
      (by simp only [sum_sub_distrib, ← mul_sum, hv, hs, mul_zero, sub_self])
      (by rw [h₀, mul_one, sub_self])
    rwa [reciprocalLinear_sub_scaling, reciprocalLinear_radial x hx, hr,
      neg_zero, mul_zero, sub_zero] at ht
  · intro h v hv _
    exact (reciprocal_normalized_critical_iff x i₀ h₀).mpr h v hv

/-- The quadratic coefficient at a normalized critical point. -/
def reciprocalQuadratic (x v : ι → K) : K := ∑ i, x i * v i ^ 2

/-- The diagonal pairing associated to the reciprocal quadratic coefficient. -/
def reciprocalPairing (x v w : ι → K) : K := ∑ i, x i * v i * w i

/-- Polarization identifies the Hessian, including its factor of two. -/
theorem reciprocalQuadratic_polarization (x v w : ι → K) :
    reciprocalQuadratic x (v + w) - reciprocalQuadratic x v -
      reciprocalQuadratic x w = 2 * reciprocalPairing x v w := by
  simp only [reciprocalQuadratic, reciprocalPairing, Pi.add_apply,
    ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro i _
  ring

/-- The radical on the sum-zero hyperplane is exactly the scaling line. -/
theorem reciprocalPairing_radical_iff (x v : ι → K) (i₀ : ι)
    (hx : ∀ i, x i ^ 2 = 1) :
    (∀ w : ι → K, (∑ i, w i) = 0 → reciprocalPairing x v w = 0) ↔
      ∃ c : K, ∀ i, v i = c * x i := by
  simp only [reciprocalPairing]
  rw [sum_zero_annihilator_iff _ i₀]
  constructor
  · intro h
    refine ⟨x i₀ * v i₀, fun i => ?_⟩
    calc v i = x i * (x i * v i) := by rw [← mul_assoc, ← pow_two, hx, one_mul]
      _ = x i * (x i₀ * v i₀) := by rw [h i]
      _ = (x i₀ * v i₀) * x i := mul_comm _ _
  · rintro ⟨c, hc⟩ i
    rw [hc i, hc i₀]
    calc x i * (c * x i) = c * x i ^ 2 := by ring
      _ = c * x i₀ ^ 2 := by rw [hx i, hx i₀]
      _ = x i₀ * (c * x i₀) := by ring

/-- Fixing one normalized coordinate makes the quadratic pairing nondegenerate. -/
theorem reciprocalPairing_transverse_nondegenerate (x v : ι → K) (i₀ : ι)
    (hx : ∀ i, x i ^ 2 = 1) (h₀ : x i₀ = 1) (hs : (∑ i, x i) = 0)
    (hv : (∑ i, v i) = 0) (hv₀ : v i₀ = 0)
    (hvan : ∀ w : ι → K, (∑ i, w i) = 0 → w i₀ = 0 →
      reciprocalPairing x v w = 0) : v = 0 := by
  have hall : ∀ w : ι → K, (∑ i, w i) = 0 → reciprocalPairing x v w = 0 := by
    intro w hw
    have ht := hvan (fun i => w i - w i₀ * x i)
      (by simp only [sum_sub_distrib, ← mul_sum, hw, hs, mul_zero, sub_self])
      (by rw [h₀, mul_one, sub_self])
    have heq : reciprocalPairing x v (fun i => w i - w i₀ * x i) =
        reciprocalPairing x v w - w i₀ * ∑ i, v i := by
      simp only [reciprocalPairing, mul_sub, sum_sub_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i _
      calc x i * v i * (w i₀ * x i) = w i₀ * v i * x i ^ 2 := by ring
        _ = w i₀ * v i := by rw [hx, mul_one]
    rwa [heq, hv, mul_zero, sub_zero] at ht
  obtain ⟨c, hc⟩ := (reciprocalPairing_radical_iff x v i₀ hx).mp hall
  have hc0 : c = 0 := by simpa [h₀, hv₀] using (hc i₀).symm
  funext i
  simp [hc i, hc0]

/-- The reciprocal of a linear polynomial, expressed without convergence assumptions. -/
def reciprocalLineInverse (x v : K) : PowerSeries K :=
  PowerSeries.mk (fun n => x⁻¹ * (-(v * x⁻¹)) ^ n)

/-- The formal series is an actual inverse whenever the constant term is nonzero. -/
theorem reciprocalLineInverse_mul (x v : K) (hx : x ≠ 0) :
    (PowerSeries.C x + PowerSeries.C v * PowerSeries.X) * reciprocalLineInverse x v = 1 := by
  rw [add_mul, mul_assoc]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [reciprocalLineInverse, hx]
  | succ n =>
      simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
        reciprocalLineInverse, PowerSeries.coeff_mk, PowerSeries.coeff_one,
        Nat.succ_ne_zero, if_false]
      calc x * (x⁻¹ * (-(v * x⁻¹)) ^ (n + 1)) + v * (x⁻¹ * (-(v * x⁻¹)) ^ n)
          = (x * x⁻¹) * (-(v * x⁻¹)) ^ (n + 1) +
              (v * x⁻¹) * (-(v * x⁻¹)) ^ n := by ring
        _ = 0 := by rw [mul_inv_cancel₀ hx, one_mul, pow_succ]; ring

/-- The reciprocal equation restricted to a formal line through `x` in direction `v`. -/
def reciprocalSeries (x v : ι → K) : PowerSeries K :=
  ∑ i, reciprocalLineInverse (x i) (v i)

theorem reciprocalSeries_constant (x v : ι → K) :
    PowerSeries.coeff 0 (reciprocalSeries x v) = ∑ i, (x i)⁻¹ := by
  simp [reciprocalSeries, reciprocalLineInverse]

/-- The linear coefficient is the reciprocal differential. -/
theorem reciprocalSeries_linear (x v : ι → K) :
    PowerSeries.coeff 1 (reciprocalSeries x v) = reciprocalLinear x v := by
  simp only [reciprocalSeries, map_sum, reciprocalLineInverse, PowerSeries.coeff_mk,
    pow_one, reciprocalLinear, ← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  rw [← inv_pow]
  ring

private theorem inv_eq_self_of_sq_one {x : K} (hx : x ^ 2 = 1) : x⁻¹ = x := by
  have hne : x ≠ 0 := by intro h; simp [h] at hx
  calc x⁻¹ = x⁻¹ * (x * x) := by rw [← pow_two, hx, mul_one]
    _ = x := by rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- At a normalized critical point, the quadratic coefficient is the diagonal form. -/
theorem reciprocalSeries_quadratic (x v : ι → K) (hx : ∀ i, x i ^ 2 = 1) :
    PowerSeries.coeff 2 (reciprocalSeries x v) = reciprocalQuadratic x v := by
  simp only [reciprocalSeries, map_sum, reciprocalLineInverse, PowerSeries.coeff_mk,
    reciprocalQuadratic]
  apply sum_congr rfl
  intro i _
  rw [inv_eq_self_of_sq_one (hx i)]
  calc x i * (-(v i * x i)) ^ 2 = x i * v i ^ 2 * x i ^ 2 := by ring
    _ = x i * v i ^ 2 := by rw [hx i, mul_one]

/-- At a critical point of the double-zero locus the constant and linear terms vanish. -/
theorem reciprocalSeries_lower_terms_zero (x v : ι → K) (hx : ∀ i, x i ^ 2 = 1)
    (hs : (∑ i, x i) = 0) (hv : (∑ i, v i) = 0) :
    PowerSeries.coeff 0 (reciprocalSeries x v) = 0 ∧
      PowerSeries.coeff 1 (reciprocalSeries x v) = 0 := by
  constructor
  · rw [reciprocalSeries_constant]
    simpa only [fun i => inv_eq_self_of_sq_one (hx i)] using hs
  · rw [reciprocalSeries_linear]
    simp only [reciprocalLinear, hx, inv_one, one_mul, hv, neg_zero]

/-- In characteristic different from two, the actual transverse Hessian is nondegenerate. -/
theorem reciprocalHessian_transverse_nondegenerate (h₂ : (2 : K) ≠ 0)
    (x v : ι → K) (i₀ : ι) (hx : ∀ i, x i ^ 2 = 1)
    (h₀ : x i₀ = 1) (hs : (∑ i, x i) = 0)
    (hv : (∑ i, v i) = 0) (hv₀ : v i₀ = 0)
    (hvan : ∀ w : ι → K, (∑ i, w i) = 0 → w i₀ = 0 →
      PowerSeries.coeff 2 (reciprocalSeries x (v + w)) -
        PowerSeries.coeff 2 (reciprocalSeries x v) -
        PowerSeries.coeff 2 (reciprocalSeries x w) = 0) : v = 0 := by
  apply reciprocalPairing_transverse_nondegenerate x v i₀ hx h₀ hs hv hv₀
  intro w hw hw₀
  have h := hvan w hw hw₀
  simp only [reciprocalSeries_quadratic x _ hx, reciprocalQuadratic_polarization] at h
  exact (mul_eq_zero.mp h).resolve_left h₂

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The critical-point classification applies to the actual normalized tuples
whose point count occurs in the Kloosterman moment identity. -/
theorem normalizedDoubleZeroTorus_critical_iff {m : ℕ} (x : MomentTorus F m)
    (hx : x ∈ normalizedDoubleZeroTorus (F := F) m) :
    (∀ v : Fin (m + 1) → F, (∑ i, v i) = 0 → v 0 = 0 →
      reciprocalLinear (Fin.cons 1 (fun j => (x j : F))) v = 0) ↔
      ∀ j, (x j : F) = 1 ∨ (x j : F) = -1 := by
  have hs := (mem_filter.mp (mem_filter.mp hx).1).2
  have hr := (mem_filter.mp hx).2
  have hne : ∀ i : Fin (m + 1),
      (Fin.cons (1 : F) (fun j => (x j : F)) : Fin (m + 1) → F) i ≠ 0 := by
    intro i
    exact Fin.cases one_ne_zero (fun j => (x j).property) i
  rw [reciprocal_projective_critical_iff _ 0 hne rfl
    (by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hs)
    (by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, inv_one] using hr)]
  constructor
  · intro h j
    exact h j.succ
  · intro h i
    exact Fin.cases (Or.inl rfl) h i

end FiniteField

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
