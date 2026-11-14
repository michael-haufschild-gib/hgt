import GaloisForLFunctions.EisensteinDegeneration.PeriodImage
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Exact pole detection by a specialized matrix

A power-series matrix reflects divisibility by every power of the parameter
if and only if its reduction is injective. Equivalently, it detects every
pole in a family presented with a common finite denominator. This works
for rectangular matrices and requires no inverse over the fraction field.

The criterion isolates the special-fibre injectivity used in Polo–Rivero,
equation (5.13). The converse identifies precisely what generic injectivity
alone leaves uncontrolled.
-/

namespace GaloisForLFunctions.EisensteinDegeneration
open Matrix PowerSeries
noncomputable section
variable {K I J : Type*} [Field K] [Fintype J]

/-- Reduction commutes with the matrix action on an integral family. -/
theorem matrix_mulVec_constantCoeff (A : Matrix I J (PowerSeries K)) (f : J → PowerSeries K) :
    (fun i => constantCoeff ((A *ᵥ f) i)) =
      A.map constantCoeff *ᵥ (fun j => constantCoeff (f j)) := by
  classical
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map]

private theorem matrix_mulVec_factor (A : Matrix I J (PowerSeries K))
    (d : PowerSeries K) (f : J → PowerSeries K) :
    A *ᵥ (fun j => d * f j) = fun i => d * (A *ᵥ f) i :=
  Matrix.mulVec_smul A d f

/-- Injectivity on the special fibre is exactly reflection of every parameter-divisibility
condition. Generic injectivity alone does not imply this property. -/
theorem matrix_specialization_injective_iff (A : Matrix I J (PowerSeries K)) :
    Function.Injective (A.map constantCoeff).mulVec ↔
      ∀ (m : ℕ) (f : J → PowerSeries K),
        (∀ i, X ^ m ∣ (A *ᵥ f) i) ↔ ∀ j, X ^ m ∣ f j := by
  classical
  have preserve (d : PowerSeries K) (f : J → PowerSeries K)
      (hf : ∀ j, d ∣ f j) : ∀ i, d ∣ (A *ᵥ f) i := by
    choose g hg using hf
    have hfg : f = fun j => d * g j := funext hg
    rw [hfg, matrix_mulVec_factor]
    exact fun i => ⟨(A *ᵥ g) i, rfl⟩
  constructor
  · intro hinj m
    induction m with
    | zero => intro f; simp
    | succ m ih =>
      intro f
      refine ⟨?_, preserve (X ^ (m + 1)) f⟩
      intro hf
      have hprev : ∀ i, X ^ m ∣ (A *ᵥ f) i :=
        fun i => (pow_dvd_pow X (Nat.le_succ m)).trans (hf i)
      choose g hg using (ih f).mp hprev
      have hfg : f = fun j => X ^ m * g j := funext hg
      have hAg : ∀ i, X ∣ (A *ᵥ g) i := by
        intro i
        have hi := hf i
        rw [hfg, matrix_mulVec_factor, pow_succ] at hi
        exact (mul_dvd_mul_iff_left (pow_ne_zero m X_ne_zero)).mp hi
      have hzero : (fun j => constantCoeff (g j)) = 0 := by
        apply hinj
        rw [← matrix_mulVec_constantCoeff, Matrix.mulVec_zero]
        funext i
        exact X_dvd_iff.mp (hAg i)
      intro j
      obtain ⟨v, hv⟩ := X_dvd_iff.mpr (congrFun hzero j)
      refine ⟨v, ?_⟩
      rw [hg j, hv, pow_succ, mul_assoc]
  · intro h x y hxy
    have hz : (fun i => constantCoeff
        ((A *ᵥ (fun j => C (x j - y j))) i)) = 0 := by
      rw [matrix_mulVec_constantCoeff]
      simp only [constantCoeff_C]
      change A.map constantCoeff *ᵥ (x - y) = 0
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hd := (h 1 (fun j => C (x j - y j))).mp
      (fun i => by simpa only [pow_one, X_dvd_iff, Pi.zero_apply] using congrFun hz i)
    funext j
    have hj : constantCoeff (C (x j - y j)) = 0 :=
      X_dvd_iff.mp (by simpa only [pow_one] using hd j)
    simpa only [constantCoeff_C, sub_eq_zero] using hj

/-- Exact finite-pole criterion: a matrix detects every meromorphic pole precisely when
its reduction is injective. The matrix may be rectangular. -/
theorem matrix_regular_specialization_iff (A : Matrix I J (PowerSeries K)) :
    Function.Injective (A.map constantCoeff).mulVec ↔
      ∀ (m : ℕ) (f : J → PowerSeries K),
        (∀ i, Regular (HahnSeries.single (-(m : ℤ)) (1 : K) *
          (((A *ᵥ f) i : PowerSeries K) : LaurentSeries K))) ↔
        ∀ j, Regular (HahnSeries.single (-(m : ℤ)) (1 : K) *
          ((f j : PowerSeries K) : LaurentSeries K)) := by
  simpa only [regular_shift_iff] using matrix_specialization_injective_iff A

end
end GaloisForLFunctions.EisensteinDegeneration
