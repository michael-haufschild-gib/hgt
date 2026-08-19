import Mathlib

/-!
# Antidiagonal regrouping of a summable family on `ℕ × ℕ`

A summable family on `ℕ × ℕ` may be summed by antidiagonals.  This is the general form of the
step used in every Cauchy-product argument, stated for an arbitrary complete Hausdorff topological
additive group rather than only for products `f i * g j`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [T2Space α]

/-- **Antidiagonal regrouping.** -/
theorem tsum_sum_antidiagonal {T : ℕ × ℕ → α} (hT : Summable T) :
    ∑' n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, T p = ∑' p : ℕ × ℕ, T p := by
  have hsig : Summable fun x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
      T (x.2 : ℕ × ℕ) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hT
  have hfib : ∀ n : ℕ,
      Summable fun p : Finset.HasAntidiagonal.antidiagonal n => T (p : ℕ × ℕ) := fun n =>
    (hasSum_fintype _).summable
  have hsigma := hsig.tsum_sigma' hfib
  have hprod : ∑' x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n, T (x.2 : ℕ × ℕ)
      = ∑' p : ℕ × ℕ, T p :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq T
  calc ∑' n : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, T p
      = ∑' n : ℕ, ∑' p : Finset.HasAntidiagonal.antidiagonal n, T (p : ℕ × ℕ) := by
        refine tsum_congr fun n => ?_
        rw [tsum_fintype, Finset.sum_coe_sort]
    _ = ∑' x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n, T (x.2 : ℕ × ℕ) := hsigma.symm
    _ = ∑' p : ℕ × ℕ, T p := hprod

omit [T2Space α] in
/-- The antidiagonal sums of a summable family are summable. -/
theorem summable_sum_antidiagonal {T : ℕ × ℕ → α} (hT : Summable T) :
    Summable fun n : ℕ => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, T p := by
  have hsig : Summable fun x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
      T (x.2 : ℕ × ℕ) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hT
  have hfib : ∀ n : ℕ,
      Summable fun p : Finset.HasAntidiagonal.antidiagonal n => T (p : ℕ × ℕ) := fun n =>
    (hasSum_fintype _).summable
  have h := hsig.sigma' hfib
  refine h.congr fun n => ?_
  rw [tsum_fintype, Finset.sum_coe_sort]

end GaloisForLFunctions.HTGeometry
