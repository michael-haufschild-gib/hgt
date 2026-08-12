import GaloisForLFunctions.RHTower.Sieve.MaynardDefectExcision

/-!
# Multiplicative propagation of one factor deficit

A power saving on one distinguished factor propagates through a finite product whose other
factors obey their trivial multiplicative thresholds.  If the distinguished constant is absorbed
by that saving, the full product cannot attain its trivial threshold.
-/

noncomputable section
namespace RHTower.Sieve

open Finset

theorem norm_fintype_prod_le_distinguished_defect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ℝ) (z : ι → ℂ) (e δ C : ℝ) (j : ι)
    (hA : ∀ i, 0 < A i)
    (hj : ‖z j‖ ≤ C * (A j) ^ e * (A j) ^ (-δ))
    (hother : ∀ i, i ≠ j → ‖z i‖ ≤ (A i) ^ e) :
    ‖∏ i, z i‖ ≤ C * (∏ i, A i) ^ e * (A j) ^ (-δ) := by
  let u : Finset ι := Finset.univ.erase j
  have hjmem : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ j
  have hprodZ : (∏ i, z i) = z j * ∏ i ∈ u, z i := by
    rw [show (∏ i, z i) = ∏ i ∈ (Finset.univ : Finset ι), z i by simp]
    rw [Finset.mul_prod_erase Finset.univ z hjmem]
  have hprodA : (∏ i, A i) = A j * ∏ i ∈ u, A i := by
    rw [show (∏ i, A i) = ∏ i ∈ (Finset.univ : Finset ι), A i by simp]
    rw [Finset.mul_prod_erase Finset.univ A hjmem]
  have hotherProd : ‖∏ i ∈ u, z i‖ ≤ ∏ i ∈ u, (A i) ^ e := by
    rw [Complex.norm_prod]
    apply Finset.prod_le_prod
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      apply hother i
      simpa [u] using hi
  have hAu : 0 ≤ ∏ i ∈ u, A i :=
    Finset.prod_nonneg fun i _ => (hA i).le
  have hrpow : ∏ i ∈ u, (A i) ^ e = (∏ i ∈ u, A i) ^ e :=
    Real.finsetProd_rpow u A (fun i _ => (hA i).le) e
  rw [hprodZ, norm_mul]
  calc
    ‖z j‖ * ‖∏ i ∈ u, z i‖
        ≤ ‖z j‖ * ∏ i ∈ u, (A i) ^ e :=
      mul_le_mul_of_nonneg_left hotherProd (norm_nonneg _)
    _ = ‖z j‖ * (∏ i ∈ u, A i) ^ e := by rw [hrpow]
    _ ≤ (C * (A j) ^ e * (A j) ^ (-δ)) *
          (∏ i ∈ u, A i) ^ e :=
      mul_le_mul_of_nonneg_right hj (Real.rpow_nonneg hAu _)
    _ = C * (A j * ∏ i ∈ u, A i) ^ e * (A j) ^ (-δ) := by
      rw [Real.mul_rpow (hA j).le hAu]
      ring
    _ = C * (∏ i, A i) ^ e * (A j) ^ (-δ) := by rw [hprodA]

theorem not_large_product_of_distinguished_defect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ℝ) (z : ι → ℂ) (e δ C : ℝ) (j : ι)
    (hA : ∀ i, 0 < A i)
    (hj : ‖z j‖ ≤ C * (A j) ^ e * (A j) ^ (-δ))
    (hother : ∀ i, i ≠ j → ‖z i‖ ≤ (A i) ^ e)
    (habsorb : C * (A j) ^ (-δ) < 1) :
    ¬ (∏ i, A i) ^ e ≤ ‖∏ i, z i‖ := by
  intro hlarge
  have hupper := norm_fintype_prod_le_distinguished_defect
    A z e δ C j hA hj hother
  have htotal : 0 < (∏ i, A i) ^ e := by
    exact Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => hA i) e
  have hstrict : C * (∏ i, A i) ^ e * (A j) ^ (-δ) <
      (∏ i, A i) ^ e := by
    calc
      C * (∏ i, A i) ^ e * (A j) ^ (-δ) =
          (∏ i, A i) ^ e * (C * (A j) ^ (-δ)) := by ring
      _ < (∏ i, A i) ^ e * 1 :=
        mul_lt_mul_of_pos_left habsorb htotal
      _ = (∏ i, A i) ^ e := mul_one _
  linarith

/-- Version with a single explicit constant on the entire complementary product. -/
theorem norm_fintype_prod_le_distinguished_defect_of_complement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ℝ) (z : ι → ℂ) (e δ C D : ℝ) (j : ι)
    (hA : ∀ i, 0 < A i)
    (hj : ‖z j‖ ≤ C * (A j) ^ e * (A j) ^ (-δ))
    (hcomp : ‖∏ i ∈ (Finset.univ.erase j), z i‖ ≤
      D * (∏ i ∈ (Finset.univ.erase j), A i) ^ e) :
    ‖∏ i, z i‖ ≤ (C * D) * (∏ i, A i) ^ e * (A j) ^ (-δ) := by
  let u : Finset ι := Finset.univ.erase j
  have hjmem : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ j
  have hprodZ : (∏ i, z i) = z j * ∏ i ∈ u, z i := by
    rw [show (∏ i, z i) = ∏ i ∈ (Finset.univ : Finset ι), z i by simp]
    rw [Finset.mul_prod_erase Finset.univ z hjmem]
  have hprodA : (∏ i, A i) = A j * ∏ i ∈ u, A i := by
    rw [show (∏ i, A i) = ∏ i ∈ (Finset.univ : Finset ι), A i by simp]
    rw [Finset.mul_prod_erase Finset.univ A hjmem]
  have hAu : 0 ≤ ∏ i ∈ u, A i :=
    Finset.prod_nonneg fun i _ => (hA i).le
  have hjnonneg : 0 ≤ C * (A j) ^ e * (A j) ^ (-δ) :=
    (norm_nonneg (z j)).trans hj
  rw [hprodZ, norm_mul]
  calc
    ‖z j‖ * ‖∏ i ∈ u, z i‖
        ≤ (C * (A j) ^ e * (A j) ^ (-δ)) *
            (D * (∏ i ∈ u, A i) ^ e) :=
      mul_le_mul hj (by simpa [u] using hcomp) (norm_nonneg _) hjnonneg
    _ = (C * D) * (A j * ∏ i ∈ u, A i) ^ e * (A j) ^ (-δ) := by
      rw [Real.mul_rpow (hA j).le hAu]
      ring
    _ = (C * D) * (∏ i, A i) ^ e * (A j) ^ (-δ) := by rw [hprodA]

/-- Complement-constant version of product exclusion. -/
theorem not_large_product_of_distinguished_defect_of_complement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ℝ) (z : ι → ℂ) (e δ C D : ℝ) (j : ι)
    (hA : ∀ i, 0 < A i)
    (hj : ‖z j‖ ≤ C * (A j) ^ e * (A j) ^ (-δ))
    (hcomp : ‖∏ i ∈ (Finset.univ.erase j), z i‖ ≤
      D * (∏ i ∈ (Finset.univ.erase j), A i) ^ e)
    (habsorb : (C * D) * (A j) ^ (-δ) < 1) :
    ¬ (∏ i, A i) ^ e ≤ ‖∏ i, z i‖ := by
  intro hlarge
  have hupper := norm_fintype_prod_le_distinguished_defect_of_complement
    A z e δ C D j hA hj hcomp
  have htotal : 0 < (∏ i, A i) ^ e :=
    Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => hA i) e
  have hstrict : (C * D) * (∏ i, A i) ^ e * (A j) ^ (-δ) <
      (∏ i, A i) ^ e := by
    calc
      (C * D) * (∏ i, A i) ^ e * (A j) ^ (-δ) =
          (∏ i, A i) ^ e * ((C * D) * (A j) ^ (-δ)) := by ring
      _ < (∏ i, A i) ^ e * 1 := mul_lt_mul_of_pos_left habsorb htotal
      _ = (∏ i, A i) ^ e := mul_one _
  linarith

end RHTower.Sieve
