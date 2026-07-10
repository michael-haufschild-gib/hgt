import GaloisForLFunctions.RHTower.FEPairedPrimeJetRigidity
import Mathlib.LinearAlgebra.Lagrange

/-!
# Barycentric nonlocality of FE-paired prime jets

The FE-paired interpolation theorem gives a unique finite coefficient packet but does not identify
its coefficients.  This file computes them.  For squared nodes `x_i = (log p_i)^2`, evaluation at
zero has the Lagrange weights

`b_i = ∏_{j ≠ i} (-x_j)/(x_i-x_j)`,

so the coefficient of the reflected pair `±log p_i` is `a_i = b_i/(2 log p_i)`.

This formula exposes a stronger obstruction than failure of coefficient-preserving extension.
Every coefficient is nonzero, and adjoining one new prime multiplies each old barycentric weight by

`(-x_new)/(x_i-x_new) ≠ 1`.

Hence every old coefficient changes whenever the support grows.  The exact finite interpolant is
globally dependent on the complete chosen support; it cannot be interpreted as a packet of fixed
local Euler coefficients.  This is a constraint-side theorem, with no cutoff or carrier limit.
-/

namespace RHTower

open Polynomial
open scoped BigOperators

noncomputable section

/-- Barycentric weight representing evaluation at zero on a finite node family. -/
def originInterpolationWeight {k : ℕ} (x : Fin k → ℂ) (i : Fin k) : ℂ :=
  ∏ j : Fin k, if j = i then 1 else (-x j) / (x i - x j)

theorem originInterpolationWeight_eq_eval_lagrangeBasis {k : ℕ}
    (x : Fin k → ℂ) (i : Fin k) :
    originInterpolationWeight x i =
      (Lagrange.basis Finset.univ x i).eval 0 := by
  classical
  rw [originInterpolationWeight, Lagrange.basis, Polynomial.eval_prod]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [if_pos, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hji, Lagrange.basisDivisor, div_eq_mul_inv, mul_comm]

/-- The barycentric origin weights have moment sequence `(1,0,...,0)` below the number of nodes. -/
theorem originInterpolationWeight_moments {k : ℕ} (x : Fin k → ℂ)
    (hinj : Function.Injective x) (j : Fin k) :
    (∑ i : Fin k, originInterpolationWeight x i * x i ^ (j : ℕ)) =
      originValueMoment (j : ℕ) := by
  classical
  let P : Polynomial ℂ := X ^ (j : ℕ)
  have hdeg : P.degree < (((Finset.univ : Finset (Fin k)).card : ℕ) : WithBot ℕ) := by
    dsimp [P]
    rw [Polynomial.degree_X_pow]
    simp only [Fintype.card_fin]
    exact_mod_cast j.isLt
  have hpoly := Lagrange.eq_interpolate (s := Finset.univ) (v := x)
    hinj.injOn hdeg
  have heval := congrArg (Polynomial.eval 0) hpoly
  dsimp [P] at heval
  rw [Polynomial.eval_finsetSum] at heval
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  calc
    (∑ i : Fin k, originInterpolationWeight x i * x i ^ (j : ℕ)) =
        ∑ i : Fin k, x i ^ (j : ℕ) *
          (Lagrange.basis Finset.univ x i).eval 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [originInterpolationWeight_eq_eval_lagrangeBasis]
      ring
    _ = 0 ^ (j : ℕ) := heval.symm
    _ = originValueMoment (j : ℕ) := by
      by_cases hj : (j : ℕ) = 0
      · simp [originValueMoment, hj]
      · simp [originValueMoment, hj]

/-- Every barycentric origin weight is nonzero when the nodes are distinct and avoid zero. -/
theorem originInterpolationWeight_ne_zero {k : ℕ} (x : Fin k → ℂ)
    (hinj : Function.Injective x) (hx : ∀ i, x i ≠ 0) (i : Fin k) :
    originInterpolationWeight x i ≠ 0 := by
  classical
  rw [originInterpolationWeight]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hji : j = i
  · simp [hji]
  · rw [if_neg hji]
    exact div_ne_zero (neg_ne_zero.mpr (hx j))
      (sub_ne_zero.mpr (hinj.ne (Ne.symm hji)))

/-- Adding a last node multiplies every old barycentric origin weight by one explicit factor. -/
theorem originInterpolationWeight_castSucc {k : ℕ} (x : Fin (k + 1) → ℂ)
    (i : Fin k) :
    originInterpolationWeight x i.castSucc =
      originInterpolationWeight (fun j : Fin k => x j.castSucc) i *
        ((-x (Fin.last k)) / (x i.castSucc - x (Fin.last k))) := by
  classical
  rw [originInterpolationWeight, Fin.prod_univ_castSucc, originInterpolationWeight]
  have hlast : Fin.last k ≠ i.castSucc := by
    intro h
    have hv : k = (i : ℕ) := by simpa using congrArg Fin.val h
    exact (Nat.ne_of_lt i.isLt) hv.symm
  simp [hlast]

/-- The extension factor cannot equal one when the old node is nonzero and distinct from the new
node. -/
theorem neg_div_sub_ne_one {x y : ℂ} (hx : x ≠ 0) (hxy : x ≠ y) :
    (-y) / (x - y) ≠ 1 := by
  intro h
  have hden : x - y ≠ 0 := sub_ne_zero.mpr hxy
  field_simp [hden] at h
  apply hx
  linear_combination -h

/-- The explicit reflected-pair coefficient obtained from barycentric evaluation at zero. -/
def fePairedOriginCoefficient {k : ℕ} (r : Fin k → ℂ) (i : Fin k) : ℂ :=
  originInterpolationWeight (fun j => r j ^ 2) i / (2 * r i)

/-- The barycentric reflected-pair coefficients match the origin derivation at all available odd
degrees. -/
theorem fePairedOriginCoefficient_odd_match {k : ℕ} (r : Fin k → ℂ)
    (hr2inj : Function.Injective (fun i => r i ^ 2))
    (hr0 : ∀ i, r i ≠ 0) (j : Fin k) :
    fePairedMoment r (fePairedOriginCoefficient r) (2 * (j : ℕ) + 1) =
      archimedeanDerivationMoment (2 * (j : ℕ) + 1) := by
  rw [fePairedMoment_odd_eq]
  calc
    (∑ i : Fin k, (2 * fePairedOriginCoefficient r i * r i) *
        (r i ^ 2) ^ (j : ℕ)) =
        ∑ i : Fin k, originInterpolationWeight (fun q => r q ^ 2) i *
          (r i ^ 2) ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [fePairedOriginCoefficient]
      field_simp [hr0 i]
    _ = originValueMoment (j : ℕ) :=
      originInterpolationWeight_moments (fun i => r i ^ 2) hr2inj j
    _ = archimedeanDerivationMoment (2 * (j : ℕ) + 1) :=
      (archimedeanDerivationMoment_odd_eq_originValueMoment (j : ℕ)).symm

/-- Every explicit reflected-pair coefficient is nonzero. -/
theorem fePairedOriginCoefficient_ne_zero {k : ℕ} (r : Fin k → ℂ)
    (hr2inj : Function.Injective (fun i => r i ^ 2))
    (hr0 : ∀ i, r i ≠ 0) (i : Fin k) :
    fePairedOriginCoefficient r i ≠ 0 := by
  exact div_ne_zero
    (originInterpolationWeight_ne_zero (fun j => r j ^ 2) hr2inj
      (fun j => pow_ne_zero 2 (hr0 j)) i)
    (mul_ne_zero (by norm_num) (hr0 i))

/-- **Barycentric nonlocality.** Adding one nonzero squared-distinct reflected node changes every
old explicit interpolation coefficient. -/
theorem fePairedOriginCoefficient_castSucc_ne {k : ℕ} (r : Fin (k + 1) → ℂ)
    (hr2inj : Function.Injective (fun i => r i ^ 2))
    (hr0 : ∀ i, r i ≠ 0) (i : Fin k) :
    fePairedOriginCoefficient r i.castSucc ≠
      fePairedOriginCoefficient (fun j : Fin k => r j.castSucc) i := by
  intro hcoeff
  let x : Fin (k + 1) → ℂ := fun q => r q ^ 2
  let xold : Fin k → ℂ := fun q => x q.castSucc
  let W : ℂ := originInterpolationWeight xold i
  let c : ℂ := (-x (Fin.last k)) / (x i.castSucc - x (Fin.last k))
  have hWeightEq : originInterpolationWeight x i.castSucc = W := by
    dsimp [fePairedOriginCoefficient, x, xold, W] at hcoeff ⊢
    field_simp [hr0 i.castSucc] at hcoeff
    exact hcoeff
  have hWmul : W * c = W := by
    calc
      W * c = originInterpolationWeight x i.castSucc :=
        (originInterpolationWeight_castSucc x i).symm
      _ = W := hWeightEq
  have hxoldInj : Function.Injective xold := fun _ _ h =>
    Fin.castSucc_inj.mp (hr2inj h)
  have hxold0 : ∀ q, xold q ≠ 0 := fun q => pow_ne_zero 2 (hr0 q.castSucc)
  have hW0 : W ≠ 0 := by
    dsimp [W]
    exact originInterpolationWeight_ne_zero xold hxoldInj hxold0 i
  have hc1 : c = 1 := by
    apply (mul_left_cancel₀ hW0)
    simpa using hWmul
  have hidx : i.castSucc ≠ Fin.last k := by
    intro h
    have hv : (i : ℕ) = k := by simpa using congrArg Fin.val h
    exact (Nat.ne_of_lt i.isLt) hv
  have hxy : x i.castSucc ≠ x (Fin.last k) := hr2inj.ne hidx
  exact (neg_div_sub_ne_one (pow_ne_zero 2 (hr0 i.castSucc)) hxy) hc1

/-- Closed barycentric formula for the unique FE-paired prime interpolation coefficients. -/
def fePairedPrimeBarycentricCoefficient {k : ℕ} (p : Fin k → ℕ) (i : Fin k) : ℂ :=
  fePairedOriginCoefficient (fun q => (Real.log (p q) : ℂ)) i

theorem fePairedPrimeBarycentricCoefficient_odd_match {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p)
    (j : Fin k) :
    fePairedMoment (fun i => (Real.log (p i) : ℂ))
        (fePairedPrimeBarycentricCoefficient p) (2 * (j : ℕ) + 1) =
      archimedeanDerivationMoment (2 * (j : ℕ) + 1) := by
  exact fePairedOriginCoefficient_odd_match
    (fun i => (Real.log (p i) : ℂ))
    (log_sq_nat_injective p hp hpinj)
    (fun i => Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp i)).ne') j

/-- The abstract unique interpolation packet is exactly the barycentric packet. -/
theorem fePairedPrimeDerivationInterpolation_eq_barycentric {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p)
    (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      fePairedMoment (fun i => (Real.log (p i) : ℂ)) a (2 * (j : ℕ) + 1) =
        archimedeanDerivationMoment (2 * (j : ℕ) + 1)) :
    a = fePairedPrimeBarycentricCoefficient p := by
  obtain ⟨u, hu, huu⟩ :=
    existsUnique_fePairedPrimeDerivationInterpolation p hp hpinj
  calc
    a = u := huu a hmatch
    _ = fePairedPrimeBarycentricCoefficient p :=
      (huu _ (fePairedPrimeBarycentricCoefficient_odd_match p hp hpinj)).symm

/-- **Every old coefficient changes.** Extending an injective positive prime packet by one new
prime changes each barycentric interpolation coefficient, not merely one unspecified coefficient. -/
theorem fePairedPrimeBarycentricCoefficient_castSucc_ne {k : ℕ}
    (p : Fin (k + 1) → ℕ) (hp : ∀ i, 1 < p i)
    (hpinj : Function.Injective p) (i : Fin k) :
    fePairedPrimeBarycentricCoefficient p i.castSucc ≠
      fePairedPrimeBarycentricCoefficient (fun j : Fin k => p j.castSucc) i := by
  exact fePairedOriginCoefficient_castSucc_ne
    (fun q => (Real.log (p q) : ℂ))
    (log_sq_nat_injective p hp hpinj)
    (fun q => Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp q)).ne') i

end

end RHTower

