import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Critical rational-ratio wall: scalar finite-part positivity no-go

The leading theta cusp wall is a positive rational-ratio autocorrelation for every
aperture `a > 0`. Its critical Laurent finite part is not another positive kernel.
On finite squarefree prime cubes, the all-ones energy has a negative direction
for every scalar subtraction. The analytic identification with the full theta
boundary current is not claimed here; this file proves the exact arithmetic
squarefree-cube obstruction.
-/

open Finset

namespace RHTower

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def localW (r : ι → ℝ) (i : ι) (b : Bool × Bool) : ℝ :=
  if b.1 = b.2 then 1 else r i

private def localL (l : ι → ℝ) (i : ι) (b : Bool × Bool) : ℝ :=
  if b.1 = b.2 then 0 else l i

omit [Fintype ι] [DecidableEq ι] in
private theorem localW_sum (r : ι → ℝ) (i : ι) :
    (∑ b : Bool × Bool, localW r i b) = 2 * (1 + r i) := by
  simp [Fintype.sum_prod_type, localW]
  ring

omit [Fintype ι] [DecidableEq ι] in
private theorem localWL_sum (r l : ι → ℝ) (i : ι) :
    (∑ b : Bool × Bool, localW r i b * localL l i b) = 2 * r i * l i := by
  simp [Fintype.sum_prod_type, localW, localL]
  ring

private def cubeMass (r : ι → ℝ) : ℝ :=
  ∑ x : ι → Bool × Bool, ∏ i, localW r i (x i)

private def cubeMoment (r l : ι → ℝ) : ℝ :=
  ∑ x : ι → Bool × Bool,
    (∏ i, localW r i (x i)) * (∑ i, localL l i (x i))

private theorem cubeMass_eq (r : ι → ℝ) :
    cubeMass r = ∏ i, 2 * (1 + r i) := by
  unfold cubeMass
  rw [← Fintype.prod_sum]
  simp only [localW_sum]

private theorem cubeMoment_eq (r l : ι → ℝ) :
    cubeMoment r l =
      ∑ i, (2 * r i * l i) * (∏ j ∈ (univ : Finset ι).erase i, 2 * (1 + r j)) := by
  unfold cubeMoment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have h :
      (∑ x : ι → Bool × Bool,
        (∏ j, localW r j (x j)) * localL l i (x i)) =
        ∏ j, (∑ b : Bool × Bool,
          localW r j b * if j = i then localL l j b else 1) := by
    rw [Fintype.prod_sum]
    congr 1
    funext x
    calc
      (∏ j, localW r j (x j)) * localL l i (x i) =
          (∏ j, localW r j (x j)) *
            (∏ j, if j = i then localL l j (x j) else 1) := by simp
      _ = ∏ j, (localW r j (x j)) *
            (if j = i then localL l j (x j) else 1) := by
              rw [Finset.prod_mul_distrib]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        split_ifs <;> simp
  rw [h]
  let F : ι → ℝ := fun j => ∑ b : Bool × Bool,
    localW r j b * if j = i then localL l j b else 1
  change (∏ j, F j) = _
  rw [← Finset.prod_erase_mul (univ : Finset ι) F (Finset.mem_univ i)]
  have hF : F i = 2 * r i * l i := by
    simp only [F]
    exact localWL_sum r l i
  rw [hF]
  have hrest : (∏ j ∈ (univ : Finset ι).erase i, F j) =
      ∏ j ∈ (univ : Finset ι).erase i, 2 * (1 + r j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp only [F, if_neg hji, mul_one]
    exact localW_sum r j
  rw [hrest]
  ring

private theorem cubeMoment_eq_mass_mul_sum (r l : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) :
    cubeMoment r l = cubeMass r * ∑ i, r i * l i / (1 + r i) := by
  rw [cubeMoment_eq, cubeMass_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hpos : 0 < 1 + r i := by linarith [hr i]
  have hprod := Finset.prod_erase_mul (univ : Finset ι)
      (fun j => 2 * (1 + r j)) (Finset.mem_univ i)
  rw [← hprod]
  field_simp

private def cubeFinitePartEnergy (C : ℝ) (r l : ι → ℝ) : ℝ :=
  ∑ x : ι → Bool × Bool,
    (∏ i, localW r i (x i)) *
      (C - (1 / 2 : ℝ) * (∑ i, localL l i (x i)))

private theorem cubeFinitePartEnergy_eq (C : ℝ) (r l : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) :
    cubeFinitePartEnergy C r l =
      cubeMass r * (C - (1 / 2 : ℝ) * ∑ i, r i * l i / (1 + r i)) := by
  unfold cubeFinitePartEnergy
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  change (∑ x : ι → Bool × Bool, (∏ i, localW r i (x i)) * C) -
      (∑ x : ι → Bool × Bool,
        (∏ i, localW r i (x i)) * ((1 / 2 : ℝ) * ∑ i, localL l i (x i))) = _
  rw [← Finset.sum_mul]
  have h2 :
      (∑ x : ι → Bool × Bool,
        (∏ i, localW r i (x i)) * ((1 / 2 : ℝ) * ∑ i, localL l i (x i))) =
      (1 / 2 : ℝ) * cubeMoment r l := by
    unfold cubeMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h2, cubeMoment_eq_mass_mul_sum r l hr]
  change cubeMass r * C -
    (1 / 2 : ℝ) * (cubeMass r * ∑ i, r i * l i / (1 + r i)) = _
  ring

private theorem cubeMass_pos (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    0 < cubeMass r := by
  rw [cubeMass_eq]
  apply Finset.prod_pos
  intro i _
  nlinarith [hr i]

private theorem cubeFinitePartEnergy_neg (C : ℝ) (r l : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hlarge : 2 * C < ∑ i, r i * l i / (1 + r i)) :
    cubeFinitePartEnergy C r l < 0 := by
  rw [cubeFinitePartEnergy_eq C r l hr]
  apply mul_neg_of_pos_of_neg (cubeMass_pos r hr)
  linarith

private def primeRatioWeight (p : Nat.Primes) : ℝ :=
  ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

private def primeFinitePartCost (p : Nat.Primes) : ℝ :=
  primeRatioWeight p * Real.log ((p : ℕ) : ℝ) / (1 + primeRatioWeight p)

private theorem primeRatioWeight_nonneg (p : Nat.Primes) :
    0 ≤ primeRatioWeight p := by
  unfold primeRatioWeight
  positivity

private theorem primeRatioWeight_le_one (p : Nat.Primes) :
    primeRatioWeight p ≤ 1 := by
  unfold primeRatioWeight
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast (Nat.Prime.one_le p.property)
  · norm_num

private theorem primeFinitePartCost_lower (p : Nat.Primes) :
    (Real.log 2 / 2) * primeRatioWeight p ≤ primeFinitePartCost p := by
  have hr0 := primeRatioWeight_nonneg p
  have hr1 := primeRatioWeight_le_one p
  have hd : 0 < 1 + primeRatioWeight p := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    exact_mod_cast p.property.two_le
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp2
  have hratio : primeRatioWeight p / 2 ≤
      primeRatioWeight p / (1 + primeRatioWeight p) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hd).2
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]
  have hleft := mul_le_mul_of_nonneg_left hratio hlog2.le
  have hright := mul_le_mul_of_nonneg_right hlog (div_nonneg hr0 hd.le)
  unfold primeFinitePartCost
  calc
    Real.log 2 / 2 * primeRatioWeight p =
        Real.log 2 * (primeRatioWeight p / 2) := by ring
    _ ≤ Real.log 2 * (primeRatioWeight p / (1 + primeRatioWeight p)) := hleft
    _ ≤ Real.log ((p : ℕ) : ℝ) *
        (primeRatioWeight p / (1 + primeRatioWeight p)) := hright
    _ = primeRatioWeight p * Real.log ((p : ℕ) : ℝ) /
        (1 + primeRatioWeight p) := by ring

private theorem not_summable_primeFinitePartCost :
    ¬ Summable primeFinitePartCost := by
  intro hf
  have hscaled : Summable (fun p : Nat.Primes =>
      (Real.log 2 / 2) * primeRatioWeight p) := by
    apply Summable.of_nonneg_of_le
    · intro p; exact mul_nonneg (by positivity) (primeRatioWeight_nonneg p)
    · exact primeFinitePartCost_lower
    · exact hf
  have hbase : Summable primeRatioWeight :=
    (summable_mul_left_iff (by positivity : (Real.log 2 / 2 : ℝ) ≠ 0)).mp hscaled
  have hcritical : ¬ Summable primeRatioWeight := by
    intro hs
    have h := Nat.Primes.summable_rpow.mp hs
    norm_num [primeRatioWeight] at h
  exact hcritical hbase

private theorem exists_primeFinitePartCost_large (C : ℝ) :
    ∃ P : Finset Nat.Primes, C < ∑ p ∈ P, primeFinitePartCost p := by
  by_contra h
  push Not at h
  apply not_summable_primeFinitePartCost
  apply summable_of_sum_le
  · intro p
    have hlog : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.property.one_le)
    unfold primeFinitePartCost
    exact div_nonneg (mul_nonneg (primeRatioWeight_nonneg p) hlog)
      (by linarith [primeRatioWeight_nonneg p])
  · exact h

/-- Pair-cube quadratic form of the scalar-renormalized critical rational-ratio wall.
Each coordinate is one prime and two Boolean occupancies; unequal occupancies carry
`p^(-1/2)` and `log p`. This is the exact squarefree reduced-ratio kernel at the
Laurent first variation, with arbitrary scalar subtraction `C`. -/
def thetaWallCriticalPrimeCubeEnergy (C : ℝ) (P : Finset Nat.Primes) : ℝ :=
  cubeFinitePartEnergy (ι := P) C
    (fun p => primeRatioWeight p.1)
    (fun p => Real.log (((p.1 : Nat.Primes) : ℕ) : ℝ))

/-- Exact squarefree-prime product law. The positive prefactor is the leading
autocorrelation mass; the bracket is its critical signed first variation. -/
theorem thetaWallCriticalPrimeCubeEnergy_eq (C : ℝ) (P : Finset Nat.Primes) :
    thetaWallCriticalPrimeCubeEnergy C P =
      (∏ p : P, 2 * (1 + primeRatioWeight p.1)) *
        (C - (1 / 2 : ℝ) * ∑ p ∈ P, primeFinitePartCost p) := by
  classical
  unfold thetaWallCriticalPrimeCubeEnergy
  rw [cubeFinitePartEnergy_eq]
  · rw [cubeMass_eq]
    congr 1
    simpa [primeFinitePartCost] using
      (Finset.sum_attach P primeFinitePartCost)
  · intro p
    exact primeRatioWeight_nonneg p.1

/-- No scalar counterterm makes the critical first-variation ratio kernel positive
semidefinite on all finite squarefree prime cubes: its all-ones quadratic form is
negative on some finite actual-prime cube, for every `C`. This is a wall-scalar
no-go, not a theorem about the signed completed Xi current or RH. -/
theorem exists_negative_thetaWallCriticalPrimeCubeEnergy (C : ℝ) :
    ∃ P : Finset Nat.Primes, thetaWallCriticalPrimeCubeEnergy C P < 0 := by
  obtain ⟨P, hP⟩ := exists_primeFinitePartCost_large (2 * C)
  refine ⟨P, ?_⟩
  classical
  unfold thetaWallCriticalPrimeCubeEnergy
  apply cubeFinitePartEnergy_neg
  · intro p
    exact primeRatioWeight_nonneg p.1
  · have hsum :
        (∑ p : P, primeRatioWeight p.1 *
          Real.log (((p.1 : Nat.Primes) : ℕ) : ℝ) /
          (1 + primeRatioWeight p.1)) =
        ∑ p ∈ P, primeFinitePartCost p := by
          simpa [primeFinitePartCost] using
            (Finset.sum_attach P primeFinitePartCost)
    rw [hsum]
    exact hP

end

end RHTower
