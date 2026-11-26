import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Sampling
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Atoms

/-! # Physical count sectors supported in a selected pair of packets -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Finset Filter Topology Real _root_.RHTower
open Set (Ioi)
open BinaryOrientation.LargestPrime.Bands
open BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
local instance : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective
variable {S : Finset Nat.Primes}

def sector (S : Finset Nat.Primes) (P : Finset ℕ) (m : ℕ) : Finset (BreadthSubset m ↥S) :=
  univ.filter fun R => R.val ⊆ modes S P

def countRead (S : Finset Nat.Primes) (P Q : Finset ℕ) (b : ℝ) (m : ℕ) (B : Finset ℕ) :=
  let U := sector S P m
  share (born b) U (U.filter fun R => upperCount (modes S Q) R ∈ B)

/-- Exclusion and fixed count turn translated one-draw weights into the physical Gibbs law. -/
theorem born_subset (P Q : Finset ℕ) (hp : P.Nonempty) (b t : ℝ) (m : ℕ) (B : Finset ℕ) :
    countRead S P Q b m B = subsetRead (draw S P b t) (modes S Q) m B := by
  classical
  let q := draw S P b t
  let U := sector S P m
  let c := exp (b*t)/mass (shifted b t) P
  have hc : 0 < c := div_pos (exp_pos _) (mass_pos (shifted_pos _ _) hp)
  have pw (R : BreadthSubset m ↥S) : productWeight q R =
      if R ∈ U then c^m*weight b energyOf R else 0 := by
    by_cases hr : R ∈ U
    · rw [if_pos hr]
      have allp := (mem_filter.mp hr).2
      have one p (h : p ∈ R.val) : q p = c*exp (-b*squarefreePrimeEnergy p.val) := by
        change draw S P b t p = _
        rw [draw,if_pos (allp h),shifted]
        have hh : log (serial p:ℝ) = squarefreePrimeEnergy p.val := rfl
        rw [hh,show -b*(squarefreePrimeEnergy p.val-t)=b*t+(-b*squarefreePrimeEnergy p.val) by ring,exp_add]
        dsimp only [c]; ring
      rw [productWeight,prod_congr rfl one,prod_mul_distrib,prod_const,R.property,← exp_sum,← mul_sum]
      rfl
    · rw [if_neg hr]
      have hn : ¬R.val ⊆ modes S P := fun h => hr (mem_filter.mpr ⟨mem_univ _,h⟩)
      obtain ⟨p,hm,hnp⟩ := not_subset.mp hn
      exact prod_eq_zero hm (if_neg hnp : draw S P b t p = 0)
  have hd : (∑ R : BreadthSubset m ↥S, productWeight q R) = c^m*mass (weight b energyOf) U := by
    simp only [pw,← sum_filter,filter_mem_eq_inter,univ_inter,← mul_sum,mass]
  have he : (∑ R : BreadthSubset m ↥S, if upperCount (modes S Q) R ∈ B then productWeight q R else 0) =
      c^m*mass (weight b energyOf) (U.filter fun R => upperCount (modes S Q) R ∈ B) := by
    unfold mass
    rw [mul_sum,sum_filter,show U = univ.filter (fun R => R.val ⊆ modes S P) from rfl,sum_filter]
    apply sum_congr rfl
    intro R _
    rw [pw]
    by_cases h : R.val ⊆ modes S P <;> by_cases j : upperCount (modes S Q) R ∈ B <;>
      simp only [U,sector,mem_filter,mem_univ,true_and,h,j,if_true,if_false]
  rw [countRead,born_share,subsetRead]
  change _ = (∑ R, if upperCount (modes S Q) R ∈ B then productWeight q R else 0)/(∑ R : BreadthSubset m ↥S, productWeight q R)
  rw [he,hd,mul_div_mul_left _ _ (pow_pos hc m).ne']
  rfl

def read (c d D k b : ℝ) (m : ℕ) (B : Finset ℕ) (h : Ioi (0:ℝ)) :=
  let t := c/h.val
  countRead (added c d h) (both D k t) (high D k t) b m B

def upper (D k b t : ℝ) := share (shifted b t) (both D k t) (high D k t)

/-- A uniform finite error bound for every upper-occupation count event and every count. -/
theorem finite_error {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    ∀ᶠ h in criticalApproach, ∀ (m : ℕ) (B : Finset ℕ), let t := c/h.val
      |read c d D k b m B h-binEvent m B (upper D k b t)| ≤
        (m.choose 2:ℝ)*(∑ p, draw (added c d h) (both D k t) b t p^2) := by
  filter_upwards [mode_coverage hc hcd hD hk,(translation_limit hc).eventually (windows hD hk)] with h hm hw
  intro m B
  let t := c/h.val
  let q := draw (added c d h) (both D k t) b t
  have hP : (both D k t).Nonempty := hw.1.mono subset_union_left
  have hn := draw_total hP hm b t
  have per := subset_error q (draw_nonneg _ _ _) hn (modes (added c d h) (high D k t)) m B
  have H := per.trans (repeat_le q (draw_nonneg _ _ _) hn m).2
  change |countRead _ (both D k t) (high D k t) b m B-binEvent m B (upper D k b t)| ≤ _
  rw [born_subset _ _ hP b t]
  change |subsetRead q _ m B-binEvent m B (upper D k b t)| ≤ _
  have hcov : (modes (added c d h) (both D k t)).image serial = both D k t := hm
  have prob : (∑ x ∈ modes (added c d h) (high D k t), q x) = upper D k b t :=
    draw_event hcov (show high D k t ⊆ both D k t from subset_union_right) b t
  rw [prob] at H
  exact H

#print axioms born_subset
#print axioms finite_error

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
