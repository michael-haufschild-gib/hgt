import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.BinaryContrast

/-! # Comparing finite conditional laws by their event odds -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

variable {Ω : Type*}

def mass (w : Ω → ℝ) (U : Finset Ω) := ∑ x ∈ U, w x

/-- Relative weight of an event A contained in the selection U. -/
def share (w : Ω → ℝ) (U A : Finset Ω) := mass w A/mass w U

theorem mass_pos {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {U : Finset Ω} (hU : U.Nonempty) :
    0 < mass w U := Finset.sum_pos (fun x _ => hw x) hU

theorem share_nonneg {w : Ω → ℝ} (hw : ∀ x, 0 < w x) (U A : Finset Ω) :
    0 ≤ share w U A := div_nonneg (Finset.sum_nonneg fun x _ => (hw x).le) (Finset.sum_nonneg fun x _ => (hw x).le)

theorem one_sub_share [DecidableEq Ω] {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {U A : Finset Ω} (hU : U.Nonempty) (hA : A ⊆ U) :
    1-share w U A = share w U (U \ A) := by
  have h : mass w (U \ A)+mass w A = mass w U := Finset.sum_sdiff hA
  unfold share
  rw [← div_self (mass_pos hw hU).ne',← sub_div]
  congr 1
  linarith only [h]

private def crossSlack (C : ℝ) (w z : Ω → ℝ) (A B : Finset Ω) :=
  ∑ x ∈ A, ∑ y ∈ B, (C*z x*w y-w x*z y)

private theorem crossSlack_eq (C : ℝ) (w z : Ω → ℝ) (A B : Finset Ω) :
    crossSlack C w z A B = C*mass z A*mass w B-mass w A*mass z B := by
  rw [crossSlack]
  calc _ = ∑ x ∈ A, (C*z x*mass w B-w x*mass z B) := by
         simp only [mass,Finset.sum_sub_distrib,← Finset.mul_sum]
       _ = _ := by rw [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum]; rfl

/-- The defect in the aggregate odds inequality is a sum of nonnegative cross-pair defects. -/
private theorem odds_control [DecidableEq Ω] {w z : Ω → ℝ} (hw : ∀ x, 0 < w x) (hz : ∀ x, 0 < z x)
    {U A : Finset Ω} (hU : U.Nonempty) (hA : A ⊆ U) {C : ℝ}
    (hpair : ∀ x ∈ A, ∀ y ∈ U \ A, w x*z y ≤ C*z x*w y) :
    share w U A*(1-share z U A) ≤ C*share z U A*(1-share w U A) ∧
    (share w U A*(1-share z U A) = C*share z U A*(1-share w U A) ↔
      ∀ x ∈ A, ∀ y ∈ U \ A, w x*z y = C*z x*w y) := by
  let B := U \ A
  have hp (x) (hx : x ∈ A) (y) (hy : y ∈ B) : 0 ≤ C*z x*w y-w x*z y := sub_nonneg.mpr (hpair x hx y hy)
  have hs x (hx : x ∈ A) := Finset.sum_nonneg (hp x hx)
  have hn : 0 ≤ crossSlack C w z A B := Finset.sum_nonneg hs
  have hden := mul_pos (mass_pos hz hU) (mass_pos hw hU)
  have he : C*share z U A*(1-share w U A)-share w U A*(1-share z U A) =
      crossSlack C w z A B/(mass z U*mass w U) := by
    rw [one_sub_share hw hU hA,one_sub_share hz hU hA,crossSlack_eq]
    unfold share
    dsimp [B]
    field_simp [(mass_pos hz hU).ne',(mass_pos hw hU).ne']
  refine ⟨sub_nonneg.mp (he.ge.trans' (div_nonneg hn hden.le)),?_⟩
  have hzero : crossSlack C w z A B = 0 ↔ ∀ x ∈ A, ∀ y ∈ B, w x*z y = C*z x*w y := by
    rw [crossSlack,Finset.sum_eq_zero_iff_of_nonneg hs]
    constructor
    · intro h x hx y hy
      exact (sub_eq_zero.mp (((Finset.sum_eq_zero_iff_of_nonneg (hp x hx)).mp (h x hx)) y hy)).symm
    · intro h x hx
      exact Finset.sum_eq_zero fun y hy => sub_eq_zero.mpr (h x hx y hy).symm
  constructor
  · intro h
    rw [← h,sub_self] at he
    exact hzero.mp ((div_eq_zero_iff.mp he.symm).resolve_right hden.ne')
  · intro h
    rw [hzero.mpr h,zero_div] at he
    exact (sub_eq_zero.mp he).symm

theorem signed_bound [DecidableEq Ω] {w z : Ω → ℝ} (hw : ∀ x, 0 < w x) (hz : ∀ x, 0 < z x)
    {U A : Finset Ω} (hU : U.Nonempty) (hA : A ⊆ U) {s : ℝ} (hs : 1 ≤ s)
    (hpair : ∀ x ∈ A, ∀ y ∈ U \ A, w x*z y ≤ s^2*z x*w y) :
    share w U A-share z U A ≤ (s-1)/(s+1) :=
  binary_bound hs (share_nonneg hz U A) (odds_control hw hz hU hA hpair).1

theorem signed_equality [DecidableEq Ω] {w z : Ω → ℝ} (hw : ∀ x, 0 < w x) (hz : ∀ x, 0 < z x)
    {U A : Finset Ω} (hU : U.Nonempty) (hA : A ⊆ U) {s : ℝ} (hs : 1 < s)
    (hpair : ∀ x ∈ A, ∀ y ∈ U \ A, w x*z y ≤ s^2*z x*w y) :
    share w U A-share z U A = (s-1)/(s+1) ↔
      (s+1)*share z U A = 1 ∧ ∀ x ∈ A, ∀ y ∈ U \ A, w x*z y = s^2*z x*w y := by
  have H := odds_control hw hz hU hA hpair
  rw [binary_equality hs (share_nonneg hz U A) H.1,H.2]

/-- Total variation is the largest event-probability difference on a finite selection. -/
def variation (w z : Ω → ℝ) (U : Finset Ω) :=
  U.powerset.sup' U.powerset_nonempty fun A => |share w U A-share z U A|

theorem event_le_variation (w z : Ω → ℝ) {U A : Finset Ω} (hA : A ⊆ U) :
    |share w U A-share z U A| ≤ variation w z U :=
  Finset.le_sup' (fun B => |share w U B-share z U B|) (Finset.mem_powerset.mpr hA)

theorem variation_le {w z : Ω → ℝ} {U : Finset Ω} {r : ℝ}
    (h : ∀ A ⊆ U, |share w U A-share z U A| ≤ r) : variation w z U ≤ r :=
  Finset.sup'_le _ _ fun A ha => h A (Finset.mem_powerset.mp ha)

#print axioms signed_bound
#print axioms signed_equality
#print axioms variation_le

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
