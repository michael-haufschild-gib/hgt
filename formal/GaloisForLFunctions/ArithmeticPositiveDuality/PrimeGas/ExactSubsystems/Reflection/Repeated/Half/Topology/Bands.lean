import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Heat
import GaloisForLFunctions.HTGeometry.BorsukUlam.Theorem

/-! # An antipodal sphere of asymmetric centered spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Topology

open Finset Metric

abbrev Bands (q p : ℕ) := (Fin (q+1) ⊕ Fin (q+1)) ⊕ (Unit ⊕ Fin p)

variable {q p : ℕ}

private def anchor (i : Fin (q+1)) : ℝ := 4*((q : ℝ)+2)+4*(i.val : ℝ)

/-- Distinct positive and negative bands carry the same displacement. A central state
absorbs their total shift, leaving the mean exactly zero. -/
def levels (z : EuclideanSpace ℝ (Fin (q+1))) : Bands q p → ℝ
  | .inl (.inl i) => anchor i+z i
  | .inl (.inr i) => -anchor i+z i
  | .inr (.inl _) => -2*∑ i, z i
  | .inr (.inr _) => 0

def swap (q p : ℕ) : Equiv.Perm (Bands q p) := (Equiv.sumComm _ _).sumCongr (Equiv.refl _)

theorem sum_levels (z : EuclideanSpace ℝ (Fin (q+1))) : ∑ i : Bands q p, levels z i=0 := by
  simp [Fintype.sum_sum_type,levels,sum_add_distrib,sum_neg_distrib]
  ring

theorem levels_continuous (i : Bands q p) : Continuous (fun z => levels z i) := by
  rcases i with (j | j) | (j | j)
  · exact continuous_const.add (EuclideanSpace.proj j).continuous
  · exact continuous_const.add (EuclideanSpace.proj j).continuous
  · exact continuous_const.mul (continuous_finsetSum _ fun j _ => (EuclideanSpace.proj j).continuous)
  · exact continuous_const

theorem antipodal (z : EuclideanSpace ℝ (Fin (q+1))) (i : Bands q p) :
    levels (-z) i = -levels z (swap q p i) := by
  rcases i with (j | j) | (j | j)
  · change anchor j + -z j = -(-anchor j+z j)
    ring
  · change -anchor j + -z j = -(anchor j+z j)
    ring
  · change -2*(∑ i, -z i) = -(-2*∑ i, z i)
    rw [sum_neg_distrib]; ring
  · exact neg_zero.symm

private theorem gap {i j : Fin (q+1)} (h : i<j) : anchor i+4 ≤ anchor j := by
  have hi : (i.val : ℝ)+1 ≤ (j.val : ℝ) := by exact_mod_cast (show i.val+1 ≤ j.val from h)
  unfold anchor
  linarith only [hi]

/-- Band separation forces a partner to have the same band index. The two displacements
then add to zero only when that coordinate vanishes. -/
theorem asymmetric {z : EuclideanSpace ℝ (Fin (q+1))} (hz : z ∈ sphere 0 1) :
    ¬Reflects (levels (p := p) z) := by
  intro reflect
  have norm : ‖z‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz
  have bounds (i : Fin (q+1)) : -1 ≤ z i ∧ z i ≤ 1 := abs_le.mp ((BorsukUlam.abs_coord_le_norm z i).trans_eq norm)
  have total : (∑ i, z i) ≤ (q : ℝ)+1 := by
    calc _ ≤ ∑ _ : Fin (q+1), (1 : ℝ) := sum_le_sum fun i _ => (bounds i).2
         _ = _ := by simp
  have hn : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have band (i : Fin (q+1)) : 2*((q : ℝ)+1) < anchor i+z i := by
    have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    unfold anchor
    linarith only [hn,hi,(bounds i).1]
  have pair := (reflects_iff_centered_pair _).mp reflect
  rw [centered_eq_of_sum_zero (sum_levels z)] at pair
  obtain ⟨R,hR⟩ := pair
  have vanished (i : Fin (q+1)) : z i=0 := by
    have h := hR (Sum.inl (Sum.inl i))
    generalize R (Sum.inl (Sum.inl i))=y at h
    rcases y with (j | j) | (j | j)
    · change (anchor i+z i)+(anchor j+z j)=0 at h
      linarith only [band i,band j,hn,h]
    · change (anchor i+z i)+(-anchor j+z j)=0 at h
      rcases lt_trichotomy i j with lt | rfl | gt
      · linarith only [gap lt,(bounds i).2,(bounds j).2,h]
      · linarith only [h]
      · linarith only [gap gt,(bounds i).1,(bounds j).1,h]
    · change (anchor i+z i)+(-2*∑ s, z s)=0 at h
      linarith only [band i,total,h]
    · change (anchor i+z i)+0=0 at h
      linarith only [band i,hn,h]
  have zero : z=0 := by ext i; exact vanished i
  rw [zero,norm_zero] at norm
  exact zero_ne_one norm

#print axioms sum_levels
#print axioms asymmetric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Topology
