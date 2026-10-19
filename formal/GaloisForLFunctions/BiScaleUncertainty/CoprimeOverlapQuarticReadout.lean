import GaloisForLFunctions.BiScaleUncertainty.SixthValuationPhaseRecovery

/-!
# Quartic readouts from overlapping coprime orders

The three orders `2pq,2pr,2qr` have a primitive quartic resonance when the
odd blocks are pairwise coprime. Its full lag Fourier coefficient reads two
signed coordinates times the square of the third, with exact normalization.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CoprimeOverlap
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Four frequencies coupling the three pair-product orders. -/
def frequencies (N p q r : ℕ) : Fin 4 → ZMod N.factorial :=
  let d : ZMod N.factorial := (N.factorial / 2 : ℕ)
  let a : ZMod N.factorial := (N.factorial / p : ℕ)
  let b : ZMod N.factorial := (N.factorial / q : ℕ)
  let c : ZMod N.factorial := (N.factorial / r : ℕ)
  ![d+a+b, d-a+c, d+b+c, d-2•b-2•c]

private theorem add_order {P A B : ℕ} [NeZero P] (x y : ZMod P)
    (hx : addOrderOf x = A) (hy : addOrderOf y = B) (hc : Nat.Coprime A B) :
    addOrderOf (x+y) = A*B := by
  have hcomm : AddCommute x y := add_comm x y
  have h := hcomm.addOrderOf_add_eq_mul_addOrderOf_of_coprime
    (show Nat.Coprime (addOrderOf x) (addOrderOf y) by rwa [hx,hy])
  simpa only [hx,hy] using h

/-- The common order-two component closes the resonance. -/
theorem frequencies_sum {N p q r : ℕ} (hN : 2 ≤ N) :
    (∑ i, frequencies N p q r i) = 0 := by
  have hd := frequency_order (Finset.mem_Icc.mpr ⟨by omega,hN⟩)
  have hz := addOrderOf_nsmul_eq_zero (((N.factorial / 2 : ℕ)) : ZMod N.factorial)
  rw [hd,two_nsmul] at hz
  rw [Fin.sum_univ_four]
  let d : ZMod N.factorial := (N.factorial / 2 : ℕ)
  let a : ZMod N.factorial := (N.factorial / p : ℕ)
  let b : ZMod N.factorial := (N.factorial / q : ℕ)
  let c : ZMod N.factorial := (N.factorial / r : ℕ)
  change (d+a+b)+(d-a+c)+(d+b+c)+(d-2•b-2•c) = 0
  change d+d = 0 at hz
  simp only [two_nsmul]
  linear_combination 2 * hz

/-- Coprime addition and invertibility of two preserve each exact odd order. -/
theorem frequencies_orders {N p q r : ℕ}
    (hN : 2 ≤ N) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpN : p ∈ Finset.Icc 1 N) (hqN : q ∈ Finset.Icc 1 N)
    (hrN : r ∈ Finset.Icc 1 N)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r)
    (i : Fin 4) :
    addOrderOf (frequencies N p q r i) = ![2*p*q,2*p*r,2*q*r,2*q*r] i := by
  let d : ZMod N.factorial := (N.factorial / 2 : ℕ)
  let a : ZMod N.factorial := (N.factorial / p : ℕ)
  let b : ZMod N.factorial := (N.factorial / q : ℕ)
  let c : ZMod N.factorial := (N.factorial / r : ℕ)
  have hd : addOrderOf d = 2 := frequency_order (Finset.mem_Icc.mpr ⟨by omega,hN⟩)
  have ha : addOrderOf a = p := frequency_order hpN
  have hb : addOrderOf b = q := frequency_order hqN
  have hc : addOrderOf c = r := frequency_order hrN
  have hna : addOrderOf (-a) = p := by simpa only [addOrderOf_neg] using ha
  have hnb : addOrderOf (-(2•b)) = q := by
    rw [addOrderOf_neg]
    exact (show Nat.Coprime (addOrderOf b) 2 by rw [hb]; exact hq.coprime_two_right).addOrderOf_nsmul.trans hb
  have hnc : addOrderOf (-(2•c)) = r := by
    rw [addOrderOf_neg]
    exact (show Nat.Coprime (addOrderOf c) 2 by rw [hc]; exact hr.coprime_two_right).addOrderOf_nsmul.trans hc
  fin_cases i
  · exact add_order (d+a) b (add_order d a hd ha hp.coprime_two_left) hb
      (hq.coprime_two_left.mul_left hpq)
  · change addOrderOf (d-a+c) = 2*p*r
    rw [sub_eq_add_neg]
    exact add_order (d+(-a)) c (add_order d (-a) hd hna hp.coprime_two_left) hc
      (hr.coprime_two_left.mul_left hpr)
  · exact add_order (d+b) c (add_order d b hd hb hq.coprime_two_left) hc
      (hr.coprime_two_left.mul_left hqr)
  · change addOrderOf (d-2•b-2•c) = 2*q*r
    simp only [sub_eq_add_neg]
    exact add_order (d+(-(2•b))) (-(2•c))
      (add_order d (-(2•b)) hd hnb hq.coprime_two_left) hnc
      (hr.coprime_two_left.mul_left hqr)

/-- A Fourier readout of the literal fourth translated observation array. -/
def fourthReadout (N p q r : ℕ) (c : ℕ → ℝ) : ℝ :=
  (momentDFT (fun h : Fin 4 → ZMod N.factorial =>
    (translatedMoment N c (fun i => (h i).val) : ℂ)) (frequencies N p q r)).re

/-- A realized overlap reads the relative sign of two modes through a third mode. -/
theorem fourthReadout_eq {N p q r : ℕ}
    (hN : 2 ≤ N) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpN : p ∈ Finset.Icc 1 N) (hqN : q ∈ Finset.Icc 1 N)
    (hrN : r ∈ Finset.Icc 1 N)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r) (hqr : Nat.Coprime q r)
    (c : ℕ → ℝ) :
    fourthReadout N p q r c = (N.factorial : ℝ)^4 *
      selbergMultiplesCoord N c (2*p*q) * selbergMultiplesCoord N c (2*p*r) *
        selbergMultiplesCoord N c (2*q*r)^2 := by
  unfold fourthReadout
  simp_rw [translatedMoment_complex_eq,ZMod.natCast_zmod_val]
  rw [momentDFT_sieve,if_pos (frequencies_sum hN)]
  simp_rw [frequencies_orders hN hp hq hr hpN hqN hrN hpq hpr hqr]
  rw [Fin.prod_univ_four]
  change ((N.factorial : ℂ)^4 *
    (coordinate N (fun d => (c d : ℂ)) (2*p*q) *
      coordinate N (fun d => (c d : ℂ)) (2*p*r) *
      coordinate N (fun d => (c d : ℂ)) (2*q*r) *
      coordinate N (fun d => (c d : ℂ)) (2*q*r))).re = _
  simp only [coordinate_ofReal]
  norm_cast
  ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.CoprimeOverlap
