import GaloisForLFunctions.HTGeometry.MeromorphicPolePrimitive
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Nat.Choose.Basic

/-!
# The polynomial at infinity of a heat Hankel normal block

The coefficients below solve the singular heat connection exactly. The
degree `k` polynomial retains every coefficient of the packet lost by the
projective contraction to the preceding regular head.
-/

open Filter Topology Polynomial

namespace HTGeometry
noncomputable section

/-- Increasing the cancellation exponent makes the extended value zero. -/
theorem ScaledAnalyticGerm.raise {f : ℝ → ℝ} {a c : ℝ} {k l : ℕ}
    (h : ScaledAnalyticGerm f a k c) (hkl : k < l) :
    ScaledAnalyticGerm f a l 0 := by
  obtain ⟨g, hg, _, he⟩ := h
  refine ⟨fun t => (t - a) ^ (l - k) * g t,
    ((analyticAt_id.sub analyticAt_const).pow _).mul hg, ?_, ?_⟩
  · simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hkl)]
  · filter_upwards [he] with t ht
    rw [← ht, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hkl.le]

/-- Coefficient of `X^j` in the universal degree `k` escaping packet. -/
def heatEscapeCoeff (d k j : ℕ) : ℝ :=
  (k.choose j : ℝ) * ((d - 1 - j).descFactorial (k - j) : ℝ)

/-- The universal packet attached to an offset `k` in a block of length `d`. -/
def heatEscapePolynomial (d k : ℕ) : ℝ[X] :=
  Polynomial.ofFn (k + 1) (fun j : Fin (k + 1) => heatEscapeCoeff d k j)

@[simp] theorem heatEscapeCoeff_self (d k : ℕ) : heatEscapeCoeff d k k = 1 := by
  simp [heatEscapeCoeff]

theorem heatEscapeCoeff_step {d k j : ℕ} (hj : j ≤ k) :
    ((k + 1 - j : ℕ) : ℝ) * heatEscapeCoeff d (k + 1) j =
      (((k + 1) * (d - (k + 1)) : ℕ) : ℝ) * heatEscapeCoeff d k j := by
  have hidx : k + 1 - j = (k - j) + 1 := by omega
  have hsub : d - 1 - j - (k - j) = d - (k + 1) := by omega
  have hchoose := Nat.choose_mul_succ_eq k j
  have hc : ((k + 1 - j : ℕ) : ℝ) * ((k + 1).choose j : ℝ) =
      ((k + 1 : ℕ) : ℝ) * (k.choose j : ℝ) := by
    have hnat : (k + 1 - j) * (k + 1).choose j = (k + 1) * k.choose j := by
      calc
        _ = (k + 1).choose j * (k + 1 - j) := Nat.mul_comm _ _
        _ = k.choose j * (k + 1) := hchoose.symm
        _ = (k + 1) * k.choose j := Nat.mul_comm _ _
    exact_mod_cast hnat
  unfold heatEscapeCoeff
  rw [hidx, Nat.descFactorial_succ, hsub, Nat.cast_mul, Nat.cast_mul]
  rw [← hidx, ← mul_assoc, hc]
  ring

theorem heatEscapePolynomial_coeff {d k j : ℕ} (hj : j ≤ k) :
    (heatEscapePolynomial d k).coeff j = heatEscapeCoeff d k j :=
  Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)

theorem heatEscapePolynomial_coeff_gt {d k j : ℕ} (hj : k < j) :
    (heatEscapePolynomial d k).coeff j = 0 :=
  Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)

/-- Deficit indexing exhibits the rising-factorial form of the packet. -/
theorem heatEscapePolynomial_coeff_deficit {d k l : ℕ} (hkd : k < d) (hl : l ≤ k) :
    (heatEscapePolynomial d k).coeff (k - l) =
      (k.choose l : ℝ) * ((d - k).ascFactorial l : ℝ) := by
  rw [heatEscapePolynomial_coeff (by omega), heatEscapeCoeff, Nat.choose_symm hl,
    Nat.sub_sub_self hl]
  have hidx : d - 1 - (k - l) = d - k + l - 1 := by omega
  rw [hidx, Nat.add_descFactorial_eq_ascFactorial']

/-- No part of the escaping packet remains at the zero of the scaled variable. -/
theorem heatEscapePolynomial_coeff_zero_pos {d k : ℕ} (hkd : k < d) :
    0 < (heatEscapePolynomial d k).coeff 0 := by
  rw [heatEscapePolynomial_coeff (Nat.zero_le k), heatEscapeCoeff]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  exact_mod_cast (Nat.descFactorial_pos.mpr (show k ≤ d - 1 by omega))

end
end HTGeometry
