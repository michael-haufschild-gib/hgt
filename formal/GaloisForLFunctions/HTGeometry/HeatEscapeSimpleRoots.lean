import GaloisForLFunctions.HTGeometry.HeatEscapeNonreal
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Separable

/-!
# No ramification in a heat escaping packet

The derivative and raising recurrences descend any hypothetical multiple root
to a multiple root of the constant packet. All escaping residues are therefore
nonzero and simple, without a genericity assumption on the heat contact.
-/

open Polynomial

namespace HTGeometry
noncomputable section

@[simp] theorem heatEscapePolynomial_zero (d : ℕ) : heatEscapePolynomial d 0 = 1 := by
  ext j
  cases j with
  | zero => simp [heatEscapePolynomial_coeff, heatEscapeCoeff]
  | succ j => simp [heatEscapePolynomial_coeff_gt (by omega : 0 < j + 1), coeff_one]

/-- Differentiation lowers both the block length and the packet degree. -/
theorem heatEscapePolynomial_derivative (d k : ℕ) :
    derivative (heatEscapePolynomial (d + 1) (k + 1)) =
      C (k + 1 : ℝ) * heatEscapePolynomial d k := by
  ext j
  rw [coeff_derivative, coeff_C_mul]
  by_cases hj : j ≤ k
  · rw [heatEscapePolynomial_coeff (by omega), heatEscapePolynomial_coeff hj]
    have hidx : d + 1 - 1 - (j + 1) = d - 1 - j := by omega
    have hc : ((k + 1).choose (j + 1) : ℝ) * (j + 1) =
        (k + 1) * (k.choose j : ℝ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq k j).symm
    simp only [heatEscapeCoeff, Nat.add_sub_add_right, hidx]
    nlinarith only [hc]
  · rw [heatEscapePolynomial_coeff_gt (by omega),
      heatEscapePolynomial_coeff_gt (by omega)]
    simp

/-- The raising recurrence controls common roots with the derivative. -/
theorem heatEscapePolynomial_raise {d k : ℕ} (hkd : k < d) :
    heatEscapePolynomial (d + 1) (k + 1) =
      (X + C (d : ℝ)) * heatEscapePolynomial d k -
        X * derivative (heatEscapePolynomial d k) := by
  ext j
  rw [add_mul, coeff_sub, coeff_add, coeff_C_mul]
  cases j with
  | zero =>
    simp only [coeff_X_mul_zero, zero_add, sub_zero]
    rw [heatEscapePolynomial_coeff (by omega), heatEscapePolynomial_coeff (by omega)]
    simp only [heatEscapeCoeff, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    have hd : d = (d - 1) + 1 := by omega
    rw [show d + 1 - 1 = d by omega, hd, Nat.succ_descFactorial_succ]
    push_cast
    rfl
  | succ j =>
    rw [coeff_X_mul, coeff_X_mul, coeff_derivative]
    by_cases hj : j < k
    · rw [heatEscapePolynomial_coeff (by omega), heatEscapePolynomial_coeff (by omega),
        heatEscapePolynomial_coeff (by omega)]
      have hidx : d + 1 - 1 - (j + 1) = d - 1 - j := by omega
      have hstep : d - 1 - j = (d - 1 - (j + 1)) + 1 := by omega
      have hlen : k - j = (k - (j + 1)) + 1 := by omega
      have hc : ((k + 1).choose (j + 1) : ℝ) =
          (k.choose j : ℝ) + (k.choose (j + 1) : ℝ) := by
        exact_mod_cast Nat.choose_succ_succ' k j
      have hd : ((d - 1 - (j + 1) : ℕ) : ℝ) + 1 = (d : ℝ) - (j + 1) := by
        have hn : d - 1 - (j + 1) + 1 + (j + 1) = d := by omega
        have hr : ((d - 1 - (j + 1) : ℕ) : ℝ) + 1 + (j + 1) = (d : ℝ) := by
          exact_mod_cast hn
        linarith
      simp only [heatEscapeCoeff, Nat.add_sub_add_right, hidx]
      rw [hc, hstep, hlen, Nat.succ_descFactorial_succ]
      push_cast
      rw [hd]
      ring
    · by_cases he : j = k
      · subst j
        rw [heatEscapePolynomial_coeff le_rfl, heatEscapeCoeff_self,
          heatEscapePolynomial_coeff le_rfl, heatEscapeCoeff_self,
          heatEscapePolynomial_coeff_gt (by omega)]
        simp
      · rw [heatEscapePolynomial_coeff_gt (by omega),
          heatEscapePolynomial_coeff_gt (by omega),
          heatEscapePolynomial_coeff_gt (by omega)]
        simp

/-- No escaping residue is zero. -/
theorem heatEscapePolynomial_root_ne_zero {d k : ℕ} (hkd : k < d)
    {z : ℂ} (hz : aeval z (heatEscapePolynomial d k) = 0) : z ≠ 0 := by
  intro he
  subst z
  have hc : (heatEscapePolynomial d k).coeff 0 ≠ 0 :=
    ne_of_gt (heatEscapePolynomial_coeff_zero_pos hkd)
  have hz' : ((heatEscapePolynomial d k).coeff 0 : ℂ) = 0 := by
    simpa [aeval_def] using hz
  exact hc (Complex.ofReal_eq_zero.mp hz')

/-- Every escaping residue is simple, including at multiple heat contacts. -/
theorem heatEscapePolynomial_root_simple {d k : ℕ} (hkd : k < d)
    {z : ℂ} (hz : aeval z (heatEscapePolynomial d k) = 0) :
    aeval z (derivative (heatEscapePolynomial d k)) ≠ 0 := by
  induction k generalizing d with
  | zero => simp at hz
  | succ k ih =>
    cases d with
    | zero => omega
    | succ d =>
      have hk : k < d := by omega
      have hz0 := heatEscapePolynomial_root_ne_zero hkd hz
      intro hd
      rw [heatEscapePolynomial_derivative] at hd
      have hk0 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have hzold : aeval z (heatEscapePolynomial d k) = 0 := by
        simp only [map_mul, map_add, map_natCast, map_one] at hd
        exact (mul_eq_zero.mp hd).resolve_left hk0
      have hrec := congrArg (aeval z : ℝ[X] →ₐ[ℝ] ℂ) (heatEscapePolynomial_raise hk)
      simp only [hz, map_sub, map_mul, map_add, aeval_X, aeval_C, hzold,
        mul_zero, zero_sub] at hrec
      have hdold : aeval z (derivative (heatEscapePolynomial d k)) = 0 := by
        exact (mul_eq_zero.mp (neg_eq_zero.mp hrec.symm)).resolve_left hz0
      exact ih hk hzold hdold

/-- The zero cluster from the regular head does not affect escaping-root simplicity. -/
theorem heatEscapePolynomial_shift_root_simple {d k : ℕ} (hkd : k < d)
    (n : ℕ) {z : ℂ} (hz : aeval z (heatEscapePolynomial d k) = 0) :
    aeval z (derivative (X ^ n * heatEscapePolynomial d k)) ≠ 0 := by
  rw [derivative_mul]
  simp only [map_add, map_mul, hz, mul_zero, zero_add, map_pow, aeval_X]
  exact mul_ne_zero (pow_ne_zero _ (heatEscapePolynomial_root_ne_zero hkd hz))
    (heatEscapePolynomial_root_simple hkd hz)

/-- Simplicity is a theorem about the entire packet, not an assumed root condition. -/
theorem heatEscapePolynomial_separable {d k : ℕ} (hkd : k < d) :
    (heatEscapePolynomial d k).Separable := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).mpr
  intro z
  by_cases hz : aeval z (heatEscapePolynomial d k) = 0
  · exact Or.inr (heatEscapePolynomial_root_simple hkd hz)
  · exact Or.inl hz

/-- A degree `k` packet has exactly `k` distinct complex residues. -/
theorem heatEscapePolynomial_card_rootSet {d k : ℕ} (hkd : k < d) :
    Fintype.card ((heatEscapePolynomial d k).rootSet ℂ) = k := by
  rw [Polynomial.card_rootSet_eq_natDegree (heatEscapePolynomial_separable hkd)
    (IsAlgClosed.splits _), heatEscapePolynomial_natDegree]

/-- Weighted blow-up preserves monicity and degree even at scale zero. -/
theorem weightedPolynomial_monic_natDegree {p : ℝ[X]} {N : ℕ}
    (hp : p.Monic) (hN : p.natDegree = N) (ε : ℝ) :
    (weightedPolynomial p N ε).Monic ∧ (weightedPolynomial p N ε).natDegree = N := by
  have hc : (weightedPolynomial p N ε).coeff N = 1 := by
    rw [weightedPolynomial, ofFn_coeff_eq_val_of_lt _ (by omega)]
    simp only [Nat.sub_self, pow_zero, one_mul, ← hN, hp.coeff_natDegree]
  have hn : (weightedPolynomial p N ε).natDegree = N := by
    apply le_antisymm
    · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
    · exact le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero)
  exact ⟨by rw [Monic, leadingCoeff, hn, hc], hn⟩

/-- Exact transport of complex roots through the weighted blow-up. -/
theorem weightedPolynomial_aeval {p : ℝ[X]} {N : ℕ} {ε : ℝ}
    (hp : p.natDegree ≤ N) (hε : ε ≠ 0) (z : ℂ) :
    aeval z (weightedPolynomial p N ε) =
      (ε : ℂ) ^ N * aeval (z / (ε : ℂ)) p := by
  rw [weightedPolynomial_eq hp hε]
  simp only [map_mul, aeval_C, aeval_comp, aeval_X, map_pow]
  change (ε : ℂ) ^ N * aeval (((ε⁻¹ : ℝ) : ℂ) * z) p = _
  rw [Complex.ofReal_inv]
  rw [div_eq_mul_inv, mul_comm (ε : ℂ)⁻¹ z]

theorem weightedPolynomial_aeval_eq_zero_iff {p : ℝ[X]} {N : ℕ} {ε : ℝ}
    (hp : p.natDegree ≤ N) (hε : ε ≠ 0) (z : ℂ) :
    aeval z (weightedPolynomial p N ε) = 0 ↔ aeval (z / (ε : ℂ)) p = 0 := by
  rw [weightedPolynomial_aeval hp hε]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero N (Complex.ofReal_ne_zero.mpr hε)))

end
end HTGeometry
