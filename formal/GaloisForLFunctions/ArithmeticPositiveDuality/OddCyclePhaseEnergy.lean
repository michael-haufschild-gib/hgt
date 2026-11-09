import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval

/-!
# Sharp phase energy on an odd cycle

The least real part of an odd cyclic character is `-cos (π/q)`. Parseval
transfers this spectral bound to cycle edges. Partial products then give the
sharp squared-defect bound for unit phases whose product is one.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem odd_cosine_lower {q : ℕ} (hq : Odd q) (k : ℕ) (hk : k < q) :
    -Real.cos (Real.pi / q) ≤ Real.cos (2 * Real.pi * k / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hsmall (m : ℕ) (hm : 2 * m < q) :
      -Real.cos (Real.pi / q) ≤ Real.cos (2 * Real.pi * m / q) := by
    have hmR : 2 * (m : ℝ) + 1 ≤ q := by exact_mod_cast hm
    have hangle : 2 * Real.pi * m / q ≤ Real.pi - Real.pi / q := by
      rw [show Real.pi - Real.pi / q = Real.pi * (q - 1) / q by
        field_simp]
      apply (div_le_div_iff_of_pos_right hqR).mpr
      nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hmR)]
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : 0 ≤ 2 * Real.pi * m / q)
      (sub_le_self Real.pi (by positivity : 0 ≤ Real.pi / q)) hangle
    rwa [Real.cos_pi_sub] at h
  by_cases hhalf : 2 * k < q
  · exact hsmall k hhalf
  · have hfold : 2 * (q - k) < q := by
      obtain ⟨r, hr⟩ := hq
      omega
    have h := hsmall (q - k) hfold
    have he : 2 * Real.pi * ((q - k : ℕ) : ℝ) / q =
        2 * Real.pi - 2 * Real.pi * k / q := by
      rw [Nat.cast_sub hk.le]
      field_simp
    rwa [he, Real.cos_two_pi_sub] at h

private theorem character_sq_defect_lower {q : ℕ} [NeZero q] (hq : Odd q)
    (k : ZMod q) :
    2 * (1 - Real.cos (Real.pi / q)) ≤ Complex.normSq (ZMod.stdAddChar k + 1) := by
  have he : ZMod.stdAddChar k =
      Complex.exp (((2 * Real.pi * k.val / q : ℝ) : ℂ) * I) := by
    calc
      _ = ZMod.stdAddChar (((k.val : ℤ) : ZMod q)) := by congr 1; simp
      _ = _ := by
        rw [ZMod.stdAddChar_coe]
        congr 1
        push_cast
        ring
  have hre : (ZMod.stdAddChar k).re = Real.cos (2 * Real.pi * k.val / q) := by
    rw [he, Complex.exp_ofReal_mul_I_re]
  have hn : Complex.normSq (ZMod.stdAddChar k) = 1 := by
    rw [Complex.normSq_eq_norm_sq, ZMod.stdAddChar_apply, Circle.norm_coe, one_pow]
  rw [Complex.normSq_add, hn]
  simp only [map_one, mul_one]
  rw [hre]
  linarith only [odd_cosine_lower hq k.val k.val_lt]

private theorem dft_cycle_shift {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (t k : ZMod q) :
    ZMod.dft (fun j => f (t + j)) k = ZMod.stdAddChar (t * k) * ZMod.dft f k := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft t)
    (fun j => ZMod.stdAddChar (-(j * k)) * f (t + j))
    (fun j => ZMod.stdAddChar (t * k) * (ZMod.stdAddChar (-(j * k)) * f j)) ?_
  intro j
  change ZMod.stdAddChar (-(j * k)) * f (t + j) =
    ZMod.stdAddChar (t * k) * (ZMod.stdAddChar (-((t + j) * k)) * f (t + j))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [show t * k + -((t + j) * k) = -(j * k) by ring]

/-- The odd-cycle adjacency spectrum gives a sharp lower bound for edge sums. -/
theorem odd_cycle_edge_energy {q : ℕ} [NeZero q] (hq : Odd q) (f : ZMod q → ℂ) :
    2 * (1 - Real.cos (Real.pi / q)) * (∑ j, Complex.normSq (f j)) ≤
      ∑ j, Complex.normSq (f (1 + j) + f j) := by
  have hdft (k : ZMod q) :
      ZMod.dft (fun j => f (1 + j) + f j) k =
        (ZMod.stdAddChar k + 1) * ZMod.dft f k := by
    change ZMod.dft ((fun j => f (1 + j)) + f) k = _
    rw [map_add]
    change ZMod.dft (fun j => f (1 + j)) k + ZMod.dft f k = _
    rw [dft_cycle_shift, one_mul]
    ring
  have hsum : 2 * (1 - Real.cos (Real.pi / q)) *
      (∑ k, Complex.normSq (ZMod.dft f k)) ≤
        ∑ k, Complex.normSq (ZMod.dft (fun j => f (1 + j) + f j) k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [hdft, Complex.normSq_mul]
    exact mul_le_mul_of_nonneg_right (character_sq_defect_lower hq k)
      (Complex.normSq_nonneg _)
  rw [RHTower.fieldOneFiniteCyclicFourier_parseval,
    RHTower.fieldOneFiniteCyclicFourier_parseval] at hsum
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  apply le_of_mul_le_mul_left (a := (q : ℝ)) _ hqR
  nlinarith only [hsum]

private theorem cycle_next_val {q : ℕ} [NeZero q] (hq : 1 < q) (j : ZMod q) :
    (1 + j).val = if j.val + 1 < q then j.val + 1 else 0 := by
  have hone : (1 : ZMod q).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hq]
  rw [ZMod.val_add, hone, add_comm 1]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have hj := j.val_lt
    have he : j.val + 1 = q := by omega
    rw [he, Nat.mod_self]

/-- Unit phases with product one pay the sharp odd-cycle defect energy. -/
theorem odd_unit_product_phase_energy {q : ℕ} [NeZero q] (hq : Odd q) (h3 : 3 ≤ q)
    (u : ZMod q → ℂ) (hu : ∀ j, ‖u j‖ = 1) (hp : ∏ j, u j = 1) :
    2 * (q : ℝ) * (1 - Real.cos (Real.pi / q)) ≤ ∑ j, ‖u j + 1‖ ^ 2 := by
  let f : ZMod q → ℂ := fun j => ∏ k ∈ Finset.range j.val, u (k : ZMod q)
  have hf (j : ZMod q) : ‖f j‖ = 1 := by
    simp only [f, norm_prod, hu, Finset.prod_const_one]
  have hpRange : (∏ k ∈ Finset.range q, u (k : ZMod q)) = 1 := by
    calc
      _ = ∏ k : Fin q, u ((k : ℕ) : ZMod q) := (Fin.prod_univ_eq_prod_range _ q).symm
      _ = ∏ k : ZMod q, u k := by
        cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ n =>
          apply Finset.prod_congr rfl
          intro k _
          congr 1
          exact ZMod.natCast_zmod_val (n := n + 1) k
      _ = 1 := hp
  have hstep (j : ZMod q) : f (1 + j) = f j * u j := by
    have hv := cycle_next_val (by omega : 1 < q) j
    by_cases hlt : j.val + 1 < q
    · rw [if_pos hlt] at hv
      simp only [f, hv, Finset.prod_range_succ, ZMod.natCast_zmod_val]
    · rw [if_neg hlt] at hv
      have hj := j.val_lt
      have hlast : j.val + 1 = q := by omega
      have he : (∏ k ∈ Finset.range (j.val + 1), u (k : ZMod q)) = 1 := by
        rw [hlast, hpRange]
      rw [Finset.prod_range_succ, ZMod.natCast_zmod_val] at he
      simpa only [f, hv, Finset.range_zero, Finset.prod_empty] using he.symm
  have h := odd_cycle_edge_energy hq f
  have hs : (∑ j, Complex.normSq (f (1 + j) + f j)) = ∑ j, ‖u j + 1‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hstep, show f j * u j + f j = f j * (u j + 1) by ring,
      Complex.normSq_mul, Complex.normSq_eq_norm_sq (f j), hf, one_pow, one_mul,
      Complex.normSq_eq_norm_sq]
  rw [hs] at h
  simp only [Complex.normSq_eq_norm_sq, hf, one_pow, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  nlinarith only [h]

#print axioms odd_cycle_edge_energy
#print axioms odd_unit_product_phase_energy

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
