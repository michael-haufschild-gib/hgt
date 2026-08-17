import GaloisForLFunctions.HTGeometry.BoundedDiscExpansion

/-!
# Expansions with a single controlling constant

Tracking the error constant and the disc bound separately is unnecessary once one only wants the
size of the assembled constant: bounding both by one scalar turns every closure rule into an
explicit arithmetic operation on that scalar, so the constant of a long product is an explicit
expression in the constants of its factors.  This is what makes an expansion uniform over a family
of shell parameters.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

/-- Raising the error constant of an expansion. -/
theorem HasPolyExpansion.weaken {r C C' : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (h : HasPolyExpansion r n C f P) (hCC : C ≤ C') : HasPolyExpansion r n C' f P := fun w hw =>
  le_trans (h w hw) (mul_le_mul_of_nonneg_right hCC (pow_nonneg (norm_nonneg w) n))

/-- An expansion whose error constant and whose bound on the disc are both at most `S`. -/
def BddExpS (r : ℝ) (n : ℕ) (S : ℝ) (f : ℂ → ℂ) (P : Polynomial ℂ) : Prop :=
  1 ≤ S ∧ (∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ S) ∧ HasPolyExpansion r n S f P

theorem BddExpS.one_le {r S : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (h : BddExpS r n S f P) : 1 ≤ S := h.1

theorem BddExpS.weaken {r S T : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ}
    (h : BddExpS r n S f P) (hST : S ≤ T) : BddExpS r n T f P :=
  ⟨le_trans h.1 hST, fun w hw => le_trans (h.2.1 w hw) hST, h.2.2.weaken hST⟩

theorem BddExpS.norm_poly_le {r S : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (h : BddExpS r n S f P) {w : ℂ} (hw : ‖w‖ ≤ r) : ‖P.eval w‖ ≤ 2 * S := by
  have hS0 : (0 : ℝ) ≤ S := by linarith [h.1]
  have hrn : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1
  have := h.2.2.norm_poly_le h.2.1 hS0 hw
  nlinarith

theorem BddExpS.add {r S T : ℝ} {n : ℕ} {f g : ℂ → ℂ} {P Q : Polynomial ℂ}
    (hf : BddExpS r n S f P) (hg : BddExpS r n T g Q) :
    BddExpS r n (S + T) (fun w => f w + g w) (P + Q) :=
  ⟨by linarith [hf.1, hg.1],
    fun w hw => le_trans (norm_add_le _ _) (add_le_add (hf.2.1 w hw) (hg.2.1 w hw)),
    hf.2.2.add hg.2.2⟩

theorem BddExpS.mul {r S T : ℝ} {n : ℕ} {f g : ℂ → ℂ} {P Q : Polynomial ℂ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hf : BddExpS r n S f P) (hg : BddExpS r n T g Q) :
    BddExpS r n (3 * S * T) (fun w => f w * g w) (P * Q) := by
  have hS0 : (0 : ℝ) ≤ S := by linarith [hf.1]
  have hT0 : (0 : ℝ) ≤ T := by linarith [hg.1]
  refine ⟨by nlinarith [hf.1, hg.1], fun w hw => ?_, ?_⟩
  · rw [norm_mul]
    have h1 := hf.2.1 w hw
    have h2 := hg.2.1 w hw
    nlinarith [norm_nonneg (f w), norm_nonneg (g w)]
  · exact (hf.2.2.mul hg.2.2 hg.2.1 (fun w hw => hf.norm_poly_le hr0 hr1 hw) hS0).weaken
      (by nlinarith)

theorem BddExpS.const_mul {r S : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (c : ℂ)
    (hf : BddExpS r n S f P) :
    BddExpS r n (max 1 ‖c‖ * S) (fun w => c * f w) (Polynomial.C c * P) := by
  have hS0 : (0 : ℝ) ≤ S := by linarith [hf.1]
  have hm1 : (1 : ℝ) ≤ max 1 ‖c‖ := le_max_left _ _
  have hmc : ‖c‖ ≤ max 1 ‖c‖ := le_max_right _ _
  refine ⟨by nlinarith [hf.1], fun w hw => ?_, (hf.2.2.const_mul c).weaken (by nlinarith)⟩
  rw [norm_mul]
  have := hf.2.1 w hw
  nlinarith [norm_nonneg c]

theorem BddExpS.finsetSum {ι : Type*} {r : ℝ} {n : ℕ} (s : Finset ι) {f : ι → ℂ → ℂ}
    {P : ι → Polynomial ℂ} {S : ι → ℝ} (h : ∀ i ∈ s, BddExpS r n (S i) (f i) (P i)) :
    BddExpS r n (1 + ∑ i ∈ s, S i) (fun w => ∑ i ∈ s, f i w) (∑ i ∈ s, P i) := by
  have hsum : (0 : ℝ) ≤ ∑ i ∈ s, S i :=
    Finset.sum_nonneg fun i hi => by linarith [(h i hi).1]
  refine ⟨by linarith, fun w hw => ?_, ?_⟩
  · refine le_trans (norm_sum_le _ _) ?_
    have hle : ∑ i ∈ s, ‖f i w‖ ≤ ∑ i ∈ s, S i :=
      Finset.sum_le_sum fun i hi => (h i hi).2.1 w hw
    linarith
  · exact (HasPolyExpansion.finsetSum s (fun i hi => (h i hi).2.2)).weaken (by linarith)

theorem BddExpS.mono {r S : ℝ} {n n' : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hn : n' ≤ n) (hf : BddExpS r n S f P) : BddExpS r n' S f P := by
  have hS0 : (0 : ℝ) ≤ S := by linarith [hf.1]
  have hrn : r ^ (n - n') ≤ 1 := pow_le_one₀ hr0 hr1
  exact ⟨hf.1, hf.2.1, (hf.2.2.mono hS0 hn).weaken (by nlinarith)⟩

/-- **The exponential, with an explicit constant separating the linear rate from the rest.** -/
theorem bddExpS_cexp {r S K : ℝ} {n : ℕ} {f : ℂ → ℂ} {P : Polynomial ℂ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hf : BddExpS r n S f P) (hK : 0 ≤ K)
    (hsmall : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ K * ‖w‖)
    (htiny : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ / ((n : ℝ) + 1) ≤ 1 / 2) :
    BddExpS r n (2 * K ^ n + (n : ℝ) ^ 2 * 2 ^ n * S ^ (n + 1) + Real.exp (2 * S) + 1)
      (fun w => Complex.exp (f w))
      (∑ j ∈ Finset.range n, Polynomial.C (((Nat.factorial j : ℕ) : ℂ)⁻¹) * P ^ j) := by
  have hS1 := hf.1
  have hS0 : (0 : ℝ) ≤ S := by linarith
  have h2S : (1 : ℝ) ≤ 2 * S := by linarith
  have hfb : ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ 2 * S := fun w hw => by
    have := hf.2.1 w hw
    linarith
  have hPb : ∀ w : ℂ, ‖w‖ ≤ r → ‖P.eval w‖ ≤ 2 * S := fun w hw => hf.norm_poly_le hr0 hr1 hw
  have hexp := hf.2.2.cexp hfb hPb h2S hS0 hsmall htiny
  have hfacn : (1 : ℝ) ≤ (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hKn : (0 : ℝ) ≤ K ^ n := pow_nonneg hK n
  have hhead : 2 * K ^ n / (Nat.factorial n : ℝ) ≤ 2 * K ^ n := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hterm : ∀ j ∈ Finset.range n, S * (j : ℝ) * (2 * S) ^ j / (Nat.factorial j : ℝ)
      ≤ S * (n : ℝ) * (2 * S) ^ n := by
    intro j hj
    have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
    have hfacj : (1 : ℝ) ≤ (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hpj : (2 * S) ^ j ≤ (2 * S) ^ n := pow_le_pow_right₀ h2S hjn
    have hpj0 : (0 : ℝ) ≤ (2 * S) ^ j := pow_nonneg (by linarith) j
    have hjr : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc S * (j : ℝ) * (2 * S) ^ j / (Nat.factorial j : ℝ)
        ≤ S * (j : ℝ) * (2 * S) ^ j :=
          div_le_self (mul_nonneg (mul_nonneg hS0 hj0) hpj0) hfacj
      _ ≤ S * (n : ℝ) * (2 * S) ^ j := by
          nlinarith [mul_nonneg (mul_nonneg hS0 hpj0) (sub_nonneg.mpr hjr)]
      _ ≤ S * (n : ℝ) * (2 * S) ^ n := by
          nlinarith [mul_nonneg (mul_nonneg hS0 hn0) (sub_nonneg.mpr hpj)]
  have hsum : ∑ j ∈ Finset.range n, S * (j : ℝ) * (2 * S) ^ j / (Nat.factorial j : ℝ)
      ≤ (n : ℝ) ^ 2 * 2 ^ n * S ^ (n + 1) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow]
    exact le_of_eq (by ring)
  have hexpb : (0 : ℝ) < Real.exp (2 * S) := Real.exp_pos _
  have hA : (0 : ℝ) ≤ 2 * K ^ n := by linarith
  have hB : (0 : ℝ) ≤ (n : ℝ) ^ 2 * 2 ^ n * S ^ (n + 1) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) n)) (pow_nonneg hS0 (n + 1))
  refine ⟨by linarith, fun w hw => ?_, hexp.weaken (by linarith)⟩
  rw [Complex.norm_exp]
  have hre : (f w).re ≤ 2 * S := le_trans (Complex.re_le_norm _) (hfb w hw)
  have hle := Real.exp_le_exp.mpr hre
  linarith

end

end GaloisForLFunctions.HTGeometry
