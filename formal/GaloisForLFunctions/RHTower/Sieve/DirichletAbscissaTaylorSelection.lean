import Mathlib

/-!
# Moving a large value of a Dirichlet polynomial to a fixed abscissa

Zero detection produces large values of a Dirichlet polynomial `F(s) = Σ_{k ∈ S} c_k k^{-s}` at the
zeros `ρ = β + iγ` themselves, whose real parts vary.  Large-value theorems count points on one
vertical line.  The transfer is a finite Taylor expansion in the real part.  If
`0 ≤ δ` and `δ log k ≤ δΛ ≤ 1` on the support, then

`F(σ₀ + δ + iγ) = Σ_{i < I} ((-δΛ)^i / i!) P_i(σ₀ + iγ) + O(Σ_k |c_k| k^{-σ₀} · 2/I!)`,

with the companion polynomials `P_i(s) = Σ_{k ∈ S} c_k (log k / Λ)^i k^{-s}`.  Their coefficients
are those of `F` damped by weights in `[0, 1]`.  Hence a large value `V` of `F` at `σ₀ + δ + iγ`
forces a large value `V/6` of some `P_i` with `i < I` at `σ₀ + iγ`, as soon as the Taylor tail is
below `V/2`.  Every loss is a fixed constant or a factor `I`.
-/

namespace RHTower.Sieve

open Complex Finset

noncomputable section

/-- The companion polynomial with weight `(log k / Λ)^i`, evaluated at `σ + iγ`. -/
def abscissaTaylorPoly (S : Finset ℕ) (c : ℕ → ℂ) (Λ : ℝ) (i : ℕ) (σ γ : ℝ) : ℂ :=
  ∑ k ∈ S, c k * (((Real.log k / Λ) ^ i : ℝ) : ℂ) * (k : ℂ) ^ (-((σ : ℂ) + (γ : ℂ) * I))

/-- The polynomial `F` itself at `σ + iγ`. -/
def abscissaDirichletValue (S : Finset ℕ) (c : ℕ → ℂ) (σ γ : ℝ) : ℂ :=
  ∑ k ∈ S, c k * (k : ℂ) ^ (-((σ : ℂ) + (γ : ℂ) * I))

theorem natCast_cpow_shift_real {k : ℕ} (hk : 1 ≤ k) (σ δ γ : ℝ) :
    (k : ℂ) ^ (-(((σ + δ : ℝ) : ℂ) + (γ : ℂ) * I))
      = (k : ℂ) ^ (-((σ : ℂ) + (γ : ℂ) * I)) * ((Real.exp (-(δ * Real.log k)) : ℝ) : ℂ) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk0' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [show -(((σ + δ : ℝ) : ℂ) + (γ : ℂ) * I) = -((σ : ℂ) + (γ : ℂ) * I) + ((-δ : ℝ) : ℂ) by
    push_cast; ring, Complex.cpow_add _ _ hk0]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hk0'.le, Real.rpow_def_of_pos hk0']
  congr 2
  ring

/-- **Taylor transfer of a large value to a fixed abscissa.**  If `V ≤ |F(σ₀ + δ + iγ)|`, with
`0 ≤ δ`, `0 ≤ log k ≤ Λ` on the support, `δΛ ≤ 1`, and the Taylor tail
`(2/J!)·Σ |c_k| k^{-σ₀}` is at most `V/2`, then some companion polynomial `P_i`, `i < J`, has
`V/6 ≤ |P_i(σ₀ + iγ)|`. -/
theorem exists_abscissaTaylorPoly_large {S : Finset ℕ} (hS : ∀ k ∈ S, 1 ≤ k) (c : ℕ → ℂ)
    {σ₀ δ Λ γ V : ℝ} {J : ℕ} (hδ : 0 ≤ δ) (hΛ0 : 0 < Λ) (hΛ : ∀ k ∈ S, Real.log k ≤ Λ)
    (hδΛ : δ * Λ ≤ 1) (hJ : 1 ≤ J)
    (hV : V ≤ ‖abscissaDirichletValue S c (σ₀ + δ) γ‖)
    (htail : 2 / (J.factorial : ℝ) * ∑ k ∈ S, ‖c k‖ * (k : ℝ) ^ (-σ₀) ≤ V / 2) :
    ∃ i < J, V / 6 ≤ ‖abscissaTaylorPoly S c Λ i σ₀ γ‖ := by
  by_contra hcon
  push Not at hcon
  -- the Taylor decomposition, term by term
  set x : ℕ → ℝ := fun k => δ * Real.log k with hx
  have hx0 : ∀ k ∈ S, 0 ≤ x k := fun k hk =>
    mul_nonneg hδ (Real.log_nonneg (by exact_mod_cast hS k hk))
  have hx1 : ∀ k ∈ S, x k ≤ 1 := by
    intro k hk
    calc x k = δ * Real.log k := rfl
      _ ≤ δ * Λ := mul_le_mul_of_nonneg_left (hΛ k hk) hδ
      _ ≤ 1 := hδΛ
  set r : ℕ → ℝ := fun k =>
    Real.exp (-(x k)) - ∑ m ∈ range J, (-(x k)) ^ m / (m.factorial : ℝ) with hr
  have hrbound : ∀ k ∈ S, |r k| ≤ 2 / (J.factorial : ℝ) := by
    intro k hk
    have habs : |(-(x k))| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (hx0 k hk)]
      exact hx1 k hk
    have hb := Real.exp_bound habs (by omega : 0 < J)
    have hpow : |(-(x k))| ^ J ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
    have hIpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
    have hfac : (0 : ℝ) < (J.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos J
    have hfrac : ((J.succ : ℕ) : ℝ) / ((J.factorial : ℝ) * J) ≤ 2 / (J.factorial : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hfac]
      have : ((J.succ : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
      rw [this]
      have hI1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      nlinarith
    calc |r k| ≤ |(-(x k))| ^ J * (((J.succ : ℕ) : ℝ) / ((J.factorial : ℝ) * J)) := hb
      _ ≤ 1 * (2 / (J.factorial : ℝ)) :=
          mul_le_mul hpow hfrac (by positivity) zero_le_one
      _ = 2 / (J.factorial : ℝ) := one_mul _
  have hexp_split : ∀ k ∈ S, Real.exp (-(x k))
      = ∑ m ∈ range J, ((-(δ * Λ)) ^ m / (m.factorial : ℝ)) * (Real.log k / Λ) ^ m + r k := by
    intro k _
    have hsum : ∑ m ∈ range J, (-(x k)) ^ m / (m.factorial : ℝ)
        = ∑ m ∈ range J, ((-(δ * Λ)) ^ m / (m.factorial : ℝ)) * (Real.log k / Λ) ^ m := by
      refine sum_congr rfl fun m _ => ?_
      have hxk : -(x k) = (-(δ * Λ)) * (Real.log k / Λ) := by
        simp only [hx]
        field_simp
      rw [hxk, mul_pow]
      ring
    rw [← hsum]
    simp only [hr]
    ring
  -- the decomposition of `F`
  have hF : abscissaDirichletValue S c (σ₀ + δ) γ
      = ∑ m ∈ range J, (((-(δ * Λ)) ^ m / (m.factorial : ℝ) : ℝ) : ℂ)
          * abscissaTaylorPoly S c Λ m σ₀ γ
        + ∑ k ∈ S, c k * (k : ℂ) ^ (-((σ₀ : ℂ) + (γ : ℂ) * Complex.I)) * ((r k : ℝ) : ℂ) := by
    unfold abscissaDirichletValue abscissaTaylorPoly
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [natCast_cpow_shift_real (hS k hk), hexp_split k hk]
    push_cast
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact sum_congr rfl fun m _ => by ring
    · ring
  -- bounding each piece
  have hfac_sum : ∑ m ∈ range J, (1 / (m.factorial : ℝ)) < 3 := by
    have h := Real.sum_le_exp_of_nonneg (x := 1) zero_le_one J
    simp only [one_pow] at h
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hmain : ‖∑ m ∈ range J, (((-(δ * Λ)) ^ m / (m.factorial : ℝ) : ℝ) : ℂ)
        * abscissaTaylorPoly S c Λ m σ₀ γ‖ < V / 2 ∨ V ≤ 0 := by
    by_cases hV0 : V ≤ 0
    · exact Or.inr hV0
    left
    push Not at hV0
    calc ‖∑ m ∈ range J, (((-(δ * Λ)) ^ m / (m.factorial : ℝ) : ℝ) : ℂ)
          * abscissaTaylorPoly S c Λ m σ₀ γ‖
        ≤ ∑ m ∈ range J, (1 / (m.factorial : ℝ)) * (V / 6) := by
          refine le_trans (norm_sum_le _ _) (sum_le_sum fun m hm => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg,
            abs_of_nonneg (mul_nonneg hδ hΛ0.le),
            abs_of_pos (by exact_mod_cast Nat.factorial_pos m : (0 : ℝ) < m.factorial)]
          have hp : (δ * Λ) ^ m ≤ 1 := pow_le_one₀ (mul_nonneg hδ hΛ0.le) hδΛ
          have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
          have hq : (δ * Λ) ^ m / (m.factorial : ℝ) ≤ 1 / (m.factorial : ℝ) :=
            div_le_div_of_nonneg_right hp hfac.le
          exact mul_le_mul hq (hcon m (mem_range.mp hm)).le (norm_nonneg _) (by positivity)
      _ = (∑ m ∈ range J, (1 / (m.factorial : ℝ))) * (V / 6) := by rw [Finset.sum_mul]
      _ < 3 * (V / 6) := mul_lt_mul_of_pos_right hfac_sum (by linarith)
      _ = V / 2 := by ring
  have htailN : ‖∑ k ∈ S, c k * (k : ℂ) ^ (-((σ₀ : ℂ) + (γ : ℂ) * Complex.I)) * ((r k : ℝ) : ℂ)‖
      ≤ V / 2 := by
    refine le_trans (norm_sum_le _ _) (le_trans ?_ htail)
    rw [Finset.mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by have := hS k hk; omega : 0 < k)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (by have := hS k hk; omega : 0 < k))]
    have hre : (-((σ₀ : ℂ) + (γ : ℂ) * Complex.I)).re = -σ₀ := by simp
    rw [hre]
    have hpow0 : 0 ≤ (k : ℝ) ^ (-σ₀) := Real.rpow_nonneg hk0.le _
    calc ‖c k‖ * (k : ℝ) ^ (-σ₀) * |r k|
        ≤ ‖c k‖ * (k : ℝ) ^ (-σ₀) * (2 / (J.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (hrbound k hk) (by positivity)
      _ = 2 / (J.factorial : ℝ) * (‖c k‖ * (k : ℝ) ^ (-σ₀)) := by ring
  rcases hmain with hmain | hV0
  · have hlt : ‖abscissaDirichletValue S c (σ₀ + δ) γ‖ < V := by
      rw [hF]
      calc _ ≤ _ := norm_add_le _ _
        _ < V / 2 + V / 2 := add_lt_add_of_lt_of_le hmain htailN
        _ = V := by ring
    linarith
  · have h0 := hcon 0 (by omega)
    have : 0 ≤ ‖abscissaTaylorPoly S c Λ 0 σ₀ γ‖ := norm_nonneg _
    linarith

end

end RHTower.Sieve
