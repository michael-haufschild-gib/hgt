import GaloisForLFunctions.HTGeometry.RationalVanishingOrderBound

/-!
# The shift ratio of a Gamma monomial in a dominant class

`ρ_g(s) = ∏_k (s+λ_k)^{g_k}` with `∑_k g_k = 0` is `∏_k (1 + λ_k/s)^{g_k}`, a rational function of
`u = 1/s` equal to `1 + (∑_k g_k λ_k) u + O(u²)`.  Inside a dominant class the first moment also
vanishes, so `ρ_g(s) = 1 + O(‖s‖^{-2})`.

That is the step bound of the ladder for a Gamma-monomial ratio: `R(s+1) - R(s) = (ρ_g(s) - 1)R(s)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

theorem coeff_one_mul (f g : Polynomial ℂ) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff01_shift_pow (lam : ℂ) (n : ℕ) :
    ((1 + Polynomial.C lam * Polynomial.X) ^ n).coeff 0 = 1
    ∧ ((1 + Polynomial.C lam * Polynomial.X) ^ n).coeff 1 = (n : ℂ) * lam := by
  induction n with
  | zero => simp [Polynomial.coeff_one]
  | succ n ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have hbase0 : ((1 : Polynomial ℂ) + Polynomial.C lam * Polynomial.X).coeff 0 = 1 := by
        simp
      have hbase1 : ((1 : Polynomial ℂ) + Polynomial.C lam * Polynomial.X).coeff 1 = lam := by
        simp [Polynomial.coeff_one]
      constructor
      · rw [pow_succ, Polynomial.mul_coeff_zero, ih0, hbase0, mul_one]
      · rw [pow_succ, coeff_one_mul, ih0, ih1, hbase0, hbase1]
        push_cast
        ring

theorem coeff01_prod_shift {r : ℕ} (lam : Fin r → ℂ) (n : Fin r → ℕ) (T : Finset (Fin r)) :
    (∏ k ∈ T, (1 + Polynomial.C (lam k) * Polynomial.X) ^ (n k)).coeff 0 = 1
    ∧ (∏ k ∈ T, (1 + Polynomial.C (lam k) * Polynomial.X) ^ (n k)).coeff 1
        = ∑ k ∈ T, (n k : ℂ) * lam k := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | insert a T ha ih =>
      obtain ⟨ih0, ih1⟩ := ih
      obtain ⟨h0, h1⟩ := coeff01_shift_pow (lam a) (n a)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      constructor
      · rw [Polynomial.mul_coeff_zero, h0, ih0, mul_one]
      · rw [coeff_one_mul, h0, h1, ih0, ih1]
        ring


theorem prod_zpow_const {r : ℕ} (s : ℂ) (hs : s ≠ 0) (g : Fin r → ℤ) :
    (∏ k, s ^ (g k)) = s ^ (∑ k, g k) := by
  classical
  induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hs]

theorem zpow_eq_toNat_div (x : ℂ) (_hx : x ≠ 0) (n : ℤ) :
    x ^ n = x ^ (n.toNat) / x ^ ((-n).toNat) := by
  by_cases h : 0 ≤ n
  · rw [show (-n).toNat = 0 by omega, pow_zero, div_one, ← zpow_natCast x n.toNat,
      Int.toNat_of_nonneg h]
  · rw [show n.toNat = 0 by omega, pow_zero, ← zpow_natCast x (-n).toNat,
      Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n), zpow_neg, one_div, inv_inv]

/-- The numerator of the shift ratio in the variable `u = 1/s`. -/
def shiftNumer {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) : Polynomial ℂ :=
  ∏ k, (1 + Polynomial.C (lam k) * Polynomial.X) ^ ((g k).toNat)

/-- The denominator of the shift ratio in the variable `u = 1/s`. -/
def shiftDenom {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) : Polynomial ℂ :=
  ∏ k, (1 + Polynomial.C (lam k) * Polynomial.X) ^ ((-(g k)).toNat)

theorem eval_shiftNumer {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (u : ℂ) :
    Polynomial.eval u (shiftNumer lam g) = ∏ k, (1 + lam k * u) ^ ((g k).toNat) := by
  rw [shiftNumer, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun k _ => by simp

theorem eval_shiftDenom {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (u : ℂ) :
    Polynomial.eval u (shiftDenom lam g) = ∏ k, (1 + lam k * u) ^ ((-(g k)).toNat) := by
  rw [shiftDenom, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun k _ => by simp

/-- **The numerator and denominator agree to first order.** -/
theorem X_sq_dvd_shiftNumer_sub_shiftDenom {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ((Polynomial.X : Polynomial ℂ) ^ 2) ∣ (shiftNumer lam g - shiftDenom lam g) := by
  obtain ⟨h0n, h1n⟩ := coeff01_prod_shift lam (fun k => (g k).toNat) Finset.univ
  obtain ⟨h0d, h1d⟩ := coeff01_prod_shift lam (fun k => (-(g k)).toNat) Finset.univ
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  interval_cases d
  · rw [Polynomial.coeff_sub, shiftNumer, shiftDenom, h0n, h0d, sub_self]
  · rw [Polynomial.coeff_sub, shiftNumer, shiftDenom, h1n, h1d, ← Finset.sum_sub_distrib]
    rw [← hmom]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsplit : (((g k).toNat : ℂ)) - (((-(g k)).toNat : ℂ)) = (g k : ℂ) := by
      have : ((g k).toNat : ℤ) - ((-(g k)).toNat : ℤ) = g k := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this
    rw [← hsplit]
    ring


theorem eval_zero_shiftDenom {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) :
    Polynomial.eval 0 (shiftDenom lam g) = 1 := by
  rw [eval_shiftDenom]
  simp

/-- **The shift ratio in a dominant class is `1 + O(‖s‖^{-2})`.** -/
theorem exists_norm_shiftRatio_sub_one_le {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ K Rb : ℝ, 0 ≤ K ∧ 0 < Rb ∧ ∀ s : ℂ, Rb ≤ ‖s‖ → (∀ k, s + lam k ≠ 0) →
      ‖(∏ k, (s + lam k) ^ (g k)) - 1‖ ≤ K / ‖s‖ ^ 2 := by
  have hden0 : Polynomial.eval 0 (shiftDenom lam g) ≠ 0 := by
    rw [eval_zero_shiftDenom]
    exact one_ne_zero
  obtain ⟨C, ρ, hC0, hρ0, hCb⟩ :=
    exists_norm_polyEval_div_le_of_dvd (X_sq_dvd_shiftNumer_sub_shiftDenom lam g hmom) hden0
  refine ⟨C, max (1 / ρ) 1, hC0, lt_of_lt_of_le one_pos (le_max_right _ _), fun s hs hlam => ?_⟩
  have hs1 : (1 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) hs
  have hsρ : 1 / ρ ≤ ‖s‖ := le_trans (le_max_left _ _) hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs1
    linarith
  set u : ℂ := 1 / s with hu
  have hunorm : ‖u‖ = 1 / ‖s‖ := by rw [hu, norm_div, norm_one]
  have huρ : ‖u‖ ≤ ρ := by
    rw [hunorm]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖s‖)]
    rw [div_le_iff₀ hρ0] at hsρ
    linarith
  have hfac : ∀ k, (1 : ℂ) + lam k * u = (s + lam k) / s := by
    intro k
    rw [hu]
    field_simp
  have hfacne : ∀ k, (1 : ℂ) + lam k * u ≠ 0 := by
    intro k
    rw [hfac k]
    exact div_ne_zero (hlam k) hs0
  have hdenne : Polynomial.eval u (shiftDenom lam g) ≠ 0 := by
    rw [eval_shiftDenom]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hfacne k)
  have hprod : (∏ k, (s + lam k) ^ (g k))
      = Polynomial.eval u (shiftNumer lam g) / Polynomial.eval u (shiftDenom lam g) := by
    have hstep : ∀ k : Fin r, (s + lam k) ^ (g k) = s ^ (g k) * ((1 : ℂ) + lam k * u) ^ (g k) := by
      intro k
      rw [← mul_zpow]
      congr 1
      rw [hfac k]
      field_simp
    rw [Finset.prod_congr rfl fun k _ => hstep k, Finset.prod_mul_distrib,
      prod_zpow_const s hs0 g, hdeg, zpow_zero, one_mul]
    rw [eval_shiftNumer, eval_shiftDenom, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_eq_toNat_div _ (hfacne k) (g k)
  have hsub : (∏ k, (s + lam k) ^ (g k)) - 1
      = Polynomial.eval u (shiftNumer lam g - shiftDenom lam g)
        / Polynomial.eval u (shiftDenom lam g) := by
    rw [hprod, Polynomial.eval_sub]
    field_simp
  rw [hsub]
  have hbound := hCb u huρ
  have hpow : ‖u‖ ^ 2 = 1 / ‖s‖ ^ 2 := by rw [hunorm, div_pow, one_pow]
  rw [hpow] at hbound
  calc ‖Polynomial.eval u (shiftNumer lam g - shiftDenom lam g)
        / Polynomial.eval u (shiftDenom lam g)‖
      ≤ C * (1 / ‖s‖ ^ 2) := hbound
    _ = C / ‖s‖ ^ 2 := by ring

end

end GaloisForLFunctions.HTGeometry
