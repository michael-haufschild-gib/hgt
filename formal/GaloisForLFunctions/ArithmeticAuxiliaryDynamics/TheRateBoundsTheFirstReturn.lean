import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMellinTransformOfAStencil

/-!
# The rate bounds the first return

A producer inverts `ζ` on the line `Re s = 1` up to `‖s‖ T`. At a height `τ` where every letter of the
alphabet nearly returns, `k^{-iτ} ≈ 1`, balance forces `D_c(1 + iτ) ≈ D_c(1) = 0`. Both cannot hold
while `ε ‖s‖ ≤ ½` unless `ζ(1 + iτ)` is large. This is an effective Kronecker statement at
arithmetic scale: **the letters of a producer of rate `ε` have no simultaneous return of precision
`θ` before height `1/(2ε)`, unless `|ζ(1 + iτ)| ≳ 1/θ`.**

The size of the harmonic coefficient mass `L₁ = Σ |c(k)|/k` is polylogarithmic in `K`:
`L₁ ≤ 2 (1 + log K)(m (1 + log K) + (K + 1) T)`.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The harmonic coefficient mass `L₁ = Σ |c(k)|/k`. -/
def harmonicMass (c : ℕ →₀ ℤ) : ℝ := ∑ k ∈ c.support, |(c k : ℝ)| / k

/-- Summing over multiples of `k` in `[1, x]`. -/
private lemma sum_Icc_dvd (f : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (x : ℕ) :
    ∑ n ∈ Icc 1 x, (if k ∣ n then f n else 0) = ∑ j ∈ Icc 1 (x / k), f (k * j) := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.succ_div]
    split_ifs with hd
    · obtain ⟨q, hq⟩ := hd
      have hq' : x / k + 1 = q := by
        have h1 : (x + 1) / k = q := by rw [hq]; exact Nat.mul_div_cancel_left q hk
        rw [Nat.succ_div, if_pos ⟨q, hq⟩] at h1
        exact h1
      rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 _), hq', hq]
    · simp

/-- The harmonic sum over multiples of `d` is at most `(1 + log K)/d`. -/
private lemma sum_multiples_inv_le {d K : ℕ} (hd : 0 < d) :
    ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / k else 0) ≤ (1 + Real.log K) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sum_Icc_dvd (fun k => (1 : ℝ) / k) hd]
  have hterm : ∀ j ∈ Icc 1 (K / d), (1 : ℝ) / ((d * j : ℕ) : ℝ) = (1 / (j : ℝ)) / d := by
    intro j _
    push_cast
    ring
  rw [sum_congr rfl hterm, ← sum_div]
  refine div_le_div_of_nonneg_right ?_ hdR.le
  have hH := harmonic_le_one_add_log (K / d)
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  have hsum : ∑ j ∈ Icc 1 (K / d), (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log ((K / d : ℕ) : ℝ) := by
    refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) hH
    rw [one_div]
  refine hsum.trans ?_
  rcases Nat.eq_zero_or_pos (K / d) with h0 | hpos
  · rw [h0]
    have : 0 ≤ Real.log (K : ℝ) := Real.log_natCast_nonneg K
    simp
    linarith
  · have h1 : ((K / d : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.div_le_self K d
    have h2 : (0 : ℝ) < ((K / d : ℕ) : ℝ) := by exact_mod_cast hpos
    linarith [Real.log_le_log h2 h1]

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- The harmonic mass shifted by one index. -/
private lemma sum_pred_le (hP : IsProducer c m B) (K : ℕ) :
    ∑ d ∈ Icc 1 K, (stepWeight c (d - 1) : ℝ) / d ≤ ∑ r ∈ Icc 1 K, (stepWeight c r : ℝ) / r := by
  have hshift : ∀ K : ℕ, ∑ d ∈ Icc 1 (K + 1), (stepWeight c (d - 1) : ℝ) / d ≤
      ∑ r ∈ Icc 1 K, (stepWeight c r : ℝ) / r := by
    intro K
    induction K with
    | zero => simp [stepWeight_zero]
    | succ K ih =>
      have hL := Finset.sum_Icc_succ_top (a := 1) (b := K + 1) (by omega)
        (fun d => (stepWeight c (d - 1) : ℝ) / d)
      have hR := Finset.sum_Icc_succ_top (a := 1) (b := K) (by omega)
        (fun r => (stepWeight c r : ℝ) / r)
      rw [hL, hR]
      have hg : (0 : ℝ) ≤ stepWeight c (K + 1) := by exact_mod_cast hP.nonneg (K + 1)
      have hdiv : (stepWeight c (K + 1 + 1 - 1) : ℝ) / ((K + 1 + 1 : ℕ) : ℝ) ≤
          (stepWeight c (K + 1) : ℝ) / ((K + 1 : ℕ) : ℝ) := by
        rw [Nat.add_sub_cancel]
        refine div_le_div_of_nonneg_left hg (by positivity) ?_
        push_cast
        linarith
      linarith
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    refine (hshift n).trans ?_
    rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
    have hg : (0 : ℝ) ≤ (stepWeight c (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
      div_nonneg (by exact_mod_cast hP.nonneg (n + 1)) (by positivity)
    linarith

/-- **The harmonic coefficient mass law.** `L₁ ≤ 2 (1 + log K)(m (1 + log K) + (K + 1) T)`. -/
theorem harmonicMass_le (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) :
    harmonicMass c ≤
      2 * (1 + Real.log K) * ((m : ℝ) * (1 + Real.log K) + ((K : ℝ) + 1) * excess c m B) := by
  classical
  have hsub := hP.support_subset_Icc hK
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_natCast_nonneg K
  have hL : 0 ≤ 1 + Real.log (K : ℝ) := by linarith
  have hstep1 : harmonicMass c ≤
      ∑ k ∈ Icc 1 K, ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ)) := by
    calc harmonicMass c ≤ ∑ k ∈ c.support, ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ)) := by
          refine sum_le_sum fun k hk => ?_
          have hk1 := (mem_Icc.mp (hsub hk)).1
          rw [← sum_mul, div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right (abs_coeff_le_sum_increment c hk1) (by positivity)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
          sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (by positivity)
  have hswap : ∑ k ∈ Icc 1 K, ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ)) =
      ∑ d ∈ Icc 1 K, |(increment c d : ℝ)| * ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / k else 0) := by
    have hdiv : ∀ k ∈ Icc 1 K, ∑ d ∈ k.divisors, |(increment c d : ℝ)| * (1 / (k : ℝ)) =
        ∑ d ∈ Icc 1 K, if d ∣ k then |(increment c d : ℝ)| * (1 / (k : ℝ)) else 0 := by
      intro k hk
      obtain ⟨hk1, hkK⟩ := mem_Icc.mp hk
      rw [← sum_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hk1, (Nat.le_of_dvd hk1 hd).trans hkK⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, by omega⟩
    rw [sum_congr rfl hdiv, sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hterm : ∀ d ∈ Icc 1 K, |(increment c d : ℝ)| *
      ∑ k ∈ Icc 1 K, (if d ∣ k then (1 : ℝ) / k else 0) ≤
      (1 + Real.log K) * ((stepWeight c d : ℝ) / d + (stepWeight c (d - 1) : ℝ) / d) := by
    intro d hd
    obtain ⟨hd1, _⟩ := mem_Icc.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hsucc : (stepWeight c (e + 1) : ℝ) = stepWeight c e + increment c (e + 1) := by
      exact_mod_cast stepWeight_succ c e
    have h0 : (0 : ℝ) ≤ stepWeight c (e + 1) := by exact_mod_cast hP.nonneg (e + 1)
    have h1 : (0 : ℝ) ≤ stepWeight c e := by exact_mod_cast hP.nonneg e
    have habs : |(increment c (e + 1) : ℝ)| ≤ stepWeight c (e + 1) + stepWeight c e := by
      rw [abs_le]
      constructor <;> linarith
    rw [Nat.add_sub_cancel]
    calc |(increment c (e + 1) : ℝ)| * ∑ k ∈ Icc 1 K, (if e + 1 ∣ k then (1 : ℝ) / k else 0)
        ≤ ((stepWeight c (e + 1) : ℝ) + stepWeight c e) * ((1 + Real.log K) / ((e + 1 : ℕ) : ℝ)) :=
          mul_le_mul habs (sum_multiples_inv_le hd1) (sum_nonneg fun k _ => by
            split_ifs <;> positivity) (by linarith)
      _ = _ := by
          field_simp
  rw [hswap] at hstep1
  have hsum := sum_le_sum hterm
  rw [← mul_sum, sum_add_distrib] at hsum
  have h1 := hP.sum_stepWeight_div_le K
  have h2 := hP.sum_pred_le K
  have hfinal := mul_le_mul_of_nonneg_left (add_le_add h1 (h2.trans h1)) hL
  calc harmonicMass c ≤ _ := hstep1
    _ ≤ _ := hsum
    _ ≤ _ := hfinal
    _ = _ := by ring

/-- On `Re s = 1`, balance turns `D_c(s)` into a sum of phase defects. -/
theorem norm_dirichletPoly_le (hP : IsProducer c m B) {τ θ : ℝ}
    (hθ : ∀ k ∈ c.support, ‖((k : ℝ) : ℂ) ^ (-((τ : ℂ) * Complex.I)) - 1‖ ≤ θ) :
    ‖dirichletPoly c (1 + (τ : ℂ) * Complex.I)‖ ≤ θ * harmonicMass c := by
  have hb : ∑ k ∈ c.support, (((c k : ℝ) / k : ℝ) : ℂ) = 0 := by
    have : ((∑ k ∈ c.support, (c k : ℝ) / k : ℝ) : ℂ) = 0 := by
      rw [show ∑ k ∈ c.support, (c k : ℝ) / k = 0 from hP.balanced]; simp
    simpa using this
  have hrew : dirichletPoly c (1 + (τ : ℂ) * Complex.I) = ∑ k ∈ c.support,
      (((c k : ℝ) / k : ℝ) : ℂ) * (((k : ℝ) : ℂ) ^ (-((τ : ℂ) * Complex.I)) - 1) := by
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib, hb, sub_zero, dirichletPoly]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h; exact Finsupp.mem_support_iff.mp hk hP.zero
    have hkC : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
    rw [neg_add, Complex.cpow_add _ _ hkC, Complex.cpow_neg_one]
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [hrew, harmonicMass, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hP.zero
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hkR, mul_comm]
  exact mul_le_mul_of_nonneg_right (hθ k hk) (by positivity)

/-- **No early return.** If `ε ‖s‖ ≤ ½` at `s = 1 + iτ`, `τ ≠ 0`, and every letter has phase defect at
most `θ`, then `m (1 − 1/B) / 2 ≤ θ L₁ ‖ζ(s)‖`. -/
theorem le_of_phase_return (hP : IsProducer c m B) {τ θ : ℝ} (hτ : τ ≠ 0)
    (hθ : ∀ k ∈ c.support, ‖((k : ℝ) : ℂ) ^ (-((τ : ℂ) * Complex.I)) - 1‖ ≤ θ)
    (hε : rate c m B * ‖(1 : ℂ) + (τ : ℂ) * Complex.I‖ ≤ 1 / 2) :
    (m : ℝ) * (1 - 1 / (B : ℝ)) / 2 ≤
      θ * harmonicMass c * ‖riemannZeta (1 + (τ : ℂ) * Complex.I)‖ := by
  have hσ : ((1 : ℂ) + (τ : ℂ) * Complex.I).re = 1 := by simp
  have hs1 : (1 : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hτ him
  have hlow := hP.le_norm_dirichletPoly_mul_zeta hσ hs1
  have hnorm := hP.norm_dirichletPoly_le hθ
  have hprod : 0 < (m : ℝ) * (1 - 1 / (B : ℝ)) := mul_pos hP.m_pos hP.one_sub_pos
  have hstep : (m : ℝ) * (1 - 1 / (B : ℝ)) / 2 ≤
      (m : ℝ) * (1 - 1 / (B : ℝ)) * (1 - rate c m B * ‖(1 : ℂ) + (τ : ℂ) * Complex.I‖) := by
    nlinarith
  refine hstep.trans (hlow.trans ?_)
  exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

end IsProducer

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
