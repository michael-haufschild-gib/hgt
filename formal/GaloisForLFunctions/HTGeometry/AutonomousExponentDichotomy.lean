import GaloisForLFunctions.HTGeometry.VanishingPowerSum
import GaloisForLFunctions.HTGeometry.PolynomialMagnitudeBalance

/-!
# The exponent dichotomy of an autonomous algebraic relation

At a point where `‖F z‖` is large, the relation `∑_{k ≤ m} C_k(F)(F′)^k = 0` forces the maximal term
to be attained twice, so `‖F′ z‖^{v-u} ≍ ‖C_u(F z)‖/‖C_v(F z)‖ ≍ ‖F z‖^{d_u - d_v}` for a pair of
indices `u < v`.  The exponent `(d_u - d_v)/(v - u)` is a ratio of integers with denominator at most
`m`, so it cannot lie strictly between `1` and `1 + 1/m`.  That integrality gives a **gap**:

```text
‖F′ z‖ ≤ K‖F z‖      or      c‖F z‖^{m+1} ≤ ‖F′ z‖^m,
```

with `K`, `c` depending only on the coefficient polynomials.  The second alternative is `‖F′‖`
exceeding `‖F‖^{1+1/m}`, which no branch can do marginally.

Both alternatives are stated with natural-number powers, so no real exponentiation enters.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1000000 in
/-- **The exponent dichotomy.**  Wherever `‖F z‖` is large, either `‖F′ z‖` is at most a constant
multiple of `‖F z‖`, or it exceeds `‖F z‖^{1+1/m}` by a fixed constant.  The intermediate range is
empty because the Newton exponent of the relation is a fraction with denominator at most `m`. -/
theorem exists_dichotomy_of_relation {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ}
    (hCm : C m ≠ 0) {Y W : ℂ → ℂ}
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (Y z) * (W z) ^ k = 0) :
    ∃ K c R₀ : ℝ, 1 ≤ K ∧ 0 < c ∧ c ≤ 1 ∧ 1 ≤ R₀ ∧ ∀ z : ℂ, R₀ ≤ ‖Y z‖ →
      ‖W z‖ ≤ K * ‖Y z‖ ∨ c * ‖Y z‖ ^ (m + 1) ≤ ‖W z‖ ^ m := by
  classical
  set Li : ℕ → ℝ := fun i => if C i = 0 then 1 else ‖(C i).leadingCoeff‖ / 2 with hLi
  set Ai : ℕ → ℝ := fun i => ∑ j ∈ Finset.range ((C i).natDegree + 1), ‖(C i).coeff j‖ with hAi
  have hLipos : ∀ i, 0 < Li i := by
    intro i
    rw [hLi]
    by_cases h : C i = 0
    · simp [h]
    · simp only [h, if_false]
      have : 0 < ‖(C i).leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr h)
      linarith
  have hR : ∀ i : ℕ, ∃ R : ℝ, 1 ≤ R ∧ ∀ y : ℂ, R ≤ ‖y‖ → C i ≠ 0 →
      Li i * ‖y‖ ^ (C i).natDegree ≤ ‖(C i).eval y‖ := by
    intro i
    by_cases h : C i = 0
    · exact ⟨1, le_rfl, fun y _ hne => absurd h hne⟩
    · obtain ⟨R, hR1, hRle⟩ := exists_le_norm_eval (C i) h
      refine ⟨R, hR1, fun y hy _ => ?_⟩
      have := hRle y hy
      rw [hLi]
      simpa [h] using this
  choose Rf hRf1 hRf2 using hR
  have hne : (Finset.range (m + 1)).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  set Anum : ℝ := (Finset.range (m + 1)).sup' hne (fun i => max 1 (Ai i)) with hAnum
  set Lnum : ℝ := (Finset.range (m + 1)).inf' hne (fun i => min 1 (Li i)) with hLnum
  set R₀ : ℝ := (Finset.range (m + 1)).sup' hne (fun i => max 1 (Rf i)) with hR₀
  have hAnum1 : 1 ≤ Anum := by
    rw [hAnum]
    exact le_trans (le_max_left 1 (Ai 0))
      (Finset.le_sup' (fun i => max 1 (Ai i)) (Finset.mem_range.mpr (by omega)))
  have hLnum1 : Lnum ≤ 1 := by
    rw [hLnum]
    exact le_trans (Finset.inf'_le (fun i => min 1 (Li i)) (Finset.mem_range.mpr (by omega)))
      (min_le_left 1 (Li 0))
  have hLnum0 : 0 < Lnum := by
    rw [hLnum, Finset.lt_inf'_iff]
    intro i _
    exact lt_min zero_lt_one (hLipos i)
  have hR₀1 : 1 ≤ R₀ := by
    rw [hR₀]
    exact le_trans (le_max_left 1 (Rf 0))
      (Finset.le_sup' (fun i => max 1 (Rf i)) (Finset.mem_range.mpr (by omega)))
  have hAle : ∀ i ≤ m, Ai i ≤ Anum := by
    intro i hi
    rw [hAnum]
    exact le_trans (le_max_right 1 (Ai i))
      (Finset.le_sup' (fun j => max 1 (Ai j)) (Finset.mem_range.mpr (by omega)))
  have hLle : ∀ i ≤ m, Lnum ≤ Li i := by
    intro i hi
    rw [hLnum]
    exact le_trans (Finset.inf'_le (fun j => min 1 (Li j)) (Finset.mem_range.mpr (by omega)))
      (min_le_right 1 (Li i))
  have hRle : ∀ i ≤ m, Rf i ≤ R₀ := by
    intro i hi
    rw [hR₀]
    exact le_trans (le_max_right 1 (Rf i))
      (Finset.le_sup' (fun j => max 1 (Rf j)) (Finset.mem_range.mpr (by omega)))
  set K : ℝ := ((m : ℝ) + 1) * Anum / Lnum with hK
  set c₀ : ℝ := Lnum / (((m : ℝ) + 1) * Anum) with hc₀
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hK1 : 1 ≤ K := by
    rw [hK, le_div_iff₀ hLnum0]
    nlinarith [hAnum1, hLnum1, hLnum0, hm1]
  have hc₀0 : 0 < c₀ := by
    rw [hc₀]
    positivity
  have hc₀1 : c₀ ≤ 1 := by
    rw [hc₀, div_le_one (by positivity)]
    nlinarith [hAnum1, hLnum1, hm1]
  refine ⟨K, c₀ ^ m, R₀, hK1, by positivity, pow_le_one₀ hc₀0.le hc₀1, hR₀1, ?_⟩
  intro z hz
  set y : ℂ := Y z with hy
  set w : ℂ := W z with hw
  have hy1 : (1 : ℝ) ≤ ‖y‖ := le_trans hR₀1 hz
  have hy0 : (0 : ℝ) < ‖y‖ := by linarith
  -- coefficient bounds at `y`
  have hupper : ∀ i ≤ m, ‖(C i).eval y‖ ≤ Anum * ‖y‖ ^ (C i).natDegree := by
    intro i hi
    refine le_trans (norm_eval_le_mul_pow (C i) hy1) ?_
    exact mul_le_mul_of_nonneg_right (hAle i hi) (by positivity)
  have hlower : ∀ i ≤ m, C i ≠ 0 → Lnum * ‖y‖ ^ (C i).natDegree ≤ ‖(C i).eval y‖ := by
    intro i hi hCi
    refine le_trans ?_ (hRf2 i y (le_trans (hRle i hi) hz) hCi)
    exact mul_le_mul_of_nonneg_right (hLle i hi) (by positivity)
  have hCmy : (C m).eval y ≠ 0 := by
    intro h0
    have := hlower m le_rfl hCm
    rw [h0, norm_zero] at this
    nlinarith [this, hLnum0, pow_pos hy0 (C m).natDegree]
  rcases eq_or_ne w 0 with hw0 | hwne
  · refine Or.inl ?_
    rw [hw0, norm_zero]
    nlinarith [hK1, hy1]
  obtain ⟨u, v, huv, hvm, hAu, hAv, hlow, hhigh⟩ :=
    exists_pow_between_of_vanishing_sum (m := m) (α := fun k => (C k).eval y) hwne
      (by simpa [hy, hw] using hrel z) ⟨m, le_rfl, hCmy⟩
  set p : ℕ := v - u with hp
  have hp1 : 1 ≤ p := by omega
  have hpm : p ≤ m := by omega
  have hum : u ≤ m := by omega
  have hCvne : C v ≠ 0 := by
    intro h0
    rw [h0] at hAv
    simp at hAv
  have hAvpos : (0 : ℝ) < ‖(C v).eval y‖ := norm_pos_iff.mpr hAv
  have hup : ‖(C u).eval y‖ ≤ Anum * ‖y‖ ^ (C u).natDegree := hupper u hum
  have hlo : Lnum * ‖y‖ ^ (C v).natDegree ≤ ‖(C v).eval y‖ := hlower v hvm hCvne
  have hydvpos : (0 : ℝ) < ‖y‖ ^ (C v).natDegree := pow_pos hy0 _
  by_cases hcase : (C u).natDegree ≤ (C v).natDegree + p
  · -- the tame branch
    refine Or.inl ?_
    have hstep : ‖w‖ ^ p * ‖(C v).eval y‖ ≤ ((m : ℝ) + 1) * ‖(C u).eval y‖ := by
      have := hhigh
      have h2 : ‖w‖ ^ p * ‖(C v).eval y‖
          ≤ (((m : ℝ) + 1) * (‖(C u).eval y‖ / ‖(C v).eval y‖)) * ‖(C v).eval y‖ :=
        mul_le_mul_of_nonneg_right this hAvpos.le
      rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hAvpos)] at h2
      exact h2
    have hpowmono : ‖y‖ ^ (C u).natDegree ≤ ‖y‖ ^ (C v).natDegree * ‖y‖ ^ p := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hy1 hcase
    have hkey : ‖w‖ ^ p * (Lnum * ‖y‖ ^ (C v).natDegree)
        ≤ ((m : ℝ) + 1) * (Anum * (‖y‖ ^ (C v).natDegree * ‖y‖ ^ p)) := by
      have h1 : ‖w‖ ^ p * (Lnum * ‖y‖ ^ (C v).natDegree) ≤ ‖w‖ ^ p * ‖(C v).eval y‖ :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      have h2 : ((m : ℝ) + 1) * ‖(C u).eval y‖
          ≤ ((m : ℝ) + 1) * (Anum * ‖y‖ ^ (C u).natDegree) :=
        mul_le_mul_of_nonneg_left hup hm1.le
      have h3 : ((m : ℝ) + 1) * (Anum * ‖y‖ ^ (C u).natDegree)
          ≤ ((m : ℝ) + 1) * (Anum * (‖y‖ ^ (C v).natDegree * ‖y‖ ^ p)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowmono ?_) hm1.le
        linarith [hAnum1]
      linarith [h1, h2, h3, hstep]
    have hdiv : ‖w‖ ^ p ≤ K * ‖y‖ ^ p := by
      rw [hK]
      rw [div_mul_eq_mul_div, le_div_iff₀ hLnum0]
      nlinarith [hkey, hydvpos, hLnum0]
    by_contra hcon
    push Not at hcon
    have hKy : (0 : ℝ) ≤ K * ‖y‖ := by positivity
    have hlt : (K * ‖y‖) ^ p < ‖w‖ ^ p := by
      refine pow_lt_pow_left₀ hcon hKy (by omega)
    have hexp : K * ‖y‖ ^ p ≤ (K * ‖y‖) ^ p := by
      rw [mul_pow]
      have hKp : K ≤ K ^ p := le_self_pow₀ hK1 (by omega)
      exact mul_le_mul_of_nonneg_right hKp (by positivity)
    linarith [hdiv, hlt, hexp]
  · -- the wild branch
    refine Or.inr ?_
    have hdeg : (C v).natDegree + p + 1 ≤ (C u).natDegree := by omega
    have hstep : ‖(C u).eval y‖ ≤ ((m : ℝ) + 1) * ‖(C v).eval y‖ * ‖w‖ ^ p := by
      have := hlow
      have h2 : ‖(C u).eval y‖ / (((m : ℝ) + 1) * ‖(C v).eval y‖) * (((m : ℝ) + 1)
          * ‖(C v).eval y‖) ≤ ‖w‖ ^ p * (((m : ℝ) + 1) * ‖(C v).eval y‖) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      rw [div_mul_cancel₀ _ (by positivity : ((m : ℝ) + 1) * ‖(C v).eval y‖ ≠ 0)] at h2
      linarith [h2]
    have hpowmono : ‖y‖ ^ (C v).natDegree * (‖y‖ ^ p * ‖y‖)
        ≤ ‖y‖ ^ (C u).natDegree := by
      have : ‖y‖ ^ ((C v).natDegree + p + 1) ≤ ‖y‖ ^ (C u).natDegree :=
        pow_le_pow_right₀ hy1 hdeg
      calc ‖y‖ ^ (C v).natDegree * (‖y‖ ^ p * ‖y‖)
          = ‖y‖ ^ ((C v).natDegree + p + 1) := by ring
        _ ≤ ‖y‖ ^ (C u).natDegree := this
    have hkey : Lnum * (‖y‖ ^ (C v).natDegree * (‖y‖ ^ p * ‖y‖))
        ≤ ((m : ℝ) + 1) * (Anum * ‖y‖ ^ (C v).natDegree) * ‖w‖ ^ p := by
      have h1 : Lnum * (‖y‖ ^ (C v).natDegree * (‖y‖ ^ p * ‖y‖))
          ≤ Lnum * ‖y‖ ^ (C u).natDegree :=
        mul_le_mul_of_nonneg_left hpowmono hLnum0.le
      have h2 : Lnum * ‖y‖ ^ (C u).natDegree ≤ ‖(C u).eval y‖ := hlower u hum (by
        intro h0
        rw [h0] at hAu
        simp at hAu)
      have h3 : ((m : ℝ) + 1) * ‖(C v).eval y‖ * ‖w‖ ^ p
          ≤ ((m : ℝ) + 1) * (Anum * ‖y‖ ^ (C v).natDegree) * ‖w‖ ^ p := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (hupper v hvm) hm1.le
      linarith [h1, h2, h3, hstep]
    have hcancel : c₀ * (‖y‖ ^ p * ‖y‖) ≤ ‖w‖ ^ p := by
      rw [hc₀, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hkey, hydvpos]
    -- raise to the `m`-th power and compare exponents
    have hstep2 : c₀ ^ m * (‖y‖ ^ ((p + 1) * m)) ≤ (‖w‖ ^ p) ^ m := by
      have hbase : (0 : ℝ) ≤ c₀ * (‖y‖ ^ p * ‖y‖) := by positivity
      have := pow_le_pow_left₀ hbase hcancel m
      calc c₀ ^ m * ‖y‖ ^ ((p + 1) * m)
          = (c₀ * (‖y‖ ^ p * ‖y‖)) ^ m := by
            rw [mul_pow, ← pow_succ, ← pow_mul]
        _ ≤ (‖w‖ ^ p) ^ m := this
    by_contra hcon
    push Not at hcon
    have hwm0 : (0 : ℝ) ≤ ‖w‖ ^ m := by positivity
    have hlt : (‖w‖ ^ m) ^ p < (c₀ ^ m * ‖y‖ ^ (m + 1)) ^ p :=
      pow_lt_pow_left₀ hcon hwm0 (by omega)
    have hswap : (‖w‖ ^ m) ^ p = (‖w‖ ^ p) ^ m := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hrhs : (c₀ ^ m * ‖y‖ ^ (m + 1)) ^ p = (c₀ ^ m) ^ p * ‖y‖ ^ ((m + 1) * p) := by
      ring
    have hcpow : (c₀ ^ m) ^ p ≤ c₀ ^ m := by
      refine pow_le_of_le_one (by positivity) (pow_le_one₀ hc₀0.le hc₀1) (by omega)
    have hypow : ‖y‖ ^ ((m + 1) * p) ≤ ‖y‖ ^ ((p + 1) * m) :=
      pow_le_pow_right₀ hy1 (by nlinarith [hpm])
    have hcm0 : (0 : ℝ) < c₀ ^ m := by positivity
    have hfinal : (c₀ ^ m) ^ p * ‖y‖ ^ ((m + 1) * p) ≤ c₀ ^ m * ‖y‖ ^ ((p + 1) * m) := by
      have h1 : (c₀ ^ m) ^ p * ‖y‖ ^ ((m + 1) * p) ≤ c₀ ^ m * ‖y‖ ^ ((m + 1) * p) :=
        mul_le_mul_of_nonneg_right hcpow (by positivity)
      have h2 : c₀ ^ m * ‖y‖ ^ ((m + 1) * p) ≤ c₀ ^ m * ‖y‖ ^ ((p + 1) * m) :=
        mul_le_mul_of_nonneg_left hypow hcm0.le
      linarith
    rw [hswap, hrhs] at hlt
    linarith [hlt, hfinal, hstep2]

/-- The dichotomy for an autonomous first-order relation, with `W = F′`. -/
theorem exists_deriv_dichotomy_of_relation {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ}
    (hCm : C m ≠ 0) {F : ℂ → ℂ}
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (F z) * (deriv F z) ^ k = 0) :
    ∃ K c R₀ : ℝ, 1 ≤ K ∧ 0 < c ∧ c ≤ 1 ∧ 1 ≤ R₀ ∧ ∀ z : ℂ, R₀ ≤ ‖F z‖ →
      ‖deriv F z‖ ≤ K * ‖F z‖ ∨ c * ‖F z‖ ^ (m + 1) ≤ ‖deriv F z‖ ^ m :=
  exists_dichotomy_of_relation hm hCm hrel

end GaloisForLFunctions.HTGeometry
