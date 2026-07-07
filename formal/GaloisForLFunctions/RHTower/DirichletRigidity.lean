/-
Finite-divisor rigidity for Dirichlet series (MWM lane; 08-population-and-local-returns §5.3,
the "surgery no-go" fragment of the droves dichotomy).

Main result: `RHTower.no_polynomial_surgery` — a somewhere-convergent L-series can never agree
on a right half-line with P(s)·(another somewhere-convergent L-series) for a polynomial P of
positive degree. Consequence for the lane: the divisor of a member of the Dirichlet-series
class cannot be modified by finite surgery (e.g. inserting a lone off-line zero quadruple
(s−ρ)(s−ρ̄)(1−s−ρ)(1−s−ρ̄) into ζ) without leaving the class — the class axiom itself is a
rigidity constraint.

Engine: mathlib's first-coefficient asymptotic `LSeries.tendsto_cpow_mul_atTop`
(n₀^x · LSeries f x → first nonzero coefficient), plus polynomial-vs-exponential asymptotics.
-/
import Mathlib

namespace RHTower

open Filter Real Complex LSeries Polynomial

/-- Least-nonzero-index extraction in the form `LSeries.tendsto_cpow_mul_atTop` consumes. -/
private lemma exists_first_index {g : ℕ → ℂ} (hg0 : g 0 = 0) (h : ∃ n, g n ≠ 0) :
    ∃ n : ℕ, (∀ m ≤ n, g m = 0) ∧ g (n + 1) ≠ 0 := by
  classical
  set k := Nat.find h with hkdef
  have hkne : g k ≠ 0 := Nat.find_spec h
  have hkpos : k ≠ 0 := fun h0 => hkne (h0 ▸ hg0)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkpos
  have hn' : k = n + 1 := hn
  refine ⟨n, fun m hm => ?_, by rw [← hn']; exact hkne⟩
  by_contra hne
  have hle : k ≤ m := Nat.find_le hne
  omega

/-- Crude but sufficient eventual bound: `‖P(x)‖ ≤ C·x^d` for `x ≥ 1`. -/
private lemma poly_norm_le (P : Polynomial ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖P.eval (x : ℂ)‖
      ≤ (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * x ^ P.natDegree := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  calc ‖∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (x : ℂ) ^ i‖
      ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i * (x : ℂ) ^ i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * x ^ P.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul, norm_pow]
        have hxn : ‖(x : ℂ)‖ = x := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
        rw [hxn]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hx (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
          (norm_nonneg _)

/-- Polynomial times decaying exponential vanishes: `‖P(x)‖ · r^x → 0` for `0 < r < 1`. -/
private lemma poly_mul_rpow_tendsto_zero (P : Polynomial ℂ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun x : ℝ => ‖P.eval (x : ℂ)‖ * r ^ x) atTop (nhds 0) := by
  set d := P.natDegree
  set C := ∑ i ∈ Finset.range (d + 1), ‖P.coeff i‖ with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set c := -Real.log r with hcdef
  have hcpos : 0 < c := by
    have := Real.log_neg hr0 hr1
    rw [hcdef]; linarith
  have hmain : Tendsto (fun x : ℝ => x ^ d * r ^ x) atTop (nhds 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.exp u / u ^ d) atTop atTop :=
      Real.tendsto_exp_div_pow_atTop d
    have h2 : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      Tendsto.const_mul_atTop hcpos tendsto_id
    have h3 : Tendsto (fun x : ℝ => Real.exp (c * x) / (c * x) ^ d) atTop atTop := h1.comp h2
    have h4 : Tendsto (fun x : ℝ => (Real.exp (c * x) / (c * x) ^ d) * c ^ d) atTop atTop :=
      h3.atTop_mul_const (pow_pos hcpos d)
    have h5 : Tendsto (fun x : ℝ => Real.exp (c * x) / x ^ d) atTop atTop := by
      refine h4.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hxd : (x : ℝ) ^ d ≠ 0 := pow_ne_zero _ hx.ne'
      have hcd : (c : ℝ) ^ d ≠ 0 := pow_ne_zero _ hcpos.ne'
      field_simp [mul_pow]
      ring
    have h6 := h5.inv_tendsto_atTop
    refine h6.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hexp : Real.exp (c * x) ≠ 0 := (Real.exp_pos _).ne'
    rw [Pi.inv_apply, Real.rpow_def_of_pos hr0]
    have hlog : Real.log r * x = -(c * x) := by rw [hcdef]; ring
    rw [hlog, Real.exp_neg]
    field_simp
  have hsq : Tendsto (fun x : ℝ => C * (x ^ d * r ^ x)) atTop (nhds 0) := by
    have := hmain.const_mul C
    simpa using this
  refine squeeze_zero' ?_ ?_ hsq
  · filter_upwards with x
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h := poly_norm_le P hx
    have hrx : (0 : ℝ) ≤ r ^ x := (Real.rpow_pos_of_pos hr0 x).le
    calc ‖P.eval (x : ℂ)‖ * r ^ x ≤ (C * x ^ d) * r ^ x :=
          mul_le_mul_of_nonneg_right h hrx
      _ = C * (x ^ d * r ^ x) := by ring

/-- Norm of the cpow prefactor in `LSeries.tendsto_cpow_mul_atTop`. -/
private lemma norm_natCast_cpow (n : ℕ) (x : ℝ) :
    ‖((n : ℂ) + 1) ^ (x : ℂ)‖ = ((n : ℝ) + 1) ^ x := by
  have h : ((n : ℂ) + 1) = ((((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.ofReal_re]

/-- **No polynomial surgery on Dirichlet series.** If `f` and `g` are coefficient sequences
whose L-series converge somewhere, `g` is not (essentially) zero, and `P` is a polynomial of
positive degree, then `LSeries f` cannot agree with `P · LSeries g` on any right half-line.
In particular the divisor of an L-series admits no modification by a polynomial factor
within the class. -/
theorem no_polynomial_surgery
    {P : Polynomial ℂ} (hP : 0 < P.natDegree)
    {g : ℕ → ℂ} (hga : abscissaOfAbsConv g < ⊤) (hgne : ∃ n, n ≠ 0 ∧ g n ≠ 0)
    {f : ℕ → ℂ} (hfa : abscissaOfAbsConv f < ⊤)
    (heq : ∀ᶠ x : ℝ in atTop, LSeries f (x : ℂ) = P.eval (x : ℂ) * LSeries g (x : ℂ)) :
    False := by
  classical
  -- Normalize the (irrelevant) value at 0.
  set f' : ℕ → ℂ := fun n => if n = 0 then 0 else f n with hf'def
  set g' : ℕ → ℂ := fun n => if n = 0 then 0 else g n with hg'def
  have hff' : ∀ {n : ℕ}, n ≠ 0 → f n = f' n := fun hn => by simp [hf'def, hn]
  have hgg' : ∀ {n : ℕ}, n ≠ 0 → g n = g' n := fun hn => by simp [hg'def, hn]
  have hf'a : abscissaOfAbsConv f' < ⊤ := (abscissaOfAbsConv_congr hff') ▸ hfa
  have hg'a : abscissaOfAbsConv g' < ⊤ := (abscissaOfAbsConv_congr hgg') ▸ hga
  have hLf : ∀ s : ℂ, LSeries f s = LSeries f' s := LSeries_congr hff'
  have hLg : ∀ s : ℂ, LSeries g s = LSeries g' s := LSeries_congr hgg'
  have heq' : ∀ᶠ x : ℝ in atTop,
      LSeries f' (x : ℂ) = P.eval (x : ℂ) * LSeries g' (x : ℂ) := by
    filter_upwards [heq] with x hx
    rw [← hLf, ← hLg]; exact hx
  -- Polynomial norm blows up along the real axis.
  have hznorm : Tendsto (fun x : ℝ => ‖(x : ℂ)‖) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self x
  have hPnorm : Tendsto (fun x : ℝ => ‖P.eval (x : ℂ)‖) atTop atTop :=
    Polynomial.tendsto_norm_atTop P (Polynomial.natDegree_pos_iff_degree_pos.mp hP) hznorm
  have hPone : ∀ᶠ x : ℝ in atTop, 1 ≤ ‖P.eval (x : ℂ)‖ := hPnorm.eventually_ge_atTop 1
  -- First nonzero g-coefficient and its asymptotic.
  have hg'ne : ∃ n, g' n ≠ 0 := by
    obtain ⟨n, hn0, hgn⟩ := hgne
    exact ⟨n, by rw [← hgg' hn0]; exact hgn⟩
  obtain ⟨a, ha0, hane⟩ := exists_first_index (by simp [hg'def]) hg'ne
  have hB := LSeries.tendsto_cpow_mul_atTop (f := g') (n := a) ha0 hg'a
  have hBnorm := hB.norm
  by_cases hfz : ∀ n, f' n = 0
  · -- f' ≡ 0: the right-hand side must vanish eventually, forcing g' (a+1) = 0.
    have hf0 : f' = 0 := funext hfz
    have hzero : ∀ᶠ x : ℝ in atTop,
        ((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ) = 0 := by
      filter_upwards [heq', hPone] with x hx h1
      have hPne : P.eval (x : ℂ) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h1; linarith
      have : LSeries g' (x : ℂ) = 0 := by
        have := hx
        rw [hf0, LSeries_zero] at this
        rcases mul_eq_zero.mp this.symm with h | h
        · exact absurd h hPne
        · exact h
      rw [this, mul_zero]
    have h0 : Tendsto (fun x : ℝ => ((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ))
        atTop (nhds 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hzero] with x hx
      exact hx.symm
    exact hane (tendsto_nhds_unique hB h0)
  · -- f' has a first nonzero coefficient.
    push Not at hfz
    obtain ⟨b, hb0, hbne⟩ := exists_first_index (by simp [hf'def]) hfz
    have hA := LSeries.tendsto_cpow_mul_atTop (f := f') (n := b) hb0 hf'a
    have hAnorm := hA.norm
    -- The eventual norm identity linking the two asymptotics through P.
    have hnorm : ∀ᶠ x : ℝ in atTop,
        ‖((b : ℂ) + 1) ^ (x : ℂ) * LSeries f' (x : ℂ)‖
          = (‖P.eval (x : ℂ)‖ * (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x)
            * ‖((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ)‖ := by
      filter_upwards [heq'] with x hx
      have hb1 : (0 : ℝ) < (b : ℝ) + 1 := by positivity
      have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      rw [norm_mul, norm_mul, norm_natCast_cpow, norm_natCast_cpow, hx, norm_mul,
        Real.div_rpow hb1.le ha1.le]
      have hax : ((a : ℝ) + 1) ^ x ≠ 0 := (Real.rpow_pos_of_pos ha1 x).ne'
      field_simp
    have hαpos : 0 < ‖f' (b + 1)‖ := norm_pos_iff.mpr hbne
    have hβpos : 0 < ‖g' (a + 1)‖ := norm_pos_iff.mpr hane
    have hBhalf : ∀ᶠ x : ℝ in atTop,
        ‖g' (a + 1)‖ / 2 < ‖((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ)‖ :=
      hBnorm.eventually (eventually_gt_nhds (half_lt_self hβpos))
    rcases lt_trichotomy b a with hba | hba | hba
    · -- b < a: ratio < 1; the right side collapses to 0, the left tends to ‖f' (b+1)‖ ≠ 0.
      have hr0 : 0 < ((b : ℝ) + 1) / ((a : ℝ) + 1) := by positivity
      have hr1 : ((b : ℝ) + 1) / ((a : ℝ) + 1) < 1 := by
        rw [div_lt_one (by positivity)]
        exact_mod_cast Nat.add_lt_add_right hba 1
      have hRHS : Tendsto (fun x : ℝ =>
          (‖P.eval (x : ℂ)‖ * (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x)
            * ‖((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ)‖) atTop (nhds 0) := by
        have := (poly_mul_rpow_tendsto_zero P hr0 hr1).mul hBnorm
        simpa using this
      have hLHS : Tendsto (fun x : ℝ =>
          ‖((b : ℂ) + 1) ^ (x : ℂ) * LSeries f' (x : ℂ)‖) atTop (nhds 0) :=
        hRHS.congr' (by filter_upwards [hnorm] with x hx; exact hx.symm)
      exact hαpos.ne' (tendsto_nhds_unique hAnorm hLHS)
    · -- b = a: the left side is ‖P‖·‖B‖, which blows up while tending to a finite limit.
      subst hba
      have hratio : ∀ᶠ x : ℝ in atTop,
          ‖P.eval (x : ℂ)‖ * (‖g' (b + 1)‖ / 2)
            ≤ ‖((b : ℂ) + 1) ^ (x : ℂ) * LSeries f' (x : ℂ)‖ := by
        filter_upwards [hnorm, hBhalf] with x hx hBx
        rw [hx]
        have h1 : (((b : ℝ) + 1) / ((b : ℝ) + 1)) ^ x = 1 := by
          rw [div_self (by positivity : ((b : ℝ) + 1) ≠ 0), Real.one_rpow]
        rw [h1, mul_one]
        exact mul_le_mul_of_nonneg_left hBx.le (norm_nonneg _)
      have hblow : Tendsto (fun x : ℝ =>
          ‖((b : ℂ) + 1) ^ (x : ℂ) * LSeries f' (x : ℂ)‖) atTop atTop :=
        tendsto_atTop_mono' _ hratio (hPnorm.atTop_mul_const (by positivity))
      exact hAnorm.not_tendsto (disjoint_nhds_atTop _) hblow
    · -- a < b: ratio > 1; the left side blows up at exponential rate.
      have hr1 : 1 < ((b : ℝ) + 1) / ((a : ℝ) + 1) := by
        rw [lt_div_iff₀ (by positivity)]
        have : (a : ℝ) + 1 < (b : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right hba 1
        linarith
      have hrx : Tendsto (fun x : ℝ => (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x) atTop atTop := by
        have hlog : 0 < Real.log (((b : ℝ) + 1) / ((a : ℝ) + 1)) := Real.log_pos hr1
        have h2 : Tendsto (fun x : ℝ => Real.log (((b : ℝ) + 1) / ((a : ℝ) + 1)) * x)
            atTop atTop := Tendsto.const_mul_atTop hlog tendsto_id
        refine (Real.tendsto_exp_atTop.comp h2).congr' ?_
        filter_upwards with x
        rw [Function.comp_apply, ← Real.rpow_def_of_pos (by positivity)]
      have hratio : ∀ᶠ x : ℝ in atTop,
          (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x * (‖g' (a + 1)‖ / 2)
            ≤ ‖((b : ℂ) + 1) ^ (x : ℂ) * LSeries f' (x : ℂ)‖ := by
        filter_upwards [hnorm, hBhalf, hPone] with x hx hBx hPx
        rw [hx]
        have hstep : (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x * (‖g' (a + 1)‖ / 2)
            ≤ (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x
              * ‖((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hBx.le (Real.rpow_pos_of_pos (by positivity) x).le
        calc (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x * (‖g' (a + 1)‖ / 2)
            ≤ (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x
              * ‖((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ)‖ := hstep
          _ ≤ (‖P.eval (x : ℂ)‖ * (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x)
              * ‖((a : ℂ) + 1) ^ (x : ℂ) * LSeries g' (x : ℂ)‖ := by
              have h1 : (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x
                  ≤ ‖P.eval (x : ℂ)‖ * (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^ x := by
                nlinarith [(Real.rpow_pos_of_pos
                  (show (0:ℝ) < ((b : ℝ) + 1) / ((a : ℝ) + 1) by positivity) x).le]
              exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have hblow : Tendsto (fun x : ℝ =>
          ‖((b : ℂ) + 1) ^ (x : ℂ) * LSeries f' (x : ℂ)‖) atTop atTop :=
        tendsto_atTop_mono' _ hratio (hrx.atTop_mul_const (by positivity))
      exact hAnorm.not_tendsto (disjoint_nhds_atTop _) hblow

end RHTower

namespace RHTower

open Filter LSeries

/-- **ζ-instance of the surgery no-go**: no somewhere-convergent L-series agrees on a right
half-line with P(s)·ζ(s) for a polynomial P of positive degree. One cannot insert finitely
many zeros into (or excise them from) the divisor of ζ by a polynomial factor — e.g. a lone
off-line zero quadruple (s−ρ)(s−ρ̄)(1−s−ρ)(1−s−ρ̄) — and remain a Dirichlet series. -/
theorem no_polynomial_surgery_zeta
    {P : Polynomial ℂ} (hP : 0 < P.natDegree)
    {f : ℕ → ℂ} (hfa : abscissaOfAbsConv f < ⊤)
    (heq : ∀ᶠ x : ℝ in atTop,
      LSeries f (x : ℂ) = P.eval (x : ℂ) * riemannZeta (x : ℂ)) :
    False := by
  have h1a : abscissaOfAbsConv (1 : ℕ → ℂ) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_one]
    simpa using EReal.coe_lt_top 1
  refine no_polynomial_surgery hP h1a ⟨1, one_ne_zero, by norm_num⟩ hfa ?_
  filter_upwards [heq, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [hx, LSeries_one_eq_riemannZeta (by simpa using hx1)]

end RHTower
