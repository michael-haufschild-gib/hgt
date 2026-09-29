import GaloisForLFunctions.PNTPlus.Wiener

/-!
# Sharp upper bound for prime sums in a residue class

For `q ≥ 1`, `a` coprime to `q`, `a < q`, and `1 < σ ≤ 2`:

```text
Σ_{p ≡ a (mod q)} p^{−σ} ≤ (1/φ(q)) · log(1/(σ−1)) + C .
```

The leading constant `1/φ(q)` is sharp. Proof: put
`F(σ) = Σ_{n ≡ a} (Λ(n)/log n) n^{−σ}`, whose derivative is `−Σ_{n ≡ a} Λ(n) n^{−σ}`. The
residue-class `L`-series minus `(1/φ(q))/(s−1)` extends continuously to `Re s ≥ 1`, hence is
bounded by some `K` on `[1,2]`. So `F(σ) + (1/φ(q)) log(σ−1) + Kσ` is monotone on `(1,2]`, and
`F(σ) ≥ Σ_{p ≡ a} p^{−σ}` over any finite set of primes.
-/

noncomputable section

open ArithmeticFunction Filter Complex

namespace RHTower.ResidueClassPrimes

/-- `Λ(n)/log n` on the class `n ≡ a (mod q)`, zero elsewhere. -/
def logWeight (q a : ℕ) (n : ℕ) : ℂ :=
  if n % q = a then ((vonMangoldt n / Real.log n : ℝ) : ℂ) else 0

/-- `Λ(n)` on the class `n ≡ a (mod q)`, zero elsewhere. -/
def classVonMangoldt (q a : ℕ) (n : ℕ) : ℂ :=
  if n % q = a then (vonMangoldt n : ℂ) else 0

theorem vonMangoldt_div_log_le_one (n : ℕ) : vonMangoldt n / Real.log n ≤ 1 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    rw [div_le_one hlog]; exact vonMangoldt_le_log

theorem vonMangoldt_div_log_nonneg (n : ℕ) : 0 ≤ vonMangoldt n / Real.log n :=
  div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

theorem logMul_logWeight (q a : ℕ) : LSeries.logMul (logWeight q a) = classVonMangoldt q a := by
  funext n
  simp only [LSeries.logMul, logWeight, classVonMangoldt]
  split_ifs with h
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), ← Complex.ofReal_mul]
      congr 1
      field_simp
  · simp

theorem norm_logWeight_le (q a n : ℕ) : ‖logWeight q a n‖ ≤ 1 := by
  unfold logWeight
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (vonMangoldt_div_log_nonneg n)]
    exact vonMangoldt_div_log_le_one n
  · simp

theorem LSeriesSummable_logWeight (q a : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (logWeight q a) s := by
  exact LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => norm_logWeight_le q a n) hs

theorem abscissa_logWeight_le (q a : ℕ) :
    LSeries.abscissaOfAbsConv (logWeight q a) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact LSeriesSummable_logWeight q a (by simpa using hy)

/-- `F(σ) = Σ_{n ≡ a} (Λ(n)/log n) n^{−σ}` as a real function. -/
def logWeightSum (q a : ℕ) (σ : ℝ) : ℝ := (LSeries (logWeight q a) σ).re

theorem hasDerivAt_logWeightSum (q a : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (logWeightSum q a) (-(LSeries (classVonMangoldt q a) σ).re) σ := by
  have h := LSeries_hasDerivAt (f := logWeight q a) (s := (σ : ℂ))
    (lt_of_le_of_lt (abscissa_logWeight_le q a) (by exact_mod_cast hσ))
  rw [logMul_logWeight] at h
  exact h.real_of_complex

/-- The class `L`-series is at most `(1/φ(q))/(σ−1) + K` on `(1,2]`. -/
theorem exists_classVonMangoldt_re_le {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (LSeries (classVonMangoldt q a) σ).re ≤ (1 / (q.totient : ℝ)) / (σ - 1) + K := by
  obtain ⟨G, hGc, hGeq⟩ := WeakPNT_AP_prelim hq ha haq
  have hcomp : IsCompact ((fun t : ℝ => (t : ℂ)) '' Set.Icc 1 2) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hsub : (fun t : ℝ => (t : ℂ)) '' Set.Icc 1 2 ⊆ {s : ℂ | 1 ≤ s.re} := by
    rintro _ ⟨t, ht, rfl⟩; simpa using ht.1
  obtain ⟨K, hK⟩ := hcomp.exists_bound_of_continuousOn (hGc.mono hsub)
  refine ⟨|K|, abs_nonneg _, fun σ hσ hσ2 => ?_⟩
  have hmem : (σ : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hσ
  have heq := hGeq hmem
  have hL : LSeries (classVonMangoldt q a) σ =
      G σ + 1 / ((q.totient : ℂ) * ((σ : ℂ) - 1)) := by
    have : G σ = LSeries (classVonMangoldt q a) σ - 1 / ((q.totient : ℂ) * ((σ : ℂ) - 1)) := heq
    rw [this]; ring
  have hGσ : ‖G σ‖ ≤ K := hK _ ⟨σ, ⟨hσ.le, hσ2⟩, rfl⟩
  have hre : (1 / ((q.totient : ℂ) * ((σ : ℂ) - 1))).re = (1 / (q.totient : ℝ)) / (σ - 1) := by
    rw [show ((q.totient : ℂ) * ((σ : ℂ) - 1)) = (((q.totient : ℝ) * (σ - 1) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    field_simp
  rw [hL, Complex.add_re, hre]
  have := (Complex.re_le_norm (G σ)).trans (hGσ.trans (le_abs_self K))
  linarith

/-- **Sharp upper bound for `F`.** `F(σ) ≤ (1/φ(q)) log(1/(σ−1)) + C` on `(1,2]`. -/
theorem exists_logWeightSum_le {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      logWeightSum q a σ ≤ (1 / (q.totient : ℝ)) * Real.log (1 / (σ - 1)) + C := by
  obtain ⟨K, hK0, hK⟩ := exists_classVonMangoldt_re_le hq ha haq
  set c : ℝ := 1 / (q.totient : ℝ) with hc
  set H : ℝ → ℝ := fun σ => logWeightSum q a σ + c * Real.log (σ - 1) + K * σ with hH
  have hderiv : ∀ σ : ℝ, 1 < σ →
      HasDerivAt H (-(LSeries (classVonMangoldt q a) σ).re + c * (1 / (σ - 1)) + K) σ := by
    intro σ hσ
    have h1 := hasDerivAt_logWeightSum q a hσ
    have h2 : HasDerivAt (fun t : ℝ => Real.log (t - 1)) (1 / (σ - 1)) σ := by
      have := ((hasDerivAt_id σ).sub_const 1).log (by simp; linarith)
      simpa using this
    have h3 : HasDerivAt (fun t : ℝ => K * t) K σ := by
      simpa using (hasDerivAt_id σ).const_mul K
    exact (h1.add (h2.const_mul c)).add h3
  have hmono : MonotoneOn H (Set.Ioc 1 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 1 2)
    · intro σ hσ
      exact (hderiv σ hσ.1).continuousAt.continuousWithinAt
    · intro σ hσ
      rw [interior_Ioc] at hσ
      exact (hderiv σ hσ.1).differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Ioc] at hσ
      rw [(hderiv σ hσ.1).deriv]
      have := hK σ hσ.1 hσ.2.le
      have hpos : 0 < σ - 1 := by linarith [hσ.1]
      rw [hc] at this ⊢
      have : c * (1 / (σ - 1)) = (1 / (q.totient : ℝ)) / (σ - 1) := by rw [hc]; ring
      linarith
  refine ⟨H 2, fun σ hσ hσ2 => ?_⟩
  have hle := hmono ⟨hσ, hσ2⟩ ⟨by norm_num, le_refl 2⟩ hσ2
  simp only [hH] at hle
  have hlog : Real.log (1 / (σ - 1)) = -Real.log (σ - 1) := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  have hKσ : 0 ≤ K * σ := mul_nonneg hK0 (by linarith)
  nlinarith

/-- `F(σ)` dominates the prime sum over any finite set. -/
theorem sum_prime_rpow_le_logWeightSum (q a : ℕ) {σ : ℝ} (hσ : 1 < σ) (s : Finset ℕ) :
    ∑ p ∈ s.filter (fun p => p.Prime ∧ p % q = a), (p : ℝ) ^ (-σ) ≤ logWeightSum q a σ := by
  have hsum : LSeriesSummable (logWeight q a) σ := LSeriesSummable_logWeight q a (by simpa using hσ)
  have hre : logWeightSum q a σ = ∑' n : ℕ, (LSeries.term (logWeight q a) σ n).re := by
    rw [logWeightSum, LSeries, Complex.re_tsum hsum]
  -- the real terms
  have hterm : ∀ n : ℕ, (LSeries.term (logWeight q a) σ n).re =
      if n = 0 then 0 else (if n % q = a then vonMangoldt n / Real.log n else 0) *
        (n : ℝ) ^ (-σ) := by
    intro n
    rw [LSeries.term_def]
    split_ifs with h0 hq'
    · simp
    · rw [logWeight, if_pos hq', ← Complex.ofReal_natCast,
        ← Complex.ofReal_cpow (Nat.cast_nonneg n), ← Complex.ofReal_div, Complex.ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    · simp [logWeight, if_neg hq']
  have hnonneg : ∀ n : ℕ, 0 ≤ (LSeries.term (logWeight q a) σ n).re := by
    intro n
    rw [hterm]
    split_ifs
    · exact le_refl 0
    · exact mul_nonneg (vonMangoldt_div_log_nonneg n) (by positivity)
    · simp
  have hsumre : Summable fun n : ℕ => (LSeries.term (logWeight q a) σ n).re :=
    (Complex.reCLM.summable hsum)
  rw [hre]
  refine le_trans ?_ (hsumre.sum_le_tsum (s.filter fun p => p.Prime ∧ p % q = a)
    (fun n _ => hnonneg n))
  refine le_of_eq (Finset.sum_congr rfl fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hpp, hpq⟩ := hp
  rw [hterm, if_neg hpp.ne_zero, if_pos hpq, vonMangoldt_apply_prime hpp,
    div_self (Real.log_pos (by exact_mod_cast hpp.one_lt)).ne', one_mul]

/-- **Sharp prime-sum bound in a residue class.** -/
theorem exists_sum_prime_rpow_le {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ s : Finset ℕ,
      ∑ p ∈ s.filter (fun p => p.Prime ∧ p % q = a), (p : ℝ) ^ (-σ) ≤
        (1 / (q.totient : ℝ)) * Real.log (1 / (σ - 1)) + C := by
  obtain ⟨C, hC⟩ := exists_logWeightSum_le hq ha haq
  exact ⟨C, fun σ hσ hσ2 s => (sum_prime_rpow_le_logWeightSum q a hσ s).trans (hC σ hσ hσ2)⟩

end RHTower.ResidueClassPrimes
