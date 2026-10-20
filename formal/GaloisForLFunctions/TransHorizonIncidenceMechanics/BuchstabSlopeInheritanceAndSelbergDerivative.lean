import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabSlopeLawAndPrimeHorizonDissipation

/-!
# Buchstab slopes: the horizon derivative of the Selberg form, and inheritance

Write `A(m) = Σ_{d<m} μ(d) gcd(d,m)/d`, so the Buchstab slope is `λ(m) = 1 + 2 μ(m) A(m)`.

* **Horizon derivative.** The Selberg diagonal form of the Möbius sieve, equal to the period mean
  square of the response, changes across one horizon step by exactly `μ(m)² λ(m)/m`. The slope
  that governs the prefix-energy step at large ratios is the derivative of the mean square.
* **Inheritance.** For squarefree `a` and a prime `q > a`,
  `λ(aq) = λ(a) - 2 μ(a) (G_a(aq-1) + A(a)/q)` with `G_a(x) = Σ_{d≤x} μ(d) gcd(d,a)/d`.
  The gcd-twisted harmonic Möbius sum `G_a` tends to zero, because it is a finite combination of
  coprime harmonic Möbius sums, each obtained from `m(x) → 0` by a contracting recursion. Hence
  `λ(aq) → λ(a)`: attaching a large prime factor to a horizon does not change its slope. This is
  rough absorption for horizon steps: large primes are invisible to the Buchstab slope, which is
  fixed by the small-prime part of the horizon. For instance `λ(2q) → -1` and `λ(3q) → 0`, while
  `λ(q) → 1`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The gcd-twisted harmonic Möbius sum `A(m) = Σ_{d<m} μ(d) gcd(d,m)/d` inside the slope. -/
def buchstabSlopeCore (m : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 (m - 1), moebiusReal d * ((Nat.gcd d m : ℕ) : ℝ) / (d : ℝ)

theorem buchstabSlope_eq_core (m : ℕ) :
    buchstabSlope m = 1 + 2 * moebiusReal m * buchstabSlopeCore m := rfl

/-! ### The horizon derivative of the Selberg form -/

private theorem lcm_form_split (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ (Icc 1 (N + 1)) ×ˢ (Icc 1 (N + 1)), f p.1 p.2) =
      (∑ p ∈ (Icc 1 N) ×ˢ (Icc 1 N), f p.1 p.2) + (∑ d ∈ Icc 1 N, f d (N + 1)) +
        (∑ e ∈ Icc 1 N, f (N + 1) e) + f (N + 1) (N + 1) := by
  rw [sum_product, sum_product, sum_Icc_succ_top (by omega)]
  simp_rw [sum_Icc_succ_top (show 1 ≤ N + 1 by omega)]
  rw [sum_add_distrib]
  ring

/-- **Horizon derivative of the Selberg form.** Across the horizon step to `m = n + 1`,
`Q_Sel(m) - Q_Sel(m-1) = μ(m)² (1 + 2 μ(m) A(m))/m`; at squarefree `m` this is `λ(m)/m`. -/
theorem selbergTotientDiagonalForm_moebius_step (n : ℕ) :
    selbergTotientDiagonalForm (n + 1) moebiusReal - selbergTotientDiagonalForm n moebiusReal =
      (moebiusReal (n + 1) ^ 2 + 2 * moebiusReal (n + 1) * buchstabSlopeCore (n + 1)) /
        ((n : ℝ) + 1) := by
  rw [← sum_div_lcm_eq_selbergTotientDiagonalForm, ← sum_div_lcm_eq_selbergTotientDiagonalForm,
    lcm_form_split n (fun d e => moebiusReal d * moebiusReal e / (Nat.lcm d e : ℝ))]
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hterm (d : ℕ) (hd : d ∈ Icc 1 n) :
      moebiusReal d * moebiusReal (n + 1) / (Nat.lcm d (n + 1) : ℝ) =
        moebiusReal (n + 1) * (moebiusReal d * ((Nat.gcd d (n + 1) : ℕ) : ℝ) / (d : ℝ)) /
          ((n : ℝ) + 1) := by
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    have hgl := Nat.gcd_mul_lcm d (n + 1)
    have hgl' : ((Nat.gcd d (n + 1) : ℕ) : ℝ) * (Nat.lcm d (n + 1) : ℝ) = d * ((n : ℝ) + 1) := by
      exact_mod_cast hgl
    have hl : (0 : ℝ) < (Nat.lcm d (n + 1) : ℝ) := by
      exact_mod_cast Nat.lcm_pos hd0 (by omega)
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
    have hinv : (1 : ℝ) / (Nat.lcm d (n + 1) : ℝ) =
        ((Nat.gcd d (n + 1) : ℕ) : ℝ) / ((d : ℝ) * ((n : ℝ) + 1)) := by
      rw [div_eq_div_iff hl.ne' (by positivity)]
      linarith [hgl']
    calc moebiusReal d * moebiusReal (n + 1) / (Nat.lcm d (n + 1) : ℝ) =
        moebiusReal d * moebiusReal (n + 1) * ((1 : ℝ) / (Nat.lcm d (n + 1) : ℝ)) := by ring
      _ = moebiusReal d * moebiusReal (n + 1) *
          (((Nat.gcd d (n + 1) : ℕ) : ℝ) / ((d : ℝ) * ((n : ℝ) + 1))) := by rw [hinv]
      _ = _ := by field_simp
  have hsym : (∑ e ∈ Icc 1 n, moebiusReal (n + 1) * moebiusReal e / (Nat.lcm (n + 1) e : ℝ)) =
      ∑ d ∈ Icc 1 n, moebiusReal d * moebiusReal (n + 1) / (Nat.lcm d (n + 1) : ℝ) :=
    sum_congr rfl fun e _ => by rw [Nat.lcm_comm, mul_comm (moebiusReal (n + 1))]
  rw [hsym, sum_congr rfl hterm, Nat.lcm_self]
  unfold buchstabSlopeCore
  rw [show n + 1 - 1 = n by omega, ← sum_div, ← mul_sum]
  push_cast
  field_simp
  ring

/-- At a squarefree horizon the Selberg form grows by exactly `λ(m)/m`. -/
theorem selbergTotientDiagonalForm_moebius_step_squarefree {n : ℕ} (hsq : Squarefree (n + 1)) :
    selbergTotientDiagonalForm (n + 1) moebiusReal - selbergTotientDiagonalForm n moebiusReal =
      buchstabSlope (n + 1) / ((n : ℝ) + 1) := by
  rw [selbergTotientDiagonalForm_moebius_step, buchstabSlope_eq_core]
  have hμ : moebiusReal (n + 1) ^ 2 = 1 := by
    unfold moebiusReal
    rw [moebius_apply_of_squarefree hsq]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hμ]

/-! ### Coprime harmonic Möbius sums -/

/-- The coprime harmonic Möbius sum `m_f(n) = Σ_{d≤n, (d,f)=1} μ(d)/d`. -/
def coprimeHarmonicMoebius (f n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, if Nat.Coprime d f then moebiusReal d / (d : ℝ) else 0

private theorem sum_Icc_multiples (p n : ℕ) (hp : 0 < p) (g : ℕ → ℝ) :
    (∑ d ∈ (Icc 1 n).filter (fun d => p ∣ d), g d) = ∑ e ∈ Icc 1 (n / p), g (p * e) := by
  have hset : (Icc 1 n).filter (fun d => p ∣ d) = (Icc 1 (n / p)).image (fun e => p * e) := by
    ext d
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hp).mpr (by linarith [mul_comm p k])⟩, rfl⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h1
      · exact hk
    · rintro ⟨e, ⟨h1, h2⟩, rfl⟩
      have := (Nat.le_div_iff_mul_le hp).mp h2
      exact ⟨⟨by nlinarith, by linarith [mul_comm p e]⟩, dvd_mul_right p e⟩
  rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]

/-- Removing a prime: `m_f(n) = m_{fp}(n) - m_{fp}(n/p)/p` for a prime `p ∤ f`. -/
theorem coprimeHarmonicMoebius_prime_step {f p : ℕ} (hp : p.Prime) (hpf : ¬ p ∣ f) (n : ℕ) :
    coprimeHarmonicMoebius f n =
      coprimeHarmonicMoebius (f * p) n - coprimeHarmonicMoebius (f * p) (n / p) / p := by
  unfold coprimeHarmonicMoebius
  rw [← sum_filter_add_sum_filter_not (Icc 1 n) (fun d => p ∣ d)]
  have hnot : (∑ d ∈ (Icc 1 n).filter (fun d => ¬ p ∣ d),
      if Nat.Coprime d f then moebiusReal d / (d : ℝ) else 0) =
      ∑ d ∈ Icc 1 n, if Nat.Coprime d (f * p) then moebiusReal d / (d : ℝ) else 0 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases hd : p ∣ d
    · have : ¬ Nat.Coprime d (f * p) := fun h =>
        (Nat.Prime.coprime_iff_not_dvd hp).mp
          (Nat.Coprime.coprime_dvd_right (dvd_mul_left p f) h).symm hd
      simp [hd, this]
    · have hdp : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd).symm
      rw [if_pos hd]
      simp only [Nat.coprime_mul_iff_right, and_iff_left hdp]
  have hdiv : (∑ d ∈ (Icc 1 n).filter (fun d => p ∣ d),
      if Nat.Coprime d f then moebiusReal d / (d : ℝ) else 0) =
      -(∑ e ∈ Icc 1 (n / p), if Nat.Coprime e (f * p) then moebiusReal e / (e : ℝ) else 0) /
        p := by
    rw [sum_Icc_multiples p n hp.pos]
    rw [show -(∑ e ∈ Icc 1 (n / p), if Nat.Coprime e (f * p) then moebiusReal e / (e : ℝ) else 0) /
        (p : ℝ) = ∑ e ∈ Icc 1 (n / p),
          -(if Nat.Coprime e (f * p) then moebiusReal e / (e : ℝ) else 0) / (p : ℝ) by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]]
    apply sum_congr rfl
    intro e he
    have he0 : 0 < e := (mem_Icc.mp he).1
    have hcopf : Nat.Coprime (p * e) f ↔ Nat.Coprime e f := by
      rw [Nat.coprime_mul_iff_left]
      exact ⟨fun h => h.2, fun h => ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hpf, h⟩⟩
    by_cases hpe : p ∣ e
    · have hμ : moebiusReal (p * e) = 0 := by
        apply moebiusReal_eq_zero_of_not_squarefree
        intro hsq
        obtain ⟨k, rfl⟩ := hpe
        have := hsq p ⟨k, by ring⟩
        exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
      have hnc : ¬ Nat.Coprime e (f * p) := fun h =>
        (Nat.Prime.coprime_iff_not_dvd hp).mp
          (Nat.Coprime.coprime_dvd_right (dvd_mul_left p f) h).symm hpe
      simp [hμ, hnc]
    · have hcop : Nat.Coprime p e := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpe
      have hμ : moebiusReal (p * e) = -moebiusReal e := by
        unfold moebiusReal
        rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp]
        push_cast; ring
      have hc2 : Nat.Coprime e (f * p) ↔ Nat.Coprime e f := by
        rw [Nat.coprime_mul_iff_right]
        exact ⟨fun h => h.1, fun h => ⟨h, hcop.symm⟩⟩
      by_cases hc : Nat.Coprime e f
      · rw [if_pos (hcopf.mpr hc), if_pos (hc2.mpr hc), hμ]
        push_cast
        field_simp
      · rw [if_neg (fun h => hc (hcopf.mp h)), if_neg (fun h => hc (hc2.mp h))]
        simp
  rw [hnot, hdiv]
  ring

/-- A contracting recursion `u(n) = v(n) + u(n/p)/p` transmits convergence to zero. -/
private theorem tendsto_zero_of_contraction (u v : ℕ → ℝ) {p : ℕ} (hp : 2 ≤ p)
    (hrec : ∀ n, u n = v n + u (n / p) / p) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, |v n| ≤ C := by
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto v hv).exists_norm_le
    exact ⟨C, fun n => by simpa using hC (v n) ⟨n, rfl⟩⟩
  -- uniform bound `|u| ≤ 2C`
  have hub : ∀ n, |u n| ≤ 2 * C := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h0 := hrec 0
        simp only [Nat.zero_div] at h0
        have : u 0 * (1 - 1 / (p : ℝ)) = v 0 := by field_simp at h0 ⊢; linarith
        have hq : (1 / 2 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
          rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
          rw [div_le_iff₀ (by linarith)]; linarith
        have habs : |u 0| * (1 - 1 / (p : ℝ)) = |v 0| := by
          rw [← this, abs_mul, abs_of_pos (show (0 : ℝ) < 1 - 1 / (p : ℝ) by linarith)]
        nlinarith [hC 0, abs_nonneg (u 0)]
      · have hlt : n / p < n := Nat.div_lt_self hn (by omega)
        have h := ih (n / p) hlt
        rw [hrec n]
        have hdiv : |u (n / p) / p| ≤ |u (n / p)| / 2 := by
          rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < p)]
          exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hpR
        calc |v n + u (n / p) / p| ≤ |v n| + |u (n / p) / p| := abs_add_le _ _
          _ ≤ C + 2 * C / 2 := by linarith [hC n]
          _ = 2 * C := by ring
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := (Metric.tendsto_atTop.mp hv) (ε / 4) (by positivity)
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (4 * (C + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  -- `|u n| ≤ ε/2 (1 - 2^-j) + 2C 2^-j` beyond `n₀ p^j`
  have hstep : ∀ j : ℕ, ∀ n, (n₀ + 1) * p ^ j ≤ n →
      |u n| ≤ ε / 2 * (1 - (1 / 2 : ℝ) ^ j) + 2 * C * (1 / 2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => intro n _; simpa using hub n
    | succ j ih =>
      intro n hn
      have hnp : (n₀ + 1) * p ^ j ≤ n / p := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        calc (n₀ + 1) * p ^ j * p = (n₀ + 1) * p ^ (j + 1) := by ring
          _ ≤ n := hn
      have hn0 : n₀ ≤ n := by
        have : (n₀ + 1) * 1 ≤ (n₀ + 1) * p ^ (j + 1) :=
          Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
        omega
      have hv' := hn₀ n hn0
      rw [Real.dist_eq, sub_zero] at hv'
      have hu' := ih (n / p) hnp
      rw [hrec n]
      have hdiv : |u (n / p) / p| ≤ |u (n / p)| / 2 := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < p)]
        exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hpR
      calc |v n + u (n / p) / p| ≤ |v n| + |u (n / p) / p| := abs_add_le _ _
        _ ≤ ε / 4 + (ε / 2 * (1 - (1 / 2 : ℝ) ^ j) + 2 * C * (1 / 2 : ℝ) ^ j) / 2 := by
            linarith
        _ ≤ _ := by
            rw [pow_succ]
            have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
            nlinarith
  refine ⟨(n₀ + 1) * p ^ J, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have h := hstep J n hn
  have hpow : 2 * C * (1 / 2 : ℝ) ^ J < ε / 2 := by
    have : 2 * C * (1 / 2 : ℝ) ^ J ≤ 2 * (C + 1) * (ε / (4 * (C + 1))) := by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := by positivity
      nlinarith
    have e : 2 * (C + 1) * (ε / (4 * (C + 1))) = ε / 2 := by field_simp; ring
    have hpos : (0 : ℝ) < (1 / 2) ^ J := by positivity
    nlinarith
  have : ε / 2 * (1 - (1 / 2 : ℝ) ^ J) ≤ ε / 2 := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := by positivity
    nlinarith
  linarith

/-- Coprime harmonic Möbius sums over any finite set of primes tend to zero. -/
theorem tendsto_coprimeHarmonicMoebius_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Tendsto (coprimeHarmonicMoebius (∏ p ∈ s, p)) atTop (𝓝 0) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    have : coprimeHarmonicMoebius 1 = fun n => finiteHarmonicSum n moebiusReal := by
      funext n
      unfold coprimeHarmonicMoebius finiteHarmonicSum
      simp
    rw [this]
    exact tendsto_finiteHarmonicSum_moebiusReal_zero
  | insert p s hps ih =>
    have hp : p.Prime := hs p (mem_insert_self p s)
    have ih' := ih (fun q hq => hs q (mem_insert_of_mem hq))
    have hpf : ¬ p ∣ ∏ q ∈ s, q := by
      intro h
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
      have hqp : q.Prime := hs q (mem_insert_of_mem hq)
      have := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
      exact hps (this ▸ hq)
    rw [prod_insert hps, mul_comm]
    apply tendsto_zero_of_contraction (coprimeHarmonicMoebius ((∏ q ∈ s, q) * p))
      (coprimeHarmonicMoebius (∏ q ∈ s, q)) hp.two_le _ ih'
    intro n
    rw [coprimeHarmonicMoebius_prime_step hp hpf n]
    ring

/-! ### The gcd-twisted sum and slope inheritance -/

/-- `G_a(n) = Σ_{d≤n} μ(d) gcd(d,a)/d`. -/
def gcdTwistedHarmonicMoebius (a n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / (d : ℝ)

/-- `G_a` decomposes over the divisors of a squarefree `a` into coprime harmonic Möbius sums:
`G_a(n) = Σ_{f∣a} φ(f) μ(f)/f · m_f(⌊n/f⌋)`. -/
theorem gcdTwistedHarmonicMoebius_eq {a : ℕ} (ha : Squarefree a) (n : ℕ) :
    gcdTwistedHarmonicMoebius a n = ∑ f ∈ a.divisors,
      (Nat.totient f : ℝ) * moebiusReal f / (f : ℝ) * coprimeHarmonicMoebius f (n / f) := by
  unfold gcdTwistedHarmonicMoebius
  have hgcd (d : ℕ) : ((Nat.gcd d a : ℕ) : ℝ) =
      ∑ f ∈ a.divisors, if f ∣ d then (Nat.totient f : ℝ) else 0 := by
    have ha0 : a ≠ 0 := ha.ne_zero
    have h := Nat.sum_totient (Nat.gcd d a)
    have hset : (Nat.gcd d a).divisors = a.divisors.filter (fun f => f ∣ d) := by
      ext f
      simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, ha0⟩, h1⟩
      · rintro ⟨⟨h2, -⟩, h1⟩
        exact ⟨⟨h1, h2⟩, Nat.gcd_ne_zero_right ha0⟩
    rw [hset] at h
    rw [← sum_filter, ← h]
    push_cast
    rfl
  simp_rw [hgcd, mul_sum, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro f hf
  have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
  have hfsq : Squarefree f := ha.squarefree_of_dvd (Nat.dvd_of_mem_divisors hf)
  rw [← sum_filter_add_sum_filter_not (Icc 1 n) (fun d => f ∣ d)]
  have hnot : (∑ d ∈ (Icc 1 n).filter (fun d => ¬ f ∣ d),
      moebiusReal d * (if f ∣ d then (Nat.totient f : ℝ) else 0) / (d : ℝ)) = 0 :=
    sum_eq_zero fun d hd => by rw [if_neg (mem_filter.mp hd).2]; simp
  rw [hnot, add_zero, sum_Icc_multiples f n hf0]
  unfold coprimeHarmonicMoebius
  rw [mul_sum]
  apply sum_congr rfl
  intro e he
  have he0 : 0 < e := (mem_Icc.mp he).1
  rw [if_pos (dvd_mul_right f e)]
  by_cases hc : Nat.Coprime e f
  · rw [if_pos hc]
    have hμ : moebiusReal (f * e) = moebiusReal f * moebiusReal e := by
      unfold moebiusReal
      rw [isMultiplicative_moebius.map_mul_of_coprime hc.symm]
      push_cast; ring
    rw [hμ]; push_cast; field_simp
  · rw [if_neg hc]
    have hμ : moebiusReal (f * e) = 0 := by
      apply moebiusReal_eq_zero_of_not_squarefree
      rw [Nat.squarefree_mul_iff]
      exact fun h => hc h.1.symm
    rw [hμ]; simp

/-- The gcd-twisted harmonic Möbius sum tends to zero for every squarefree `a`. -/
theorem tendsto_gcdTwistedHarmonicMoebius {a : ℕ} (ha : Squarefree a) :
    Tendsto (gcdTwistedHarmonicMoebius a) atTop (𝓝 0) := by
  have hfun : gcdTwistedHarmonicMoebius a = fun n => ∑ f ∈ a.divisors,
      (Nat.totient f : ℝ) * moebiusReal f / (f : ℝ) * coprimeHarmonicMoebius f (n / f) :=
    funext (gcdTwistedHarmonicMoebius_eq ha)
  rw [hfun]
  have : (0 : ℝ) = ∑ f ∈ a.divisors, (Nat.totient f : ℝ) * moebiusReal f / (f : ℝ) * 0 := by simp
  rw [this]
  apply tendsto_finsetSum
  intro f hf
  apply Tendsto.const_mul
  have hf0 : f ≠ 0 := (Nat.pos_of_mem_divisors hf).ne'
  have hfsq : Squarefree f := ha.squarefree_of_dvd (Nat.dvd_of_mem_divisors hf)
  have hm := tendsto_coprimeHarmonicMoebius_prod f.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [Nat.prod_primeFactors_of_squarefree hfsq] at hm
  exact hm.comp (Nat.tendsto_div_const_atTop hf0)

/-- **Exact inheritance identity.** For squarefree `a ≥ 1` and a prime `q > a`,
`A(aq) = G_a(aq - 1) + A(a)/q - A(a)`. -/
theorem buchstabSlopeCore_mul_prime {a q : ℕ} (ha1 : 1 ≤ a) (hq : q.Prime) (haq : a < q) :
    buchstabSlopeCore (a * q) =
      gcdTwistedHarmonicMoebius a (a * q - 1) + buchstabSlopeCore a / q - buchstabSlopeCore a := by
  have hq0 : 0 < q := hq.pos
  have hcopqa : Nat.Coprime q a :=
    (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => by have := Nat.le_of_dvd (by omega) h; omega)
  have hdiv : (a * q - 1) / q = a - 1 := by
    apply Nat.div_eq_of_lt_le
    · have : (a - 1) * q + q = a * q := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel ha1]
      omega
    · rw [Nat.sub_add_cancel ha1]
      have : 0 < a * q := Nat.mul_pos (by omega) hq0
      omega
  have hμqe (e : ℕ) (he : e ∈ Icc 1 (a - 1)) : moebiusReal (q * e) = -moebiusReal e := by
    have he0 : 0 < e := (mem_Icc.mp he).1
    have hqe : Nat.Coprime q e :=
      (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => by
        have := Nat.le_of_dvd he0 h; have := (mem_Icc.mp he).2; omega)
    unfold moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime hqe, moebius_apply_prime hq]
    push_cast; ring
  -- multiples of `q`, weight `gcd(·, aq)`: they carry `-A(a)`
  have hm1 : (∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => q ∣ d),
      moebiusReal d * ((Nat.gcd d (a * q) : ℕ) : ℝ) / (d : ℝ)) = -buchstabSlopeCore a := by
    rw [sum_Icc_multiples q _ hq0, hdiv]
    unfold buchstabSlopeCore
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast (mem_Icc.mp he).1
    rw [hμqe e he, show a * q = q * a by ring, Nat.gcd_mul_left]
    push_cast
    field_simp
  -- multiples of `q`, weight `gcd(·, a)`: they carry `-A(a)/q`
  have hm2 : (∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => q ∣ d),
      moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / (d : ℝ)) = -buchstabSlopeCore a / q := by
    rw [sum_Icc_multiples q _ hq0, hdiv]
    unfold buchstabSlopeCore
    calc (∑ e ∈ Icc 1 (a - 1), moebiusReal (q * e) * ((Nat.gcd (q * e) a : ℕ) : ℝ) /
          ((q * e : ℕ) : ℝ)) =
        ∑ e ∈ Icc 1 (a - 1), -(moebiusReal e * ((Nat.gcd e a : ℕ) : ℝ) / (e : ℝ)) / q := by
          apply sum_congr rfl
          intro e he
          have he0 : (0 : ℝ) < e := by exact_mod_cast (mem_Icc.mp he).1
          rw [hμqe e he, Nat.Coprime.gcd_mul_left_cancel e hcopqa]
          push_cast
          field_simp
      _ = _ := by rw [← Finset.sum_div, Finset.sum_neg_distrib]
  -- off the multiples of `q` both weights agree
  have hn : (∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => ¬ q ∣ d),
      moebiusReal d * ((Nat.gcd d (a * q) : ℕ) : ℝ) / (d : ℝ)) =
      ∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => ¬ q ∣ d),
        moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / (d : ℝ) := by
    apply sum_congr rfl
    intro d hd
    have hcop : Nat.Coprime d q :=
      ((Nat.Prime.coprime_iff_not_dvd hq).mpr (mem_filter.mp hd).2).symm
    rw [Nat.gcd_mul_left_right_of_gcd_eq_one hcop]
  have hL : buchstabSlopeCore (a * q) =
      (∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => q ∣ d),
        moebiusReal d * ((Nat.gcd d (a * q) : ℕ) : ℝ) / (d : ℝ)) +
      ∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => ¬ q ∣ d),
        moebiusReal d * ((Nat.gcd d (a * q) : ℕ) : ℝ) / (d : ℝ) := by
    unfold buchstabSlopeCore
    rw [sum_filter_add_sum_filter_not]
  have hG : gcdTwistedHarmonicMoebius a (a * q - 1) =
      (∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => q ∣ d),
        moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / (d : ℝ)) +
      ∑ d ∈ (Icc 1 (a * q - 1)).filter (fun d => ¬ q ∣ d),
        moebiusReal d * ((Nat.gcd d a : ℕ) : ℝ) / (d : ℝ) := by
    unfold gcdTwistedHarmonicMoebius
    rw [sum_filter_add_sum_filter_not]
  rw [hL, hG, hm1, hm2, hn]
  ring

/-- **Slope inheritance identity.** For squarefree `a ≥ 1` and a prime `q > a`,
`λ(aq) = λ(a) - 2 μ(a) (G_a(aq - 1) + A(a)/q)`. -/
theorem buchstabSlope_mul_prime {a q : ℕ} (ha1 : 1 ≤ a) (hq : q.Prime) (haq : a < q) :
    buchstabSlope (a * q) = buchstabSlope a -
      2 * moebiusReal a * (gcdTwistedHarmonicMoebius a (a * q - 1) + buchstabSlopeCore a / q) := by
  have hcopaq : Nat.Coprime a q :=
    ((Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => by
      have := Nat.le_of_dvd (by omega) h; omega)).symm
  have hμ : moebiusReal (a * q) = -moebiusReal a := by
    unfold moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime hcopaq, moebius_apply_prime hq]
    push_cast; ring
  rw [buchstabSlope_eq_core, buchstabSlope_eq_core, buchstabSlopeCore_mul_prime ha1 hq haq, hμ]
  ring

/-- **Slope inheritance.** For every squarefree `a`, the Buchstab slope of `aq` tends to the slope
of `a` as the prime `q` grows: large primes are invisible to horizon steps. -/
theorem tendsto_buchstabSlope_mul_prime {a : ℕ} (ha : Squarefree a) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, q.Prime → |buchstabSlope (a * q) - buchstabSlope a| < ε := by
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha.ne_zero
  have hG := tendsto_gcdTwistedHarmonicMoebius ha
  have hshift : Tendsto (fun q : ℕ => a * q - 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun q hq => by
      have : q ≤ a * q := Nat.le_mul_of_pos_left q (by omega)
      omega⟩
  have hGq := (hG.comp hshift).eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity :
    (0 : ℝ) < ε / 4))
  have hAq : ∀ᶠ q : ℕ in atTop, |buchstabSlopeCore a| / (q : ℝ) < ε / 4 := by
    have h := (tendsto_const_nhds (x := |buchstabSlopeCore a|)).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    exact h.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [hGq, hAq, eventually_gt_atTop a] with q hGq' hAq' haq hq
  simp only [Function.comp, Real.dist_eq, sub_zero] at hGq'
  rw [buchstabSlope_mul_prime ha1 hq haq]
  have hμa : |moebiusReal a| ≤ 1 := by
    unfold moebiusReal; exact_mod_cast abs_moebius_le_one
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  rw [show buchstabSlope a - 2 * moebiusReal a * (gcdTwistedHarmonicMoebius a (a * q - 1) +
      buchstabSlopeCore a / q) - buchstabSlope a = -(2 * moebiusReal a *
      (gcdTwistedHarmonicMoebius a (a * q - 1) + buchstabSlopeCore a / q)) by ring, abs_neg,
    abs_mul, abs_mul]
  have h1 : |gcdTwistedHarmonicMoebius a (a * q - 1) + buchstabSlopeCore a / q| < ε / 2 := by
    calc _ ≤ |gcdTwistedHarmonicMoebius a (a * q - 1)| + |buchstabSlopeCore a / q| :=
          abs_add_le _ _
      _ < ε / 4 + ε / 4 := by
          rw [abs_div, abs_of_pos hq0]
          linarith
      _ = ε / 2 := by ring
  have h2 : |(2 : ℝ)| * |moebiusReal a| ≤ 2 := by
    rw [abs_two]; linarith
  calc |(2 : ℝ)| * |moebiusReal a| * |gcdTwistedHarmonicMoebius a (a * q - 1) +
        buchstabSlopeCore a / q| ≤ 2 * |gcdTwistedHarmonicMoebius a (a * q - 1) +
        buchstabSlopeCore a / q| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    _ < 2 * (ε / 2) := by linarith
    _ = ε := by ring

/-- The slope of the horizon `2` is `-1`: by inheritance, horizons `2q` have slope near `-1`. -/
theorem buchstabSlope_two : buchstabSlope 2 = -1 := by
  have hμ2 : moebiusReal 2 = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime Nat.prime_two]; norm_num
  have hμ1 : moebiusReal 1 = 1 := by unfold moebiusReal; simp
  unfold buchstabSlope
  rw [show (2 : ℕ) - 1 = 1 from rfl, Finset.Icc_self, Finset.sum_singleton, hμ2, hμ1]
  norm_num

/-- **Horizons `2q` lower the energy.** For all large primes `q`, adding the horizon `2q`
strictly lowers the Möbius `L²` prefix energy at every prefix `M ≥ 2q (8q + 1)`. -/
theorem eventually_two_mul_prime_horizon_step_neg :
    ∀ᶠ q : ℕ in atTop, q.Prime → ∀ M : ℕ, 2 * q * (8 * q + 1) ≤ M →
      sieveL2PrefixEnergy (2 * q) M moebiusReal <
        sieveL2PrefixEnergy (2 * q - 1) M moebiusReal := by
  filter_upwards [tendsto_buchstabSlope_mul_prime (a := 2) Nat.prime_two.squarefree (1 / 2)
    (by norm_num),
    eventually_gt_atTop 2] with q hslope hq2 hq M hM
  have hlam := hslope hq
  rw [buchstabSlope_two] at hlam
  have hlam' : buchstabSlope (2 * q) ≤ -1 / 2 := by
    rw [abs_lt] at hlam; linarith
  have hsq : Squarefree (2 * q - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    rw [Nat.squarefree_mul_iff]
    exact ⟨(Nat.coprime_primes Nat.prime_two hq).mpr (by omega), Nat.prime_two.squarefree,
      hq.squarefree⟩
  have h := abs_horizon_step_sub_slope_le hsq M
  rw [Nat.sub_add_cancel (by omega)] at h
  set B : ℕ := M / (2 * q)
  have hB : 8 * q + 1 ≤ B := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
  have hBr : (8 * q + 1 : ℝ) ≤ B := by exact_mod_cast hB
  have hstep := (abs_le.mp h).2
  have hq1 : ((2 * q - 1 : ℕ) : ℝ) = 2 * (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hq1] at hstep
  have hB0 : (0 : ℝ) ≤ B := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlam' hB0]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
