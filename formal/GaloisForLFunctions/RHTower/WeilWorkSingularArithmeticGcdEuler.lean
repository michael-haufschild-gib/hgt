import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPrimeDeletion
import GaloisForLFunctions.RHTower.WeilConeNotchBochnerLaw

/-!
# Exact gcd-harmonic Euler coefficients

The finite-prime restriction has an absolutely convergent harmonic series,
computed by the finite Euler product. Weighting a multiplicative profile by
its bounded finite gcd factor preserves multiplicativity and leaves its rough
restriction unchanged. Endpoint convolution therefore computes every ordinary
gcd-weighted harmonic limit. The final theorem uses the literal notch
`gcdHarmonicSum` and retains the subtraction of the unit coefficient.
-/

open ArithmeticFunction RHTower.Sieve Filter Topology

noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem prime_dvd_primeProd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} (hq : q.Prime) : q ∣ ∏ p ∈ P, p ↔ q ∈ P := by
  classical
  constructor
  · intro hd
    by_contra hqP
    have hc : Nat.Coprime q (∏ p ∈ P, p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hq (hP p hp)).2 (fun he => hqP (he.symm ▸ hp))
    exact (hq.coprime_iff_not_dvd.mp hc) hd
  · intro hqP
    exact Finset.dvd_prod_of_mem _ hqP

private theorem smoothRestriction_indicator_harmonic (f : ArithmeticFunction ℂ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (Nat.factoredNumbers P).indicator (fun n : ℕ => f n / (n : ℂ)) =
      fun n : ℕ => smoothRestriction (∏ p ∈ P, p) f n / (n : ℂ) := by
  classical
  funext n
  have he : n ∈ Nat.factoredNumbers P ↔ primeSupportedOn (∏ p ∈ P, p) n := by
    rw [Nat.mem_factoredNumbers']
    unfold primeSupportedOn
    exact forall_congr' fun p => forall_congr' fun hp =>
      forall_congr' fun _ => (prime_dvd_primeProd_iff P hP hp).symm
  by_cases hn : n ∈ Nat.factoredNumbers P
  · rw [Set.indicator_of_mem hn]
    change _ = (if primeSupportedOn (∏ p ∈ P, p) n then f n else 0) / (n : ℂ)
    rw [if_pos (he.mp hn)]
  · rw [Set.indicator_of_notMem hn]
    change _ = (if primeSupportedOn (∏ p ∈ P, p) n then f n else 0) / (n : ℂ)
    rw [if_neg (fun hs => hn (he.mpr hs)), zero_div]

theorem smoothRestriction_harmonic_euler {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative)
    (hs : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => ‖f (p ^ k) / ((p ^ k : ℕ) : ℂ)‖))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Summable (fun n : ℕ => ‖smoothRestriction (∏ p ∈ P, p) f n / (n : ℂ)‖) ∧
      HasSum (fun n : ℕ => smoothRestriction (∏ p ∈ P, p) f n / (n : ℂ))
        (∏ p ∈ P, ∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ)) := by
  classical
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => f n / (n : ℂ)) (by simp [hf.map_one])
    (fun {m n} hmn => by rw [hf.map_mul_of_coprime hmn, Nat.cast_mul, div_mul_div_comm])
    (fun {p} hp => hs p hp) P
  have hfilter : P.filter Nat.Prime = P := Finset.filter_eq_self.mpr hP
  rw [hfilter] at he
  constructor
  · have hn := (summable_subtype_iff_indicator (s := Nat.factoredNumbers P)
      (f := fun n : ℕ => ‖f n / (n : ℂ)‖)).mp he.1
    refine hn.congr fun n => ?_
    have hh := congrFun (smoothRestriction_indicator_harmonic f P hP) n
    by_cases hmem : n ∈ Nat.factoredNumbers P
    · simpa only [Set.indicator_of_mem hmem] using congrArg norm hh
    · simpa only [Set.indicator_of_notMem hmem, norm_zero] using congrArg norm hh
  · have hh := (hasSum_subtype_iff_indicator (s := Nat.factoredNumbers P)
      (f := fun n : ℕ => f n / (n : ℂ))).mp he.2
    rwa [smoothRestriction_indicator_harmonic f P hP] at hh

theorem gcdPart_mul_of_coprime (P : Finset ℕ) (h : P → ℕ)
    {m n : ℕ} (hmn : Nat.Coprime m n) :
    WeilAbscissa.gcdPart P (m * n) h = WeilAbscissa.gcdPart P m h * WeilAbscissa.gcdPart P n h := by
  unfold WeilAbscissa.gcdPart
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [Nat.factorization_mul_apply_of_coprime hmn]
  have hor : m.factorization p = 0 ∨ n.factorization p = 0 := by
    simp only [← Nat.primeFactorsList_count_eq]
    by_cases hp : (p : ℕ) ∈ m.primeFactorsList
    · exact Or.inr (List.count_eq_zero.mpr ((Nat.coprime_primeFactorsList_disjoint hmn) hp))
    · exact Or.inl (List.count_eq_zero.mpr hp)
  rcases hor with hm | hn
  · simp [hm]
  · simp [hn]

def gcdWeighted (f : ArithmeticFunction ℂ) (P : Finset ℕ) (h : P → ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n * (WeilAbscissa.gcdPart P n h : ℂ), by simp⟩

theorem gcdWeighted_multiplicative {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (P : Finset ℕ) (h : P → ℕ) : (gcdWeighted f P h).IsMultiplicative := by
  constructor
  · simp [gcdWeighted, hf.map_one, WeilAbscissa.gcdPart]
  · intro m n hmn
    change f (m * n) * (WeilAbscissa.gcdPart P (m * n) h : ℂ) = _
    rw [hf.map_mul_of_coprime hmn, gcdPart_mul_of_coprime P h hmn, Nat.cast_mul]
    change _ = (f m * (WeilAbscissa.gcdPart P m h : ℂ)) *
      (f n * (WeilAbscissa.gcdPart P n h : ℂ))
    ring

theorem gcdPart_prime_pow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h : P → ℕ) (p : P) (k : ℕ) :
    WeilAbscissa.gcdPart P ((p : ℕ) ^ k) h = (p : ℕ) ^ min k (h p) := by
  classical
  unfold WeilAbscissa.gcdPart
  rw [Fintype.prod_eq_single p]
  · rw [(hP p p.2).factorization_pow, Finsupp.single_eq_same]
  · intro q hqp
    have hpq : (p : ℕ) ≠ q := by intro he; exact hqp (Subtype.ext he.symm)
    rw [(hP p p.2).factorization_pow, Finsupp.single_eq_of_ne hpq.symm]
    simp

theorem gcdPart_le_primePowProd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h : P → ℕ) (n : ℕ) :
    WeilAbscissa.gcdPart P n h ≤ ∏ p : P, (p : ℕ) ^ h p := by
  unfold WeilAbscissa.gcdPart
  apply Finset.prod_le_prod'
  intro p _
  exact Nat.pow_le_pow_right (hP p p.2).pos (min_le_right _ _)

theorem roughRestriction_gcdWeighted (f : ArithmeticFunction ℂ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h : P → ℕ) :
    roughRestriction (∏ p ∈ P, p) (gcdWeighted f P h) = roughRestriction (∏ p ∈ P, p) f := by
  classical
  ext n
  change (if Nat.Coprime (∏ p ∈ P, p) n then f n * (WeilAbscissa.gcdPart P n h : ℂ) else 0) =
    if Nat.Coprime (∏ p ∈ P, p) n then f n else 0
  by_cases hc : Nat.Coprime (∏ p ∈ P, p) n
  · have hg : WeilAbscissa.gcdPart P n h = 1 := by
      unfold WeilAbscissa.gcdPart
      apply Finset.prod_eq_one
      intro p _
      have hcp : Nat.Coprime (p : ℕ) n := (Nat.coprime_prod_left_iff.mp hc) p p.2
      rw [Nat.factorization_eq_zero_of_not_dvd ((hP p p.2).coprime_iff_not_dvd.mp hcp)]
      simp
    simp only [if_pos hc, hg, Nat.cast_one, mul_one]
  · simp only [if_neg hc]

theorem gcdWeighted_prime_harmonic_summable {f : ArithmeticFunction ℂ}
    (hs : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => ‖f (p ^ k) / ((p ^ k : ℕ) : ℂ)‖))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h : P → ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖gcdWeighted f P h (p ^ k) / ((p ^ k : ℕ) : ℂ)‖) := by
  let M : ℝ := (∏ q : P, (q : ℕ) ^ h q : ℕ)
  apply ((hs p hp).mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  change ‖(f (p ^ k) * (WeilAbscissa.gcdPart P (p ^ k) h : ℂ)) /
    ((p ^ k : ℕ) : ℂ)‖ ≤ _
  rw [mul_div_right_comm, norm_mul, Complex.norm_natCast]
  have hle : (WeilAbscissa.gcdPart P (p ^ k) h : ℝ) ≤ M := by
    dsimp [M]
    exact_mod_cast gcdPart_le_primePowProd P hP h (p ^ k)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hle (norm_nonneg (f (p ^ k) / ((p ^ k : ℕ) : ℂ)))

/-- Exact gcd-weighted harmonic limit for a strictly bounded multiplicative
profile. The local factors are ordinary absolutely convergent series. -/
theorem tendsto_gcdWeighted_harmonic {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ‖f (p ^ k)‖ ≤ θ)
    {H : ℂ} (hH : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ)) atTop (𝓝 H))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (h : P → ℕ) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, gcdWeighted f P h n / (n : ℂ)) atTop
      (𝓝 ((H / (∏ p ∈ P, ∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ))) *
        (∏ p : P, ∑' k : ℕ, f ((p : ℕ) ^ k) * ((p : ℕ) ^ min k (h p) : ℕ) /
          (((p : ℕ) ^ k : ℕ) : ℂ)))) := by
  have hs (p : ℕ) (hp : p.Prime) :
      Summable (fun k : ℕ => ‖f (p ^ k) / ((p ^ k : ℕ) : ℂ)‖) := by
    have hs := (smoothRestriction_prime_harmonic_summable hp (hb p hp)).comp_injective
      (pow_right_strictMono₀ hp.one_lt).injective
    simpa only [Function.comp_def, smoothRestriction_prime_pow _ hp, dvd_refl, or_true, if_true] using hs
  have hF := gcdWeighted_multiplicative hf P h
  obtain ⟨habs, heuler⟩ := smoothRestriction_harmonic_euler hF
    (fun p hp => gcdWeighted_prime_harmonic_summable hs P hP h hp) P hP
  have hrough := tendsto_roughRestriction_finset hf hθ P hP (fun p hp => hb p (hP p hp)) hH
  rw [← roughRestriction_gcdWeighted f P hP h] at hrough
  have hlim := tendsto_harmonic_mul_of_summable habs hrough
  rw [smoothRestriction_mul_roughRestriction hF, heuler.tsum_eq] at hlim
  have hprod : (∏ p ∈ P, ∑' k : ℕ, gcdWeighted f P h (p ^ k) / ((p ^ k : ℕ) : ℂ)) =
      ∏ p : P, ∑' k : ℕ, f ((p : ℕ) ^ k) * ((p : ℕ) ^ min k (h p) : ℕ) /
        (((p : ℕ) ^ k : ℕ) : ℂ) := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro p _
    apply tsum_congr
    intro k
    change f ((p : ℕ) ^ k) * (WeilAbscissa.gcdPart P ((p : ℕ) ^ k) h : ℂ) / _ = _
    rw [gcdPart_prime_pow P hP h p k]
  rw [hprod, mul_comm] at hlim
  exact hlim

/-- The actual real gcd-harmonic coefficient of the deviation `Re f - delta_1`.
The normalization at one contributes exactly `-1`. -/
theorem tendsto_gcdHarmonicSum_of_multiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ‖f (p ^ k)‖ ≤ θ)
    {H : ℂ} (hH : Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ)) atTop (𝓝 H))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (g : P → ℤ) :
    Tendsto (WeilAbscissa.gcdHarmonicSum P
      (fun n => (f n).re - if n = 1 then 1 else 0) g) atTop
      (𝓝 (((H / (∏ p ∈ P, ∑' k : ℕ, f (p ^ k) / ((p ^ k : ℕ) : ℂ))) *
        (∏ p : P, ∑' k : ℕ, f ((p : ℕ) ^ k) * ((p : ℕ) ^ min k (g p).toNat : ℕ) /
          (((p : ℕ) ^ k : ℕ) : ℂ))).re - 1)) := by
  have ht := ((Complex.continuous_re.tendsto _).comp
    (tendsto_gcdWeighted_harmonic hf hθ hb hH P hP (fun p => (g p).toNat))).sub
    (tendsto_const_nhds (x := (1 : ℝ)))
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  let W : ℕ → ℝ := fun n => (WeilAbscissa.gcdPart P n (fun p => (g p).toNat) : ℝ)
  have hw1 : W 1 = 1 := by simp [W, WeilAbscissa.gcdPart]
  have hz : ((f 0).re - if (0 : ℕ) = 1 then 1 else 0) * W 0 / ((0 : ℕ) : ℝ) = 0 := by simp
  have herase : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hterm (n : ℕ) : (gcdWeighted f P (fun p => (g p).toNat) n / (n : ℂ)).re =
      (f n).re * W n / (n : ℝ) := by
    simp [gcdWeighted, W, Complex.mul_re]
  have hdelta : (∑ n ∈ Finset.Icc 1 N, (if n = 1 then (1 : ℝ) else 0) * W n / (n : ℝ)) = 1 := by
    have he (n : ℕ) : (if n = 1 then (1 : ℝ) else 0) * W n / (n : ℝ) =
        if n = 1 then 1 else 0 := by
      split_ifs with hn
      · subst n; simp [hw1]
      · simp
    simp only [he]
    simp [hN]
  change (∑ n ∈ Finset.Icc 1 N, gcdWeighted f P (fun p => (g p).toNat) n / (n : ℂ)).re - 1 =
    ∑ n ∈ Finset.range (N + 1), ((f n).re - if n = 1 then 1 else 0) * W n / (n : ℝ)
  rw [← Finset.sum_erase (Finset.range (N + 1)) hz, herase]
  simp only [sub_mul, sub_div, Finset.sum_sub_distrib, Complex.re_sum, hterm, hdelta]

end RHTower.WeilSingularArithmetic
