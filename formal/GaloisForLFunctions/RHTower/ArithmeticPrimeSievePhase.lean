import GaloisForLFunctions.RHTower.EulerDeletionRemainderFirstCoefficient
import GaloisForLFunctions.RHTower.ArithmeticMinimumPhaseCompleteness
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Exact arithmetic prime sieving of the ordinary remainder

Finite Möbius sums of the modulus-normalized ordinary remainder equal the absolutely
convergent sums over indices coprime to the sieve modulus. Removing every prime below
a growing cutoff leaves the unit term, with the complete zeta discrepancy retained.

For positive real part and positive imaginary part, the normalized weighted remainder
has first coefficient `-1 / (12 * (conjugate(s) + 1))`. Its imaginary part is negative.
After all exceptional small indices have been removed, each sieve sum lies strictly
below its unit limit in imaginary part, and inserting any new prime strictly increases
that imaginary part. These properties hold without a zero equation.

At a positive-height strip zero, eventual phase nonpositivity is equivalent to the real
part being at most one half. The exact identity, limit, and approach direction do not
supply an independent proof of that sign condition or exclude any off-line zero.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The actual weighted ordinary remainder before the Möbius reconstruction. -/
def normalizedWeightedRemainder (s : ℂ) (n : ℕ) : ℂ :=
  weightedPowerRemainder s n / minimumNormalization s

/-- The normalized weighted remainder has a fixed complex first coefficient. -/
theorem tendsto_normalizedWeightedRemainder_scaled {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun n : ℕ => normalizedWeightedRemainder s n * (((n : ℝ)^(2*s.re+1):ℝ):ℂ))
      atTop (𝓝 (-(star s+1)⁻¹/12)) := by
  have hu : star s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hv : star s+1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have ht := ((tendsto_powerSumRemainder_mul_endpoint (by linarith : -1 < s.re) hs1).star).div_const
    (minimumNormalization s)
  simp only [star_div₀, star_neg, star_ofNat] at ht
  have halg (u : ℂ) (hu : u ≠ 0) (hv : u+1 ≠ 0) :
      (-u/12)/(u*(u+1)) = -(u+1)⁻¹/12 := by field_simp
  have hc : (-star s/12)/minimumNormalization s = -(star s+1)⁻¹/12 := by
    exact halg (star s) hu hv
  rw [hc] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n≠0)
  have he : ((2*s.re+1:ℝ):ℂ) = s+star s+1 := by
    apply Complex.ext <;> simp
    ring
  rw [normalizedWeightedRemainder, weightedPowerRemainder, kernel,
    Complex.ofReal_cpow (by positivity), he]
  push_cast
  have hp : (n : ℂ)^(-s)*(n : ℂ)^(s+star s+1) = (n : ℂ)^(star s+1) := by
    rw [← Complex.cpow_add _ _ hnc]
    congr 1
    ring
  simp only [star_mul, star_nat_cpow, star_add, star_one]
  symm
  calc
    _ = (star (powerSumRemainder s n)*((n : ℂ)^(-s)*(n : ℂ)^(s+star s+1)))/minimumNormalization s := by ring
    _ = _ := by rw [hp]; ring

/-- At positive height every sufficiently late arithmetic summand has negative imaginary part. -/
theorem eventually_normalizedWeightedRemainder_im_neg {s : ℂ}
    (hs : 0 < s.re) (ht : 0 < s.im) :
    ∀ᶠ n : ℕ in atTop, (normalizedWeightedRemainder s n).im < 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  have hnorm : 0 < Complex.normSq (star s+1) := by
    rw [Complex.normSq_apply]
    have he : (star s+1).re = s.re+1 := by simp
    rw [he]
    nlinarith [sq_nonneg (star s+1).im]
  have hc : (-(star s+1)⁻¹/12).im < 0 := by
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.inv_im,
      Complex.add_im, Complex.star_def, Complex.conj_im, Complex.one_im, add_zero, neg_neg]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos ht hnorm)) (by norm_num)
  have hl := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_normalizedWeightedRemainder_scaled hs hs1)
  have he := (tendsto_order.mp hl).2 0 hc
  filter_upwards [he, eventually_ge_atTop 1] with n hn hnp
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < (n : ℝ)^(2*s.re+1) := Real.rpow_pos_of_pos hnpos _
  simp only [Function.comp_apply, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, zero_add] at hn
  by_contra h
  have hmul := mul_nonneg (le_of_not_gt h) hr.le
  linarith

private theorem summable_normalizedWeighted {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun n : ℕ+ => normalizedWeightedRemainder s n) := by
  have hh := (summable_norm_weightedPowerRemainder_pair hs hs1 (m := 1) (by omega)).prod_factor (1:ℕ+)
  have h : Summable (fun n : ℕ+ => weightedPowerRemainder s n) := by
    apply Summable.of_norm
    simpa only [PNat.val_ofNat, Nat.one_mul] using hh
  exact h.div_const _

/-- The full complex remainder sum on indices coprime to an arithmetic modulus. -/
def coprimeRemainder (s : ℂ) (M : ℕ) : ℂ :=
  ∑' n : ℕ+, if M.Coprime (n : ℕ) then normalizedWeightedRemainder s n else 0

private theorem summable_coprimeRemainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (M : ℕ) :
    Summable (fun n : ℕ+ => if M.Coprime (n : ℕ) then normalizedWeightedRemainder s n else 0) := by
  exact ((summable_normalizedWeighted hs hs1).indicator
    {n : ℕ+ | M.Coprime (n : ℕ)}).congr (fun n => by simp [Set.indicator_apply])

private theorem coprime_factorial_forces_large {N M n : ℕ} (hn : 0 < n)
    (hM : N.factorial ∣ M) (hc : M.Coprime n) (hn1 : n ≠ 1) : N < n := by
  by_contra h
  have hd : n ∣ M := (Nat.dvd_factorial hn (by omega)).trans hM
  exact hn1 ((Nat.coprime_self n).mp (Nat.Coprime.of_dvd_left hd hc))

/-- Removing all primes below a growing cutoff leaves exactly the unit term in the limit. -/
theorem tendsto_coprimeRemainder_factorial {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => coprimeRemainder s N.factorial) atTop
      (𝓝 (normalizedWeightedRemainder s 1)) := by
  classical
  let g : ℕ+ → ℂ := fun n => if n = 1 then normalizedWeightedRemainder s n else 0
  have hl : ∀ n : ℕ+, Tendsto
      (fun N : ℕ => if N.factorial.Coprime (n : ℕ) then normalizedWeightedRemainder s n else 0)
      atTop (𝓝 (g n)) := by
    intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n : ℕ)] with N hN
    by_cases hn : n = 1
    · simp [hn, g]
    · have hn1 : (n : ℕ) ≠ 1 := by intro h; apply hn; exact PNat.eq h
      have hc : ¬ N.factorial.Coprime (n : ℕ) := by
        intro hc
        have := coprime_factorial_forces_large n.pos (dvd_refl _) hc hn1
        omega
      simp [g, hn, hc]
  have hb : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ+,
      ‖if N.factorial.Coprime (n : ℕ) then normalizedWeightedRemainder s n else 0‖
      ≤ ‖normalizedWeightedRemainder s n‖ := by
    filter_upwards [] with N n
    split_ifs <;> simp
  have h := tendsto_tsum_of_dominated_convergence
    (summable_normalizedWeighted hs hs1).norm hl hb
  simpa only [g, tsum_ite_eq, PNat.val_ofNat, coprimeRemainder] using h

private theorem summable_im {f : ℕ+ → ℂ} (hf : Summable f) :
    Summable (fun n => (f n).im) := Complex.imCLM.summable hf

private theorem coprime_prime_coverage_forces_large {N M n : ℕ} (hn : 0 < n)
    (hM : ∀ p : ℕ, p.Prime → p ≤ N → p ∣ M) (hc : M.Coprime n) (hn1 : n ≠ 1) :
    N < n := by
  by_contra h
  obtain ⟨p,hp,hpn⟩ := Nat.exists_prime_and_dvd hn1
  have hpN : p ≤ N := (Nat.le_of_dvd hn hpn).trans (by omega)
  have hc' := Nat.Coprime.of_dvd_left (hM p hp hpN) (Nat.Coprime.of_dvd_right hpn hc)
  exact hp.ne_one ((Nat.coprime_self p).mp hc')

/-- After removing the finite exceptional head, every sieve value lies strictly below its
unit-term limit, and deleting any new prime strictly increases its imaginary part. -/
theorem eventually_coprimeRemainder_strict_phase {s : ℂ} (hs : 0 < s.re) (ht : 0 < s.im) :
    ∃ N : ℕ, ∀ M : ℕ, 0 < M → (∀ p : ℕ, p.Prime → p ≤ N → p ∣ M) →
      (coprimeRemainder s M).im < (normalizedWeightedRemainder s 1).im ∧
      ∀ q : ℕ, q.Prime → ¬ q ∣ M →
        (coprimeRemainder s M).im < (coprimeRemainder s (M*q)).im := by
  classical
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_normalizedWeightedRemainder_im_neg hs ht)
  refine ⟨N,fun M hM hNM => ?_⟩
  have hneg : ∀ n : ℕ+, M.Coprime (n : ℕ) → n ≠ 1 →
      (normalizedWeightedRemainder s n).im < 0 := by
    intro n hc hn
    have hn1 : (n : ℕ) ≠ 1 := by intro h; exact hn (PNat.eq h)
    exact hN n (coprime_prime_coverage_forces_large n.pos hNM hc hn1).le
  let f : ℕ+ → ℂ := fun n => if M.Coprime (n : ℕ) then normalizedWeightedRemainder s n else 0
  have hf : Summable f := summable_coprimeRemainder hs hs1 M
  constructor
  · let g : ℕ+ → ℂ := fun n => if n = 1 then normalizedWeightedRemainder s n else 0
    have hg : Summable g := by
      apply summable_of_ne_finset_zero (s := {1})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [g, hn]
    have hle : (fun n => (f n).im) ≤ (fun n => (g n).im) := by
      intro n
      by_cases hn : n = 1
      · simp [f, g, hn]
      · by_cases hc : M.Coprime (n : ℕ)
        · simpa only [f, g, if_pos hc, if_neg hn, Complex.zero_im] using (hneg n hc hn).le
        · simp [f, g, hn, hc]
    obtain ⟨q,hqM,hq⟩ := Nat.exists_infinite_primes (M+1)
    have hqnd : ¬ q ∣ M := by intro h; have := Nat.le_of_dvd hM h; omega
    have hc : M.Coprime q := (hq.coprime_iff_not_dvd.mpr hqnd).symm
    have hq1 : (⟨q,hq.pos⟩ : ℕ+) ≠ 1 := by
      intro h; exact hq.ne_one (congrArg (fun n : ℕ+ => (n : ℕ)) h)
    have hlt : (f ⟨q,hq.pos⟩).im < (g ⟨q,hq.pos⟩).im := by
      change (if M.Coprime q then normalizedWeightedRemainder s q else 0).im <
        (if (⟨q,hq.pos⟩ : ℕ+) = 1 then normalizedWeightedRemainder s q else 0).im
      rw [if_pos hc, if_neg hq1]
      exact hneg ⟨q,hq.pos⟩ hc hq1
    have hh := Summable.tsum_lt_tsum hle hlt (summable_im hf) (summable_im hg)
    rw [← Complex.im_tsum hf, ← Complex.im_tsum hg] at hh
    simpa only [f, g, tsum_ite_eq, PNat.val_ofNat, coprimeRemainder] using hh
  · intro q hq hqnd
    let g : ℕ+ → ℂ := fun n =>
      if (M*q).Coprime (n : ℕ) then normalizedWeightedRemainder s n else 0
    have hg : Summable g := summable_coprimeRemainder hs hs1 (M*q)
    have hle : (fun n => (f n).im) ≤ (fun n => (g n).im) := by
      intro n
      by_cases hc : M.Coprime (n : ℕ)
      · by_cases hd : q.Coprime (n : ℕ)
        · dsimp only [f, g]
          rw [if_pos hc, if_pos (Nat.coprime_mul_iff_left.mpr ⟨hc,hd⟩)]
        · have hn : n ≠ 1 := by intro h; subst n; simp at hd
          dsimp only [f, g]
          rw [if_pos hc, if_neg (fun h => hd (Nat.coprime_mul_iff_left.mp h).2)]
          exact (hneg n hc hn).le
      · simp [f, g, Nat.coprime_mul_iff_left, hc]
    have hc : M.Coprime q := (hq.coprime_iff_not_dvd.mpr hqnd).symm
    have hd : ¬ q.Coprime q := by simpa only [Nat.coprime_self] using hq.ne_one
    have hq1 : (⟨q,hq.pos⟩ : ℕ+) ≠ 1 := by
      intro h; exact hq.ne_one (congrArg (fun n : ℕ+ => (n : ℕ)) h)
    have hlt : (f ⟨q,hq.pos⟩).im < (g ⟨q,hq.pos⟩).im := by
      change (if M.Coprime q then normalizedWeightedRemainder s q else 0).im <
        (if (M*q).Coprime q then normalizedWeightedRemainder s q else 0).im
      rw [if_pos hc, if_neg (fun h => hd (Nat.coprime_mul_iff_left.mp h).2)]
      exact hneg ⟨q,hq.pos⟩ hc hq1
    have hh := Summable.tsum_lt_tsum hle hlt (summable_im hf) (summable_im hg)
    rw [← Complex.im_tsum hf, ← Complex.im_tsum hg] at hh
    exact hh

private theorem tsum_pnat_dvd_eq_multiples (f : ℕ → ℂ) {d : ℕ} (hd : 0 < d) :
    (∑' n : ℕ+, if d ∣ (n : ℕ) then f n else 0) = ∑' k : ℕ+, f (d*(k : ℕ)) := by
  classical
  let j : ℕ+ → ℕ+ := fun k => ⟨d*(k : ℕ),Nat.mul_pos hd k.pos⟩
  have hj : Function.Injective j := by
    intro a b hab
    apply PNat.eq
    exact mul_left_cancel₀ hd.ne' (congrArg (fun n : ℕ+ => (n : ℕ)) hab)
  have hsupp : Function.support (fun n : ℕ+ => if d ∣ (n : ℕ) then f n else 0) ⊆
      Set.range j := by
    intro n hn
    by_cases hdv : d ∣ (n : ℕ)
    · obtain ⟨k,hk⟩ := hdv
      have hkpos : 0 < k := by
        by_contra h
        have hk0 : k=0 := by omega
        rw [hk0, Nat.mul_zero] at hk
        have := n.pos
        omega
      exact ⟨⟨k,hkpos⟩,PNat.eq hk.symm⟩
    · simp [Function.mem_support, hdv] at hn
  rw [← hj.tsum_eq hsupp]
  apply tsum_congr
  intro k
  change (if d ∣ d*(k : ℕ) then f (d*(k : ℕ)) else 0) = _
  rw [if_pos (dvd_mul_right d (k : ℕ))]

private theorem divisors_filter_dvd {M : ℕ} (hM : M ≠ 0) (n : ℕ) :
    M.divisors.filter (fun d => d ∣ n) = (Nat.gcd M n).divisors := by
  classical
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨hdM,-⟩,hdn⟩
    exact ⟨⟨hdM,hdn⟩,fun h => hM (Nat.eq_zero_of_gcd_eq_zero_left h)⟩
  · rintro ⟨⟨hdM,hdn⟩,-⟩
    exact ⟨⟨hdM,hM⟩,hdn⟩

private theorem moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℂ)) = if n= 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  exact hc

/-- Finite Möbius deletion over the divisors of a modulus equals the full complex sum over
indices coprime to that modulus. Every interchange is justified by absolute convergence. -/
theorem coprimeRemainder_eq_sum_divisors {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {M : ℕ} (hM : M ≠ 0) :
    coprimeRemainder s M = ∑ d ∈ M.divisors, minimumBalanceTerm s d := by
  classical
  let f : ℕ → ℂ := normalizedWeightedRemainder s
  have hf : Summable (fun n : ℕ+ => f n) := summable_normalizedWeighted hs hs1
  have hind : ∀ d : ℕ, Summable (fun n : ℕ+ => if d ∣ (n : ℕ) then f n else 0) := by
    intro d
    exact (hf.indicator {n : ℕ+ | d ∣ (n : ℕ)}).congr (fun n => by simp [Set.indicator_apply])
  have hterm : ∀ d ∈ M.divisors, minimumBalanceTerm s d =
      ∑' n : ℕ+, (μ d : ℂ)*(if d ∣ (n : ℕ) then f n else 0) := by
    intro d hd
    rw [tsum_mul_left, tsum_pnat_dvd_eq_multiples f (Nat.pos_of_mem_divisors hd)]
    simp only [f, normalizedWeightedRemainder, tsum_div_const, minimumBalanceTerm]
    rw [← infiniteRemainder_div_eq_multiples s (Nat.pos_of_mem_divisors hd)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum
    (fun d _ => (hind d).mul_left (μ d : ℂ))]
  apply tsum_congr
  intro n
  simp only [mul_ite, mul_zero, ← Finset.sum_filter]
  rw [divisors_filter_dvd hM, ← Finset.sum_mul, moebius_divisor_sum]
  by_cases hc : M.Coprime (n : ℕ)
  · rw [if_pos hc, if_pos hc, one_mul]
  · rw [if_neg hc, if_neg hc, zero_mul]

private theorem normalizedWeightedRemainder_one_eq_tsum {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    normalizedWeightedRemainder s 1 = ∑' p : ℕ+, minimumBalanceTerm s p := by
  have h := infiniteRemainder_moebius_inversion hs hs1 (m := 1) (by omega)
  simp only [Nat.one_mul] at h
  simp only [minimumBalanceTerm, tsum_div_const, normalizedWeightedRemainder]
  rw [h]

/-- The surviving unit term retains the full zeta discrepancy, not just its real part. -/
theorem normalizedWeightedRemainder_one_eq_boundary {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    normalizedWeightedRemainder s 1 = minimumZeroBoundary s -
      star (riemannZeta s / (s*(s+1))) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  rw [normalizedWeightedRemainder_one_eq_tsum hs hs1, tsum_minimumBalanceTerm_eq hs hs']

/-- Eventual nonpositivity of the sieve phases is exactly nonpositivity of their unit limit. -/
theorem eventually_coprimeRemainder_im_nonpos_iff {s : ℂ} (hs : 0 < s.re) (ht : 0 < s.im) :
    (∀ᶠ N : ℕ in atTop, (coprimeRemainder s N.factorial).im ≤ 0) ↔
      (normalizedWeightedRemainder s 1).im ≤ 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  constructor
  · intro h
    exact le_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_coprimeRemainder_factorial hs hs1)) h
  · intro h
    obtain ⟨N,hN⟩ := eventually_coprimeRemainder_strict_phase hs ht
    filter_upwards [eventually_ge_atTop N] with K hK
    have hc : ∀ p : ℕ, p.Prime → p ≤ N → p ∣ K.factorial := by
      intro p hp hpN
      exact Nat.dvd_factorial hp.pos (hpN.trans hK)
    exact ((hN K.factorial K.factorial_pos hc).1.le.trans h)

/-- At a positive-height strip zero, eventual phase nonpositivity is equivalent to lying in
 the closed left half of the strip. This equivalence supplies no independent sign law. -/
theorem eventually_coprimeRemainder_im_nonpos_at_zero_iff {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (ht : 0 < s.im) (hz : riemannZeta s = 0) :
    (∀ᶠ N : ℕ in atTop, (coprimeRemainder s N.factorial).im ≤ 0) ↔ s.re ≤ 1/2 := by
  rw [eventually_coprimeRemainder_im_nonpos_iff hs ht,
    normalizedWeightedRemainder_one_eq_boundary hs hs', hz]
  simp only [zero_div, star_zero, sub_zero]
  rw [minimumZeroBoundary_im]
  have ha : star s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hb : 1-star s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hd : 0 < 2*Complex.normSq (star s*(1-star s)) :=
    mul_pos (by norm_num) (Complex.normSq_pos.mpr (mul_ne_zero ha hb))
  rw [div_le_iff₀ hd]
  simp only [zero_mul]
  constructor
  · intro h
    by_contra he
    have hp := mul_pos ht (by linarith : 0<2*s.re-1)
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos ht.le (by linarith)

end RHTower.DeletionMixedRefinement
