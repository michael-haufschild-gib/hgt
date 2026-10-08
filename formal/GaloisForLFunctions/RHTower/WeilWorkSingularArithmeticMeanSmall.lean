import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSourceEuler
import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Strict multiplicative profiles are notch-small

Finite prime attenuation majorizes the absolute coefficients. Counting
multiples computes its Cesaro mean exactly; divergence of prime reciprocals
makes these means tend to zero. Sublinear absolute sums then control every
far logarithmic window, which proves NotchSmall. The final theorem joins
this arithmetic result to the actual source Euler density: no separate
smallness or harmonic convergence assumption remains.
-/

open ArithmeticFunction Complex Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.WeilSingularArithmetic

def primeAttenuation (θ : ℝ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ P, if p ∣ n then θ else 1

theorem primeAttenuation_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (P : Finset ℕ) (n : ℕ) :
    0 ≤ primeAttenuation θ P n := by
  apply Finset.prod_nonneg
  intro p hp
  split_ifs <;> positivity

theorem abs_le_primeAttenuation {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    |f n| ≤ primeAttenuation θ P n := by
  classical
  by_cases hn : n = 0
  · subst n
    simpa using primeAttenuation_nonneg hθ0 P 0
  have hfprod : |f n| = ∏ p ∈ n.primeFactors, |f (p ^ n.factorization p)| := by
    rw [hf.multiplicative_factorization f hn]
    simp only [Finsupp.prod, Nat.support_factorization, Finset.abs_prod]
  have hsub : P.filter (fun p => p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hP p hm.1, hm.2, hn⟩
  calc
    |f n| ≤ ∏ p ∈ n.primeFactors, θ := by
      rw [hfprod]
      apply Finset.prod_le_prod (fun p _ => abs_nonneg _)
      intro p hp
      obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
      exact hb p hpp (n.factorization p) (hpp.factorization_pos_of_dvd hn hpd)
    _ ≤ ∏ p ∈ P.filter (fun p => p ∣ n), θ :=
      Finset.prod_le_prod_of_subset_of_le_one hsub (fun _ _ => hθ0) (fun _ _ _ => hθ1)
    _ = primeAttenuation θ P n := by
      exact Finset.prod_filter (fun p => p ∣ n) (fun _ => θ)

private theorem primeProd_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hpp := hP p (Finset.mem_insert_self p P)
    have hPs : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hpp (hPs q hq)).2 (by intro he; subst q; exact hp hq)
    rw [Finset.prod_insert hp, Finset.forall_mem_insert]
    constructor
    · intro hd
      exact ⟨(show p ∣ p * ∏ q ∈ P, q from ⟨_, rfl⟩).trans hd,
        (ih hPs).1 ((show (∏ q ∈ P, q) ∣ p * ∏ q ∈ P, q from ⟨p, mul_comm _ _⟩).trans hd)⟩
    · rintro ⟨hpn, hPn⟩
      exact hcop.mul_dvd_of_dvd_of_dvd hpn ((ih hPs).2 hPn)

private theorem primeAttenuation_expansion (θ : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    primeAttenuation θ P n = ∑ S ∈ P.powerset,
      if (∏ p ∈ S, p) ∣ n then (θ - 1) ^ S.card else 0 := by
  classical
  have he (p : ℕ) : (if p ∣ n then θ else 1) = 1 + (if p ∣ n then θ - 1 else 0) := by
    split_ifs <;> ring
  simp only [primeAttenuation, he, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S hS
  have hSP := Finset.mem_powerset.mp hS
  have hSPprime : ∀ p ∈ S, p.Prime := fun p hp => hP p (hSP hp)
  by_cases hd : ∀ p ∈ S, p ∣ n
  · rw [if_pos ((primeProd_dvd_iff S hSPprime n).2 hd)]
    simp only [Finset.prod_congr rfl (fun p hp => if_pos (hd p hp)), Finset.prod_const]
  · rw [if_neg (fun h => hd ((primeProd_dvd_iff S hSPprime n).1 h))]
    push Not at hd
    obtain ⟨p, hp, hpn⟩ := hd
    exact Finset.prod_eq_zero hp (if_neg hpn)

private theorem sum_multiples_const (d : ℕ) (hd : 0 < d) (N : ℕ) (c : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, if d ∣ n then c else 0) = c * ((N / d : ℕ) : ℝ) := by
  classical
  rw [← Finset.sum_filter, multiples_Icc hd N]
  rw [Finset.sum_const, Finset.card_image_of_injective _ (fun a b h => Nat.mul_left_cancel hd h)]
  simp [Nat.card_Icc, nsmul_eq_mul, mul_comm]

theorem primeAttenuation_sum (θ : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, primeAttenuation θ P n) =
      ∑ S ∈ P.powerset, (θ - 1) ^ S.card * ((N / (∏ p ∈ S, p) : ℕ) : ℝ) := by
  simp_rw [primeAttenuation_expansion θ P hP]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  exact sum_multiples_const _ (Finset.prod_pos (fun p hp =>
    (hP p ((Finset.mem_powerset.mp hS) hp)).pos)) N _


def primeAttenuationMean (θ : ℝ) (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + (θ - 1) / (p : ℝ))

theorem tendsto_primeAttenuation_mean (θ : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, primeAttenuation θ P n) / (N : ℝ))
      atTop (𝓝 (primeAttenuationMean θ P)) := by
  have ht := tendsto_finsetSum P.powerset (fun S hS =>
    (tendsto_natDiv_div_self (Finset.prod_pos (fun p hp =>
      (hP p ((Finset.mem_powerset.mp hS) hp)).pos))).const_mul ((θ - 1) ^ S.card))
  have hm : primeAttenuationMean θ P =
      ∑ S ∈ P.powerset, (θ - 1) ^ S.card * (1 / ((∏ p ∈ S, p) : ℕ)) := by
    rw [primeAttenuationMean, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro S _
    rw [Finset.prod_div_distrib, Finset.prod_const, ← Nat.cast_prod]
    ring
  rw [hm]
  convert ht using 1
  ext N
  rw [primeAttenuation_sum θ P hP N]
  simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem primeAttenuationMean_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : 0 ≤ primeAttenuationMean θ P := by
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have he : 1 + (θ - 1) / (p : ℝ) = ((p : ℝ) + θ - 1) / p := by
    field_simp
    ring
  rw [he]
  exact div_nonneg (by linarith) hp0.le

/-- Any fixed strict prime-power attenuation has vanishing finite-prime mean. -/
theorem tendsto_primeAttenuationMean_prefix {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (e : ℕ ≃ Nat.Primes) :
    Tendsto (fun N => primeAttenuationMean θ ((Finset.range N).image (fun j => (e j : ℕ))))
      atTop (𝓝 0) := by
  have hnonneg : ∀ n : ℕ, (0 : ℝ) ≤ ((e n : ℕ) : ℝ)⁻¹ := fun n => by positivity
  have hnotsummable : ¬ Summable fun n : ℕ => ((e n : ℕ) : ℝ)⁻¹ := by
    intro hsum
    refine Nat.Primes.not_summable_one_div ?_
    have hre := (e.summable_iff (f := fun p : Nat.Primes => ((p : ℕ) : ℝ)⁻¹)).mp hsum
    simpa [one_div] using hre
  have hdiv : Tendsto
      (fun N => ∑ n ∈ Finset.range N, ((e n : ℕ) : ℝ)⁻¹) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hnotsummable
  have hexp : Tendsto
      (fun N => Real.exp (-((1 - θ) * ∑ n ∈ Finset.range N, ((e n : ℕ) : ℝ)⁻¹)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hdiv.const_mul_atTop (sub_pos.mpr hθ1))
  have hinj : Function.Injective (fun j => (e j : ℕ)) :=
    Subtype.val_injective.comp e.injective
  have hprime (N : ℕ) : ∀ p ∈ (Finset.range N).image (fun j => (e j : ℕ)), p.Prime := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact (e j).property
  refine squeeze_zero (fun N => primeAttenuationMean_nonneg hθ0 _ (hprime N)) (fun N => ?_) hexp
  rw [primeAttenuationMean, Finset.prod_image (fun a _ b _ hab => hinj hab)]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro n _
    have hp1 := one_lt_prime_cast (e n)
    have hp0 : (0 : ℝ) < (e n : ℕ) := by linarith
    have he : 1 + (θ - 1) / ((e n : ℕ) : ℝ) =
        (((e n : ℕ) : ℝ) + θ - 1) / ((e n : ℕ) : ℝ) := by field_simp; ring
    rw [he]
    exact div_nonneg (by linarith) hp0.le
  · intro n _
    have h := Real.add_one_le_exp (-((1 - θ) * ((e n : ℕ) : ℝ)⁻¹))
    have he : 1 + (θ - 1) / ((e n : ℕ) : ℝ) =
        -((1 - θ) * ((e n : ℕ) : ℝ)⁻¹) + 1 := by ring
    rw [he]
    exact h

/-- A uniform strict bound on every prime power forces absolute Cesaro mean zero. -/
theorem tendsto_absolute_mean_of_prime_power_bound {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, |f n|) / (N : ℝ)) atTop (𝓝 0) := by
  classical
  letI : Encodable Nat.Primes := Encodable.ofCountable _
  letI : Denumerable Nat.Primes := Denumerable.ofEncodableOfInfinite Nat.Primes
  let e : ℕ ≃ Nat.Primes := (Denumerable.eqv Nat.Primes).symm
  have hmean := tendsto_primeAttenuationMean_prefix hθ0 hθ1 e
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hmean (ε / 2) (half_pos hε)
  let P := (Finset.range M).image (fun j => (e j : ℕ))
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact (e j).property
  have hsmall : primeAttenuationMean θ P < ε / 2 := by
    have h := hM M le_rfl
    simp only [Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans_lt h
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (tendsto_primeAttenuation_mean θ P hP)
    (ε / 2) (half_pos hε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hupper := hN₀ N hN
  simp only [Real.dist_eq] at hupper
  have hle : (∑ n ∈ Finset.Icc 1 N, |f n|) / (N : ℝ) ≤
      (∑ n ∈ Finset.Icc 1 N, primeAttenuation θ P n) / (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    exact Finset.sum_le_sum fun n _ => abs_le_primeAttenuation hf hθ0 hθ1.le hb P hP n
  have hnonneg : 0 ≤ (∑ n ∈ Finset.Icc 1 N, |f n|) / (N : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith [(abs_lt.mp hupper).2]

/-- Sublinear absolute sums control every far logarithmic window uniformly. -/
theorem localMassTendsZero_of_absolute_mean {d : ℕ → ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, |d n|) / (N : ℝ))
      atTop (𝓝 0)) : WeilAbscissa.LocalMassTendsZero d := by
  classical
  intro η hη
  let δ : ℝ := η / Real.exp 1
  have hδ : 0 < δ := div_pos hη (Real.exp_pos 1)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hmean δ hδ
  let N₀ : ℕ := max M 1
  refine ⟨max 1 (Real.log ((N₀ : ℝ) + 1)), fun Z hZ N₁ => ?_⟩
  have hZ1 : 1 ≤ Z := (le_max_left _ _).trans hZ
  have hZlog : Real.log ((N₀ : ℝ) + 1) ≤ Z := (le_max_right _ _).trans hZ
  let K : ℕ := ⌊Real.exp (Z + 1 / 2)⌋₊
  let c : ℝ := Real.exp (-(Z - 1 / 2))
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hN₀K : N₀ ≤ K := by
    apply Nat.le_floor
    have hN₀pos : 0 < (N₀ : ℝ) + 1 := by positivity
    have h := Real.exp_le_exp.mpr (show Real.log ((N₀ : ℝ) + 1) ≤ Z + 1 / 2 by linarith)
    rw [Real.exp_log hN₀pos] at h
    linarith
  have hK1 : 1 ≤ K := (le_max_right M 1).trans hN₀K
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hsum : (∑ n ∈ Finset.Icc 1 K, |d n|) ≤ δ * K := by
    have h := hM K ((le_max_left M 1).trans hN₀K)
    simp only [Real.dist_eq, sub_zero] at h
    have hle := (le_abs_self _).trans h.le
    exact (div_le_iff₀ hK0).mp hle
  have hpt (n : ℕ) : |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤
      if n ∈ Finset.Icc 1 K then c * |d n| else 0 := by
    by_cases hn : n = 0
    · subst n
      simp
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    by_cases hw : |Real.log n - Z| ≤ 1 / 2
    · have hu : Real.log n ≤ Z + 1 / 2 := by linarith [(abs_le.mp hw).2]
      have hl : Z - 1 / 2 ≤ Real.log n := by linarith [(abs_le.mp hw).1]
      have hnK : n ≤ K := by
        apply Nat.le_floor
        simpa only [Real.exp_log hn0] using Real.exp_le_exp.mpr hu
      have hinv : (n : ℝ)⁻¹ ≤ c := by
        change (n : ℝ)⁻¹ ≤ Real.exp (-(Z - 1 / 2))
        rw [Real.exp_neg]
        apply inv_anti₀ (Real.exp_pos _)
        simpa only [Real.exp_log hn0] using Real.exp_le_exp.mpr hl
      rw [if_pos hw, mul_one, if_pos (Finset.mem_Icc.mpr ⟨hn1, hnK⟩), div_eq_mul_inv]
      exact (mul_le_mul_of_nonneg_left hinv (abs_nonneg _)).trans_eq (mul_comm _ _)
    · rw [if_neg hw, mul_zero]
      split_ifs <;> positivity
  calc
    _ ≤ ∑ n ∈ Finset.range N₁, if n ∈ Finset.Icc 1 K then c * |d n| else 0 :=
      Finset.sum_le_sum (fun n _ => hpt n)
    _ = ∑ n ∈ (Finset.range N₁).filter (fun n => n ∈ Finset.Icc 1 K), c * |d n| :=
      (Finset.sum_filter _ _).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 K, c * |d n| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => (Finset.mem_filter.mp hn).2) (fun n _ _ => mul_nonneg hc (abs_nonneg _))
    _ = c * ∑ n ∈ Finset.Icc 1 K, |d n| := (Finset.mul_sum _ _ _).symm
    _ ≤ c * (δ * K) := mul_le_mul_of_nonneg_left hsum hc
    _ ≤ c * (δ * Real.exp (Z + 1 / 2)) := by
      gcongr
      exact Nat.floor_le (Real.exp_pos _).le
    _ = η := by
      have he : c * Real.exp (Z + 1 / 2) = Real.exp 1 := by
        change Real.exp (-(Z - 1 / 2)) * Real.exp (Z + 1 / 2) = Real.exp 1
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        c * (δ * Real.exp (Z + 1 / 2)) = δ * (c * Real.exp (Z + 1 / 2)) := by ring
        _ = η := by
          rw [he]
          exact div_mul_cancel₀ _ (Real.exp_ne_zero _)

theorem notchSmall_of_multiplicative_prime_power_bound {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ1 : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ) :
    PrimeSmallDeviation.NotchSmall (fun n => f n - if n = 1 then 1 else 0) := by
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (hb 2 Nat.prime_two 1 le_rfl)
  have hmean := tendsto_absolute_mean_of_prime_power_bound hf hθ0 hθ1 hb
  have hdmean : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, |f n - if n = 1 then 1 else 0|) / (N : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun N => by positivity) (fun N => ?_) hmean
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply Finset.sum_le_sum
    intro n _
    by_cases hn : n = 1
    · simp [hn, hf.map_one]
    · simp [hn]
  exact WeilAbscissa.notchSmall_of_localMassTendsZero (by simp) (by simp [hf.map_one])
    (localMassTendsZero_of_absolute_mean hdmean)


/-- The strict prime-power profile pays every smallness and ordinary convergence
input of the finite Euler inequality. Positivity of `H` is a separate theorem. -/
theorem exists_finiteEuler_bound_of_strict_multiplicative_source {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    ∃ H : ℝ,
      Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H) ∧ H ≤ 1 ∧
      ∀ (P : Finset ℕ) (_ : ∀ p ∈ P, p.Prime) (x : UnitAddTorus P),
        (H / ∏ p ∈ P, localEulerValue f p) *
          (∏ p : P, boundedFun (fun k => (f ((p : ℕ) ^ k) : ℂ))
            ((primeRadius p : ℂ) * fourier 1 (x p))).re ≤ 1 := by
  have hd : PrimeSmallDeviation.NotchSmall (WeilOneSided.coneDeviation lam) := by
    rw [coneDeviation_eq_of_multiplicative_source hf hs]
    exact notchSmall_of_multiplicative_prime_power_bound hf hθ hb
  obtain ⟨H, hH, hbound⟩ := exists_finiteEuler_bound_of_multiplicative_source hf hθ hb hW hs hd
  have hHle : H ≤ 1 := by
    have h := hbound ∅ (by simp) 0
    simpa using h
  exact ⟨H, hH, hHle, hbound⟩

end RHTower.WeilSingularArithmetic
