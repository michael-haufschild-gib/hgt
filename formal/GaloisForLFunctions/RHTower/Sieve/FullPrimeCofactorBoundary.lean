import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The logarithmic boundary layer of the literal all-prime Ramaré cofactor

For `a(n) = μ(n)/(1+ω(n))`, with `ω(n)` counting distinct prime factors, the
real Dirichlet series is the integral of the full damped Euler product.
Logarithmic concavity traps it between two elementary Laplace integrals.
The prime-square error is uniformly summable, while the prime reciprocal
mass diverges at one. Consequently `F(σ) * log ‖ζ(σ)‖ → 1` as `σ → 1+`.

`fullPrimeCofactor_eq_ramare` identifies these coefficients with the existing
cutoff-dependent Ramaré coefficients wherever the cutoff admits the integer.
This is an unconditional boundary invariant of that actual cofactor. It does
not bound the complete physical covariance or prove RH. The separate Abel
argument excluding strong partial-sum estimates is not formalized here.
-/

noncomputable section
open Finset Filter Topology MeasureTheory
namespace RHTower.Sieve

/-- Möbius damping by the number of all distinct prime factors. -/
def fullPrimeDampedMoebius (u : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * u ^ n.primeFactors.card

/-- The literal all-prime Ramaré coefficient. -/
def fullPrimeCofactor (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) / (n.primeFactors.card + 1)

/-- The full damped Dirichlet series at a real abscissa. -/
def fullPrimeDampedSeries (u σ : ℝ) : ℝ :=
  ∑' n : ℕ, fullPrimeDampedMoebius u n * (n : ℝ) ^ (-σ)

/-- The Dirichlet series of the literal cofactor. -/
def fullPrimeCofactorSeries (σ : ℝ) : ℝ :=
  ∑' n : ℕ, fullPrimeCofactor n * (n : ℝ) ^ (-σ)

theorem abs_fullPrimeDampedMoebius_le {u : ℝ} (hu : u ∈ Set.Icc 0 1) (n : ℕ) :
    |fullPrimeDampedMoebius u n| ≤ 1 := by
  have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  rw [fullPrimeDampedMoebius, abs_mul, abs_of_nonneg (pow_nonneg hu.1 _)]
  exact mul_le_one₀ hmu (pow_nonneg hu.1 _) (pow_le_one₀ hu.1 hu.2)

theorem fullPrimeDampedMoebius_mul {u : ℝ} {m n : ℕ} (h : m.Coprime n) :
    fullPrimeDampedMoebius u (m*n) = fullPrimeDampedMoebius u m * fullPrimeDampedMoebius u n := by
  by_cases hm : m = 0
  · simp [hm, fullPrimeDampedMoebius]
  by_cases hn : n = 0
  · simp [hn, fullPrimeDampedMoebius]
  simp only [fullPrimeDampedMoebius, Nat.primeFactors_mul hm hn,
    card_union_of_disjoint h.disjoint_primeFactors, pow_add,
    ArithmeticFunction.isMultiplicative_moebius.2 h]
  push_cast
  ring

theorem summable_fullPrimeDampedTerm {u σ : ℝ} (hu : u ∈ Set.Icc 0 1) (hσ : 1 < σ) :
    Summable (fun n : ℕ => fullPrimeDampedMoebius u n * (n : ℝ)^(-σ)) := by
  apply (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_fullPrimeDampedMoebius_le hu n)

theorem hasProd_fullPrimeDampedSeries {u σ : ℝ} (hu : u ∈ Set.Icc 0 1) (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes => 1-u*((p : ℕ) : ℝ)^(-σ)) (fullPrimeDampedSeries u σ) := by
  let f : ℕ → ℝ := fun n => fullPrimeDampedMoebius u n * (n : ℝ)^(-σ)
  have hf1 : f 1 = 1 := by simp [f, fullPrimeDampedMoebius]
  have hf0 : f 0 = 0 := by simp [f, fullPrimeDampedMoebius]
  have hmul {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f, fullPrimeDampedMoebius_mul h, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hlocal (p : Nat.Primes) : (∑' k : ℕ, f ((p : ℕ)^k)) = 1-u*((p : ℕ) : ℝ)^(-σ) := by
    have hz : ∀ k ∉ ({0,1} : Finset ℕ), f ((p : ℕ)^k) = 0 := by
      intro k hk
      have hk0 : k ≠ 0 := by simp only [mem_insert, mem_singleton, not_or] at hk; exact hk.1
      have hk1 : k ≠ 1 := by simp only [mem_insert, mem_singleton, not_or] at hk; exact hk.2
      simp [f, fullPrimeDampedMoebius, ArithmeticFunction.moebius_apply_prime_pow p.2 hk0, hk1]
    rw [tsum_eq_sum hz]
    simp [f, fullPrimeDampedMoebius, ArithmeticFunction.moebius_apply_prime p.2, p.2.primeFactors]
    ring
  have he := EulerProduct.eulerProduct_hasProd hf1 (fun {m n} h => hmul h)
    (summable_fullPrimeDampedTerm hu hσ).norm hf0
  simpa only [hlocal, fullPrimeDampedSeries, f] using he


private theorem damped_factor_log_lower {x u : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hu : u ∈ Set.Icc 0 1) : Real.exp (u * Real.log (1-x)) ≤ 1-u*x := by
  have hy : 0 < 1-u*x := by nlinarith [mul_nonneg (by linarith [hu.2] : 0 ≤ 1-u) hx]
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1-x ∈ Set.Ioi 0 by simp; linarith)
    (show 0 ≤ 1-u by linarith [hu.2]) hu.1 (show 1-u+u=1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at h
  have he : (1-u)*1+u*(1-x)=1-u*x := by ring
  rw [he] at h
  exact (Real.exp_le_exp.mpr h).trans_eq (Real.exp_log hy)

private theorem damped_product_bounds {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ P, 0 ≤ x p ∧ x p < 1) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    Real.exp (u * ∑ p ∈ P, Real.log (1-x p)) ≤ ∏ p ∈ P, (1-u*x p) ∧
      (∏ p ∈ P, (1-u*x p)) ≤ Real.exp (-u * ∑ p ∈ P, x p) := by
  constructor
  · rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun p hp => damped_factor_log_lower (hx p hp).1 (hx p hp).2 hu)
  · rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have ht := hx p hp
      nlinarith [mul_nonneg (by linarith [hu.2] : 0 ≤ 1-u) ht.1]
    · intro p hp
      have := Real.add_one_le_exp (-u*x p)
      linarith

private theorem neg_log_one_sub_bounds {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1/2) :
    0 ≤ -Real.log (1-x) ∧ -Real.log (1-x) ≤ 2*x := by
  have hd : 0 < 1-x := by linarith
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos hd.le (by linarith))
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
    rw [Real.log_inv] at h
    have hfrac : (1-x)⁻¹-1 ≤ 2*x := by
      rw [inv_eq_one_div]
      have hb : 1/(1-x) ≤ 1+2*x := (div_le_iff₀ hd).mpr (by nlinarith)
      linarith
    exact h.trans hfrac

/-- The convergent prime logarithm in the Euler half-plane. -/
def fullPrimeEulerLog (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, -Real.log (1-((p : ℕ) : ℝ)^(-σ))

private theorem prime_rpow_le_half {σ : ℝ} (hσ : 1 < σ) (p : Nat.Primes) :
    ((p : ℕ) : ℝ)^(-σ) ≤ 1/2 := by
  have hp : (2:ℝ) ≤ (p:ℕ) := by exact_mod_cast p.2.two_le
  calc ((p:ℕ):ℝ)^(-σ) ≤ ((p:ℕ):ℝ)^(-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1/((p:ℕ):ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp

private theorem summable_fullPrimeMass {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => ((p:ℕ):ℝ)^(-σ)) :=
  (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).comp_injective Nat.Primes.coe_nat_injective

private theorem summable_fullPrimeEulerLog {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => -Real.log (1-((p:ℕ):ℝ)^(-σ))) := by
  apply ((summable_fullPrimeMass hσ).mul_left 2).of_norm_bounded
  intro p
  have h := neg_log_one_sub_bounds (Real.rpow_nonneg (Nat.cast_nonneg _) _) (prime_rpow_le_half hσ p)
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

theorem fullPrimeDampedSeries_bounds {u σ : ℝ} (hu : u ∈ Set.Icc 0 1) (hσ : 1 < σ) :
    Real.exp (-u * fullPrimeEulerLog σ) ≤ fullPrimeDampedSeries u σ ∧
      fullPrimeDampedSeries u σ ≤ Real.exp (-u * ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)) := by
  have hp := hasProd_fullPrimeDampedSeries hu hσ
  have hlow : Tendsto (fun P : Finset Nat.Primes =>
      Real.exp (u * ∑ p ∈ P, Real.log (1-((p:ℕ):ℝ)^(-σ)))) atTop
      (𝓝 (Real.exp (-u * fullPrimeEulerLog σ))) := by
    have ht := Real.continuous_exp.continuousAt.tendsto.comp
      (((summable_fullPrimeEulerLog hσ).neg.hasSum).const_mul u)
    simpa only [neg_neg, tsum_neg, fullPrimeEulerLog, mul_neg, neg_mul, Function.comp_def, SummationFilter.unconditional] using ht
  have hupp : Tendsto (fun P : Finset Nat.Primes =>
      Real.exp (-u * ∑ p ∈ P, ((p:ℕ):ℝ)^(-σ))) atTop
      (𝓝 (Real.exp (-u * ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp ((summable_fullPrimeMass hσ).hasSum.const_mul (-u))
  have hb (P : Finset Nat.Primes) := damped_product_bounds P
    (fun p : Nat.Primes => ((p:ℕ):ℝ)^(-σ)) (fun p _ =>
      ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, (prime_rpow_le_half hσ p).trans_lt (by norm_num)⟩) hu
  exact ⟨le_of_tendsto_of_tendsto hlow hp (Eventually.of_forall fun P => (hb P).1),
    le_of_tendsto_of_tendsto hp hupp (Eventually.of_forall fun P => (hb P).2)⟩


private theorem continuous_fullPrimeDampedTerm (n : ℕ) (σ : ℝ) :
    Continuous (fun u : ℝ => fullPrimeDampedMoebius u n * (n : ℝ)^(-σ)) := by
  unfold fullPrimeDampedMoebius
  fun_prop

private theorem norm_fullPrimeDampedTerm_le {u σ : ℝ} (hu : u ∈ Set.Icc 0 1) (n : ℕ) :
    ‖fullPrimeDampedMoebius u n * (n : ℝ)^(-σ)‖ ≤ (n : ℝ)^(-σ) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_fullPrimeDampedMoebius_le hu n)

theorem continuousOn_fullPrimeDampedSeries {σ : ℝ} (hσ : 1 < σ) :
    ContinuousOn (fun u => fullPrimeDampedSeries u σ) (Set.Icc 0 1) := by
  apply continuousOn_tsum (fun n => (continuous_fullPrimeDampedTerm n σ).continuousOn)
    (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  intro n u hu
  exact norm_fullPrimeDampedTerm_le hu n

theorem fullPrimeCofactorSeries_eq_integral (σ : ℝ) (hσ : 1 < σ) :
    fullPrimeCofactorSeries σ = ∫ u in (0:ℝ)..1, fullPrimeDampedSeries u σ := by
  let f : ℕ → ℝ → ℝ := fun n u => fullPrimeDampedMoebius u n * (n : ℝ)^(-σ)
  have hf (n : ℕ) : Integrable (f n) (volume.restrict (Set.Ioc 0 1)) :=
    ((continuous_fullPrimeDampedTerm n σ).intervalIntegrable 0 1).1
  have hbn (n : ℕ) : (∫ u in Set.Ioc (0:ℝ) 1, ‖f n u‖) ≤ (n : ℝ)^(-σ) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    calc (∫ u in (0:ℝ)..1, ‖f n u‖) ≤ ∫ _u in (0:ℝ)..1, (n : ℝ)^(-σ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          ((continuous_fullPrimeDampedTerm n σ).norm.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1) (fun u hu => norm_fullPrimeDampedTerm_le hu n)
      _ = _ := by simp
  have hsum : Summable (fun n => ∫ u in Set.Ioc (0:ℝ) 1, ‖f n u‖) := by
    apply (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hbn n
  have hv (n : ℕ) : (∫ u in Set.Ioc (0:ℝ) 1, f n u) = fullPrimeCofactor n * (n : ℝ)^(-σ) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    simp only [f, fullPrimeDampedMoebius, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (by omega : n.primeFactors.card+1 ≠ 0), sub_zero]
    simp only [fullPrimeCofactor]
    ring
  calc fullPrimeCofactorSeries σ = ∑' n, ∫ u in Set.Ioc (0:ℝ) 1, f n u := by
        simp only [fullPrimeCofactorSeries, hv]
    _ = ∫ u in Set.Ioc (0:ℝ) 1, ∑' n, f n u := integral_tsum_of_summable_integral_norm hf hsum
    _ = ∫ u in (0:ℝ)..1, fullPrimeDampedSeries u σ := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
        rfl

/-- The elementary Laplace transform of the unit interval. -/
def cofactorUnitLaplace (a : ℝ) : ℝ := ∫ u in (0:ℝ)..1, Real.exp (-a*u)

theorem cofactorUnitLaplace_eq {a : ℝ} (ha : 0 < a) :
    cofactorUnitLaplace a = (1-Real.exp (-a))/a := by
  rw [cofactorUnitLaplace, intervalIntegral.integral_comp_mul_left Real.exp (by linarith : -a ≠ 0), integral_exp]
  simp only [mul_one, mul_zero, Real.exp_zero, smul_eq_mul, inv_neg]
  ring

theorem fullPrimeCofactorSeries_bounds {σ : ℝ} (hσ : 1 < σ) :
    cofactorUnitLaplace (fullPrimeEulerLog σ) ≤ fullPrimeCofactorSeries σ ∧
      fullPrimeCofactorSeries σ ≤ cofactorUnitLaplace (∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)) := by
  rw [fullPrimeCofactorSeries_eq_integral σ hσ]
  have hi : IntervalIntegrable (fun u => fullPrimeDampedSeries u σ) volume 0 1 :=
    (continuousOn_fullPrimeDampedSeries hσ).intervalIntegrable_of_Icc (by norm_num)
  have he (a : ℝ) : IntervalIntegrable (fun u : ℝ => Real.exp (-a*u)) volume 0 1 :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1
  constructor
  · exact intervalIntegral.integral_mono_on (by norm_num) (he _) hi (fun u hu => by
      simpa only [neg_mul, mul_neg, mul_comm] using (fullPrimeDampedSeries_bounds hu hσ).1)
  · exact intervalIntegral.integral_mono_on (by norm_num) hi (he _) (fun u hu => by
      simpa only [neg_mul, mul_neg, mul_comm] using (fullPrimeDampedSeries_bounds hu hσ).2)


private theorem neg_log_one_sub_sub_le {x : ℝ} (_hx : 0 ≤ x) (hx2 : x ≤ 1/2) :
    x ≤ -Real.log (1-x) ∧ -Real.log (1-x) - x ≤ 2*x^2 := by
  have hd : 0 < 1-x := by linarith
  constructor
  · have h := Real.log_le_sub_one_of_pos hd
    linarith
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
    rw [Real.log_inv] at h
    have hb : 1/(1-x) ≤ 1+x+2*x^2 := (div_le_iff₀ hd).mpr (by nlinarith)
    rw [← one_div] at h
    linarith

theorem fullPrimeEulerLog_mass_bounds {σ : ℝ} (hσ : 1 < σ) :
    (∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)) ≤ fullPrimeEulerLog σ ∧
      fullPrimeEulerLog σ ≤ (∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)) +
        2 * ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-(2:ℝ)) := by
  have hp := summable_fullPrimeMass hσ
  have hlog := summable_fullPrimeEulerLog hσ
  have hp2 := summable_fullPrimeMass (σ := 2) (by norm_num)
  have hloc (p : Nat.Primes) := neg_log_one_sub_sub_le
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (prime_rpow_le_half hσ p)
  constructor
  · exact Summable.tsum_le_tsum (fun p => (hloc p).1) hp hlog
  · have hsq (p : Nat.Primes) : (((p:ℕ):ℝ)^(-σ))^2 ≤ ((p:ℕ):ℝ)^(-(2:ℝ)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) (by linarith)
    have hle : (∑' p : Nat.Primes, -Real.log (1-((p:ℕ):ℝ)^(-σ))) ≤
        ∑' p : Nat.Primes, (((p:ℕ):ℝ)^(-σ) + 2*((p:ℕ):ℝ)^(-(2:ℝ))) := by
      apply Summable.tsum_le_tsum _ hlog (hp.add (hp2.mul_left 2))
      intro p
      linarith [hloc p, hsq p]
    simpa only [hp.tsum_add (hp2.mul_left 2), tsum_mul_left, fullPrimeEulerLog] using hle

theorem tendsto_fullPrimeMass_one :
    Tendsto (fun σ : ℝ => ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)) (𝓝[>] 1) atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hex : ∃ P : Finset Nat.Primes, b < ∑ p ∈ P, (1:ℝ)/(p:ℕ) := by
    by_contra h
    push Not at h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨P,hP⟩ := hex
  have hc : Continuous (fun σ : ℝ => ∑ p ∈ P, ((p:ℕ):ℝ)^(-σ)) := by
    apply continuous_finsetSum
    intro p hp
    have hpn : ((p:ℕ):ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    fun_prop (disch := assumption)
  have hl : Tendsto (fun σ : ℝ => ∑ p ∈ P, ((p:ℕ):ℝ)^(-σ)) (𝓝[>] 1)
      (𝓝 (∑ p ∈ P, (1:ℝ)/(p:ℕ))) := by
    simpa only [Real.rpow_neg_one, one_div] using (hc.continuousAt (x := (1:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
  have hb := hl.eventually (eventually_gt_nhds hP)
  filter_upwards [hb, self_mem_nhdsWithin] with σ hlow hσ
  exact hlow.le.trans ((summable_fullPrimeMass hσ).sum_le_tsum P (fun _ _ => by positivity))

private theorem cofactorUnitLaplace_antitone : Antitone cofactorUnitLaplace := by
  intro a b hab
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
  intro u hu
  apply Real.exp_le_exp.mpr
  change -b*u ≤ -a*u
  nlinarith [mul_le_mul_of_nonneg_right hab hu.1]


/-- The actual all-prime cofactor has reciprocal-prime-mass boundary scale. -/
theorem tendsto_fullPrimeCofactorSeries_mul_primeMass :
    Tendsto (fun σ : ℝ => fullPrimeCofactorSeries σ *
      (∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ))) (𝓝[>] 1) (𝓝 1) := by
  let S : ℝ → ℝ := fun σ => ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)
  let K : ℝ := 2 * ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-(2:ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : Tendsto S (𝓝[>] 1) atTop := tendsto_fullPrimeMass_one
  have hSK : Tendsto (fun σ => S σ + K) (𝓝[>] 1) atTop :=
    tendsto_atTop_add_const_right _ K hS
  have hdiv : Tendsto (fun σ => K / (S σ+K)) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hSK
  have hExp : Tendsto (fun σ => Real.exp (-(S σ))) (𝓝[>] 1) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hS)
  have hExpK : Tendsto (fun σ => Real.exp (-(S σ+K))) (𝓝[>] 1) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hSK)
  have hlo : Tendsto (fun σ => (1-K/(S σ+K))*(1-Real.exp (-(S σ+K))))
      (𝓝[>] 1) (𝓝 1) := by
    convert (tendsto_const_nhds.sub hdiv).mul (tendsto_const_nhds.sub hExpK) using 1
    norm_num
  have hhi : Tendsto (fun σ => 1-Real.exp (-(S σ))) (𝓝[>] 1) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hExp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hS.eventually_gt_atTop 0, self_mem_nhdsWithin] with σ hS0 hσ
    have hSK0 : 0 < S σ+K := by linarith
    have hbound := (fullPrimeCofactorSeries_bounds hσ).1
    have hB := (fullPrimeEulerLog_mass_bounds hσ).2
    have hlow := (cofactorUnitLaplace_antitone hB).trans hbound
    rw [cofactorUnitLaplace_eq hSK0] at hlow
    have hm := mul_le_mul_of_nonneg_right hlow hS0.le
    have he : ((1-Real.exp (-(S σ+K)))/(S σ+K))*S σ =
        (1-K/(S σ+K))*(1-Real.exp (-(S σ+K))) := by
      field_simp
      ring
    simpa only [S, K, he] using hm
  · filter_upwards [hS.eventually_gt_atTop 0, self_mem_nhdsWithin] with σ hS0 hσ
    have hbound := (fullPrimeCofactorSeries_bounds hσ).2
    rw [cofactorUnitLaplace_eq hS0] at hbound
    have hm := mul_le_mul_of_nonneg_right hbound hS0.le
    simpa only [div_mul_cancel₀ _ (ne_of_gt hS0)] using hm

/-- Its limit is zero, although the cofactor retains the preceding boundary layer. -/
theorem tendsto_fullPrimeCofactorSeries_one :
    Tendsto fullPrimeCofactorSeries (𝓝[>] (1:ℝ)) (𝓝 0) := by
  have h := tendsto_fullPrimeCofactorSeries_mul_primeMass.div_atTop tendsto_fullPrimeMass_one
  apply h.congr'
  filter_upwards [tendsto_fullPrimeMass_one.eventually_gt_atTop 0] with σ hσ
  simp only [mul_div_cancel_right₀ _ (ne_of_gt hσ)]


/-- The full coefficient agrees with the existing Ramaré coefficient at every admitted cutoff. -/
theorem fullPrimeCofactor_eq_ramare {n N : ℕ} (hnN : n ≤ N) :
    (fullPrimeCofactor n : ℂ) = ramareCofactorCoeff (Nat.primesLE N) n := by
  by_cases hn : n = 0
  · simp [hn, fullPrimeCofactor, ramareCofactorCoeff]
  have hp : primeFactorsIn (Nat.primesLE N) n = n.primeFactors := by
    ext p
    rw [mem_primeFactorsIn, Nat.mem_primesLE, Nat.mem_primeFactors_of_ne_zero hn]
    constructor
    · intro h
      exact ⟨h.1.2, h.2⟩
    · intro h
      exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h.2).trans hnN, h.1⟩, h.2⟩
  simp only [fullPrimeCofactor, ramareCofactorCoeff, hp]
  push_cast
  rfl

/-- The real Euler logarithm is exactly log of zeta on the Euler half-plane. -/
theorem fullPrimeEulerLog_eq_log_zeta {σ : ℝ} (hσ : 1 < σ) :
    fullPrimeEulerLog σ = Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hb : (fullPrimeEulerLog σ : ℂ) =
      ∑' p : Nat.Primes, -Complex.log (1-((p:ℕ):ℂ)^(-(σ:ℂ))) := by
    rw [fullPrimeEulerLog, Complex.ofReal_tsum]
    apply tsum_congr
    intro p
    have hp : 0 ≤ 1-((p:ℕ):ℝ)^(-σ) := by linarith [prime_rpow_le_half hσ p]
    rw [Complex.ofReal_neg, Complex.ofReal_log hp, Complex.ofReal_sub, Complex.ofReal_one]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (p:ℕ))]
    simp only [Complex.ofReal_natCast, Complex.ofReal_neg]
  rw [← riemannZeta_eulerProduct_exp_log (by simpa using hσ), ← hb,
    Complex.norm_exp, Complex.ofReal_re, Real.log_exp]

/-- The literal Ramaré cofactor has a unit logarithmic zeta boundary invariant. -/
theorem tendsto_fullPrimeCofactorSeries_mul_log_zeta :
    Tendsto (fun σ : ℝ => fullPrimeCofactorSeries σ * Real.log ‖riemannZeta (σ:ℂ)‖)
      (𝓝[>] 1) (𝓝 1) := by
  let S : ℝ → ℝ := fun σ => ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-σ)
  let K : ℝ := 2 * ∑' p : Nat.Primes, ((p:ℕ):ℝ)^(-(2:ℝ))
  have hlo := tendsto_fullPrimeCofactorSeries_mul_primeMass
  have hup : Tendsto (fun σ => fullPrimeCofactorSeries σ*S σ+K*fullPrimeCofactorSeries σ)
      (𝓝[>] 1) (𝓝 1) := by
    simpa using hlo.add (tendsto_fullPrimeCofactorSeries_one.const_mul K)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hF : 0 ≤ fullPrimeCofactorSeries σ := by
      rw [fullPrimeCofactorSeries_eq_integral σ hσ]
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro u hu
      exact (Real.exp_pos _).le.trans (fullPrimeDampedSeries_bounds hu hσ).1
    rw [← fullPrimeEulerLog_eq_log_zeta hσ]
    exact mul_le_mul_of_nonneg_left (fullPrimeEulerLog_mass_bounds hσ).1 hF
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hF : 0 ≤ fullPrimeCofactorSeries σ := by
      rw [fullPrimeCofactorSeries_eq_integral σ hσ]
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro u hu
      exact (Real.exp_pos _).le.trans (fullPrimeDampedSeries_bounds hu hσ).1
    rw [← fullPrimeEulerLog_eq_log_zeta hσ]
    have h := mul_le_mul_of_nonneg_left (fullPrimeEulerLog_mass_bounds hσ).2 hF
    dsimp only [S, K]
    nlinarith [h]

end RHTower.Sieve
