import GaloisForLFunctions.BiScaleUncertainty.TwoLagArithmeticCone
import GaloisForLFunctions.BiScaleUncertainty.TwoLagSievePeriod
import GaloisForLFunctions.BezoutValuationIncidence.ExactSuccessorMomentRegionAndUniversalInequalities
import Mathlib.Analysis.Real.Sqrt

/-!
# Exact two-lag sieve moment cone

Literal centered covariances on `1 .. N!` have an exact divisor-coordinate
diagonal. Profiles on modes `1, 2, 3, 4, 6, 12`, followed by the finite
multiples inverse, realize every admissible tuple and prescribed mean.
The five facets classify all attainable tuples and all universal linear
inequalities, for actual finite signed divisor-sieve weights.
-/

noncomputable section
open Finset ArithmeticFunction RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
set_option autoImplicit false

/-- Literal centered lag covariance over the complete period `1 .. N!`. -/
def periodCovariance (N : ℕ) (c : ℕ → ℝ) (h : ℕ) : ℝ :=
  (∑ k ∈ Finset.Ioc 0 (Nat.factorial N),
    (sieveSeq N c k - finiteHarmonicSum N c) *
      (sieveSeq N c (k+h) - finiteHarmonicSum N c)) / (Nat.factorial N : ℝ)

private def lagKernelForm (N : ℕ) (c : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    (if Nat.gcd p.1 p.2 ∣ h then (Nat.gcd p.1 p.2 : ℝ) else 0) *
      (c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ))

private theorem sum_rows (S T : Finset ℕ) (c : ℕ → ℝ) (h : ℕ) :
    (∑ k ∈ T, ∑ a ∈ S, if a ∣ k+h then c a else 0) =
      ∑ a ∈ S, c a * ((T.filter (fun k => a ∣ k+h)).card : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_filter]
  simp [mul_comm]

private theorem sum_row_products (S T : Finset ℕ) (c : ℕ → ℝ) (h : ℕ) :
    (∑ k ∈ T, (∑ a ∈ S, if a ∣ k then c a else 0) *
      (∑ b ∈ S, if b ∣ k+h then c b else 0)) =
      ∑ a ∈ S, ∑ b ∈ S, (c a*c b) *
        ((T.filter (fun k => a ∣ k ∧ b ∣ k+h)).card : ℝ) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  have hpoint (k : ℕ) : (if a ∣ k then c a else 0) * (if b ∣ k+h then c b else 0) =
      if a ∣ k ∧ b ∣ k+h then c a*c b else 0 := by
    by_cases hka : a ∣ k <;> by_cases hkb : b ∣ k+h <;> simp [hka, hkb]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp [mul_comm]

private theorem center_sum (T : Finset ℕ) (u v : ℕ → ℝ) (H : ℝ) :
    (∑ k ∈ T, (u k-H)*(v k-H)) =
      (∑ k ∈ T, u k*v k) - H*(∑ k ∈ T, u k) - H*(∑ k ∈ T, v k) + T.card*H^2 := by
  have hpoint (k : ℕ) : (u k-H)*(v k-H) = u k*v k-H*u k-H*v k+H^2 := by ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- Every additive shift has the same exact finite-period mean. -/
theorem sum_sieveSeq_complete_period (N h : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c (k+h)) =
      (Nat.factorial N : ℝ) * finiteHarmonicSum N c := by
  simp_rw [sieveSeq, Finset.sum_filter]
  rw [sum_rows]
  unfold finiteHarmonicSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨ha, haN⟩ := Finset.mem_Icc.mp ha
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have had := Nat.dvd_factorial (show 0 < a by omega) haN
  rw [card_shift_complete_period h had, Nat.cast_div had ha0]
  ring

private theorem product_average_eq_kernel (N h : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c k * sieveSeq N c (k+h)) /
      (Nat.factorial N : ℝ) = lagKernelForm N c h := by
  simp_rw [sieveSeq, Finset.sum_filter]
  rw [sum_row_products]
  unfold lagKernelForm
  rw [Finset.sum_product, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨ha, haN⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb, hbN⟩ := Finset.mem_Icc.mp hb
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  have hL := Nat.lcm_dvd (Nat.dvd_factorial (show 0 < a by omega) haN)
    (Nat.dvd_factorial (show 0 < b by omega) hbN)
  rw [mul_div_assoc, joint_density_complete_period (by omega) (by omega) hL (Nat.factorial_pos N)]
  by_cases hg : Nat.gcd a b ∣ h
  · simp only [if_pos hg]
    field_simp
  · simp [hg]

private theorem periodCovariance_eq_kernel_sub_mean (N h : ℕ) (c : ℕ → ℝ) :
    periodCovariance N c h = lagKernelForm N c h - (finiteHarmonicSum N c)^2 := by
  have hP0 : (Nat.factorial N : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  have hsum0 : (∑ k ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c k) =
      (Nat.factorial N : ℝ) * finiteHarmonicSum N c := by
    simpa using sum_sieveSeq_complete_period N 0 c
  unfold periodCovariance
  rw [center_sum, hsum0, sum_sieveSeq_complete_period]
  simp only [Nat.card_Ioc, Nat.sub_zero]
  calc
    _ = (∑ k ∈ Finset.Ioc 0 (Nat.factorial N), sieveSeq N c k * sieveSeq N c (k+h)) /
        (Nat.factorial N : ℝ) - (finiteHarmonicSum N c)^2 := by
      (field_simp; ring)
    _ = _ := by rw [product_average_eq_kernel]

private theorem lagKernelForm_eq_diagonal (N h : ℕ) (c w : ℕ → ℝ)
    (hw : ∀ g : ℕ, 0 < g → ∑ e ∈ g.divisors, w e = if g ∣ h then (g : ℝ) else 0) :
    lagKernelForm N c h = ∑ e ∈ Finset.Icc 1 N, w e * (selbergMultiplesCoord N c e)^2 := by
  classical
  unfold lagKernelForm selbergMultiplesCoord
  have hS : ∀ m ∈ Finset.Icc 1 N, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have hexp : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      (if Nat.gcd p.1 p.2 ∣ h then (Nat.gcd p.1 p.2 : ℝ) else 0) *
        (c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ)) =
        ∑ e ∈ (Nat.gcd p.1 p.2).divisors,
          w e * ((c p.1 / (p.1 : ℝ)) * (c p.2 / (p.2 : ℝ))) := by
    intro p hp
    obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
    rw [← hw _ (Nat.gcd_pos_of_pos_left _ (hS _ hp1)), Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (p : ℕ × ℕ) (e : ℕ),
      p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ∧ e ∈ (Nat.gcd p.1 p.2).divisors ↔
        p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) ∧
          e ∈ (Finset.Icc 1 N).biUnion Nat.divisors := by
    intro p e
    constructor
    · rintro ⟨hp, he⟩
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      have hgcd : e ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors he
      have hd1 : e ∣ p.1 := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
      have hd2 : e ∣ p.2 := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
      refine ⟨Finset.mem_filter.mpr ⟨hp, hd1, hd2⟩, Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩⟩
      have hp1_pos := hS _ hp1
      exact Nat.mem_divisors.mpr ⟨hd1, by omega⟩
    · rintro ⟨hpf, -⟩
      obtain ⟨hp, hd1, hd2⟩ := Finset.mem_filter.mp hpf
      obtain ⟨hp1, _⟩ := Finset.mem_product.mp hp
      refine ⟨hp, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd1 hd2, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_left _ (hS _ hp1)).ne'
  rw [Finset.sum_comm' hmem, biUnion_divisors_Icc_eq_Icc]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfilter : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) =
      ((Finset.Icc 1 N).filter (fun m => e ∣ m)) ×ˢ ((Finset.Icc 1 N).filter (fun m => e ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfilter, ← Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_product]

private theorem periodCovariance_eq_diagonal (N h : ℕ) (c w : ℕ → ℝ)
    (hw : ∀ g : ℕ, 0 < g → ∑ e ∈ g.divisors, w e = if g ∣ h then (g : ℝ) else 0) :
    periodCovariance N c h = ∑ e ∈ Finset.Icc 2 N, w e * (selbergMultiplesCoord N c e)^2 := by
  rw [periodCovariance_eq_kernel_sub_mean, lagKernelForm_eq_diagonal N h c w hw]
  have hw1 : w 1 = 1 := by
    have h := hw 1 (by omega)
    simpa using h
  rcases N with _ | N
  · simp [finiteHarmonicSum]
  · have hI : Finset.Icc 1 (N+1) = insert 1 (Finset.Icc 2 (N+1)) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_insert (by simp), hw1, one_mul,
      selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    ring

/-- The existing Selberg variance is the literal zero-lag centered period average. -/
theorem periodCovariance_zero (N : ℕ) (c : ℕ → ℝ) :
    periodCovariance N c 0 = sieveVariance N c := by
  apply periodCovariance_eq_diagonal N 0 c (fun e => (Nat.totient e : ℝ))
  intro g hg
  simp only [dvd_zero, if_true]
  exact_mod_cast Nat.sum_totient g

/-- The existing Bézout covariance is the literal first-lag centered period average. -/
theorem periodCovariance_one (N : ℕ) (c : ℕ → ℝ) :
    periodCovariance N c 1 = bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2 := by
  rw [bezout_sub_harmonic_sq_eq]
  apply periodCovariance_eq_diagonal N 1 c moebiusReal
  intro g hg
  rw [sum_divisors_moebiusReal_eq_ite_one (by omega)]
  by_cases h1 : g=1
  · subst g
    simp
  · simp [h1, Nat.dvd_one]

/-- Exact second-lag diagonal for every finite real divisor weight. -/
theorem periodCovariance_two (N : ℕ) (c : ℕ → ℝ) :
    periodCovariance N c 2 =
      ∑ e ∈ Finset.Icc 2 N, lagTwoEigenvalue e * (selbergMultiplesCoord N c e)^2 :=
  periodCovariance_eq_diagonal N 2 c lagTwoEigenvalue (fun _ hg => lagTwoEigenvalue_divisor_sum hg)

/-- Every actual finite sieve satisfies the five simultaneous moment inequalities. -/
theorem sieve_momentCone (N : ℕ) (c : ℕ → ℝ) :
    MomentCone (sieveVariance N c)
      (bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2) (periodCovariance N c 2) := by
  rw [bezout_sub_harmonic_sq_eq, periodCovariance_two]
  unfold sieveVariance moebiusReal MomentCone
  have hc (e : ℕ) (he : e ∈ Finset.Icc 2 N) := arithmetic_momentCone (Finset.mem_Icc.mp he).1
  have h1 := Finset.sum_nonneg (fun e he => mul_nonneg (hc e he).1 (sq_nonneg (selbergMultiplesCoord N c e)))
  have h2 := Finset.sum_nonneg (fun e he => mul_nonneg (hc e he).2.1 (sq_nonneg (selbergMultiplesCoord N c e)))
  have h3 := Finset.sum_nonneg (fun e he => mul_nonneg (hc e he).2.2.1 (sq_nonneg (selbergMultiplesCoord N c e)))
  have h4 := Finset.sum_nonneg (fun e he => mul_nonneg (hc e he).2.2.2.1 (sq_nonneg (selbergMultiplesCoord N c e)))
  have h5 := Finset.sum_nonneg (fun e he => mul_nonneg (hc e he).2.2.2.2 (sq_nonneg (selbergMultiplesCoord N c e)))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | simpa only [add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum] using h1
    | simpa only [add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum] using h2
    | simpa only [add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum] using h3
    | simpa only [add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum] using h4
    | simpa only [add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum] using h5


/-- Constant coordinate and the five nonconstant generating modes. -/
def fiveModeProfile (H a b c d e : ℝ) (q : ℕ) : ℝ :=
  if q=1 then H else if q=2 then a else if q=3 then b else
    if q=4 then c else if q=6 then d else if q=12 then e else 0

/-- Exact weighted diagonal evaluation at every cutoff at least twelve. -/
theorem sum_fiveModeProfile_sq (N : ℕ) (w : ℕ → ℝ) (H a b c d e : ℝ) :
    (∑ q ∈ Finset.Icc 1 (N+12), w q * (fiveModeProfile H a b c d e q)^2) =
      w 1*H^2+w 2*a^2+w 3*b^2+w 4*c^2+w 6*d^2+w 12*e^2 := by
  have hterm (q : ℕ) : w q * (fiveModeProfile H a b c d e q)^2 =
      (if q=1 then w 1*H^2 else 0) + (if q=2 then w 2*a^2 else 0) +
      (if q=3 then w 3*b^2 else 0) + (if q=4 then w 4*c^2 else 0) +
      (if q=6 then w 6*d^2 else 0) + (if q=12 then w 12*e^2 else 0) := by
    by_cases h1 : q=1
    · subst q; simp [fiveModeProfile]
    by_cases h2 : q=2
    · subst q; simp [fiveModeProfile]
    by_cases h3 : q=3
    · subst q; simp [fiveModeProfile]
    by_cases h4 : q=4
    · subst q; simp [fiveModeProfile]
    by_cases h6 : q=6
    · subst q; simp [fiveModeProfile]
    by_cases h12 : q=12
    · subst q; simp [fiveModeProfile]
    simp [fiveModeProfile, h1, h2, h3, h4, h6, h12]
  simp_rw [hterm, Finset.sum_add_distrib]
  have h1 : 1 ≤ N+12 := by omega
  have h2 : 2 ≤ N+12 := by omega
  have h3 : 3 ≤ N+12 := by omega
  have h4 : 4 ≤ N+12 := by omega
  have h6 : 6 ≤ N+12 := by omega
  have h12 : 12 ≤ N+12 := by omega
  simp [h1, h2, h3, h4, h6, h12]

/-- Explicit finite divisor weight with the prescribed six Selberg coordinates. -/
def fiveModeWeight (N : ℕ) (H a b c d e : ℝ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff (fiveModeProfile H a b c d e) (N+12)

private theorem fiveModeWeight_tail (N : ℕ) (w : ℕ → ℝ) (H a b c d e : ℝ) :
    (∑ q ∈ Finset.Icc 2 (N+12), w q *
      (selbergMultiplesCoord (N+12) (fiveModeWeight N H a b c d e) q)^2) =
        w 2*a^2+w 3*b^2+w 4*c^2+w 6*d^2+w 12*e^2 := by
  have htail : (∑ q ∈ Finset.Icc 2 (N+12), w q *
      (selbergMultiplesCoord (N+12) (fiveModeWeight N H a b c d e) q)^2) =
        ∑ q ∈ Finset.Icc 2 (N+12), w q * (fiveModeProfile H a b c d e q)^2 := by
    apply Finset.sum_congr rfl
    intro q hq
    unfold fiveModeWeight
    rw [selbergMultiplesCoord_ramanujan_inverse, if_pos]
    obtain ⟨hq, hqN⟩ := Finset.mem_Icc.mp hq
    exact Finset.mem_Icc.mpr ⟨by omega, hqN⟩
  rw [htail]
  have hfull := sum_fiveModeProfile_sq N w H a b c d e
  have hI : Finset.Icc 1 (N+12) = insert 1 (Finset.Icc 2 (N+12)) := by
    ext q
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hI, Finset.sum_insert (by simp)] at hfull
  have hp1 : fiveModeProfile H a b c d e 1 = H := by simp [fiveModeProfile]
  rw [hp1] at hfull
  linarith

private theorem generating_moebius_values :
    μ 2 = -1 ∧ μ 3 = -1 ∧ μ 4 = 0 ∧ μ 6 = 1 ∧ μ 12 = 0 := by
  have h2 : μ 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : μ 3 = -1 := ArithmeticFunction.moebius_apply_prime (by decide)
  have h4 (r : ℕ) : μ (4*r) = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two ⟨r, by ring⟩
  have h6 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (show Nat.Coprime 2 3 by decide)
  exact ⟨h2, h3, by simpa using h4 1, by simpa [h2, h3] using h6, by simpa using h4 3⟩

/-- One actual finite weight realizes the mean and all three centered period moments. -/
theorem fiveModeWeight_moments (N : ℕ) (H a b c d e : ℝ) :
    finiteHarmonicSum (N+12) (fiveModeWeight N H a b c d e) = H ∧
      periodCovariance (N+12) (fiveModeWeight N H a b c d e) 0 =
        a^2+2*b^2+2*c^2+2*d^2+4*e^2 ∧
      periodCovariance (N+12) (fiveModeWeight N H a b c d e) 1 = -a^2-b^2+d^2 ∧
      periodCovariance (N+12) (fiveModeWeight N H a b c d e) 2 = a^2-b^2-2*c^2-d^2+2*e^2 := by
  obtain ⟨hm2, hm3, hm4, hm6, hm12⟩ := generating_moebius_values
  have hphi : Nat.totient 2 = 1 ∧ Nat.totient 3 = 2 ∧ Nat.totient 4 = 2 ∧
      Nat.totient 6 = 2 ∧ Nat.totient 12 = 4 := by decide
  obtain ⟨hf2, hf3, hf4, hf6, hf12⟩ := hphi
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    unfold fiveModeWeight
    rw [selbergMultiplesCoord_ramanujan_inverse, if_pos (by simp)]
    simp [fiveModeProfile]
  · rw [periodCovariance_zero]
    unfold sieveVariance
    rw [fiveModeWeight_tail]
    simp [hf2, hf3, hf4, hf6, hf12]
  · rw [periodCovariance_one, bezout_sub_harmonic_sq_eq, fiveModeWeight_tail]
    (simp [moebiusReal, hm2, hm3, hm4, hm6, hm12]; ring)
  · rw [periodCovariance_two, fiveModeWeight_tail]
    (norm_num [lagTwoEigenvalue, hm2, hm3, hm4, hm6, hm12]; ring)

/-- Every finite sieve has its literal three centered lag moments in the cone. -/
theorem period_momentCone (N : ℕ) (c : ℕ → ℝ) :
    MomentCone (periodCovariance N c 0) (periodCovariance N c 1) (periodCovariance N c 2) := by
  rw [periodCovariance_zero, periodCovariance_one]
  exact sieve_momentCone N c

/-- Exact attainable region at every cutoff at least twelve, with arbitrary prescribed mean. -/
theorem exists_sieve_with_two_lag_moments_iff (N : ℕ) (H V x y : ℝ) :
    (∃ c : ℕ → ℝ, finiteHarmonicSum (N+12) c = H ∧
      periodCovariance (N+12) c 0 = V ∧ periodCovariance (N+12) c 1 = x ∧
      periodCovariance (N+12) c 2 = y) ↔ MomentCone V x y := by
  constructor
  · rintro ⟨c, _, hV, hx, hy⟩
    have h := period_momentCone (N+12) c
    rwa [hV, hx, hy] at h
  · intro hcone
    obtain ⟨A, B, C, D, E, hA, hB, hC, hD, hE, hV, hx, hy⟩ :=
      (momentCone_iff_exists_nonnegative_five_masses V x y).mp hcone
    have hsA := Real.sq_sqrt hA
    have hsB := Real.sq_sqrt (show 0 ≤ B/2 by positivity)
    have hsC := Real.sq_sqrt (show 0 ≤ C/2 by positivity)
    have hsD := Real.sq_sqrt (show 0 ≤ D/2 by positivity)
    have hsE := Real.sq_sqrt (show 0 ≤ E/4 by positivity)
    obtain ⟨hmean, hvar, hfirst, hsecond⟩ := fiveModeWeight_moments N H
      (Real.sqrt A) (Real.sqrt (B/2)) (Real.sqrt (C/2)) (Real.sqrt (D/2)) (Real.sqrt (E/4))
    simp only [hsA, hsB, hsC, hsD, hsE] at hvar hfirst hsecond
    refine ⟨fiveModeWeight N H (Real.sqrt A) (Real.sqrt (B/2)) (Real.sqrt (C/2))
      (Real.sqrt (D/2)) (Real.sqrt (E/4)), hmean, ?_, ?_, ?_⟩ <;> linarith

/-- Complete classification of universal linear inequalities in the three literal lag moments. -/
theorem universal_two_lag_sieve_inequality_iff (α β γ : ℝ) :
    (∀ (N : ℕ) (c : ℕ → ℝ), 0 ≤ α*periodCovariance N c 0 +
      β*periodCovariance N c 1 + γ*periodCovariance N c 2) ↔
        0 ≤ α-β+γ ∧ 0 ≤ 2*α-β-γ ∧ 0 ≤ α-γ ∧
        0 ≤ 2*α+β-γ ∧ 0 ≤ 2*α+γ := by
  rw [← universal_momentCone_linear_inequality_iff]
  constructor
  · intro h V x y hcone
    obtain ⟨c, _, hV, hx, hy⟩ := (exists_sieve_with_two_lag_moments_iff 0 0 V x y).mpr hcone
    have hc := h 12 c
    simpa only [Nat.zero_add, hV, hx, hy] using hc
  · intro h N c
    exact h _ _ _ (period_momentCone N c)

/-- Lag two separates two actual weights with identical mean, variance and first-lag covariance. -/
theorem exists_same_first_moments_distinct_second_lag (N : ℕ) (H : ℝ) :
    ∃ c d : ℕ → ℝ,
      finiteHarmonicSum (N+12) c = H ∧ finiteHarmonicSum (N+12) d = H ∧
      periodCovariance (N+12) c 0 = 1 ∧ periodCovariance (N+12) d 0 = 1 ∧
      periodCovariance (N+12) c 1 = 0 ∧ periodCovariance (N+12) d 1 = 0 ∧
      periodCovariance (N+12) c 2 = -1 ∧ periodCovariance (N+12) d 2 = 1/2 := by
  obtain ⟨c, hcH, hcV, hcx, hcy⟩ :=
    (exists_sieve_with_two_lag_moments_iff N H 1 0 (-1)).mpr (by norm_num [MomentCone])
  obtain ⟨d, hdH, hdV, hdx, hdy⟩ :=
    (exists_sieve_with_two_lag_moments_iff N H 1 0 (1/2)).mpr (by norm_num [MomentCone])
  exact ⟨c, d, hcH, hdH, hcV, hdV, hcx, hdx, hcy, hdy⟩

end GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
