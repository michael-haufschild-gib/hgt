import GaloisForLFunctions.RHTower.EulerDeletionMixedCurrentGram
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusHarmonicZero

/-!
# Möbius channel completion and escape of the literal current

The actual finite Möbius combinations have zero endpoints at zeta zeros, but
converge on each fixed positive prefix to minus one. Their Gram heads retain
this unit defect and force current escape at every off-line zero.
-/
noncomputable section
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionMobiusCurrent
open DeletionMixedCurrent DeletionReflectedEnergy DeletionReflectedCurrent
open DeletionReflectedGram DeletionJointCirculation DeletionChronologicalLimit

/-- Actual reciprocal-modulus Möbius coefficients; index p means modulus p+1. -/
def coefficient (p : ℕ) : ℂ := (moebius (p+1):ℤ)/((p+1:ℕ):ℂ)

/-- The literal growing family of finite deletion paths. -/
def sourcePath (N : ℕ) (s : ℂ) : ℕ → ℂ := mixedPath (Finset.range N) coefficient s

/-- Its full ordinary source prefix. -/
def sourcePrefix (N : ℕ) (s : ℂ) (K : ℕ) : ℂ := endpoint (sourcePath N s) K

/-- The complete mixed chronological current, with every Möbius cross term retained. -/
def sourceCurrent (N : ℕ) (s : ℂ) : ℂ := quadraticCurrent (Finset.range N) coefficient s

/-- The actual finite Gram head of the same source. -/
def energyHead (N : ℕ) (s : ℂ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, mixedEnergy (Finset.range N) coefficient s n

private theorem harmonic_tendsto :
    Tendsto (fun N => (deningerHarmonicPartial N:ℂ)) atTop (nhds 0) := by
  have ht := (Complex.continuous_ofReal.tendsto _).comp deningerHarmonicPartial_tendsto
  simpa only [deningerHarmonicLimit_eq_zero, Complex.ofReal_zero, Function.comp_def] using ht

private theorem coefficient_sum (N : ℕ) :
    ∑ p ∈ Finset.range N, coefficient p=(deningerHarmonicPartial N:ℂ) := by
  have h := Finset.sum_range_succ' (fun d : ℕ => ((moebius d:ℤ):ℂ)/(d:ℂ)) N
  simpa [coefficient, deningerHarmonicPartial, Complex.ofReal_sum] using h.symm

private theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, ((moebius d:ℤ):ℂ)=if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

private theorem divisor_sum_initial {N n : ℕ} (hN : n+1≤N) :
    (∑ p ∈ Finset.range N,
      if (p+1)∣(n+1) then ((moebius (p+1):ℤ):ℂ) else 0) =
      if n=0 then 1 else 0 := by
  have h := Finset.sum_range_succ'
    (fun d : ℕ => if d∣(n+1) then ((moebius d:ℤ):ℂ) else 0) N
  simp at h
  have hd : (Finset.range (N+1)).filter (fun d => d∣n+1)=(n+1).divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2,Nat.succ_ne_zero n⟩
    · intro h
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.succ_pos n) h.1)
        (Nat.lt_succ_of_le hN),h.1⟩
  rw [← h, ← Finset.sum_filter, hd, sum_moebius_divisors]
  simp

/-- Exact finite arithmetic collapse; the conditional harmonic series is never rearranged. -/
theorem source_coefficient_initial {N n : ℕ} (hN : n+1≤N) :
    (∑ p ∈ Finset.range N, coefficient p*eulerDeletionDirichletCoefficient p n) =
      (deningerHarmonicPartial N:ℂ)-(if n=0 then 1 else 0) := by
  have he (p : ℕ) : coefficient p*eulerDeletionDirichletCoefficient p n =
      coefficient p-(if (p+1)∣(n+1) then ((moebius (p+1):ℤ):ℂ) else 0) := by
    have hp : ((p+1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero p
    by_cases hd : (p+1)∣(n+1)
    all_goals simp [coefficient, eulerDeletionDirichletCoefficient, blockDeletionCoefficient, hd]
    all_goals field_simp
    all_goals ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, coefficient_sum, divisor_sum_initial hN]

/-- The weighted path retains the exact unit impulse after its full harmonic term. -/
theorem sourcePath_initial {N n : ℕ} (hN : n+1≤N) (s : ℂ) :
    sourcePath N s n=((deningerHarmonicPartial N:ℂ)-(if n=0 then 1 else 0))*kernel s n := by
  have he : sourcePath N s n =
      (∑ p ∈ Finset.range N, coefficient p*eulerDeletionDirichletCoefficient p n)*kernel s n := by
    simp only [sourcePath, mixedPath, eulerDeletionWeightedJump, kernel, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he, source_coefficient_initial hN]

/-- Exact ordinary prefix formula, valid throughout the expanding initial source window. -/
theorem sourcePrefix_initial {N K : ℕ} (hK : 0<K) (hKN : K≤N) (s : ℂ) :
    sourcePrefix N s K=(deningerHarmonicPartial N:ℂ)*(∑ n ∈ Finset.range K, kernel s n)-1 := by
  have he : sourcePrefix N s K = ∑ n ∈ Finset.range K,
      ((deningerHarmonicPartial N:ℂ)-(if n=0 then 1 else 0))*kernel s n := by
    unfold sourcePrefix endpoint
    apply Finset.sum_congr rfl
    intro n hn
    exact sourcePath_initial (by have := Finset.mem_range.mp hn; omega) s
  rw [he]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hi : (∑ n ∈ Finset.range K, (if n=0 then (1:ℂ) else 0)*kernel s n)=1 := by
    rw [Finset.sum_eq_single 0]
    · simp [kernel]
    · intro n hn hn0
      simp only [hn0, if_false, zero_mul]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hK))
  rw [hi]

/-- Increasing the channel cutoff leaves a nonzero unit endpoint on every fixed positive prefix. -/
theorem sourcePrefix_tendsto (s : ℂ) {K : ℕ} (hK : 0<K) :
    Tendsto (fun N => sourcePrefix N s K) atTop (nhds (-1)) := by
  have ht := (harmonic_tendsto.mul_const (∑ n ∈ Finset.range K, kernel s n)).sub_const 1
  simp only [zero_mul, zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop K] with N hN
  exact (sourcePrefix_initial hK hN s).symm

/-- At every actual zero each fixed finite-channel path still has ordinary endpoint zero. -/
theorem sourcePrefix_zero_endpoint (N : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (sourcePrefix N rho.1) atTop (nhds 0) := by
  have ht := ((kernel_tendsto_zero rho.1
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)).norm).const_mul
      (∑ p ∈ Finset.range N, ‖coefficient p‖*eulerDeletionAbelTailConstant p rho.1)
  apply squeeze_zero_norm (fun K => mixed_endpoint_bound (Finset.range N) coefficient rho K)
  simpa only [norm_kernel, norm_zero, mul_zero] using ht

/-- The two endpoint limits retain an exact nonzero unit defect at every actual zero. -/
theorem endpoint_limit_defect (rho : RiemannGaussian.NontrivialZetaZero) :
    (∀ N : ℕ, Tendsto (sourcePrefix N rho.1) atTop (nhds 0)) ∧
      (∀ K : ℕ, 0<K → Tendsto (fun N => sourcePrefix N rho.1 K) atTop (nhds (-1))) :=
  ⟨fun N => sourcePrefix_zero_endpoint N rho,fun _ hK => sourcePrefix_tendsto rho.1 hK⟩

private theorem sum_weight_increments (s : ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range K, (weight s (n+1)-weight s n))=weight s K-1 := by
  induction K with
  | zero => simp [weight]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Every fixed Gram head has an exact unit-defect limit as the arithmetic channel family grows. -/
theorem energyHead_tendsto (s : ℂ) (K : ℕ) :
    Tendsto (fun N => energyHead N s K) atTop (nhds (weight s K-1)) := by
  have ht := tendsto_finsetSum (Finset.range K) (fun n hn =>
    (((sourcePrefix_tendsto s (Nat.succ_pos n)).norm).pow 2).const_mul
      (weight s (n+1)-weight s n))
  simpa only [norm_neg, norm_one, one_pow, mul_one, sum_weight_increments,
    energyHead, mixedEnergy, sourcePrefix, sourcePath] using ht

/-- The growing Möbius family retains the exact source reflection reversal. -/
theorem sourceCurrent_partner (N : ℕ) (s : ℂ) :
    sourceCurrent N (partner s)= -sourceCurrent N s := by
  have hv (p q : ℕ) : variationCurrent p q (partner s) s= -variationCurrent p q s (partner s) := by
    simp only [variationCurrent, ← tsum_neg]
    congr 1
    funext n
    ring
  simp only [sourceCurrent, quadraticCurrent, partner_partner, hv, mul_neg, Finset.sum_neg_distrib]

/-- At every right-half zero the actual Möbius quadratic current tends to positive infinity. -/
theorem sourceCurrent_tendsto_atTop (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2<rho.1.re) :
    Tendsto (fun N => (sourceCurrent N rho.1).re) atTop atTop := by
  have he : 0<exponent rho.1 := by unfold exponent; linarith
  have hw : Tendsto (fun K : ℕ => weight rho.1 K) atTop atTop := by
    have ht := (tendsto_rpow_atTop he).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1))
    simpa only [weight, Nat.cast_add, Nat.cast_one, Function.comp_def] using ht
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨K,hK⟩ := (hw.eventually_gt_atTop (B+1)).exists
  have hB : B<weight rho.1 K-1 := by linarith
  have hhead := (energyHead_tendsto rho.1 K).eventually (eventually_gt_nhds hB)
  filter_upwards [hhead] with N hN
  exact hN.le.trans (mixed_energy_prefix_le_current (Finset.range N) coefficient rho hs.le K)

/-- At every off-line zero the absolute current escapes every finite bound. -/
theorem abs_sourceCurrent_tendsto_atTop (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : rho.1.re≠1/2) :
    Tendsto (fun N => |(sourceCurrent N rho.1).re|) atTop atTop := by
  rcases lt_or_gt_of_ne hs with hleft | hright
  · let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
    have hr : r.1=partner rho.1 := rfl
    have hrr : 1/2<r.1.re := by rw [hr]; simp only [partner, Complex.sub_re,
      Complex.one_re, Complex.star_def, Complex.conj_re]; linarith
    have ht := tendsto_atTop_mono (fun N => le_abs_self ((sourceCurrent N r.1).re))
      (sourceCurrent_tendsto_atTop r hrr)
    simpa only [hr, sourceCurrent_partner, Complex.neg_re, abs_neg] using ht
  · exact tendsto_atTop_mono (fun N => le_abs_self ((sourceCurrent N rho.1).re))
      (sourceCurrent_tendsto_atTop rho hright)

/-- At a zero, boundedness of this concrete arithmetic family is exactly critical-line location. -/
theorem sourceCurrent_bounded_iff (rho : RiemannGaussian.NontrivialZetaZero) :
    (∃ B : ℝ, ∀ N : ℕ, |(sourceCurrent N rho.1).re|≤B) ↔ rho.1.re=1/2 := by
  constructor
  · rintro ⟨B,hB⟩
    by_contra hr
    obtain ⟨N,hN⟩ := ((abs_sourceCurrent_tendsto_atTop rho hr).eventually_gt_atTop B).exists
    exact (not_le.mpr hN) (hB N)
  · intro hr
    refine ⟨0,fun N => ?_⟩
    rw [sourceCurrent, quadraticCurrent_of_re_half _ _ hr]
    simp

/-- Even arbitrarily late bounded returns of the concrete current force critical-line location. -/
theorem sourceCurrent_cofinally_bounded_iff (rho : RiemannGaussian.NontrivialZetaZero) :
    (∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧ |(sourceCurrent N rho.1).re|≤B) ↔
      rho.1.re=1/2 := by
  constructor
  · rintro ⟨B,hB⟩
    by_contra hr
    obtain ⟨K,hK⟩ := eventually_atTop.mp
      ((abs_sourceCurrent_tendsto_atTop rho hr).eventually_gt_atTop B)
    obtain ⟨N,hKN,hN⟩ := hB K
    exact (not_le.mpr (hK N hKN)) hN
  · intro hr
    refine ⟨0,fun K => ⟨K,le_rfl,?_⟩⟩
    rw [sourceCurrent, quadraticCurrent_of_re_half _ _ hr]
    simp

/-- Exact RH receiver: boundedness of the literal Möbius currents at every actual zero. -/
theorem riemannHypothesis_iff_mobius_current_bounded :
    RiemannHypothesis ↔ ∀ rho : RiemannGaussian.NontrivialZetaZero,
      ∃ B : ℝ, ∀ N : ℕ, |(sourceCurrent N rho.1).re|≤B := by
  constructor
  · intro hRH rho
    exact (sourceCurrent_bounded_iff rho).2 (hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2)
  · intro h s hz ht hs1
    let rho : RiemannGaussian.NontrivialZetaZero := ⟨s,hz,ht,hs1⟩
    exact (sourceCurrent_bounded_iff rho).1 (h rho)

/-- Sharp cofinal RH receiver: a zero-dependent bound on arbitrarily late actual Möbius currents suffices. -/
theorem riemannHypothesis_iff_mobius_current_cofinally_bounded :
    RiemannHypothesis ↔ ∀ rho : RiemannGaussian.NontrivialZetaZero,
      ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧ |(sourceCurrent N rho.1).re|≤B := by
  constructor
  · intro hRH rho
    exact (sourceCurrent_cofinally_bounded_iff rho).2 (hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2)
  · intro h s hz ht hs1
    let rho : RiemannGaussian.NontrivialZetaZero := ⟨s,hz,ht,hs1⟩
    exact (sourceCurrent_cofinally_bounded_iff rho).1 (h rho)

end RHTower.DeletionMobiusCurrent
end
