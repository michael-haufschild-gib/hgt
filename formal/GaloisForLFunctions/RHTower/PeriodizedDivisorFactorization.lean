import GaloisForLFunctions.HTGeometry.LocalAnalyticQuotient
import GaloisForLFunctions.RHTower.SymmetricDivisorRealization

noncomputable section

namespace GaloisForLFunctions.RHTower.PeriodizedDivisorFactorization

open Complex

def periodizedZeroFactor (N : ℕ) (logp : ℝ) (rho s : ℂ) : ℂ :=
  1 - Complex.exp ((N : ℂ) * (logp : ℂ) * (rho - s))

def stackPeriod (N : ℕ) (logp : ℝ) : ℂ :=
  ((2 * Real.pi / ((N : ℝ) * logp) : ℝ) : ℂ) * Complex.I

theorem periodizedZeroFactor_periodic {N : ℕ} {logp : ℝ}
    (hN : N ≠ 0) (hlogp : logp ≠ 0) (rho s : ℂ) :
    periodizedZeroFactor N logp rho (s + stackPeriod N logp) =
      periodizedZeroFactor N logp rho s := by
  unfold periodizedZeroFactor stackPeriod
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hlogpC : (logp : ℂ) ≠ 0 := by exact_mod_cast hlogp
  have hexp : Complex.exp
      ((N : ℂ) * (logp : ℂ) *
        (rho - (s + ((2 * Real.pi / ((N : ℝ) * logp) : ℝ) : ℂ) * Complex.I))) =
      Complex.exp ((N : ℂ) * (logp : ℂ) * (rho - s)) := by
    rw [show (N : ℂ) * (logp : ℂ) *
        (rho - (s + ((2 * Real.pi / ((N : ℝ) * logp) : ℝ) : ℂ) * Complex.I)) =
      (N : ℂ) * (logp : ℂ) * (rho - s) - 2 * (Real.pi : ℂ) * Complex.I by
      push_cast
      field_simp [hNC, hlogpC]
      ring]
    rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [hexp]

theorem periodizedZeroFactor_eq_zero_iff_lattice {N : ℕ} {logp : ℝ}
    (hN : N ≠ 0) (hlogp : logp ≠ 0) (rho s : ℂ) :
    periodizedZeroFactor N logp rho s = 0 ↔
      ∃ k : ℤ, s = rho - (k : ℂ) * stackPeriod N logp := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hlogpC : (logp : ℂ) ≠ 0 := by exact_mod_cast hlogp
  constructor
  · intro hzero
    have hexp : Complex.exp ((N : ℂ) * (logp : ℂ) * (rho - s)) = 1 := by
      unfold periodizedZeroFactor at hzero
      exact (sub_eq_zero.mp hzero).symm
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨k, ?_⟩
    unfold stackPeriod
    push_cast
    field_simp [hNC, hlogpC] at hk ⊢
    linear_combination -hk
  · rintro ⟨k, rfl⟩
    unfold periodizedZeroFactor stackPeriod
    have harg : (N : ℂ) * (logp : ℂ) *
        (rho - (rho - (k : ℂ) *
          (((2 * Real.pi / ((N : ℝ) * logp) : ℝ) : ℂ) * Complex.I))) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp [hNC, hlogpC]
      ring
    rw [harg]
    have hexp : Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨k, rfl⟩
    rw [hexp, sub_self]

theorem analyticAt_periodizedZeroFactor (N : ℕ) (logp : ℝ) (rho z : ℂ) :
    AnalyticAt ℂ (periodizedZeroFactor N logp rho) z := by
  unfold periodizedZeroFactor
  fun_prop

theorem deriv_periodizedZeroFactor (N : ℕ) (logp : ℝ) (rho s : ℂ) :
    deriv (periodizedZeroFactor N logp rho) s =
      (N : ℂ) * (logp : ℂ) *
        Complex.exp ((N : ℂ) * (logp : ℂ) * (rho - s)) := by
  let A : ℂ := (N : ℂ) * (logp : ℂ)
  change deriv (fun z : ℂ => 1 - Complex.exp (A * (rho - z))) s =
    A * Complex.exp (A * (rho - s))
  have hinner : HasDerivAt (fun z : ℂ => A * (rho - z)) (-A) s := by
    simpa using ((hasDerivAt_const s rho).sub (hasDerivAt_id s)).const_mul A
  have h := (hasDerivAt_const s (1 : ℂ)).sub hinner.cexp
  have hder : (0 : ℂ) - Complex.exp (A * (rho - s)) * (-A) =
      A * Complex.exp (A * (rho - s)) := by ring
  rw [show (fun z : ℂ => 1 - Complex.exp (A * (rho - z))) =
      (fun _ : ℂ => (1 : ℂ)) - fun z => Complex.exp (A * (rho - z)) by rfl]
  rw [h.deriv, hder]

theorem deriv_periodizedZeroFactor_ne_zero_at_zero
    {N : ℕ} {logp : ℝ} (hN : N ≠ 0) (hlogp : logp ≠ 0)
    {rho s : ℂ} (hzero : periodizedZeroFactor N logp rho s = 0) :
    deriv (periodizedZeroFactor N logp rho) s ≠ 0 := by
  rw [deriv_periodizedZeroFactor]
  have hexp : Complex.exp ((N : ℂ) * (logp : ℂ) * (rho - s)) = 1 := by
    unfold periodizedZeroFactor at hzero
    exact (sub_eq_zero.mp hzero).symm
  rw [hexp, mul_one]
  exact mul_ne_zero (by exact_mod_cast hN) (by exact_mod_cast hlogp)

theorem analyticOrderAt_periodizedZeroFactor_of_zero
    {N : ℕ} {logp : ℝ} (hN : N ≠ 0) (hlogp : logp ≠ 0)
    {rho z : ℂ} (hz : periodizedZeroFactor N logp rho z = 0) :
    analyticOrderAt (periodizedZeroFactor N logp rho) z = 1 :=
  (analyticAt_periodizedZeroFactor N logp rho z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    hz (deriv_periodizedZeroFactor_ne_zero_at_zero hN hlogp hz)

def periodizedDivisorProduct {ι : Type*} (s : Finset ι)
    (rho : ι → ℂ) (m : ι → ℕ) (N : ℕ) (logp : ℝ) (z : ℂ) : ℂ :=
  ∏ i ∈ s, (periodizedZeroFactor N logp (rho i) z) ^ m i

def periodizedDivisorMultiplicity {ι : Type*} (s : Finset ι)
    (rho : ι → ℂ) (m : ι → ℕ) (N : ℕ) (logp : ℝ) (z : ℂ) : ℕ∞ := by
  classical
  exact ∑ i ∈ s.filter (fun i => ∃ k : ℤ,
    z = rho i - (k : ℂ) * stackPeriod N logp), (m i : ℕ∞)

theorem periodizedDivisorProduct_periodic {ι : Type*} {s : Finset ι}
    {rho : ι → ℂ} {m : ι → ℕ} {N : ℕ} {logp : ℝ}
    (hN : N ≠ 0) (hlogp : logp ≠ 0) (z : ℂ) :
    periodizedDivisorProduct s rho m N logp (z + stackPeriod N logp) =
      periodizedDivisorProduct s rho m N logp z := by
  classical
  unfold periodizedDivisorProduct
  apply Finset.prod_congr rfl
  intro i hi
  rw [periodizedZeroFactor_periodic hN hlogp]

theorem analyticAt_periodizedDivisorProduct {ι : Type*} (s : Finset ι)
    (rho : ι → ℂ) (m : ι → ℕ) (N : ℕ) (logp : ℝ) (z : ℂ) :
    AnalyticAt ℂ (periodizedDivisorProduct s rho m N logp) z := by
  classical
  unfold periodizedDivisorProduct
  have hfun :
      (fun w : ℂ => ∏ i ∈ s, periodizedZeroFactor N logp (rho i) w ^ m i) =
        ∏ i ∈ s, (fun w : ℂ => periodizedZeroFactor N logp (rho i) w ^ m i) := by
    funext w
    simp only [Finset.prod_apply]
  rw [hfun]
  exact Finset.analyticAt_prod s (fun i hi =>
    (analyticAt_periodizedZeroFactor N logp (rho i) z).pow (m i))

theorem analyticOrderAt_periodizedDivisorProduct
    {ι : Type*} {s : Finset ι} {rho : ι → ℂ} {m : ι → ℕ}
    {N : ℕ} {logp : ℝ} (hN : N ≠ 0) (hlogp : logp ≠ 0) (z : ℂ) :
    analyticOrderAt (periodizedDivisorProduct s rho m N logp) z =
      periodizedDivisorMultiplicity s rho m N logp z := by
  classical
  unfold periodizedDivisorProduct periodizedDivisorMultiplicity
  have hprod := RHTower.analyticOrderAt_finsetProd z s
    (fun i w => periodizedZeroFactor N logp (rho i) w ^ m i)
    (fun i hi => (analyticAt_periodizedZeroFactor N logp (rho i) z).pow (m i))
  rw [hprod, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hAn := analyticAt_periodizedZeroFactor N logp (rho i) z
  have hpow :
      analyticOrderAt (fun w : ℂ => periodizedZeroFactor N logp (rho i) w ^ m i) z =
        m i • analyticOrderAt (periodizedZeroFactor N logp (rho i)) z := by
    have heq : (fun w : ℂ => periodizedZeroFactor N logp (rho i) w ^ m i) =
        (periodizedZeroFactor N logp (rho i)) ^ m i := by
      funext w
      rw [Pi.pow_apply]
    rw [heq, analyticOrderAt_pow hAn]
  rw [hpow]
  by_cases hz : periodizedZeroFactor N logp (rho i) z = 0
  · rw [if_pos ((periodizedZeroFactor_eq_zero_iff_lattice
        hN hlogp (rho i) z).mp hz),
      analyticOrderAt_periodizedZeroFactor_of_zero hN hlogp hz,
      nsmul_eq_mul, mul_one]
  · have hnot : ¬ ∃ k : ℤ, z = rho i - (k : ℂ) * stackPeriod N logp :=
      (not_congr (periodizedZeroFactor_eq_zero_iff_lattice
        hN hlogp (rho i) z)).mp hz
    rw [if_neg hnot,
      hAn.analyticOrderAt_eq_zero.mpr hz, smul_zero]

theorem periodizedDivisorProduct_eq_zero_iff_verticalLattice
    {ι : Type*} {s : Finset ι} {rho : ι → ℂ} {m : ι → ℕ}
    {N : ℕ} {logp : ℝ} (hN : N ≠ 0) (hlogp : logp ≠ 0)
    (hm : ∀ i ∈ s, 0 < m i) (z : ℂ) :
    periodizedDivisorProduct s rho m N logp z = 0 ↔
      ∃ i ∈ s, ∃ k : ℤ, z = rho i - (k : ℂ) * stackPeriod N logp := by
  classical
  unfold periodizedDivisorProduct
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, hi, hpow⟩
    have hfactor : periodizedZeroFactor N logp (rho i) z = 0 := by
      by_contra hne
      exact (pow_ne_zero (m i) hne) hpow
    exact ⟨i, hi, (periodizedZeroFactor_eq_zero_iff_lattice
      hN hlogp (rho i) z).mp hfactor⟩
  · rintro ⟨i, hi, k, hk⟩
    refine ⟨i, hi, ?_⟩
    rw [(periodizedZeroFactor_eq_zero_iff_lattice hN hlogp (rho i) z).2 ⟨k, hk⟩]
    exact zero_pow (Nat.ne_of_gt (hm i hi))

theorem analyticOrderAt_eq_of_zeroFree_factorizationOn
    {f g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U)
    (hh0 : ∀ z ∈ U, h z ≠ 0)
    (hfactor : ∀ z ∈ U, f z = g z * h z) {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt f z = analyticOrderAt g z := by
  have hev : f =ᶠ[nhds z] fun w => g w * h w := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hfactor w hw
  rw [analyticOrderAt_congr hev]
  change analyticOrderAt (g * h) z = analyticOrderAt g z
  rw [analyticOrderAt_mul (hg z hz) (hh z hz),
    (hh z hz).analyticOrderAt_eq_zero.mpr (hh0 z hz), add_zero]

/-- Exact constructive converse from Theorem 2(ii): an AP-invariant analytic divisor is
equivalent, on the same open neighborhood, to a periodic elementary factor times a holomorphic
zero-free remainder. -/
theorem periodizedDivisor_iff_exists_zeroFree_remainder
    {ι : Type*} {s : Finset ι} {rho : ι → ℂ} {m : ι → ℕ}
    {N : ℕ} {logp : ℝ} (hN : N ≠ 0) (hlogp : logp ≠ 0)
    {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U) :
    (∀ z ∈ U, analyticOrderAt F z =
      periodizedDivisorMultiplicity s rho m N logp z) ↔
      ∃ R : ℂ → ℂ,
        AnalyticOnNhd ℂ R U ∧ (∀ z ∈ U, R z ≠ 0) ∧
        ∀ z ∈ U, F z = periodizedDivisorProduct s rho m N logp z * R z := by
  classical
  let P : ℂ → ℂ := periodizedDivisorProduct s rho m N logp
  have hP : AnalyticOnNhd ℂ P U := fun z hz =>
    analyticAt_periodizedDivisorProduct s rho m N logp z
  constructor
  · intro hAP
    have hfinite : ∀ z ∈ U, analyticOrderAt F z ≠ ⊤ := by
      intro z hz
      rw [hAP z hz]
      simp [periodizedDivisorMultiplicity]
    have horder : ∀ z ∈ U, analyticOrderAt F z = analyticOrderAt P z := by
      intro z hz
      rw [hAP z hz]
      exact (analyticOrderAt_periodizedDivisorProduct hN hlogp z).symm
    obtain ⟨hR, hR0, hfactor⟩ :=
      GaloisForLFunctions.HTGeometry.localQuotientOn_analytic_nonvanishing_factorization
        hF hP hfinite horder
    refine ⟨GaloisForLFunctions.HTGeometry.localQuotientOn F P U, hR, hR0, ?_⟩
    intro z hz
    rw [hfactor z hz]
    exact mul_comm _ _
  · rintro ⟨R, hR, hR0, hfactor⟩
    intro z hz
    rw [analyticOrderAt_eq_of_zeroFree_factorizationOn hU hP hR hR0 hfactor hz]
    exact analyticOrderAt_periodizedDivisorProduct hN hlogp z

end GaloisForLFunctions.RHTower.PeriodizedDivisorFactorization
