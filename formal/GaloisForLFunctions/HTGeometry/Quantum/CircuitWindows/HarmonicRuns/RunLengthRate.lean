import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.SharpRate

/-! # The price of a long run at physical gate error one tenth -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
open SharpOccupation

/-- If m(s+1)=o(D/N), persisting at s gates for the first m multiples pays
the factor m to the power 1−D, between two explicit exponential factors.
The schedules and the observation origin may depend on the Gaussian draw. -/
theorem gaussian_physical_run_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s m : ℕ → ℕ,
      (∀ n, 0 < m n) → subcriticalBudget (fun n => m n*(s n+1)) →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let M := m N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          let f := volume.real (circuitRunSet H (s N) M (1/10) ∩ Icc a T)/(T-a)
          (1/64:ℝ)^D/(M:ℝ)^(D-1) < f ∧ f < (1/4:ℝ)^D/(M:ℝ)^(D-1) := by
  filter_upwards [gaussian_sharp_run_rate] with ω hω
  intro s m hm hsub
  have hε : (1/10:ℝ) < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [h,Real.sqrt_nonneg 2]
  obtain ⟨hx,htol⟩ := physicalArc_spec (by norm_num : (0:ℝ)<1/10) hε
  have hsmall : zeroGateArcTolerance (1/64) < (1/10:ℝ) := by
    have hsin := Real.sin_le (show 0 ≤ Real.pi*(1/64)/2 by positivity)
    dsimp only [zeroGateArcTolerance]
    linarith only [hsin,Real.pi_lt_four]
  have hlarge : (1/10:ℝ) < zeroGateArcTolerance (1/8) :=
    (by norm_num : (1/10:ℝ) < 3*(1/8)).trans_le (three_mul_le_arcTolerance (by norm_num) (by norm_num))
  have hl : 1/64 < physicalArc (1/10) := (strictMonoOn_zeroGateArcTolerance.lt_iff_lt
    (by norm_num) ⟨hx.1.le,hx.2.le⟩).mp (by rw [htol]; exact hsmall)
  have hu : physicalArc (1/10) < 1/8 := (strictMonoOn_zeroGateArcTolerance.lt_iff_lt
    ⟨hx.1.le,hx.2.le⟩ (by norm_num)).mp (by rw [htol]; exact hlarge)
  have h := hω s m hm hsub _ ⟨hx.1,hu.trans (by norm_num)⟩ (1/64) (1/4)
    (by norm_num) hl (hu.trans (by norm_num))
  rwa [htol] at h

private theorem half_exponential_schedule (p : ℕ) :
    subcriticalBudget (fun n => (2^(n/2))*(n^p+1)) := by
  let a := Real.sqrt 2
  have ha2 : a^2 = 2 := Real.sq_sqrt (by norm_num)
  have ha : 1 < a := by
    have h := Real.sqrt_nonneg 2
    dsimp [a] at *
    nlinarith only [h,ha2]
  have hl := (tendsto_pow_const_div_const_pow_of_one_lt (p+1) ha).const_mul (6:ℝ)
  rw [mul_zero] at hl
  unfold subcriticalBudget
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _ hl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hpow : 1 ≤ (n:ℝ)^p := one_le_pow₀ h1
  have hhalf : (2:ℝ)^(n/2) ≤ a^n := by
    rw [←ha2,←pow_mul]
    exact pow_le_pow_right₀ ha.le (by omega)
  have hfull : (2:ℝ)^n = a^n*a^n := by rw [←mul_pow,←sq,ha2]
  have halfpos : 0 < a^n := pow_pos (zero_lt_one.trans ha) _
  have hnum : ((n:ℝ)+1)*((2:ℝ)^(n/2)*((n:ℝ)^p+1)+1) ≤ 6*(n:ℝ)^(p+1)*a^n := by
    have h2 : (2:ℝ)^(n/2)*((n:ℝ)^p+1)+1 ≤ a^n*((n:ℝ)^p+2) := by
      have hmain := mul_le_mul_of_nonneg_right hhalf (by positivity : 0 ≤ (n:ℝ)^p+1)
      have hh := one_le_pow₀ ha.le (n := n)
      nlinarith only [hmain,hh]
    have hpoly := mul_le_mul (by linarith only [h1] : (n:ℝ)+1 ≤ 2*n)
      (by linarith only [hpow] : (n:ℝ)^p+2 ≤ 3*n^p) (by positivity) (by positivity)
    calc
      _ ≤ ((n:ℝ)+1)*(a^n*((n:ℝ)^p+2)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (((n:ℝ)+1)*((n:ℝ)^p+2))*a^n := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right hpoly halfpos.le).trans_eq (by rw [pow_succ]; ring)
  push_cast
  rw [hfull]
  apply (div_le_iff₀ (mul_pos halfpos halfpos)).mpr
  exact hnum.trans_eq (by field_simp)

/-- For any polynomial gate budget, requiring affordability for 2^⌊N/2⌋
harmonics has long-time fraction between two explicit multiples of
(2^⌊N/2⌋)^(1−D). Their logarithms differ by at most a constant times D. -/
theorem gaussian_polynomial_exponential_runs :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ p : ℕ, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let M := (2:ℕ)^(N/2)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        let f := volume.real (circuitRunSet H (N^p) M (1/10) ∩ Icc a T)/(T-a)
        (1/64:ℝ)^D/(M:ℝ)^(D-1) < f ∧ f < (1/4:ℝ)^D/(M:ℝ)^(D-1) := by
  filter_upwards [gaussian_physical_run_rate] with ω hω
  intro p
  exact hω (fun n => n^p) (fun n => 2^(n/2))
    (fun n => Nat.pow_pos (by decide : 0 < 2)) (half_exponential_schedule p)

#print axioms gaussian_polynomial_exponential_runs
#print axioms gaussian_physical_run_rate
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
