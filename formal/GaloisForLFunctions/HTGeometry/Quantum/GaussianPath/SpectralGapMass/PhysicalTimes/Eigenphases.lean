import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.TraceDecay
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.RHTower.PrimeCirclePeriodization
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Haar eigenphase distribution at positive physical dates -/
open MeasureTheory Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open _root_.RHTower.PrimeCirclePeriodization
noncomputable section

/-- Each Hamiltonian eigenvalue contributes one atom, with multiplicity,
at the angle of its physical eigenphase in radians. -/
def eigenphaseLaw {n : ℕ} (u : PathShell n) (t : ℝ) : ProbabilityMeasure (AddCircle (2*Real.pi)) :=
  let μ : ProbabilityMeasure (Fin (n+2) → Bool) := ⟨(PMF.uniformOfFintype _).toMeasure,inferInstance⟩
  μ.map (f:=fun j => phase (-t) ((isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j))
    (measurable_of_finite _).aemeasurable

/-- The kth empirical Fourier coefficient is the physical trace amplitude at kt. -/
theorem eigenphase_moment (ω : PathPauliDisorder) (n : ℕ) (t : ℝ) (k : ℤ) :
    (∫ z, fourier k z ∂(eigenphaseLaw (pathPauliDisorderShell ω n) t : Measure (AddCircle (2*Real.pi)))) =
      amplitude ω n (k*t) := by
  let u := pathPauliDisorderShell ω n
  let h := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let V := h.eigenvectorUnitary.val
  let f (j) := Complex.exp (-(Complex.I*((((k:ℝ)*t:ℝ):ℂ)*h.eigenvalues j)))
  have htrace : (unitaryEvolution (pathHamiltonian u) (k*t)).trace = ∑ j, f j := by
    rw [unitaryEvolution_spectral h]
    change (V*diagonal f*star V).trace=_
    rw [Matrix.trace_mul_cycle,show star V*V=1 from h.eigenvectorUnitary.property.1,one_mul,
      Matrix.trace_diagonal]
  rw [eigenphaseLaw,ProbabilityMeasure.toMeasure_map,integral_map
    (measurable_of_finite _).aemeasurable (fourier k).continuous.aestronglyMeasurable]
  change (∫ i, fourier k (phase (-t) (h.eigenvalues i)) ∂(PMF.uniformOfFintype _).toMeasure) =
    (unitaryEvolution (pathHamiltonian u) (k*t)).trace / (2:ℂ)^(n+2)
  rw [PMF.integral_eq_sum,htrace]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,Complex.real_smul,
    Complex.ofReal_inv,←Finset.mul_sum,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,div_eq_inv_mul]
  congr 1
  · simp
  apply Finset.sum_congr rfl
  intro i _
  rw [fourier_phase]
  dsimp only [f]
  congr 1
  push_cast
  ring

/-- Haar probability on the circle of physical eigenphase angles. -/
def uniformAngles : ProbabilityMeasure (AddCircle (2*Real.pi)) := ⟨AddCircle.haarAddCircle,inferInstance⟩

/-- Vanishing positive Fourier moments determine Haar probability on the circle. -/
theorem haar_of_positive_moments (μ : ℕ → ProbabilityMeasure (AddCircle (2*Real.pi)))
    (h : ∀ k : ℕ, Tendsto (fun n => ∫ z, fourier ((k+1:ℕ):ℤ) z ∂(μ n : Measure (AddCircle (2*Real.pi))))
      atTop (𝓝 0)) : Tendsto μ atTop (𝓝 uniformAngles) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ν hν
  apply ProbabilityMeasure.toMeasure_injective
  apply addCircle_measure_eq_of_nat_fourier_integral_eq
  intro k
  cases k with
  | zero => simp
  | succ k =>
    let F (ρ : ProbabilityMeasure (AddCircle (2*Real.pi))) :=
      ∫ z, fourier ((k+1:ℕ):ℤ) z ∂(ρ : Measure (AddCircle (2*Real.pi)))
    have hF := hν.continuousAt_comp
      (continuous_integral_complex_continuousMap (fourier ((k+1:ℕ):ℤ))).continuousAt
    have he : Tendsto (F ∘ μ) atTop (𝓝 0) := h k
    have hz : F ν=0 := eq_of_mapClusterPt_of_tendsto hF he
    change F ν = ∫ z, fourier ((k+1:ℕ):ℤ) z ∂AddCircle.haarAddCircle
    rw [hz,integral_fourier_haar,if_neg (by positivity)]

/-- Almost surely on the infinite Gaussian chain, every sequence of
observation dates in a compact positive interval gives the same weak limit
of the empirical eigenphase measures. Dates may depend on the entire chain. -/
theorem gaussian_eigenphase_haar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0<a → ∀ t : ℕ→ℝ,
      (∀ᶠ n in atTop, t n∈Icc a T) →
      Tendsto (fun n => eigenphaseLaw (pathPauliDisorderShell ω n) (t n)) atTop (𝓝 uniformAngles) := by
  filter_upwards [gaussian_trace_along_dates] with ω hω
  intro a T ha t ht
  let μ (n) := eigenphaseLaw (pathPauliDisorderShell ω n) (t n)
  apply haar_of_positive_moments μ
  intro k
  let j : ℝ := (k+1:ℕ)
  have hj : 0<j := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hconv := hω (j*a) (j*T) (mul_pos hj ha) (fun n => j*t n) (ht.mono fun _ hn =>
    ⟨mul_le_mul_of_nonneg_left hn.1 hj.le,mul_le_mul_of_nonneg_left hn.2 hj.le⟩)
  simpa only [μ,eigenphase_moment,Int.cast_natCast,j] using hconv

#print axioms gaussian_eigenphase_haar
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
