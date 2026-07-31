import GaloisForLFunctions.RHTower.BlaschkeLocalizedClockAsymptotic
import GaloisForLFunctions.RHTower.MaximalRealDiagonalSelfAdjoint

/-!
# Self-adjoint Hamiltonian realization of the Blaschke return clock

The countable phase packet is realized as the survival amplitude of one
normalized state under one fixed self-adjoint diagonal Hamiltonian on
`ℓ²(ℕ)`.  Integer-time Schrödinger phases agree exactly with the torus
phases used by the first-return theorem.
-/

open scoped BigOperators InnerProductSpace LinearPMap
open Complex
open MeasureTheory Filter Topology

noncomputable section

namespace RHTower

/-- Hilbert space carrying the countably infinite Blaschke packet. -/
abbrev BlaschkePhaseSpace := DiagonalL2 ℕ

/-- The real energy represented by one additive-circle phase.  The minus
sign makes standard `exp (-i t H)` evolution agree with the positive
Fourier clock convention. -/
def blaschkePhaseEnergy (x : ℕ → UnitAddCircle) (k : ℕ) : ℝ :=
  -torusRealFrequency (x k)

/-- One fixed self-adjoint Hamiltonian associated with the phase packet. -/
def blaschkePhaseHamiltonian (x : ℕ → UnitAddCircle) :
    BlaschkePhaseSpace →ₗ.[ℂ] BlaschkePhaseSpace :=
  maximalRealDiagonal (blaschkePhaseEnergy x)

theorem blaschkePhaseHamiltonian_selfAdjoint
    (x : ℕ → UnitAddCircle) :
    IsSelfAdjoint (blaschkePhaseHamiltonian x) :=
  maximalRealDiagonal_isSelfAdjoint _

theorem blaschkeLocalizedWeight_nonneg (a : ℝ) (k : ℕ) :
    0 ≤ blaschkeLocalizedWeight a k :=
  sq_nonneg _

theorem blaschkeLocalizedWeight_summable
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (blaschkeLocalizedWeight a) := by
  change Summable (fun k : ℕ => blaschkeLocalizedKernel a k ^ 2)
  exact blaschkeLocalizedKernel_sq_summable a ha0 ha1

/-- Normalized state whose Born weights are the exact Blaschke local
spectral weights. -/
def blaschkePhaseKet
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    BlaschkePhaseSpace :=
  ⟨fun k => (Real.sqrt (blaschkeLocalizedWeight a k) : ℂ),
    HilbertSchmidt.memℓp_of_sq (by
      apply (blaschkeLocalizedWeight_summable a ha0 ha1).congr
      intro k
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (blaschkeLocalizedWeight_nonneg a k)])⟩

@[simp] theorem blaschkePhaseKet_apply
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (k : ℕ) :
    blaschkePhaseKet a ha0 ha1 k =
      (Real.sqrt (blaschkeLocalizedWeight a k) : ℂ) :=
  rfl

/-- Coordinate phase of standard Schrödinger evolution under
`blaschkePhaseHamiltonian`. -/
def blaschkeHamiltonianEvolutionPhase
    (x : ℕ → UnitAddCircle) (t : ℝ) (k : ℕ) : ℂ :=
  Complex.exp
    (((-t * blaschkePhaseEnergy x k : ℝ) : ℂ) * Complex.I)

theorem blaschkeHamiltonianEvolutionPhase_norm
    (x : ℕ → UnitAddCircle) (t : ℝ) (k : ℕ) :
    ‖blaschkeHamiltonianEvolutionPhase x t k‖ = 1 := by
  rw [blaschkeHamiltonianEvolutionPhase]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Exact diagonal Schrödinger orbit of the Blaschke state. -/
def blaschkePhaseKetAt
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (t : ℝ) :
    BlaschkePhaseSpace :=
  ⟨fun k =>
      (Real.sqrt (blaschkeLocalizedWeight a k) : ℂ) *
        blaschkeHamiltonianEvolutionPhase x t k,
    HilbertSchmidt.memℓp_of_sq (by
      apply (blaschkeLocalizedWeight_summable a ha0 ha1).congr
      intro k
      rw [norm_mul, blaschkeHamiltonianEvolutionPhase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (blaschkeLocalizedWeight_nonneg a k)])⟩

@[simp] theorem blaschkePhaseKetAt_apply
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (t : ℝ) (k : ℕ) :
    blaschkePhaseKetAt a ha0 ha1 x t k =
      (Real.sqrt (blaschkeLocalizedWeight a k) : ℂ) *
        blaschkeHamiltonianEvolutionPhase x t k :=
  rfl

theorem blaschkePhaseKetAt_zero
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) :
    blaschkePhaseKetAt a ha0 ha1 x 0 =
      blaschkePhaseKet a ha0 ha1 := by
  apply lp.ext
  funext k
  simp [blaschkeHamiltonianEvolutionPhase]

theorem blaschkePhaseKet_norm
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ‖blaschkePhaseKet a ha0 ha1‖ = 1 := by
  have hnormsq : ‖blaschkePhaseKet a ha0 ha1‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rw [show (∑' k : ℕ, ‖blaschkePhaseKet a ha0 ha1 k‖ ^ 2) =
        ∑' k : ℕ, blaschkeLocalizedWeight a k by
      apply tsum_congr
      intro k
      rw [blaschkePhaseKet_apply, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (blaschkeLocalizedWeight_nonneg a k)]]
    exact blaschkeLocalizedWeight_tsum a ha0 ha1
  nlinarith [norm_nonneg (blaschkePhaseKet a ha0 ha1)]

theorem blaschkePhaseKetAt_norm
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (t : ℝ) :
    ‖blaschkePhaseKetAt a ha0 ha1 x t‖ = 1 := by
  have hnormsq : ‖blaschkePhaseKetAt a ha0 ha1 x t‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rw [show (∑' k : ℕ,
        ‖blaschkePhaseKetAt a ha0 ha1 x t k‖ ^ 2) =
        ∑' k : ℕ, blaschkeLocalizedWeight a k by
      apply tsum_congr
      intro k
      rw [blaschkePhaseKetAt_apply, norm_mul,
        blaschkeHamiltonianEvolutionPhase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (blaschkeLocalizedWeight_nonneg a k)]]
    exact blaschkeLocalizedWeight_tsum a ha0 ha1
  nlinarith [norm_nonneg (blaschkePhaseKetAt a ha0 ha1 x t)]

/-- The Hilbert-space survival amplitude is exactly the weighted spectral
phase sum. -/
theorem blaschkePhaseKet_inner_ketAt
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (t : ℝ) :
    inner ℂ (blaschkePhaseKet a ha0 ha1)
        (blaschkePhaseKetAt a ha0 ha1 x t) =
      summableWeightedPhaseAmplitude
        (blaschkeLocalizedWeight a)
        (blaschkeHamiltonianEvolutionPhase x t) := by
  rw [lp.inner_eq_tsum, summableWeightedPhaseAmplitude]
  apply tsum_congr
  intro k
  rw [blaschkePhaseKet_apply, blaschkePhaseKetAt_apply,
    RCLike.inner_apply, Complex.conj_ofReal]
  calc
    (Real.sqrt (blaschkeLocalizedWeight a k) : ℂ) *
          blaschkeHamiltonianEvolutionPhase x t k *
        (Real.sqrt (blaschkeLocalizedWeight a k) : ℂ) =
      ((Real.sqrt (blaschkeLocalizedWeight a k) ^ 2 : ℝ) : ℂ) *
        blaschkeHamiltonianEvolutionPhase x t k := by
          push_cast
          ring
    _ = _ := by
      rw [Real.sq_sqrt (blaschkeLocalizedWeight_nonneg a k)]

/-- Integer-time Schrödinger phases are exactly the torus Fourier clocks. -/
theorem blaschkeHamiltonianEvolutionPhase_nat
    (x : ℕ → UnitAddCircle) (n k : ℕ) :
    blaschkeHamiltonianEvolutionPhase x n k =
      fourier 1 (((n : ℕ) : ℤ) • x k) := by
  rw [blaschkeHamiltonianEvolutionPhase, blaschkePhaseEnergy]
  calc
    Complex.exp
        (((-(n : ℝ) * -torusRealFrequency (x k) : ℝ) : ℂ) *
          Complex.I) =
      Complex.exp
        (Complex.I *
          ((((n : ℝ) * torusRealFrequency (x k) : ℝ) : ℂ))) := by
            congr 1
            push_cast
            ring
    _ = _ := exp_torusRealFrequency_eq_fourier_zsmul (x k) n

/--
At every positive integer time, the coherence predicate defining the
first-return theorem is exactly the survival-amplitude return of the
self-adjoint Hamiltonian and normalized state above.
-/
theorem countableTorusWeightedCoherenceAt_blaschke_iff_hamiltonian
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (η : ℝ) (n : ℕ) :
    CountableTorusWeightedCoherenceAt
        (blaschkeLocalizedWeight a) x η n ↔
      0 < n ∧
        1 - η ≤
          ‖inner ℂ (blaschkePhaseKet a ha0 ha1)
            (blaschkePhaseKetAt a ha0 ha1 x n)‖ := by
  rw [CountableTorusWeightedCoherenceAt,
    blaschkePhaseKet_inner_ketAt]
  have heq :
      summableWeightedPhaseAmplitude
          (blaschkeLocalizedWeight a)
          (blaschkeHamiltonianEvolutionPhase x n) =
        summableWeightedPhaseAmplitude
          (blaschkeLocalizedWeight a)
          (fun k => fourier 1 (((n : ℕ) : ℤ) • x k)) := by
    rw [summableWeightedPhaseAmplitude,
      summableWeightedPhaseAmplitude]
    apply tsum_congr
    intro k
    rw [blaschkeHamiltonianEvolutionPhase_nat]
  rw [heq]

/-- Positive-time survival return for the realized Hamiltonian and state. -/
def BlaschkeHamiltonianCoherenceAt
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (η : ℝ) (n : ℕ) : Prop :=
  0 < n ∧
    1 - η ≤
      ‖inner ℂ (blaschkePhaseKet a ha0 ha1)
        (blaschkePhaseKetAt a ha0 ha1 x n)‖

/-- Actual first positive survival return of the self-adjoint Hamiltonian,
with value `∞` if no return exists. -/
noncomputable def blaschkeHamiltonianFirstReturnTime
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (η : ℝ) : WithTop ℕ := by
  classical
  exact if h : ∃ n,
      BlaschkeHamiltonianCoherenceAt a ha0 ha1 x η n then
    (Nat.find h : WithTop ℕ)
  else ⊤

theorem blaschkeHamiltonianFirstReturnTime_eq_countable
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (η : ℝ) :
    blaschkeHamiltonianFirstReturnTime a ha0 ha1 x η =
      countableTorusWeightedFirstCoherenceTime
        (blaschkeLocalizedWeight a) x η := by
  classical
  have hiff : ∀ n : ℕ,
      BlaschkeHamiltonianCoherenceAt a ha0 ha1 x η n ↔
        CountableTorusWeightedCoherenceAt
          (blaschkeLocalizedWeight a) x η n := by
    intro n
    exact
      (countableTorusWeightedCoherenceAt_blaschke_iff_hamiltonian
        a ha0 ha1 x η n).symm
  by_cases hc : ∃ n,
      CountableTorusWeightedCoherenceAt
        (blaschkeLocalizedWeight a) x η n
  · have hh : ∃ n,
        BlaschkeHamiltonianCoherenceAt a ha0 ha1 x η n := by
      obtain ⟨n, hn⟩ := hc
      exact ⟨n, (hiff n).2 hn⟩
    rw [blaschkeHamiltonianFirstReturnTime,
      countableTorusWeightedFirstCoherenceTime, dif_pos hh, dif_pos hc]
    congr 1
    apply le_antisymm
    · exact Nat.find_min' hh ((hiff (Nat.find hc)).2 (Nat.find_spec hc))
    · exact Nat.find_min' hc ((hiff (Nat.find hh)).1 (Nat.find_spec hh))
  · have hh : ¬∃ n,
        BlaschkeHamiltonianCoherenceAt a ha0 ha1 x η n := by
      intro h
      obtain ⟨n, hn⟩ := h
      exact hc ⟨n, (hiff n).1 hn⟩
    rw [blaschkeHamiltonianFirstReturnTime,
      countableTorusWeightedFirstCoherenceTime, dif_neg hh, dif_neg hc]

/-- Nat-valued physical first return at the logarithmic target scale. -/
noncomputable def blaschkeHamiltonianFirstReturnClock
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (K : ℝ) (k : ℕ) : ℕ :=
  WithTop.untopD 0
    (blaschkeHamiltonianFirstReturnTime a ha0 ha1 x
      (Real.exp (-blaschkeShiftedScale K k)))

theorem blaschkeHamiltonianFirstReturnClock_eq
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (x : ℕ → UnitAddCircle) (K : ℝ) (k : ℕ) :
    blaschkeHamiltonianFirstReturnClock a ha0 ha1 x K k =
      blaschkeFirstReturnClock a x K k := by
  rw [blaschkeHamiltonianFirstReturnClock, blaschkeFirstReturnClock,
    blaschkeHamiltonianFirstReturnTime_eq_countable]

/--
Exact almost-sure quantum survival-return law for one normalized state
under one self-adjoint Hamiltonian on a countably infinite Hilbert space.
-/
theorem ae_tendsto_blaschkeHamiltonianFirstReturnClock_normalized
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
          (volume : Measure UnitAddCircle)),
      Tendsto (fun k : ℕ =>
        Real.log
            (blaschkeHamiltonianFirstReturnClock
              a ha0 ha1 x K k : ℝ) /
          (k : ℝ) ^ 2)
        atTop (𝓝 (1 / (4 * blaschkeSpectralSlope a))) := by
  filter_upwards [
    ae_tendsto_blaschkeFirstReturnClock_normalized
      a ha0 ha1 hKtail hKzero hKnonneg] with x hx
  simpa only [blaschkeHamiltonianFirstReturnClock_eq] using hx

end RHTower
