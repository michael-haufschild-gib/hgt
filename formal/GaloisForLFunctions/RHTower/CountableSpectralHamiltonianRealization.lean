import GaloisForLFunctions.RHTower.CountableSpectralDepthFirstReturnLaw
import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint

/-!
# Hamiltonian realization of the universal countable spectral-depth law

Every normalized nonnegative summable weight sequence is realized as the
Born spectral measure of a normalized state for a self-adjoint diagonal
Hamiltonian on `ℓ²(ℕ)`. Its integer-time survival amplitude is exactly the
countable phase packet controlled by the spectral-depth law.
-/

open scoped BigOperators InnerProductSpace LinearPMap
open Complex

noncomputable section

namespace RHTower

/-- Countably infinite Hilbert space carrying an arbitrary pure-point
spectral packet. -/
abbrev CountableSpectralPhaseSpace := DiagonalL2 ℕ

/-- Real energy represented by one additive-circle phase. -/
def countableSpectralPhaseEnergy
    (x : ℕ → UnitAddCircle) (k : ℕ) : ℝ :=
  -torusRealFrequency (x k)

/-- Self-adjoint diagonal Hamiltonian associated with the phase packet. -/
def countableSpectralPhaseHamiltonian
    (x : ℕ → UnitAddCircle) :
    CountableSpectralPhaseSpace →ₗ.[ℂ]
      CountableSpectralPhaseSpace :=
  maximalRealDiagonal (countableSpectralPhaseEnergy x)

theorem countableSpectralPhaseHamiltonian_selfAdjoint
    (x : ℕ → UnitAddCircle) :
    IsSelfAdjoint (countableSpectralPhaseHamiltonian x) :=
  maximalRealDiagonal_isSelfAdjoint _

/-- State whose Born weights are the given countable spectral weights. -/
def countableSpectralKet
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p) :
    CountableSpectralPhaseSpace :=
  ⟨fun k => (Real.sqrt (p k) : ℂ),
    HilbertSchmidt.memℓp_of_sq (by
      apply hsum.congr
      intro k
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hp k)])⟩

@[simp] theorem countableSpectralKet_apply
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (k : ℕ) :
    countableSpectralKet p hp hsum k =
      (Real.sqrt (p k) : ℂ) :=
  rfl

/-- Coordinate phase of standard Schrödinger evolution. -/
def countableSpectralHamiltonianEvolutionPhase
    (x : ℕ → UnitAddCircle) (t : ℝ) (k : ℕ) : ℂ :=
  Complex.exp
    (((-t * countableSpectralPhaseEnergy x k : ℝ) : ℂ) *
      Complex.I)

theorem countableSpectralHamiltonianEvolutionPhase_norm
    (x : ℕ → UnitAddCircle) (t : ℝ) (k : ℕ) :
    ‖countableSpectralHamiltonianEvolutionPhase x t k‖ = 1 := by
  rw [countableSpectralHamiltonianEvolutionPhase]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Exact diagonal Schrödinger orbit of the spectral state. -/
def countableSpectralKetAt
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) (t : ℝ) :
    CountableSpectralPhaseSpace :=
  ⟨fun k =>
      (Real.sqrt (p k) : ℂ) *
        countableSpectralHamiltonianEvolutionPhase x t k,
    HilbertSchmidt.memℓp_of_sq (by
      apply hsum.congr
      intro k
      rw [norm_mul,
        countableSpectralHamiltonianEvolutionPhase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hp k)])⟩

@[simp] theorem countableSpectralKetAt_apply
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) (t : ℝ) (k : ℕ) :
    countableSpectralKetAt p hp hsum x t k =
      (Real.sqrt (p k) : ℂ) *
        countableSpectralHamiltonianEvolutionPhase x t k :=
  rfl

theorem countableSpectralKet_norm
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (htotal : ∑' k, p k = 1) :
    ‖countableSpectralKet p hp hsum‖ = 1 := by
  have hnormsq : ‖countableSpectralKet p hp hsum‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rw [show (∑' k : ℕ, ‖countableSpectralKet p hp hsum k‖ ^ 2) =
        ∑' k : ℕ, p k by
      apply tsum_congr
      intro k
      rw [countableSpectralKet_apply, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hp k)]]
    exact htotal
  nlinarith [norm_nonneg (countableSpectralKet p hp hsum)]

theorem countableSpectralKetAt_norm
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (htotal : ∑' k, p k = 1)
    (x : ℕ → UnitAddCircle) (t : ℝ) :
    ‖countableSpectralKetAt p hp hsum x t‖ = 1 := by
  have hnormsq :
      ‖countableSpectralKetAt p hp hsum x t‖ ^ 2 = 1 := by
    rw [HilbertSchmidt.lp_norm_sq_eq]
    rw [show (∑' k : ℕ,
        ‖countableSpectralKetAt p hp hsum x t k‖ ^ 2) =
        ∑' k : ℕ, p k by
      apply tsum_congr
      intro k
      rw [countableSpectralKetAt_apply, norm_mul,
        countableSpectralHamiltonianEvolutionPhase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hp k)]]
    exact htotal
  nlinarith [norm_nonneg
    (countableSpectralKetAt p hp hsum x t)]

/-- Survival amplitude equals the weighted spectral phase sum. -/
theorem countableSpectralKet_inner_ketAt
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) (t : ℝ) :
    inner ℂ (countableSpectralKet p hp hsum)
        (countableSpectralKetAt p hp hsum x t) =
      summableWeightedPhaseAmplitude p
        (countableSpectralHamiltonianEvolutionPhase x t) := by
  rw [lp.inner_eq_tsum, summableWeightedPhaseAmplitude]
  apply tsum_congr
  intro k
  rw [countableSpectralKet_apply, countableSpectralKetAt_apply,
    RCLike.inner_apply, Complex.conj_ofReal]
  calc
    (Real.sqrt (p k) : ℂ) *
          countableSpectralHamiltonianEvolutionPhase x t k *
        (Real.sqrt (p k) : ℂ) =
      ((Real.sqrt (p k) ^ 2 : ℝ) : ℂ) *
        countableSpectralHamiltonianEvolutionPhase x t k := by
          push_cast
          ring
    _ = _ := by rw [Real.sq_sqrt (hp k)]

theorem countableSpectralHamiltonianEvolutionPhase_nat
    (x : ℕ → UnitAddCircle) (n k : ℕ) :
    countableSpectralHamiltonianEvolutionPhase x n k =
      fourier 1 (((n : ℕ) : ℤ) • x k) := by
  rw [countableSpectralHamiltonianEvolutionPhase,
    countableSpectralPhaseEnergy]
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
The abstract coherence predicate is exactly survival-amplitude recurrence
of a normalized state under a self-adjoint Hamiltonian.
-/
theorem countableTorusWeightedCoherenceAt_iff_hamiltonian
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) (eta : ℝ) (n : ℕ) :
    CountableTorusWeightedCoherenceAt p x eta n ↔
      0 < n ∧
        1 - eta ≤
          ‖inner ℂ (countableSpectralKet p hp hsum)
            (countableSpectralKetAt p hp hsum x n)‖ := by
  rw [CountableTorusWeightedCoherenceAt,
    countableSpectralKet_inner_ketAt]
  have heq :
      summableWeightedPhaseAmplitude p
          (countableSpectralHamiltonianEvolutionPhase x n) =
        summableWeightedPhaseAmplitude p
          (fun k => fourier 1 (((n : ℕ) : ℤ) • x k)) := by
    rw [summableWeightedPhaseAmplitude,
      summableWeightedPhaseAmplitude]
    apply tsum_congr
    intro k
    rw [countableSpectralHamiltonianEvolutionPhase_nat]
  rw [heq]

/-- Physical survival-return predicate. -/
def CountableSpectralHamiltonianCoherenceAt
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) (eta : ℝ) (n : ℕ) : Prop :=
  0 < n ∧
    1 - eta ≤
      ‖inner ℂ (countableSpectralKet p hp hsum)
        (countableSpectralKetAt p hp hsum x n)‖

/-- Actual first positive survival return, with `∞` if none exists. -/
noncomputable def countableSpectralHamiltonianFirstReturnTime
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) (eta : ℝ) : WithTop ℕ := by
  classical
  exact if h : ∃ n,
      CountableSpectralHamiltonianCoherenceAt
        p hp hsum x eta n then
    (Nat.find h : WithTop ℕ)
  else ⊤

theorem countableSpectralHamiltonianFirstReturnTime_eq
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (x : ℕ → UnitAddCircle) (eta : ℝ) :
    countableSpectralHamiltonianFirstReturnTime
        p hp hsum x eta =
      countableTorusWeightedFirstCoherenceTime p x eta := by
  classical
  have hiff : ∀ n : ℕ,
      CountableSpectralHamiltonianCoherenceAt
          p hp hsum x eta n ↔
        CountableTorusWeightedCoherenceAt p x eta n := by
    intro n
    exact
      (countableTorusWeightedCoherenceAt_iff_hamiltonian
        p hp hsum x eta n).symm
  by_cases hc : ∃ n, CountableTorusWeightedCoherenceAt p x eta n
  · have hh : ∃ n,
        CountableSpectralHamiltonianCoherenceAt
          p hp hsum x eta n := by
      obtain ⟨n, hn⟩ := hc
      exact ⟨n, (hiff n).2 hn⟩
    rw [countableSpectralHamiltonianFirstReturnTime,
      countableTorusWeightedFirstCoherenceTime, dif_pos hh, dif_pos hc]
    congr 1
    apply le_antisymm
    · exact Nat.find_min' hh ((hiff (Nat.find hc)).2 (Nat.find_spec hc))
    · exact Nat.find_min' hc ((hiff (Nat.find hh)).1 (Nat.find_spec hh))
  · have hh : ¬∃ n,
        CountableSpectralHamiltonianCoherenceAt
          p hp hsum x eta n := by
      intro h
      obtain ⟨n, hn⟩ := h
      exact hc ⟨n, (hiff n).1 hn⟩
    rw [countableSpectralHamiltonianFirstReturnTime,
      countableTorusWeightedFirstCoherenceTime, dif_neg hh, dif_neg hc]

/--
Universal deterministic survival-return law for arbitrary normalized
countable pure-point spectra.
-/
theorem exists_countableSpectralHamiltonianFirstReturnDeadline
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hmass : 0 < summableWeightedHeadMass p M)
    (pivot : Fin M)
    {eta lam : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hlam : 0 < lam)
    (hwater :
      projectiveWaterMass
          (normalizedWeightedHeadWeight p M) pivot
          (summableWeightedHeadMass p M * lam) ≤ eta) :
    ∃ T : ℕ,
      (∀ x : ℕ → UnitAddCircle,
        countableSpectralHamiltonianFirstReturnTime p hp hsum x
            (countableSpectralDepthDefect p M eta) ≤ T) ∧
      Real.log (T : ℝ) ≤
        countableSpectralDepthEntropy p M lam +
          countableSpectralDepthResolutionCost M := by
  obtain ⟨T, hfirst, hlog⟩ :=
    exists_countableSpectralDepthFirstReturnDeadline
      p hp hsum htotal M hM hmass pivot
      heta0 heta1 hlam hwater
  refine ⟨T, ?_, hlog⟩
  intro x
  rw [countableSpectralHamiltonianFirstReturnTime_eq]
  exact hfirst x

end RHTower
