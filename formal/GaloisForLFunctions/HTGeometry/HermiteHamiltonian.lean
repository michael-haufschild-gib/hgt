import GaloisForLFunctions.HTGeometry.HermiteCoefficientDecay

/-!
# The oscillator Hamiltonian and its seminorms

The symmetric combination `(A B + B A)/2` of the creation and annihilation operators is the number
operator shifted by `2π`, because the commutator is `4π`.  Its eigenvalue on the `n`-th Hermite
function is `2π(2n+1)`, which never vanishes — unlike the eigenvalue of the number operator itself.
So the Hamiltonian gives a decay estimate for the Hermite coefficients that is meaningful at every
index, including the ground state.

Its powers give an increasing family of Hilbertian seminorms `qₖ(f) = ‖Hᵏf‖₂` on the Schwartz
space, the family in which the nuclear structure of the Schwartz space is visible: the Hermite
functions diagonalize every one of them, with eigenvalues `(2π(2n+1))ᵏ`.

* `hamiltonianCLM`, `hamiltonianCLM_two_smul` : the Hamiltonian as `(A B + B A)/2`.
* `hamiltonianCLM_hermiteSchwartz` : **eigenvalue `2π(2n+1)`.**
* `schwartzPair_hamiltonianCLM` : **it is symmetric for the bilinear pairing.**
* `schwartzPair_hermiteSchwartz_hamiltonian_decay` : **`(2π(2n+1))ᵏ‖⟨f, hₙ⟩‖ ≤ ‖hₙ‖₂‖Hᵏf‖₂`.**
* `oscillatorSeminorm` : the seminorms `qₖ(f) = ‖Hᵏf‖₂`.
-/

open scoped Real SchwartzMap ENNReal
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## Additivity of the pairing -/

theorem schwartzPair_add_right (f g h : 𝓢(ℝ, ℂ)) :
    schwartzPair f (g + h) = schwartzPair f g + schwartzPair f h := by
  rw [schwartzPair_def, schwartzPair_def, schwartzPair_def, show mulS f (g + h)
    = mulS f g + mulS f h from map_add _ _ _, map_add]

theorem schwartzPair_add_left (f g h : 𝓢(ℝ, ℂ)) :
    schwartzPair (f + g) h = schwartzPair f h + schwartzPair g h := by
  rw [schwartzPair_comm, schwartzPair_add_right, schwartzPair_comm h f, schwartzPair_comm h g]

/-! ## The Hamiltonian -/

/-- The **oscillator Hamiltonian** `H = A B + 2π`. -/
def hamiltonianCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  numberCLM + (2 * (π : ℂ)) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)

theorem hamiltonianCLM_apply (f : 𝓢(ℝ, ℂ)) :
    hamiltonianCLM f = numberCLM f + (2 * (π : ℂ)) • f := rfl

/-- **The Hamiltonian is the symmetric combination `(A B + B A)/2`**, by the commutation
relation. -/
theorem hamiltonianCLM_two_smul (f : 𝓢(ℝ, ℂ)) :
    (2 : ℂ) • hamiltonianCLM f
      = creationCLM (annihilationCLM f) + annihilationCLM (creationCLM f) := by
  have hcomm := annihilationCLM_creationCLM_sub f
  rw [sub_eq_iff_eq_add] at hcomm
  rw [hamiltonianCLM_apply, numberCLM_apply, hcomm]
  module

/-- **The Hermite functions are eigenfunctions of the Hamiltonian**, with eigenvalue
`2π(2n+1)`. -/
theorem hamiltonianCLM_hermiteSchwartz (n : ℕ) :
    hamiltonianCLM (hermiteSchwartz n) = (2 * (π : ℂ) * (2 * n + 1)) • hermiteSchwartz n := by
  rw [hamiltonianCLM_apply, numberCLM_hermiteSchwartz, ← add_smul]
  congr 1
  ring

/-- **The Hamiltonian is symmetric for the bilinear pairing.** -/
theorem schwartzPair_hamiltonianCLM (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (hamiltonianCLM f) g = schwartzPair f (hamiltonianCLM g) := by
  rw [hamiltonianCLM_apply, hamiltonianCLM_apply, schwartzPair_add_left, schwartzPair_add_right,
    schwartzPair_numberCLM, schwartzPair_smul_left, schwartzPair_smul_right]

/-! ## Powers of the Hamiltonian -/

/-- The `k`-th power of the Hamiltonian, as a continuous linear map. -/
def hamiltonianPowCLM : ℕ → (𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))
  | 0 => ContinuousLinearMap.id ℂ _
  | (k + 1) => hamiltonianCLM.comp (hamiltonianPowCLM k)

theorem hamiltonianPowCLM_apply (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    hamiltonianPowCLM k f = (hamiltonianCLM^[k]) f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    show hamiltonianCLM (hamiltonianPowCLM k f) = _
    rw [ih, Function.iterate_succ_apply']

theorem hamiltonianCLM_iterate_hermiteSchwartz (k n : ℕ) :
    (hamiltonianCLM^[k]) (hermiteSchwartz n)
      = ((2 * (π : ℂ) * (2 * n + 1)) ^ k) • hermiteSchwartz n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, hamiltonianCLM_hermiteSchwartz, smul_smul,
      pow_succ]

theorem schwartzPair_hamiltonianCLM_iterate (k : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair ((hamiltonianCLM^[k]) f) g = schwartzPair f ((hamiltonianCLM^[k]) g) := by
  induction k generalizing f g with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', ih, schwartzPair_hamiltonianCLM]

/-- **The Hermite coefficient of `Hᵏf` is `(2π(2n+1))ᵏ` times the Hermite coefficient of `f`.** -/
theorem schwartzPair_hermiteSchwartz_hamiltonian_iterate (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    schwartzPair ((hamiltonianCLM^[k]) f) (hermiteSchwartz n)
      = (2 * (π : ℂ) * (2 * n + 1)) ^ k * schwartzPair f (hermiteSchwartz n) := by
  rw [schwartzPair_hamiltonianCLM_iterate, hamiltonianCLM_iterate_hermiteSchwartz,
    schwartzPair_smul_right]

/-- **The Hermite coefficients decay faster than any power of `2n+1`**, with no exceptional index:
the eigenvalue `2π(2n+1)` of the Hamiltonian never vanishes. -/
theorem schwartzPair_hermiteSchwartz_hamiltonian_decay (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (2 * π * (2 * n + 1)) ^ k * ‖schwartzPair f (hermiteSchwartz n)‖
      ≤ ‖(hermiteSchwartz n).toLp 2 volume‖ * ‖((hamiltonianCLM^[k]) f).toLp 2 volume‖ := by
  have hpair := schwartzPair_hermiteSchwartz_hamiltonian_iterate k n f
  have hnorm : ‖schwartzPair ((hamiltonianCLM^[k]) f) (hermiteSchwartz n)‖
      = (2 * π * (2 * n + 1)) ^ k * ‖schwartzPair f (hermiteSchwartz n)‖ := by
    rw [hpair, norm_mul, norm_pow]
    congr 2
    have hval : (2 * (π : ℂ) * (2 * n + 1)) = ((2 * π * (2 * n + 1) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [← hnorm]
  exact norm_schwartzPair_hermiteSchwartz_le _ n

/-! ## The oscillator seminorms -/

/-- **The oscillator seminorms** `qₖ(f) = ‖Hᵏf‖₂` on the Schwartz space. -/
def oscillatorSeminorm (k : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  (normSeminorm ℂ (Lp ℂ 2 (volume : Measure ℝ))).comp
    ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap.comp
      (hamiltonianPowCLM k).toLinearMap)

theorem oscillatorSeminorm_apply (k : ℕ) (f : 𝓢(ℝ, ℂ)) :
    oscillatorSeminorm k f = ‖((hamiltonianCLM^[k]) f).toLp 2 volume‖ := by
  show ‖SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ) (hamiltonianPowCLM k f)‖ = _
  rw [SchwartzMap.toLpCLM_apply, hamiltonianPowCLM_apply]

/-- The decay estimate in terms of the oscillator seminorms. -/
theorem schwartzPair_hermiteSchwartz_oscillatorSeminorm (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (2 * π * (2 * n + 1)) ^ k * ‖schwartzPair f (hermiteSchwartz n)‖
      ≤ oscillatorSeminorm 0 (hermiteSchwartz n) * oscillatorSeminorm k f := by
  rw [oscillatorSeminorm_apply, oscillatorSeminorm_apply]
  simpa using schwartzPair_hermiteSchwartz_hamiltonian_decay k n f

end GaloisForLFunctions

end
