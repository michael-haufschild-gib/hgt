import GaloisForLFunctions.HTGeometry.GomesGaussianChargeLadder
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Independence, orthogonality, and norm growth of the charged Gaussian ladder

The common tensor-charge connection produces actual independent Schwartz states, not merely
formal eigenvalue labels. Its spectral spacing forces orthogonality; the adjoint factorization
fixes factorial norm growth. This extends the corpus's unit-charge Hermite geometry to all
positive effective charges and their shifted dual sectors.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Distinct ladder indices have distinct charge-scaled eigenvalues. -/
theorem gomesGaussianChargeLadder_eigenvalue_injective (a : Set.Ioi (0 : ℝ)) :
    Function.Injective (fun n : ℕ => 4 * (Real.pi : ℂ) * a.val * n) := by
  intro m n h
  have hp : 0 < 4 * Real.pi * a.val := mul_pos (mul_pos (by linarith) Real.pi_pos) a.property
  have hc : 4 * (Real.pi : ℂ) * a.val ≠ 0 := by exact_mod_cast ne_of_gt hp
  exact Nat.cast_injective (mul_left_cancel₀ hc h)

/-- Every rung is a bundled nonzero eigenvector of the actual linear Hamiltonian. -/
theorem gomesGaussianChargeLadder_hasEigenvector (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    Module.End.HasEigenvector (dilatonHamiltonianCLM (gomesGaussianLogWeight a.val)).toLinearMap
      (4 * (Real.pi : ℂ) * a.val * n) (gomesGaussianChargeLadder a n) := by
  refine ⟨?_, gomesGaussianChargeLadder_ne_zero a n⟩
  rw [Module.End.mem_eigenspace_iff]
  exact gomesGaussianChargeLadder_eigen a n

/-- The entire infinite ladder is linearly independent over the complex numbers. -/
theorem gomesGaussianChargeLadder_linearIndependent (a : Set.Ioi (0 : ℝ)) :
    LinearIndependent ℂ (gomesGaussianChargeLadder a) :=
  Module.End.eigenvectors_linearIndependent'
    (dilatonHamiltonianCLM (gomesGaussianLogWeight a.val)).toLinearMap
    _ (gomesGaussianChargeLadder_eigenvalue_injective a) _ (gomesGaussianChargeLadder_hasEigenvector a)

/-- The shared real dilaton connection gives a symmetric bilinear Hamiltonian pairing. -/
theorem gomesDilatonHamiltonian_pair_symmetric (H : ℝ[X]) (f g : 𝓢(ℝ, ℂ)) :
    schwartzPair (dilatonHamiltonianCLM H f) g = schwartzPair f (dilatonHamiltonianCLM H g) := by
  change schwartzPair (dilatonAdjointChargeCLM H (dilatonSuperchargeCLM H f)) g =
    schwartzPair f (dilatonAdjointChargeCLM H (dilatonSuperchargeCLM H g))
  rw [schwartzPair_comm, dilatonCharges_pair_adjoint, schwartzPair_comm,
    ← dilatonCharges_pair_adjoint]

/-- The pairing of two rungs is annihilated by their exact spectral gap. -/
theorem gomesGaussianChargeLadder_pair_gap (a : Set.Ioi (0 : ℝ)) (m n : ℕ) :
    (4 * (Real.pi : ℂ) * a.val * m - 4 * (Real.pi : ℂ) * a.val * n) *
      schwartzPair (gomesGaussianChargeLadder a m) (gomesGaussianChargeLadder a n) = 0 := by
  have h := gomesDilatonHamiltonian_pair_symmetric (gomesGaussianLogWeight a.val)
    (gomesGaussianChargeLadder a m) (gomesGaussianChargeLadder a n)
  rw [gomesGaussianChargeLadder_eigen, gomesGaussianChargeLadder_eigen,
    schwartzPair_smul_left, schwartzPair_smul_right] at h
  rw [sub_mul, h, sub_self]

/-- Charged creation commutes with complex conjugation. -/
theorem gomesGaussianAdjointCharge_conj (a : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    SchwartzMap.conjSLM (dilatonAdjointChargeCLM (gomesGaussianLogWeight a) ψ) =
      dilatonAdjointChargeCLM (gomesGaussianLogWeight a) (SchwartzMap.conjSLM ψ) := by
  have hd := gomesGaussianSupercharge_dual a
  have he : dilatonAdjointChargeCLM (gomesGaussianLogWeight a) =
      -dilatonSuperchargeCLM (gomesGaussianLogWeight (-a)) := by rw [hd, neg_neg]
  rw [he]
  change SchwartzMap.conjSLM (-(dilatonSuperchargeCLM (gomesGaussianLogWeight (-a)) ψ)) =
    -(dilatonSuperchargeCLM (gomesGaussianLogWeight (-a)) (SchwartzMap.conjSLM ψ))
  rw [map_neg, dilatonSuperchargeCLM_conj]

/-- Every charged rung is real-valued as a complex Schwartz state. -/
theorem gomesGaussianChargeLadder_conj (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    SchwartzMap.conjSLM (gomesGaussianChargeLadder a n) = gomesGaussianChargeLadder a n := by
  induction n with
  | zero =>
    ext x
    rw [SchwartzMap.conjSLM_apply, gomesGaussianChargeLadder_zero,
      gomesGaussianChargeGroundState_apply, Complex.conj_ofReal]
  | succ n ih =>
    rw [← gomesGaussianChargeLadder_raise, gomesGaussianAdjointCharge_conj, ih]

/-- The bilinear and Hilbert pairings coincide on the real-valued charged ladder. -/
theorem gomesGaussianChargeLadder_inner (a : Set.Ioi (0 : ℝ)) (m n : ℕ) :
    inner ℂ ((gomesGaussianChargeLadder a m).toLp 2 volume)
      ((gomesGaussianChargeLadder a n).toLp 2 volume) =
      schwartzPair (gomesGaussianChargeLadder a m) (gomesGaussianChargeLadder a n) := by
  rw [schwartzPair_eq_inner, gomesGaussianChargeLadder_conj]

/-- The nonzero Schwartz ladder remains nonzero after passage to L². -/
theorem gomesGaussianChargeLadder_toLp_ne_zero (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    (gomesGaussianChargeLadder a n).toLp 2 (volume : Measure ℝ) ≠ 0 := by
  intro h
  apply gomesGaussianChargeLadder_ne_zero a n
  apply SchwartzMap.injective_toLp 2 (volume : Measure ℝ)
  have hz := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_zero
  rw [SchwartzMap.toLpCLM_apply] at hz
  exact h.trans hz.symm

/-- Self-pairing is exactly the squared L² norm. -/
theorem gomesGaussianChargeLadder_pair_self (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    schwartzPair (gomesGaussianChargeLadder a n) (gomesGaussianChargeLadder a n) =
      ((‖(gomesGaussianChargeLadder a n).toLp 2 (volume : Measure ℝ)‖ ^ 2 : ℝ) : ℂ) := by
  rw [← schwartzPair_conj_self, gomesGaussianChargeLadder_conj]

/-- Orthogonality is exact: the pairing vanishes precisely off the diagonal. -/
theorem gomesGaussianChargeLadder_pair_zero_iff (a : Set.Ioi (0 : ℝ)) (m n : ℕ) :
    schwartzPair (gomesGaussianChargeLadder a m) (gomesGaussianChargeLadder a n) = 0 ↔ m ≠ n := by
  constructor
  · intro hz hmn
    subst n
    rw [gomesGaussianChargeLadder_pair_self] at hz
    have hn : ‖(gomesGaussianChargeLadder a m).toLp 2 (volume : Measure ℝ)‖ ^ 2 = 0 := by
      exact_mod_cast hz
    exact gomesGaussianChargeLadder_toLp_ne_zero a m (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro hmn
    have hgap : 4 * (Real.pi : ℂ) * a.val * m - 4 * (Real.pi : ℂ) * a.val * n ≠ 0 :=
      sub_ne_zero.mpr (fun h => hmn (gomesGaussianChargeLadder_eigenvalue_injective a h))
    exact (mul_eq_zero.mp (gomesGaussianChargeLadder_pair_gap a m n)).resolve_left hgap

/-- Adjacent squared norms obey the exact charge-scaled oscillator recursion. -/
theorem gomesGaussianChargeLadder_pair_self_succ (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    schwartzPair (gomesGaussianChargeLadder a (n + 1)) (gomesGaussianChargeLadder a (n + 1)) =
      (4 * (Real.pi : ℂ) * a.val * ((n : ℂ) + 1)) *
        schwartzPair (gomesGaussianChargeLadder a n) (gomesGaussianChargeLadder a n) := by
  nth_rw 2 [← gomesGaussianChargeLadder_raise]
  rw [dilatonCharges_pair_adjoint, gomesGaussianChargeLadder_lower, schwartzPair_smul_left]

/-- The entire norm recursion closes to charge powers times a factorial. -/
theorem gomesGaussianChargeLadder_pair_self_factorial (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    schwartzPair (gomesGaussianChargeLadder a n) (gomesGaussianChargeLadder a n) =
      ((4 * (Real.pi : ℂ) * a.val) ^ n * (n.factorial : ℂ)) *
        schwartzPair (gomesGaussianChargeGroundState a) (gomesGaussianChargeGroundState a) := by
  induction n with
  | zero => simp [gomesGaussianChargeLadder_zero]
  | succ n ih =>
    rw [gomesGaussianChargeLadder_pair_self_succ, ih, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_succ, pow_succ]
    ring

/-- The factorial growth identity holds for the actual Hilbert norms. -/
theorem gomesGaussianChargeLadder_norm_sq_factorial (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    ‖(gomesGaussianChargeLadder a n).toLp 2 (volume : Measure ℝ)‖ ^ 2 =
      ((4 * Real.pi * a.val) ^ n * (n.factorial : ℝ)) *
        ‖(gomesGaussianChargeGroundState a).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have h := gomesGaussianChargeLadder_pair_self_factorial a n
  rw [gomesGaussianChargeLadder_pair_self] at h
  have hzero := gomesGaussianChargeLadder_pair_self a 0
  rw [gomesGaussianChargeLadder_zero] at hzero
  rw [hzero] at h
  exact_mod_cast h

end GaloisForLFunctions.HTGeometry
