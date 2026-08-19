import GaloisForLFunctions.HTGeometry.EndpointProbeTransitionCriterion

/-!
# A maximally entangled orthonormal basis is endpoint complete

The base case of endpoint completeness asks for an orthonormal eigenbasis of a two-qubit system
in which *every* ordered pair of eigenvectors is seen by some one-site probe at one endpoint.  By
the endpoint criterion this is the non-vanishing of the reduced transition operator
`R(ψ,φ) = Tr_ū |φ⟩⟨ψ|`, and reshaping a bipartite vector into a matrix identifies

`R(ψ, φ) = reshape φ · (reshape ψ)ᴴ`.

So a basis all of whose members have *invertible* reshape -- maximally entangled states -- is
endpoint complete, with no case analysis at all.  The Bell basis is such a basis: each Bell
vector reshapes to `2^{-1/2}` times a unitary.
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Reshaping -/

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]

/-- A bipartite vector, reshaped into a matrix. -/
def bipartiteReshape (ψ : a × b → ℂ) : Matrix a b ℂ := Matrix.of fun i k => ψ (i, k)

omit [Fintype a] [DecidableEq a] in
/-- **The reduced transition is a product of reshapes.** -/
theorem reducedTransition_eq_reshape (ψ φ : a × b → ℂ) :
    reducedTransition ψ φ = bipartiteReshape φ * (bipartiteReshape ψ)ᴴ := by
  ext j i
  rw [reducedTransition, Matrix.of_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by
    simp [bipartiteReshape, Matrix.conjTranspose_apply]

/-- **Maximally entangled vectors are endpoint visible.**  If two bipartite vectors reshape to
nonzero multiples of unitaries, their reduced transition operator is nonzero, so some endpoint
probe sees the pair. -/
theorem reducedTransition_ne_zero_of_unitary_reshape [Nonempty a] {ψ φ : a × a → ℂ} {c d : ℂ}
    (hc : c ≠ 0) (hd : d ≠ 0) {V W : Matrix a a ℂ}
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hψ : bipartiteReshape ψ = c • V) (hφ : bipartiteReshape φ = d • W) :
    reducedTransition ψ φ ≠ 0 := by
  classical
  intro hzero
  have hgram : (bipartiteReshape ψ)ᴴ * bipartiteReshape ψ
      = (star c * c) • (1 : Matrix a a ℂ) := by
    rw [hψ, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV]
  have hstep : bipartiteReshape φ * ((bipartiteReshape ψ)ᴴ * bipartiteReshape ψ) = 0 := by
    rw [← Matrix.mul_assoc, ← reducedTransition_eq_reshape, hzero, Matrix.zero_mul]
  rw [hgram, Matrix.mul_smul, Matrix.mul_one] at hstep
  have hcc : star c * c ≠ 0 := mul_ne_zero (star_ne_zero.mpr hc) hc
  have hφ0 : bipartiteReshape φ = 0 := by
    rcases smul_eq_zero.mp hstep with h | h
    · exact absurd h hcc
    · exact h
  rw [hφ] at hφ0
  have hW0 : W = 0 := by
    rcases smul_eq_zero.mp hφ0 with h | h
    · exact absurd h hd
    · exact h
  have hone : (1 : Matrix a a ℂ) = 0 := by rw [← hW, hW0]; simp
  obtain ⟨i⟩ := ‹Nonempty a›
  have := congrFun (congrFun hone i) i
  simp [Matrix.one_apply_eq] at this

/-! ## The Bell basis -/

/-- The sign `(-1)^{a·x}`. -/
def boolSign (a x : Bool) : ℂ := if a && x then -1 else 1

@[simp] theorem star_boolSign (a x : Bool) : star (boolSign a x) = boolSign a x := by
  rw [boolSign]
  split <;> simp

theorem boolSign_mul_self (a x : Bool) : boolSign a x * boolSign a x = 1 := by
  rw [boolSign]
  split <;> norm_num

/-- The reshape of the Bell vector labelled by `α`: `(-1)^{α₁ i}` on the entry `k = i ⊕ α₂`. -/
def bellReshape (α : Bool × Bool) : Matrix Bool Bool ℂ :=
  Matrix.of fun i k => if k = xor i α.2 then boolSign α.1 i else 0

/-- **The Bell reshapes are unitary.** -/
theorem bellReshape_conjTranspose_mul (α : Bool × Bool) :
    (bellReshape α)ᴴ * bellReshape α = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, bellReshape, Matrix.of_apply]
  rw [Finset.sum_eq_single (xor k α.2)]
  · by_cases hkl : k = l
    · subst hkl
      simp [star_boolSign, boolSign_mul_self, Matrix.one_apply_eq]
    · have hxx : xor (xor k α.2) α.2 = k := by simp
      rw [Matrix.one_apply_ne hkl, hxx, if_pos rfl,
        if_neg (fun h : l = k => hkl h.symm), mul_zero]
  · intro i _ hi
    have hik : ¬ (k = xor i α.2) := by
      intro h
      apply hi
      rw [h]
      simp
    simp [hik]
  · intro h
    exact absurd (Finset.mem_univ (xor k α.2)) h

/-- The Bell vector labelled by `α`. -/
def bellVector (α : Bool × Bool) : Bool × Bool → ℂ :=
  fun x => ((Real.sqrt 2)⁻¹ : ℂ) * bellReshape α x.1 x.2

theorem bipartiteReshape_bellVector (α : Bool × Bool) :
    bipartiteReshape (bellVector α) = ((Real.sqrt 2)⁻¹ : ℂ) • bellReshape α := by
  ext i k
  rfl

theorem sqrtTwo_inv_ne_zero : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by
  have h2 : Real.sqrt 2 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact ne_of_gt this
  simp [h2]

/-- **The Bell basis is endpoint complete.**  Every ordered pair of Bell vectors -- including a
vector with itself -- has a nonzero reduced transition operator, so some Hermitian one-site probe
at the endpoint sees it. -/
theorem reducedTransition_bellVector_ne_zero (α β : Bool × Bool) :
    reducedTransition (bellVector α) (bellVector β) ≠ 0 :=
  reducedTransition_ne_zero_of_unitary_reshape sqrtTwo_inv_ne_zero sqrtTwo_inv_ne_zero
    (bellReshape_conjTranspose_mul α) (bellReshape_conjTranspose_mul β)
    (bipartiteReshape_bellVector α) (bipartiteReshape_bellVector β)

/-! ## The Bell family is an orthonormal basis -/

theorem sqrtTwo_inv_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have h : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
  rw [← mul_inv, h2]
  norm_num

/-- The matrix whose columns are the four Bell vectors. -/
def bellMatrix : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun x α => bellVector α x

/-- **The Bell family is orthonormal.** -/
theorem bellMatrix_conjTranspose_mul : bellMatrixᴴ * bellMatrix = 1 := by
  ext α β
  obtain ⟨a₁, a₂⟩ := α
  obtain ⟨b₁, b₂⟩ := β
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, bellMatrix, Matrix.of_apply, bellVector, bellReshape,
    Fintype.sum_bool, Matrix.one_apply, boolSign, Prod.mk.injEq]
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    norm_num [sqrtTwo_inv_mul_self]


/-! ## The two-qubit endpoint-complete witness Hamiltonian -/

/-- The two-qubit Hamiltonian with a prescribed spectrum in the Bell eigenbasis. -/
def bellHamiltonian (E : Bool × Bool → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  bellMatrix * Matrix.diagonal (fun α => ((E α : ℝ) : ℂ)) * bellMatrixᴴ

theorem bellMatrix_mul_conjTranspose : bellMatrix * bellMatrixᴴ = 1 :=
  mul_eq_one_comm.mpr bellMatrix_conjTranspose_mul

theorem bellHamiltonian_isHermitian (E : Bool × Bool → ℝ) :
    (bellHamiltonian E).IsHermitian := by
  show (bellHamiltonian E)ᴴ = bellHamiltonian E
  rw [bellHamiltonian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
  have hstar : (star fun α : Bool × Bool => ((E α : ℝ) : ℂ)) = fun α => ((E α : ℝ) : ℂ) := by
    funext α
    simp
  rw [hstar]

theorem bellHamiltonian_trace (E : Bool × Bool → ℝ) :
    (bellHamiltonian E).trace = ∑ α, ((E α : ℝ) : ℂ) := by
  rw [bellHamiltonian, Matrix.trace_mul_cycle, bellMatrix_conjTranspose_mul, Matrix.one_mul,
    Matrix.trace_diagonal]

/-- **The Bell vectors are the eigenvectors.**  Conjugating the prescribed diagonal spectrum by
the Bell matrix intertwines the Hamiltonian with the spectrum. -/
theorem bellHamiltonian_mul_bellMatrix (E : Bool × Bool → ℝ) :
    bellHamiltonian E * bellMatrix
      = bellMatrix * Matrix.diagonal (fun α => ((E α : ℝ) : ℂ)) := by
  rw [bellHamiltonian, Matrix.mul_assoc, Matrix.mul_assoc, bellMatrix_conjTranspose_mul,
    Matrix.mul_one]

/-- **The two-qubit endpoint-complete witness.**  For every prescribed real spectrum the Bell
Hamiltonian is Hermitian, has that spectrum in an orthonormal eigenbasis, and every ordered pair
of its eigenvectors is seen by some one-site probe at the endpoint qubit. -/
theorem exists_endpointComplete_twoQubit_witness (E : Bool × Bool → ℝ) :
    ∃ H : Matrix (Bool × Bool) (Bool × Bool) ℂ, ∃ U : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      H.IsHermitian ∧ Uᴴ * U = 1 ∧ H * U = U * Matrix.diagonal (fun α => ((E α : ℝ) : ℂ)) ∧
        H.trace = ∑ α, ((E α : ℝ) : ℂ) ∧
        ∀ α β : Bool × Bool,
          reducedTransition (fun x => U x α) (fun x => U x β) ≠ 0 :=
  ⟨bellHamiltonian E, bellMatrix, bellHamiltonian_isHermitian E,
    bellMatrix_conjTranspose_mul, bellHamiltonian_mul_bellMatrix E, bellHamiltonian_trace E,
    fun α β => reducedTransition_bellVector_ne_zero α β⟩


end GaloisForLFunctions.HTGeometry
