import GaloisForLFunctions.HTGeometry.PolynomialCircuitParametrisation
import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw
import Mathlib.Analysis.Complex.Basic

/-!
# A two-qubit gate word is a sixteen-parameter-per-gate polynomial map

The exact-complexity argument needs the states reachable by `s` two-qubit gates to lie inside the
image of a polynomial map with `16 s` parameters — one per entry of each `4 × 4` gate.  Unitarity is
not imposed: constraints only shrink the parameter set, and the argument needs the reachable states
to lie *inside* the image, not to fill it.

## Main results

* `IsTwoQubitGate` — acting on two named qubits and as the identity elsewhere.
* `genericTwoQubitGate` — the same with the sixteen entries as indeterminates.
* `exists_param_of_twoQubitGates` — **every two-qubit gate word is an evaluation of the generic
  one.**
* `twoQubitCircuitCoords`, `aeval_twoQubitCircuitCoords` — the prepared state, coordinatewise, is a
  fixed polynomial in the gate entries.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace TwoQubitCircuit

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Evaluation commutes with the linear algebra, over an arbitrary index type -/

variable {α : Type*} [Fintype α] [DecidableEq α] {B : Type*} [CommRing B] [Algebra ℚ B] {m : ℕ}

theorem aeval_mulVec' (u : Fin m → B)
    (A : Matrix α α (MvPolynomial (Fin m) ℚ)) (v : α → MvPolynomial (Fin m) ℚ) (i : α) :
    MvPolynomial.aeval u (A.mulVec v i)
      = (A.map (MvPolynomial.aeval u)).mulVec (fun j => MvPolynomial.aeval u (v j)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply]

theorem aeval_matrix_prod' (u : Fin m → B)
    (A : List (Matrix α α (MvPolynomial (Fin m) ℚ))) :
    (A.prod).map (MvPolynomial.aeval u)
      = (A.map (fun N => Matrix.map N (MvPolynomial.aeval u))).prod := by
  have hhom := List.prod_hom A
    ((MvPolynomial.aeval u : MvPolynomial (Fin m) ℚ →ₐ[ℚ] B).mapMatrix (m := α))
  have hfun : (⇑((MvPolynomial.aeval u : MvPolynomial (Fin m) ℚ →ₐ[ℚ] B).mapMatrix (m := α)))
      = fun N => Matrix.map N (MvPolynomial.aeval u) := by
    funext N
    rfl
  rw [← hfun]
  exact hhom.symm

theorem aeval_circuit' (u : Fin m → B)
    (A : List (Matrix α α (MvPolynomial (Fin m) ℚ))) (v : α → MvPolynomial (Fin m) ℚ) (i : α) :
    MvPolynomial.aeval u ((A.prod.mulVec v) i)
      = ((A.map (fun N => Matrix.map N (MvPolynomial.aeval u))).prod.mulVec
          (fun j => MvPolynomial.aeval u (v j))) i := by
  rw [aeval_mulVec', aeval_matrix_prod']

/-! ### Two-qubit gates -/

variable {n : ℕ}

/-- A gate acting on the two qubits `a`, `b` and as the identity on every other qubit. -/
def IsTwoQubitGate (a b : Fin n) (G : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : Prop :=
  ∃ U : (Bool × Bool) → (Bool × Bool) → ℂ, ∀ x y : Fin n → Bool,
    G x y = if (∀ c, c ≠ a → c ≠ b → x c = y c) then U (x a, x b) (y a, y b) else 0

/-- The identity is a two-qubit gate at any pair of qubits. -/
theorem isTwoQubitGate_one (a b : Fin n) :
    IsTwoQubitGate a b (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  classical
  refine ⟨fun p q => if p = q then 1 else 0, fun x y => ?_⟩
  rw [Matrix.one_apply]
  by_cases hagree : ∀ c, c ≠ a → c ≠ b → x c = y c
  · rw [if_pos hagree]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [if_neg hxy]
      have hne : ((x a, x b) : Bool × Bool) ≠ (y a, y b) := by
        intro hcon
        refine hxy (funext fun c => ?_)
        by_cases hca : c = a
        · subst hca
          exact congrArg Prod.fst hcon
        · by_cases hcb : c = b
          · subst hcb
            exact congrArg Prod.snd hcon
          · exact hagree c hca hcb
      simp [hne]
  · rw [if_neg hagree, if_neg]
    intro hcon
    exact hagree (fun c _ _ => congrFun hcon c)

/-- The sixteen parameters of each of `s` gates. -/
def gateParamIndex (s : ℕ) : Fin s × ((Bool × Bool) × (Bool × Bool)) ≃ Fin (s * 16) :=
  Fintype.equivFinOfCardEq (by simp)

/-- The `k`-th generic two-qubit gate at the qubits `a`, `b`. -/
def genericTwoQubitGate (s : ℕ) (a b : Fin n) (k : Fin s) :
    Matrix (Fin n → Bool) (Fin n → Bool) (MvPolynomial (Fin (s * 16)) ℚ) :=
  fun x y => if (∀ c, c ≠ a → c ≠ b → x c = y c)
    then MvPolynomial.X (gateParamIndex s (k, ((x a, x b), (y a, y b)))) else 0

/-- **Every two-qubit gate word is an evaluation of the generic one.** -/
theorem exists_param_of_twoQubitGates {s : ℕ} (pos : Fin s → Fin n × Fin n)
    (G : Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ k, IsTwoQubitGate (pos k).1 (pos k).2 (G k)) :
    ∃ u : Fin (s * 16) → ℂ, ∀ k,
      (genericTwoQubitGate s (pos k).1 (pos k).2 k).map (MvPolynomial.aeval u) = G k := by
  classical
  choose U hU using hG
  refine ⟨fun idx =>
    U ((gateParamIndex s).symm idx).1 ((gateParamIndex s).symm idx).2.1
      ((gateParamIndex s).symm idx).2.2, fun k => ?_⟩
  ext x y
  rw [Matrix.map_apply, genericTwoQubitGate, hU k x y]
  by_cases hagree : ∀ c, c ≠ (pos k).1 → c ≠ (pos k).2 → x c = y c
  · rw [if_pos hagree, if_pos hagree, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
  · rw [if_neg hagree, if_neg hagree, map_zero]

/-- The coordinates of the state prepared by a generic two-qubit gate word. -/
def twoQubitCircuitCoords (s : ℕ) (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ) : (Fin n → Bool) → MvPolynomial (Fin (s * 16)) ℚ :=
  fun i => ((List.ofFn (fun k => genericTwoQubitGate s (pos k).1 (pos k).2 k)).prod.mulVec
    (fun j => MvPolynomial.C (v j))) i

/-- **The prepared state is the evaluation of fixed polynomials at the gate entries.** -/
theorem aeval_twoQubitCircuitCoords {s : ℕ} (pos : Fin s → Fin n × Fin n)
    (v : (Fin n → Bool) → ℚ) (G : Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hG : ∀ k, IsTwoQubitGate (pos k).1 (pos k).2 (G k)) :
    ∃ u : Fin (s * 16) → ℂ, ∀ i,
      MvPolynomial.aeval u (twoQubitCircuitCoords s pos v i)
        = ((List.ofFn G).prod.mulVec (fun j => algebraMap ℚ ℂ (v j))) i := by
  classical
  obtain ⟨u, hu⟩ := exists_param_of_twoQubitGates pos G hG
  refine ⟨u, fun i => ?_⟩
  rw [twoQubitCircuitCoords, aeval_circuit' u]
  have hfun : ((fun N : Matrix (Fin n → Bool) (Fin n → Bool) (MvPolynomial (Fin (s * 16)) ℚ) =>
      Matrix.map N (MvPolynomial.aeval u)) ∘
      fun k => genericTwoQubitGate s (pos k).1 (pos k).2 k) = G := funext hu
  rw [List.map_ofFn, hfun]
  congr 1
  funext j
  rw [MvPolynomial.aeval_C]

end

end TwoQubitCircuit

end GaloisForLFunctions.HTGeometry
