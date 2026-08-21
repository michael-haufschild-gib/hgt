/-
# The depth-`s` dictionary of gate words

A finite alphabet of unitary gates acts on a fixed seed state.  The states reachable by words of
length exactly `s` form a dictionary of unit vectors indexed by `Fin s → Γ`, and if the alphabet
contains the identity gate then every state reachable by a shorter word already occurs in it.  Its
cardinality is `|Γ|^s`, so an alphabet bound `|Γ| ≤ M` gives the counting condition `M^{s+1}` that
the completed-time circuit bound consumes.

Main results:
* `gateWord`, `wordState` — the ordered product of a word of gates and its action on the seed.
* `finiteComplexInner_wordState_self` — **every reachable state is a unit vector**.
* `exists_wordState_pad` — **padding**: the depth-`s` dictionary contains every shorter word's
  endpoint once the identity gate is available.
-/
import GaloisForLFunctions.HTGeometry.CircuitDictionaryCounting
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A unitary matrix preserves the pairing of register states. -/
theorem finiteComplexInner_mulVec_unitary {U : Matrix I I ℂ} (hU : Uᴴ * U = 1) (x y : I → ℂ) :
    finiteComplexInner (U *ᵥ x) (U *ᵥ y) = finiteComplexInner x y := by
  have hdot : ∀ u v : I → ℂ, finiteComplexInner u v = (star u) ⬝ᵥ v := fun _ _ => rfl
  rw [hdot, hdot, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
    Matrix.vecMul_one]

variable {Γ : Type*}

/-- The ordered product of the gates named by a word. -/
def gateWord (g : Γ → Matrix I I ℂ) {s : ℕ} (word : Fin s → Γ) : Matrix I I ℂ :=
  (List.ofFn fun i => g (word i)).prod

/-- A word in unitary gates is unitary. -/
theorem gateWord_mem_unitary {g : Γ → Matrix I I ℂ}
    (hg : ∀ c, g c ∈ Matrix.unitaryGroup I ℂ) {s : ℕ} (word : Fin s → Γ) :
    gateWord g word ∈ Matrix.unitaryGroup I ℂ := by
  refine Submonoid.list_prod_mem _ ?_
  intro U hU
  rw [List.mem_ofFn] at hU
  obtain ⟨i, rfl⟩ := hU
  exact hg (word i)

/-- Concatenation of words is composition of the gate products. -/
theorem gateWord_append {g : Γ → Matrix I I ℂ} {m k : ℕ} (u : Fin m → Γ) (v : Fin k → Γ) :
    gateWord g (Fin.append u v) = gateWord g u * gateWord g v := by
  have h : (fun i => g (Fin.append u v i))
      = Fin.append (fun i => g (u i)) (fun i => g (v i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  rw [gateWord, h, List.ofFn_fin_append, List.prod_append, gateWord, gateWord]

/-- The state reached from a seed by a word of gates. -/
def wordState (g : Γ → Matrix I I ℂ) (psi : I → ℂ) {s : ℕ} (word : Fin s → Γ) : I → ℂ :=
  gateWord g word *ᵥ psi

/-- **Every reachable state is a unit vector.** -/
theorem finiteComplexInner_wordState_self {g : Γ → Matrix I I ℂ}
    (hg : ∀ c, g c ∈ Matrix.unitaryGroup I ℂ) {psi : I → ℂ}
    (hpsi : finiteComplexInner psi psi = 1) {s : ℕ} (word : Fin s → Γ) :
    finiteComplexInner (wordState g psi word) (wordState g psi word) = 1 := by
  rw [wordState, finiteComplexInner_mulVec_unitary
    (Matrix.mem_unitaryGroup_iff'.mp (gateWord_mem_unitary hg word)), hpsi]

/-- **Padding.**  With the identity gate in the alphabet, the depth-`s` dictionary already contains
the endpoint of every word of length at most `s`. -/
theorem exists_wordState_pad {g : Γ → Matrix I I ℂ} {e : Γ} (he : g e = 1) (psi : I → ℂ)
    {k s : ℕ} (hk : k ≤ s) (word : Fin k → Γ) :
    ∃ w' : Fin s → Γ, wordState g psi w' = wordState g psi word := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + k := ⟨s - k, by omega⟩
  refine ⟨Fin.append (fun _ => e) word, ?_⟩
  rw [wordState, wordState, gateWord_append]
  have h1 : gateWord g (fun _ : Fin m => e) = 1 := by
    rw [gateWord]
    refine List.prod_eq_one ?_
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact he
  rw [h1, one_mul]

end GaloisForLFunctions.HTGeometry

end
