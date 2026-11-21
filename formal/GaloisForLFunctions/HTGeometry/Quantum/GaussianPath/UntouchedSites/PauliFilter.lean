import GaloisForLFunctions.HTGeometry.PauliChainLabels
import GaloisForLFunctions.HTGeometry.FinitePauliConjugationLaw

/-! # Selecting a single Pauli coefficient at one site by conjugation -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section
variable {S : Type*} [Fintype S] [DecidableEq S]
abbrev SpinMatrix (S : Type*) := Matrix (S → Bool) (S → Bool) ℂ

/-- Pauli matrix acting on one physical site. -/
def spin (v : S) (a : Fin 3) : SpinMatrix S := finitePauliMatrix (siteLabel v a)

private def reject (v : S) (a : Fin 3) : SpinMatrix S →ₗ[ℂ] SpinMatrix S :=
  LinearMap.id - (LinearMap.mulRight ℂ (spin v a)).comp (LinearMap.mulLeft ℂ (spin v a))

private theorem reject_word (v : S) (a : Fin 3) (p : S → Option (Fin 3)) :
    reject v a (finitePauliMatrix p) =
      (1-boolPauliConjugationSign (some a) (p v)) • finitePauliMatrix p := by
  have he : finitePauliConjugationSign (siteLabel v a) p = boolPauliConjugationSign (some a) (p v) := by
    unfold finitePauliConjugationSign
    rw [Finset.prod_eq_single v]
    · simp [siteLabel]
    · intro w _ hw
      simp [siteLabel,hw,boolPauliConjugationSign]
    · simp
  change finitePauliMatrix p - finitePauliMatrix (siteLabel v a)*finitePauliMatrix p*
    finitePauliMatrix (siteLabel v a) = _
  rw [finitePauliMatrix_conj,he,sub_smul,one_smul]

/-- The two sign changes under the other Pauli axes isolate exactly the
specified Pauli direction and kill the identity component. -/
def selectAxis (v : S) (a : Fin 3) : SpinMatrix S →ₗ[ℂ] SpinMatrix S :=
  ((4:ℂ)⁻¹) • ((reject v (a+1)).comp (reject v (a+2)))

private theorem selector_factor (a : Fin 3) (p : Option (Fin 3)) :
    (4:ℂ)⁻¹*((1-boolPauliConjugationSign (some (a+2)) p)*
      (1-boolPauliConjugationSign (some (a+1)) p)) = if p=some a then 1 else 0 := by
  cases p with
  | none => simp [boolPauliConjugationSign]
  | some b =>
    fin_cases a <;> fin_cases b <;>
      simp (config := {decide := true}) [boolPauliConjugationSign] <;> norm_num

theorem selectAxis_word (v : S) (a : Fin 3) (p : S → Option (Fin 3)) :
    selectAxis v a (finitePauliMatrix p) = if p v=some a then finitePauliMatrix p else 0 := by
  simp only [selectAxis,LinearMap.smul_apply,LinearMap.comp_apply,reject_word,map_smul,smul_smul,
    ←mul_assoc]
  rw [mul_assoc,selector_factor]
  split <;> simp

/-- A matrix commuting with the site algebra still commutes with each
selected component of any operator it commutes with. -/
theorem commute_selectAxis {v : S} {U H : SpinMatrix S} (hu : ∀ a, Commute U (spin v a))
    (hh : Commute U H) (a : Fin 3) : Commute U (selectAxis v a H) := by
  have hrej (b : Fin 3) (X : SpinMatrix S) (hx : Commute U X) : Commute U (reject v b X) :=
    hx.sub_right (((hu b).mul_right hx).mul_right (hu b))
  exact (hrej (a+1) _ (hrej (a+2) H hh)).smul_right ((4:ℂ)⁻¹)

#print axioms selectAxis_word
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
