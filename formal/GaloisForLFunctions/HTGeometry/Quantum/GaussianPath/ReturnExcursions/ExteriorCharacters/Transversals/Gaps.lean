import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Transversals.Diagonal

/-! # A transversal character in the selected physical energy gaps -/

open Matrix Finset Complex
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The frequency of one transversal, relative to the all-false choice. -/
def gapEnergy (E : I → ℝ) (f : Fin q × Bool ↪ I) (x : Fin q → Bool) : ℝ :=
  ∑ j, if x j then E (f (j,true))-E (f (j,false)) else 0

private def oscillation (t u : ℝ) : ℂ := Complex.exp (((-t*u:ℝ):ℂ)*Complex.I)

private theorem osc_add (t u v : ℝ) :
    oscillation t (u+v)=oscillation t u*oscillation t v := by
  simp only [oscillation,mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

private theorem osc_sum {J : Type*} [Fintype J] (t : ℝ) (a : J → ℝ) :
    (∏ j, oscillation t (a j))=oscillation t (∑ j, a j) := by
  classical
  suffices h : ∀ S : Finset J, (∏ j ∈ S, oscillation t (a j))=oscillation t (∑ j ∈ S,a j) from h univ
  intro S
  induction S using Finset.induction_on with
  | empty => simp [oscillation]
  | insert i s hi ih => rw [prod_insert hi,sum_insert hi,ih,osc_add]

/-- Removing the common phase leaves precisely the signed sum in the
chosen pair gaps, even for a pairing selected from the observed energies. -/
theorem pair_character_norm_gaps (W : unitary (Mat I)) (E : I → ℝ)
    (f : Fin q × Bool ↪ I) (t : ℝ) :
    ‖pairCharacter W f (fun i => Complex.exp (((-t*E i:ℝ):ℂ)*Complex.I))‖=
    ‖∑ x : Fin q → Bool, pairWeight W f x*
      Complex.exp (((-t*gapEnergy E f x:ℝ):ℂ)*Complex.I)‖ := by
  let base := ∑ j, E (f (j,false))
  have h (x : Fin q → Bool) : (∑ j, E (f (j,x j)))=base+gapEnergy E f x := by
    dsimp only [base,gapEnergy]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    cases x j <;> simp
  have he : pairCharacter W f (fun i => oscillation t (E i))=oscillation t base*
      ∑ x, pairWeight W f x*oscillation t (gapEnergy E f x) := by
    rw [pairCharacter,mul_sum]
    apply sum_congr rfl
    intro x _
    rw [osc_sum,h,osc_add]
    ring
  change ‖pairCharacter W f (fun i => oscillation t (E i))‖=_
  rw [he,norm_mul,show ‖oscillation t base‖=1 from Complex.norm_exp_ofReal_mul_I _,one_mul]
  rfl

#print axioms pair_character_norm_gaps
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
