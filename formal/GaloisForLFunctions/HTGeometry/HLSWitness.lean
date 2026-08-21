import GaloisForLFunctions.HTGeometry.HLSTheorem
import Mathlib.Algebra.Module.PUnit

/-!
# The `N = 1` super-Poincaré witness

`HLSGradedSymmetry` is not a vacuous hypothesis: this module constructs the four-dimensional
`N = 1` super-Poincaré algebra as an explicit inhabitant, with odd part
`(Q_1, Q_2, Q̄_1̇, Q̄_2̇)`, no internal charges, `{Q_α, Q̄_β̇} = 2 P_{α β̇}`, `{Q, Q} = 0` and
`[P, Q] = 0`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

/-- The trivial internal symmetry algebra of the `N = 1` witness. -/
def HLSNoCharge : Type := PUnit

instance : AddCommGroup HLSNoCharge := inferInstanceAs (AddCommGroup PUnit)
instance : Module ℂ HLSNoCharge := inferInstanceAs (Module ℂ PUnit)
instance : Bracket HLSNoCharge HLSNoCharge := ⟨fun _ _ => (0 : HLSNoCharge)⟩

instance : LieRing HLSNoCharge where
  add_lie _ _ _ := rfl
  lie_add _ _ _ := rfl
  lie_self _ := rfl
  leibniz_lie _ _ _ := rfl

instance : LieAlgebra ℂ HLSNoCharge where
  lie_smul _ _ _ := rfl

theorem hlsNoCharge_eq (b c : HLSNoCharge) : b = c := rfl

/-- Odd part of the witness: the four Weyl components `(Q_1, Q_2, Q̄_1̇, Q̄_2̇)`. -/
abbrev HLSWitnessOdd : Type := Fin 4 → ℂ

/-- The Lorentz action on the witness odd part. -/
def hlsWitnessActFun (X : HLSEven HLSNoCharge) (v : HLSWitnessOdd) : HLSWitnessOdd :=
  ![X.1 2 * v 0 + X.1 0 * v 1, X.1 1 * v 0 - X.1 2 * v 1,
    X.2.1 2 * v 2 + X.2.1 0 * v 3, X.2.1 1 * v 2 - X.2.1 2 * v 3]

/-- The odd--odd anticommutator of the witness: `{Q_α, Q̄_β̇} = 2 P_{α β̇}`. -/
def hlsWitnessBrMat (u v : HLSWitnessOdd) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![2 * (u 0 * v 2 + v 0 * u 2), 2 * (u 0 * v 3 + v 0 * u 3);
     2 * (u 1 * v 2 + v 1 * u 2), 2 * (u 1 * v 3 + v 1 * u 3)]

/-- The real structure of the witness: `Q̄ = Q★`. -/
def hlsWitnessConjFun (v : HLSWitnessOdd) : HLSWitnessOdd :=
  ![(starRingEnd ℂ) (v 2), (starRingEnd ℂ) (v 3),
    (starRingEnd ℂ) (v 0), (starRingEnd ℂ) (v 1)]

/-- The rest-frame state functional of the witness: the trace of the translation component. -/
def hlsWitnessStateFun (X : HLSEven HLSNoCharge) : ℂ := X.2.2.1 0 0 + X.2.2.1 1 1


theorem hlsSl2Mat_transpose (x : HLSSl2) : (hlsSl2Mat x)ᵀ = !![x 2, x 1; x 0, -x 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hlsSl2Mat]

theorem hlsEvenBr_mom_right {B : Type*} [LieRing B] [LieAlgebra ℂ B] (X : HLSEven B)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    hlsEvenBr X (hlsMom M) = hlsMom (hlsLorAct X.1 X.2.1 M) := by
  simp [hlsEvenBr, hlsMom]

/-- The trivial real form of the trivial internal algebra. -/
def hlsWitnessInternalRealForm : HLSInternalRealForm HLSNoCharge where
  conj := { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  conj_conj := fun _ => rfl
  conj_lie := fun _ _ => rfl

/-- The bundled even action of the witness. -/
def hlsWitnessAct : HLSEven HLSNoCharge →ₗ[ℂ] (HLSWitnessOdd →ₗ[ℂ] HLSWitnessOdd) :=
  LinearMap.mk₂ ℂ hlsWitnessActFun
    (fun X Y v => by funext i; fin_cases i <;> simp [hlsWitnessActFun] <;> ring)
    (fun c X v => by funext i; fin_cases i <;> simp [hlsWitnessActFun] <;> ring)
    (fun X u v => by funext i; fin_cases i <;> simp [hlsWitnessActFun] <;> ring)
    (fun X c v => by funext i; fin_cases i <;> simp [hlsWitnessActFun] <;> ring)

@[simp] theorem hlsWitnessAct_apply (X : HLSEven HLSNoCharge) (v : HLSWitnessOdd) :
    hlsWitnessAct X v = hlsWitnessActFun X v := rfl

/-- The bundled odd--odd bracket of the witness. -/
def hlsWitnessBr : HLSWitnessOdd →ₗ[ℂ] HLSWitnessOdd →ₗ[ℂ] HLSEven HLSNoCharge :=
  LinearMap.mk₂ ℂ (fun u v => hlsMom (hlsWitnessBrMat u v))
    (fun u u' v => by
      rw [← hlsMom_add]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hlsWitnessBrMat] <;> ring)
    (fun c u v => by
      rw [← hlsMom_smul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hlsWitnessBrMat] <;> ring)
    (fun u v v' => by
      rw [← hlsMom_add]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hlsWitnessBrMat] <;> ring)
    (fun u c v => by
      rw [← hlsMom_smul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hlsWitnessBrMat] <;> ring)

@[simp] theorem hlsWitnessBr_apply (u v : HLSWitnessOdd) :
    hlsWitnessBr u v = hlsMom (hlsWitnessBrMat u v) := rfl

/-- The bundled real structure of the witness. -/
def hlsWitnessConj : HLSWitnessOdd →ₛₗ[starRingEnd ℂ] HLSWitnessOdd where
  toFun := hlsWitnessConjFun
  map_add' u v := by funext i; fin_cases i <;> simp [hlsWitnessConjFun]
  map_smul' c v := by funext i; fin_cases i <;> simp [hlsWitnessConjFun]

@[simp] theorem hlsWitnessConj_apply (v : HLSWitnessOdd) :
    hlsWitnessConj v = hlsWitnessConjFun v := rfl

/-- The bundled state functional of the witness. -/
def hlsWitnessState : HLSEven HLSNoCharge →ₗ[ℂ] ℂ where
  toFun := hlsWitnessStateFun
  map_add' X Y := by simp [hlsWitnessStateFun]; ring
  map_smul' c X := by simp [hlsWitnessStateFun]; ring

@[simp] theorem hlsWitnessState_apply (X : HLSEven HLSNoCharge) :
    hlsWitnessState X = hlsWitnessStateFun X := rfl



/-- **The `N = 1` super-Poincaré algebra as an HLS graded symmetry.**
This inhabits `HLSGradedSymmetry`, so the Haag--Łopuszański--Sohnius hypotheses are not
vacuous. -/
def hlsWitness : HLSGradedSymmetry HLSNoCharge HLSWitnessOdd where
  internal := hlsWitnessInternalRealForm
  act := hlsWitnessAct
  br := hlsWitnessBr
  br_symm u v := by
    simp only [hlsWitnessBr_apply]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hlsWitnessBrMat] <;> ring
  act_lie X Y v := by
    simp only [hlsWitnessAct_apply, LinearMap.sub_apply]
    funext i
    fin_cases i <;>
      simp [hlsWitnessActFun, hlsEvenBr, hlsSl2Br] <;> ring
  act_br X u v := by
    simp only [hlsWitnessBr_apply, hlsWitnessAct_apply, hlsEvenBr_mom_right, ← hlsMom_add]
    congr 1
    simp only [hlsLorAct, hlsSl2Mat_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hlsSl2Mat, hlsWitnessBrMat, hlsWitnessActFun, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring
  jacobi u v w := by
    have hzero : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (x : HLSWitnessOdd),
        hlsWitnessAct (hlsMom M) x = 0 := by
      intro M x
      simp only [hlsWitnessAct_apply]
      funext i
      fin_cases i <;> simp [hlsWitnessActFun, hlsMom]
    simp only [hlsWitnessBr_apply, hzero]
    abel
  oddConj := hlsWitnessConj
  oddConj_conj v := by
    funext i
    fin_cases i <;> simp [hlsWitnessConj, hlsWitnessConjFun]
  oddConj_act X v := by
    simp only [hlsWitnessAct_apply, hlsWitnessConj_apply]
    funext i
    fin_cases i <;>
      simp [hlsWitnessConjFun, hlsWitnessActFun, hlsEvenConj, Pi.star_apply, map_add, map_mul,
        map_sub] <;> ring
  oddConj_br u v := by
    simp only [hlsWitnessBr_apply, hlsWitnessConj_apply]
    rw [hlsEvenConj_mom]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hlsWitnessBrMat, hlsWitnessConjFun, Matrix.conjTranspose_apply, map_add, map_mul,
        map_ofNat] <;> ring
  state := hlsWitnessState
  state_conj X := by
    simp [hlsWitnessState, hlsWitnessStateFun, hlsEvenConj, Matrix.conjTranspose_apply,
      map_add]
  state_mom_posDef := by
    have h : (Matrix.of fun a b => hlsWitnessState (hlsMom (B := HLSNoCharge)
        (Matrix.single a b (1 : ℂ)))) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hlsWitnessState, hlsWitnessStateFun, hlsMom, Matrix.single_apply,
          Matrix.one_apply]
    rw [h]
    exact Matrix.PosDef.one
  state_positive v hv := by
    have e0 : v 0 * (starRingEnd ℂ) (v 0) = (Complex.normSq (v 0) : ℂ) := Complex.mul_conj _
    have e1 : v 1 * (starRingEnd ℂ) (v 1) = (Complex.normSq (v 1) : ℂ) := Complex.mul_conj _
    have e2 : (starRingEnd ℂ) (v 2) * v 2 = (Complex.normSq (v 2) : ℂ) := by
      rw [mul_comm]; exact Complex.mul_conj _
    have e3 : (starRingEnd ℂ) (v 3) * v 3 = (Complex.normSq (v 3) : ℂ) := by
      rw [mul_comm]; exact Complex.mul_conj _
    have hval : hlsWitnessState (hlsWitnessBr v (hlsWitnessConj v))
        = ((2 * (Complex.normSq (v 0) + Complex.normSq (v 2) + Complex.normSq (v 1)
              + Complex.normSq (v 3)) : ℝ) : ℂ) := by
      simp only [hlsWitnessBr_apply, hlsWitnessConj_apply, hlsWitnessState_apply,
        hlsWitnessStateFun, hlsMom, hlsWitnessBrMat, hlsWitnessConjFun,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
      push_cast
      rw [← e0, ← e1, ← e2, ← e3]
      ring
    rw [hval, Complex.ofReal_re]
    have hne : ∃ i, v i ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hv (funext hcon)
    obtain ⟨i, hi⟩ := hne
    have h0 := Complex.normSq_nonneg (v 0)
    have h1 := Complex.normSq_nonneg (v 1)
    have h2 := Complex.normSq_nonneg (v 2)
    have h3 := Complex.normSq_nonneg (v 3)
    have hor : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 := by
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hi))
      · exact Or.inr (Or.inr (Or.inr hi))
    rcases hor with h | h | h | h
    · have := Complex.normSq_pos.mpr h; linarith
    · have := Complex.normSq_pos.mpr h; linarith
    · have := Complex.normSq_pos.mpr h; linarith
    · have := Complex.normSq_pos.mpr h; linarith

/-- The Haag--Łopuszański--Sohnius hypotheses are inhabited. -/
theorem hlsGradedSymmetry_nonempty :
    Nonempty (HLSGradedSymmetry HLSNoCharge HLSWitnessOdd) := ⟨hlsWitness⟩



/-- The Haag--Łopuszański--Sohnius classification applied to the `N = 1` witness: the
hypotheses are satisfiable and the conclusion is realized. -/
theorem hlsWitness_haag_lopuszanski_sohnius :
    ∃ (N : ℕ) (Q : Fin N → Fin 2 → HLSWitnessOdd) (Z : Fin N → Fin N → HLSNoCharge),
      (∀ I, Q I 0 ∈ hlsWitness.wt 1 0) ∧
      (∀ I, Q I 1 ∈ hlsWitness.wt (-1) 0) ∧
      (∀ I J α β, hlsWitness.br (Q I α) (hlsWitness.oddConj (Q J β))
          = hlsMom ((if I = J then (2 : ℂ) else 0) • hlsMomUnit α β)) ∧
      (∀ I J α β, hlsWitness.br (Q I α) (Q J β) = hlsEps α β • hlsInt (Z I J)) ∧
      (∀ I J, Z I J = -Z J I) ∧
      (∀ I J, hlsWitness.act (hlsInt (Z I J)) = 0) ∧
      (∀ P : Matrix (Fin 2) (Fin 2) ℂ, hlsWitness.act (hlsMom P) = 0) ∧
      (hlsWitness.wt 0 0 ⊔ (Submodule.span ℂ (Set.range fun p : Fin N × Fin 2 => Q p.1 p.2)
          ⊔ Submodule.span ℂ
            (Set.range fun p : Fin N × Fin 2 => hlsWitness.oddConj (Q p.1 p.2))) = ⊤) :=
  hlsWitness.haag_lopuszanski_sohnius


end GaloisForLFunctions.HTGeometry
