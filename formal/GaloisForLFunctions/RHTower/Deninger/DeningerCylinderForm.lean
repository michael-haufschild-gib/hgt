import GaloisForLFunctions.RHTower.Deninger.DeningerStageTransition

/-!
# Cylinder differential forms

A cylinder differential form on the character space is a holomorphic form at a finite character
stage, presented through finitely many evaluation coordinates; the cylinder de Rham complex is the
colimit of the stage complexes along the monomial transition maps.  The exterior derivative is
computed at the stage, stays cylinder, squares to zero, and commutes with the transitions, so it is
defined on the colimit.  Two cylinder forms are added by pulling both back to the concatenated
stage, along the coordinate projections, which are themselves monomial maps.

* `DeningerCylinderForm` : a form at a finite stage together with its evaluation coordinates.
* `DeningerCylinderForm.extDeriv`, `extDeriv_extDeriv` : the exterior derivative and `d ∘ d = 0`.
* `DeningerCylinderForm.transition`, `transition_extDeriv` : compatibility with the transitions.
* `DeningerCylinderForm.add` : the sum, formed on the concatenated stage.
-/

namespace RHTower

section Select

variable {r s : ℕ}

/-- A matrix that selects coordinates: the exponent matrix of a coordinate projection. -/
def deningerSelectMatrix (e : Fin r → Fin s) : Fin r → Fin s → ℤ :=
  fun i j => if j = e i then 1 else 0

/-- **The monomial map of a selection matrix is the reindexing of coordinates.**  Coordinate
projections between character stages are of this shape. -/
theorem deningerMonomialMap_select (e : Fin r → Fin s) :
    deningerMonomialMap (deningerSelectMatrix e) = fun z i => z (e i) := by
  funext z i
  show (∏ j, (z j) ^ (deningerSelectMatrix e i j)) = z (e i)
  rw [Finset.prod_eq_single (e i)]
  · simp [deningerSelectMatrix]
  · intro j _ hj
    rw [show deningerSelectMatrix e i j = 0 from if_neg hj, zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ (e i)) h

end Select

/-- **A cylinder differential form**: a holomorphic form at a finite character stage, together with
the evaluation coordinates that present the stage. -/
structure DeningerCylinderForm (V : Type*) (n : ℕ) where
  /-- The number of evaluation coordinates. -/
  rank : ℕ
  /-- The evaluation coordinates. -/
  coords : Fin rank → V
  /-- The form at the finite stage. -/
  form : DeningerStageForm rank n
  /-- The form is holomorphic on the stage. -/
  holo : DeningerIsHolomorphicForm form

namespace DeningerCylinderForm

variable {V : Type*} {n : ℕ}

/-- The coordinate tuple of a character. -/
def evalCoords (F : DeningerCylinderForm V n) (P : V → ℂ) : Fin F.rank → ℂ :=
  fun i => P (F.coords i)

/-- The value of a cylinder form at a character, a form in the evaluation coordinates. -/
def value (F : DeningerCylinderForm V n) (P : V → ℂ) :
    (Fin F.rank → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
  F.form (F.evalCoords P)

/-- **The exterior derivative of a cylinder form**, computed at its stage: it is again a cylinder
form, on the same coordinates. -/
noncomputable def extDeriv (F : DeningerCylinderForm V n) : DeningerCylinderForm V (n + 1) where
  rank := F.rank
  coords := F.coords
  form := _root_.extDeriv F.form
  holo := deningerStage_extDeriv_holomorphic F.holo

@[simp]
theorem extDeriv_rank (F : DeningerCylinderForm V n) : F.extDeriv.rank = F.rank := rfl

@[simp]
theorem extDeriv_coords (F : DeningerCylinderForm V n) : F.extDeriv.coords = F.coords := rfl

@[simp]
theorem extDeriv_form (F : DeningerCylinderForm V n) :
    F.extDeriv.form = _root_.extDeriv F.form := rfl

/-- **The exterior derivative squares to zero on cylinder forms.** -/
theorem extDeriv_extDeriv (F : DeningerCylinderForm V n) {P : V → ℂ}
    (hP : F.evalCoords P ∈ deningerStageTorus F.rank) :
    F.extDeriv.extDeriv.value P = 0 :=
  deningerStage_extDeriv_extDeriv F.holo hP

/-- **Transport of a cylinder form to a finer stage** along a monomial change of coordinates. -/
noncomputable def transition (F : DeningerCylinderForm V n) {s : ℕ} (b : Fin s → V)
    (m : Fin F.rank → Fin s → ℤ) : DeningerCylinderForm V n where
  rank := s
  coords := b
  form := deningerStagePullback (deningerMonomialMap m) F.form
  holo := deningerMonomialPullback_holomorphic m F.holo

@[simp]
theorem transition_rank (F : DeningerCylinderForm V n) {s : ℕ} (b : Fin s → V)
    (m : Fin F.rank → Fin s → ℤ) : (F.transition b m).rank = s := rfl

/-- **The exterior derivative commutes with the transition maps**, so it is defined on the colimit
of the stage complexes. -/
theorem transition_extDeriv (F : DeningerCylinderForm V n) {s : ℕ} (b : Fin s → V)
    (m : Fin F.rank → Fin s → ℤ) {z : Fin s → ℂ} (hz : z ∈ deningerStageTorus s) :
    (F.transition b m).extDeriv.form z = (F.extDeriv.transition b m).form z :=
  deningerMonomialPullback_extDeriv m F.holo hz

/-- **The transition of a cylinder form is a genuine restatement of the same form**: if the coarse
coordinates of a character are the monomials of its fine coordinates, both stages give the same
value on the tangent vectors that the fine stage sees. -/
theorem transition_value (F : DeningerCylinderForm V n) {s : ℕ} (b : Fin s → V)
    (m : Fin F.rank → Fin s → ℤ) (P : V → ℂ)
    (hP : F.evalCoords P = deningerMonomialMap m fun j => P (b j))
    (v : Fin n → (Fin s → ℂ)) :
    (F.transition b m).value P v =
      F.value P fun i => fderiv ℂ (deningerMonomialMap m) (fun j => P (b j)) (v i) := by
  show F.form (deningerMonomialMap m fun j => P (b j))
      (fun i => fderiv ℂ (deningerMonomialMap m) (fun j => P (b j)) (v i)) = _
  rw [value, hP]

section Add

variable {n : ℕ}

/-- The left coordinate projection out of a concatenated stage. -/
def leftMatrix (r s : ℕ) : Fin r → Fin (r + s) → ℤ :=
  deningerSelectMatrix (Fin.castAdd s)

/-- The right coordinate projection out of a concatenated stage. -/
def rightMatrix (r s : ℕ) : Fin s → Fin (r + s) → ℤ :=
  deningerSelectMatrix (Fin.natAdd r)

/-- **The sum of two cylinder forms**, formed after pulling both back to the concatenated stage
along the coordinate projections. -/
noncomputable def add (F G : DeningerCylinderForm V n) : DeningerCylinderForm V n where
  rank := F.rank + G.rank
  coords := Fin.append F.coords G.coords
  form := deningerStagePullback (deningerMonomialMap (leftMatrix F.rank G.rank)) F.form +
    deningerStagePullback (deningerMonomialMap (rightMatrix F.rank G.rank)) G.form
  holo := deningerIsHolomorphicForm_add
    (deningerMonomialPullback_holomorphic _ F.holo)
    (deningerMonomialPullback_holomorphic _ G.holo)

@[simp]
theorem add_rank (F G : DeningerCylinderForm V n) : (F.add G).rank = F.rank + G.rank := rfl

@[simp]
theorem add_coords (F G : DeningerCylinderForm V n) :
    (F.add G).coords = Fin.append F.coords G.coords := rfl

/-- The coordinates of the concatenated stage restrict to those of the two summands. -/
theorem add_evalCoords_left (F G : DeningerCylinderForm V n) (P : V → ℂ) :
    (fun i => (F.add G).evalCoords P (Fin.castAdd G.rank i)) = F.evalCoords P := by
  funext i
  simp [evalCoords, Fin.append_left]

theorem add_evalCoords_right (F G : DeningerCylinderForm V n) (P : V → ℂ) :
    (fun i => (F.add G).evalCoords P (Fin.natAdd F.rank i)) = G.evalCoords P := by
  funext i
  simp [evalCoords, Fin.append_right]

end Add

end DeningerCylinderForm

end RHTower
