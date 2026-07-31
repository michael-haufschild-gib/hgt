import GaloisForLFunctions.HTGeometry.EntireSRRealization
import GaloisForLFunctions.HTGeometry.SRDifferenceCarrier
import GaloisForLFunctions.HTGeometry.BoundaryWedgeTwoThick

/-!
# Gluing two one-variable seeds into an entire two-variable realization of the boundary wedge

The boundary wedge has two blocks meeting at the common centre, and the periodic pencil moves each
block along its own coordinate.  A seed of the form `F(z₁, z₂) = G(z₁) + H(z₂)` therefore turns the
mixed nonface relations into identities — a left step does not move `z₁` and a right step does not
move `z₂` — and the two block relations into one-variable relations for `H` and for `G`.

The one-variable input for a block `B` is a `BlockSeed`: steps vanishing off `B`, an entire carrier
seed annihilated by the full block product of difference operators, and faithfulness — a polynomial
with a monomial supported inside `B` but not containing all of `B` has nonconstant carrier.

* `BlockSeed` — the one-variable datum for one block;
* `seedCarrierPoly_splitSeed` — the carrier of the glued seed splits along the two coordinates;
* `boundaryWedgeEntireRealization` — two block seeds with `ℚ`-independent glued steps give an
  entire two-variable realization of the boundary wedge.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Gluing two one-variable step families and seeds -/

variable {α : Type*}

/-- The two-coordinate steps glued from a first-coordinate and a second-coordinate family. -/
def splitSteps (b a : α → ℂ) : α → (Fin 2 → ℂ) := fun v => ![b v, a v]

/-- The two-coordinate seed glued from two one-variable seeds. -/
def splitSeed (G H : ℂ → ℂ) : (Fin 2 → ℂ) → ℂ := fun z => G (z 0) + H (z 1)

theorem differentiable_coord (i : Fin 2) : Differentiable ℂ fun z : Fin 2 → ℂ => z i :=
  differentiable_apply i

theorem differentiable_splitSeed {G H : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hH : Differentiable ℂ H) : Differentiable ℂ (splitSeed G H) :=
  (hG.comp (differentiable_coord 0)).add (hH.comp (differentiable_coord 1))

/-- **The glued carrier splits along the two coordinates.** -/
theorem seedCarrierPoly_splitSeed (b a : α → ℂ) (G H : ℂ → ℂ) (P : MvPolynomial α ℂ) :
    seedCarrierPoly (splitSteps b a) (splitSeed G H) P
      = fun z => seedCarrierPoly b G P (z 0) + seedCarrierPoly a H P (z 1) := by
  refine MvPolynomial.induction_on
    (motive := fun P => seedCarrierPoly (splitSteps b a) (splitSeed G H) P
      = fun z => seedCarrierPoly b G P (z 0) + seedCarrierPoly a H P (z 1))
    P (fun c => ?_) (fun p q hp hq => ?_) (fun p n hp => ?_)
  · rw [seedCarrierPoly_C, seedCarrierPoly_C, seedCarrierPoly_C]
    funext z
    show c * (G (z 0) + H (z 1)) = c * G (z 0) + c * H (z 1)
    ring
  · funext z
    have hpz := congrFun hp z
    have hqz := congrFun hq z
    rw [seedCarrierPoly_add]
    show seedCarrierPoly (splitSteps b a) (splitSeed G H) p z
      + seedCarrierPoly (splitSteps b a) (splitSeed G H) q z = _
    rw [hpz, hqz, seedCarrierPoly_add, seedCarrierPoly_add]
    show _ = (seedCarrierPoly b G p + seedCarrierPoly b G q) (z 0)
      + (seedCarrierPoly a H p + seedCarrierPoly a H q) (z 1)
    simp only [Pi.add_apply]
    ring
  · funext z
    rw [mul_comm p (X n), seedCarrierPoly_X_mul, seedCarrierPoly_X_mul, seedCarrierPoly_X_mul]
    show seedCarrierPoly (splitSteps b a) (splitSeed G H) p (z + splitSteps b a n)
        - seedCarrierPoly (splitSteps b a) (splitSeed G H) p z
      = (seedCarrierPoly b G p (z 0 + b n) - seedCarrierPoly b G p (z 0))
        + (seedCarrierPoly a H p (z 1 + a n) - seedCarrierPoly a H p (z 1))
    have h0 : (z + splitSteps b a n) 0 = z 0 + b n := rfl
    have h1 : (z + splitSteps b a n) 1 = z 1 + a n := rfl
    rw [congrFun hp (z + splitSteps b a n), congrFun hp z, h0, h1]
    ring

/-! ### The one-variable datum for one block -/

variable [DecidableEq α]

/-- **A one-variable block seed.**  Steps vanishing off the block, an entire seed annihilated by the
full block product of difference operators, and faithfulness for polynomials having a monomial
supported inside the block but not containing the whole block. -/
structure BlockSeed (B : Finset α) where
  /-- The one-variable translation step of each vertex; zero off the block. -/
  step : α → ℂ
  /-- Vertices outside the block do not move the seed. -/
  step_off : ∀ v ∉ B, step v = 0
  /-- The seed. -/
  seed : ℂ → ℂ
  /-- The seed is entire. -/
  seed_entire : Differentiable ℂ seed
  /-- The full block product of difference operators annihilates the seed. -/
  seed_ann : shiftAlgHom (∏ v ∈ B, stepVar step v) seed = 0
  /-- A polynomial with a monomial supported inside the block and missing a block vertex has
  nonconstant carrier. -/
  seed_nonconstant : ∀ P : MvPolynomial α ℂ,
    (∃ m ∈ P.support, m.support ⊆ B ∧ ¬ B ⊆ m.support) →
    ∃ x y, seedCarrierPoly step seed P x ≠ seedCarrierPoly step seed P y

namespace BlockSeed

variable {B : Finset α}

/-- The block product of difference operators over any set that is not a proper subset of the block
annihilates the seed: either a step outside the block makes a factor vanish, or the set is the whole
block. -/
theorem shiftAlgHom_prod_eq_zero (S : BlockSeed B) {J : Finset α} (hJ : J ⊆ B → J = B) :
    shiftAlgHom (∏ v ∈ J, stepVar S.step v) S.seed = 0 := by
  by_cases hsub : J ⊆ B
  · rw [hJ hsub]
    exact S.seed_ann
  · obtain ⟨v, hvJ, hvB⟩ := Finset.not_subset.mp hsub
    have hzero : (∏ v ∈ J, stepVar S.step v) = 0 :=
      Finset.prod_eq_zero hvJ (stepVar_eq_zero (S.step_off v hvB))
    rw [hzero, map_zero]
    rfl

omit [DecidableEq α] in
theorem differentiable_seedCarrierPoly (S : BlockSeed B) (P : MvPolynomial α ℂ) :
    Differentiable ℂ (seedCarrierPoly S.step S.seed P) :=
  differentiable_shiftAlgHom _ S.seed_entire

end BlockSeed

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.UniformBoundaryWedge

open GaloisForLFunctions.HTGeometry MvPolynomial

noncomputable section

variable {r s : ℕ}

/-- The glued two-coordinate seed of two block seeds. -/
def glueSeed (SL : BlockSeed (leftBlock r s)) (SR : BlockSeed (rightBlock r s)) :
    (Fin 2 → ℂ) → ℂ :=
  splitSeed SR.seed SL.seed

/-- The glued two-coordinate steps of two block seeds: the right block moves the first coordinate
and the left block moves the second. -/
def glueSteps (SL : BlockSeed (leftBlock r s)) (SR : BlockSeed (rightBlock r s)) :
    BoundaryWedgeVertex r s → (Fin 2 → ℂ) :=
  splitSteps SR.step SL.step

/-- A set that is not a face of the boundary wedge is not a proper subset of either block. -/
theorem eq_block_of_not_isFaceOf {J : Finset (BoundaryWedgeVertex r s)}
    (hJ : ¬ IsFaceOf (↑(boundaryWedgeFacetFinset r s) :
      Set (Finset (BoundaryWedgeVertex r s))) J) :
    (J ⊆ leftBlock r s → J = leftBlock r s) ∧ (J ⊆ rightBlock r s → J = rightBlock r s) := by
  rw [coe_boundaryWedgeFacetFinset, isFaceOf_boundaryWedgeFacets_iff] at hJ
  constructor
  · intro hsub
    by_contra hne
    exact hJ (Or.inl ⟨hsub, hne⟩)
  · intro hsub
    by_contra hne
    exact hJ (Or.inr ⟨hsub, hne⟩)

/-- **The glued seed is annihilated by the Stanley–Reisner ideal of the boundary wedge.** -/
theorem seedAnnihilates_glue (SL : BlockSeed (leftBlock r s)) (SR : BlockSeed (rightBlock r s)) :
    SeedAnnihilates (glueSteps SL SR) (boundaryWedgeFacetFinset r s) (glueSeed SL SR) := by
  intro J hJ
  obtain ⟨hL, hR⟩ := eq_block_of_not_isFaceOf hJ
  have hsplit := seedCarrierPoly_splitSeed SR.step SL.step SR.seed SL.seed (∏ v ∈ J, X v)
  rw [seedCarrierPoly_prod_X, seedCarrierPoly_prod_X, seedCarrierPoly_prod_X] at hsplit
  show shiftAlgHom (∏ v ∈ J, stepVar (glueSteps SL SR) v) (glueSeed SL SR) = 0
  rw [glueSteps, glueSeed, hsplit, SR.shiftAlgHom_prod_eq_zero hR,
    SL.shiftAlgHom_prod_eq_zero hL]
  funext z
  simp

/-- **The entire two-variable realization of the boundary wedge built from two block seeds.** -/
def boundaryWedgeEntireRealization (SL : BlockSeed (leftBlock r s))
    (SR : BlockSeed (rightBlock r s))
    (hindep : LinearIndependent ℚ (glueSteps SL SR)) :
    EntireSRRealization 2 (boundaryWedgeFacetFinset r s) where
  ω := glueSteps SL SR
  indep := hindep
  carrier := seedCarrier (glueSteps SL SR) (boundaryWedgeFacetFinset r s) (glueSeed SL SR)
    (seedAnnihilates_glue SL SR)
  carrier_entire := fun q =>
    differentiable_seedCarrier _ _ (differentiable_splitSeed SR.seed_entire SL.seed_entire) _ q
  carrier_zero := map_zero _
  carrier_vertex := fun v q => seedCarrier_srVertexX_mul _ _ _ _ v q
  carrier_nonconstant := by
    intro q hq
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective
      (I := stanleyReisnerIdeal ℂ (boundaryWedgeFacetFinset r s)) q
    have hPI : P ∉ stanleyReisnerIdeal ℂ (boundaryWedgeFacetFinset r s) := by
      intro hP
      exact hq ((Submodule.Quotient.mk_eq_zero _).mpr hP)
    obtain ⟨m, hmP, hface⟩ : ∃ m ∈ P.support,
        IsFaceOf (↑(boundaryWedgeFacetFinset r s) :
          Set (Finset (BoundaryWedgeVertex r s))) m.support := by
      by_contra hcon
      refine hPI ((mem_stanleyReisnerIdeal_iff _ P).mpr fun m hm hface => hcon ⟨m, hm, hface⟩)
    rw [coe_boundaryWedgeFacetFinset, isFaceOf_boundaryWedgeFacets_iff] at hface
    have hcarrier : ∀ z : Fin 2 → ℂ,
        seedCarrier (glueSteps SL SR) (boundaryWedgeFacetFinset r s) (glueSeed SL SR)
          (seedAnnihilates_glue SL SR) (Ideal.Quotient.mk _ P) z
          = seedCarrierPoly SR.step SR.seed P (z 0)
            + seedCarrierPoly SL.step SL.seed P (z 1) := by
      intro z
      rw [seedCarrier_mk]
      exact congrFun (seedCarrierPoly_splitSeed SR.step SL.step SR.seed SL.seed P) z
    rcases hface with ⟨hsub, hne⟩ | ⟨hsub, hne⟩
    · obtain ⟨x, y, hxy⟩ :=
        SL.seed_nonconstant P ⟨m, hmP, hsub, fun hcon => hne (Finset.Subset.antisymm hsub hcon)⟩
      refine ⟨![0, x], ![0, y], ?_⟩
      rw [hcarrier ![0, x], hcarrier ![0, y]]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact fun h => hxy (add_left_cancel h)
    · obtain ⟨x, y, hxy⟩ :=
        SR.seed_nonconstant P ⟨m, hmP, hsub, fun hcon => hne (Finset.Subset.antisymm hsub hcon)⟩
      refine ⟨![x, 0], ![y, 0], ?_⟩
      rw [hcarrier ![x, 0], hcarrier ![y, 0]]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact fun h => hxy (add_right_cancel h)

/-- **The boundary wedge is entirely realizable in two variables** once both blocks carry a one
variable seed with `ℚ`-independent glued steps. -/
theorem boundaryWedgeHTRealizable_two (SL : BlockSeed (leftBlock r s))
    (SR : BlockSeed (rightBlock r s)) (hindep : LinearIndependent ℚ (glueSteps SL SR)) :
    BoundaryWedgeHTRealizable r s 2 :=
  ⟨boundaryWedgeEntireRealization SL SR hindep⟩

end

end GaloisForLFunctions.UniformBoundaryWedge
