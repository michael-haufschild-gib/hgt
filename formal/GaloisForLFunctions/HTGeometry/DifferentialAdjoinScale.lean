import GaloisForLFunctions.HTGeometry.FreeDifferentialFamilyScale

/-!
# Scalar action on a freely generated differential field

The scalar-isotropy theorem in `FreeDifferentialFamilyScale` is phrased for a family generating its
whole ambient field.  A Manin horizon is naturally an embedded intermediate field
`F⟨x_i⟩`.  This file proves that the lifted generators are still differentially independent and
generate that intermediate field internally, then constructs the exact simultaneous scalar
automorphism of the embedded horizon.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F K ι : Type*} [Field F] [Field K]
  [Algebra F K] [Differential F] [Differential K]
  [DifferentialAlgebra F K]

/-- Ambient coercion commutes with every differential jet on a differential adjunction. -/
@[simp]
theorem coe_differentialJet_differentialAdjoin
    (S : Set K) (n : ℕ) (x : differentialAdjoin F S) :
    ((differentialJet n x : differentialAdjoin F S) : K) =
      differentialJet n (x : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, ← ih]
      rfl

/-- Order-zero lift of a generating family into its embedded differential field. -/
def differentialAdjoinGenerator (x : ι → K) (i : ι) :
    differentialAdjoin F (Set.range x) :=
  ⟨x i, subset_differentialAdjoin F (Set.range x) (Set.mem_range_self i)⟩

omit [Differential F] [DifferentialAlgebra F K] in
@[simp]
theorem coe_differentialAdjoinGenerator (x : ι → K) (i : ι) :
    (differentialAdjoinGenerator (F := F) x i : K) = x i :=
  rfl

/-- Differential independence survives the canonical lift into the generated intermediate field. -/
theorem differentialIndependent_differentialAdjoinGenerator
    (x : ι → K) (hx : DifferentialIndependent F x) :
    DifferentialIndependent F (differentialAdjoinGenerator (F := F) x) := by
  unfold DifferentialIndependent at hx ⊢
  apply AlgebraicIndependent.of_comp
    (differentialAdjoin F (Set.range x)).val
  convert hx using 1
  funext p
  exact coe_differentialJet_differentialAdjoin
    (F := F) (Set.range x) p.2 (differentialAdjoinGenerator (F := F) x p.1)

/-- The lifted family generates its differential adjunction as an internal differential field. -/
theorem differentialAdjoin_range_differentialAdjoinGenerator_eq_top
    (x : ι → K) :
    differentialAdjoin F
        (Set.range (differentialAdjoinGenerator (F := F) x)) =
      (⊤ : IntermediateField F (differentialAdjoin F (Set.range x))) := by
  apply top_unique
  intro z hz
  let E : IntermediateField F K := differentialAdjoin F (Set.range x)
  let T : IntermediateField F E :=
    differentialAdjoin F
      (Set.range (differentialAdjoinGenerator (F := F) x))
  let p : ∀ y : K, y ∈ E → Prop := fun y hy => (⟨y, hy⟩ : E) ∈ T
  change p z.1 z.2
  refine IntermediateField.adjoin_induction F (p := p) ?_ ?_ ?_ ?_ ?_ z.2
  · rintro y ⟨w, ⟨i, rfl⟩, n, rfl⟩
    have hjet :
        differentialJet n (differentialAdjoinGenerator (F := F) x i) ∈ T :=
      differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n
    have heq :
        (⟨differentialJet n (x i),
            differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ : E) =
          differentialJet n (differentialAdjoinGenerator (F := F) x i) := by
      apply Subtype.ext
      exact (coe_differentialJet_differentialAdjoin
        (F := F) (Set.range x) n
          (differentialAdjoinGenerator (F := F) x i)).symm
    change
      (⟨differentialJet n (x i),
          differentialJet_mem_differentialAdjoin F (Set.mem_range_self i) n⟩ : E) ∈ T
    rw [heq]
    exact hjet
  · intro c
    change (⟨algebraMap F K c, E.algebraMap_mem c⟩ : E) ∈ T
    have heq : (⟨algebraMap F K c, E.algebraMap_mem c⟩ : E) = algebraMap F E c := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact T.algebraMap_mem c
  · intro a b ha hb hpa hpb
    change (⟨a + b, E.add_mem ha hb⟩ : E) ∈ T
    have heq : (⟨a + b, E.add_mem ha hb⟩ : E) =
        (⟨a, ha⟩ : E) + ⟨b, hb⟩ := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact T.add_mem hpa hpb
  · intro a ha hpa
    change (⟨a⁻¹, E.inv_mem ha⟩ : E) ∈ T
    have heq : (⟨a⁻¹, E.inv_mem ha⟩ : E) = (⟨a, ha⟩ : E)⁻¹ := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact T.inv_mem hpa
  · intro a b ha hb hpa hpb
    change (⟨a * b, E.mul_mem ha hb⟩ : E) ∈ T
    have heq : (⟨a * b, E.mul_mem ha hb⟩ : E) =
        (⟨a, ha⟩ : E) * ⟨b, hb⟩ := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact T.mul_mem hpa hpb

/-- Simultaneous multiplication by a nonzero base scalar on every free horizon coordinate. -/
def differentialIndependentAdjoinScaleDifferentialAlgEquiv
    (x : ι → K) (hx : DifferentialIndependent F x) (u : Fˣ) :
    DifferentialAlgEquiv F (differentialAdjoin F (Set.range x)) :=
  differentialIndependentFamilyScaleDifferentialAlgEquiv
    (differentialAdjoinGenerator (F := F) x)
    (differentialIndependent_differentialAdjoinGenerator x hx)
    (differentialAdjoin_range_differentialAdjoinGenerator_eq_top x) u

@[simp]
theorem differentialIndependentAdjoinScaleDifferentialAlgEquiv_apply
    (x : ι → K) (hx : DifferentialIndependent F x) (u : Fˣ) (i : ι) :
    (differentialIndependentAdjoinScaleDifferentialAlgEquiv x hx u).toAlgEquiv
        (differentialAdjoinGenerator (F := F) x i) =
      algebraMap F (differentialAdjoin F (Set.range x)) (u : F) *
        differentialAdjoinGenerator (F := F) x i :=
  differentialIndependentFamilyScaleDifferentialAlgEquiv_apply
    (differentialAdjoinGenerator (F := F) x)
    (differentialIndependent_differentialAdjoinGenerator x hx)
    (differentialAdjoin_range_differentialAdjoinGenerator_eq_top x) u i

/-- Ambient form of the scalar-coordinate law. -/
theorem coe_differentialIndependentAdjoinScaleDifferentialAlgEquiv_apply
    (x : ι → K) (hx : DifferentialIndependent F x) (u : Fˣ) (i : ι) :
    (((differentialIndependentAdjoinScaleDifferentialAlgEquiv x hx u).toAlgEquiv
        (differentialAdjoinGenerator (F := F) x i) :
          differentialAdjoin F (Set.range x)) : K) =
      algebraMap F K (u : F) * x i := by
  exact congrArg Subtype.val
    (differentialIndependentAdjoinScaleDifferentialAlgEquiv_apply x hx u i)

omit [Differential F] in
/-- Two differential algebra homomorphisms out of a differentially generated field are determined
by the order-zero generators. -/
theorem differentialAlgHom_ext_of_differentialAdjoin_eq_top
    {E M κ : Type*} [Field E] [Field M]
    [Algebra F E] [Algebra F M]
    [Differential E] [Differential M]
    (x : κ → E) (hgen : differentialAdjoin F (Set.range x) = ⊤)
    (f g : E →ₐ[F] M)
    (hfderiv : ∀ z : E, f z′ = (f z)′)
    (hgderiv : ∀ z : E, g z′ = (g z)′)
    (hx : ∀ i, f (x i) = g (x i)) :
    f = g := by
  apply AlgHom.ext
  intro z
  have hz : z ∈ differentialAdjoin F (Set.range x) := by
    rw [hgen]
    exact IntermediateField.mem_top
  let p : ∀ y : E, y ∈ differentialAdjoin F (Set.range x) → Prop :=
    fun y _ => f y = g y
  change p z hz
  refine IntermediateField.adjoin_induction F (p := p) ?_ ?_ ?_ ?_ ?_ hz
  · rintro y ⟨w, ⟨i, rfl⟩, n, rfl⟩
    induction n with
    | zero =>
        change f (differentialJet 0 (x i)) = g (differentialJet 0 (x i))
        simpa only [differentialJet_zero] using hx i
    | succ n ih =>
        change f (differentialJet (n + 1) (x i)) =
          g (differentialJet (n + 1) (x i))
        change f (differentialJet n (x i)) = g (differentialJet n (x i)) at ih
        rw [differentialJet_succ, hfderiv, hgderiv, ih]
  · intro c
    change f (algebraMap F E c) = g (algebraMap F E c)
    exact f.commutes c |>.trans (g.commutes c).symm
  · intro a b ha hb hfa hfb
    change f (a + b) = g (a + b)
    change f a = g a at hfa
    change f b = g b at hfb
    simpa only [map_add] using congrArg₂ (· + ·) hfa hfb
  · intro a ha hfa
    change f a⁻¹ = g a⁻¹
    change f a = g a at hfa
    simpa only [map_inv₀] using congrArg Inv.inv hfa
  · intro a b ha hb hfa hfb
    change f (a * b) = g (a * b)
    change f a = g a at hfa
    change f b = g b at hfb
    simpa only [map_mul] using congrArg₂ (· * ·) hfa hfb

/-- Canonical equivalence between two free differential horizons conjugates their simultaneous
nonzero scalar actions.  This is the exact dynamical, rather than merely field-theoretic, no-hair
statement. -/
theorem differentialIndependentAdjoinAlgEquiv_scale_commutes
    {L : Type*} [Field L] [Algebra F L] [Differential L]
    [DifferentialAlgebra F L]
    (x : ι → K) (y : ι → L)
    (hx : DifferentialIndependent F x) (hy : DifferentialIndependent F y)
    (u : Fˣ) (z : differentialAdjoin F (Set.range x)) :
    GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy
        ((differentialIndependentAdjoinScaleDifferentialAlgEquiv x hx u).toAlgEquiv z) =
      (differentialIndependentAdjoinScaleDifferentialAlgEquiv y hy u).toAlgEquiv
        (GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy z) := by
  let xE : ι → differentialAdjoin F (Set.range x) :=
    differentialAdjoinGenerator (F := F) x
  let yE : ι → differentialAdjoin F (Set.range y) :=
    differentialAdjoinGenerator (F := F) y
  let e := GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv x y hx hy
  let sx := differentialIndependentAdjoinScaleDifferentialAlgEquiv x hx u
  let sy := differentialIndependentAdjoinScaleDifferentialAlgEquiv y hy u
  let f : differentialAdjoin F (Set.range x) →ₐ[F]
      differentialAdjoin F (Set.range y) := e.toAlgHom.comp sx.toAlgEquiv.toAlgHom
  let g : differentialAdjoin F (Set.range x) →ₐ[F]
      differentialAdjoin F (Set.range y) := sy.toAlgEquiv.toAlgHom.comp e.toAlgHom
  have hfderiv (w : differentialAdjoin F (Set.range x)) : f w′ = (f w)′ := by
    change e (sx.toAlgEquiv w′) = (e (sx.toAlgEquiv w))′
    rw [sx.map_deriv',
      GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv_deriv]
  have hgderiv (w : differentialAdjoin F (Set.range x)) : g w′ = (g w)′ := by
    change sy.toAlgEquiv (e w′) = (sy.toAlgEquiv (e w))′
    rw [GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv_deriv,
      sy.map_deriv']
  have hxy (i : ι) : e (xE i) = yE i := by
    simpa only [xE, yE, differentialAdjoinGenerator, differentialJet_zero] using
      (GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv_jet
        x y hx hy i 0)
  have hfgenerator (i : ι) : f (xE i) = g (xE i) := by
    change e (sx.toAlgEquiv (xE i)) = sy.toAlgEquiv (e (xE i))
    rw [show sx.toAlgEquiv (xE i) =
        algebraMap F (differentialAdjoin F (Set.range x)) (u : F) * xE i by
          exact differentialIndependentAdjoinScaleDifferentialAlgEquiv_apply x hx u i,
      map_mul, e.commutes, hxy,
      differentialIndependentAdjoinScaleDifferentialAlgEquiv_apply]
  have hfg : f = g :=
    differentialAlgHom_ext_of_differentialAdjoin_eq_top xE
      (differentialAdjoin_range_differentialAdjoinGenerator_eq_top x)
      f g hfderiv hgderiv hfgenerator
  exact AlgHom.congr_fun hfg z

/-- A derivation-preserving ambient endomorphism which scales the free quotient coordinates agrees
on their entire differential field with the canonical scalar automorphism. -/
theorem algHom_eq_coe_differentialIndependentAdjoinScale_on_differentialAdjoin
    (x : ι → K) (hx : DifferentialIndependent F x) (u : Fˣ)
    (φ : K →ₐ[F] K)
    (hφderiv : ∀ z : K, φ z′ = (φ z)′)
    (hφx : ∀ i, φ (x i) = algebraMap F K (u : F) * x i)
    (z : differentialAdjoin F (Set.range x)) :
    φ z.1 =
      ((differentialIndependentAdjoinScaleDifferentialAlgEquiv x hx u).toAlgEquiv z).1 := by
  let E : IntermediateField F K := differentialAdjoin F (Set.range x)
  let xE : ι → E := differentialAdjoinGenerator (F := F) x
  let σ := differentialIndependentAdjoinScaleDifferentialAlgEquiv x hx u
  let f : E →ₐ[F] K := φ.comp E.val
  let g : E →ₐ[F] K := E.val.comp σ.toAlgEquiv.toAlgHom
  have hfderiv (w : E) : f w′ = (f w)′ := by
    change φ w.1′ = (φ w.1)′
    exact hφderiv w.1
  have hgderiv (w : E) : g w′ = (g w)′ := by
    change (σ.toAlgEquiv w′).1 = (σ.toAlgEquiv w).1′
    exact congrArg Subtype.val (σ.map_deriv' w)
  have hfgenerator (i : ι) : f (xE i) = g (xE i) := by
    change φ (x i) = (σ.toAlgEquiv (xE i)).1
    rw [hφx,
      show (σ.toAlgEquiv (xE i)).1 = algebraMap F K (u : F) * x i by
        exact coe_differentialIndependentAdjoinScaleDifferentialAlgEquiv_apply x hx u i]
  have hfg : f = g :=
    differentialAlgHom_ext_of_differentialAdjoin_eq_top xE
      (differentialAdjoin_range_differentialAdjoinGenerator_eq_top x)
      f g hfderiv hgderiv hfgenerator
  exact AlgHom.congr_fun hfg z

end

end GaloisForLFunctions.HTGeometry
