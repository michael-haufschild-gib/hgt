import GaloisForLFunctions.RHTower.SelbergMaassRationalTrace
import GaloisForLFunctions.RHTower.MaassHomogeneousSpaceCorrespondence

/-!
# Rational Maass trace and the right regular action

This file places the literal rational pullback and finite relative-coset trace in one
`GL(2, ℝ)` automorphic carrier.  A positive rational correspondence changes the left
invariance subgroup, hence is an inter-quotient map; it is not prematurely treated as
an endomorphism of one quotient.  In that carrier it is left multiplication, and both
pullback and finite trace commute exactly with every right `SL(2, ℝ)` translation.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

abbrev GL2R := GL (Fin 2) ℝ

/-- Left `Γ`-invariant functions on `GL(2, ℝ)`.  The right `SL(2, ℝ)` action is retained
without first choosing a determinant-normalization of a positive `GL(2, ℝ)` matrix. -/
def glAutomorphicFunctionSpace (Γ : Subgroup GL2R) : Submodule ℂ (GL2R → ℂ) where
  carrier := {F | ∀ γ : Γ, ∀ x : GL2R, F (γ.val * x) = F x}
  zero_mem' := by
    intro γ x
    rfl
  add_mem' := by
    intro F K hF hK γ x
    simp only [Pi.add_apply, hF γ x, hK γ x]
  smul_mem' := by
    intro c F hF γ x
    simp only [Pi.smul_apply, hF γ x]

@[simp]
theorem mem_glAutomorphicFunctionSpace (Γ : Subgroup GL2R) (F : GL2R → ℂ) :
    F ∈ glAutomorphicFunctionSpace Γ ↔
      ∀ γ : Γ, ∀ x : GL2R, F (γ.val * x) = F x :=
  Iff.rfl

/-- Right translation by an `SL(2, ℝ)` element preserves every left quotient. -/
def glAutomorphicRightTranslation (Γ : Subgroup GL2R) (k : SL2R) :
    glAutomorphicFunctionSpace Γ →ₗ[ℂ] glAutomorphicFunctionSpace Γ where
  toFun F :=
    ⟨fun x => F.1 (x * Matrix.SpecialLinearGroup.toGL k), by
      intro γ x
      change F.1 ((γ.val * x) * Matrix.SpecialLinearGroup.toGL k) =
        F.1 (x * Matrix.SpecialLinearGroup.toGL k)
      rw [mul_assoc]
      exact F.property γ (x * Matrix.SpecialLinearGroup.toGL k)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right regular `SL(2, ℝ)` representation on the `GL(2, ℝ)` quotient carrier. -/
def glAutomorphicRightRegularRepresentation (Γ : Subgroup GL2R) :
    Representation ℂ SL2R (glAutomorphicFunctionSpace Γ) where
  toFun := glAutomorphicRightTranslation Γ
  map_one' := by
    ext F x
    change F.1 (x * Matrix.SpecialLinearGroup.toGL (1 : SL2R)) = F.1 x
    simp
  map_mul' k₁ k₂ := by
    ext F x
    change F.1 (x * Matrix.SpecialLinearGroup.toGL (k₁ * k₂)) =
      F.1 ((x * Matrix.SpecialLinearGroup.toGL k₁) * Matrix.SpecialLinearGroup.toGL k₂)
    rw [map_mul, mul_assoc]

@[simp]
theorem glAutomorphicRightRegularRepresentation_apply (Γ : Subgroup GL2R)
    (k : SL2R) (x : GL2R) (F : glAutomorphicFunctionSpace Γ) :
    (glAutomorphicRightRegularRepresentation Γ k F).1 x =
      F.1 (x * Matrix.SpecialLinearGroup.toGL k) :=
  rfl

/-- Lift a `GL(2, ℝ)`-invariant function along the orbit map `x ↦ x • I`. -/
def glLiftInvariantFunction (Γ : Subgroup GL2R) :
    glUpperHalfPlaneInvariantFunctions Γ →ₗ[ℂ] glAutomorphicFunctionSpace Γ where
  toFun f :=
    ⟨fun x => f.1 (x • UpperHalfPlane.I), by
      intro γ x
      simpa only [mul_smul] using f.property γ (x • UpperHalfPlane.I)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem glLiftInvariantFunction_apply (Γ : Subgroup GL2R)
    (f : glUpperHalfPlaneInvariantFunctions Γ) (x : GL2R) :
    (glLiftInvariantFunction Γ f).1 x = f.1 (x • UpperHalfPlane.I) :=
  rfl

/-- Left multiplication carries a `Γ`-quotient to the quotient by its conjugate.
This is the automorphic realization of pullback. -/
def glAutomorphicLeftTranslation (g : GL2R) (Γ : Subgroup GL2R) :
    glAutomorphicFunctionSpace Γ →ₗ[ℂ]
      glAutomorphicFunctionSpace (ConjAct.toConjAct g⁻¹ • Γ) where
  toFun F :=
    ⟨fun x => F.1 (g * x), by
      intro γ x
      have hγ := γ.2
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hγ
      let a : GL2R := g * γ.val * g⁻¹
      have ha : a ∈ Γ := by
        simpa only [a, ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul] using hγ
      have hmul : g * γ.val = a * g := by
        dsimp only [a]
        group
      change F.1 (g * (γ.val * x)) = F.1 (g * x)
      rw [← mul_assoc, hmul, mul_assoc]
      exact F.property ⟨a, ha⟩ (g * x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Rational upper-half-plane pullback is literal left multiplication after lifting to `GL(2, ℝ)`. -/
theorem glLift_rationalMaassPullbackInvariant_general
    (Γ : Subgroup GL2R) (g : GL (Fin 2) ℚ)
    (f : glUpperHalfPlaneInvariantFunctions Γ) :
    glLiftInvariantFunction (rationalPullbackConjugateGroup Γ g)
      (rationalMaassPullbackInvariant_general Γ g f) =
      glAutomorphicLeftTranslation (g.map (algebraMap ℚ ℝ)) Γ
        (glLiftInvariantFunction Γ f) := by
  apply Subtype.ext
  funext x
  change f.1 (g.map (algebraMap ℚ ℝ) • (x • UpperHalfPlane.I)) =
    f.1 ((g.map (algebraMap ℚ ℝ) * x) • UpperHalfPlane.I)
  rw [mul_smul]

/-- Left rational correspondence and right regular translation commute exactly. -/
theorem glAutomorphicLeftTranslation_commutes_right
    (g : GL2R) (Γ : Subgroup GL2R) (k : SL2R)
    (F : glAutomorphicFunctionSpace Γ) :
    glAutomorphicRightTranslation (ConjAct.toConjAct g⁻¹ • Γ) k
      (glAutomorphicLeftTranslation g Γ F) =
      glAutomorphicLeftTranslation g Γ (glAutomorphicRightTranslation Γ k F) := by
  apply Subtype.ext
  funext x
  change F.1 (g * (x * Matrix.SpecialLinearGroup.toGL k)) =
    F.1 ((g * x) * Matrix.SpecialLinearGroup.toGL k)
  rw [mul_assoc]

variable {G H : Subgroup GL2R}

local notation "𝒬" => H ⧸ (G.subgroupOf H)

local instance : MulAction H H := Monoid.toMulAction ..
local instance : MulAction H 𝒬 := .quotient ..

/-- One relative-coset summand in the `GL(2, ℝ)` automorphic carrier. -/
def glAutomorphicTraceQuotientFunc
    (F : glAutomorphicFunctionSpace G) (q : 𝒬) (x : GL2R) : ℂ :=
  q.liftOn (fun h => F.1 (h.val⁻¹ * x)) (fun h h' hhh' => by
    obtain ⟨j, hj, hj'⟩ : ∃ j ∈ G, h' = h * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    rw [hj', _root_.mul_inv_rev, mul_assoc]
    exact (F.property ⟨j⁻¹, inv_mem hj⟩ _).symm)

@[simp]
theorem glAutomorphicTraceQuotientFunc_mk
    (F : glAutomorphicFunctionSpace G) (h : H) (x : GL2R) :
    glAutomorphicTraceQuotientFunc F (QuotientGroup.mk h) x = F.1 (h.val⁻¹ * x) :=
  rfl

/-- Target left multiplication permutes finite trace summands. -/
theorem glAutomorphicTraceQuotientFunc_left_mul
    (F : glAutomorphicFunctionSpace G) (h : H) (q : 𝒬) (x : GL2R) :
    glAutomorphicTraceQuotientFunc F q (h.val * x) =
      glAutomorphicTraceQuotientFunc F (h⁻¹ • q) x := by
  induction q using Quotient.inductionOn with
  | h r => simp [glAutomorphicTraceQuotientFunc, _root_.mul_inv_rev, mul_assoc]

/-- A trace summand is linear in its source. -/
theorem glAutomorphicTraceQuotientFunc_add
    (F K : glAutomorphicFunctionSpace G) (q : 𝒬) (x : GL2R) :
    glAutomorphicTraceQuotientFunc (F + K) q x =
      glAutomorphicTraceQuotientFunc F q x + glAutomorphicTraceQuotientFunc K q x := by
  induction q using Quotient.inductionOn with
  | h r => rfl

/-- A trace summand commutes with complex scalar multiplication. -/
theorem glAutomorphicTraceQuotientFunc_csmul
    (c : ℂ) (F : glAutomorphicFunctionSpace G) (q : 𝒬) (x : GL2R) :
    glAutomorphicTraceQuotientFunc (c • F) q x =
      c • glAutomorphicTraceQuotientFunc F q x := by
  induction q using Quotient.inductionOn with
  | h r => rfl

variable [G.IsFiniteRelIndex H]

/-- Finite relative-coset trace in the `GL(2, ℝ)` automorphic carrier. -/
def glAutomorphicTrace :
    glAutomorphicFunctionSpace G →ₗ[ℂ] glAutomorphicFunctionSpace H where
  toFun F :=
    ⟨fun x => by
      letI := Fintype.ofFinite 𝒬
      exact ∑ q : 𝒬, glAutomorphicTraceQuotientFunc F q x, by
      intro h x
      letI := Fintype.ofFinite 𝒬
      change (∑ q : 𝒬, glAutomorphicTraceQuotientFunc F q (h.val * x)) =
        ∑ q : 𝒬, glAutomorphicTraceQuotientFunc F q x
      calc
        ∑ q : 𝒬, glAutomorphicTraceQuotientFunc F q (h.val * x) =
            ∑ q : 𝒬, glAutomorphicTraceQuotientFunc F (h⁻¹ • q) x := by
          apply Finset.sum_congr rfl
          intro q _
          exact glAutomorphicTraceQuotientFunc_left_mul F h q x
        _ = ∑ q : 𝒬, glAutomorphicTraceQuotientFunc F q x :=
          Equiv.sum_comp (MulAction.toPerm h⁻¹)
            (fun q : 𝒬 => glAutomorphicTraceQuotientFunc F q x)⟩
  map_add' F K := by
    apply Subtype.ext
    funext x
    letI := Fintype.ofFinite 𝒬
    change (∑ q : 𝒬, glAutomorphicTraceQuotientFunc (F + K) q x) =
      (∑ q : 𝒬, glAutomorphicTraceQuotientFunc F q x) +
        ∑ q : 𝒬, glAutomorphicTraceQuotientFunc K q x
    simp_rw [glAutomorphicTraceQuotientFunc_add]
    exact Finset.sum_add_distrib
  map_smul' c F := by
    apply Subtype.ext
    funext x
    letI := Fintype.ofFinite 𝒬
    change (∑ q : 𝒬, glAutomorphicTraceQuotientFunc (c • F) q x) =
      c • ∑ q : 𝒬, glAutomorphicTraceQuotientFunc F q x
    simp_rw [glAutomorphicTraceQuotientFunc_csmul]
    exact Finset.smul_sum.symm

/-- Lifting the existing finite Maass trace equals the finite trace in the automorphic carrier. -/
theorem glLift_maassTraceInvariant
    (f : glUpperHalfPlaneInvariantFunctions G) :
    glLiftInvariantFunction H (maassTraceInvariant (H := H) f) =
      glAutomorphicTrace (glLiftInvariantFunction G f) := by
  apply Subtype.ext
  funext x
  letI := Fintype.ofFinite 𝒬
  change (∑ q : 𝒬, maassTraceQuotientFunc f q (x • UpperHalfPlane.I)) =
    ∑ q : 𝒬, glAutomorphicTraceQuotientFunc (glLiftInvariantFunction G f) q x
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h r =>
    change f.1 (r.val⁻¹ • (x • UpperHalfPlane.I)) =
      f.1 ((r.val⁻¹ * x) • UpperHalfPlane.I)
    rw [mul_smul]

/-- Finite relative-coset trace commutes with every right `SL(2, ℝ)` translation. -/
theorem glAutomorphicTrace_commutes_right
    (k : SL2R) (F : glAutomorphicFunctionSpace G) :
    glAutomorphicRightTranslation H k (glAutomorphicTrace F) =
      glAutomorphicTrace (glAutomorphicRightTranslation G k F) := by
  apply Subtype.ext
  funext x
  letI := Fintype.ofFinite 𝒬
  change (∑ q : 𝒬,
      glAutomorphicTraceQuotientFunc F q (x * Matrix.SpecialLinearGroup.toGL k)) =
    ∑ q : 𝒬,
      glAutomorphicTraceQuotientFunc (glAutomorphicRightTranslation G k F) q x
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h r =>
    change F.1 (r.val⁻¹ * (x * Matrix.SpecialLinearGroup.toGL k)) =
      F.1 ((r.val⁻¹ * x) * Matrix.SpecialLinearGroup.toGL k)
    rw [mul_assoc]

/-- The literal rational pullback followed by the finite trace is a right-regular
intertwiner in the automorphic `GL(2, ℝ)` carrier. -/
theorem rationalPrincipalPullbackTrace_lift_commutes_right
    (N : ℕ) (g : GL (Fin 2) ℚ) (k : SL2R)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    glAutomorphicRightTranslation (principalCongruenceGL N) k
      (glLiftInvariantFunction (principalCongruenceGL N)
        (maassTraceInvariant (H := principalCongruenceGL N)
          (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f))) =
      glAutomorphicTrace
        (glAutomorphicLeftTranslation (g.map (algebraMap ℚ ℝ)) (principalCongruenceGL N)
          (glAutomorphicRightTranslation (principalCongruenceGL N) k
            (glLiftInvariantFunction (principalCongruenceGL N) f))) := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  rw [glLift_maassTraceInvariant]
  rw [glLift_rationalMaassPullbackInvariant_general]
  rw [glAutomorphicTrace_commutes_right]
  rw [glAutomorphicLeftTranslation_commutes_right]



private theorem integralSL2ToReal_toGL_eq_mapGL (x : SL2Z) :
    Matrix.SpecialLinearGroup.toGL (integralSL2ToReal x) =
      Matrix.SpecialLinearGroup.mapGL ℝ x := by
  have hcast : Int.castRingHom ℝ = algebraMap ℤ ℝ := by
    ext n
    rfl
  rw [integralSL2ToReal, hcast]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact congr_fun (congr_fun (Matrix.SpecialLinearGroup.mapGL_coe_matrix (S := ℝ) x).symm i) j

/-- Pulling the principal `GL(2, ℝ)` source subgroup back to `SL(2, ℝ)` recovers
its literal real integral image. -/
theorem principalCongruenceGL_comap_sl2ToGL (N : ℕ) :
    (principalCongruenceGL N).comap Matrix.SpecialLinearGroup.toGL =
      realImage (CongruenceSubgroup.Gamma (N + 1)) := by
  ext g
  simp only [Subgroup.mem_comap, principalCongruenceGL, realImage, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hmap⟩
    refine ⟨x, hx, ?_⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [integralSL2ToReal_toGL_eq_mapGL, hmap]
  · rintro ⟨x, hx, hmap⟩
    refine ⟨x, hx, ?_⟩
    rw [← integralSL2ToReal_toGL_eq_mapGL, hmap]

/-- The standard embedding of `SL(2, ℝ)` into `GL(2, ℝ)`. -/
abbrev sl2ToGL : SL2R →* GL2R := Matrix.SpecialLinearGroup.toGL

private theorem sl2ToGL_eq_mapGL (x : SL2R) :
    sl2ToGL x = Matrix.SpecialLinearGroup.mapGL ℝ x := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- Restrict `GL(2, ℝ)`-invariant upper-half-plane functions to the associated
`SL(2, ℝ)` quotient. -/
def glInvariantRestrictToSL (Γ : Subgroup GL2R) :
    glUpperHalfPlaneInvariantFunctions Γ →ₗ[ℂ]
      upperHalfPlaneInvariantFunctions (Γ.comap sl2ToGL) where
  toFun f :=
    ⟨fun z => f.1 z, by
      intro γ z
      change f.1 ((sl2ToGL γ.val) • z) = f.1 z
      exact f.property ⟨sl2ToGL γ.val, γ.property⟩ z⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict the `GL(2, ℝ)` automorphic carrier to the associated `SL(2, ℝ)`
automorphic carrier. -/
def glAutomorphicRestrictToSL (Γ : Subgroup GL2R) :
    glAutomorphicFunctionSpace Γ →ₗ[ℂ]
      automorphicFunctionSpace (Γ.comap sl2ToGL) where
  toFun F :=
    ⟨fun x => F.1 (sl2ToGL x), by
      intro γ x
      change F.1 (sl2ToGL (γ.val * x)) = F.1 (sl2ToGL x)
      rw [map_mul]
      exact F.property ⟨sl2ToGL γ.val, γ.property⟩ (sl2ToGL x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction from the `GL(2, ℝ)` carrier commutes with every right
`SL(2, ℝ)` translation. -/
theorem glAutomorphicRestrictToSL_commutes_right (Γ : Subgroup GL2R)
    (k : SL2R) (F : glAutomorphicFunctionSpace Γ) :
    automorphicRightTranslation (Γ.comap sl2ToGL) k
      (glAutomorphicRestrictToSL Γ F) =
      glAutomorphicRestrictToSL Γ (glAutomorphicRightTranslation Γ k F) := by
  apply Subtype.ext
  funext x
  change F.1 (sl2ToGL (x * k)) = F.1 (sl2ToGL x * sl2ToGL k)
  rw [map_mul]

/-- Restricting a lifted `GL(2, ℝ)` source gives its usual spherical
`SL(2, ℝ)` automorphic vector. -/
theorem glAutomorphicRestrictToSL_lift (Γ : Subgroup GL2R)
    (f : glUpperHalfPlaneInvariantFunctions Γ) :
    glAutomorphicRestrictToSL Γ (glLiftInvariantFunction Γ f) =
      (maassToSphericalAutomorphicCorrespondence (Γ.comap sl2ToGL)
        (glInvariantRestrictToSL Γ f)).1.1 := by
  funext x
  change f.1 ((sl2ToGL x) • UpperHalfPlane.I) = f.1 (x • UpperHalfPlane.I)
  rw [MulAction.compHom_smul_def, sl2ToGL_eq_mapGL]



private theorem sl2ToGL_mem_principal_of_realImage (N : ℕ)
    (γ : realImage (CongruenceSubgroup.Gamma (N + 1))) :
    sl2ToGL γ.val ∈ principalCongruenceGL N := by
  rcases γ.property with ⟨a, ha, hγ⟩
  change ∃ b ∈ CongruenceSubgroup.Gamma (N + 1),
    Matrix.SpecialLinearGroup.mapGL ℝ b = sl2ToGL γ.val
  refine ⟨a, ha, ?_⟩
  rw [← hγ, integralSL2ToReal_toGL_eq_mapGL]

/-- Restrict principal `GL(2, ℝ)` invariant source data directly to the identical
real principal `SL(2, ℝ)` quotient. -/
def principalGLInvariantRestrictToSL (N : ℕ) :
    glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N) →ₗ[ℂ]
      upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma (N + 1))) where
  toFun f :=
    ⟨fun z => f.1 z, by
      intro γ z
      have hγ : sl2ToGL γ.val ∈ principalCongruenceGL N :=
        sl2ToGL_mem_principal_of_realImage N γ
      change f.1 ((sl2ToGL γ.val) • z) = f.1 z
      exact f.property ⟨sl2ToGL γ.val, hγ⟩ z⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The principal `GL(2, ℝ)` automorphic source, restricted directly to the
identical real principal `SL(2, ℝ)` quotient. -/
def principalGLAutomorphicRestrictToSL (N : ℕ) :
    glAutomorphicFunctionSpace (principalCongruenceGL N) →ₗ[ℂ]
      automorphicFunctionSpace (realImage (CongruenceSubgroup.Gamma (N + 1))) where
  toFun F :=
    ⟨fun x => F.1 (sl2ToGL x), by
      intro γ x
      have hγ : sl2ToGL γ.val ∈ principalCongruenceGL N :=
        sl2ToGL_mem_principal_of_realImage N γ
      change F.1 (sl2ToGL (γ.val * x)) = F.1 (sl2ToGL x)
      rw [map_mul]
      exact F.property ⟨sl2ToGL γ.val, hγ⟩ (sl2ToGL x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Principal restriction commutes with every right `SL(2, ℝ)` translation. -/
theorem principalGLAutomorphicRestrictToSL_commutes_right (N : ℕ)
    (k : SL2R) (F : glAutomorphicFunctionSpace (principalCongruenceGL N)) :
    automorphicRightTranslation (realImage (CongruenceSubgroup.Gamma (N + 1))) k
      (principalGLAutomorphicRestrictToSL N F) =
      principalGLAutomorphicRestrictToSL N
        (glAutomorphicRightTranslation (principalCongruenceGL N) k F) := by
  apply Subtype.ext
  funext x
  change F.1 (sl2ToGL (x * k)) = F.1 (sl2ToGL x * sl2ToGL k)
  rw [map_mul]

/-- Principal restriction sends a lifted `GL(2, ℝ)` source to its usual spherical
`SL(2, ℝ)` automorphic vector. -/
theorem principalGLAutomorphicRestrictToSL_lift (N : ℕ)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    principalGLAutomorphicRestrictToSL N
      (glLiftInvariantFunction (principalCongruenceGL N) f) =
      (maassToSphericalAutomorphicCorrespondence
        (realImage (CongruenceSubgroup.Gamma (N + 1)))
        (principalGLInvariantRestrictToSL N f)).1.1 := by
  funext x
  change f.1 ((sl2ToGL x) • UpperHalfPlane.I) = f.1 (x • UpperHalfPlane.I)
  rw [MulAction.compHom_smul_def, sl2ToGL_eq_mapGL]



/-- After restriction to the actual principal `SL(2, ℝ)` quotient, the literal
rational pullback followed by finite trace still intertwines every right translation. -/
theorem rationalPrincipalTrace_restrictToSL_commutes_right
    (N : ℕ) (g : GL (Fin 2) ℚ) (k : SL2R)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    automorphicRightTranslation (realImage (CongruenceSubgroup.Gamma (N + 1))) k
      (principalGLAutomorphicRestrictToSL N
        (glLiftInvariantFunction (principalCongruenceGL N)
          (maassTraceInvariant (H := principalCongruenceGL N)
            (rationalMaassPullbackInvariant_general (principalCongruenceGL N) g f)))) =
      principalGLAutomorphicRestrictToSL N
        (glAutomorphicTrace
          (glAutomorphicLeftTranslation (g.map (algebraMap ℚ ℝ)) (principalCongruenceGL N)
            (glAutomorphicRightTranslation (principalCongruenceGL N) k
              (glLiftInvariantFunction (principalCongruenceGL N) f))) ) := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  rw [principalGLAutomorphicRestrictToSL_commutes_right]
  rw [rationalPrincipalPullbackTrace_lift_commutes_right]
end

end GaloisForLFunctions.RHTower
