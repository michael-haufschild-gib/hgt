import GaloisForLFunctions.HTGeometry.DeckClosureStableCore
import GaloisForLFunctions.HTGeometry.NonautonomousDeckClosure
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality
import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction

/-!
# Differential horizon interfaces

This module isolates the exact field-theoretic deductions used by the
constant-isogeny, Manin-horizon, embedded-reconstruction, and
nonautonomous-isogeny theorems.  Algebraic-group geometry supplies
finite-level deck quotients, closure invariance, and quotient
coordinates.  No such parent theorem is postulated globally: each is
an explicit hypothesis of the corresponding unconditional result.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A differential automorphism fixing a labelled family pointwise
fixes its entire generated differential field pointwise. -/
theorem DifferentialAlgEquiv.fixed_on_differentialAdjoin
    {C L ι : Type*} [Field C] [Field L] [Algebra C L]
    [Differential L]
    (σ : DifferentialAlgEquiv C L) (x : ι → L)
    (hfix : ∀ i, σ.toAlgEquiv (x i) = x i)
    {z : L} (hz : z ∈ differentialAdjoin C (Set.range x)) :
    σ.toAlgEquiv z = z := by
  let p : ∀ y : L,
      y ∈ differentialAdjoin C (Set.range x) → Prop :=
    fun y _ => σ.toAlgEquiv y = y
  change p z hz
  refine IntermediateField.adjoin_induction C
    (p := p) ?_ ?_ ?_ ?_ ?_ hz
  · rintro y ⟨y₀, ⟨i, rfl⟩, n, rfl⟩
    show σ.toAlgEquiv (differentialJet n (x i)) =
      differentialJet n (x i)
    rw [σ.map_differentialJet, hfix]
  · intro c
    exact σ.toAlgEquiv.commutes c
  · intro y w hy hw hpy hpw
    change σ.toAlgEquiv (y + w) = y + w
    simpa only [map_add] using congrArg₂ (· + ·) hpy hpw
  · intro y hy hpy
    change σ.toAlgEquiv y⁻¹ = y⁻¹
    simpa only [map_inv₀] using congrArg Inv.inv hpy
  · intro y w hy hw hpy hpw
    change σ.toAlgEquiv (y * w) = y * w
    simpa only [map_mul] using congrArg₂ (· * ·) hpy hpw

/-- Translation stabilizer of an embedded differential field. -/
def differentialTranslationStabilizer
    {C L A : Type*} [Field C] [Field L] [Algebra C L]
    [Differential L]
    (translation : A → DifferentialAlgEquiv C L)
    (E : IntermediateField C L) : Set A :=
  {h | ∀ z : L, z ∈ E → (translation h).toAlgEquiv z = z}

/-- **Exact embedded-horizon stabilizer.**  If translated quotient
coordinates change by the Manin-coordinate value of the translating
point, the stabilizer of their generated differential field is
exactly the common kernel of those point coordinates. -/
theorem differentialTranslationStabilizer_differentialAdjoin_eq_kernel
    {C L A ι : Type*} [Field C] [Field L] [Algebra C L]
    [Differential L]
    (translation : A → DifferentialAlgEquiv C L)
    (μ : ι → L) (μpoint : A → ι → L)
    (htranslate : ∀ h i,
      (translation h).toAlgEquiv (μ i) =
        μ i + μpoint h i) :
    differentialTranslationStabilizer translation
        (differentialAdjoin C (Set.range μ)) =
      {h | ∀ i, μpoint h i = 0} := by
  ext h
  constructor
  · intro hstab i
    have hμmem :
        μ i ∈ differentialAdjoin C (Set.range μ) :=
      subset_differentialAdjoin C (Set.range μ)
        (Set.mem_range_self i)
    have hfixed := hstab (μ i) hμmem
    rw [htranslate] at hfixed
    exact add_left_cancel (hfixed.trans (add_zero (μ i)).symm)
  · intro hker z hz
    apply (translation h).fixed_on_differentialAdjoin μ
    · intro i
      rw [htranslate, hker i, add_zero]
    · exact hz

/-- **Manin/deck horizon identity.**  Finite deck quotients give the
stable core; closure invariance replaces their generated subgroup by
the Manin kernel; differential quotient coordinates generate its
fixed field. -/
theorem stableRangeCore_eq_closedDeck_eq_differentialQuotient
    {C L ι : Type*} [Field C] [Field L] [Algebra C L]
    [Differential C] [Differential L]
    [DifferentialAlgebra C L]
    (φ : L →ₐ[C] L)
    (deck : ℕ → Subgroup (L ≃ₐ[C] L))
    (hdeck : ∀ n,
      IntermediateField.map (φ ^ n) ⊤ =
        IntermediateField.fixedField (deck n))
    (closedDeck : Subgroup (L ≃ₐ[C] L))
    (hclosure :
      IntermediateField.fixedField (⨆ n, deck n) =
        IntermediateField.fixedField closedDeck)
    (quotientCoordinate : ι → L)
    (hquotient :
      IntermediateField.fixedField closedDeck =
        differentialAdjoin C
          (Set.range quotientCoordinate)) :
    stableRangeCore φ =
        IntermediateField.fixedField closedDeck ∧
      stableRangeCore φ =
        differentialAdjoin C
          (Set.range quotientCoordinate) := by
  have htail :=
    stableRangeCore_eq_fixedField_iSup φ deck hdeck
  exact ⟨htail.trans hclosure,
    htail.trans (hclosure.trans hquotient)⟩

/-- Pointwise Manin-horizon form. -/
theorem mem_stableRangeCore_iff_mem_differentialQuotient
    {C L ι : Type*} [Field C] [Field L] [Algebra C L]
    [Differential C] [Differential L]
    [DifferentialAlgebra C L]
    (φ : L →ₐ[C] L)
    (deck : ℕ → Subgroup (L ≃ₐ[C] L))
    (hdeck : ∀ n,
      IntermediateField.map (φ ^ n) ⊤ =
        IntermediateField.fixedField (deck n))
    (closedDeck : Subgroup (L ≃ₐ[C] L))
    (hclosure :
      IntermediateField.fixedField (⨆ n, deck n) =
        IntermediateField.fixedField closedDeck)
    (quotientCoordinate : ι → L)
    (hquotient :
      IntermediateField.fixedField closedDeck =
        differentialAdjoin C
          (Set.range quotientCoordinate))
    (z : L) :
    z ∈ stableRangeCore φ ↔
      z ∈ differentialAdjoin C
        (Set.range quotientCoordinate) := by
  rw [(stableRangeCore_eq_closedDeck_eq_differentialQuotient
    φ deck hdeck closedDeck hclosure quotientCoordinate
      hquotient).2]

/-- Canonical abstract equivalence between two Manin horizons of the
same rank.  It maps every labelled quotient coordinate, and every
differential jet of it, to its counterpart. -/
def differentialQuotientFreeAlgEquiv
    {C L₁ L₂ ι : Type*}
    [Field C] [Field L₁] [Field L₂]
    [Algebra C L₁] [Algebra C L₂]
    [Differential L₁] [Differential L₂]
    (x : ι → L₁) (y : ι → L₂)
    (hx : DifferentialIndependent C x)
    (hy : DifferentialIndependent C y) :
    differentialAdjoin C (Set.range x) ≃ₐ[C]
      differentialAdjoin C (Set.range y) :=
  GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv
    x y hx hy

@[simp]
theorem differentialQuotientFreeAlgEquiv_jet
    {C L₁ L₂ ι : Type*}
    [Field C] [Field L₁] [Field L₂]
    [Algebra C L₁] [Algebra C L₂]
    [Differential L₁] [Differential L₂]
    (x : ι → L₁) (y : ι → L₂)
    (hx : DifferentialIndependent C x)
    (hy : DifferentialIndependent C y)
    (i : ι) (n : ℕ) :
    differentialQuotientFreeAlgEquiv x y hx hy
      ⟨differentialJet n (x i),
        differentialJet_mem_differentialAdjoin C
          (Set.mem_range_self i) n⟩ =
      ⟨differentialJet n (y i),
        differentialJet_mem_differentialAdjoin C
          (Set.mem_range_self i) n⟩ :=
  GaloisForLFunctions.differentialIndependentAdjoinAlgEquiv_jet
    x y hx hy i n

/-- **Universal no-hair form.**  Any two horizon quotients freely
generated by equally labelled rank families are canonically
isomorphic as embedded abstract differential-generator fields. -/
theorem exists_differentialQuotientFreeAlgEquiv
    {C L₁ L₂ ι : Type*}
    [Field C] [Field L₁] [Field L₂]
    [Algebra C L₁] [Algebra C L₂]
    [Differential L₁] [Differential L₂]
    (x : ι → L₁) (y : ι → L₂)
    (hx : DifferentialIndependent C x)
    (hy : DifferentialIndependent C y) :
    ∃ e :
        differentialAdjoin C (Set.range x) ≃ₐ[C]
          differentialAdjoin C (Set.range y),
      ∀ i n,
        e ⟨differentialJet n (x i),
            differentialJet_mem_differentialAdjoin C
              (Set.mem_range_self i) n⟩ =
          ⟨differentialJet n (y i),
            differentialJet_mem_differentialAdjoin C
              (Set.mem_range_self i) n⟩ :=
  ⟨differentialQuotientFreeAlgEquiv x y hx hy,
    differentialQuotientFreeAlgEquiv_jet x y hx hy⟩

/-- **Position--velocity isogeny-tail decomposition.**  Once the
closed deck invariant field is generated by quotient positions and
Maurer--Cartan velocities, the stable tail is exactly their joint
differential field. -/
theorem stableRangeCore_eq_positionVelocity
    {C L I J : Type*} [Field C] [Field L] [Algebra C L]
    [Differential C] [Differential L]
    [DifferentialAlgebra C L]
    (φ : L →ₐ[C] L)
    (deck : ℕ → Subgroup (L ≃ₐ[C] L))
    (hdeck : ∀ n,
      IntermediateField.map (φ ^ n) ⊤ =
        IntermediateField.fixedField (deck n))
    (closedDeck : Subgroup (L ≃ₐ[C] L))
    (hclosure :
      IntermediateField.fixedField (⨆ n, deck n) =
        IntermediateField.fixedField closedDeck)
    (position : I → L) (velocity : J → L)
    (hquotient :
      IntermediateField.fixedField closedDeck =
        differentialAdjoin C
          (Set.range (Sum.elim position velocity))) :
    stableRangeCore φ =
      differentialAdjoin C
        (Set.range (Sum.elim position velocity)) :=
  (stableRangeCore_eq_closedDeck_eq_differentialQuotient
    φ deck hdeck closedDeck hclosure
      (Sum.elim position velocity) hquotient).2

/-- Pure expansion: when no reversible position coordinate remains,
the entire stable tail is generated by Maurer--Cartan velocity. -/
theorem stableRangeCore_eq_velocity_of_noPosition
    {C L J : Type*} [Field C] [Field L] [Algebra C L]
    [Differential C] [Differential L]
    [DifferentialAlgebra C L]
    (φ : L →ₐ[C] L)
    (deck : ℕ → Subgroup (L ≃ₐ[C] L))
    (hdeck : ∀ n,
      IntermediateField.map (φ ^ n) ⊤ =
        IntermediateField.fixedField (deck n))
    (closedDeck : Subgroup (L ≃ₐ[C] L))
    (hclosure :
      IntermediateField.fixedField (⨆ n, deck n) =
        IntermediateField.fixedField closedDeck)
    (velocity : J → L)
    (hquotient :
      IntermediateField.fixedField closedDeck =
        differentialAdjoin C (Set.range velocity)) :
    stableRangeCore φ =
      differentialAdjoin C (Set.range velocity) :=
  (stableRangeCore_eq_closedDeck_eq_differentialQuotient
    φ deck hdeck closedDeck hclosure velocity hquotient).2

/-- Finite holonomy acts after the total deck closure by intersecting
its fixed field with the position--velocity horizon. -/
theorem stableRangeCore_inf_holonomy_eq_closedDeck_sup
    {C L : Type*} [Field C] [Field L] [Algebra C L]
    (φ : L →ₐ[C] L)
    (deck : ℕ → Subgroup (L ≃ₐ[C] L))
    (hdeck : ∀ n,
      IntermediateField.map (φ ^ n) ⊤ =
        IntermediateField.fixedField (deck n))
    (closedDeck holonomy : Subgroup (L ≃ₐ[C] L))
    (hclosure :
      IntermediateField.fixedField (⨆ n, deck n) =
        IntermediateField.fixedField closedDeck) :
    stableRangeCore φ ⊓
        IntermediateField.fixedField holonomy =
      IntermediateField.fixedField
        (closedDeck ⊔ holonomy) := by
  rw [stableRangeCore_eq_fixedField_iSup φ deck hdeck,
    hclosure, fixedField_sup]

/-- **Nonautonomous closed-deck horizon.**  At every phase the
prefix tail is the closed-deck fixed field and, equivalently, the
differential field generated by its position--velocity coordinates. -/
theorem nonautonomousTail_eq_closedDeck_eq_positionVelocity
    {C L I : Type*} [Field C] [Field L] [Algebra C L]
    [Differential C] [Differential L]
    [DifferentialAlgebra C L]
    (φ : ℕ → L →ₐ[C] L) (phase : ℕ)
    (deck : ℕ → Subgroup (L ≃ₐ[C] L))
    (hdeck : ∀ n,
      IntermediateField.map (forwardPrefix φ phase n) ⊤ =
        IntermediateField.fixedField (deck n))
    (closedDeck : Subgroup (L ≃ₐ[C] L))
    (hclosure :
      IntermediateField.fixedField (⨆ n, deck n) =
        IntermediateField.fixedField closedDeck)
    (positionVelocity : I → L)
    (hquotient :
      IntermediateField.fixedField closedDeck =
        differentialAdjoin C
          (Set.range positionVelocity)) :
    nonautonomousTail φ phase =
        IntermediateField.fixedField closedDeck ∧
      nonautonomousTail φ phase =
        differentialAdjoin C
          (Set.range positionVelocity) := by
  have htail :=
    nonautonomousTail_eq_fixedField_iSup
      φ phase deck hdeck
  exact ⟨htail.trans hclosure,
    htail.trans (hclosure.trans hquotient)⟩

/-- Exact reconstruction substitution: once embedded stabilizers are
identified with Manin kernels, any kernel nonorthogonality/isogeny
rigidity theorem becomes the horizon reconstruction theorem. -/
theorem embeddedHorizon_nonorthogonal_iff_isogenous
    {A B : Type*}
    (horizonA sharpA : Set A)
    (horizonB sharpB : Set B)
    (hA : horizonA = sharpA)
    (hB : horizonB = sharpB)
    (Nonorthogonal : Set A → Set B → Prop)
    (Isogenous : Prop)
    (hrigidity :
      Nonorthogonal sharpA sharpB ↔ Isogenous) :
    Nonorthogonal horizonA horizonB ↔ Isogenous := by
  rw [hA, hB]
  exact hrigidity

/-- Homomorphism from one phase quotient to the next. -/
def nonautonomousQuotientAddHom
    {G₀ G₁ : Type*} [AddCommGroup G₀] [AddCommGroup G₁]
    (H₀ : AddSubgroup G₀) (H₁ : AddSubgroup G₁)
    (a : G₀ →+ G₁) (hpre : H₀ ≤ H₁.comap a) :
    G₀ ⧸ H₀ →+ G₁ ⧸ H₁ :=
  QuotientAddGroup.map H₀ H₁ a hpre

/-- **Canonical quotient transport.**  A surjective phase map whose
inverse image of the next erased subgroup is exactly the current
erased subgroup induces an additive equivalence of reversible
quotients. -/
noncomputable def nonautonomousQuotientAddEquiv
    {G₀ G₁ : Type*} [AddCommGroup G₀] [AddCommGroup G₁]
    (H₀ : AddSubgroup G₀) (H₁ : AddSubgroup G₁)
    (a : G₀ →+ G₁) (ha : Function.Surjective a)
    (hpre : H₁.comap a = H₀) :
    G₀ ⧸ H₀ ≃+ G₁ ⧸ H₁ := by
  let f : G₀ →+ G₁ ⧸ H₁ :=
    (QuotientAddGroup.mk' H₁).comp a
  have hf : Function.Surjective f :=
    (QuotientAddGroup.mk'_surjective H₁).comp ha
  have hker : f.ker = H₀ := by
    rw [show f.ker = H₁.comap a by
      ext x
      simp [f]]
    exact hpre
  exact
    (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hf)

@[simp]
theorem nonautonomousQuotientAddEquiv_mk
    {G₀ G₁ : Type*} [AddCommGroup G₀] [AddCommGroup G₁]
    (H₀ : AddSubgroup G₀) (H₁ : AddSubgroup G₁)
    (a : G₀ →+ G₁) (ha : Function.Surjective a)
    (hpre : H₁.comap a = H₀) (x : G₀) :
    nonautonomousQuotientAddEquiv
        H₀ H₁ a ha hpre (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (a x) := by
  rfl

/-- **Flat velocity transport.**  Functoriality through an
invertible phase differential identifies both velocity values and
the dimensions of consecutive Lie sectors. -/
theorem nonautonomousVelocity_flatTransport
    {C V₀ V₁ P₀ P₁ : Type*}
    [Field C] [AddCommGroup V₀] [AddCommGroup V₁]
    [Module C V₀] [Module C V₁]
    [FiniteDimensional C V₀] [FiniteDimensional C V₁]
    (da : V₀ ≃ₗ[C] V₁)
    (a : P₀ → P₁) (ell₀ : P₀ → V₀)
    (ell₁ : P₁ → V₁)
    (hfunctorial : ∀ x, ell₁ (a x) = da (ell₀ x)) :
    (∀ x, ell₁ (a x) = da (ell₀ x)) ∧
      Module.finrank C V₀ = Module.finrank C V₁ := by
  exact ⟨hfunctorial, da.finrank_eq⟩

end

end GaloisForLFunctions.HTGeometry
