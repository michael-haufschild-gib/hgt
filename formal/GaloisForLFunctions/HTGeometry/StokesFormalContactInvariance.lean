import GaloisForLFunctions.HTGeometry.StokesLaurentFourierSource

/-!
# Universal formal-contact invariance law

A tangent coordinate change `t ↦ t u(t)`, `u(0)=1`, preserves order of every formal power
series and every Laurent series.  Consequently it preserves the contact order
`ord(f-g)` of every pair.  The proof is exact on the localized Laurent field: it handles positive
and negative monomials, transports the power-series factor, and uses the constructed inverse
substitution.  No continuity or valuation-preservation axiom is assumed.

This is the universal law behind the local-Fourier, Stokes-contact, tomography, and coarea
constructions: all those invariants depend only on pairwise Laurent contact orders and therefore
survive the exact uniformizer created by the negative Airy Fourier branch.
-/

open scoped PowerSeries

namespace GaloisForLFunctions.IrregularStokes.FormalUniformizer

noncomputable section

theorem tangentReparametrization_order
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f : PowerSeries ℂ) :
    PowerSeries.order (tangentReparametrization E u hu f) =
      PowerSeries.order f := by
  apply le_antisymm
  · have hle := PowerSeries.le_order_subst_left'
      (inverseTangentSeries_constantCoeff E u hu)
      (φ := tangentReparametrization E u hu f)
    have hinv : inverseTangentSubstitution E u hu
        (tangentReparametrization E u hu f) = f := by
      change (inverseTangentSubstitution E u hu).comp
        (tangentSubstitution E u hu) f = f
      rw [inverseTangentSubstitution_tangentSubstitution]
      rfl
    rw [← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero'
        (inverseTangentSeries_constantCoeff E u hu))] at hle
    change PowerSeries.order (tangentReparametrization E u hu f) ≤
      PowerSeries.order
        (inverseTangentSubstitution E u hu
          (tangentReparametrization E u hu f)) at hle
    rwa [hinv] at hle
  · have hle := PowerSeries.le_order_subst_left'
      (tangentUniformizer_constantCoeff E u hu) (φ := f)
    rw [← PowerSeries.coe_substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero'
        (tangentUniformizer_constantCoeff E u hu))] at hle
    change PowerSeries.order f ≤
      PowerSeries.order (tangentSubstitution E u hu f) at hle
    exact hle

theorem laurent_order_zpow (f : LaurentSeries ℂ) (hf : f ≠ 0) (n : ℤ) :
    (f ^ n).order = n • f.order := by
  cases n with
  | ofNat n =>
      change (f ^ n).order = (n : ℤ) • f.order
      rw [HahnSeries.order_pow]
      rfl
  | negSucc n =>
      change ((f ^ n.succ)⁻¹).order = (-(n.succ : ℤ)) • f.order
      rw [LaurentFourier.order_inv_of_ne_zero (f ^ n.succ)
        (pow_ne_zero n.succ hf), HahnSeries.order_pow]
      simp
      ring

theorem tangentUniformizer_laurent_order
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) :
    ((tangentUniformizer E u hu : PowerSeries ℂ) : LaurentSeries ℂ).order = 1 := by
  have hroot : (unitNthRoot E u hu : LaurentSeries ℂ) ≠ 0 :=
    LaurentFourier.powerSeries_coe_ne_zero <| by
      intro h
      have hc := unitNthRoot_constantCoeff E u hu
      rw [h] at hc
      simp at hc
  change ((PowerSeries.X * unitNthRoot E u hu : PowerSeries ℂ) :
    LaurentSeries ℂ).order = 1
  rw [map_mul, HahnSeries.ofPowerSeries_X,
    HahnSeries.order_mul (HahnSeries.single_ne_zero one_ne_zero) hroot,
    HahnSeries.order_single one_ne_zero,
    LaurentFourier.powerSeries_coe_order_zero]
  · simp
  · rw [unitNthRoot_constantCoeff]
    exact one_ne_zero

theorem laurentAlgReparametrization_monomial_order
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1) (n : ℤ) :
    (laurentAlgReparametrization E u hu
      (LaurentFourier.laurentMonomial n)).order = n := by
  rw [LaurentFourier.laurentMonomial, RatFunc.single_zpow]
  rw [map_zpow₀ (laurentAlgReparametrization E u hu)
    ((HahnSeries.single (1 : ℤ) 1) : LaurentSeries ℂ) n]
  have hX : laurentAlgReparametrization E u hu
      ((HahnSeries.single (1 : ℤ) 1) : LaurentSeries ℂ) =
      (tangentUniformizer E u hu : LaurentSeries ℂ) := by
    rw [← HahnSeries.ofPowerSeries_X]
    rw [laurentAlgReparametrization_coe, tangentReparametrization_X]
  rw [hX, laurent_order_zpow]
  · rw [tangentUniformizer_laurent_order]
    simp
  · intro h
    have hord := tangentUniformizer_laurent_order E u hu
    rw [h, HahnSeries.order_zero] at hord
    omega

theorem powerSeriesPart_constantCoeff_ne_zero
    {f : LaurentSeries ℂ} (hf : f ≠ 0) :
    f.powerSeriesPart.constantCoeff ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    LaurentSeries.powerSeriesPart_coeff]
  simp only [Nat.cast_zero, add_zero]
  rw [← HahnSeries.leadingCoeff_eq]
  exact HahnSeries.leadingCoeff_ne_zero.mpr hf

theorem tangentReparametrization_constantCoeff_ne_zero
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f : PowerSeries ℂ) (hf : f.constantCoeff ≠ 0) :
    (tangentReparametrization E u hu f).constantCoeff ≠ 0 := by
  have hforder : PowerSeries.order f = 0 := by
    by_contra h
    exact hf (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h)
  intro hzero
  have horderNe : PowerSeries.order (tangentReparametrization E u hu f) ≠ 0 :=
    PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr hzero
  rw [tangentReparametrization_order, hforder] at horderNe
  exact horderNe rfl

/-- Universal valuation law: every Laurent valuation is invariant under a tangent formal
reparametrization. -/
theorem laurentAlgReparametrization_order
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f : LaurentSeries ℂ) :
    (laurentAlgReparametrization E u hu f).order = f.order := by
  by_cases hf : f = 0
  · simp [hf]
  let p := f.powerSeriesPart
  have hp0 : p.constantCoeff ≠ 0 := powerSeriesPart_constantCoeff_ne_zero hf
  have hdecomp : LaurentFourier.laurentMonomial f.order *
      (p : LaurentSeries ℂ) = f := by
    exact f.single_order_mul_powerSeriesPart
  have hmono : laurentAlgReparametrization E u hu
      (LaurentFourier.laurentMonomial f.order) ≠ 0 := by
    intro hzero
    apply LaurentFourier.laurentMonomial_ne_zero f.order
    apply (laurentAlgReparametrization E u hu).injective
    rw [hzero, map_zero]
  have hp : laurentAlgReparametrization E u hu
      (p : LaurentSeries ℂ) ≠ 0 := by
    have hpSource : (p : LaurentSeries ℂ) ≠ 0 :=
      LaurentFourier.powerSeries_coe_ne_zero <| by
      intro h
      rw [h] at hp0
      simp at hp0
    simpa using (laurentAlgReparametrization E u hu).injective.ne hpSource
  have hmap : laurentAlgReparametrization E u hu f =
      laurentAlgReparametrization E u hu
          (LaurentFourier.laurentMonomial f.order) *
        laurentAlgReparametrization E u hu (p : LaurentSeries ℂ) := by
    calc
      laurentAlgReparametrization E u hu f =
          laurentAlgReparametrization E u hu
            (LaurentFourier.laurentMonomial f.order *
              (p : LaurentSeries ℂ)) :=
        congrArg (laurentAlgReparametrization E u hu) hdecomp.symm
      _ = _ := map_mul _ _ _
  rw [hmap, HahnSeries.order_mul hmono hp,
    laurentAlgReparametrization_monomial_order,
    laurentAlgReparametrization_coe,
    LaurentFourier.powerSeries_coe_order_zero]
  · simp
  · exact tangentReparametrization_constantCoeff_ne_zero E u hu p hp0

/-- Contact orders are invariant under simultaneous tangent reparametrization. -/
theorem laurentAlgReparametrization_contact
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f g : LaurentSeries ℂ) :
    (laurentAlgReparametrization E u hu f -
      laurentAlgReparametrization E u hu g).order = (f - g).order := by
  rw [← map_sub]
  exact laurentAlgReparametrization_order E u hu (f - g)

theorem laurentAlgReparametrization_orderTop
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f : LaurentSeries ℂ) :
    (laurentAlgReparametrization E u hu f).orderTop = f.orderTop := by
  by_cases hf : f = 0
  · simp [hf]
  have hmap : laurentAlgReparametrization E u hu f ≠ 0 := by
    intro hzero
    apply hf
    apply (laurentAlgReparametrization E u hu).injective
    rw [hzero, map_zero]
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hmap,
    ← HahnSeries.order_eq_orderTop_of_ne_zero hf,
    laurentAlgReparametrization_order]

theorem laurentAlgReparametrization_contactTop
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f g : LaurentSeries ℂ) :
    (laurentAlgReparametrization E u hu f -
      laurentAlgReparametrization E u hu g).orderTop = (f - g).orderTop := by
  rw [← map_sub]
  exact laurentAlgReparametrization_orderTop E u hu (f - g)

theorem laurentAlgReparametrization_symm_order
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f : LaurentSeries ℂ) :
    ((laurentAlgReparametrization E u hu).symm f).order = f.order := by
  have h := laurentAlgReparametrization_order E u hu
    ((laurentAlgReparametrization E u hu).symm f)
  simpa using h.symm

theorem laurentAlgReparametrization_symm_contactTop
    (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (f g : LaurentSeries ℂ) :
    ((laurentAlgReparametrization E u hu).symm f -
      (laurentAlgReparametrization E u hu).symm g).orderTop =
        (f - g).orderTop := by
  rw [← map_sub]
  have h := laurentAlgReparametrization_orderTop E u hu
    ((laurentAlgReparametrization E u hu).symm (f - g))
  simpa using h.symm

/-- Pairwise Laurent contact matrix of a finite or infinite family of irregular values. -/
def laurentContactMatrix {ι : Type*} (q : ι → LaurentSeries ℂ)
    (i j : ι) : WithTop ℤ :=
  (q i - q j).orderTop

theorem laurentContactMatrix_reparametrization
    {ι : Type*} (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (q : ι → LaurentSeries ℂ) (i j : ι) :
    laurentContactMatrix (fun k => laurentAlgReparametrization E u hu (q k)) i j =
      laurentContactMatrix q i j := by
  exact laurentAlgReparametrization_contactTop E u hu (q i) (q j)

/-- Contact cluster at a valuation threshold. -/
def laurentContactCluster {ι : Type*} (q : ι → LaurentSeries ℂ)
    (a : WithTop ℤ) (i : ι) : Set ι :=
  {j | a ≤ laurentContactMatrix q i j}

/-- Hierarchy formed by all contact-threshold clusters. -/
def laurentContactHierarchy {ι : Type*} (q : ι → LaurentSeries ℂ) : Set (Set ι) :=
  {A | ∃ a i, A = laurentContactCluster q a i}

theorem laurentContactCluster_reparametrization
    {ι : Type*} (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (q : ι → LaurentSeries ℂ) (a : WithTop ℤ) (i : ι) :
    laurentContactCluster (fun k => laurentAlgReparametrization E u hu (q k)) a i =
      laurentContactCluster q a i := by
  ext j
  simp only [laurentContactCluster, Set.mem_setOf_eq,
    laurentContactMatrix_reparametrization]

/-- Full threshold tomography is invariant under tangent formal coordinates. -/
theorem laurentContactHierarchy_reparametrization
    {ι : Type*} (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (q : ι → LaurentSeries ℂ) :
    laurentContactHierarchy
        (fun k => laurentAlgReparametrization E u hu (q k)) =
      laurentContactHierarchy q := by
  ext A
  simp only [laurentContactHierarchy, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, i, rfl⟩
    exact ⟨a, i, laurentContactCluster_reparametrization E u hu q a i⟩
  · rintro ⟨a, i, rfl⟩
    exact ⟨a, i, (laurentContactCluster_reparametrization E u hu q a i).symm⟩

/-- Re-expression in the inverse tangent coordinate preserves full threshold tomography. -/
theorem laurentContactHierarchy_symm_reparametrization
    {ι : Type*} (E : ℕ) (u : PowerSeries ℂ) (hu : u.constantCoeff = 1)
    (q : ι → LaurentSeries ℂ) :
    laurentContactHierarchy
        (fun k => (laurentAlgReparametrization E u hu).symm (q k)) =
      laurentContactHierarchy q := by
  have h := laurentContactHierarchy_reparametrization E u hu
    (fun k => (laurentAlgReparametrization E u hu).symm (q k))
  simpa using h.symm


end
end GaloisForLFunctions.IrregularStokes.FormalUniformizer
