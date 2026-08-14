import GaloisForLFunctions.HTGeometry.ComplexTorusVelocityTail

/-!
# The deck group of an isogeny of a complex torus

Pulling back along the isogeny `z ↦ m z` of `V / Λ` is an automorphism of the entire fraction field
of `V`, and an element is such a pullback of a `Λ`-periodic function exactly when it is invariant
under every translation `t` with `m t ∈ Λ`: the deck group of the isogeny is its group of division
points.

Along a sequence of accumulated degrees of unbounded norm those division points are dense, so an
element that is a pullback at every depth is a constant.  This is the deck closure of a compact
complex torus in every dimension.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The pullback of an entire function along the isogeny `z ↦ m z`. -/
noncomputable def entireScale (m : ℂ) (a : entireSubring V) : entireSubring V :=
  ⟨fun z => (a : V → ℂ) (m • z), by
    have hs : AnalyticOnNhd ℂ (fun z : V => m • z) Set.univ :=
      analyticOnNhd_const.smul analyticOnNhd_id
    exact (analyticOnNhd_of_mem_entireSubring a.2).comp hs (Set.mapsTo_univ _ _)⟩

@[simp] theorem entireScale_coe (m : ℂ) (a : entireSubring V) :
    ((entireScale m a : entireSubring V) : V → ℂ) = fun z => (a : V → ℂ) (m • z) := rfl

theorem entireScale_entireScale (m m' : ℂ) (a : entireSubring V) :
    entireScale m (entireScale m' a) = entireScale (m' * m) a := by
  apply Subtype.ext
  funext z
  show (a : V → ℂ) (m' • m • z) = (a : V → ℂ) ((m' * m) • z)
  rw [mul_smul]

theorem entireScale_one (a : entireSubring V) : entireScale 1 a = a := by
  apply Subtype.ext
  funext z
  show (a : V → ℂ) ((1 : ℂ) • z) = _
  rw [one_smul]

/-- Pullback along `z ↦ m z`, as an automorphism of the entire functions. -/
noncomputable def entireScaleEquiv {m : ℂ} (hm : m ≠ 0) :
    entireSubring V ≃+* entireSubring V where
  toFun := entireScale m
  invFun := entireScale m⁻¹
  left_inv a := by rw [entireScale_entireScale, mul_inv_cancel₀ hm, entireScale_one]
  right_inv a := by rw [entireScale_entireScale, inv_mul_cancel₀ hm, entireScale_one]
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem entireScaleEquiv_apply {m : ℂ} (hm : m ≠ 0) (a : entireSubring V) :
    entireScaleEquiv hm a = entireScale m a := rfl

/-- Pullback along `z ↦ m z`, as an automorphism of the entire fraction field. -/
noncomputable def fieldScaleEquiv {m : ℂ} (hm : m ≠ 0) : EntireField V ≃+* EntireField V :=
  IsFractionRing.ringEquivOfRingEquiv (entireScaleEquiv (V := V) hm)

theorem fieldScaleEquiv_algebraMap {m : ℂ} (hm : m ≠ 0) (a : entireSubring V) :
    fieldScaleEquiv hm (algebraMap (entireSubring V) (EntireField V) a)
      = algebraMap (entireSubring V) (EntireField V) (entireScale m a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (entireScaleEquiv (V := V) hm) a

/-- Scaling turns a translation of the variable into the scaled translation. -/
theorem entireScale_entireTranslate (m : ℂ) (s : V) (a : entireSubring V) :
    entireScale m (entireTranslate (m • s) a) = entireTranslate s (entireScale m a) := by
  apply Subtype.ext
  funext z
  show (a : V → ℂ) (m • z + m • s) = (a : V → ℂ) (m • (z + s))
  rw [smul_add]

/-- **Translation and scaling of the entire fraction field commute up to the isogeny.** -/
theorem fieldTranslateEquiv_fieldScaleEquiv {m : ℂ} (hm : m ≠ 0) (s : V) (x : EntireField V) :
    fieldTranslateEquiv s (fieldScaleEquiv hm x)
      = fieldScaleEquiv hm (fieldTranslateEquiv (m • s) x) := by
  have hcomp : ((fieldTranslateEquiv s : EntireField V ≃+* EntireField V) :
        EntireField V →+* EntireField V).comp
        ((fieldScaleEquiv hm : EntireField V ≃+* EntireField V) : EntireField V →+* EntireField V)
      = ((fieldScaleEquiv hm : EntireField V ≃+* EntireField V) :
          EntireField V →+* EntireField V).comp
        ((fieldTranslateEquiv (m • s) : EntireField V ≃+* EntireField V) :
          EntireField V →+* EntireField V) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (entireSubring V)) ?_
    refine RingHom.ext fun a => ?_
    show fieldTranslateEquiv s (fieldScaleEquiv hm
      (algebraMap (entireSubring V) (EntireField V) a))
      = fieldScaleEquiv hm (fieldTranslateEquiv (m • s)
        (algebraMap (entireSubring V) (EntireField V) a))
    rw [fieldScaleEquiv_algebraMap, fieldTranslateEquiv_algebraMap,
      fieldTranslateEquiv_algebraMap, fieldScaleEquiv_algebraMap, entireScale_entireTranslate]
  exact RingHom.congr_fun hcomp x

/-- The functions of the complex torus `V / Λ`: the `Λ`-periodic elements of the entire fraction
field. -/
noncomputable def torusSubfield (L : PeriodLattice V) : IntermediateField ℂ (EntireField V) where
  carrier := {x : EntireField V | ∀ t ∈ L.lattice, fieldTranslateEquiv t x = x}
  zero_mem' := by intro t _; simp
  one_mem' := by intro t _; simp
  add_mem' := by
    intro x y hx hy t ht
    rw [map_add, hx t ht, hy t ht]
  mul_mem' := by
    intro x y hx hy t ht
    rw [map_mul, hx t ht, hy t ht]
  inv_mem' := by
    intro x hx t ht
    rw [map_inv₀, hx t ht]
  algebraMap_mem' := by
    intro c t _
    show fieldTranslateEquiv t (constEntire V c) = constEntire V c
    rw [fieldTranslateEquiv_constEntire]

theorem mem_torusSubfield_iff (L : PeriodLattice V) {x : EntireField V} :
    x ∈ torusSubfield L ↔ ∀ t ∈ L.lattice, fieldTranslateEquiv t x = x := Iff.rfl

/-- **The deck group of an isogeny is its group of division points.**  An element of the entire
fraction field is the pullback of a function of the torus `V / Λ` along `z ↦ m z` exactly when every
translation by a point whose `m`-multiple lies in `Λ` fixes it. -/
theorem exists_mem_torusSubfield_fieldScaleEquiv_iff (L : PeriodLattice V) {m : ℂ} (hm : m ≠ 0)
    (x : EntireField V) :
    (∃ y ∈ torusSubfield L, fieldScaleEquiv hm y = x)
      ↔ ∀ t : V, m • t ∈ L.lattice → fieldTranslateEquiv t x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩ t ht
    rw [fieldTranslateEquiv_fieldScaleEquiv, hy (m • t) ht]
  · intro hx
    refine ⟨(fieldScaleEquiv hm).symm x, ?_, (fieldScaleEquiv hm).apply_symm_apply x⟩
    intro t ht
    refine (fieldScaleEquiv hm).injective ?_
    have hms : m • (m⁻¹ • t) = t := by
      rw [smul_smul, mul_inv_cancel₀ hm, one_smul]
    have hkey := fieldTranslateEquiv_fieldScaleEquiv hm (m⁻¹ • t)
      ((fieldScaleEquiv hm).symm x)
    rw [hms, (fieldScaleEquiv hm).apply_symm_apply] at hkey
    rw [← hkey, (fieldScaleEquiv hm).apply_symm_apply]
    exact hx (m⁻¹ • t) (by rw [hms]; exact ht)

/-- **The phase tail of a complex torus protocol is the constants.**  For accumulated degrees of
unbounded norm, an element of the entire fraction field that is a pullback of a function of the
torus at every depth is a constant: the union of the prefix kernels is dense. -/
theorem eq_constEntire_of_forall_mem_range_fieldScaleEquiv (L : PeriodLattice V) (M : ℕ → ℂ)
    (hM : ∀ k, M k ≠ 0) (hMinf : Tendsto (fun k => ‖M k‖) atTop atTop) {x : EntireField V}
    (hx : ∀ k : ℕ, ∃ y ∈ torusSubfield L, fieldScaleEquiv (hM k) y = x) :
    ∃ c : ℂ, x = constEntire V c := by
  refine eq_constEntire_of_dense_translation_invariant (dense_divisionPoints L M hM hMinf) ?_
  rintro t ⟨k, hk⟩
  exact (exists_mem_torusSubfield_fieldScaleEquiv_iff L (hM k) x).mp (hx k) t hk

end GaloisForLFunctions.HTGeometry
