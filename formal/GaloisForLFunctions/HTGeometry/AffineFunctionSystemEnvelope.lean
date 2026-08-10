import GaloisForLFunctions.HTGeometry.CStarEnvelopeCommutative

/-!
# The C*-envelope of the affine functions on a compact convex set

For a compact convex set `K` in a locally convex space, the continuous complex affine functions
`A(K)` form a unital, self-adjoint, separating subspace of `C(K, ℂ)`.  Because every element of
`A(K)` is affine, the evaluation map `δ : K → (A(K) → ℂ)` is affine, so its range is already convex
and compact: the state body of `A(K)` *is* the range, with no hull or closure to take.

Consequently the extreme-point structure transports exactly, and the Choquet boundary of `A(K)` is
the set of extreme points of `K`.  Combined with the commutative C*-envelope this identifies the
envelope of `A(K)` as the continuous functions on the closure of `ext K`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
variable {K : Set E}

/-- The continuous complex-valued affine functions on a convex set. -/
def affineFunctions (hK : Convex ℝ K) : Submodule ℂ C(K, ℂ) where
  carrier := {f : C(K, ℂ) | ∀ (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    f ⟨a • (x : E) + b • (y : E), hK x.2 y.2 ha hb hab⟩ = (a : ℂ) • f x + (b : ℂ) • f y}
  add_mem' {f g} hf hg := by
    intro x y a b ha hb hab
    simp only [ContinuousMap.add_apply, hf x y a b ha hb hab, hg x y a b ha hb hab]
    module
  zero_mem' := by
    intro x y a b ha hb hab
    simp
  smul_mem' c f hf := by
    intro x y a b ha hb hab
    simp only [ContinuousMap.smul_apply, hf x y a b ha hb hab]
    module

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
theorem mem_affineFunctions {hK : Convex ℝ K} {f : C(K, ℂ)} :
    f ∈ affineFunctions hK ↔ ∀ (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
      f ⟨a • (x : E) + b • (y : E), hK x.2 y.2 ha hb hab⟩ = (a : ℂ) • f x + (b : ℂ) • f y :=
  Iff.rfl

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
theorem one_mem_affineFunctions (hK : Convex ℝ K) : (1 : C(K, ℂ)) ∈ affineFunctions hK := by
  intro x y a b ha hb hab
  simp only [ContinuousMap.one_apply, smul_eq_mul, mul_one]
  rw [← Complex.ofReal_add, hab, Complex.ofReal_one]

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
theorem star_mem_affineFunctions (hK : Convex ℝ K) {f : C(K, ℂ)} (hf : f ∈ affineFunctions hK) :
    star f ∈ affineFunctions hK := by
  intro x y a b ha hb hab
  simp only [ContinuousMap.star_apply, hf x y a b ha hb hab, star_add, star_smul,
    Complex.star_def, Complex.conj_ofReal]

variable [CompactSpace K]

omit [CompactSpace K] in
theorem separating_affineFunctions (hK : Convex ℝ K) :
    ∀ x y : K, x ≠ y → ∃ f ∈ affineFunctions hK, (f : C(K, ℂ)) x ≠ f y := by
  intro x y hxy
  have hne : (x : E) ≠ (y : E) := fun h => hxy (Subtype.ext h)
  obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hne
  refine ⟨⟨fun z => ((l (z : E) : ℝ) : ℂ), by fun_prop⟩, ?_, ?_⟩
  · intro u v a b ha hb hab
    simp only [ContinuousMap.coe_mk, map_add, map_smul, smul_eq_mul]
    push_cast
    ring
  · simp only [ContinuousMap.coe_mk, ne_eq, Complex.ofReal_inj]
    exact ne_of_lt hl

/-! ## The state body is the range -/

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E][CompactSpace K] in
theorem evalPoint_affine (hK : Convex ℝ K) {u v : E} (hu : u ∈ K) (hv : v ∈ K) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z : K) (hz : (z : E) = a • u + b • v) :
    evalPoint (affineFunctions hK) z
      = a • evalPoint (affineFunctions hK) ⟨u, hu⟩ + b • evalPoint (affineFunctions hK) ⟨v, hv⟩ := by
  funext f
  have hzeq : z = (⟨a • u + b • v, hK hu hv ha hb hab⟩ : K) := Subtype.ext hz
  have haff := f.2 ⟨u, hu⟩ ⟨v, hv⟩ a b ha hb hab
  simp only [evalPoint_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  rw [hzeq]
  exact haff

omit [CompactSpace K] in
theorem injective_evalPoint (hK : Convex ℝ K) :
    Function.Injective (evalPoint (affineFunctions hK)) := by
  intro x y hxy
  by_contra hne
  obtain ⟨f, hf, hfne⟩ := separating_affineFunctions hK x y hne
  exact hfne (congrFun hxy ⟨f, hf⟩)

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [CompactSpace K] in
theorem convex_range_evalPoint (hK : Convex ℝ K) :
    Convex ℝ (Set.range (evalPoint (affineFunctions hK))) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb hab
  refine ⟨⟨a • (x : E) + b • (y : E), hK x.2 y.2 ha hb hab⟩, ?_⟩
  exact evalPoint_affine hK x.2 y.2 ha hb hab _ rfl

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
theorem stateBody_affineFunctions (hK : Convex ℝ K) :
    stateBody (affineFunctions hK) = Set.range (evalPoint (affineFunctions hK)) := by
  rw [stateBody, (convex_range_evalPoint hK).convexHull_eq,
    (isCompact_range_evalPoint (affineFunctions hK)).isClosed.closure_eq]

/-! ## The Choquet boundary is the set of extreme points -/

theorem mem_choquetBoundary_iff_extremePoint (hK : Convex ℝ K) (x : K) :
    x ∈ choquetBoundary (affineFunctions hK) ↔ (x : E) ∈ K.extremePoints ℝ := by
  rw [choquetBoundary, Set.mem_setOf_eq, stateBody_affineFunctions hK]
  constructor
  · rintro ⟨-, hext⟩
    refine ⟨x.2, fun u hu v hv hxseg => ?_⟩
    obtain ⟨a, b, ha, hb, hab, hxab⟩ := hxseg
    have hδseg : evalPoint (affineFunctions hK) x
        ∈ openSegment ℝ (evalPoint (affineFunctions hK) ⟨u, hu⟩)
          (evalPoint (affineFunctions hK) ⟨v, hv⟩) :=
      ⟨a, b, ha, hb, hab, (evalPoint_affine hK hu hv ha.le hb.le hab x hxab.symm).symm⟩
    have heq := hext ⟨⟨u, hu⟩, rfl⟩ ⟨⟨v, hv⟩, rfl⟩ hδseg
    exact congrArg Subtype.val (injective_evalPoint hK heq)
  · rintro ⟨-, hext⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ hseg
    obtain ⟨a, b, ha, hb, hab, hxab⟩ := hseg
    have hxval : (x : E) = a • (u : E) + b • (v : E) := by
      have hxeq : evalPoint (affineFunctions hK) x
          = evalPoint (affineFunctions hK) ⟨a • (u : E) + b • (v : E), hK u.2 v.2 ha.le hb.le hab⟩ := by
        rw [evalPoint_affine hK u.2 v.2 ha.le hb.le hab
              (⟨a • (u : E) + b • (v : E), hK u.2 v.2 ha.le hb.le hab⟩ : K) rfl, hxab]
      exact congrArg Subtype.val (injective_evalPoint hK hxeq)
    have hxE : (x : E) ∈ openSegment ℝ (u : E) (v : E) := ⟨a, b, ha, hb, hab, hxval.symm⟩
    have huv := hext u.2 v.2 hxE
    exact congrArg (evalPoint (affineFunctions hK)) (Subtype.ext huv)

/-- **The Choquet boundary of `A(K)` is the extreme boundary of `K`.** -/
theorem image_choquetBoundary_affineFunctions (hK : Convex ℝ K) :
    Subtype.val '' choquetBoundary (affineFunctions hK) = K.extremePoints ℝ := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_choquetBoundary_iff_extremePoint hK x).mp hx
  · intro hp
    exact ⟨⟨p, hp.1⟩, (mem_choquetBoundary_iff_extremePoint hK ⟨p, hp.1⟩).mpr hp, rfl⟩

/-- **The Shilov boundary of `A(K)` is the closure of the extreme points of `K`.** -/
theorem image_shilovBoundary_affineFunctions (hK : Convex ℝ K) (hKclosed : IsClosed K) :
    Subtype.val '' shilovBoundary (affineFunctions hK) = closure (K.extremePoints ℝ) := by
  have hemb : Topology.IsClosedEmbedding (Subtype.val : K → E) :=
    Topology.IsClosedEmbedding.subtypeVal hKclosed
  rw [shilovBoundary_eq_closure_choquetBoundary _ (one_mem_affineFunctions hK)
      (fun _ hf => star_mem_affineFunctions hK hf) (separating_affineFunctions hK),
    ← image_choquetBoundary_affineFunctions hK]
  exact (hemb.isClosedMap.closure_image_eq_of_continuous continuous_subtype_val _).symm

/-- **The C*-envelope of the affine functions on a compact convex set.**  The restriction map onto
the closure of the extreme points of `K` is a surjective `*`-homomorphism, isometric on `A(K)`, and
its kernel is the Shilov ideal. -/
theorem envelope_affineFunctions (hK : Convex ℝ K) (hKclosed : IsClosed K) :
    Function.Surjective (envelopeMap (affineFunctions hK)) ∧
      (∀ f ∈ affineFunctions hK, ‖envelopeMap (affineFunctions hK) f‖ = ‖f‖) ∧
      (∀ f : C(K, ℂ), envelopeMap (affineFunctions hK) f = 0 ↔ f ∈ shilovIdeal (affineFunctions hK))
      ∧ Subtype.val '' shilovBoundary (affineFunctions hK) = closure (K.extremePoints ℝ) := by
  obtain ⟨hsurj, hiso, hker, -⟩ :=
    envelope_isometric_surjective_kernel (affineFunctions hK) (one_mem_affineFunctions hK)
      (fun _ hf => star_mem_affineFunctions hK hf) (separating_affineFunctions hK)
  exact ⟨hsurj, hiso, hker, image_shilovBoundary_affineFunctions hK hKclosed⟩

end ShilovLocal

end GaloisForLFunctions.HTGeometry
