import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness

/-!
# Equivariant intervention-response blindness and transverse-mark necessity

A group `G` acts on a manifold `X`; a doctrine map `P : X → Q` is `G`-invariant and an intervention
vector field `V` is `G`-equivariant.  Then the first doctrine response `x ↦ dP_x (V x)` is constant
on `G`-orbits, so no coframe of equivariant interventions can identify a coordinate along the orbit.

* `doctrineResponse`, `mfderiv_comp_eq_of_invariant`, `doctrineResponse_eq_of_equivariant`,
  `doctrineResponse_smul` — Theorem 1, the naturality identity `dP_{gx} ∘ g_* = dP_x` applied to an
  equivariant field;
* `responseCoframe_constant_on_orbit` and `orbitResponseCoframe` — an arbitrary family of
  equivariant interventions has combined first response factoring through the orbit space;
* `separation_forces_escape` — Corollary 2, necessity: a first-order coframe that does separate two
  points of one orbit forces one of the structural hypotheses to fail;
* `circleDoctrine`, `radialField`, `conjField`, `tangentModulatedField` — a complete concrete model
  on `ℂ` under the rotation group showing that the escape routes are *necessary but not sufficient*:
  the conjugation field is non-equivariant and does separate, while the orbit-tangent modulated
  field is equally non-equivariant and separates nothing;
* `kummerReporter_radial` — the exact source instantiation: the identity trace and the Kummer
  cyclic cocycle of a graded algebra, reused from
  `HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness`, form a reporter coframe that is
  invariant under the whole radial gauge family and therefore cannot select the radial origin.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Manifold

/-! ## Theorem 1 — equivariant response blindness -/

section EquivariantResponse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]

/-- The first doctrine response of an intervention field, equation (3). -/
noncomputable def doctrineResponse (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (P : X → Q) (V : ∀ x : X, TangentSpace I x) (x : X) : TangentSpace J (P x) :=
  mfderiv I J P x (V x)

/-- **Naturality of an invariant doctrine map:** `dP_{Φx} ∘ Φ_* = dP_x`. -/
theorem mfderiv_comp_eq_of_invariant {Φ : X → X} {P : X → Q} (x : X)
    (hP : MDifferentiableAt I J P (Φ x)) (hΦ : MDifferentiableAt I I Φ x)
    (hinv : P ∘ Φ = P) :
    (mfderiv I J P (Φ x)).comp (mfderiv I I Φ x) = mfderiv I J P x := by
  rw [← mfderiv_comp x hP hΦ, hinv]

/-- **Theorem 1, equation (4), for one symmetry.**  An invariant doctrine map and an equivariant
intervention field have equal first responses at `x` and at `Φ x`. -/
theorem doctrineResponse_eq_of_equivariant {Φ : X → X} {P : X → Q}
    {V : ∀ x : X, TangentSpace I x} (x : X)
    (hP : MDifferentiableAt I J P (Φ x)) (hΦ : MDifferentiableAt I I Φ x)
    (hinv : P ∘ Φ = P) (hV : V (Φ x) = mfderiv I I Φ x (V x)) :
    doctrineResponse I J P V (Φ x) = doctrineResponse I J P V x := by
  rw [doctrineResponse, doctrineResponse, hV, ← ContinuousLinearMap.comp_apply,
    mfderiv_comp_eq_of_invariant x hP hΦ hinv]
  rfl

variable {G : Type*} [Group G] [MulAction G X]

/-- **Theorem 1, equation (4).**  For a group acting by smooth maps, an invariant doctrine map and
an equivariant intervention field give a `G`-invariant first response. -/
theorem doctrineResponse_smul {P : X → Q} {V : ∀ x : X, TangentSpace I x}
    (hP : MDifferentiable I J P)
    (hsmul : ∀ g : G, MDifferentiable I I (fun y : X => g • y))
    (hPinv : ∀ (g : G) (x : X), P (g • x) = P x)
    (hV : ∀ (g : G) (x : X), V (g • x) = mfderiv I I (fun y : X => g • y) x (V x))
    (g : G) (x : X) :
    doctrineResponse I J P V (g • x) = doctrineResponse I J P V x :=
  doctrineResponse_eq_of_equivariant (Φ := fun y : X => g • y) x (hP _) (hsmul g x)
    (funext fun y => hPinv g y) (hV g x)

/-- The combined first-response map of a whole family of interventions — the response coframe. -/
noncomputable def responseCoframe (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (P : X → Q) {ι : Type*} (V : ι → ∀ x : X, TangentSpace I x) (x : X) : ι → F :=
  fun i => doctrineResponse I J P (V i) x

/-- **The combined first response of an equivariant family is constant on orbits.** -/
theorem responseCoframe_smul {P : X → Q} {ι : Type*} {V : ι → ∀ x : X, TangentSpace I x}
    (hP : MDifferentiable I J P)
    (hsmul : ∀ g : G, MDifferentiable I I (fun y : X => g • y))
    (hPinv : ∀ (g : G) (x : X), P (g • x) = P x)
    (hV : ∀ (i : ι) (g : G) (x : X),
      V i (g • x) = mfderiv I I (fun y : X => g • y) x (V i x))
    (g : G) (x : X) :
    responseCoframe I J P V (g • x) = responseCoframe I J P V x :=
  funext fun i => doctrineResponse_smul hP hsmul hPinv (hV i) g x

theorem responseCoframe_constant_on_orbit {P : X → Q} {ι : Type*}
    {V : ι → ∀ x : X, TangentSpace I x}
    (hP : MDifferentiable I J P)
    (hsmul : ∀ g : G, MDifferentiable I I (fun y : X => g • y))
    (hPinv : ∀ (g : G) (x : X), P (g • x) = P x)
    (hV : ∀ (i : ι) (g : G) (x : X),
      V i (g • x) = mfderiv I I (fun y : X => g • y) x (V i x))
    {x y : X} (hxy : y ∈ MulAction.orbit G x) :
    responseCoframe I J P V y = responseCoframe I J P V x := by
  obtain ⟨g, rfl⟩ := hxy
  exact responseCoframe_smul hP hsmul hPinv hV g x

/-- **The first-response coframe factors through the orbit space.**  This is the exact sense in
which an equivariant family cannot identify a coordinate along the orbits. -/
noncomputable def orbitResponseCoframe {P : X → Q} {ι : Type*}
    {V : ι → ∀ x : X, TangentSpace I x}
    (hP : MDifferentiable I J P)
    (hsmul : ∀ g : G, MDifferentiable I I (fun y : X => g • y))
    (hPinv : ∀ (g : G) (x : X), P (g • x) = P x)
    (hV : ∀ (i : ι) (g : G) (x : X),
      V i (g • x) = mfderiv I I (fun y : X => g • y) x (V i x)) :
    MulAction.orbitRel.Quotient G X → (ι → F) :=
  Quotient.lift (responseCoframe I J P V) (by
    intro a b hab
    exact responseCoframe_constant_on_orbit hP hsmul hPinv hV
      ((MulAction.orbitRel_apply).mp hab))

@[simp] theorem orbitResponseCoframe_mk {P : X → Q} {ι : Type*}
    {V : ι → ∀ x : X, TangentSpace I x}
    (hP : MDifferentiable I J P)
    (hsmul : ∀ g : G, MDifferentiable I I (fun y : X => g • y))
    (hPinv : ∀ (g : G) (x : X), P (g • x) = P x)
    (hV : ∀ (i : ι) (g : G) (x : X),
      V i (g • x) = mfderiv I I (fun y : X => g • y) x (V i x)) (x : X) :
    orbitResponseCoframe hP hsmul hPinv hV
      (Quotient.mk (MulAction.orbitRel G X) x) = responseCoframe I J P V x := rfl

/-! ## Corollary 2 — necessity of an escape -/

/-- **Corollary 2 (necessity).**  If a first-order response coframe separates two points of one
`G`-orbit, then at least one structural hypothesis fails: the doctrine map is not `G`-invariant,
or some intervention of the family is not `G`-equivariant, or the action is not smooth, or the
doctrine map is not differentiable.  Since the separating datum here *is* a first jet of an
intervention, the fourth escape route of the paper card — a higher or nonlocal response — is the
statement that the separating datum is not of this form at all. -/
theorem separation_forces_escape {P : X → Q} {ι : Type*} {V : ι → ∀ x : X, TangentSpace I x}
    {g : G} {x : X} (hsep : responseCoframe I J P V (g • x) ≠ responseCoframe I J P V x) :
    (¬ ∀ (g : G) (x : X), P (g • x) = P x) ∨
      (¬ ∀ (i : ι) (g : G) (x : X),
        V i (g • x) = mfderiv I I (fun y : X => g • y) x (V i x)) ∨
      (¬ ∀ g : G, MDifferentiable I I (fun y : X => g • y)) ∨
      (¬ MDifferentiable I J P) := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  exact hsep (responseCoframe_smul h4 h3 h1 h2 g x)

end EquivariantResponse

/-! ## A complete concrete model: the rotation group acting on the plane

The escape routes of Corollary 2 are **necessary but not sufficient**.  This section certifies both
halves on one fixed model: `X = Q = ℂ`, `G = Circle` acting by rotation, and the invariant doctrine
map `z ↦ z · conj z`.  The conjugation field is non-equivariant and *does* separate a rotation
orbit; the orbit-tangent modulated field is equally non-equivariant and separates nothing. -/

section CircleModel

/-- Multiplication by a fixed complex number, as a real-linear map: the differential of a
rotation. -/
noncomputable def rotCLM (c : ℂ) : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) c

@[simp] theorem rotCLM_apply (c z : ℂ) : rotCLM c z = c * z := rfl

theorem rot_eq (g : Circle) : (fun y : ℂ => g • y) = ⇑(rotCLM (g : ℂ)) :=
  funext fun y => Circle.smul_def g y

/-- The rotation action is smooth. -/
theorem mdifferentiable_rot (g : Circle) :
    MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => g • z) := by
  intro z
  have h : HasFDerivAt (fun y : ℂ => g • y) (rotCLM (g : ℂ)) z := by
    rw [rot_eq]; exact (rotCLM (g : ℂ)).hasFDerivAt
  exact h.hasMFDerivAt.mdifferentiableAt

/-- The pushforward of a rotation is multiplication by the same unit complex number. -/
theorem mfderiv_rot (g : Circle) (z w : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y) z w = (g : ℂ) * w := by
  have hstep : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y) z w
      = fderiv ℝ (fun y : ℂ => g • y) z w := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hstep, rot_eq, (rotCLM (g : ℂ)).fderiv]
  rfl

theorem circle_mul_conj (g : Circle) : (g : ℂ) * (starRingEnd ℂ) (g : ℂ) = 1 := by
  rw [Complex.mul_conj, Circle.normSq_coe]
  norm_num

/-- The rotation-invariant doctrine map of the plane. -/
def circleDoctrine (z : ℂ) : ℂ := z * (starRingEnd ℂ) z

theorem hasFDerivAt_circleDoctrine (z : ℂ) :
    HasFDerivAt circleDoctrine
      (z • (Complex.conjCLE : ℂ →L[ℝ] ℂ) +
        ((starRingEnd ℂ) z) • (ContinuousLinearMap.id ℝ ℂ)) z :=
  (hasFDerivAt_id z).mul Complex.conjCLE.hasFDerivAt

theorem mdifferentiable_circleDoctrine :
    MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine := fun z =>
  (hasFDerivAt_circleDoctrine z).hasMFDerivAt.mdifferentiableAt

/-- **The doctrine map is rotation invariant.** -/
theorem circleDoctrine_smul (g : Circle) (z : ℂ) :
    circleDoctrine (g • z) = circleDoctrine z := by
  have hg := circle_mul_conj g
  have hs : (g : Circle) • z = (g : ℂ) * z := by rw [Circle.smul_def, smul_eq_mul]
  rw [circleDoctrine, circleDoctrine, hs, map_mul]
  calc (g : ℂ) * z * ((starRingEnd ℂ) (g : ℂ) * (starRingEnd ℂ) z)
      = ((g : ℂ) * (starRingEnd ℂ) (g : ℂ)) * (z * (starRingEnd ℂ) z) := by ring
    _ = z * (starRingEnd ℂ) z := by rw [hg, one_mul]

/-- The first response of the plane doctrine to an arbitrary intervention direction. -/
theorem mfderiv_circleDoctrine (z w : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine z w
      = z * (starRingEnd ℂ) w + (starRingEnd ℂ) z * w := by
  have hstep : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine z w
      = fderiv ℝ circleDoctrine z w := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hstep, (hasFDerivAt_circleDoctrine z).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, smul_eq_mul]

/-! ### Three intervention fields -/

/-- The radial field `z ↦ z`: equivariant. -/
noncomputable def radialField : ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z := fun z => z

/-- The conjugation field `z ↦ conj z`: not equivariant, and it does separate. -/
noncomputable def conjField : ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z := fun z => (starRingEnd ℂ) z

/-- The orbit-tangent field modulated by a non-invariant real amplitude: not equivariant either,
and it separates nothing. -/
noncomputable def tangentModulatedField : ∀ z : ℂ, TangentSpace 𝓘(ℝ, ℂ) z :=
  fun z => (z.re : ℂ) * Complex.I * z

theorem radialField_equivariant (g : Circle) (z : ℂ) :
    radialField (g • z)
      = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y) z (radialField z) :=
  (Circle.smul_def g z).trans (mfderiv_rot g z z).symm

/-- **The equivariant field has a rotation-invariant response**, as Theorem 1 predicts. -/
theorem doctrineResponse_radialField (z : ℂ) :
    doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine radialField z
      = z * (starRingEnd ℂ) z + (starRingEnd ℂ) z * z :=
  mfderiv_circleDoctrine z z

theorem doctrineResponse_conjField (z : ℂ) :
    doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine conjField z
      = z * z + (starRingEnd ℂ) z * (starRingEnd ℂ) z := by
  have h := mfderiv_circleDoctrine z ((starRingEnd ℂ) z)
  rw [Complex.conj_conj] at h
  exact h

/-- **The orbit-tangent modulated field has identically zero first response.** -/
theorem doctrineResponse_tangentModulatedField (z : ℂ) :
    doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine tangentModulatedField z = 0 := by
  have h := mfderiv_circleDoctrine z ((z.re : ℂ) * Complex.I * z)
  have h0 : z * (starRingEnd ℂ) ((z.re : ℂ) * Complex.I * z)
      + (starRingEnd ℂ) z * ((z.re : ℂ) * Complex.I * z) = 0 := by
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  exact h.trans h0

/-- A quarter turn. -/
def quarterTurn : Circle :=
  ⟨Complex.I, by
    show Complex.I ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    simp⟩

@[simp] theorem quarterTurn_coe : (quarterTurn : ℂ) = Complex.I := rfl

/-- **The conjugation field is not equivariant.** -/
theorem conjField_not_equivariant :
    ¬ ∀ (g : Circle) (z : ℂ),
        conjField (g • z)
          = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y) z (conjField z) := by
  intro h
  have h1 := h quarterTurn 1
  rw [mfderiv_rot] at h1
  have h2 : ((starRingEnd ℂ) ((quarterTurn : ℂ) * 1) : ℂ)
      = (quarterTurn : ℂ) * (starRingEnd ℂ) (1 : ℂ) := by
    have hs : (quarterTurn : Circle) • (1 : ℂ) = (quarterTurn : ℂ) * 1 := by
      rw [Circle.smul_def, smul_eq_mul]
    rw [← hs]
    exact h1
  rw [quarterTurn_coe] at h2
  simp only [mul_one, Complex.conj_I, map_one] at h2
  exact Complex.I_ne_zero (by linear_combination -h2 / 2)

/-- **The orbit-tangent modulated field is not equivariant either.** -/
theorem tangentModulatedField_not_equivariant :
    ¬ ∀ (g : Circle) (z : ℂ),
        tangentModulatedField (g • z)
          = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y) z (tangentModulatedField z) := by
  intro h
  have h1 := h quarterTurn 1
  rw [mfderiv_rot] at h1
  have hs : (quarterTurn : Circle) • (1 : ℂ) = (quarterTurn : ℂ) * 1 := by
    rw [Circle.smul_def, smul_eq_mul]
  have h2 : ((((quarterTurn : ℂ) * 1).re : ℂ) * Complex.I * ((quarterTurn : ℂ) * 1))
      = (quarterTurn : ℂ) * (((1 : ℂ).re : ℂ) * Complex.I * 1) := by
    rw [← hs]; exact h1
  rw [quarterTurn_coe] at h2
  simp only [mul_one, Complex.I_re, Complex.one_re, Complex.ofReal_zero, Complex.ofReal_one,
    zero_mul, one_mul, Complex.I_mul_I] at h2
  exact one_ne_zero (α := ℂ) (by linear_combination h2)

/-- The conjugation response at the base point. -/
theorem conjField_response_one :
    doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine conjField 1 = (2 : ℂ) := by
  have h : (1 : ℂ) * 1 + (starRingEnd ℂ) (1 : ℂ) * (starRingEnd ℂ) (1 : ℂ) = (2 : ℂ) := by
    norm_num
  exact (doctrineResponse_conjField 1).trans h

theorem quarterTurn_smul_one : (quarterTurn • (1 : ℂ)) = Complex.I := by
  rw [Circle.smul_def, smul_eq_mul, quarterTurn_coe, mul_one]

/-- The conjugation response at the quarter-turn image of the base point. -/
theorem conjField_response_smul_one :
    doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine conjField (quarterTurn • (1 : ℂ))
      = (-2 : ℂ) := by
  have h : (quarterTurn • (1 : ℂ)) * (quarterTurn • (1 : ℂ))
      + (starRingEnd ℂ) (quarterTurn • (1 : ℂ)) * (starRingEnd ℂ) (quarterTurn • (1 : ℂ))
      = (-2 : ℂ) := by
    rw [quarterTurn_smul_one, Complex.conj_I]
    linear_combination (2 : ℂ) * Complex.I_mul_I
  exact (doctrineResponse_conjField _).trans h

/-- **Escape route 1 is real.**  A non-equivariant legal intervention does separate two points of
one rotation orbit, even though the doctrine map is invariant and the action is smooth. -/
theorem circleModel_escape_separates :
    (∀ (g : Circle) (z : ℂ), circleDoctrine (g • z) = circleDoctrine z) ∧
      (∀ g : Circle, MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y)) ∧
      MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine ∧
      (¬ ∀ (g : Circle) (z : ℂ),
        conjField (g • z)
          = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y) z (conjField z)) ∧
      doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine conjField (quarterTurn • (1 : ℂ))
        ≠ doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine conjField 1 := by
  refine ⟨circleDoctrine_smul, mdifferentiable_rot, mdifferentiable_circleDoctrine,
    conjField_not_equivariant, ?_⟩
  intro hcon
  have h : (-2 : ℂ) = (2 : ℂ) :=
    conjField_response_smul_one.symm.trans (hcon.trans conjField_response_one)
  norm_num at h

/-- **Escape route 1 is not sufficient.**  An equally non-equivariant legal intervention can have
identically vanishing first response, so it separates nothing at all. -/
theorem circleModel_escape_not_sufficient :
    (¬ ∀ (g : Circle) (z : ℂ),
        tangentModulatedField (g • z)
          = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y : ℂ => g • y) z (tangentModulatedField z)) ∧
      (∀ (g : Circle) (z : ℂ),
        doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine tangentModulatedField (g • z)
          = doctrineResponse 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) circleDoctrine tangentModulatedField z) :=
  ⟨tangentModulatedField_not_equivariant, fun g z =>
    (doctrineResponse_tangentModulatedField (g • z)).trans
      (doctrineResponse_tangentModulatedField z).symm⟩

end CircleModel

/-! ## Orbit blindness of an invariant reporter -/

section InvariantReporter

variable {S R G : Type*} [Group G] [MulAction G S]

/-- A reporter invariant under the whole symmetry group takes the same value at every point of an
orbit. -/
theorem reporter_eq_of_mem_orbit (rep : S → R) (h : ∀ (g : G) (s : S), rep (g • s) = rep s)
    {s t : S} (hst : t ∈ MulAction.orbit G s) : rep t = rep s := by
  obtain ⟨g, rfl⟩ := hst
  exact h g s

/-- An invariant reporter descends to the orbit space; it is exactly a function of the orbit. -/
def orbitReporter (rep : S → R) (h : ∀ (g : G) (s : S), rep (g • s) = rep s) :
    MulAction.orbitRel.Quotient G S → R :=
  Quotient.lift rep fun _ _ hab =>
    reporter_eq_of_mem_orbit rep h ((MulAction.orbitRel_apply).mp hab)

@[simp] theorem orbitReporter_mk (rep : S → R) (h : ∀ (g : G) (s : S), rep (g • s) = rep s)
    (s : S) :
    orbitReporter rep h (Quotient.mk (MulAction.orbitRel G S) s) = rep s := rfl

end InvariantReporter

/-! ## The exact radial-source instantiation

The literal graded source of the corpus already carries the radial gauge family `Γ_c` and its
reporters; they are reused verbatim from
`HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness`.  The point of this section is that
the *whole* valuation/Kummer reporter coframe is `Γ_c`-invariant, so by the previous section it is a
function of the radial orbit alone and can never select the radial origin. -/

section RadialSource

open _root_.HTGeometry.ConstraintRelativity

variable {ι A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommRing A] [Algebra ℂ A]
  (𝒜 : ι → Submodule ℂ A) [GradedAlgebra 𝒜]

/-- The valuation/Kummer reporter coframe of the graded source: the identity-sector trace together
with the logarithmic cyclic one-cocycle. -/
noncomputable def kummerReporter (L : ι → ℂ) (x y : A) : A × A :=
  (identityTrace 𝒜 x, kummerCocycle 𝒜 L x y)

/-- **The whole reporter coframe is blind to every character gauge.** -/
theorem kummerReporter_gradeDiag {f L : ι → ℂ} (hf0 : f 0 = 1)
    (hf : ∀ i j, f (i + j) = f i * f j) (x y : A) :
    kummerReporter 𝒜 L (gradeDiag 𝒜 f x) (gradeDiag 𝒜 f y) = kummerReporter 𝒜 L x y := by
  rw [kummerReporter, kummerReporter, identityTrace_gradeDiag 𝒜 hf0,
    kummerCocycle_gradeDiag 𝒜 hf0 hf]

omit [DecidableEq ι] in
/-- A positive multiplicative absolute grade takes the value one at the identity grade. -/
theorem absoluteGrade_zero {ν : ι → ℝ} (hνpos : ∀ i, 0 < ν i)
    (hν : ∀ i j, ν (i + j) = ν i * ν j) : ν 0 = 1 := by
  have h := hν 0 0
  rw [add_zero] at h
  nlinarith [hνpos 0]

/-- **The exact instantiation.**  The reporter coframe takes the same value at a chain and at every
radial gauge transform of it. -/
theorem kummerReporter_radial {ν : ι → ℝ} (hνpos : ∀ i, 0 < ν i)
    (hν : ∀ i j, ν (i + j) = ν i * ν j) (L : ι → ℂ) (c : ℝ) (x y : A) :
    kummerReporter 𝒜 L (gradeDiag 𝒜 (radialMultiplier ν c) x)
        (gradeDiag 𝒜 (radialMultiplier ν c) y) = kummerReporter 𝒜 L x y :=
  kummerReporter_gradeDiag 𝒜 (radialMultiplier_zero (absoluteGrade_zero hνpos hν) c)
    (radialMultiplier_add hνpos hν c) x y

/-- **The reporter coframe cannot separate two members of one radial orbit.**  This is the exact
source obstruction: no amount of additional equivariant cyclic reporting selects the radial
parameter. -/
theorem kummerReporter_not_separating {ν : ι → ℝ} (hνpos : ∀ i, 0 < ν i)
    (hν : ∀ i j, ν (i + j) = ν i * ν j) (L : ι → ℂ) (c d : ℝ) (x y : A) :
    kummerReporter 𝒜 L (gradeDiag 𝒜 (radialMultiplier ν c) x)
        (gradeDiag 𝒜 (radialMultiplier ν c) y)
      = kummerReporter 𝒜 L (gradeDiag 𝒜 (radialMultiplier ν d) x)
        (gradeDiag 𝒜 (radialMultiplier ν d) y) :=
  (kummerReporter_radial 𝒜 hνpos hν L c x y).trans
    (kummerReporter_radial 𝒜 hνpos hν L d x y).symm

end RadialSource

end GaloisForLFunctions.HTGeometry
