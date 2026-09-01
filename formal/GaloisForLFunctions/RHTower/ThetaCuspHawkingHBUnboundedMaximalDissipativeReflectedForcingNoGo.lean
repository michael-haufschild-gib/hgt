import GaloisForLFunctions.RHTower.ThetaCuspHawkingHBBoundedDissipativeReflectedForcingNoGo
import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent

/-!
# Unbounded maximal dissipative reflected-forcing no-go

The exact reduced doubled-weight Einstein--Teukolsky source is nonzero on every tilted Xi fibre,
and Schwarz conjugation sends its angular parameter to the opposite open half-plane. This module
closes the unbounded maximal passive forcing-extinction loophole left by the bounded no-go.

For a closed dissipative partial linear operator `A`, every upper-half-plane shift `A-z` is bounded
below and has closed range. A nonzero vector `y` orthogonal to that range cannot lie in `A.domain`.
Adjoining `y` with eigenvalue `conj z` produces a proper dissipative extension: the range
orthogonality makes its cross terms conjugate and its new diagonal imaginary part strictly
negative. Order maximality therefore forces the range orthogonal to vanish, so `A-z` is
surjective. Reversing signs proves the lower-half-plane antidissipative theorem.

Consequently both exact sources on every hypothetical off-wall Schwarz pair have unique nonzero
responses for any closed order-maximal unbounded passive boundary pair. Such dynamics cannot
produce HB universal source extinction.

Strongest positive survivor: a viable linear extinction law must exploit a non-maximal deficiency
space/domain exclusion. Otherwise it must be nonlinear, reverse the reflected half-plane
orientation, or cancel only after applying a genuinely source-fixed two-leg observable.

`[NEW APPLICATION] [HB ROUTE KILL] [UNBOUNDED] [MAXIMAL DISSIPATIVE] [DEFECT EXTENSION]
[REFLECTED TEUKOLSKY SOURCE] [LEAN-PROVED]`
-/

open Complex Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

def IsPMapDissipative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →ₗ.[ℂ] H) : Prop :=
  ∀ x : A.domain, (⟪(x : H), A x⟫_ℂ).im ≤ 0

def IsPMapAntidissipative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →ₗ.[ℂ] H) : Prop :=
  ∀ x : A.domain, 0 ≤ (⟪(x : H), A x⟫_ℂ).im

def IsClosedMaximalPMapDissipative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →ₗ.[ℂ] H) : Prop :=
  A.IsClosed ∧ IsPMapDissipative A ∧
    ∀ B : H →ₗ.[ℂ] H, IsPMapDissipative B → A ≤ B → B ≤ A

def IsClosedMaximalPMapAntidissipative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →ₗ.[ℂ] H) : Prop :=
  A.IsClosed ∧ IsPMapAntidissipative A ∧
    ∀ B : H →ₗ.[ℂ] H, IsPMapAntidissipative B → A ≤ B → B ≤ A

theorem pmapDissipative_shift_norm_lower
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapDissipative A)
    (z : ℂ) (x : A.domain) :
    z.im * ‖(x : H)‖ ≤ ‖shiftedMap A z x‖ := by
  by_cases hx : (x : H) = 0
  · simp [hx]
  have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hx
  have him :
      (⟪(x : H), shiftedMap A z x⟫_ℂ).im =
        (⟪(x : H), A x⟫_ℂ).im - z.im * ‖(x : H)‖ ^ 2 := by
    simp [shiftedMap_apply, pow_two, Complex.mul_im]
  have hraw :
      z.im * ‖(x : H)‖ ^ 2 ≤ -(⟪(x : H), shiftedMap A z x⟫_ℂ).im := by
    rw [him]
    linarith [hA x]
  have habs :
      -(⟪(x : H), shiftedMap A z x⟫_ℂ).im ≤
        |(⟪(x : H), shiftedMap A z x⟫_ℂ).im| := neg_le_abs _
  have himnorm :
      |(⟪(x : H), shiftedMap A z x⟫_ℂ).im| ≤
        ‖⟪(x : H), shiftedMap A z x⟫_ℂ‖ :=
    Complex.abs_im_le_norm _
  have hcs :
      ‖⟪(x : H), shiftedMap A z x⟫_ℂ‖ ≤
        ‖(x : H)‖ * ‖shiftedMap A z x‖ := norm_inner_le_norm _ _
  have htotal : z.im * ‖(x : H)‖ ^ 2 ≤
      ‖(x : H)‖ * ‖shiftedMap A z x‖ :=
    hraw.trans (habs.trans (himnorm.trans hcs))
  nlinarith

theorem pmapDissipative_shift_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    Function.Injective (shiftedMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hzero : ‖shiftedMap A z x‖ = 0 := by rw [hx, norm_zero]
  have hbound := pmapDissipative_shift_norm_lower A hA z x
  rw [hzero] at hbound
  have hnorm : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
  exact Subtype.ext (norm_eq_zero.mp hnorm)

theorem pmapDissipative_graph_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) (p : A.graph) :
    ‖p‖ ≤ (1 + (1 + ‖z‖) / z.im) * ‖graphShift A z p‖ := by
  obtain ⟨y, hy1, hy2⟩ := A.mem_graph_iff.1 p.2
  have hv : graphShift A z p = A y - z • (y : H) := by
    rw [graphShift_apply, hy1, hy2]
  have hlow := pmapDissipative_shift_norm_lower A hA z y
  rw [shiftedMap_apply, ← hv] at hlow
  have hx : ‖(p : H × H).1‖ ≤ ‖graphShift A z p‖ / z.im := by
    rw [← hy1, le_div_iff₀ hz, mul_comm]
    exact hlow
  have hy : ‖(p : H × H).2‖ ≤
      ‖graphShift A z p‖ + ‖z‖ * ‖(p : H × H).1‖ := by
    have hsplit : (p : H × H).2 = graphShift A z p + z • (p : H × H).1 := by
      rw [graphShift_apply]
      abel
    calc
      ‖(p : H × H).2‖ = ‖graphShift A z p + z • (p : H × H).1‖ := by rw [← hsplit]
      _ ≤ ‖graphShift A z p‖ + ‖z • (p : H × H).1‖ := norm_add_le _ _
      _ = ‖graphShift A z p‖ + ‖z‖ * ‖(p : H × H).1‖ := by rw [norm_smul]
  have hnn : 0 ≤ ‖graphShift A z p‖ := norm_nonneg _
  have hznn : 0 ≤ ‖z‖ := norm_nonneg _
  rw [show ‖p‖ = ‖(p : H × H)‖ from rfl, Prod.norm_def]
  refine max_le ?_ ?_
  · refine le_trans hx ?_
    rw [div_le_iff₀ hz]
    have hkey : (1 + ‖z‖) / z.im * z.im = 1 + ‖z‖ := div_mul_cancel₀ _ hz.ne'
    nlinarith [hnn, hz.le, hznn, hkey, mul_nonneg hnn hz.le, mul_nonneg hnn hznn]
  · refine le_trans hy ?_
    have hx' : ‖z‖ * ‖(p : H × H).1‖ ≤ ‖z‖ * (‖graphShift A z p‖ / z.im) :=
      mul_le_mul_of_nonneg_left hx hznn
    have hdiv : ‖z‖ * (‖graphShift A z p‖ / z.im) =
        (‖z‖ / z.im) * ‖graphShift A z p‖ := by field_simp
    rw [hdiv] at hx'
    have hcoef : (1 : ℝ) + ‖z‖ / z.im ≤ 1 + (1 + ‖z‖) / z.im := by
      gcongr
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hnn]

theorem pmapDissipative_shift_range_closed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hclosed : A.IsClosed) (hA : IsPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    IsClosed (Set.range (shiftedMap A z)) := by
  haveI : IsClosed (A.graph : Set (H × H)) := hclosed
  haveI : CompleteSpace (A.graph : Set (H × H)) := IsClosed.completeSpace_coe
  haveI : CompleteSpace A.graph := this
  let K : NNReal := ⟨1 + (1 + ‖z‖) / z.im, by positivity⟩
  have hanti : AntilipschitzWith K (graphShift A z) := by
    refine AddMonoidHomClass.antilipschitz_of_bound (graphShift A z) fun p => ?_
    exact pmapDissipative_graph_norm_le A hA z hz p
  have hrange := hanti.isClosed_range (graphShift A z).uniformContinuous
  rwa [range_graphShift] at hrange

def pmapDefectCoordinate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (y : H) : A.domain × ℂ →ₗ[ℂ] H where
  toFun p := (p.1 : H) + p.2 • y
  map_add' p q := by simp; module
  map_smul' c p := by simp; module

def pmapDefectOutput
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (y : H) : A.domain × ℂ →ₗ[ℂ] H where
  toFun p := A p.1 + p.2 • ((starRingEnd ℂ) z • y)
  map_add' p q := by
    change A (p.1 + q.1) + (p.2 + q.2) • ((starRingEnd ℂ) z • y) = _
    have hAadd : A (p.1 + q.1) = A p.1 + A q.1 := by
      exact A.toFun.map_add p.1 q.1
    rw [hAadd, add_smul]
    abel
  map_smul' c p := by
    change A (c • p.1) + (c * p.2) • ((starRingEnd ℂ) z • y) =
      c • (A p.1 + p.2 • ((starRingEnd ℂ) z • y))
    have hAsmul : A (c • p.1) = c • A p.1 := by
      exact A.toFun.map_smul c p.1
    rw [hAsmul, smul_add, mul_smul]

theorem pmapDefectCoordinate_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) {y : H} (hy : y ∉ A.domain) :
    Function.Injective (pmapDefectCoordinate A y) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro p hp
  change (p.1 : H) + p.2 • y = 0 at hp
  by_cases hc : p.2 = 0
  · apply Prod.ext
    · apply Subtype.ext
      simpa [hc] using hp
    · exact hc
  · exfalso
    apply hy
    have hxy : (-p.2) • y = (p.1 : H) := by
      linear_combination (norm := module) -hp
    have hneg : -p.2 ≠ 0 := neg_ne_zero.mpr hc
    have hyval : y = (-p.2)⁻¹ • (p.1 : H) := by
      rw [← hxy, ← mul_smul, inv_mul_cancel₀ hneg, one_smul]
    rw [hyval]
    exact A.domain.smul_mem _ p.1.property

def pmapDefectExtension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (y : H)
    (hcoord : Function.Injective (pmapDefectCoordinate A y)) : H →ₗ.[ℂ] H where
  domain := LinearMap.range (pmapDefectCoordinate A y)
  toFun := (pmapDefectOutput A z y).comp
    (LinearEquiv.ofInjective (pmapDefectCoordinate A y) hcoord).symm.toLinearMap

theorem pmapDissipative_orthogonal_not_mem_domain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) {y : H}
    (hy : y ∈ (LinearMap.range (shiftedMap A z))ᗮ) (hy0 : y ≠ 0) :
    y ∉ A.domain := by
  intro hydom
  let yd : A.domain := ⟨y, hydom⟩
  have hperp : ⟪shiftedMap A z yd, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ y).1 hy _ ⟨yd, rfl⟩
  have hperp' : ⟪y, shiftedMap A z yd⟫_ℂ = 0 := by
    have hc := congrArg (starRingEnd ℂ) hperp
    simpa [inner_conj_symm, mul_comm] using hc
  have him : (⟪y, A yd⟫_ℂ).im - z.im * ‖y‖ ^ 2 = 0 := by
    change ⟪y, A yd - z • y⟫_ℂ = 0 at hperp'
    rw [inner_sub_right, inner_smul_right] at hperp'
    have hi := congrArg Complex.im hperp'
    rw [inner_self_eq_norm_sq_to_K] at hi
    simpa [pow_two, Complex.mul_im] using hi
  have hsq : ‖y‖ ^ 2 = 0 := by
    nlinarith [hA yd, sq_nonneg ‖y‖]
  exact hy0 (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

@[simp] theorem pmapDefectExtension_coordinate_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (y : H)
    (hcoord : Function.Injective (pmapDefectCoordinate A y))
    (p : A.domain × ℂ) :
    pmapDefectExtension A z y hcoord
      ⟨pmapDefectCoordinate A y p, ⟨p, rfl⟩⟩ =
        pmapDefectOutput A z y p := by
  let e := LinearEquiv.ofInjective (pmapDefectCoordinate A y) hcoord
  change pmapDefectOutput A z y (e.symm (e p)) = pmapDefectOutput A z y p
  rw [e.symm_apply_apply]

theorem le_pmapDefectExtension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (y : H)
    (hcoord : Function.Injective (pmapDefectCoordinate A y)) :
    A ≤ pmapDefectExtension A z y hcoord := by
  let B := pmapDefectExtension A z y hcoord
  refine ⟨?_, ?_⟩
  · intro x hx
    exact ⟨((⟨x, hx⟩ : A.domain), 0), by simp [pmapDefectCoordinate]⟩
  · intro x v hxv
    let p : A.domain × ℂ := (x, 0)
    have hv : v =
        (⟨pmapDefectCoordinate A y p, ⟨p, rfl⟩⟩ : B.domain) := by
      apply Subtype.ext
      simpa [B, p, pmapDefectCoordinate] using hxv.symm
    rw [hv]
    simp [B, pmapDefectOutput, p]

theorem not_pmapDefectExtension_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) {y : H} (hy : y ∉ A.domain)
    (hcoord : Function.Injective (pmapDefectCoordinate A y)) :
    ¬pmapDefectExtension A z y hcoord ≤ A := by
  intro hle
  apply hy
  apply hle.1
  exact ⟨((0 : A.domain), 1), by simp [pmapDefectCoordinate]⟩

theorem pmapDefectExtension_isDissipative
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) {y : H}
    (hy : y ∈ (LinearMap.range (shiftedMap A z))ᗮ)
    (hcoord : Function.Injective (pmapDefectCoordinate A y)) :
    IsPMapDissipative (pmapDefectExtension A z y hcoord) := by
  intro v
  let e := LinearEquiv.ofInjective (pmapDefectCoordinate A y) hcoord
  let p : A.domain × ℂ := e.symm v
  have hv : (v : H) = pmapDefectCoordinate A y p := by
    have he := e.apply_symm_apply v
    exact (congrArg Subtype.val he).symm
  change (⟪(v : H), pmapDefectOutput A z y p⟫_ℂ).im ≤ 0
  rw [hv]
  have hperp : ⟪shiftedMap A z p.1, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ y).1 hy _ ⟨p.1, rfl⟩
  have hrel : ⟪A p.1, y⟫_ℂ =
      (starRingEnd ℂ) z * ⟪(p.1 : H), y⟫_ℂ := by
    change ⟪A p.1 - z • (p.1 : H), y⟫_ℂ = 0 at hperp
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hperp
    exact hperp
  have hrel' : ⟪y, A p.1⟫_ℂ = z * ⟪y, (p.1 : H)⟫_ℂ := by
    have hc := congrArg (starRingEnd ℂ) hrel
    simpa [inner_conj_symm, map_mul, mul_comm] using hc
  have hxy : ⟪y, (p.1 : H)⟫_ℂ = (starRingEnd ℂ) ⟪(p.1 : H), y⟫_ℂ :=
    (inner_conj_symm y (p.1 : H)).symm
  have hxy_re : (⟪y, (p.1 : H)⟫_ℂ).re = (⟪(p.1 : H), y⟫_ℂ).re :=
    calc
      _ = ((starRingEnd ℂ) ⟪(p.1 : H), y⟫_ℂ).re := congrArg Complex.re hxy
      _ = _ := rfl
  have hxy_im : (⟪y, (p.1 : H)⟫_ℂ).im = -(⟪(p.1 : H), y⟫_ℂ).im :=
    calc
      _ = ((starRingEnd ℂ) ⟪(p.1 : H), y⟫_ℂ).im := congrArg Complex.im hxy
      _ = _ := rfl
  have hformula :
      (⟪pmapDefectCoordinate A y p, pmapDefectOutput A z y p⟫_ℂ).im =
        (⟪(p.1 : H), A p.1⟫_ℂ).im -
          Complex.normSq p.2 * z.im * ‖y‖ ^ 2 := by
    change
      (⟪(p.1 : H) + p.2 • y,
        A p.1 + p.2 • ((starRingEnd ℂ) z • y)⟫_ℂ).im = _
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    rw [hrel', inner_self_eq_norm_sq_to_K]
    simp only [starRingEnd_apply]
    simp [Complex.add_im, Complex.mul_im, Complex.normSq_apply, pow_two]
    rw [hxy_re, hxy_im]
    ring
  rw [hformula]
  have hnormSq : 0 ≤ Complex.normSq p.2 := Complex.normSq_nonneg _
  have hnormy : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hprod : 0 ≤ Complex.normSq p.2 * z.im * ‖y‖ ^ 2 :=
    mul_nonneg (mul_nonneg hnormSq hz.le) hnormy
  linarith [hA p.1]

theorem closedMaximalPMapDissipative_shift_range_orthogonal_eq_bot
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsClosedMaximalPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    (LinearMap.range (shiftedMap A z))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  by_contra hy0
  have hydom : y ∉ A.domain :=
    pmapDissipative_orthogonal_not_mem_domain A hA.2.1 z hz hy hy0
  let hcoord : Function.Injective (pmapDefectCoordinate A y) :=
    pmapDefectCoordinate_injective A hydom
  let B := pmapDefectExtension A z y hcoord
  have hAB : A ≤ B := le_pmapDefectExtension A z y hcoord
  have hBdiss : IsPMapDissipative B :=
    pmapDefectExtension_isDissipative A hA.2.1 z hz hy hcoord
  have hBA : B ≤ A := hA.2.2 B hBdiss hAB
  exact not_pmapDefectExtension_le A z hydom hcoord hBA

theorem closedMaximalPMapDissipative_shift_surjective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsClosedMaximalPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) :
    Function.Surjective (shiftedMap A z) := by
  have hclosed : IsClosed
      ((LinearMap.range (shiftedMap A z) : Submodule ℂ H) : Set H) :=
    pmapDissipative_shift_range_closed A hA.1 hA.2.1 z hz
  have htop := Submodule.topologicalClosure_eq_top_iff.2
    (closedMaximalPMapDissipative_shift_range_orthogonal_eq_bot A hA z hz)
  have hself : (LinearMap.range (shiftedMap A z)).topologicalClosure =
      LinearMap.range (shiftedMap A z) :=
    SetLike.coe_injective hclosed.closure_eq
  rw [hself] at htop
  exact LinearMap.range_eq_top.1 htop

def HasUniquePMapShiftedResponse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (source : H) : Prop :=
  ∃! x : A.domain,
    shiftedMap A z x = source ∧ (x : H) ≠ 0 ∧
      |z.im| * ‖(x : H)‖ ≤ ‖source‖

theorem closedMaximalPMapDissipative_hasUniqueShiftedResponse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsClosedMaximalPMapDissipative A)
    (z : ℂ) (hz : 0 < z.im) (source : H) (hsource : source ≠ 0) :
    HasUniquePMapShiftedResponse A z source := by
  obtain ⟨x, hx⟩ := closedMaximalPMapDissipative_shift_surjective A hA z hz source
  have hx0 : (x : H) ≠ 0 := by
    intro hzero
    apply hsource
    have hxsub : x = 0 := Subtype.ext hzero
    rw [← hx, hxsub, map_zero]
  have hbound : |z.im| * ‖(x : H)‖ ≤ ‖source‖ := by
    rw [abs_of_pos hz]
    simpa [hx] using pmapDissipative_shift_norm_lower A hA.2.1 z x
  refine ⟨x, ⟨hx, hx0, hbound⟩, ?_⟩
  intro y hy
  exact pmapDissipative_shift_injective A hA.2.1 z hz (hy.1.trans hx.symm)

theorem pmapAntidissipative_shift_norm_lower
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapAntidissipative A)
    (z : ℂ) (x : A.domain) :
    (-z.im) * ‖(x : H)‖ ≤ ‖shiftedMap A z x‖ := by
  by_cases hx : (x : H) = 0
  · simp [hx]
  have hnorm : 0 < ‖(x : H)‖ := norm_pos_iff.mpr hx
  have him :
      (⟪(x : H), shiftedMap A z x⟫_ℂ).im =
        (⟪(x : H), A x⟫_ℂ).im - z.im * ‖(x : H)‖ ^ 2 := by
    simp [shiftedMap_apply, pow_two, Complex.mul_im]
  have hraw :
      (-z.im) * ‖(x : H)‖ ^ 2 ≤ (⟪(x : H), shiftedMap A z x⟫_ℂ).im := by
    rw [him]
    linarith [hA x]
  have habs :
      (⟪(x : H), shiftedMap A z x⟫_ℂ).im ≤
        |(⟪(x : H), shiftedMap A z x⟫_ℂ).im| := le_abs_self _
  have himnorm :
      |(⟪(x : H), shiftedMap A z x⟫_ℂ).im| ≤
        ‖⟪(x : H), shiftedMap A z x⟫_ℂ‖ :=
    Complex.abs_im_le_norm _
  have hcs :
      ‖⟪(x : H), shiftedMap A z x⟫_ℂ‖ ≤
        ‖(x : H)‖ * ‖shiftedMap A z x‖ := norm_inner_le_norm _ _
  have htotal : (-z.im) * ‖(x : H)‖ ^ 2 ≤
      ‖(x : H)‖ * ‖shiftedMap A z x‖ :=
    hraw.trans (habs.trans (himnorm.trans hcs))
  nlinarith

theorem pmapAntidissipative_shift_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    Function.Injective (shiftedMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hzero : ‖shiftedMap A z x‖ = 0 := by rw [hx, norm_zero]
  have hbound := pmapAntidissipative_shift_norm_lower A hA z x
  rw [hzero] at hbound
  have hnorm : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
  exact Subtype.ext (norm_eq_zero.mp hnorm)

theorem pmapAntidissipative_graph_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) (p : A.graph) :
    ‖p‖ ≤ (1 + (1 + ‖z‖) / (-z.im)) * ‖graphShift A z p‖ := by
  obtain ⟨y, hy1, hy2⟩ := A.mem_graph_iff.1 p.2
  have hdelta : 0 < -z.im := neg_pos.mpr hz
  have hv : graphShift A z p = A y - z • (y : H) := by
    rw [graphShift_apply, hy1, hy2]
  have hlow := pmapAntidissipative_shift_norm_lower A hA z y
  rw [shiftedMap_apply, ← hv] at hlow
  have hx : ‖(p : H × H).1‖ ≤ ‖graphShift A z p‖ / (-z.im) := by
    rw [← hy1, le_div_iff₀ hdelta, mul_comm]
    exact hlow
  have hy : ‖(p : H × H).2‖ ≤
      ‖graphShift A z p‖ + ‖z‖ * ‖(p : H × H).1‖ := by
    have hsplit : (p : H × H).2 = graphShift A z p + z • (p : H × H).1 := by
      rw [graphShift_apply]
      abel
    calc
      ‖(p : H × H).2‖ = ‖graphShift A z p + z • (p : H × H).1‖ := by rw [← hsplit]
      _ ≤ ‖graphShift A z p‖ + ‖z • (p : H × H).1‖ := norm_add_le _ _
      _ = ‖graphShift A z p‖ + ‖z‖ * ‖(p : H × H).1‖ := by rw [norm_smul]
  have hnn : 0 ≤ ‖graphShift A z p‖ := norm_nonneg _
  have hznn : 0 ≤ ‖z‖ := norm_nonneg _
  rw [show ‖p‖ = ‖(p : H × H)‖ from rfl, Prod.norm_def]
  refine max_le ?_ ?_
  · refine le_trans hx ?_
    rw [div_le_iff₀ hdelta]
    have hkey : (1 + ‖z‖) / (-z.im) * (-z.im) = 1 + ‖z‖ :=
      div_mul_cancel₀ _ hdelta.ne'
    nlinarith [hnn, hdelta.le, hznn, hkey,
      mul_nonneg hnn hdelta.le, mul_nonneg hnn hznn]
  · refine le_trans hy ?_
    have hx' : ‖z‖ * ‖(p : H × H).1‖ ≤
        ‖z‖ * (‖graphShift A z p‖ / (-z.im)) :=
      mul_le_mul_of_nonneg_left hx hznn
    have hdiv : ‖z‖ * (‖graphShift A z p‖ / (-z.im)) =
        (‖z‖ / (-z.im)) * ‖graphShift A z p‖ := by field_simp
    rw [hdiv] at hx'
    have hcoef : (1 : ℝ) + ‖z‖ / (-z.im) ≤
        1 + (1 + ‖z‖) / (-z.im) := by
      gcongr
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hnn]

theorem pmapAntidissipative_shift_range_closed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hclosed : A.IsClosed) (hA : IsPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    IsClosed (Set.range (shiftedMap A z)) := by
  haveI : IsClosed (A.graph : Set (H × H)) := hclosed
  haveI : CompleteSpace (A.graph : Set (H × H)) := IsClosed.completeSpace_coe
  haveI : CompleteSpace A.graph := this
  have hdelta : 0 < -z.im := neg_pos.mpr hz
  let K : NNReal := ⟨1 + (1 + ‖z‖) / (-z.im), by positivity⟩
  have hanti : AntilipschitzWith K (graphShift A z) := by
    refine AddMonoidHomClass.antilipschitz_of_bound (graphShift A z) fun p => ?_
    exact pmapAntidissipative_graph_norm_le A hA z hz p
  have hrange := hanti.isClosed_range (graphShift A z).uniformContinuous
  rwa [range_graphShift] at hrange

theorem pmapAntidissipative_orthogonal_not_mem_domain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) {y : H}
    (hy : y ∈ (LinearMap.range (shiftedMap A z))ᗮ) (hy0 : y ≠ 0) :
    y ∉ A.domain := by
  intro hydom
  let yd : A.domain := ⟨y, hydom⟩
  have hperp : ⟪shiftedMap A z yd, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ y).1 hy _ ⟨yd, rfl⟩
  have hperp' : ⟪y, shiftedMap A z yd⟫_ℂ = 0 := by
    have hc := congrArg (starRingEnd ℂ) hperp
    simpa [inner_conj_symm, mul_comm] using hc
  have him : (⟪y, A yd⟫_ℂ).im - z.im * ‖y‖ ^ 2 = 0 := by
    change ⟪y, A yd - z • y⟫_ℂ = 0 at hperp'
    rw [inner_sub_right, inner_smul_right] at hperp'
    have hi := congrArg Complex.im hperp'
    rw [inner_self_eq_norm_sq_to_K] at hi
    simpa [pow_two, Complex.mul_im] using hi
  have hsq : ‖y‖ ^ 2 = 0 := by
    nlinarith [hA yd, sq_nonneg ‖y‖]
  exact hy0 (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

theorem pmapDefectExtension_isAntidissipative
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) {y : H}
    (hy : y ∈ (LinearMap.range (shiftedMap A z))ᗮ)
    (hcoord : Function.Injective (pmapDefectCoordinate A y)) :
    IsPMapAntidissipative (pmapDefectExtension A z y hcoord) := by
  intro v
  let e := LinearEquiv.ofInjective (pmapDefectCoordinate A y) hcoord
  let p : A.domain × ℂ := e.symm v
  have hv : (v : H) = pmapDefectCoordinate A y p := by
    have he := e.apply_symm_apply v
    exact (congrArg Subtype.val he).symm
  change 0 ≤ (⟪(v : H), pmapDefectOutput A z y p⟫_ℂ).im
  rw [hv]
  have hperp : ⟪shiftedMap A z p.1, y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ y).1 hy _ ⟨p.1, rfl⟩
  have hrel : ⟪A p.1, y⟫_ℂ =
      (starRingEnd ℂ) z * ⟪(p.1 : H), y⟫_ℂ := by
    change ⟪A p.1 - z • (p.1 : H), y⟫_ℂ = 0 at hperp
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hperp
    exact hperp
  have hrel' : ⟪y, A p.1⟫_ℂ = z * ⟪y, (p.1 : H)⟫_ℂ := by
    have hc := congrArg (starRingEnd ℂ) hrel
    simpa [inner_conj_symm, map_mul, mul_comm] using hc
  have hxy : ⟪y, (p.1 : H)⟫_ℂ = (starRingEnd ℂ) ⟪(p.1 : H), y⟫_ℂ :=
    (inner_conj_symm y (p.1 : H)).symm
  have hxy_re : (⟪y, (p.1 : H)⟫_ℂ).re = (⟪(p.1 : H), y⟫_ℂ).re :=
    calc
      _ = ((starRingEnd ℂ) ⟪(p.1 : H), y⟫_ℂ).re := congrArg Complex.re hxy
      _ = _ := rfl
  have hxy_im : (⟪y, (p.1 : H)⟫_ℂ).im = -(⟪(p.1 : H), y⟫_ℂ).im :=
    calc
      _ = ((starRingEnd ℂ) ⟪(p.1 : H), y⟫_ℂ).im := congrArg Complex.im hxy
      _ = _ := rfl
  have hformula :
      (⟪pmapDefectCoordinate A y p, pmapDefectOutput A z y p⟫_ℂ).im =
        (⟪(p.1 : H), A p.1⟫_ℂ).im -
          Complex.normSq p.2 * z.im * ‖y‖ ^ 2 := by
    change
      (⟪(p.1 : H) + p.2 • y,
        A p.1 + p.2 • ((starRingEnd ℂ) z • y)⟫_ℂ).im = _
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    rw [hrel', inner_self_eq_norm_sq_to_K]
    simp only [starRingEnd_apply]
    simp [Complex.add_im, Complex.mul_im, Complex.normSq_apply, pow_two]
    rw [hxy_re, hxy_im]
    ring
  rw [hformula]
  have hnormSq : 0 ≤ Complex.normSq p.2 := Complex.normSq_nonneg _
  have hnormy : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hprod : Complex.normSq p.2 * z.im * ‖y‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hnormSq hz.le) hnormy
  linarith [hA p.1]

theorem closedMaximalPMapAntidissipative_shift_range_orthogonal_eq_bot
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (hA : IsClosedMaximalPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    (LinearMap.range (shiftedMap A z))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  by_contra hy0
  have hydom : y ∉ A.domain :=
    pmapAntidissipative_orthogonal_not_mem_domain A hA.2.1 z hz hy hy0
  let hcoord : Function.Injective (pmapDefectCoordinate A y) :=
    pmapDefectCoordinate_injective A hydom
  let B := pmapDefectExtension A z y hcoord
  have hAB : A ≤ B := le_pmapDefectExtension A z y hcoord
  have hBanti : IsPMapAntidissipative B :=
    pmapDefectExtension_isAntidissipative A hA.2.1 z hz hy hcoord
  have hBA : B ≤ A := hA.2.2 B hBanti hAB
  exact not_pmapDefectExtension_le A z hydom hcoord hBA

theorem closedMaximalPMapAntidissipative_shift_surjective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsClosedMaximalPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) :
    Function.Surjective (shiftedMap A z) := by
  have hclosed : IsClosed
      ((LinearMap.range (shiftedMap A z) : Submodule ℂ H) : Set H) :=
    pmapAntidissipative_shift_range_closed A hA.1 hA.2.1 z hz
  have htop := Submodule.topologicalClosure_eq_top_iff.2
    (closedMaximalPMapAntidissipative_shift_range_orthogonal_eq_bot A hA z hz)
  have hself : (LinearMap.range (shiftedMap A z)).topologicalClosure =
      LinearMap.range (shiftedMap A z) :=
    SetLike.coe_injective hclosed.closure_eq
  rw [hself] at htop
  exact LinearMap.range_eq_top.1 htop

theorem closedMaximalPMapAntidissipative_hasUniqueShiftedResponse
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsClosedMaximalPMapAntidissipative A)
    (z : ℂ) (hz : z.im < 0) (source : H) (hsource : source ≠ 0) :
    HasUniquePMapShiftedResponse A z source := by
  obtain ⟨x, hx⟩ := closedMaximalPMapAntidissipative_shift_surjective A hA z hz source
  have hx0 : (x : H) ≠ 0 := by
    intro hzero
    apply hsource
    have hxsub : x = 0 := Subtype.ext hzero
    rw [← hx, hxsub, map_zero]
  have hbound : |z.im| * ‖(x : H)‖ ≤ ‖source‖ := by
    rw [abs_of_neg hz]
    simpa [hx] using pmapAntidissipative_shift_norm_lower A hA.2.1 z x
  refine ⟨x, ⟨hx, hx0, hbound⟩, ?_⟩
  intro y hy
  exact pmapAntidissipative_shift_injective A hA.2.1 z hz (hy.1.trans hx.symm)

/-- Both exact sources on a reflected tilted Xi pair respond in the matching maximal passive
half-plane resolvents. -/
def D4HBUnboundedMaximalDissipativeReflectedSourcePairResponds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (upper lower : H →ₗ.[ℂ] H) (amplitude mixed anti : ℂ)
    (profile : H) (q : XiZeroCopy) : Prop :=
  let qstar := xiZeroCopyConjEquiv q
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let lambdaStar :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint qstar)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  let sourceStar := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile qstar
  (0 < lambda.im ∧
      HasUniquePMapShiftedResponse upper lambda source ∧
      HasUniquePMapShiftedResponse lower lambdaStar sourceStar) ∨
    (lambda.im < 0 ∧
      HasUniquePMapShiftedResponse lower lambda source ∧
      HasUniquePMapShiftedResponse upper lambdaStar sourceStar)

theorem d4ThetaReducedSecondOrderChiralTeukolskySource_unboundedMaximalDissipative_reflectedPair_responds
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (upper lower : H →ₗ.[ℂ] H)
    (hupper : IsClosedMaximalPMapDissipative upper)
    (hlower : IsClosedMaximalPMapAntidissipative lower)
    {amplitude : ℂ} (ha : amplitude ≠ 0) (mixed anti : ℂ)
    (profile : H) (hprofile : profile ≠ 0)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    D4HBUnboundedMaximalDissipativeReflectedSourcePairResponds
      upper lower amplitude mixed anti profile q := by
  let qstar := xiZeroCopyConjEquiv q
  let lambda := d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)
  let lambdaStar :=
    d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint qstar)
  let source := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile q
  let sourceStar := d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector
    amplitude mixed anti profile qstar
  have htiltStar : (qstar.1 : ℂ).re ≠ 1 / 2 := by
    exact xiZeroCopyConjEquiv_tilt q htilt
  have hlambda : lambda.im ≠ 0 := by
    exact d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_xi_im_ne_zero_of_tilt q htilt
  have hreflect : lambdaStar.im = -lambda.im := by
    exact d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_copyConj_im q
  have hsource : source ≠ 0 := by
    exact d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti 0 profile hprofile q htilt
  have hsourceStar : sourceStar ≠ 0 := by
    exact d4ThetaReducedSecondOrderChiralTeukolskyPrincipalSourceVector_ne_zero
      ha mixed anti 0 profile hprofile qstar htiltStar
  change (0 < lambda.im ∧
      HasUniquePMapShiftedResponse upper lambda source ∧
      HasUniquePMapShiftedResponse lower lambdaStar sourceStar) ∨
    (lambda.im < 0 ∧
      HasUniquePMapShiftedResponse lower lambda source ∧
      HasUniquePMapShiftedResponse upper lambdaStar sourceStar)
  rcases lt_or_gt_of_ne hlambda with hneg | hpos
  · right
    refine ⟨hneg,
      closedMaximalPMapAntidissipative_hasUniqueShiftedResponse
        lower hlower lambda hneg source hsource, ?_⟩
    apply closedMaximalPMapDissipative_hasUniqueShiftedResponse
      upper hupper lambdaStar
    · linarith
    · exact hsourceStar
  · left
    refine ⟨hpos,
      closedMaximalPMapDissipative_hasUniqueShiftedResponse
        upper hupper lambda hpos source hsource, ?_⟩
    apply closedMaximalPMapAntidissipative_hasUniqueShiftedResponse
      lower hlower lambdaStar
    · linarith
    · exact hsourceStar

/-- Closed route-class certificate: unbounded closed order-maximal passive dynamics cannot
extinguish either exact doubled-weight source on a hypothetical off-wall Xi orbit. -/
def D4HBUnboundedMaximalDissipativeReflectedForcingExclusionRouteKilled : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (upper lower : H →ₗ.[ℂ] H)
    (amplitude mixed anti : ℂ) (profile : H),
      IsClosedMaximalPMapDissipative upper →
      IsClosedMaximalPMapAntidissipative lower →
      amplitude ≠ 0 → profile ≠ 0 →
      ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
        D4HBUnboundedMaximalDissipativeReflectedSourcePairResponds
          upper lower amplitude mixed anti profile q

theorem d4HBUnboundedMaximalDissipativeReflectedForcingExclusionRouteKilled :
    D4HBUnboundedMaximalDissipativeReflectedForcingExclusionRouteKilled := by
  intro H _ _ _ upper lower amplitude mixed anti profile
    hupper hlower ha hprofile q htilt
  exact
    d4ThetaReducedSecondOrderChiralTeukolskySource_unboundedMaximalDissipative_reflectedPair_responds
      upper lower hupper hlower ha mixed anti profile hprofile q htilt

end

end RHTower
