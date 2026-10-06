import GaloisForLFunctions.HTGeometry.DeterminantLineSquareStokes

/-!
# Edge holonomy of the determinant line

Fix a polarization projection `Q`.  At each orthogonal projection `P` with an admissible frame,
`detCoord Q P u = det(gauge(ref, u))` trivializes the dual determinant line; it obeys the cocycle
law `detCoord(u') = detCoord(u) · det(gauge(u, u'))`.

For a path `τ ↦ P₊ + e(τ)` and a smooth admissible lift on an open neighbourhood of `[a, b]`,
the edge factor `exp ∫ₐᵇ α · detCoord(w(a)) / detCoord(w(b))` is the parallel transport of the
dual determinant line expressed in determinant coordinates.

* `edgeFactor_eq`: edge factors do not depend on the lift (gauge law and Jacobi's formula).
* `edgeFactor_restrict_mul`, `segHol_eq_prod`: multiplicativity under subdivision.
* `edgeHol`, `edgeHol_eq`: the edge holonomy, computed by every uniform subdivision fine enough to
  carry lifts; `exists_fineLevel` (Lebesgue number) and `edgeHol_const` (constant paths).
-/

set_option autoImplicit false

open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Determinant coordinates of admissible frames -/

section DetCoord

variable {Q P : H →L[ℂ] H}

open Classical in
/-- A reference admissible frame of `P` relative to `Q` (when one exists). -/
def refFrame (Q P : H →L[ℂ] H) : H →L[ℂ] H :=
  if h : ∃ u, IsAdmissibleFrame Q u P then h.choose else Q

theorem refFrame_spec (h : ∃ u, IsAdmissibleFrame Q u P) :
    IsAdmissibleFrame Q (refFrame Q P) P := by
  classical
  rw [refFrame, dif_pos h]; exact h.choose_spec

/-- The determinant coordinate of an admissible frame: `det` of its gauge from the reference
frame.  It is a trivialization of the dual determinant line at `P`. -/
def detCoord (Q P u : H →L[ℂ] H) : ℂ := finiteRankDet (frameGauge Q (refFrame Q P) u)

theorem finiteDimensional_range_frameGauge (hQ : IsStarProjection Q) {u u' : H →L[ℂ] H}
    (hu : IsAdmissibleFrame Q u P) (hu' : IsAdmissibleFrame Q u' P) :
    FiniteDimensional ℂ
      (LinearMap.range (((frameGauge Q u u' : H →L[ℂ] H) : H →ₗ[ℂ] H) - 1)) := by
  obtain ⟨V, hV, hVm⟩ := hu.2.2
  obtain ⟨V', hV', hV'm⟩ := hu'.2.2
  haveI := hV; haveI := hV'
  refine Submodule.finiteDimensional_of_le (S₂ := V ⊔ V') ?_
  rintro _ ⟨x, rfl⟩
  have heq := frameGauge_sub_one_eq hQ hu.1 hu'.1
  have : (((frameGauge Q u u' : H →L[ℂ] H) : H →ₗ[ℂ] H) - 1) x =
      (frameGauge Q u u' - 1) x := by simp
  rw [this, heq, sub_apply]
  exact (V ⊔ V').sub_mem (Submodule.mem_sup_right (hV'm x)) (Submodule.mem_sup_left (hVm _))

/-- **Cocycle law of determinant coordinates**:
`detCoord(u') = detCoord(u) · det(gauge(u, u'))`. -/
theorem detCoord_mul (hQ : IsStarProjection Q) {u u' : H →L[ℂ] H}
    (hu : IsAdmissibleFrame Q u P) (hu' : IsAdmissibleFrame Q u' P) :
    detCoord Q P u' = detCoord Q P u * finiteRankDet (frameGauge Q u u') := by
  have hr := refFrame_spec ⟨u, hu⟩
  unfold detCoord
  rw [← frameGauge_mul hQ hr.1 hu.1 hu'.1, finiteRankDet_mul
    (finiteDimensional_range_frameGauge hQ hr hu) (finiteDimensional_range_frameGauge hQ hu hu')]

theorem detCoord_ne_zero (hQ : IsStarProjection Q) {u : H →L[ℂ] H}
    (hu : IsAdmissibleFrame Q u P) : detCoord Q P u ≠ 0 := by
  have hr := refFrame_spec ⟨u, hu⟩
  exact finiteRankDet_ne_zero (isUnit_frameGauge hQ hr.1 hu.1)
    (finiteDimensional_range_frameGauge hQ hr hu)

end DetCoord

/-! ## Lifts of paths and edge factors -/

section PathLift

variable {Q Pp : H →L[ℂ] H} {e : ℝ → SLSpace H}

/-- An admissible `C²` lift of the path `τ ↦ P₊ + e(τ)` on an open neighbourhood of `[a, b]`. -/
structure PathLift (Q Pp : H →L[ℂ] H) (e : ℝ → SLSpace H) (a b : ℝ) where
  /-- the open domain of the lift -/
  U : Set ℝ
  isOpen_U : IsOpen U
  Icc_subset : Set.Icc a b ⊆ U
  /-- the Hilbert–Schmidt displacement `w − Q` of the lifted frames -/
  Y : ℝ → HSpace ℂ H
  /-- the finite-dimensional range of the `ran Q`-defects -/
  V : Submodule ℂ H
  finiteDimensional_V : FiniteDimensional ℂ V
  smooth : ContDiffOn ℝ 2 Y U
  frame : ∀ r ∈ U, IsFrameOf Q (frameOf Q (Y r)) (Pp + (e r).op)
  admissible : ∀ r ∈ U, Y r ∈ admissibleSubspace Q V

namespace PathLift

variable {a b : ℝ} (L : PathLift Q Pp e a b)

variable (hQ : IsStarProjection Q)
include hQ

theorem isAdmissibleFrame {r : ℝ} (hr : r ∈ L.U) :
    IsAdmissibleFrame Q (frameOf Q (L.Y r)) (Pp + (e r).op) := by
  refine ⟨L.frame r hr, ?_, L.V, L.finiteDimensional_V, fun x => ?_⟩
  · simpa [frameOf] using (L.Y r).isHS
  · have hQQ : Q (Q x) = Q x := by rw [← mul_apply_eq_comp, hQ.isIdempotentElem.eq]
    have : (Q * frameOf Q (L.Y r) - Q) x = Q ((L.Y r).op x) := by
      simp [frameOf, mul_add, sub_apply, hQQ]
    rw [this]; exact (L.admissible r hr).1 x

omit hQ in
theorem hasDerivAt {r : ℝ} (hr : r ∈ L.U) : HasDerivAt L.Y (deriv L.Y r) r :=
  ((L.smooth.contDiffAt (L.isOpen_U.mem_nhds hr)).differentiableAt (by norm_num)).hasDerivAt

omit hQ in
theorem contDiffOn_deriv : ContDiffOn ℝ 1 (deriv L.Y) L.U :=
  L.smooth.deriv_of_isOpen L.isOpen_U (by norm_num)

omit hQ in
theorem hasDerivAt_deriv {r : ℝ} (hr : r ∈ L.U) :
    HasDerivAt (deriv L.Y) (deriv (deriv L.Y) r) r :=
  ((L.contDiffOn_deriv.contDiffAt (L.isOpen_U.mem_nhds hr)).differentiableAt
    (by norm_num)).hasDerivAt

/-- The connection form along the lift is continuous on its domain. -/
theorem continuousOn_conn :
    ContinuousOn (fun r => detConnection Q (L.Y r) (deriv L.Y r)) L.U := by
  haveI := L.finiteDimensional_V
  intro r hr
  have hev : ∀ᶠ s in nhds r, s ∈ L.U := L.isOpen_U.mem_nhds hr
  have hS := isClosed_admissibleSubspace (Q := Q) (V := L.V)
  have hY' : ∀ s ∈ L.U, deriv L.Y s ∈ admissibleSubspace Q L.V := fun s hs =>
    hasDerivAt_mem_of_eventually_mem hS (L.hasDerivAt hs)
      (Filter.eventually_of_mem (L.isOpen_U.mem_nhds hs) fun t ht => L.admissible t ht)
  have hY'' : deriv (deriv L.Y) r ∈ admissibleSubspace Q L.V :=
    hasDerivAt_mem_of_eventually_mem hS (L.hasDerivAt_deriv hr) (hev.mono fun t ht => hY' t ht)
  exact (hasDerivAt_detConnection (V := L.V) hQ.isSelfAdjoint (L.hasDerivAt hr)
    (L.hasDerivAt_deriv hr) (L.frame r hr).2.1 (hev.mono fun t ht => (hY' t ht).1)
    hY''.1).continuousAt.continuousWithinAt

end PathLift

/-- The edge factor of a lifted segment:
`exp ∫ₐᵇ α(w)[ẇ] · detCoord(w(a)) / detCoord(w(b))`. -/
def edgeFactor {a b : ℝ} (L : PathLift Q Pp e a b) : ℂ :=
  Complex.exp (∫ r in a..b, detConnection Q (L.Y r) (deriv L.Y r)) *
    detCoord Q (Pp + (e a).op) (frameOf Q (L.Y a)) /
      detCoord Q (Pp + (e b).op) (frameOf Q (L.Y b))

/-- Restriction of a lift to a subinterval of its domain. -/
def PathLift.restrict {a b : ℝ} (L : PathLift Q Pp e a b) (a' b' : ℝ)
    (h : Set.Icc a' b' ⊆ L.U) : PathLift Q Pp e a' b' :=
  { L with Icc_subset := h }

@[simp] theorem PathLift.restrict_Y {a b : ℝ} (L : PathLift Q Pp e a b) (a' b' : ℝ)
    (h : Set.Icc a' b' ⊆ L.U) : (L.restrict a' b' h).Y = L.Y := rfl

/-- **Lift independence of edge factors.** -/
theorem edgeFactor_eq (hQ : IsStarProjection Q) {a b : ℝ} (hab : a ≤ b)
    (L₁ L₂ : PathLift Q Pp e a b) : edgeFactor L₁ = edgeFactor L₂ := by
  haveI := L₁.finiteDimensional_V
  haveI := L₂.finiteDimensional_V
  set U := L₁.U ∩ L₂.U
  have hU : IsOpen U := L₁.isOpen_U.inter L₂.isOpen_U
  have hIcc : Set.Icc a b ⊆ U := fun r hr => ⟨L₁.Icc_subset hr, L₂.Icc_subset hr⟩
  have key := finiteRankDet_frameGauge_eq (V₁ := L₁.V) (V₂ := L₂.V)
    (P := fun r => Pp + (e r).op) hQ hab hU hIcc
    (fun r hr => L₁.hasDerivAt hr.1) (fun r hr => L₂.hasDerivAt hr.2)
    (fun r hr => L₁.hasDerivAt_deriv hr.1) (fun r hr => L₂.hasDerivAt_deriv hr.2)
    (fun r hr => L₁.frame r hr.1) (fun r hr => L₂.frame r hr.2)
    (fun r hr => L₁.admissible r hr.1) (fun r hr => L₂.admissible r hr.2)
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hc := fun r (hr : r ∈ Set.Icc a b) =>
    detCoord_mul hQ ((L₁.isAdmissibleFrame hQ) (L₁.Icc_subset hr))
      ((L₂.isAdmissibleFrame hQ) (L₂.Icc_subset hr))
  have hn₁ := fun r (hr : r ∈ Set.Icc a b) =>
    detCoord_ne_zero hQ ((L₁.isAdmissibleFrame hQ) (L₁.Icc_subset hr))
  have hg := fun r (hr : r ∈ Set.Icc a b) =>
    finiteRankDet_ne_zero (isUnit_frameGauge hQ (L₁.frame r (L₁.Icc_subset hr))
      (L₂.frame r (L₂.Icc_subset hr)))
      (finiteDimensional_range_frameGauge hQ ((L₁.isAdmissibleFrame hQ) (L₁.Icc_subset hr))
        ((L₂.isAdmissibleFrame hQ) (L₂.Icc_subset hr)))
  have hi₁ : IntervalIntegrable (fun r => detConnection Q (L₁.Y r) (deriv L₁.Y r))
      MeasureTheory.volume a b :=
    ((L₁.continuousOn_conn hQ).mono (by rw [Set.uIcc_of_le hab]; exact L₁.Icc_subset)
      ).intervalIntegrable
  have hi₂ : IntervalIntegrable (fun r => detConnection Q (L₂.Y r) (deriv L₂.Y r))
      MeasureTheory.volume a b :=
    ((L₂.continuousOn_conn hQ).mono (by rw [Set.uIcc_of_le hab]; exact L₂.Icc_subset)
      ).intervalIntegrable
  have hsplit := intervalIntegral.integral_sub hi₂ hi₁
  unfold edgeFactor
  rw [hc a ha, hc b hb]
  set I := ∫ r in a..b, (detConnection Q (L₂.Y r) (deriv L₂.Y r) -
    detConnection Q (L₁.Y r) (deriv L₁.Y r))
  have hI : (∫ r in a..b, detConnection Q (L₂.Y r) (deriv L₂.Y r)) =
      (∫ r in a..b, detConnection Q (L₁.Y r) (deriv L₁.Y r)) + I := by
    rw [hsplit]; ring
  rw [hI, Complex.exp_add, key]
  have := hn₁ a ha; have := hn₁ b hb; have := hg a ha
  have := Complex.exp_ne_zero I
  field_simp

/-- **Additivity of edge factors** under subdivision of a lifted segment. -/
theorem edgeFactor_restrict_mul (hQ : IsStarProjection Q) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (L : PathLift Q Pp e a c) :
    edgeFactor (L.restrict a b (fun _ hr => L.Icc_subset ⟨hr.1, hr.2.trans hbc⟩)) *
        edgeFactor (L.restrict b c (fun _ hr => L.Icc_subset ⟨hab.trans hr.1, hr.2⟩)) =
      edgeFactor L := by
  have hac : a ≤ c := hab.trans hbc
  have hint : ∀ x y, a ≤ x → y ≤ c → x ≤ y → IntervalIntegrable
      (fun r => detConnection Q (L.Y r) (deriv L.Y r)) MeasureTheory.volume x y :=
    fun x y hx hy hxy => ((L.continuousOn_conn hQ).mono (by
      rw [Set.uIcc_of_le hxy]
      exact fun r hr => L.Icc_subset ⟨hx.trans hr.1, hr.2.trans hy⟩)).intervalIntegrable
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hint a b le_rfl hbc hab)
    (hint b c hab le_rfl hbc)
  have hb : detCoord Q (Pp + (e b).op) (frameOf Q (L.Y b)) ≠ 0 :=
    detCoord_ne_zero hQ ((L.isAdmissibleFrame hQ) (L.Icc_subset ⟨hab, hbc⟩))
  unfold edgeFactor
  simp only [PathLift.restrict_Y]
  rw [← hsum, Complex.exp_add]
  field_simp

end PathLift


/-! ## Existence of smooth local lifts -/

section LocalLift

variable {Q Pp : H →L[ℂ] H} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Smooth local lifts exist around every point with an admissible frame.**  For a smooth
family `x ↦ P₊ + F(x)` of orthogonal projections and an admissible frame at `x₀`, there is an open
neighbourhood of `x₀` carrying a smooth admissible lift with defects in a fixed
finite-dimensional subspace. -/
theorem exists_local_lift (hQ : IsStarProjection Q) {F : X → SLSpace H} (hF : ContDiff ℝ ⊤ F)
    (hproj : ∀ x, IsStarProjection (Pp + (F x).op)) {x₀ : X} {u₀ : H →L[ℂ] H}
    (hu₀ : IsAdmissibleFrame Q u₀ (Pp + (F x₀).op)) :
    ∃ (U : Set X) (Y : X → HSpace ℂ H) (V : Submodule ℂ H), IsOpen U ∧ x₀ ∈ U ∧
      FiniteDimensional ℂ V ∧ ContDiffOn ℝ ⊤ Y U ∧
      (∀ x ∈ U, IsFrameOf Q (frameOf Q (Y x)) (Pp + (F x).op)) ∧
      (∀ x ∈ U, Y x ∈ admissibleSubspace Q V) := by
  obtain ⟨hfr, hY₀, V, hV, hVm⟩ := hu₀
  set Y₀ : HSpace ℂ H := HSpace.mk (u₀ - Q) hY₀
  set D : X → HSpace ℂ H := fun x => (F x - F x₀).toHS
  have hD : ContDiff ℝ ⊤ D := ((slSubmodule H).subtypeL.contDiff).comp (hF.sub contDiff_const)
  have hDop : Continuous fun x => (D x).op :=
    (HSpace.opCLM H).continuous.comp hD.continuous
  set U : Set X := {x | ‖(D x).op‖ * (‖u₀‖ + 1) < 1}
  have hU : IsOpen U := isOpen_lt (hDop.norm.mul continuous_const) continuous_const
  have hx₀ : x₀ ∈ U := by
    show ‖(D x₀).op‖ * (‖u₀‖ + 1) < 1
    have : (D x₀).op = 0 := by
      show ((F x₀ - F x₀).toHS).op = 0
      rw [sub_self]; rfl
    rw [this, norm_zero, zero_mul]; exact one_pos
  have hPD : ∀ x, Pp + (F x₀).op + (D x).op = Pp + (F x).op := fun x => by
    simp only [D]
    show Pp + (F x₀).op + (F x - F x₀).op = Pp + (F x).op
    rw [SLSpace.op_sub]; abel
  refine ⟨U, fun x => liftY Q u₀ Y₀ (D x), V, hU, hx₀, hV, ?_, ?_, ?_⟩
  · intro x hx
    have hunit : IsUnit (1 + liftCorr Q u₀ (D x)) :=
      isUnit_one_add_of_norm_lt (norm_liftCorr_lt hQ hx)
    exact ((contDiffAt_liftY hunit).comp x hD.contDiffAt).contDiffWithinAt
  · intro x hx
    have h := (liftY_isFrameOf (Y₀ := Y₀) hQ hfr rfl (hproj x₀) (by rw [hPD]; exact hproj x) hx).1
    rwa [hPD] at h
  · intro x hx
    have h := liftY_isFrameOf (Y₀ := Y₀) hQ hfr rfl (hproj x₀) (by rw [hPD]; exact hproj x) hx
    refine ⟨fun y => ?_, ?_⟩
    · have hval : Q ((liftY Q u₀ Y₀ (D x)).op y) =
          ((Q * u₀ - Q) * Ring.inverse (1 + liftCorr Q u₀ (D x))) y := by
        rw [← h.2]
        simp [mul_add, sub_apply, add_apply, mul_apply_eq_comp]
        rw [← mul_apply_eq_comp Q Q, hQ.isIdempotentElem.eq]; abel
      rw [hval, mul_apply_eq_comp]
      exact hVm _
    · have hwQ := h.1.1
      ext y
      have := congrArg (fun T => T y) hwQ
      simp only [add_mul, hQ.isIdempotentElem.eq] at this
      simpa [mul_apply_eq_comp, frameOf] using this

end LocalLift


/-! ## Segment holonomy and edge holonomy -/

section EdgeHol

variable {Q Pp : H →L[ℂ] H} {e : ℝ → SLSpace H}

variable (Q Pp e) in
/-- A lift of the path exists on `[a, b]`. -/
def LiftableOn (a b : ℝ) : Prop := Nonempty (PathLift Q Pp e a b)

open Classical in
variable (Q Pp e) in
/-- The holonomy factor of a liftable segment (well defined by lift independence). -/
def segHol (a b : ℝ) : ℂ := if h : LiftableOn Q Pp e a b then edgeFactor h.some else 1

theorem segHol_eq (hQ : IsStarProjection Q) {a b : ℝ} (hab : a ≤ b)
    (L : PathLift Q Pp e a b) : segHol Q Pp e a b = edgeFactor L := by
  classical
  rw [segHol, dif_pos ⟨L⟩]
  exact edgeFactor_eq hQ hab _ _

theorem edgeFactor_ne_zero (hQ : IsStarProjection Q) {a b : ℝ} (L : PathLift Q Pp e a b)
    (hab : a ≤ b) : edgeFactor L ≠ 0 := by
  unfold edgeFactor
  have ha := detCoord_ne_zero hQ ((L.isAdmissibleFrame hQ) (L.Icc_subset ⟨le_rfl, hab⟩))
  have hb := detCoord_ne_zero hQ ((L.isAdmissibleFrame hQ) (L.Icc_subset ⟨hab, le_rfl⟩))
  exact div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) ha) hb

theorem segHol_ne_zero (hQ : IsStarProjection Q) {a b : ℝ} (hab : a ≤ b) :
    segHol Q Pp e a b ≠ 0 := by
  classical
  unfold segHol
  split_ifs with h
  · exact edgeFactor_ne_zero hQ _ hab
  · exact one_ne_zero

theorem segHol_mul (hQ : IsStarProjection Q) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (L : PathLift Q Pp e a c) :
    segHol Q Pp e a b * segHol Q Pp e b c = segHol Q Pp e a c := by
  rw [segHol_eq hQ hab (L.restrict a b fun _ hr => L.Icc_subset ⟨hr.1, hr.2.trans hbc⟩),
    segHol_eq hQ hbc (L.restrict b c fun _ hr => L.Icc_subset ⟨hab.trans hr.1, hr.2⟩),
    segHol_eq hQ (hab.trans hbc) L]
  exact edgeFactor_restrict_mul hQ hab hbc L

/-- `k`-fold equal subdivision of a lifted segment. -/
theorem segHol_eq_prod (hQ : IsStarProjection Q) {a b : ℝ} (hab : a ≤ b)
    (L : PathLift Q Pp e a b) {k : ℕ} (hk : 0 < k) :
    segHol Q Pp e a b = ∏ l ∈ Finset.range k,
      segHol Q Pp e (a + l * (b - a) / k) (a + (l + 1) * (b - a) / k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set t : ℕ → ℝ := fun l => a + l * (b - a) / k
  have ht0 : t 0 = a := by simp [t]
  have htk : t k = b := by simp only [t]; field_simp; ring
  have hmono : ∀ l, t l ≤ t (l + 1) := fun l => by
    have h0 : 0 ≤ (b - a) / k := div_nonneg (sub_nonneg.mpr hab) hkpos.le
    have h1 : t (l + 1) = t l + (b - a) / k := by simp only [t]; push_cast; ring
    linarith
  have hle : ∀ l ≤ k, a ≤ t l ∧ t l ≤ b := by
    intro l hl
    have hlk : (l : ℝ) ≤ k := by exact_mod_cast hl
    constructor
    · simp only [t]; have := div_nonneg (mul_nonneg (Nat.cast_nonneg l) (sub_nonneg.mpr hab))
        hkpos.le; linarith
    · simp only [t]
      rw [show a + l * (b - a) / k = a + (l / k) * (b - a) by ring]
      have : (l : ℝ) / k ≤ 1 := (div_le_one hkpos).mpr hlk
      nlinarith [sub_nonneg.mpr hab]
  have key : ∀ n ≤ k, segHol Q Pp e a (t n) = ∏ l ∈ Finset.range n, segHol Q Pp e (t l) (t (l + 1)) := by
    intro n hn
    induction n with
    | zero =>
      rw [ht0, Finset.prod_range_zero]
      have L0 : PathLift Q Pp e a a := L.restrict a a fun _ hr => L.Icc_subset ⟨hr.1, hr.2.trans hab⟩
      rw [segHol_eq hQ le_rfl L0]
      unfold edgeFactor
      simp only [intervalIntegral.integral_same, Complex.exp_zero, one_mul]
      exact div_self (detCoord_ne_zero hQ ((L0.isAdmissibleFrame hQ) (L0.Icc_subset ⟨le_rfl, le_rfl⟩)))
    | succ n ih =>
      have hn' : n ≤ k := Nat.le_of_succ_le hn
      rw [Finset.prod_range_succ, ← ih hn']
      have h1 := hle n hn'
      have h2 := hle (n + 1) hn
      exact (segHol_mul hQ h1.1 (hmono n)
        (L.restrict a (t (n + 1)) fun _ hr => L.Icc_subset ⟨hr.1, hr.2.trans h2.2⟩)).symm
  calc segHol Q Pp e a b = segHol Q Pp e a (t k) := by rw [htk]
    _ = _ := key k le_rfl
    _ = _ := Finset.prod_congr rfl fun l _ => by simp only [t]; push_cast; ring_nf

end EdgeHol


/-! ## Uniform subdivisions and the edge holonomy -/

section Uniform

variable {Q Pp : H →L[ℂ] H} {e : ℝ → SLSpace H}

variable (Q Pp e) in
/-- Every piece `[i/m, (i+1)/m]` of the level-`m` subdivision of `[0, 1]` carries a lift. -/
def FineLevel (m : ℕ) : Prop := ∀ i < m, LiftableOn Q Pp e (i / m) ((i + 1) / m)

variable (Q Pp e) in
/-- The product of the segment holonomies at level `m`. -/
def levelHol (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, segHol Q Pp e (i / m) ((i + 1) / m)

theorem prod_range_mul_eq {M : Type*} [CommMonoid M] (f : ℕ → M) (m k : ℕ) :
    ∏ j ∈ Finset.range (m * k), f j = ∏ i ∈ Finset.range m, ∏ l ∈ Finset.range k, f (i * k + l) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, Finset.prod_range_add, ih, Finset.prod_range_succ]

/-- **Refinement**: passing from level `m` to level `m k` preserves fineness and the product. -/
theorem levelHol_refine (hQ : IsStarProjection Q) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hfine : FineLevel Q Pp e m) :
    FineLevel Q Pp e (m * k) ∧ levelHol Q Pp e m = levelHol Q Pp e (m * k) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  -- the `l`-th subpiece of the `i`-th piece is the `(i k + l)`-th piece of level `m k`
  have hpt : ∀ i l : ℕ, (i : ℝ) / m + l * (((i + 1 : ℕ) : ℝ) / m - i / m) / k =
      ((i * k + l : ℕ) : ℝ) / (m * k : ℕ) := by
    intro i l; push_cast; field_simp; ring
  refine ⟨fun j hj => ?_, ?_⟩
  · -- piece `j` lies inside piece `j / k` of level `m`
    set i := j / k
    have hi : i < m := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hj)
    obtain ⟨L⟩ := hfine i hi
    have hjk : i * k ≤ j := Nat.div_mul_le_self j k
    have hjk' : j + 1 ≤ (i + 1) * k := by
      rw [Nat.succ_le_iff, add_mul, one_mul]; exact Nat.lt_div_mul_add hk
    refine ⟨L.restrict _ _ fun r hr => L.Icc_subset ⟨?_, ?_⟩⟩
    · calc (i : ℝ) / m = ((i * k : ℕ) : ℝ) / (m * k : ℕ) := by
            rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ hkR.ne']
        _ ≤ (j : ℝ) / (m * k : ℕ) := by gcongr
        _ ≤ r := hr.1
    · calc r ≤ ((j : ℝ) + 1) / (m * k : ℕ) := hr.2
        _ ≤ (((i + 1) * k : ℕ) : ℝ) / (m * k : ℕ) := by gcongr; exact_mod_cast hjk'
        _ = ((i : ℝ) + 1) / m := by
            rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ hkR.ne']; push_cast; ring
  · unfold levelHol
    rw [prod_range_mul_eq]
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨L⟩ := hfine i (Finset.mem_range.mp hi)
    have hle : (i : ℝ) / m ≤ ((i : ℝ) + 1) / m := by gcongr; linarith
    rw [segHol_eq_prod hQ hle L hk]
    refine Finset.prod_congr rfl fun l _ => ?_
    have h1 := hpt i l
    have h2 := hpt i (l + 1)
    push_cast at h1 h2 ⊢
    rw [h1, h2]
    congr 1; ring

open Classical in
variable (Q Pp e) in
/-- **The edge holonomy** of a path: the level product at the least fine level. -/
def edgeHol : ℂ :=
  if h : ∃ m, 0 < m ∧ FineLevel Q Pp e m then levelHol Q Pp e (Nat.find h) else 1

/-- **The edge holonomy is computed by every fine level.** -/
theorem edgeHol_eq (hQ : IsStarProjection Q) {m : ℕ} (hm : 0 < m) (hfine : FineLevel Q Pp e m) :
    edgeHol Q Pp e = levelHol Q Pp e m := by
  classical
  have h : ∃ m, 0 < m ∧ FineLevel Q Pp e m := ⟨m, hm, hfine⟩
  rw [edgeHol, dif_pos h]
  obtain ⟨hm₀, hf₀⟩ := Nat.find_spec h
  rw [(levelHol_refine hQ hm₀ hm hf₀).2, (levelHol_refine hQ hm hm₀ hfine).2, mul_comm]

/-- **Paths in the admissible sector have fine levels.** -/
theorem exists_fineLevel (hQ : IsStarProjection Q) (he : ContDiff ℝ ⊤ e)
    (hproj : ∀ τ, IsStarProjection (Pp + (e τ).op))
    (hsec : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∃ u, IsAdmissibleFrame Q u (Pp + (e τ).op)) :
    ∃ m, 0 < m ∧ FineLevel Q Pp e m := by
  classical
  have hloc : ∀ τ : Set.Icc (0 : ℝ) 1, ∃ (U : Set ℝ) (Y : ℝ → HSpace ℂ H) (V : Submodule ℂ H),
      IsOpen U ∧ (τ : ℝ) ∈ U ∧ FiniteDimensional ℂ V ∧ ContDiffOn ℝ ⊤ Y U ∧
      (∀ x ∈ U, IsFrameOf Q (frameOf Q (Y x)) (Pp + (e x).op)) ∧
      (∀ x ∈ U, Y x ∈ admissibleSubspace Q V) := fun τ =>
    exists_local_lift hQ he hproj (hsec τ τ.2).choose_spec
  choose U Y V hU hτU hV hY hfr hadm using hloc
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric isCompact_Icc (c := U) hU
    (fun τ hτ => Set.mem_iUnion.mpr ⟨⟨τ, hτ⟩, hτU ⟨τ, hτ⟩⟩)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := lt_trans (by positivity) hm
    exact_mod_cast this
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hstep : 1 / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hmR]; rw [div_lt_iff₀ hδ] at hm; linarith
  refine ⟨m, hm0, fun i hi => ?_⟩
  have hi0 : (0 : ℝ) ≤ i / m := by positivity
  have hi1 : (i : ℝ) / m ≤ 1 := by
    rw [div_le_one hmR]; exact_mod_cast hi.le
  obtain ⟨τ, hball⟩ := hcov (i / m) ⟨hi0, hi1⟩
  haveI := hV τ
  have hsub : Set.Icc ((i : ℝ) / m) ((i + 1) / m) ⊆ U τ := by
    intro r hr
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : ((i : ℝ) + 1) / m = i / m + 1 / m := by ring
    constructor <;> linarith [hr.1, hr.2]
  exact ⟨⟨U τ, hU τ, hsub, Y τ, V τ, hV τ, (hY τ).of_le (by norm_num), hfr τ, hadm τ⟩⟩

/-- The constant lift of a constant path. -/
def constLift {e : ℝ → SLSpace H} (hconst : ∀ τ, e τ = e 0) {u₀ : H →L[ℂ] H}
    (hu₀ : IsAdmissibleFrame Q u₀ (Pp + (e 0).op)) (hQ : IsStarProjection Q) (a b : ℝ) :
    PathLift Q Pp e a b :=
  { U := Set.univ
    isOpen_U := isOpen_univ
    Icc_subset := Set.subset_univ _
    Y := fun _ => HSpace.mk (u₀ - Q) hu₀.2.1
    V := hu₀.2.2.choose
    finiteDimensional_V := hu₀.2.2.choose_spec.1
    smooth := contDiffOn_const
    frame := fun r _ => by
      rw [hconst r]
      have : frameOf Q (HSpace.mk (u₀ - Q) hu₀.2.1) = u₀ := by simp [frameOf]
      rw [this]; exact hu₀.1
    admissible := fun _ _ => by
      refine ⟨fun x => ?_, ?_⟩
      · have : Q ((HSpace.mk (u₀ - Q) hu₀.2.1).op x) = (Q * u₀ - Q) x := by
          simp [sub_apply, mul_apply_eq_comp]
          rw [← mul_apply_eq_comp Q Q, hQ.isIdempotentElem.eq]
        rw [this]; exact hu₀.2.2.choose_spec.2 x
      · simp only [HSpace.op_mk, sub_mul, hu₀.1.1, hQ.isIdempotentElem.eq] }

/-- **Constant paths have trivial edge holonomy.** -/
theorem edgeHol_const (hQ : IsStarProjection Q) (hconst : ∀ τ, e τ = e 0) {u₀ : H →L[ℂ] H}
    (hu₀ : IsAdmissibleFrame Q u₀ (Pp + (e 0).op)) : edgeHol Q Pp e = 1 := by
  have hfine : FineLevel Q Pp e 1 := fun i hi => ⟨constLift hconst hu₀ hQ _ _⟩
  rw [edgeHol_eq hQ one_pos hfine, levelHol, Finset.prod_range_one]
  simp only [CharP.cast_eq_zero, Nat.cast_one, zero_add, div_one]
  rw [segHol_eq hQ zero_le_one (constLift hconst hu₀ hQ 0 1)]
  unfold edgeFactor
  simp only [constLift, deriv_const', detConnection, HSpace.op_zero, mul_zero]
  simp only [opTrace, _root_.zero_apply, inner_zero_right, tsum_zero,
    intervalIntegral.integral_zero, Complex.exp_zero, one_mul]
  rw [hconst 1]
  exact div_self (detCoord_ne_zero hQ (by
    have := (constLift hconst hu₀ hQ 0 1).isAdmissibleFrame hQ (Set.mem_univ 0)
    rwa [hconst 0] at this))

end Uniform

end

end GaloisForLFunctions.HTGeometry
