import GaloisForLFunctions.HTGeometry.SingularBoundaryTransferScaleGerm

/-!
# The boundary-history corona of compact operators

Let `K(H)` be the compact operators, `B = C_b((0,1], K(H))` the bounded norm-continuous aperture
histories and `I = C_0((0,1], K(H))` those vanishing as the aperture closes.  The corona
`Q = B/I` carries the quotient norm

`‖[F]‖ = limsup_{ε → 0+} ‖F(ε)‖`:

a history vanishing at the closed aperture cannot lower the limit superior, and cutting `F` off
near zero removes everything except the small-aperture values.

For a positive compact operator `T` and `c > 0` the singular boundary transfer history
`ε ↦ E_ε(cT)` is a compact-valued bounded continuous history; its class `𝔢_T(c)` is the scale
germ.  For `T` also injective on an infinite-dimensional space,
`‖𝔢_T(c) - 𝔢_T(d)‖ = |√c - √d|/(√c + √d)` (Theorem INBSG-A).
-/

open Filter Topology Set Metric
open scoped InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The corona -/

/-- The compact operators `K(H)`, as a normed space of its own. -/
def CompactOps (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Type _ :=
  compactOperator (RingHom.id ℂ) H H

instance (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NormedAddCommGroup (CompactOps H) :=
  Submodule.normedAddCommGroup _

instance (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    NormedSpace ℂ (CompactOps H) :=
  Submodule.normedSpace _

/-- The underlying operator of a compact operator. -/
def CompactOps.op (x : CompactOps H) : H →L[ℂ] H := Subtype.val x

/-- A compact operator as an element of `K(H)`. -/
def CompactOps.mk (A : H →L[ℂ] H) (hA : IsCompactOperator A) : CompactOps H := ⟨A, hA⟩

@[simp] theorem CompactOps.op_mk (A : H →L[ℂ] H) (hA : IsCompactOperator A) :
    (CompactOps.mk A hA).op = A := rfl

theorem CompactOps.norm_eq (x : CompactOps H) : ‖x‖ = ‖x.op‖ := rfl

theorem CompactOps.op_sub (x y : CompactOps H) : (x - y).op = x.op - y.op := rfl

theorem CompactOps.op_smul (r : ℝ) (x : CompactOps H) : (r • x).op = r • x.op := rfl

variable [CompleteSpace H]

/-- The aperture interval `(0,1]`. -/
abbrev Aperture : Type := Ioc (0 : ℝ) 1

/-- The closing aperture `ε → 0+` on `(0,1]`. -/
def apertureClosing : Filter Aperture := comap Subtype.val (𝓝[>] (0 : ℝ))

instance : (apertureClosing).NeBot := by
  refine comap_neBot fun s hs => ?_
  obtain ⟨u, hu, hu0, hus⟩ := mem_nhdsWithin.1 hs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hu 0 hu0
  refine ⟨⟨min (r / 2) 1, lt_min (half_pos hr) one_pos, min_le_right _ _⟩, hus ⟨hball ?_, ?_⟩⟩
  · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_pos (lt_min (half_pos hr) one_pos)]
    exact (min_le_left _ _).trans_lt (half_lt_self hr)
  · exact lt_min (half_pos hr) one_pos

/-- The bounded continuous compact-valued aperture histories `C_b((0,1], K(H))`. -/
abbrev ApertureHistory (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := Aperture →ᵇ CompactOps H

/-- The histories vanishing at the closing aperture, `C_0((0,1], K(H))`. -/
def vanishingHistories (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : AddSubgroup (ApertureHistory H) where
  carrier := {F | Tendsto (fun ε => ‖F ε‖) apertureClosing (𝓝 0)}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG
    refine squeeze_zero (fun _ => norm_nonneg _) (fun ε => norm_add_le (F ε) (G ε)) ?_
    simpa using hF.add hG
  neg_mem' := by
    intro F hF
    simpa using hF

/-- The boundary-history corona `Q = C_b((0,1], K(H))/C_0((0,1], K(H))`. -/
abbrev BoundaryCorona (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := ApertureHistory H ⧸ vanishingHistories H

theorem norm_history_le (F : ApertureHistory H) (ε : Aperture) : ‖F ε‖ ≤ ‖F‖ :=
  F.norm_coe_le_norm ε

theorem isBoundedUnder_norm_history (F : ApertureHistory H) :
    IsBoundedUnder (· ≤ ·) apertureClosing fun ε => ‖F ε‖ :=
  isBoundedUnder_of ⟨‖F‖, fun ε => norm_history_le F ε⟩

theorem isCoboundedUnder_norm_history (F : ApertureHistory H) :
    IsCoboundedUnder (· ≤ ·) apertureClosing fun ε => ‖F ε‖ :=
  isCoboundedUnder_le_of_le _ fun ε => norm_nonneg (F ε)

/-- A continuous cutoff equal to `1` on `(0, δ/2]` and `0` on `[δ, ∞)`. -/
def apertureCutoff (δ : ℝ) (x : ℝ) : ℝ := max 0 (min 1 (2 - 2 * x / δ))

theorem continuous_apertureCutoff (δ : ℝ) : Continuous (apertureCutoff δ) := by
  unfold apertureCutoff
  fun_prop

theorem apertureCutoff_mem_Icc (δ x : ℝ) : apertureCutoff δ x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem apertureCutoff_eq_zero {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) : apertureCutoff δ x = 0 := by
  unfold apertureCutoff
  refine max_eq_left (min_le_of_right_le ?_)
  rw [sub_nonpos, le_div_iff₀ hδ]
  linarith

theorem apertureCutoff_eq_one {δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ δ / 2) : apertureCutoff δ x = 1 := by
  unfold apertureCutoff
  rw [min_eq_left, max_eq_right zero_le_one]
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hδ]
  linarith

/-- The cutoff history `(1 - χ_δ) F`, which vanishes near the closed aperture. -/
def cutoffHistory (F : ApertureHistory H) (δ : ℝ) : ApertureHistory H :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ε => (1 - apertureCutoff δ ε) • F ε,
      ((continuous_const.sub ((continuous_apertureCutoff δ).comp continuous_subtype_val)).smul
        F.continuous)⟩
    (2 * ‖F‖) fun ε η => by
      have h : ∀ ε : Aperture, ‖(1 - apertureCutoff δ ε) • F ε‖ ≤ ‖F‖ := fun ε => by
        rw [norm_smul, Real.norm_eq_abs]
        have hc := apertureCutoff_mem_Icc δ ε
        rw [abs_of_nonneg (by linarith [hc.2])]
        calc (1 - apertureCutoff δ ε) * ‖F ε‖ ≤ 1 * ‖F ε‖ :=
              mul_le_mul_of_nonneg_right (by linarith [hc.1]) (norm_nonneg _)
          _ ≤ ‖F‖ := by rw [one_mul]; exact norm_history_le F ε
      calc dist _ _ ≤ ‖(1 - apertureCutoff δ ε) • F ε‖ + ‖(1 - apertureCutoff δ η) • F η‖ :=
            dist_le_norm_add_norm _ _
        _ ≤ ‖F‖ + ‖F‖ := add_le_add (h ε) (h η)
        _ = 2 * ‖F‖ := by ring

theorem cutoffHistory_apply (F : ApertureHistory H) (δ : ℝ) (ε : Aperture) :
    cutoffHistory F δ ε = (1 - apertureCutoff δ ε) • F ε := rfl

theorem cutoffHistory_mem (F : ApertureHistory H) {δ : ℝ} (hδ : 0 < δ) :
    cutoffHistory F δ ∈ vanishingHistories H := by
  change Tendsto (fun ε => ‖cutoffHistory F δ ε‖) apertureClosing (𝓝 0)
  refine tendsto_const_nhds.congr' ?_
  have hmem : {ε : Aperture | (ε : ℝ) < δ / 2} ∈ apertureClosing :=
    ⟨Iio (δ / 2), mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (half_pos hδ)), fun ε hε => hε⟩
  filter_upwards [hmem] with ε hε
  rw [cutoffHistory_apply, apertureCutoff_eq_one hδ hε.le, sub_self, zero_smul, norm_zero]

/-- **(INBSG.7).**  The corona norm is the limit superior at the closing aperture. -/
theorem norm_boundaryCorona_mk (F : ApertureHistory H) :
    ‖(F : BoundaryCorona H)‖ = limsup (fun ε => ‖F ε‖) apertureClosing := by
  rw [QuotientAddGroup.norm_mk]
  set L := limsup (fun ε => ‖F ε‖) apertureClosing
  have hne : (vanishingHistories H : Set (ApertureHistory H)).Nonempty :=
    ⟨0, (vanishingHistories H).zero_mem⟩
  have hL0 : 0 ≤ L :=
    le_limsup_of_frequently_le (Frequently.of_forall fun ε => norm_nonneg (F ε))
      (isBoundedUnder_norm_history F)
  apply le_antisymm
  · -- cut off away from the closed aperture
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have hev : ∀ᶠ ε in apertureClosing, ‖F ε‖ < L + η / 2 :=
      eventually_lt_of_limsup_lt (by linarith) (isBoundedUnder_norm_history F)
    obtain ⟨s, hs, hsub⟩ := hev
    obtain ⟨u, hu, hu0, hus⟩ := mem_nhdsWithin.1 hs
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hu 0 hu0
    have hsmall : ∀ ε : Aperture, (ε : ℝ) < r → ‖F ε‖ < L + η / 2 := fun ε hε =>
      hsub (hus ⟨hball (by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ε.2.1]
        exact hε), ε.2.1⟩)
    have hbound : ‖F - cutoffHistory F r‖ ≤ L + η / 2 := by
      refine (BoundedContinuousFunction.norm_le (by linarith)).2 fun ε => ?_
      rw [BoundedContinuousFunction.coe_sub, Pi.sub_apply, cutoffHistory_apply, sub_smul,
        one_smul, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (apertureCutoff_mem_Icc r ε).1]
      by_cases hε : (ε : ℝ) < r
      · calc apertureCutoff r ε * ‖F ε‖ ≤ 1 * ‖F ε‖ :=
              mul_le_mul_of_nonneg_right (apertureCutoff_mem_Icc r ε).2 (norm_nonneg _)
          _ ≤ L + η / 2 := by rw [one_mul]; exact (hsmall ε hε).le
      · rw [apertureCutoff_eq_zero hr (not_lt.1 hε), zero_mul]
        linarith
    calc infDist F (vanishingHistories H) ≤ dist F (cutoffHistory F r) :=
          infDist_le_dist_of_mem (cutoffHistory_mem F hr)
      _ ≤ L + η / 2 := by rw [dist_eq_norm]; exact hbound
      _ < L + η := by linarith
  · -- a vanishing history cannot lower the limit superior
    refine (le_infDist hne).2 fun G hG => ?_
    rw [dist_eq_norm]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hGsmall : ∀ᶠ ε in apertureClosing, ‖G ε‖ < η :=
      (show Tendsto (fun ε => ‖G ε‖) apertureClosing (𝓝 0) from hG).eventually (gt_mem_nhds hη)
    refine limsup_le_of_le (isCoboundedUnder_norm_history F) ?_
    filter_upwards [hGsmall] with ε hε
    calc ‖F ε‖ = ‖(F - G) ε + G ε‖ := by rw [BoundedContinuousFunction.coe_sub, Pi.sub_apply,
          sub_add_cancel]
      _ ≤ ‖(F - G) ε‖ + ‖G ε‖ := norm_add_le _ _
      _ ≤ ‖F - G‖ + η := add_le_add (norm_history_le _ ε) hε.le

/-! ## Scale germs of the singular boundary transfer -/

section Germ

theorem positiveBoundaryTransfer_eq_comp {T : H →L[ℂ] H} (hT : T.IsPositive) {ε : ℝ}
    (hε : 0 < ε) : positiveBoundaryTransfer T ε = T ∘L positiveBoundaryInverse T ε := by
  have hspec := spectrum_subset_Icc_of_isPositive hT
  have hinv : ContinuousOn (fun x : ℝ => 1 / (ε + x)) (spectrum ℝ T) :=
    ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => by
      have := (hspec hx).1
      positivity
  have h := cfc_mul (fun x : ℝ => x) (fun x : ℝ => 1 / (ε + x)) T (continuousOn_id' _) hinv
  rw [cfc_id' ℝ T hT.isSelfAdjoint] at h
  rw [positiveBoundaryTransfer, positiveBoundaryInverse, ← ContinuousLinearMap.mul_def, ← h]
  refine cfc_congr fun x _ => ?_
  rw [mul_one_div]

theorem isCompactOperator_positiveBoundaryTransfer {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hcpt : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    IsCompactOperator (positiveBoundaryTransfer T ε) := by
  rw [positiveBoundaryTransfer_eq_comp hT hε]
  exact hcpt.comp_clm _

theorem norm_positiveBoundaryTransfer_le_one' {T : H →L[ℂ] H} (hT : T.IsPositive) {ε : ℝ}
    (hε : 0 < ε) : ‖positiveBoundaryTransfer T ε‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · rw [Subsingleton.elim (positiveBoundaryTransfer T ε) 0, norm_zero]
    exact zero_le_one
  exact norm_positiveBoundaryTransfer_le_one hT.isSelfAdjoint
    (spectrum_subset_Icc_of_isPositive hT) ε hε

/-- The aperture modulus of continuity `‖E_ε(T) - E_{ε'}(T)‖ ≤ |ε - ε'|/ε'`. -/
theorem norm_positiveBoundaryTransfer_sub_le {T : H →L[ℂ] H} (hT : T.IsPositive) {ε ε' : ℝ}
    (hε : 0 < ε) (hε' : 0 < ε') :
    ‖positiveBoundaryTransfer T ε - positiveBoundaryTransfer T ε'‖ ≤ |ε - ε'| / ε' := by
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · rw [Subsingleton.elim (positiveBoundaryTransfer T ε - positiveBoundaryTransfer T ε') 0,
      norm_zero]
    positivity
  have hspec := spectrum_subset_Icc_of_isPositive hT
  rw [positiveBoundaryTransfer, positiveBoundaryTransfer,
    ← cfc_sub _ _ T (continuousOn_transferSymbol (fun x hx => (hspec hx).1) hε)
      (continuousOn_transferSymbol (fun x hx => (hspec hx).1) hε')]
  refine norm_cfc_le_of_forall_le _ _
    ((continuousOn_transferSymbol (fun x hx => (hspec hx).1) hε).sub
      (continuousOn_transferSymbol (fun x hx => (hspec hx).1) hε')) hT.isSelfAdjoint
    fun x hx => ?_
  have hx0 := (hspec hx).1
  have h1 : ε + x ≠ 0 := by positivity
  have h2 : ε' + x ≠ 0 := by positivity
  have heq : x / (ε + x) - x / (ε' + x) = (ε' - ε) * (x / (ε + x)) * (1 / (ε' + x)) := by
    field_simp
    ring
  rw [Real.norm_eq_abs, heq, abs_mul, abs_mul, abs_sub_comm,
    abs_of_nonneg (div_nonneg hx0 (by positivity)), abs_of_pos (by positivity : 0 < 1 / (ε' + x))]
  have hq : x / (ε + x) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hr : 1 / (ε' + x) ≤ 1 / ε' := one_div_le_one_div_of_le hε' (by linarith)
  calc |ε - ε'| * (x / (ε + x)) * (1 / (ε' + x)) ≤ |ε - ε'| * 1 * (1 / ε') := by
        gcongr
    _ = |ε - ε'| / ε' := by ring

theorem continuousOn_positiveBoundaryTransfer {T : H →L[ℂ] H} (hT : T.IsPositive) :
    ContinuousOn (fun ε => positiveBoundaryTransfer T ε) (Ioi 0) := by
  intro ε₀ hε₀
  have hε₀' : 0 < ε₀ := hε₀
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ (?_ : Tendsto (fun ε => |ε - ε₀| / ε₀) (𝓝[Ioi 0] ε₀) (𝓝 0)))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_positiveBoundaryTransfer_sub_le hT hε hε₀'
  · have h : Tendsto (fun ε : ℝ => |ε - ε₀| / ε₀) (𝓝 ε₀) (𝓝 (|ε₀ - ε₀| / ε₀)) :=
      ((continuous_abs.comp (continuous_id.sub continuous_const)).div_const ε₀).tendsto ε₀
    rw [sub_self, abs_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds

/-- The transfer history `ε ↦ E_ε(T)` of a positive compact operator, as an element of
`C_b((0,1], K(H))`. -/
def transferHistory (T : H →L[ℂ] H) (hT : T.IsPositive) (hcpt : IsCompactOperator T) :
    ApertureHistory H :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ε => CompactOps.mk (positiveBoundaryTransfer T ε)
        (isCompactOperator_positiveBoundaryTransfer hT hcpt ε.2.1),
      by
        refine continuous_iff_continuousAt.2 fun ε => ?_
        refine Metric.tendsto_nhds.2 fun r hr => ?_
        have hc := (continuousOn_positiveBoundaryTransfer hT) ε ε.2.1
        have hev := (Metric.tendsto_nhds.1 hc) r hr
        have hmap : Tendsto (Subtype.val : Aperture → ℝ) (𝓝 ε) (𝓝[Ioi 0] (ε : ℝ)) :=
          tendsto_nhdsWithin_iff.2 ⟨continuous_subtype_val.tendsto ε,
            Eventually.of_forall fun η => η.2.1⟩
        filter_upwards [hmap.eventually hev] with η hη
        exact hη⟩
    2 fun ε η => by
      calc dist _ _ ≤ ‖CompactOps.mk (positiveBoundaryTransfer T ε)
              (isCompactOperator_positiveBoundaryTransfer hT hcpt ε.2.1)‖ +
            ‖CompactOps.mk (positiveBoundaryTransfer T η)
              (isCompactOperator_positiveBoundaryTransfer hT hcpt η.2.1)‖ :=
            dist_le_norm_add_norm _ _
        _ ≤ 1 + 1 := add_le_add (norm_positiveBoundaryTransfer_le_one' hT ε.2.1)
            (norm_positiveBoundaryTransfer_le_one' hT η.2.1)
        _ = 2 := by norm_num

theorem transferHistory_apply (T : H →L[ℂ] H) (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    (ε : Aperture) : (transferHistory T hT hcpt ε).op = positiveBoundaryTransfer T ε := rfl

omit [CompleteSpace H] in
theorem isPositive_real_smul {T : H →L[ℂ] H} (hT : T.IsPositive) {c : ℝ} (hc : 0 ≤ c) :
    (c • T).IsPositive := by
  have h := hT.smul_of_nonneg (c := (c : ℂ)) (Complex.zero_le_real.2 hc)
  rwa [show ((c : ℂ) • T) = c • T from (RCLike.real_smul_eq_coe_smul (K := ℂ) c T).symm] at h

/-- **(INBSG.8).**  The scale germ `𝔢_T(c) = [ε ↦ E_ε(cT)]` in the boundary corona. -/
def scaleGerm (T : H →L[ℂ] H) (hT : T.IsPositive) (hcpt : IsCompactOperator T) {c : ℝ}
    (hc : 0 < c) : BoundaryCorona H :=
  (transferHistory (c • T) (isPositive_real_smul hT hc.le) (hcpt.smul c) : BoundaryCorona H)

/-- **Theorem INBSG-A (INBSG.9).**  For a positive compact injective operator on an
infinite-dimensional Hilbert space, `‖𝔢_T(c) - 𝔢_T(d)‖ = |√c - √d|/(√c + √d)`. -/
theorem norm_scaleGerm_sub {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) :
    ‖scaleGerm T hT hcpt hc - scaleGerm T hT hcpt hd‖ = |germContrast c d| := by
  rw [scaleGerm, scaleGerm, ← QuotientAddGroup.mk_sub, norm_boundaryCorona_mk]
  set D : Aperture → ℝ := fun ε => ‖(transferHistory (c • T) (isPositive_real_smul hT hc.le)
    (hcpt.smul c) - transferHistory (d • T) (isPositive_real_smul hT hd.le) (hcpt.smul d)) ε‖
  have hD : ∀ ε : Aperture, D ε = ‖positiveBoundaryTransfer (c • T) ε -
      positiveBoundaryTransfer (d • T) ε‖ := fun ε => rfl
  have hle : ∀ ε, D ε ≤ |germContrast c d| := fun ε => by
    rw [hD]
    exact norm_scaledTransfer_sub_le hT hc hd ε.2.1
  refine le_antisymm (limsup_le_of_le (isCoboundedUnder_le_of_le _ fun _ => norm_nonneg _)
    (Eventually.of_forall hle)) (le_limsup_of_frequently_le ?_
      (isBoundedUnder_of ⟨_, hle⟩))
  obtain ⟨x, hx, hx0⟩ := exists_spectrum_seq_tendsto_zero hT hcpt hinj hH
  have hε : Tendsto (fun n => Real.sqrt (c * d) * x n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mul_pos (Real.sqrt_pos.2 (mul_pos hc hd)) (hx n).1⟩
    simpa using hx0.const_mul (Real.sqrt (c * d))
  have hsmall : ∀ᶠ n in atTop, Real.sqrt (c * d) * x n ≤ 1 :=
    (hε.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds zero_lt_one)
  have hfreq : ∃ᶠ n in atTop, Real.sqrt (c * d) * x n ≤ 1 ∧
      |germContrast c d| ≤ ‖positiveBoundaryTransfer (c • T) (Real.sqrt (c * d) * x n) -
        positiveBoundaryTransfer (d • T) (Real.sqrt (c * d) * x n)‖ :=
    (hsmall.and (Eventually.of_forall fun n =>
      le_norm_scaledTransfer_sub_of_mem_spectrum hT hc hd (hx n).2 (hx n).1)).frequently
  have hfreq' := hε.frequently (p := fun b => b ≤ 1 ∧ |germContrast c d| ≤
      ‖positiveBoundaryTransfer (c • T) b - positiveBoundaryTransfer (d • T) b‖) hfreq
  refine (frequently_comap.2 ?_)
  refine (hfreq'.and_eventually self_mem_nhdsWithin).mono fun b hb => ?_
  exact ⟨⟨b, hb.2, hb.1.1⟩, rfl, by rw [hD]; exact hb.1.2⟩

end Germ

end GaloisForLFunctions.HTGeometry
