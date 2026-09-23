import Mathlib

/-!
# The uniform shell charges a small coordinate block with the block-dimension power

Split a finite-dimensional real inner product space as an orthogonal sum of a block `U` and its
complement `V`.  On the unit sphere of the sum, the set where the block component has norm at most
`x` is the radial projection of a cone, and the cone is squeezed between two explicit product sets:
it is contained in the product of the block ball of radius `x` with the full complement ball, and it
contains the product of the block ball of radius `x/2` with a fixed complement ball of radius `1/8`
centred at norm `5/8`.  Haar scaling turns both product volumes into constants times
`x ^ dim U`, so the shell probability of a small block is bounded above and below by constant
multiples of `x ^ dim U`.

The exponent is the block dimension alone: the complement only contributes the two constants.
-/

open MeasureTheory Metric Set
open scoped Pointwise ENNReal

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section BlockTail

variable (U V : Type*)
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

/-- The orthogonal sum of the block and its complement. -/
abbrev BlockSpace : Type _ := WithLp 2 (U × V)

/-- The points of the unit shell whose block component has norm at most `x`. -/
def blockSmall (x : ℝ) : Set (sphere (0 : BlockSpace U V) 1) :=
  {u | ‖(u : BlockSpace U V).fst‖ ≤ x}

theorem lipschitzWith_blockPart :
    LipschitzWith 1 fun v : BlockSpace U V => v.fst := by
  refine LipschitzWith.of_dist_le_mul fun v w => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  exact WithLp.norm_fst_le (x := v - w)

theorem measurableSet_blockSmall (x : ℝ) : MeasurableSet (blockSmall U V x) := by
  have hcont : Continuous fun u : sphere (0 : BlockSpace U V) 1 =>
      ‖(u : BlockSpace U V).fst‖ :=
    (((lipschitzWith_blockPart U V).continuous).comp continuous_subtype_val).norm
  exact measurableSet_le hcont.measurable measurable_const

/-- The cone over the block-small shell set lies in the product of the small block ball with the
full complement ball. -/
theorem cone_blockSmall_subset {x : ℝ} (hx : 0 ≤ x) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' blockSmall U V x)
      ⊆ (WithLp.ofLp ⁻¹' (closedBall (0 : U) x ×ˢ ball (0 : V) 1) : Set (BlockSpace U V)) := by
  rintro v hv
  rw [Set.mem_smul] at hv
  obtain ⟨r, hr, w, hw, rfl⟩ := hv
  obtain ⟨u, hu, rfl⟩ := hw
  have hunorm : ‖(u : BlockSpace U V)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hr0 : 0 < r := hr.1
  have hr1 : r < 1 := hr.2
  have hfst : ‖(r • (u : BlockSpace U V)).fst‖ ≤ x := by
    rw [WithLp.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    calc r * ‖(u : BlockSpace U V).fst‖ ≤ r * x :=
          mul_le_mul_of_nonneg_left hu hr0.le
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right hr1.le hx
      _ = x := one_mul x
  have hsnd : ‖(r • (u : BlockSpace U V)).snd‖ < 1 := by
    refine lt_of_le_of_lt (WithLp.norm_snd_le (x := r • (u : BlockSpace U V))) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hunorm, mul_one]
    exact hr1
  exact ⟨mem_closedBall_zero_iff.mpr hfst, mem_ball_zero_iff.mpr hsnd⟩

/-- A product of a small block ball with a fixed off-centre complement ball lies inside the cone
over the block-small shell set. -/
theorem prod_subset_cone_blockSmall {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {c : V}
    (hc : ‖c‖ = 5 / 8) :
    (WithLp.ofLp ⁻¹' (closedBall (0 : U) (x / 2) ×ˢ closedBall c (1 / 8)) :
        Set (BlockSpace U V))
      ⊆ Ioo (0 : ℝ) 1 • (Subtype.val '' blockSmall U V x) := by
  rintro v ⟨hv1, hv2⟩
  have hfst : ‖v.fst‖ ≤ x / 2 := mem_closedBall_zero_iff.mp hv1
  have hsnd : ‖v.snd - c‖ ≤ 1 / 8 := by
    rw [← dist_eq_norm]
    exact hv2
  have hsndub : ‖v.snd‖ ≤ 3 / 4 := by
    have h2 : ‖v.snd‖ - ‖c‖ ≤ ‖v.snd - c‖ := norm_sub_norm_le _ _
    rw [hc] at h2
    linarith
  have hsndlb : (1 : ℝ) / 2 ≤ ‖v.snd‖ := by
    have h2 : ‖c‖ - ‖v.snd‖ ≤ ‖c - v.snd‖ := norm_sub_norm_le _ _
    rw [hc, norm_sub_rev] at h2
    linarith
  have hfstub : ‖v.fst‖ ≤ 1 / 2 := le_trans hfst (by linarith)
  have hsq : ‖v‖ ^ 2 = ‖v.fst‖ ^ 2 + ‖v.snd‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 v
  have hnormlt : ‖v‖ < 1 := by
    nlinarith [norm_nonneg v, norm_nonneg v.fst, norm_nonneg v.snd]
  have hnormge : (1 : ℝ) / 2 ≤ ‖v‖ := by
    nlinarith [norm_nonneg v, norm_nonneg v.fst, norm_nonneg v.snd]
  have hnormpos : 0 < ‖v‖ := by linarith
  have hne : (‖v‖ : ℝ) ≠ 0 := ne_of_gt hnormpos
  have husphere : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnormpos), inv_mul_cancel₀ hne]
  refine Set.mem_smul.mpr ⟨‖v‖, ⟨hnormpos, hnormlt⟩, ((‖v‖⁻¹ : ℝ) • v), ?_, ?_⟩
  · refine ⟨⟨(‖v‖⁻¹ : ℝ) • v, mem_sphere_zero_iff_norm.mpr husphere⟩, ?_, rfl⟩
    show ‖(((‖v‖⁻¹ : ℝ) • v : BlockSpace U V)).fst‖ ≤ x
    rw [WithLp.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnormpos)]
    rw [inv_mul_le_iff₀ hnormpos]
    calc ‖v.fst‖ ≤ x / 2 := hfst
      _ ≤ ‖v‖ * x := by nlinarith
  · show (‖v‖ : ℝ) • ((‖v‖⁻¹ : ℝ) • v) = v
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- The volume of a preimage product in the split space is the product of the factor volumes. -/
theorem volume_ofLp_preimage_prod {S : Set U} {T : Set V} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    volume (WithLp.ofLp ⁻¹' (S ×ˢ T) : Set (BlockSpace U V)) = volume S * volume T := by
  rw [(WithLp.volume_preserving_ofLp U V).measure_preimage (hS.prod hT).nullMeasurableSet,
    Measure.volume_eq_prod U V, Measure.prod_prod]

/-- **The block tail upper bound.**  The shell mass of the block-small set is at most a constant
times `x ^ dim U`. -/
theorem toSphere_blockSmall_le {x : ℝ} (hx : 0 ≤ x) :
    volume.toSphere (blockSmall U V x)
      ≤ (Module.finrank ℝ (BlockSpace U V) : ℝ≥0∞) *
        (ENNReal.ofReal (x ^ Module.finrank ℝ U) *
          (volume (ball (0 : U) 1) * volume (ball (0 : V) 1))) := by
  rw [Measure.toSphere_apply' _ (measurableSet_blockSmall U V x)]
  gcongr
  calc volume (Ioo (0 : ℝ) 1 • (Subtype.val '' blockSmall U V x))
      ≤ volume (WithLp.ofLp ⁻¹' (closedBall (0 : U) x ×ˢ ball (0 : V) 1) :
          Set (BlockSpace U V)) := measure_mono (cone_blockSmall_subset U V hx)
    _ = volume (closedBall (0 : U) x) * volume (ball (0 : V) 1) :=
        volume_ofLp_preimage_prod U V measurableSet_closedBall measurableSet_ball
    _ = ENNReal.ofReal (x ^ Module.finrank ℝ U) *
          (volume (ball (0 : U) 1) * volume (ball (0 : V) 1)) := by
        rw [Measure.addHaar_closedBall volume 0 hx, mul_assoc]

/-- **The block tail lower bound.**  The shell mass of the block-small set is at least a positive
constant times `x ^ dim U`. -/
theorem toSphere_blockSmall_ge [Nontrivial V] {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (Module.finrank ℝ (BlockSpace U V) : ℝ≥0∞) *
        (ENNReal.ofReal ((x / 2) ^ Module.finrank ℝ U) *
          (volume (ball (0 : U) 1) *
            (ENNReal.ofReal ((1 / 8 : ℝ) ^ Module.finrank ℝ V) * volume (ball (0 : V) 1))))
      ≤ volume.toSphere (blockSmall U V x) := by
  obtain ⟨c, hc⟩ : ∃ c : V, ‖c‖ = 5 / 8 := exists_norm_eq V (by norm_num)
  rw [Measure.toSphere_apply' _ (measurableSet_blockSmall U V x)]
  gcongr
  calc ENNReal.ofReal ((x / 2) ^ Module.finrank ℝ U) *
        (volume (ball (0 : U) 1) *
          (ENNReal.ofReal ((1 / 8 : ℝ) ^ Module.finrank ℝ V) * volume (ball (0 : V) 1)))
      = volume (closedBall (0 : U) (x / 2)) * volume (closedBall c (1 / 8 : ℝ)) := by
        rw [Measure.addHaar_closedBall volume 0 (by linarith : (0:ℝ) ≤ x / 2),
          Measure.addHaar_closedBall volume c (by norm_num : (0:ℝ) ≤ 1 / 8)]
        ring
    _ = volume (WithLp.ofLp ⁻¹' (closedBall (0 : U) (x / 2) ×ˢ closedBall c (1 / 8 : ℝ)) :
          Set (BlockSpace U V)) :=
        (volume_ofLp_preimage_prod U V measurableSet_closedBall measurableSet_closedBall).symm
    _ ≤ volume (Ioo (0 : ℝ) 1 • (Subtype.val '' blockSmall U V x)) :=
        measure_mono (prod_subset_cone_blockSmall U V hx0 hx1 hc)

end BlockTail

section Probability

variable (U V : Type*)
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

/-- The uniform shell probability of a shell event: its shell mass over the total shell mass. -/
def shellProb (A : Set (sphere (0 : BlockSpace U V) 1)) : ℝ :=
  (volume.toSphere A).toReal /
    (volume.toSphere (univ : Set (sphere (0 : BlockSpace U V) 1))).toReal

theorem nontrivial_blockSpace [Nontrivial V] : Nontrivial (BlockSpace U V) := by
  obtain ⟨c, hc⟩ : ∃ c : V, ‖c‖ = 1 := exists_norm_eq V zero_le_one
  refine ⟨⟨0, WithLp.toLp 2 (0, c), fun h => ?_⟩⟩
  have hsnd : (0 : BlockSpace U V).snd = (WithLp.toLp 2 ((0 : U), c)).snd := by rw [h]
  have : (0 : V) = c := hsnd
  rw [← this] at hc
  simp at hc

theorem toSphere_univ_toReal [Nontrivial V] :
    (volume.toSphere (univ : Set (sphere (0 : BlockSpace U V) 1))).toReal
      = (Module.finrank ℝ (BlockSpace U V) : ℝ) *
        (volume (ball (0 : BlockSpace U V) 1)).toReal := by
  haveI := nontrivial_blockSpace U V
  rw [Measure.toSphere_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_natCast]

theorem toSphere_univ_toReal_pos [Nontrivial V] :
    0 < (volume.toSphere (univ : Set (sphere (0 : BlockSpace U V) 1))).toReal := by
  haveI := nontrivial_blockSpace U V
  rw [toSphere_univ_toReal]
  have hrank : 0 < Module.finrank ℝ (BlockSpace U V) := Module.finrank_pos
  have hball : 0 < (volume (ball (0 : BlockSpace U V) 1)).toReal := by
    refine ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 one_pos)) ?_
    exact ne_of_lt measure_ball_lt_top
  have : (0 : ℝ) < (Module.finrank ℝ (BlockSpace U V) : ℝ) := by exact_mod_cast hrank
  positivity

/-- **The block tail upper bound in probability form.**  The shell probability that the block
component is at most `x` is at most a constant times `x ^ dim U`. -/
theorem shellProb_blockSmall_le [Nontrivial V] {x : ℝ} (hx : 0 ≤ x) :
    shellProb U V (blockSmall U V x)
      ≤ ((volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal /
          (volume (ball (0 : BlockSpace U V) 1)).toReal) * x ^ Module.finrank ℝ U := by
  haveI := nontrivial_blockSpace U V
  have hballU : (volume (ball (0 : U) 1)).toReal = (volume (ball (0 : U) 1)).toReal := rfl
  have hfin : (volume (ball (0 : U) 1)) ≠ ⊤ := ne_of_lt measure_ball_lt_top
  have hfinV : (volume (ball (0 : V) 1)) ≠ ⊤ := ne_of_lt measure_ball_lt_top
  have hnum : (volume.toSphere (blockSmall U V x)).toReal
      ≤ (Module.finrank ℝ (BlockSpace U V) : ℝ) *
        (x ^ Module.finrank ℝ U *
          ((volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal)) := by
    have hle := toSphere_blockSmall_le U V (x := x) hx
    have htop : ((Module.finrank ℝ (BlockSpace U V) : ℝ≥0∞) *
        (ENNReal.ofReal (x ^ Module.finrank ℝ U) *
          (volume (ball (0 : U) 1) * volume (ball (0 : V) 1)))) ≠ ⊤ := by
      refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hfin hfinV)
    have := ENNReal.toReal_mono htop hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)] at this
  have hden := toSphere_univ_toReal U V
  have hdenpos := toSphere_univ_toReal_pos U V
  have hballE : 0 < (volume (ball (0 : BlockSpace U V) 1)).toReal := by
    refine ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 one_pos)) ?_
    exact ne_of_lt measure_ball_lt_top
  rw [shellProb, div_le_iff₀ hdenpos, hden]
  have hrank : (0 : ℝ) < (Module.finrank ℝ (BlockSpace U V) : ℝ) := by
    exact_mod_cast Module.finrank_pos
  calc (volume.toSphere (blockSmall U V x)).toReal
      ≤ (Module.finrank ℝ (BlockSpace U V) : ℝ) *
        (x ^ Module.finrank ℝ U *
          ((volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal)) := hnum
    _ = ((volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal /
          (volume (ball (0 : BlockSpace U V) 1)).toReal) * x ^ Module.finrank ℝ U *
          ((Module.finrank ℝ (BlockSpace U V) : ℝ) *
            (volume (ball (0 : BlockSpace U V) 1)).toReal) := by
        field_simp

/-- **The block tail lower bound in probability form.**  The shell probability that the block
component is at most `x` is at least a positive constant times `x ^ dim U`. -/
theorem shellProb_blockSmall_ge [Nontrivial V] {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ((1 / 2 : ℝ) ^ Module.finrank ℝ U * (1 / 8 : ℝ) ^ Module.finrank ℝ V *
        ((volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal /
          (volume (ball (0 : BlockSpace U V) 1)).toReal)) * x ^ Module.finrank ℝ U
      ≤ shellProb U V (blockSmall U V x) := by
  haveI := nontrivial_blockSpace U V
  have hfin : (volume (ball (0 : U) 1)) ≠ ⊤ := ne_of_lt measure_ball_lt_top
  have hfinV : (volume (ball (0 : V) 1)) ≠ ⊤ := ne_of_lt measure_ball_lt_top
  have hnum : (Module.finrank ℝ (BlockSpace U V) : ℝ) *
        ((x / 2) ^ Module.finrank ℝ U *
          ((volume (ball (0 : U) 1)).toReal *
            ((1 / 8 : ℝ) ^ Module.finrank ℝ V * (volume (ball (0 : V) 1)).toReal)))
      ≤ (volume.toSphere (blockSmall U V x)).toReal := by
    have hle := toSphere_blockSmall_ge U V (x := x) hx0 hx1
    have htop : volume.toSphere (blockSmall U V x) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (toSphere_blockSmall_le U V hx0) ?_)
      refine ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top (lt_of_le_of_ne le_top hfin) (lt_of_le_of_ne le_top hfinV))
    have := ENNReal.toReal_mono htop hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at this
  have hden := toSphere_univ_toReal U V
  have hdenpos := toSphere_univ_toReal_pos U V
  have hballE : 0 < (volume (ball (0 : BlockSpace U V) 1)).toReal := by
    refine ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 one_pos)) ?_
    exact ne_of_lt measure_ball_lt_top
  rw [shellProb, le_div_iff₀ hdenpos, hden]
  have hhalf : (x / 2) ^ Module.finrank ℝ U
      = (1 / 2 : ℝ) ^ Module.finrank ℝ U * x ^ Module.finrank ℝ U := by
    rw [← mul_pow]
    ring_nf
  calc ((1 / 2 : ℝ) ^ Module.finrank ℝ U * (1 / 8 : ℝ) ^ Module.finrank ℝ V *
        ((volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal /
          (volume (ball (0 : BlockSpace U V) 1)).toReal)) * x ^ Module.finrank ℝ U *
        ((Module.finrank ℝ (BlockSpace U V) : ℝ) *
          (volume (ball (0 : BlockSpace U V) 1)).toReal)
      = (Module.finrank ℝ (BlockSpace U V) : ℝ) *
        ((x / 2) ^ Module.finrank ℝ U *
          ((volume (ball (0 : U) 1)).toReal *
            ((1 / 8 : ℝ) ^ Module.finrank ℝ V * (volume (ball (0 : V) 1)).toReal))) := by
        rw [hhalf]
        field_simp
    _ ≤ (volume.toSphere (blockSmall U V x)).toReal := hnum

end Probability

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

variable (U V : Type*)
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

/-- The shell points whose block component under a chosen orthogonal splitting is small. -/
def blockSmallOf (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V) (x : ℝ) : Set (sphere (0 : E) 1) :=
  {u | ‖(Φ (u : E)).fst‖ ≤ x}

/-- A linear isometry equivalence preserves the volume of an arbitrary preimage. -/
theorem volume_preimage_linearIsometryEquiv (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V)
    (W : Set (BlockSpace U V)) : volume (Φ ⁻¹' W) = volume W := by
  have hmap : (volume : Measure E).map Φ = volume := Φ.measurePreserving.map_eq
  calc volume (Φ ⁻¹' W) = ((volume : Measure E).map Φ) W :=
        (MeasurableEquiv.map_apply Φ.toMeasurableEquiv W).symm
    _ = volume W := by rw [hmap]

theorem image_val_blockSmallOf (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V) (x : ℝ) :
    (Subtype.val '' blockSmallOf U V Φ x) = Φ ⁻¹' (Subtype.val '' blockSmall U V x) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨Φ (u : E), ?_⟩, hu, rfl⟩
    rw [mem_sphere_zero_iff_norm, Φ.norm_map]
    exact mem_sphere_zero_iff_norm.mp u.2
  · rintro ⟨w, hw, hwv⟩
    have hnorm : ‖v‖ = 1 := by
      rw [← Φ.norm_map v, ← hwv]
      exact mem_sphere_zero_iff_norm.mp w.2
    refine ⟨⟨v, mem_sphere_zero_iff_norm.mpr hnorm⟩, ?_, rfl⟩
    show ‖(Φ v).fst‖ ≤ x
    rw [← hwv]
    exact hw

theorem smul_preimage_linearIsometryEquiv_sphereBlockTail (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V)
    (S : Set (BlockSpace U V)) :
    Ioo (0 : ℝ) 1 • (Φ ⁻¹' S) = Φ ⁻¹' (Ioo (0 : ℝ) 1 • S) := by
  ext v
  constructor
  · intro hv
    rw [Set.mem_smul] at hv
    obtain ⟨r, hr, w, hw, rfl⟩ := hv
    refine Set.mem_smul.mpr ⟨r, hr, Φ w, hw, ?_⟩
    rw [Φ.map_smul]
  · intro hv
    rw [Set.mem_preimage, Set.mem_smul] at hv
    obtain ⟨r, hr, s, hs, hrs⟩ := hv
    refine Set.mem_smul.mpr ⟨r, hr, Φ.symm s, ?_, ?_⟩
    · rw [Set.mem_preimage, Φ.apply_symm_apply]
      exact hs
    · have : Φ (r • Φ.symm s) = r • s := by
        rw [Φ.map_smul, Φ.apply_symm_apply]
      exact Φ.injective (by rw [this, hrs])

/-- **The transported block tail law.**  Along any orthogonal splitting of a Euclidean space into a
block and its complement, the shell mass of the block-small set is the shell mass of the model
block-small set. -/
theorem toSphere_blockSmallOf (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V) (x : ℝ) :
    volume.toSphere (blockSmallOf U V Φ x) = volume.toSphere (blockSmall U V x) := by
  have hmeas : MeasurableSet (blockSmallOf U V Φ x) := by
    have hcont : Continuous fun u : sphere (0 : E) 1 => ‖(Φ (u : E)).fst‖ :=
      ((lipschitzWith_blockPart U V).continuous.comp (Φ.continuous.comp continuous_subtype_val)).norm
    exact measurableSet_le hcont.measurable measurable_const
  have hrank : Module.finrank ℝ E = Module.finrank ℝ (BlockSpace U V) :=
    Φ.toLinearEquiv.finrank_eq
  rw [Measure.toSphere_apply' _ hmeas, Measure.toSphere_apply' _ (measurableSet_blockSmall U V x),
    hrank, image_val_blockSmallOf, smul_preimage_linearIsometryEquiv_sphereBlockTail,
    volume_preimage_linearIsometryEquiv]

theorem volume_ball_eq_of_linearIsometryEquiv (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V) :
    volume (ball (0 : E) 1) = volume (ball (0 : BlockSpace U V) 1) := by
  have hpre : (Φ ⁻¹' ball (0 : BlockSpace U V) 1) = ball (0 : E) 1 := by
    ext v
    rw [Set.mem_preimage, mem_ball_zero_iff, mem_ball_zero_iff, Φ.norm_map]
  rw [← hpre, volume_preimage_linearIsometryEquiv]

/-- The total shell mass is an isometry invariant. -/
theorem toSphere_univ_eq_of_linearIsometryEquiv (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V) :
    volume.toSphere (univ : Set (sphere (0 : E) 1))
      = volume.toSphere (univ : Set (sphere (0 : BlockSpace U V) 1)) := by
  rw [Measure.toSphere_apply_univ, Measure.toSphere_apply_univ,
    Φ.toLinearEquiv.finrank_eq, volume_ball_eq_of_linearIsometryEquiv U V Φ]

/-- The shell probability of the transported block-small set agrees with the model. -/
theorem shellProb_blockSmallOf (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V) (x : ℝ) :
    (volume.toSphere (blockSmallOf U V Φ x)).toReal /
        (volume.toSphere (univ : Set (sphere (0 : E) 1))).toReal
      = shellProb U V (blockSmall U V x) := by
  rw [shellProb, toSphere_blockSmallOf, toSphere_univ_eq_of_linearIsometryEquiv U V Φ]

/-- **The block tail law along an arbitrary orthogonal splitting.**  With respect to the uniform
shell measure, the probability that the block component of a shell point is at most `x` is trapped
between two positive constant multiples of `x ^ dim U`. -/
theorem exists_blockTail_bounds [Nontrivial V] (Φ : E ≃ₗᵢ[ℝ] BlockSpace U V) :
    ∃ C c : ℝ, 0 < c ∧ 0 < C ∧
      (∀ x : ℝ, 0 ≤ x →
        (volume.toSphere (blockSmallOf U V Φ x)).toReal /
            (volume.toSphere (univ : Set (sphere (0 : E) 1))).toReal
          ≤ C * x ^ Module.finrank ℝ U) ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        c * x ^ Module.finrank ℝ U ≤
          (volume.toSphere (blockSmallOf U V Φ x)).toReal /
            (volume.toSphere (univ : Set (sphere (0 : E) 1))).toReal) := by
  have hballU : 0 < (volume (ball (0 : U) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 one_pos))
      (ne_of_lt measure_ball_lt_top)
  have hballV : 0 < (volume (ball (0 : V) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 one_pos))
      (ne_of_lt measure_ball_lt_top)
  have hballE : 0 < (volume (ball (0 : BlockSpace U V) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume 0 one_pos))
      (ne_of_lt measure_ball_lt_top)
  refine ⟨(volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal /
      (volume (ball (0 : BlockSpace U V) 1)).toReal,
    (1 / 2 : ℝ) ^ Module.finrank ℝ U * (1 / 8 : ℝ) ^ Module.finrank ℝ V *
      ((volume (ball (0 : U) 1)).toReal * (volume (ball (0 : V) 1)).toReal /
        (volume (ball (0 : BlockSpace U V) 1)).toReal), by positivity, by positivity, ?_, ?_⟩
  · intro x hx
    rw [shellProb_blockSmallOf U V Φ x]
    exact shellProb_blockSmall_le U V hx
  · intro x hx0 hx1
    rw [shellProb_blockSmallOf U V Φ x]
    exact shellProb_blockSmall_ge U V hx0 hx1

end Transport

end

end GaloisForLFunctions.HTGeometry
