import GaloisForLFunctions.RHTower.FokasLenellsParameterContinuity

/-!
# Uniform reconstruction bounds and joint Hardy boundary limits

The actual jump has one L² envelope independent of both physical parameters.
Its norm controls the entire normalized RH inverse uniformly in time and
position. Consequently the holomorphic matrix tends to the identity at vertical
infinity even when time, position, and the horizontal spectral coordinate drift
arbitrarily. At the other end, the Plemelj boundary limit is joint in height and
physical parameters. These conclusions combine the paper's Cauchy and inverse
mechanisms with the corpus's L² domination and strong multiplier continuity.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- One finite size controls the actual RH jump at every time and position. -/
def directJumpSize (q : SchwartzMap ℝ ℂ) : ℝ :=
  ‖(regularJumpL2Envelope_memLp q).toLp (regularJumpL2Envelope q)‖

/-- The common pointwise envelope controls each actual L² jump entry. -/
theorem directJumpEntry_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    ‖directJumpEntry q t x i j‖ ≤ directJumpSize q := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [directJumpEntry_ae q t x i j,(regularJumpL2Envelope_memLp q).coeFn_toLp]
    with z hj he
  rw [hj,he,Real.norm_eq_abs,abs_of_nonneg]
  · exact regularJump_sub_one_envelope q t x z i j
  · exact add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem directJumpRow_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directJumpRow q t x i‖ ≤ directJumpSize q :=
  max_le (directJumpEntry_uniform_bound q t x i 0) (directJumpEntry_uniform_bound q t x i 1)

/-- A single potential-dependent size controls the forcing, both boundary corrections, and the density everywhere. -/
theorem directRH_uniform_L2_bounds (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ‖directRHForcing q t x i‖ ≤ directJumpSize q ∧
    ‖directLowerCorrection q t x i‖ ≤ (9/5 : ℝ)*directJumpSize q ∧
    ‖directUpperCorrection q t x i‖ ≤ (9/5 : ℝ)*directJumpSize q ∧
    ‖directRHDensity q t x i‖ ≤ (9/5 : ℝ)*directJumpSize q := by
  have hb := directJumpRow_uniform_bound q t x i
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ 9/5)
  exact ⟨(boundaryCauchy_bound _).trans hb,(directLowerCorrection_bound q t x i).trans hm,
    (directUpperCorrection_bound q t x i).trans hm,(directRHDensity_bound q t x i).trans hm⟩

/-- All actual holomorphic slices have one L² bound independent of height, space, and time. -/
theorem directAnalyticSlice_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    ‖directAnalyticSlice q t x i upper a‖ ≤ (9/5 : ℝ)*directJumpSize q :=
  (directAnalyticSlice_bound q t x i upper a).trans
    (mul_le_mul_of_nonneg_left (directJumpRow_uniform_bound q t x i) (by positivity))

/-- The pointwise reconstruction bound is uniform over the entire physical plane. -/
theorem directAnalyticMatrix_entry_uniform_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i j : Fin 2) (upper : Bool) (r a : ℝ) :
    ‖directAnalyticMatrix q t x (halfPlanePoint upper r a) i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤
      (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*((9/5 : ℝ)*directJumpSize q) :=
  (directAnalyticMatrix_entry_bound q t x i j upper r a).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (directJumpRow_uniform_bound q t x i) (by positivity)) (by positivity))

/-- Normalization survives arbitrary simultaneous drift in time, position, and horizontal spectral coordinate. -/
theorem directAnalyticMatrix_tendsto_vertical_infinity_arbitrary_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (t x r : ℝ → ℝ) (i j : Fin 2) :
    Tendsto (fun a => directAnalyticMatrix q (t a) (x a) (halfPlanePoint upper (r a) a) i j) atTop
      (𝓝 ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)) := by
  have ht : Tendsto (fun a : ℝ => Real.pi/Real.exp a) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,← Real.exp_neg,mul_zero] using
      Real.tendsto_exp_neg_atTop_nhds_zero.const_mul Real.pi
  have hs : Tendsto (fun a : ℝ => (2*Real.pi)⁻¹*Real.sqrt (Real.pi/Real.exp a)*
      ((9/5 : ℝ)*directJumpSize q)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero,zero_mul] using
      (((Real.continuous_sqrt.tendsto 0).comp ht).const_mul ((2*Real.pi)⁻¹)).mul_const
        ((9/5 : ℝ)*directJumpSize q)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun a => norm_nonneg _) (fun a =>
    directAnalyticMatrix_entry_uniform_bound q (t a) (x a) i j upper (r a) a) hs

/-- The trace carrier includes height zero, where it represents the actual Hardy boundary correction. -/
def directTrace (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) (h : ℝ) : Boundary :=
  (cauchyTrace (directRHDensity q t x i).1 upper h,cauchyTrace (directRHDensity q t x i).2 upper h)

/-- Space, time, and height vary jointly in the strong L² topology, including the boundary height. -/
theorem continuous_directTrace_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directTrace q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have h0 := (continuous_cauchyTrace_joint upper).comp (continuous_snd.prodMk hd.fst)
  have h1 := (continuous_cauchyTrace_joint upper).comp (continuous_snd.prodMk hd.snd)
  exact h0.prodMk h1

/-- At positive exponential height the continuous trace is the actual horizontal holomorphic slice. -/
theorem directTrace_exp_eq_analyticSlice (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) (a : ℝ) :
    directTrace q t x i upper (Real.exp a) = directAnalyticSlice q t x i upper a :=
  Prod.ext (cauchySlice_eq_trace _ upper a).symm (cauchySlice_eq_trace _ upper a).symm

/-- The trace at height zero is exactly the constructed intrinsic Hardy boundary value. -/
theorem directTrace_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) (upper : Bool) :
    directTrace q t x i upper 0 =
      if upper then directUpperCorrection q t x i else directLowerCorrection q t x i := by
  cases upper
  · apply Prod.ext
    · exact (cauchyTrace_lower_zero _).trans (directRHDensity_lower_component q t x i 0)
    · exact (cauchyTrace_lower_zero _).trans (directRHDensity_lower_component q t x i 1)
  · apply Prod.ext
    · exact (cauchyTrace_upper_zero _).trans (directRHDensity_upper_component q t x i 0)
    · exact (cauchyTrace_upper_zero _).trans (directRHDensity_upper_component q t x i 1)

/-- The actual Plemelj boundary limit remains valid when space and time approach their limits simultaneously. -/
theorem directAnalyticSlice_joint_boundary_tendsto (q : SchwartzMap ℝ ℂ) (t x : ℝ)
    (i : Fin 2) (upper : Bool) :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => directAnalyticSlice q p.1.1 p.1.2 i upper p.2)
      ((𝓝 (t,x)) ×ˢ atBot)
      (𝓝 (if upper then directUpperCorrection q t x i else directLowerCorrection q t x i)) := by
  have hf : Tendsto (fun p : (ℝ × ℝ) × ℝ => (p.1,Real.exp p.2))
      ((𝓝 (t,x)) ×ˢ atBot) (𝓝 ((t,x),0)) :=
    tendsto_fst.prodMk_nhds (Real.tendsto_exp_atBot.comp tendsto_snd)
  have hh := ((continuous_directTrace_parameters q i upper).tendsto ((t,x),0)).comp hf
  change Tendsto (fun p : (ℝ × ℝ) × ℝ => directTrace q p.1.1 p.1.2 i upper (Real.exp p.2))
    ((𝓝 (t,x)) ×ˢ atBot) (𝓝 (directTrace q t x i upper 0)) at hh
  simpa only [directTrace_exp_eq_analyticSlice,directTrace_zero] using hh

end
end RHTower.FokasLenells
