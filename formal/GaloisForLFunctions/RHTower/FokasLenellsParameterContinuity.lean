import GaloisForLFunctions.RHTower.FokasLenellsAnalyticRH
import GaloisForLFunctions.HTGeometry.FokasLenellsJumpContinuity
import GaloisForLFunctions.HTGeometry.L2DominatedContinuity
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Strong parameter continuity of the actual Fokas–Lenells inverse

The paper's Cauchy inverse mechanism combines with the corpus's dominated
L² continuity theorem and bounded multiplier convergence. The actual jump,
forcing, inverse solution, Hardy boundary corrections, and reconstruction
density vary continuously over the entire time-position plane. A quantitative
resolvent estimate needs only the change in the Cauchy operator applied to one
fixed solution. Every input potential is explicitly normalized Schwartz data;
there are no external smallness or invertibility assumptions.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem joint_continuity_of_uniform_bound {P X Y : Type*} [TopologicalSpace P]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : P → X →L[ℂ] Y) (M : ℝ) (hb : ∀ p u, ‖T p u‖ ≤ M*‖u‖)
    (hc : ∀ u, Continuous (fun p => T p u)) :
    Continuous (fun v : P × X => T v.1 v.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨p,u⟩
  have h1 : Tendsto (fun v : P × X => T v.1 (v.2-u)) (𝓝 (p,u)) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun v : P × X => M*‖v.2-u‖) (fun v => hb _ _) ?_
    have h : Continuous (fun v : P × X => M*‖v.2-u‖) := by fun_prop
    simpa only [sub_self,norm_zero,mul_zero] using h.tendsto (p,u)
  have h2 := ((hc u).comp continuous_fst).tendsto (p,u)
  have h3 := h1.add h2
  change Tendsto (fun v : P × X => T v.1 v.2) (𝓝 (p,u)) (𝓝 (T p u))
  simpa only [Function.comp_apply,← map_add,sub_add_cancel,zero_add] using h3

/-- The actual symbols vary continuously in both physical parameters at every spectral point. -/
theorem continuous_directSymbol_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    Continuous (fun p : ℝ × ℝ => directSymbol q p.1 p.2 reverse z) := by
  have hc : Continuous (fun p : ℝ × ℝ => (p.1,p.2,z)) := by fun_prop
  cases reverse
  · exact (continuous_globalSmall_regularJump_parameters q).1.comp hc
  · exact (continuous_globalSmall_regularJump_parameters q).2.comp hc

/-- Pointwise continuity and a uniform symbol bound give strong L² multiplier continuity. -/
theorem continuous_directMultiplier_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (u : SoninL2) :
    Continuous (fun p : ℝ × ℝ => directMultiplier q p.1 p.2 reverse u) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_lpBoundedMulCLM_apply
    (fun s : ℝ × ℝ => directSymbol_measurable q s.1 s.2 reverse)
    (directSymbol_measurable q p.1 p.2 reverse) (by positivity : (0:ℝ) ≤ 1/3)
    (fun s : ℝ × ℝ => directSymbol_bound q s.1 s.2 reverse)
    (directSymbol_bound q p.1 p.2 reverse)
    (fun z => (continuous_directSymbol_parameters q reverse z).tendsto p) u

/-- The multiplier remains continuous when its L² argument also varies. -/
theorem continuous_directMultiplier_joint (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : (ℝ × ℝ) × SoninL2 => directMultiplier q p.1.1 p.1.2 reverse p.2) :=
  joint_continuity_of_uniform_bound (fun p : ℝ × ℝ => directMultiplier q p.1 p.2 reverse) (1/3)
    (fun p => directMultiplier_bound q p.1 p.2 reverse) (continuous_directMultiplier_parameters q reverse)

/-- Products of the actual two symbols remain strongly continuous as jump operators. -/
theorem continuous_directJumpPerturbation_parameters (q : SchwartzMap ℝ ℂ) (u : Boundary) :
    Continuous (fun p : ℝ × ℝ => directJumpPerturbation q p.1 p.2 u) := by
  have ha := continuous_directMultiplier_parameters q false u.2
  have hb := continuous_directMultiplier_parameters q true u.1
  have hab := (continuous_directMultiplier_joint q false).comp
    (continuous_id.prodMk (continuous_directMultiplier_parameters q true u.2))
  exact ha.neg.prodMk (hb.sub hab)

theorem continuous_directJumpPerturbation_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directJumpPerturbation q p.1.1 p.1.2 p.2) :=
  joint_continuity_of_uniform_bound (fun p : ℝ × ℝ => directJumpPerturbation q p.1 p.2) (4/9)
    (fun p => directJumpPerturbation_bound q p.1 p.2) (continuous_directJumpPerturbation_parameters q)

theorem continuous_directCauchyOperator_parameters (q : SchwartzMap ℝ ℂ) (u : Boundary) :
    Continuous (fun p : ℝ × ℝ => directCauchyOperator q p.1 p.2 u) :=
  boundaryCauchy.continuous.comp (continuous_directJumpPerturbation_parameters q u)

/-- Dominated convergence upgrades joint pointwise jump continuity to continuity in L². -/
theorem continuous_directJumpEntry_parameters (q : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpEntry q p.1 p.2 i j) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => fun z => (regularJump (globalSmallScatteringPotential q) p.1 p.2 z-1) i j)
    (fun p => globalSmall_regularJump_sub_one_memLp q p.1 p.2 i j)
    (regularJumpL2Envelope q) (regularJumpL2Envelope_memLp q)
  · intro p
    exact Filter.Eventually.of_forall fun z => regularJump_sub_one_envelope q p.1 p.2 z i j
  · refine Filter.Eventually.of_forall fun z => ?_
    exact ((continuous_globalSmall_regularJumpMatrix_entry q i j).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1,p.2,z)) by fun_prop)).sub continuous_const

theorem continuous_directJumpRow_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directJumpRow q p.1 p.2 i) :=
  (continuous_directJumpEntry_parameters q i 0).prodMk (continuous_directJumpEntry_parameters q i 1)

theorem continuous_directRHForcing_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHForcing q p.1 p.2 i) :=
  boundaryCauchy.continuous.comp (continuous_directJumpRow_parameters q i)

/-- Perturbing both physical parameters and forcing requires only one fixed-vector operator difference. -/
theorem directSolution_parameter_stability (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (d e : Boundary) :
    ‖directSolution q t x d-directSolution q s y e‖ ≤ (9/5 : ℝ)*
      (‖d-e‖+‖directCauchyOperator q t x (directSolution q s y e)-
        directCauchyOperator q s y (directSolution q s y e)‖) := by
  let u := directSolution q t x d
  let v := directSolution q s y e
  have he : u-v = (d-e)+directCauchyOperator q t x (u-v)+
      (directCauchyOperator q t x v-directCauchyOperator q s y v) := by
    calc
      u-v = (d+directCauchyOperator q t x u)-(e+directCauchyOperator q s y v) :=
        congrArg₂ (·-·) ((sub_eq_iff_eq_add).mp (directSolution_equation q t x d))
          ((sub_eq_iff_eq_add).mp (directSolution_equation q s y e))
      _ = _ := by rw [map_sub]; abel
  have hn : ‖u-v‖ ≤ ‖d-e‖+‖directCauchyOperator q t x (u-v)‖+
      ‖directCauchyOperator q t x v-directCauchyOperator q s y v‖ := by
    calc
      _ = ‖(d-e)+directCauchyOperator q t x (u-v)+
          (directCauchyOperator q t x v-directCauchyOperator q s y v)‖ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hb := directCauchyOperator_bound q t x (u-v)
  change ‖u-v‖ ≤ _
  linarith

/-- The actual inverse depends jointly continuously on time, position, and arbitrary L² forcing. -/
theorem continuous_directSolution_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directSolution q p.1.1 p.1.2 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨⟨t,x⟩,d⟩
  let u := directSolution q t x d
  have hc : Continuous (fun p : (ℝ × ℝ) × Boundary => (9/5 : ℝ)*
      (‖p.2-d‖+‖directCauchyOperator q p.1.1 p.1.2 u-directCauchyOperator q t x u‖)) :=
    continuous_const.mul (((continuous_snd.sub continuous_const).norm).add
      (((continuous_directCauchyOperator_parameters q u).comp continuous_fst).sub continuous_const).norm)
  have hlim : Tendsto (fun p : (ℝ × ℝ) × Boundary => directSolution q p.1.1 p.1.2 p.2-u)
      (𝓝 ((t,x),d)) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun p : (ℝ × ℝ) × Boundary => (9/5 : ℝ)*
      (‖p.2-d‖+‖directCauchyOperator q p.1.1 p.1.2 u-directCauchyOperator q t x u‖))
      (fun p => directSolution_parameter_stability q p.1.1 p.1.2 t x p.2 d) ?_
    simpa only [sub_self,norm_zero,add_zero,mul_zero] using hc.tendsto ((t,x),d)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_zero] using hlim.norm

/-- The lower Hardy correction varies continuously in L² over all physical parameters. -/
theorem continuous_directLowerCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directLowerCorrection q p.1 p.2 i) := by
  change Continuous (fun p : ℝ × ℝ => directSolution q p.1 p.2 (directRHForcing q p.1 p.2 i))
  have hc : Continuous (fun p : ℝ × ℝ => (p,directRHForcing q p.1 p.2 i)) :=
    continuous_id.prodMk (continuous_directRHForcing_parameters q i)
  have hh := (continuous_directSolution_joint q).comp hc
  exact hh

/-- The Cauchy reconstruction density is a continuous L²-valued function of space and time. -/
theorem continuous_directRHDensity_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHDensity q p.1 p.2 i) := by
  change Continuous (fun p : ℝ × ℝ => directJumpRow q p.1 p.2 i+
    directJumpPerturbation q p.1 p.2 (directLowerCorrection q p.1 p.2 i))
  have hc : Continuous (fun p : ℝ × ℝ => (p,directLowerCorrection q p.1 p.2 i)) :=
    continuous_id.prodMk (continuous_directLowerCorrection_parameters q i)
  have hh := (continuous_directJumpPerturbation_joint q).comp hc
  have he := (continuous_directJumpRow_parameters q i).add hh
  exact he

theorem continuous_directUpperCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directUpperCorrection q p.1 p.2 i) :=
  (continuous_directLowerCorrection_parameters q i).add (continuous_directRHDensity_parameters q i)

/-- Both normalized Hardy corrections are continuous in the L² product space. -/
theorem continuous_directBoundaryPair_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => (directLowerCorrection q p.1 p.2 i,directUpperCorrection q p.1 p.2 i)) :=
  (continuous_directLowerCorrection_parameters q i).prodMk (continuous_directUpperCorrection_parameters q i)

/-- Every reconstructed matrix entry is continuous in space and time at every off-contour point. -/
theorem continuous_directAnalyticMatrix_parameters (q : SchwartzMap ℝ ℂ)
    (upper : Bool) (r a : ℝ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directAnalyticMatrix q p.1 p.2 (halfPlanePoint upper r a) i j) := by
  have hc : Continuous (fun p : ℝ × ℝ => boundaryComponent (directRHDensity q p.1 p.2 i) j) := by
    fin_cases j
    · exact (continuous_directRHDensity_parameters q i).fst
    · exact (continuous_directRHDensity_parameters q i).snd
  have he := (continuous_const (y := (1 : Matrix (Fin 2) (Fin 2) ℂ) i j)).add
    ((cauchyEvaluation upper r a).continuous.comp hc)
  change Continuous (fun p : ℝ × ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i j+
    cauchyEvaluation upper r a (boundaryComponent (directRHDensity q p.1 p.2 i) j)) at he
  simpa only [cauchyEvaluation_apply,directAnalyticMatrix] using he


/-- Height and L² input may vary simultaneously in the damped Hardy multiplier. -/
theorem continuous_dampedCauchyDatum_joint (upper : Bool) :
    Continuous (fun p : ℝ × SoninL2 => dampedCauchyDatum upper p.1 p.2) :=
  joint_continuity_of_uniform_bound (dampedCauchyDatum upper) 1
    (fun h u => by simpa only [one_mul] using dampedCauchyDatum_bound upper h u)
    (continuous_dampedCauchyDatum upper)

/-- Strong Cauchy traces are jointly continuous in height and their boundary density, including height zero. -/
theorem continuous_cauchyTrace_joint (upper : Bool) :
    Continuous (fun p : ℝ × SoninL2 => cauchyTrace p.2 upper p.1) := by
  have hc : Continuous (fun p : ℝ × SoninL2 => (p.1,fourierUnitary.symm p.2)) :=
    continuous_fst.prodMk (fourierUnitary.symm.continuous.comp continuous_snd)
  have hm := (continuous_dampedCauchyDatum_joint upper).comp hc
  exact (fourierUnitary.continuous.comp hm).const_smul (if upper then (1:ℂ) else -1)

/-- Actual horizontal Cauchy slices vary jointly with their logarithmic height and L² input. -/
theorem continuous_cauchySlice_joint (upper : Bool) :
    Continuous (fun p : ℝ × SoninL2 => cauchySlice p.2 upper p.1) := by
  have hc : Continuous (fun p : ℝ × SoninL2 => (Real.exp p.1,p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  have hh := (continuous_cauchyTrace_joint upper).comp hc
  change Continuous (fun p : ℝ × SoninL2 => cauchyTrace p.2 upper (Real.exp p.1)) at hh
  simpa only [cauchySlice_eq_trace] using hh

/-- The reconstructed analytic slices depend continuously on time, position, and height in the L² norm. -/
theorem continuous_directAnalyticSlice_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) (upper : Bool) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => directAnalyticSlice q p.1.1 p.1.2 i upper p.2) := by
  have hd := (continuous_directRHDensity_parameters q i).comp (continuous_fst (X := ℝ × ℝ) (Y := ℝ))
  have hc0 := (continuous_cauchySlice_joint upper).comp (continuous_snd.prodMk hd.fst)
  have hc1 := (continuous_cauchySlice_joint upper).comp (continuous_snd.prodMk hd.snd)
  exact hc0.prodMk hc1

end
end RHTower.FokasLenells
