import GaloisForLFunctions.RHTower.FokasLenellsTimeDifferentiability

/-!
# Strong time derivatives of the actual Cauchy operator

The singular time generator becomes a bounded multiplier after the proved
zero-frequency cancellation. Dominated L² differentiation applies to every
vector. Opposite scattering phases cancel in the diagonal product, leaving
only two off-diagonal derivative channels and a sharp uniform bound.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

theorem directTimeSymbol_measurable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Measurable (directTimeSymbol q t x reverse) :=
  measurable_const.mul (regularInverseFrequencyJump_measurable q t x reverse)

def directTimeMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := volume) (directTimeSymbol_measurable q t x reverse)
    (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q))
    (directTimeSymbol_bound q t x reverse)

theorem directTimeMultiplier_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    (directTimeMultiplier q t x reverse u : ℝ → ℂ) =ᵐ[volume]
      (fun z => directTimeSymbol q t x reverse z*(u : ℝ → ℂ) z) :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem directTimeMultiplier_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    ‖directTimeMultiplier q t x reverse u‖ ≤ ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*‖u‖ := by
  exact ((directTimeMultiplier q t x reverse).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_lpBoundedMulCLM_le _ _ _) (norm_nonneg u))

theorem directMultiplier_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    HasDerivAt (fun s => directMultiplier q s x reverse u) (directTimeMultiplier q t x reverse u) t := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => directSymbol q s x reverse z*(u : ℝ → ℂ) z)
    (fun s z => directTimeSymbol q s x reverse z*(u : ℝ → ℂ) z)
    (fun s => memLp_mul_of_bound (directSymbol_measurable q s x reverse) (by positivity) (directSymbol_bound q s x reverse) u)
    (fun s => memLp_mul_of_bound (directTimeSymbol_measurable q s x reverse)
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)) (directTimeSymbol_bound q s x reverse) u)
    (fun z => ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*‖(u : ℝ → ℂ) z‖)
    ((Lp.memLp u).norm.const_mul _)
  · exact Eventually.of_forall fun z s => (directSymbol_time_hasDerivAt q s x reverse z).mul_const _
  · exact Eventually.of_forall fun z s => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (directTimeSymbol_bound q s x reverse z) (norm_nonneg _)

theorem continuous_directTimeMultiplier_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (u : SoninL2) :
    Continuous (fun p : ℝ × ℝ => directTimeMultiplier q p.1 p.2 reverse u) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_lpBoundedMulCLM_apply
    (fun s : ℝ × ℝ => directTimeSymbol_measurable q s.1 s.2 reverse)
    (directTimeSymbol_measurable q p.1 p.2 reverse)
    (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q))
    (fun s : ℝ × ℝ => directTimeSymbol_bound q s.1 s.2 reverse)
    (directTimeSymbol_bound q p.1 p.2 reverse)
    (fun z => (continuous_directTimeSymbol_parameters q reverse z).tendsto p) u

theorem continuous_directTimeMultiplier_joint (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : (ℝ × ℝ) × SoninL2 => directTimeMultiplier q p.1.1 p.1.2 reverse p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨p,u⟩
  have h1 : Tendsto (fun v : (ℝ × ℝ) × SoninL2 => directTimeMultiplier q v.1.1 v.1.2 reverse (v.2-u))
      (𝓝 (p,u)) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun v : (ℝ × ℝ) × SoninL2 =>
      ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*‖v.2-u‖)
      (fun v => directTimeMultiplier_bound q _ _ reverse _) ?_
    have h : Continuous (fun v : (ℝ × ℝ) × SoninL2 =>
      ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*‖v.2-u‖) := by fun_prop
    simpa only [sub_self,norm_zero,mul_zero] using h.tendsto (p,u)
  have h2 := ((continuous_directTimeMultiplier_parameters q reverse u).comp continuous_fst).tendsto (p,u)
  change Tendsto (fun v : (ℝ × ℝ) × SoninL2 => directTimeMultiplier q v.1.1 v.1.2 reverse v.2)
    (𝓝 (p,u)) (𝓝 (directTimeMultiplier q p.1 p.2 reverse u))
  simpa only [Function.comp_apply,← map_add,sub_add_cancel,zero_add] using h1.add h2

/-- Opposite time and position phases cancel in the actual diagonal multiplier. -/
theorem directMultiplier_product_invariant (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) (u : SoninL2) :
    directMultiplier q t x false (directMultiplier q t x true u) =
      directMultiplier q s y false (directMultiplier q s y true u) := by
  apply Lp.ext
  filter_upwards [directMultiplier_ae q t x false (directMultiplier q t x true u),
    directMultiplier_ae q t x true u,directMultiplier_ae q s y false (directMultiplier q s y true u),
    directMultiplier_ae q s y true u] with z h1 h2 h3 h4
  rw [h1,h2,h3,h4,← mul_assoc,← mul_assoc]
  change regularJumpReflection _ t x z*regularJumpReverseReflection _ t x z*_ =
    regularJumpReflection _ s y z*regularJumpReverseReflection _ s y z*_
  rw [regularJumpReflection_product,regularJumpReflection_product]

/-- Only the off-diagonal channels survive differentiation of the full jump action. -/
def directJumpTimeOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  ((-directTimeMultiplier q t x false).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)).prod
    ((directTimeMultiplier q t x true).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2))

theorem directJumpPerturbation_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directJumpPerturbation q s x u) (directJumpTimeOperator q t x u) t := by
  have he : (fun s => directJumpPerturbation q s x u) =
      fun s => (-directMultiplier q s x false u.2,
        directMultiplier q s x true u.1-directMultiplier q 0 0 false (directMultiplier q 0 0 true u.2)) := by
    funext s
    change (-directMultiplier q s x false u.2, directMultiplier q s x true u.1-
      directMultiplier q s x false (directMultiplier q s x true u.2)) = _
    rw [directMultiplier_product_invariant q s x 0 0]
  rw [he]
  have hd := (directMultiplier_time_hasDerivAt q t x true u.1).sub_const
    (directMultiplier q 0 0 false (directMultiplier q 0 0 true u.2))
  exact (directMultiplier_time_hasDerivAt q t x false u.2).neg.prodMk hd

theorem directJumpTimeOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directJumpTimeOperator q t x u‖ ≤ ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*‖u‖ := by
  change max ‖-directTimeMultiplier q t x false u.2‖ ‖directTimeMultiplier q t x true u.1‖ ≤ _
  rw [max_le_iff,norm_neg]
  have h0 : 0 ≤ (1/2 : ℝ)*regularReflectionFrequencyBudget q :=
    mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)
  exact ⟨(directTimeMultiplier_bound q t x false u.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le u) h0),
    (directTimeMultiplier_bound q t x true u.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le u) h0)⟩

theorem continuous_directJumpTimeOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directJumpTimeOperator q p.1.1 p.1.2 p.2) := by
  have h1 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.2)) := continuous_fst.prodMk continuous_snd.snd
  have h2 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have ha := (continuous_directTimeMultiplier_joint q false).comp h1
  have hb := (continuous_directTimeMultiplier_joint q true).comp h2
  exact ha.neg.prodMk hb

def directCauchyTimeOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  boundaryCauchy.comp (directJumpTimeOperator q t x)

theorem directCauchyOperator_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directCauchyOperator q s x u) (directCauchyTimeOperator q t x u) t :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (directJumpPerturbation_time_hasDerivAt q t x u)

theorem directCauchyTimeOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directCauchyTimeOperator q t x u‖ ≤ ((1/2 : ℝ)*regularReflectionFrequencyBudget q)*‖u‖ :=
  (boundaryCauchy_bound _).trans (directJumpTimeOperator_bound q t x u)

theorem continuous_directCauchyTimeOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directCauchyTimeOperator q p.1.1 p.1.2 p.2) :=
  boundaryCauchy.continuous.comp (continuous_directJumpTimeOperator_joint q)

end
end RHTower.FokasLenells
