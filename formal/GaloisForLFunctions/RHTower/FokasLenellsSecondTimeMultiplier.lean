import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeDifferentiability
import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeBounds

/-!
# Second strong time derivatives of the actual Cauchy operator

Odd projection builds compatible Schwartz data. Its bounded second-time
symbols act on every L2 vector and differentiate the original operator
family strongly. All physical-parameter and vector dependence is joint.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual second derivative represented in the Hilbert space. -/
def compatibleSecondTimeSymbolL2 (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 :=
  (directSecondTimeSymbol_oddInitialPart_memLp q t x reverse).toLp
    (directSecondTimeSymbol (oddInitialPart q) t x reverse)

theorem directTimeSymbolL2_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    HasDerivAt (fun s => directTimeSymbolL2 (oddInitialPart q) s x reverse)
      (compatibleSecondTimeSymbolL2 q t x reverse) t := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s => directTimeSymbol (oddInitialPart q) s x reverse)
    (fun s => directSecondTimeSymbol (oddInitialPart q) s x reverse)
    (fun s => directTimeSymbol_memLp _ s x reverse)
    (fun s => directSecondTimeSymbol_oddInitialPart_memLp q s x reverse)
    (fun z => ‖directSecondTimeSymbol (oddInitialPart q) 0 0 reverse z‖)
    (directSecondTimeSymbol_oddInitialPart_memLp q 0 0 reverse).norm
  · exact Eventually.of_forall fun z s => directTimeSymbol_time_hasDerivAt _ s x reverse z
  · exact Eventually.of_forall fun z s => by rw [directSecondTimeSymbol_norm,directSecondTimeSymbol_norm]

theorem continuous_compatibleSecondTimeSymbolL2_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : ℝ × ℝ => compatibleSecondTimeSymbolL2 q p.1 p.2 reverse) := by
  apply continuous_toLp_two_of_dominated volume
    (fun p : ℝ × ℝ => directSecondTimeSymbol (oddInitialPart q) p.1 p.2 reverse)
    (fun p => directSecondTimeSymbol_oddInitialPart_memLp q p.1 p.2 reverse)
    (fun z => ‖directSecondTimeSymbol (oddInitialPart q) 0 0 reverse z‖)
    (directSecondTimeSymbol_oddInitialPart_memLp q 0 0 reverse).norm
  · exact fun p => Eventually.of_forall fun z => by rw [directSecondTimeSymbol_norm,directSecondTimeSymbol_norm]
  · exact Eventually.of_forall fun z => continuous_directSecondTimeSymbol_parameters _ reverse z

theorem directSymbolL2_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (reverse : Bool) :
    ContDiff ℝ 2 (fun t => directSymbolL2 (oddInitialPart q) t x reverse) :=
  (directSymbolL2_time_contDiff_two_iff_memLp _ x reverse).2 (directSecondTimeSymbol_oddInitialPart_memLp q 0 x reverse)

/-- A bounded multiplier constructed from the genuine second derivative. -/
def compatibleSecondTimeMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := volume) (directSecondTimeSymbol_measurable _ t x reverse)
    (compatibleSecondTimeBudget_nonneg q reverse) (directSecondTimeSymbol_oddInitialPart_bound q t x reverse)

theorem compatibleSecondTimeMultiplier_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    (compatibleSecondTimeMultiplier q t x reverse u : ℝ → ℂ) =ᵐ[volume]
      (fun z => directSecondTimeSymbol (oddInitialPart q) t x reverse z*u z) :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem compatibleSecondTimeMultiplier_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    ‖compatibleSecondTimeMultiplier q t x reverse u‖ ≤ compatibleSecondTimeBudget q reverse*‖u‖ :=
  ((compatibleSecondTimeMultiplier q t x reverse).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_lpBoundedMulCLM_le _ _ _) (norm_nonneg u))

/-- Every fixed-vector first multiplier derivative has this genuine strong derivative. -/
theorem directTimeMultiplier_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    HasDerivAt (fun s => directTimeMultiplier (oddInitialPart q) s x reverse u)
      (compatibleSecondTimeMultiplier q t x reverse u) t := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => directTimeSymbol (oddInitialPart q) s x reverse z*u z)
    (fun s z => directSecondTimeSymbol (oddInitialPart q) s x reverse z*u z)
    (fun s => memLp_mul_of_bound (directTimeSymbol_measurable _ s x reverse)
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg _)) (directTimeSymbol_bound _ s x reverse) u)
    (fun s => memLp_mul_of_bound (directSecondTimeSymbol_measurable _ s x reverse)
      (compatibleSecondTimeBudget_nonneg q reverse) (directSecondTimeSymbol_oddInitialPart_bound q s x reverse) u)
    (fun z => compatibleSecondTimeBudget q reverse*‖u z‖) ((Lp.memLp u).norm.const_mul _)
  · exact Eventually.of_forall fun z s => (directTimeSymbol_time_hasDerivAt _ s x reverse z).mul_const _
  · exact Eventually.of_forall fun z s => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (directSecondTimeSymbol_oddInitialPart_bound q s x reverse z) (norm_nonneg _)

theorem continuous_compatibleSecondTimeMultiplier_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (u : SoninL2) :
    Continuous (fun p : ℝ × ℝ => compatibleSecondTimeMultiplier q p.1 p.2 reverse u) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_lpBoundedMulCLM_apply
    (fun s : ℝ × ℝ => directSecondTimeSymbol_measurable _ s.1 s.2 reverse)
    (directSecondTimeSymbol_measurable _ p.1 p.2 reverse) (compatibleSecondTimeBudget_nonneg q reverse)
    (fun s : ℝ × ℝ => directSecondTimeSymbol_oddInitialPart_bound q s.1 s.2 reverse)
    (directSecondTimeSymbol_oddInitialPart_bound q p.1 p.2 reverse)
    (fun z => (continuous_directSecondTimeSymbol_parameters (oddInitialPart q) reverse z).tendsto p) u

theorem continuous_compatibleSecondTimeMultiplier_joint (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : (ℝ × ℝ) × SoninL2 => compatibleSecondTimeMultiplier q p.1.1 p.1.2 reverse p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨p,u⟩
  have h1 : Tendsto (fun v : (ℝ × ℝ) × SoninL2 => compatibleSecondTimeMultiplier q v.1.1 v.1.2 reverse (v.2-u))
      (𝓝 (p,u)) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun v : (ℝ × ℝ) × SoninL2 => compatibleSecondTimeBudget q reverse*‖v.2-u‖)
      (fun v => compatibleSecondTimeMultiplier_bound q _ _ reverse _) ?_
    have h : Continuous (fun v : (ℝ × ℝ) × SoninL2 => compatibleSecondTimeBudget q reverse*‖v.2-u‖) := by fun_prop
    simpa only [sub_self,norm_zero,mul_zero] using h.tendsto (p,u)
  have h2 := ((continuous_compatibleSecondTimeMultiplier_parameters q reverse u).comp continuous_fst).tendsto (p,u)
  change Tendsto (fun v : (ℝ × ℝ) × SoninL2 => compatibleSecondTimeMultiplier q v.1.1 v.1.2 reverse v.2)
    (𝓝 (p,u)) (𝓝 (compatibleSecondTimeMultiplier q p.1 p.2 reverse u))
  simpa only [Function.comp_apply,← map_add,sub_add_cancel,zero_add] using h1.add h2

/-- The actual jump's second derivative retains only the two off-diagonal channels. -/
def compatibleJumpSecondTimeOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  ((-compatibleSecondTimeMultiplier q t x false).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)).prod
    ((compatibleSecondTimeMultiplier q t x true).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2))

theorem directJumpTimeOperator_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directJumpTimeOperator (oddInitialPart q) s x u)
      (compatibleJumpSecondTimeOperator q t x u) t :=
  (directTimeMultiplier_oddInitialPart_hasDerivAt q t x false u.2).neg.prodMk
    (directTimeMultiplier_oddInitialPart_hasDerivAt q t x true u.1)

def compatibleCauchySecondTimeBudget (q : SchwartzMap ℝ ℂ) : ℝ :=
  max (compatibleSecondTimeBudget q false) (compatibleSecondTimeBudget q true)

theorem compatibleCauchySecondTimeBudget_nonneg (q : SchwartzMap ℝ ℂ) :
    0 ≤ compatibleCauchySecondTimeBudget q :=
  (compatibleSecondTimeBudget_nonneg q false).trans (le_max_left _ _)

theorem compatibleJumpSecondTimeOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖compatibleJumpSecondTimeOperator q t x u‖ ≤ compatibleCauchySecondTimeBudget q*‖u‖ := by
  change max ‖-compatibleSecondTimeMultiplier q t x false u.2‖ ‖compatibleSecondTimeMultiplier q t x true u.1‖ ≤ _
  rw [max_le_iff,norm_neg]
  exact ⟨(compatibleSecondTimeMultiplier_bound q t x false u.2).trans
    (mul_le_mul (le_max_left _ _) (norm_snd_le u) (norm_nonneg _) (compatibleCauchySecondTimeBudget_nonneg q)),
    (compatibleSecondTimeMultiplier_bound q t x true u.1).trans
    (mul_le_mul (le_max_right _ _) (norm_fst_le u) (norm_nonneg _) (compatibleCauchySecondTimeBudget_nonneg q))⟩

theorem continuous_compatibleJumpSecondTimeOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => compatibleJumpSecondTimeOperator q p.1.1 p.1.2 p.2) := by
  have h1 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.2)) := continuous_fst.prodMk continuous_snd.snd
  have h2 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have ha := (continuous_compatibleSecondTimeMultiplier_joint q false).comp h1
  have hb := (continuous_compatibleSecondTimeMultiplier_joint q true).comp h2
  exact ha.neg.prodMk hb

def compatibleCauchySecondTimeOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  boundaryCauchy.comp (compatibleJumpSecondTimeOperator q t x)

theorem directCauchyTimeOperator_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directCauchyTimeOperator (oddInitialPart q) s x u)
      (compatibleCauchySecondTimeOperator q t x u) t :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (directJumpTimeOperator_oddInitialPart_hasDerivAt q t x u)

theorem compatibleCauchySecondTimeOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖compatibleCauchySecondTimeOperator q t x u‖ ≤ compatibleCauchySecondTimeBudget q*‖u‖ :=
  (boundaryCauchy_bound _).trans (compatibleJumpSecondTimeOperator_bound q t x u)

theorem continuous_compatibleCauchySecondTimeOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => compatibleCauchySecondTimeOperator q p.1.1 p.1.2 p.2) :=
  boundaryCauchy.continuous.comp (continuous_compatibleJumpSecondTimeOperator_joint q)

end
end RHTower.FokasLenells
