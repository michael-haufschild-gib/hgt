import GaloisForLFunctions.RHTower.FokasLenellsSpaceDifferentiability
import GaloisForLFunctions.RHTower.FokasLenellsTimeMultiplier

/-!
# Strong position derivatives of the actual Cauchy operator

The spatial generator becomes a bounded multiplier by the proved
spectral decay of the actual reflection data. Dominated L² differentiation applies to every
vector. Opposite scattering phases cancel in the diagonal product, leaving
only two off-diagonal derivative channels and a uniform bound.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

def directSpaceMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := volume) (directSpaceSymbol_measurable q t x reverse)
    (directSpaceOperatorBudget_nonneg q)
    (directSpaceSymbol_uniform_bound q t x reverse)

theorem directSpaceMultiplier_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    (directSpaceMultiplier q t x reverse u : ℝ → ℂ) =ᵐ[volume]
      (fun z => directSpaceSymbol q t x reverse z*(u : ℝ → ℂ) z) :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem directSpaceMultiplier_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    ‖directSpaceMultiplier q t x reverse u‖ ≤ (directSpaceOperatorBudget q)*‖u‖ := by
  exact ((directSpaceMultiplier q t x reverse).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_lpBoundedMulCLM_le _ _ _) (norm_nonneg u))

theorem directMultiplier_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    HasDerivAt (fun s => directMultiplier q t s reverse u) (directSpaceMultiplier q t x reverse u) x := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => directSymbol q t s reverse z*(u : ℝ → ℂ) z)
    (fun s z => directSpaceSymbol q t s reverse z*(u : ℝ → ℂ) z)
    (fun s => memLp_mul_of_bound (directSymbol_measurable q t s reverse) (by positivity) (directSymbol_bound q t s reverse) u)
    (fun s => memLp_mul_of_bound (directSpaceSymbol_measurable q t s reverse)
      (directSpaceOperatorBudget_nonneg q) (directSpaceSymbol_uniform_bound q t s reverse) u)
    (fun z => (directSpaceOperatorBudget q)*‖(u : ℝ → ℂ) z‖)
    ((Lp.memLp u).norm.const_mul _)
  · exact Eventually.of_forall fun z s => (directSymbol_space_hasDerivAt q t s reverse z).mul_const _
  · exact Eventually.of_forall fun z s => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (directSpaceSymbol_uniform_bound q t s reverse z) (norm_nonneg _)

theorem continuous_directSpaceMultiplier_parameters (q : SchwartzMap ℝ ℂ) (reverse : Bool) (u : SoninL2) :
    Continuous (fun p : ℝ × ℝ => directSpaceMultiplier q p.1 p.2 reverse u) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact tendsto_lpBoundedMulCLM_apply
    (fun s : ℝ × ℝ => directSpaceSymbol_measurable q s.1 s.2 reverse)
    (directSpaceSymbol_measurable q p.1 p.2 reverse)
    (directSpaceOperatorBudget_nonneg q)
    (fun s : ℝ × ℝ => directSpaceSymbol_uniform_bound q s.1 s.2 reverse)
    (directSpaceSymbol_uniform_bound q p.1 p.2 reverse)
    (fun z => (continuous_directSpaceSymbol_parameters q reverse z).tendsto p) u

theorem continuous_directSpaceMultiplier_joint (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Continuous (fun p : (ℝ × ℝ) × SoninL2 => directSpaceMultiplier q p.1.1 p.1.2 reverse p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨p,u⟩
  have h1 : Tendsto (fun v : (ℝ × ℝ) × SoninL2 => directSpaceMultiplier q v.1.1 v.1.2 reverse (v.2-u))
      (𝓝 (p,u)) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun v : (ℝ × ℝ) × SoninL2 =>
      (directSpaceOperatorBudget q)*‖v.2-u‖)
      (fun v => directSpaceMultiplier_bound q _ _ reverse _) ?_
    have h : Continuous (fun v : (ℝ × ℝ) × SoninL2 =>
      (directSpaceOperatorBudget q)*‖v.2-u‖) := by fun_prop
    simpa only [sub_self,norm_zero,mul_zero] using h.tendsto (p,u)
  have h2 := ((continuous_directSpaceMultiplier_parameters q reverse u).comp continuous_fst).tendsto (p,u)
  change Tendsto (fun v : (ℝ × ℝ) × SoninL2 => directSpaceMultiplier q v.1.1 v.1.2 reverse v.2)
    (𝓝 (p,u)) (𝓝 (directSpaceMultiplier q p.1 p.2 reverse u))
  simpa only [Function.comp_apply,← map_add,sub_add_cancel,zero_add] using h1.add h2

/-- Only the off-diagonal channels survive differentiation of the full jump action. -/
def directJumpSpaceOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  ((-directSpaceMultiplier q t x false).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)).prod
    ((directSpaceMultiplier q t x true).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2))

theorem directJumpPerturbation_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directJumpPerturbation q t s u) (directJumpSpaceOperator q t x u) x := by
  have he : (fun s => directJumpPerturbation q t s u) =
      fun s => (-directMultiplier q t s false u.2,
        directMultiplier q t s true u.1-directMultiplier q 0 0 false (directMultiplier q 0 0 true u.2)) := by
    funext s
    change (-directMultiplier q t s false u.2, directMultiplier q t s true u.1-
      directMultiplier q t s false (directMultiplier q t s true u.2)) = _
    rw [directMultiplier_product_invariant q t s 0 0]
  rw [he]
  have hd := (directMultiplier_space_hasDerivAt q t x true u.1).sub_const
    (directMultiplier q 0 0 false (directMultiplier q 0 0 true u.2))
  exact (directMultiplier_space_hasDerivAt q t x false u.2).neg.prodMk hd

theorem directJumpSpaceOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directJumpSpaceOperator q t x u‖ ≤ (directSpaceOperatorBudget q)*‖u‖ := by
  change max ‖-directSpaceMultiplier q t x false u.2‖ ‖directSpaceMultiplier q t x true u.1‖ ≤ _
  rw [max_le_iff,norm_neg]
  have h0 : 0 ≤ directSpaceOperatorBudget q := directSpaceOperatorBudget_nonneg q
  exact ⟨(directSpaceMultiplier_bound q t x false u.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le u) h0),
    (directSpaceMultiplier_bound q t x true u.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le u) h0)⟩

theorem continuous_directJumpSpaceOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directJumpSpaceOperator q p.1.1 p.1.2 p.2) := by
  have h1 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.2)) := continuous_fst.prodMk continuous_snd.snd
  have h2 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have ha := (continuous_directSpaceMultiplier_joint q false).comp h1
  have hb := (continuous_directSpaceMultiplier_joint q true).comp h2
  exact ha.neg.prodMk hb

def directCauchySpaceOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  boundaryCauchy.comp (directJumpSpaceOperator q t x)

theorem directCauchyOperator_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directCauchyOperator q t s u) (directCauchySpaceOperator q t x u) x :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x (directJumpPerturbation_space_hasDerivAt q t x u)

theorem directCauchySpaceOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directCauchySpaceOperator q t x u‖ ≤ (directSpaceOperatorBudget q)*‖u‖ :=
  (boundaryCauchy_bound _).trans (directJumpSpaceOperator_bound q t x u)

theorem continuous_directCauchySpaceOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directCauchySpaceOperator q p.1.1 p.1.2 p.2) :=
  boundaryCauchy.continuous.comp (continuous_directJumpSpaceOperator_joint q)

end
end RHTower.FokasLenells
