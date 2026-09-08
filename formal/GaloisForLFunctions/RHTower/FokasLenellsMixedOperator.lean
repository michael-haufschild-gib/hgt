import GaloisForLFunctions.RHTower.FokasLenellsMixedDispersion
import GaloisForLFunctions.RHTower.FokasLenellsSpaceMultiplier

/-!
# Mixed dispersion of the actual jump and Cauchy operators

The reciprocal phase generators cancel on every L² vector. The nonlinear
diagonal jump term has no physical parameter dependence, so the mixed
derivative is precisely the original off-diagonal jump action. Its universal
operator bound is one third for the explicitly normalized potentials.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

theorem directTimeMultiplier_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    HasDerivAt (fun y => directTimeMultiplier q t y reverse u) (directMultiplier q t x reverse u) x := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun y z => directTimeSymbol q t y reverse z*(u : ℝ → ℂ) z)
    (fun y z => directSymbol q t y reverse z*(u : ℝ → ℂ) z)
    (fun y => memLp_mul_of_bound (directTimeSymbol_measurable q t y reverse)
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)) (directTimeSymbol_bound q t y reverse) u)
    (fun y => memLp_mul_of_bound (directSymbol_measurable q t y reverse) (by positivity) (directSymbol_bound q t y reverse) u)
    (fun z => (1/3 : ℝ)*‖(u : ℝ → ℂ) z‖) ((Lp.memLp u).norm.const_mul _)
  · exact Eventually.of_forall fun z y => (directTimeSymbol_space_hasDerivAt q t y reverse z).mul_const _
  · exact Eventually.of_forall fun z y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (directSymbol_bound q t y reverse z) (norm_nonneg _)

theorem directSpaceMultiplier_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    HasDerivAt (fun s => directSpaceMultiplier q s x reverse u) (directMultiplier q t x reverse u) t := by
  apply hasDerivAt_toLp_two_of_dominated volume
    (fun s z => directSpaceSymbol q s x reverse z*(u : ℝ → ℂ) z)
    (fun s z => directSymbol q s x reverse z*(u : ℝ → ℂ) z)
    (fun s => memLp_mul_of_bound (directSpaceSymbol_measurable q s x reverse)
      (directSpaceOperatorBudget_nonneg q) (directSpaceSymbol_uniform_bound q s x reverse) u)
    (fun s => memLp_mul_of_bound (directSymbol_measurable q s x reverse) (by positivity) (directSymbol_bound q s x reverse) u)
    (fun z => (1/3 : ℝ)*‖(u : ℝ → ℂ) z‖) ((Lp.memLp u).norm.const_mul _)
  · exact Eventually.of_forall fun z s => (directSpaceSymbol_time_hasDerivAt q s x reverse z).mul_const _
  · exact Eventually.of_forall fun z s => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (directSymbol_bound q s x reverse z) (norm_nonneg _)

/-- The mixed derivative retains exactly the off-diagonal jump action. -/
def directJumpMixedOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  ((-directMultiplier q t x false).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)).prod
    ((directMultiplier q t x true).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2))

theorem directJumpTimeOperator_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun y => directJumpTimeOperator q t y u) (directJumpMixedOperator q t x u) x :=
  (directTimeMultiplier_space_hasDerivAt q t x false u.2).neg.prodMk
    (directTimeMultiplier_space_hasDerivAt q t x true u.1)

theorem directJumpSpaceOperator_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directJumpSpaceOperator q s x u) (directJumpMixedOperator q t x u) t :=
  (directSpaceMultiplier_time_hasDerivAt q t x false u.2).neg.prodMk
    (directSpaceMultiplier_time_hasDerivAt q t x true u.1)

/-- The mixed generator has a universal bound independent of the potential's decay budgets. -/
theorem directJumpMixedOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directJumpMixedOperator q t x u‖ ≤ (1/3 : ℝ)*‖u‖ := by
  change max ‖-directMultiplier q t x false u.2‖ ‖directMultiplier q t x true u.1‖ ≤ _
  rw [max_le_iff,norm_neg]
  exact ⟨(directMultiplier_bound q t x false u.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le u) (by positivity)),
    (directMultiplier_bound q t x true u.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le u) (by positivity))⟩

/-- The parameter-independent nonlinear diagonal is the exact defect from the linear mixed equation. -/
theorem directJumpPerturbation_mixed_decomposition (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    directJumpPerturbation q t x u = directJumpMixedOperator q t x u +
      (0,-directMultiplier q 0 0 false (directMultiplier q 0 0 true u.2)) := by
  change (-directMultiplier q t x false u.2,
    directMultiplier q t x true u.1-directMultiplier q t x false (directMultiplier q t x true u.2)) = _
  rw [directMultiplier_product_invariant q t x 0 0]
  simp [directJumpMixedOperator,sub_eq_add_neg]

def directCauchyMixedOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  boundaryCauchy.comp (directJumpMixedOperator q t x)

theorem directCauchyTimeOperator_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun y => directCauchyTimeOperator q t y u) (directCauchyMixedOperator q t x u) x :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directJumpTimeOperator_space_hasDerivAt q t x u)

theorem directCauchySpaceOperator_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    HasDerivAt (fun s => directCauchySpaceOperator q s x u) (directCauchyMixedOperator q t x u) t :=
  (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directJumpSpaceOperator_time_hasDerivAt q t x u)

theorem directCauchyMixedOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directCauchyMixedOperator q t x u‖ ≤ (1/3 : ℝ)*‖u‖ :=
  (boundaryCauchy_bound _).trans (directJumpMixedOperator_bound q t x u)

/-- Mixed differentiation commutes for the actual Cauchy operator on every Hilbert-space vector. -/
theorem directCauchyOperator_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    deriv (fun y => deriv (fun s => directCauchyOperator q s y u) t) x =
      deriv (fun s => deriv (fun y => directCauchyOperator q s y u) x) t := by
  have ht : (fun y => deriv (fun s => directCauchyOperator q s y u) t) =
      fun y => directCauchyTimeOperator q t y u :=
    funext fun y => (directCauchyOperator_time_hasDerivAt q t y u).deriv
  have hx : (fun s => deriv (fun y => directCauchyOperator q s y u) x) =
      fun s => directCauchySpaceOperator q s x u :=
    funext fun s => (directCauchyOperator_space_hasDerivAt q s x u).deriv
  rw [ht,hx,(directCauchyTimeOperator_space_hasDerivAt q t x u).deriv,
    (directCauchySpaceOperator_time_hasDerivAt q t x u).deriv]

theorem continuous_directJumpMixedOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directJumpMixedOperator q p.1.1 p.1.2 p.2) := by
  have h1 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.2)) := continuous_fst.prodMk continuous_snd.snd
  have h2 : Continuous (fun p : (ℝ × ℝ) × Boundary => (p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have ha := (continuous_directMultiplier_joint q false).comp h1
  have hb := (continuous_directMultiplier_joint q true).comp h2
  exact ha.neg.prodMk hb

theorem continuous_directCauchyMixedOperator_joint (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : (ℝ × ℝ) × Boundary => directCauchyMixedOperator q p.1.1 p.1.2 p.2) :=
  boundaryCauchy.continuous.comp (continuous_directJumpMixedOperator_joint q)

end
end RHTower.FokasLenells
