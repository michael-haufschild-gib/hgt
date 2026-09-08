import GaloisForLFunctions.RHTower.FokasLenellsMixedInverse
import GaloisForLFunctions.RHTower.FokasLenellsMixedForcing
import GaloisForLFunctions.RHTower.FokasLenellsSpaceBoundary
import GaloisForLFunctions.RHTower.FokasLenellsTimeBoundary

/-!
# Mixed differentiation through the nonlinear reconstruction density

The actual inverse with moving jump forcing has commuting mixed derivatives.
The exact differentiated reconstruction density retains all four operator
product terms. The lower and upper derivatives retain their Hardy classes.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

def directLowerMixedCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directSolution q t x (directRHMixedForcing q t x i+
    directCauchyMixedOperator q t x (directLowerCorrection q t x i)+
    directCauchyTimeOperator q t x (directLowerSpaceCorrection q t x i)+
    directCauchySpaceOperator q t x (directLowerTimeCorrection q t x i))

theorem directLowerTimeCorrection_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun y => directLowerTimeCorrection q t y i) (directLowerMixedCorrection q t x i) x := by
  have hb : ∀ y, ‖(directCauchyTimeOperator q t y).restrictScalars ℝ‖ ≤
      (1/2 : ℝ)*regularReflectionFrequencyBudget q := by
    intro y
    exact ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)) (directCauchyTimeOperator_bound q t y)
  have hc : ∀ u, Continuous (fun y => (directCauchyTimeOperator q t y).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun y : ℝ => ((t,y),u)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hh := (continuous_directCauchyTimeOperator_joint q).comp hp
    exact hh
  have hi := hasDerivAt_strong_apply hb hc (directLowerCorrection_space_hasDerivAt q t x i)
    (directCauchyTimeOperator_space_hasDerivAt q t x (directLowerCorrection q t x i))
  have hg := (directRHTimeForcing_space_hasDerivAt q t x i).fun_add hi
  have hrb : ∀ y, ‖((directResolventUnit q t y)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro y
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound q t y)
  have hrc : ∀ u, Continuous (fun y => ((directResolventUnit q t y)⁻¹).val.restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun y : ℝ => ((t,y),u)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hh := (continuous_directSolution_joint q).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hrb hrc hg
    (directSolution_space_hasDerivAt q t x (directRHTimeForcing q t x i+
      directCauchyTimeOperator q t x (directLowerCorrection q t x i)))
  convert! hd using 1
  simp only [directLowerMixedCorrection,directLowerTimeCorrection,directSpaceSolution,directSolution,ContinuousLinearMap.coe_restrictScalars',map_add]
  abel

theorem directLowerSpaceCorrection_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directLowerSpaceCorrection q s x i) (directLowerMixedCorrection q t x i) t := by
  have hb : ∀ s, ‖(directCauchySpaceOperator q s x).restrictScalars ℝ‖ ≤ directSpaceOperatorBudget q := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (directSpaceOperatorBudget_nonneg q) (directCauchySpaceOperator_bound q s x)
  have hc : ∀ u, Continuous (fun s => (directCauchySpaceOperator q s x).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => ((s,x),u)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directCauchySpaceOperator_joint q).comp hp
    exact hh
  have hi := hasDerivAt_strong_apply hb hc (directLowerCorrection_time_hasDerivAt q t x i)
    (directCauchySpaceOperator_time_hasDerivAt q t x (directLowerCorrection q t x i))
  have hg := (directRHSpaceForcing_time_hasDerivAt q t x i).fun_add hi
  have hrb : ∀ s, ‖((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound q s x)
  have hrc : ∀ u, Continuous (fun s => ((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => ((s,x),u)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directSolution_joint q).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hrb hrc hg
    (directSolution_time_hasDerivAt q t x (directRHSpaceForcing q t x i+
      directCauchySpaceOperator q t x (directLowerCorrection q t x i)))
  convert! hd using 1
  simp only [directLowerMixedCorrection,directLowerSpaceCorrection,directTimeSolution,directSolution,ContinuousLinearMap.coe_restrictScalars',map_add]
  abel

theorem directLowerMixedCorrection_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directLowerMixedCorrection q t x i-directCauchyOperator q t x (directLowerMixedCorrection q t x i) =
      directRHMixedForcing q t x i+directCauchyMixedOperator q t x (directLowerCorrection q t x i)+
        directCauchyTimeOperator q t x (directLowerSpaceCorrection q t x i)+
        directCauchySpaceOperator q t x (directLowerTimeCorrection q t x i) :=
  directSolution_equation q t x _

theorem continuous_directLowerMixedCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directLowerMixedCorrection q p.1 p.2 i) := by
  have h0 := (continuous_directCauchyMixedOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerCorrection_parameters q i))
  have h1 := (continuous_directCauchyTimeOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerSpaceCorrection_parameters q i))
  have h2 := (continuous_directCauchySpaceOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerTimeCorrection_parameters q i))
  have hh := (continuous_directSolution_joint q).comp
    (continuous_id.prodMk ((((continuous_directRHMixedForcing_parameters q i).add h0).add h1).add h2))
  exact hh

def directRHMixedDensity (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directJumpMixedRow q t x i+
    ((directJumpPerturbation q t x (directLowerMixedCorrection q t x i)+
      directJumpSpaceOperator q t x (directLowerTimeCorrection q t x i))+
      (directJumpTimeOperator q t x (directLowerSpaceCorrection q t x i)+
        directJumpMixedOperator q t x (directLowerCorrection q t x i)))

theorem directRHTimeDensity_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun y => directRHTimeDensity q t y i) (directRHMixedDensity q t x i) x := by
  have hb : ∀ y, ‖(directJumpPerturbation q t y).restrictScalars ℝ‖ ≤ (4/9 : ℝ) := by
    intro y
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directJumpPerturbation_bound q t y)
  have hc : ∀ u, Continuous (fun y => (directJumpPerturbation q t y).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun y : ℝ => ((t,y),u)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hh := (continuous_directJumpPerturbation_joint q).comp hp
    exact hh
  have h1 := hasDerivAt_strong_apply hb hc (directLowerTimeCorrection_space_hasDerivAt q t x i)
    (directJumpPerturbation_space_hasDerivAt q t x (directLowerTimeCorrection q t x i))
  have htb : ∀ y, ‖(directJumpTimeOperator q t y).restrictScalars ℝ‖ ≤
      (1/2 : ℝ)*regularReflectionFrequencyBudget q := by
    intro y
    exact ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg q)) (directJumpTimeOperator_bound q t y)
  have htc : ∀ u, Continuous (fun y => (directJumpTimeOperator q t y).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun y : ℝ => ((t,y),u)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hh := (continuous_directJumpTimeOperator_joint q).comp hp
    exact hh
  have h2 := hasDerivAt_strong_apply htb htc (directLowerCorrection_space_hasDerivAt q t x i)
    (directJumpTimeOperator_space_hasDerivAt q t x (directLowerCorrection q t x i))
  exact (directJumpTimeRow_space_hasDerivAt q t x i).fun_add (h1.fun_add h2)

theorem directRHSpaceDensity_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHSpaceDensity q s x i) (directRHMixedDensity q t x i) t := by
  have hb : ∀ s, ‖(directJumpPerturbation q s x).restrictScalars ℝ‖ ≤ (4/9 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directJumpPerturbation_bound q s x)
  have hc : ∀ u, Continuous (fun s => (directJumpPerturbation q s x).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => ((s,x),u)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directJumpPerturbation_joint q).comp hp
    exact hh
  have h1 := hasDerivAt_strong_apply hb hc (directLowerSpaceCorrection_time_hasDerivAt q t x i)
    (directJumpPerturbation_time_hasDerivAt q t x (directLowerSpaceCorrection q t x i))
  have hxb : ∀ s, ‖(directJumpSpaceOperator q s x).restrictScalars ℝ‖ ≤ directSpaceOperatorBudget q := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (directSpaceOperatorBudget_nonneg q) (directJumpSpaceOperator_bound q s x)
  have hxc : ∀ u, Continuous (fun s => (directJumpSpaceOperator q s x).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => ((s,x),u)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directJumpSpaceOperator_joint q).comp hp
    exact hh
  have h2 := hasDerivAt_strong_apply hxb hxc (directLowerCorrection_time_hasDerivAt q t x i)
    (directJumpSpaceOperator_time_hasDerivAt q t x (directLowerCorrection q t x i))
  have hd := (directJumpSpaceRow_time_hasDerivAt q t x i).fun_add (h1.fun_add h2)
  convert! hd using 1
  simp only [directRHMixedDensity,ContinuousLinearMap.coe_restrictScalars']
  abel

theorem continuous_directRHMixedDensity_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHMixedDensity q p.1 p.2 i) := by
  have h0 := (continuous_directJumpPerturbation_joint q).comp
    (continuous_id.prodMk (continuous_directLowerMixedCorrection_parameters q i))
  have h1 := (continuous_directJumpSpaceOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerTimeCorrection_parameters q i))
  have h2 := (continuous_directJumpTimeOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerSpaceCorrection_parameters q i))
  have h3 := (continuous_directJumpMixedOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerCorrection_parameters q i))
  exact (continuous_directJumpMixedRow_parameters q i).add ((h0.add h1).add (h2.add h3))

def directUpperMixedCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directLowerMixedCorrection q t x i+directRHMixedDensity q t x i

theorem directUpperTimeCorrection_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun y => directUpperTimeCorrection q t y i) (directUpperMixedCorrection q t x i) x :=
  (directLowerTimeCorrection_space_hasDerivAt q t x i).fun_add (directRHTimeDensity_space_hasDerivAt q t x i)

theorem directUpperSpaceCorrection_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directUpperSpaceCorrection q s x i) (directUpperMixedCorrection q t x i) t :=
  (directLowerSpaceCorrection_time_hasDerivAt q t x i).fun_add (directRHSpaceDensity_time_hasDerivAt q t x i)

theorem continuous_directUpperMixedCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directUpperMixedCorrection q p.1 p.2 i) :=
  (continuous_directLowerMixedCorrection_parameters q i).add (continuous_directRHMixedDensity_parameters q i)

theorem directLowerMixedCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directLowerMixedCorrection q t x i) = -directLowerMixedCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directLowerTimeCorrection_space_hasDerivAt q t x i)
  change HasDerivAt (fun y => boundaryCauchy (directLowerTimeCorrection q t y i))
    (boundaryCauchy (directLowerMixedCorrection q t x i)) x at hd
  have he : (fun y => boundaryCauchy (directLowerTimeCorrection q t y i)) =
      fun y => -directLowerTimeCorrection q t y i := funext fun y => directLowerTimeCorrection_hardy q t y i
  rw [he] at hd
  exact hd.unique (directLowerTimeCorrection_space_hasDerivAt q t x i).neg

theorem directUpperMixedCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directUpperMixedCorrection q t x i) = 0 := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directUpperTimeCorrection_space_hasDerivAt q t x i)
  change HasDerivAt (fun y => boundaryCauchy (directUpperTimeCorrection q t y i))
    (boundaryCauchy (directUpperMixedCorrection q t x i)) x at hd
  have he : (fun y => boundaryCauchy (directUpperTimeCorrection q t y i)) =
      fun _ : ℝ => (0 : Boundary) := funext fun y => directUpperTimeCorrection_hardy q t y i
  rw [he] at hd
  exact hd.unique (hasDerivAt_const x (0 : Boundary))

theorem directRHMixedDensity_lower (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directRHMixedDensity q t x i) = directLowerMixedCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directRHTimeDensity_space_hasDerivAt q t x i)
  change HasDerivAt (fun y => boundaryCauchy (directRHTimeDensity q t y i))
    (boundaryCauchy (directRHMixedDensity q t x i)) x at hd
  have he : (fun y => boundaryCauchy (directRHTimeDensity q t y i)) =
      fun y => directLowerTimeCorrection q t y i := funext fun y => directRHTimeDensity_lower q t y i
  rw [he] at hd
  exact hd.unique (directLowerTimeCorrection_space_hasDerivAt q t x i)

theorem directRHMixedDensity_upper (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directRHMixedDensity q t x i+boundaryCauchy (directRHMixedDensity q t x i) = directUpperMixedCorrection q t x i := by
  rw [directRHMixedDensity_lower]
  exact add_comm _ _

theorem directLowerCorrection_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    deriv (fun y => deriv (fun s => directLowerCorrection q s y i) t) x =
      deriv (fun s => deriv (fun y => directLowerCorrection q s y i) x) t := by
  have ht : (fun y => deriv (fun s => directLowerCorrection q s y i) t) = fun y => directLowerTimeCorrection q t y i :=
    funext fun y => (directLowerCorrection_time_hasDerivAt q t y i).deriv
  have hx : (fun s => deriv (fun y => directLowerCorrection q s y i) x) = fun s => directLowerSpaceCorrection q s x i :=
    funext fun s => (directLowerCorrection_space_hasDerivAt q s x i).deriv
  rw [ht,hx,(directLowerTimeCorrection_space_hasDerivAt q t x i).deriv,
    (directLowerSpaceCorrection_time_hasDerivAt q t x i).deriv]

theorem directRHDensity_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    deriv (fun y => deriv (fun s => directRHDensity q s y i) t) x =
      deriv (fun s => deriv (fun y => directRHDensity q s y i) x) t := by
  have ht : (fun y => deriv (fun s => directRHDensity q s y i) t) = fun y => directRHTimeDensity q t y i :=
    funext fun y => (directRHDensity_time_hasDerivAt q t y i).deriv
  have hx : (fun s => deriv (fun y => directRHDensity q s y i) x) = fun s => directRHSpaceDensity q s x i :=
    funext fun s => (directRHDensity_space_hasDerivAt q s x i).deriv
  rw [ht,hx,(directRHTimeDensity_space_hasDerivAt q t x i).deriv,
    (directRHSpaceDensity_time_hasDerivAt q t x i).deriv]

theorem directUpperCorrection_mixed_commute (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    deriv (fun y => deriv (fun s => directUpperCorrection q s y i) t) x =
      deriv (fun s => deriv (fun y => directUpperCorrection q s y i) x) t := by
  have ht : (fun y => deriv (fun s => directUpperCorrection q s y i) t) = fun y => directUpperTimeCorrection q t y i :=
    funext fun y => (directUpperCorrection_time_hasDerivAt q t y i).deriv
  have hx : (fun s => deriv (fun y => directUpperCorrection q s y i) x) = fun s => directUpperSpaceCorrection q s x i :=
    funext fun s => (directUpperCorrection_space_hasDerivAt q s x i).deriv
  rw [ht,hx,(directUpperTimeCorrection_space_hasDerivAt q t x i).deriv,
    (directUpperSpaceCorrection_time_hasDerivAt q t x i).deriv]

end
end RHTower.FokasLenells
