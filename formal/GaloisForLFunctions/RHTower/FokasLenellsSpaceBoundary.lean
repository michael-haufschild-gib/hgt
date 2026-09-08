import GaloisForLFunctions.RHTower.FokasLenellsSpaceInverse
import GaloisForLFunctions.RHTower.FokasLenellsSpaceForcing
import GaloisForLFunctions.HTGeometry.KleinGordonDuhamelDerivative

/-!
# C¹ spatial regularity of the actual RH boundary problem

The Klein–Gordon strong product rule applies to the uniformly bounded Cauchy
inverse and the actual differentiable scattering forcing. It also
differentiates the reconstruction density. Both resulting boundary
derivatives remain in their Hardy classes and obey differentiated Plemelj
identities, with no regularity or invertibility assumptions supplied.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The lower boundary derivative solves the differentiated inverse problem. -/
def directLowerSpaceCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directSolution q t x (directRHSpaceForcing q t x i+
    directCauchySpaceOperator q t x (directLowerCorrection q t x i))

/-- The corpus's strong Klein–Gordon product rule differentiates the actual inverse with moving forcing. -/
theorem directLowerCorrection_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directLowerCorrection q t s i) (directLowerSpaceCorrection q t x i) x := by
  have hb : ∀ s, ‖((directResolventUnit q t s)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound q t s)
  have hc : ∀ d, Continuous (fun s => ((directResolventUnit q t s)⁻¹).val.restrictScalars ℝ d) := by
    intro d
    have hp : Continuous (fun s : ℝ => ((t,s),d)) := (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hh := (continuous_directSolution_joint q).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hb hc (directRHForcing_space_hasDerivAt q t x i)
    (directSolution_space_hasDerivAt q t x (directRHForcing q t x i))
  have he : directSolution q t x (directRHSpaceForcing q t x i)+
      directSpaceSolution q t x (directRHForcing q t x i) = directLowerSpaceCorrection q t x i := by
    change ((directResolventUnit q t x)⁻¹).val _+((directResolventUnit q t x)⁻¹).val _ =
      ((directResolventUnit q t x)⁻¹).val (_+_)
    rw [map_add]
    rfl
  rw [← he]
  exact hd

/-- The derivative obeys the same uniquely invertible Cauchy equation with explicit differentiated forcing. -/
theorem directLowerSpaceCorrection_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directLowerSpaceCorrection q t x i-directCauchyOperator q t x (directLowerSpaceCorrection q t x i) =
      directRHSpaceForcing q t x i+directCauchySpaceOperator q t x (directLowerCorrection q t x i) :=
  directSolution_equation q t x _

/-- The differentiated lower solution depends continuously on both physical parameters. -/
theorem continuous_directLowerSpaceCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directLowerSpaceCorrection q p.1 p.2 i) := by
  have hp := continuous_id.prodMk (continuous_directLowerCorrection_parameters q i)
  have hc := (continuous_directCauchySpaceOperator_joint q).comp hp
  have hf := (continuous_directRHSpaceForcing_parameters q i).add hc
  have hg := continuous_id.prodMk hf
  have hh := (continuous_directSolution_joint q).comp hg
  exact hh

/-- The reconstruction density derivative contains the forcing and both product-rule contributions. -/
def directRHSpaceDensity (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directJumpSpaceRow q t x i+(directJumpPerturbation q t x (directLowerSpaceCorrection q t x i)+
    directJumpSpaceOperator q t x (directLowerCorrection q t x i))

/-- Strong differentiation passes through the actual nonlinear-in-data reconstruction density. -/
theorem directRHDensity_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHDensity q t s i) (directRHSpaceDensity q t x i) x := by
  have hb : ∀ s, ‖(directJumpPerturbation q t s).restrictScalars ℝ‖ ≤ (4/9 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directJumpPerturbation_bound q t s)
  have hc : ∀ u, Continuous (fun s => (directJumpPerturbation q t s).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => (t,s)) := continuous_const.prodMk continuous_id
    have hh := (continuous_directJumpPerturbation_parameters q u).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hb hc (directLowerCorrection_space_hasDerivAt q t x i)
    (directJumpPerturbation_space_hasDerivAt q t x (directLowerCorrection q t x i))
  exact (directJumpRow_space_hasDerivAt q t x i).fun_add hd

/-- The derivative density remains jointly continuous in physical parameters. -/
theorem continuous_directRHSpaceDensity_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHSpaceDensity q p.1 p.2 i) := by
  have hp := continuous_id.prodMk (continuous_directLowerSpaceCorrection_parameters q i)
  have h1 := (continuous_directJumpPerturbation_joint q).comp hp
  have hq := continuous_id.prodMk (continuous_directLowerCorrection_parameters q i)
  have h2 := (continuous_directJumpSpaceOperator_joint q).comp hq
  have hh := (continuous_directJumpSpaceRow_parameters q i).add (h1.add h2)
  exact hh

def directUpperSpaceCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directLowerSpaceCorrection q t x i+directRHSpaceDensity q t x i

/-- Both sides of the actual RH boundary jump possess strong position derivatives. -/
theorem directUpperCorrection_space_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directUpperCorrection q t s i) (directUpperSpaceCorrection q t x i) x :=
  (directLowerCorrection_space_hasDerivAt q t x i).fun_add (directRHDensity_space_hasDerivAt q t x i)

theorem continuous_directUpperSpaceCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directUpperSpaceCorrection q p.1 p.2 i) :=
  (continuous_directLowerSpaceCorrection_parameters q i).add (continuous_directRHSpaceDensity_parameters q i)

/-- The lower correction is C¹ in the genuine L² topology. -/
theorem directLowerCorrection_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun x => directLowerCorrection q t x i) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directLowerCorrection_space_hasDerivAt q t x i).differentiableAt,?_⟩
  have he : deriv (fun x => directLowerCorrection q t x i) = fun x => directLowerSpaceCorrection q t x i :=
    funext fun x => (directLowerCorrection_space_hasDerivAt q t x i).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_directLowerSpaceCorrection_parameters q i).comp hc
  exact hh

/-- The reconstructed density is C¹ in position. -/
theorem directRHDensity_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun x => directRHDensity q t x i) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (directRHDensity_space_hasDerivAt q t x i).differentiableAt,?_⟩
  have he : deriv (fun x => directRHDensity q t x i) = fun x => directRHSpaceDensity q t x i :=
    funext fun x => (directRHDensity_space_hasDerivAt q t x i).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => (t,x)) := continuous_const.prodMk continuous_id
  have hh := (continuous_directRHSpaceDensity_parameters q i).comp hc
  exact hh

/-- The upper correction is C¹ in position. -/
theorem directUpperCorrection_space_contDiff (q : SchwartzMap ℝ ℂ) (t : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun x => directUpperCorrection q t x i) :=
  (directLowerCorrection_space_contDiff q t i).add (directRHDensity_space_contDiff q t i)

/-- Space differentiation preserves the lower Hardy class. -/
theorem directLowerSpaceCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directLowerSpaceCorrection q t x i) = -directLowerSpaceCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directLowerCorrection_space_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directLowerCorrection q t s i))
    (boundaryCauchy (directLowerSpaceCorrection q t x i)) x at hd
  have he : (fun s => boundaryCauchy (directLowerCorrection q t s i)) =
      fun s => -directLowerCorrection q t s i := funext fun s => directLowerCorrection_hardy q t s i
  rw [he] at hd
  exact hd.unique (directLowerCorrection_space_hasDerivAt q t x i).neg

/-- Space differentiation preserves the upper Hardy class. -/
theorem directUpperSpaceCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directUpperSpaceCorrection q t x i) = 0 := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directUpperCorrection_space_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directUpperCorrection q t s i))
    (boundaryCauchy (directUpperSpaceCorrection q t x i)) x at hd
  have he : (fun s => boundaryCauchy (directUpperCorrection q t s i)) =
      fun _ : ℝ => (0 : Boundary) := funext fun s => directUpperCorrection_hardy q t s i
  rw [he] at hd
  exact hd.unique (hasDerivAt_const x (0 : Boundary))

/-- The differentiated density reconstructs the lower boundary derivative through the same projection. -/
theorem directRHSpaceDensity_lower (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directRHSpaceDensity q t x i) = directLowerSpaceCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x
    (directRHDensity_space_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directRHDensity q t s i))
    (boundaryCauchy (directRHSpaceDensity q t x i)) x at hd
  have he : (fun s => boundaryCauchy (directRHDensity q t s i)) =
      fun s => directLowerCorrection q t s i := funext fun s => (directLowerCorrection_equation q t s i).symm
  rw [he] at hd
  exact hd.unique (directLowerCorrection_space_hasDerivAt q t x i)

/-- The differentiated Plemelj sum reconstructs the upper boundary derivative. -/
theorem directRHSpaceDensity_upper (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directRHSpaceDensity q t x i+boundaryCauchy (directRHSpaceDensity q t x i) = directUpperSpaceCorrection q t x i := by
  rw [directRHSpaceDensity_lower,directUpperSpaceCorrection,add_comm]

end
end RHTower.FokasLenells
