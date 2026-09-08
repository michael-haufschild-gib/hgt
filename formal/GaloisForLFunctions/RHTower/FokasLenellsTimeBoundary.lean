import GaloisForLFunctions.RHTower.FokasLenellsTimeInverse
import GaloisForLFunctions.RHTower.FokasLenellsTimeForcing
import GaloisForLFunctions.HTGeometry.KleinGordonDuhamelDerivative

/-!
# C¹ time regularity of the actual RH boundary problem

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
def directLowerTimeCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directSolution q t x (directRHTimeForcing q t x i+
    directCauchyTimeOperator q t x (directLowerCorrection q t x i))

/-- The corpus's strong Klein–Gordon product rule differentiates the actual inverse with moving forcing. -/
theorem directLowerCorrection_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directLowerCorrection q s x i) (directLowerTimeCorrection q t x i) t := by
  have hb : ∀ s, ‖((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound q s x)
  have hc : ∀ d, Continuous (fun s => ((directResolventUnit q s x)⁻¹).val.restrictScalars ℝ d) := by
    intro d
    have hp : Continuous (fun s : ℝ => ((s,x),d)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directSolution_joint q).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hb hc (directRHForcing_time_hasDerivAt q t x i)
    (directSolution_time_hasDerivAt q t x (directRHForcing q t x i))
  have he : directSolution q t x (directRHTimeForcing q t x i)+
      directTimeSolution q t x (directRHForcing q t x i) = directLowerTimeCorrection q t x i := by
    change ((directResolventUnit q t x)⁻¹).val _+((directResolventUnit q t x)⁻¹).val _ =
      ((directResolventUnit q t x)⁻¹).val (_+_)
    rw [map_add]
    rfl
  rw [← he]
  exact hd

/-- The derivative obeys the same uniquely invertible Cauchy equation with explicit differentiated forcing. -/
theorem directLowerTimeCorrection_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directLowerTimeCorrection q t x i-directCauchyOperator q t x (directLowerTimeCorrection q t x i) =
      directRHTimeForcing q t x i+directCauchyTimeOperator q t x (directLowerCorrection q t x i) :=
  directSolution_equation q t x _

/-- The differentiated lower solution depends continuously on both physical parameters. -/
theorem continuous_directLowerTimeCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directLowerTimeCorrection q p.1 p.2 i) := by
  have hp := continuous_id.prodMk (continuous_directLowerCorrection_parameters q i)
  have hc := (continuous_directCauchyTimeOperator_joint q).comp hp
  have hf := (continuous_directRHTimeForcing_parameters q i).add hc
  have hg := continuous_id.prodMk hf
  have hh := (continuous_directSolution_joint q).comp hg
  exact hh

/-- The reconstruction density derivative contains the forcing and both product-rule contributions. -/
def directRHTimeDensity (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directJumpTimeRow q t x i+(directJumpPerturbation q t x (directLowerTimeCorrection q t x i)+
    directJumpTimeOperator q t x (directLowerCorrection q t x i))

/-- Strong differentiation passes through the actual nonlinear-in-data reconstruction density. -/
theorem directRHDensity_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHDensity q s x i) (directRHTimeDensity q t x i) t := by
  have hb : ∀ s, ‖(directJumpPerturbation q s x).restrictScalars ℝ‖ ≤ (4/9 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directJumpPerturbation_bound q s x)
  have hc : ∀ u, Continuous (fun s => (directJumpPerturbation q s x).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => (s,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_directJumpPerturbation_parameters q u).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hb hc (directLowerCorrection_time_hasDerivAt q t x i)
    (directJumpPerturbation_time_hasDerivAt q t x (directLowerCorrection q t x i))
  exact (directJumpRow_time_hasDerivAt q t x i).fun_add hd

/-- The derivative density remains jointly continuous in physical parameters. -/
theorem continuous_directRHTimeDensity_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directRHTimeDensity q p.1 p.2 i) := by
  have hp := continuous_id.prodMk (continuous_directLowerTimeCorrection_parameters q i)
  have h1 := (continuous_directJumpPerturbation_joint q).comp hp
  have hq := continuous_id.prodMk (continuous_directLowerCorrection_parameters q i)
  have h2 := (continuous_directJumpTimeOperator_joint q).comp hq
  have hh := (continuous_directJumpTimeRow_parameters q i).add (h1.add h2)
  exact hh

def directUpperTimeCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directLowerTimeCorrection q t x i+directRHTimeDensity q t x i

/-- Both sides of the actual RH boundary jump possess strong time derivatives. -/
theorem directUpperCorrection_time_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directUpperCorrection q s x i) (directUpperTimeCorrection q t x i) t :=
  (directLowerCorrection_time_hasDerivAt q t x i).fun_add (directRHDensity_time_hasDerivAt q t x i)

theorem continuous_directUpperTimeCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => directUpperTimeCorrection q p.1 p.2 i) :=
  (continuous_directLowerTimeCorrection_parameters q i).add (continuous_directRHTimeDensity_parameters q i)

/-- The lower correction is C¹ in the genuine L² topology. -/
theorem directLowerCorrection_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun t => directLowerCorrection q t x i) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directLowerCorrection_time_hasDerivAt q t x i).differentiableAt,?_⟩
  have he : deriv (fun t => directLowerCorrection q t x i) = fun t => directLowerTimeCorrection q t x i :=
    funext fun t => (directLowerCorrection_time_hasDerivAt q t x i).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_directLowerTimeCorrection_parameters q i).comp hc
  exact hh

/-- The reconstructed density is C¹ in time. -/
theorem directRHDensity_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun t => directRHDensity q t x i) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (directRHDensity_time_hasDerivAt q t x i).differentiableAt,?_⟩
  have he : deriv (fun t => directRHDensity q t x i) = fun t => directRHTimeDensity q t x i :=
    funext fun t => (directRHDensity_time_hasDerivAt q t x i).deriv
  rw [he]
  have hc : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_directRHTimeDensity_parameters q i).comp hc
  exact hh

/-- The upper correction is C¹ in time. -/
theorem directUpperCorrection_time_contDiff (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun t => directUpperCorrection q t x i) :=
  (directLowerCorrection_time_contDiff q x i).add (directRHDensity_time_contDiff q x i)

/-- Time differentiation preserves the lower Hardy class. -/
theorem directLowerTimeCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directLowerTimeCorrection q t x i) = -directLowerTimeCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directLowerCorrection_time_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directLowerCorrection q s x i))
    (boundaryCauchy (directLowerTimeCorrection q t x i)) t at hd
  have he : (fun s => boundaryCauchy (directLowerCorrection q s x i)) =
      fun s => -directLowerCorrection q s x i := funext fun s => directLowerCorrection_hardy q s x i
  rw [he] at hd
  exact hd.unique (directLowerCorrection_time_hasDerivAt q t x i).neg

/-- Time differentiation preserves the upper Hardy class. -/
theorem directUpperTimeCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directUpperTimeCorrection q t x i) = 0 := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directUpperCorrection_time_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directUpperCorrection q s x i))
    (boundaryCauchy (directUpperTimeCorrection q t x i)) t at hd
  have he : (fun s => boundaryCauchy (directUpperCorrection q s x i)) =
      fun _ : ℝ => (0 : Boundary) := funext fun s => directUpperCorrection_hardy q s x i
  rw [he] at hd
  exact hd.unique (hasDerivAt_const t (0 : Boundary))

/-- The differentiated density reconstructs the lower boundary derivative through the same projection. -/
theorem directRHTimeDensity_lower (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (directRHTimeDensity q t x i) = directLowerTimeCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directRHDensity_time_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directRHDensity q s x i))
    (boundaryCauchy (directRHTimeDensity q t x i)) t at hd
  have he : (fun s => boundaryCauchy (directRHDensity q s x i)) =
      fun s => directLowerCorrection q s x i := funext fun s => (directLowerCorrection_equation q s x i).symm
  rw [he] at hd
  exact hd.unique (directLowerCorrection_time_hasDerivAt q t x i)

/-- The differentiated Plemelj sum reconstructs the upper boundary derivative. -/
theorem directRHTimeDensity_upper (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    directRHTimeDensity q t x i+boundaryCauchy (directRHTimeDensity q t x i) = directUpperTimeCorrection q t x i := by
  rw [directRHTimeDensity_lower,directUpperTimeCorrection,add_comm]

end
end RHTower.FokasLenells
