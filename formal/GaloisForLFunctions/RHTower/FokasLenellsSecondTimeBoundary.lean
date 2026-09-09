import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeForcing
import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeInverse
import GaloisForLFunctions.RHTower.FokasLenellsTimeBoundary

/-!
# Second time derivatives of the actual RH boundary solution

The compatible jump and inverse give a second derivative of the actual
solution with its moving forcing, then of the reconstruction density and
both boundary values. Differentiation preserves their Hardy identities.
-/

open MeasureTheory Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual second boundary derivative solves the twice differentiated Cauchy equation. -/
def compatibleLowerSecondTimeCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  directSolution (oddInitialPart q) t x
    (compatibleRHSecondTimeForcing q t x i+
      compatibleCauchySecondTimeOperator q t x (directLowerCorrection (oddInitialPart q) t x i)+
      directCauchyTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i)+
      directCauchyTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i))

theorem directLowerTimeCorrection_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directLowerTimeCorrection (oddInitialPart q) s x i)
      (compatibleLowerSecondTimeCorrection q t x i) t := by
  have hbC : ∀ s, ‖(directCauchyTimeOperator (oddInitialPart q) s x).restrictScalars ℝ‖ ≤
      (1/2 : ℝ)*regularReflectionFrequencyBudget (oddInitialPart q) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg _)) (directCauchyTimeOperator_bound _ s x)
  have hcC : ∀ d, Continuous (fun s => (directCauchyTimeOperator (oddInitialPart q) s x).restrictScalars ℝ d) := by
    intro d
    have hp : Continuous (fun s : ℝ => ((s,x),d)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directCauchyTimeOperator_joint (oddInitialPart q)).comp hp
    exact hh
  have hC := hasDerivAt_strong_apply hbC hcC (directLowerCorrection_time_hasDerivAt (oddInitialPart q) t x i)
    (directCauchyTimeOperator_oddInitialPart_hasDerivAt q t x (directLowerCorrection (oddInitialPart q) t x i))
  have hF := (directRHTimeForcing_oddInitialPart_hasDerivAt q t x i).fun_add hC
  have hbR : ∀ s, ‖((directResolventUnit (oddInitialPart q) s x)⁻¹).val.restrictScalars ℝ‖ ≤ (9/5 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directSolution_bound _ s x)
  have hcR : ∀ d, Continuous (fun s => ((directResolventUnit (oddInitialPart q) s x)⁻¹).val.restrictScalars ℝ d) := by
    intro d
    have hp : Continuous (fun s : ℝ => ((s,x),d)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directSolution_joint (oddInitialPart q)).comp hp
    exact hh
  have hd := hasDerivAt_strong_apply hbR hcR hF (directSolution_time_hasDerivAt (oddInitialPart q) t x
    (directRHTimeForcing (oddInitialPart q) t x i+
      directCauchyTimeOperator (oddInitialPart q) t x (directLowerCorrection (oddInitialPart q) t x i)))
  have he : directSolution (oddInitialPart q) t x
      (compatibleRHSecondTimeForcing q t x i+
        (directCauchyTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i)+
          compatibleCauchySecondTimeOperator q t x (directLowerCorrection (oddInitialPart q) t x i)))+
      directTimeSolution (oddInitialPart q) t x
        (directRHTimeForcing (oddInitialPart q) t x i+
          directCauchyTimeOperator (oddInitialPart q) t x (directLowerCorrection (oddInitialPart q) t x i)) =
      compatibleLowerSecondTimeCorrection q t x i := by
    change ((directResolventUnit (oddInitialPart q) t x)⁻¹).val _+
      ((directResolventUnit (oddInitialPart q) t x)⁻¹).val _ =
      ((directResolventUnit (oddInitialPart q) t x)⁻¹).val _
    rw [← map_add]
    congr 1
    change _ + directCauchyTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i) = _
    abel
  rw [← he]
  exact hd

theorem compatibleLowerSecondTimeCorrection_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    compatibleLowerSecondTimeCorrection q t x i-
      directCauchyOperator (oddInitialPart q) t x (compatibleLowerSecondTimeCorrection q t x i) =
      compatibleRHSecondTimeForcing q t x i+
        compatibleCauchySecondTimeOperator q t x (directLowerCorrection (oddInitialPart q) t x i)+
        directCauchyTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i)+
        directCauchyTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i) :=
  directSolution_equation _ t x _

theorem continuous_compatibleLowerSecondTimeCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleLowerSecondTimeCorrection q p.1 p.2 i) := by
  have h1 := (continuous_compatibleCauchySecondTimeOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerCorrection_parameters (oddInitialPart q) i))
  have h2 := (continuous_directCauchyTimeOperator_joint (oddInitialPart q)).comp
    (continuous_id.prodMk (continuous_directLowerTimeCorrection_parameters (oddInitialPart q) i))
  have hf := (((continuous_compatibleRHSecondTimeForcing_parameters q i).add h1).add h2).add h2
  have hh := (continuous_directSolution_joint (oddInitialPart q)).comp (continuous_id.prodMk hf)
  exact hh

/-- The actual second reconstruction density contains all four product-rule terms. -/
def compatibleRHSecondTimeDensity (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  compatibleJumpSecondTimeRow q t x i+
    ((directJumpPerturbation (oddInitialPart q) t x (compatibleLowerSecondTimeCorrection q t x i)+
      directJumpTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i))+
    (directJumpTimeOperator (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i)+
      compatibleJumpSecondTimeOperator q t x (directLowerCorrection (oddInitialPart q) t x i)))

theorem directRHTimeDensity_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directRHTimeDensity (oddInitialPart q) s x i) (compatibleRHSecondTimeDensity q t x i) t := by
  have hb : ∀ s, ‖(directJumpPerturbation (oddInitialPart q) s x).restrictScalars ℝ‖ ≤ (4/9 : ℝ) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) (directJumpPerturbation_bound _ s x)
  have hc : ∀ u, Continuous (fun s => (directJumpPerturbation (oddInitialPart q) s x).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => (s,x)) := continuous_id.prodMk continuous_const
    have hh := (continuous_directJumpPerturbation_parameters (oddInitialPart q) u).comp hp
    exact hh
  have h1 := hasDerivAt_strong_apply hb hc (directLowerTimeCorrection_oddInitialPart_hasDerivAt q t x i)
    (directJumpPerturbation_time_hasDerivAt (oddInitialPart q) t x (directLowerTimeCorrection (oddInitialPart q) t x i))
  have hb2 : ∀ s, ‖(directJumpTimeOperator (oddInitialPart q) s x).restrictScalars ℝ‖ ≤
      (1/2 : ℝ)*regularReflectionFrequencyBudget (oddInitialPart q) := by
    intro s
    exact ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (by positivity) (regularReflectionFrequencyBudget_nonneg _)) (directJumpTimeOperator_bound _ s x)
  have hc2 : ∀ u, Continuous (fun s => (directJumpTimeOperator (oddInitialPart q) s x).restrictScalars ℝ u) := by
    intro u
    have hp : Continuous (fun s : ℝ => ((s,x),u)) := (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hh := (continuous_directJumpTimeOperator_joint (oddInitialPart q)).comp hp
    exact hh
  have h2 := hasDerivAt_strong_apply hb2 hc2 (directLowerCorrection_time_hasDerivAt (oddInitialPart q) t x i)
    (directJumpTimeOperator_oddInitialPart_hasDerivAt q t x (directLowerCorrection (oddInitialPart q) t x i))
  exact (directJumpTimeRow_oddInitialPart_hasDerivAt q t x i).fun_add (h1.fun_add h2)

theorem continuous_compatibleRHSecondTimeDensity_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleRHSecondTimeDensity q p.1 p.2 i) := by
  have h1 := (continuous_directJumpPerturbation_joint (oddInitialPart q)).comp
    (continuous_id.prodMk (continuous_compatibleLowerSecondTimeCorrection_parameters q i))
  have h2 := (continuous_directJumpTimeOperator_joint (oddInitialPart q)).comp
    (continuous_id.prodMk (continuous_directLowerTimeCorrection_parameters (oddInitialPart q) i))
  have h3 := (continuous_compatibleJumpSecondTimeOperator_joint q).comp
    (continuous_id.prodMk (continuous_directLowerCorrection_parameters (oddInitialPart q) i))
  have hh := (continuous_compatibleJumpSecondTimeRow_parameters q i).add ((h1.add h2).add (h2.add h3))
  exact hh

def compatibleUpperSecondTimeCorrection (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) : Boundary :=
  compatibleLowerSecondTimeCorrection q t x i+compatibleRHSecondTimeDensity q t x i

theorem directUpperTimeCorrection_oddInitialPart_hasDerivAt (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => directUpperTimeCorrection (oddInitialPart q) s x i) (compatibleUpperSecondTimeCorrection q t x i) t :=
  (directLowerTimeCorrection_oddInitialPart_hasDerivAt q t x i).fun_add (directRHTimeDensity_oddInitialPart_hasDerivAt q t x i)

theorem continuous_compatibleUpperSecondTimeCorrection_parameters (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => compatibleUpperSecondTimeCorrection q p.1 p.2 i) :=
  (continuous_compatibleLowerSecondTimeCorrection_parameters q i).add (continuous_compatibleRHSecondTimeDensity_parameters q i)

private theorem contDiff_two_of_strong_derivatives {f g h : ℝ → Boundary}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t) (hh : Continuous h) :
    ContDiff ℝ 2 f := by
  have he : deriv f = g := funext fun t => (hf t).deriv
  change ContDiff ℝ (1+1) f
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun t => (hf t).differentiableAt,by simp,?_⟩
  rw [he]
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hg t).differentiableAt,?_⟩
  have he2 : deriv g = h := funext fun t => (hg t).deriv
  rw [he2]
  exact hh

/-- The actual solved lower RH boundary value has a genuine global C2 time curve. -/
theorem directLowerCorrection_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 2 (fun t => directLowerCorrection (oddInitialPart q) t x i) := by
  apply contDiff_two_of_strong_derivatives
    (fun t => directLowerCorrection_time_hasDerivAt _ t x i)
    (fun t => directLowerTimeCorrection_oddInitialPart_hasDerivAt q t x i)
  have hp : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_compatibleLowerSecondTimeCorrection_parameters q i).comp hp
  exact hh

/-- The complete reconstruction density inherits global C2 time regularity. -/
theorem directRHDensity_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 2 (fun t => directRHDensity (oddInitialPart q) t x i) := by
  apply contDiff_two_of_strong_derivatives
    (fun t => directRHDensity_time_hasDerivAt _ t x i)
    (fun t => directRHTimeDensity_oddInitialPart_hasDerivAt q t x i)
  have hp : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_compatibleRHSecondTimeDensity_parameters q i).comp hp
  exact hh

/-- Both sides of the actual compatible RH jump are globally C2 in time. -/
theorem directUpperCorrection_oddInitialPart_time_contDiff_two (q : SchwartzMap ℝ ℂ) (x : ℝ) (i : Fin 2) :
    ContDiff ℝ 2 (fun t => directUpperCorrection (oddInitialPart q) t x i) := by
  apply contDiff_two_of_strong_derivatives
    (fun t => directUpperCorrection_time_hasDerivAt _ t x i)
    (fun t => directUpperTimeCorrection_oddInitialPart_hasDerivAt q t x i)
  have hp : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have hh := (continuous_compatibleUpperSecondTimeCorrection_parameters q i).comp hp
  exact hh

/-- Second time differentiation preserves the lower Hardy subspace. -/
theorem compatibleLowerSecondTimeCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (compatibleLowerSecondTimeCorrection q t x i) = -compatibleLowerSecondTimeCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directLowerTimeCorrection_oddInitialPart_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directLowerTimeCorrection (oddInitialPart q) s x i))
    (boundaryCauchy (compatibleLowerSecondTimeCorrection q t x i)) t at hd
  have he : (fun s => boundaryCauchy (directLowerTimeCorrection (oddInitialPart q) s x i)) =
      fun s => -directLowerTimeCorrection (oddInitialPart q) s x i := funext fun s => directLowerTimeCorrection_hardy _ s x i
  rw [he] at hd
  exact hd.unique (directLowerTimeCorrection_oddInitialPart_hasDerivAt q t x i).neg

theorem compatibleUpperSecondTimeCorrection_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (compatibleUpperSecondTimeCorrection q t x i) = 0 := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directUpperTimeCorrection_oddInitialPart_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directUpperTimeCorrection (oddInitialPart q) s x i))
    (boundaryCauchy (compatibleUpperSecondTimeCorrection q t x i)) t at hd
  have he : (fun s => boundaryCauchy (directUpperTimeCorrection (oddInitialPart q) s x i)) =
      fun _ : ℝ => (0 : Boundary) := funext fun s => directUpperTimeCorrection_hardy _ s x i
  rw [he] at hd
  exact hd.unique (hasDerivAt_const t (0 : Boundary))

/-- The second density reconstructs the second lower boundary derivative by the same Cauchy projection. -/
theorem compatibleRHSecondTimeDensity_lower (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    boundaryCauchy (compatibleRHSecondTimeDensity q t x i) = compatibleLowerSecondTimeCorrection q t x i := by
  have hd := (boundaryCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (directRHTimeDensity_oddInitialPart_hasDerivAt q t x i)
  change HasDerivAt (fun s => boundaryCauchy (directRHTimeDensity (oddInitialPart q) s x i))
    (boundaryCauchy (compatibleRHSecondTimeDensity q t x i)) t at hd
  have he : (fun s => boundaryCauchy (directRHTimeDensity (oddInitialPart q) s x i)) =
      fun s => directLowerTimeCorrection (oddInitialPart q) s x i := funext fun s => directRHTimeDensity_lower _ s x i
  rw [he] at hd
  exact hd.unique (directLowerTimeCorrection_oddInitialPart_hasDerivAt q t x i)

theorem compatibleRHSecondTimeDensity_upper (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    compatibleRHSecondTimeDensity q t x i+boundaryCauchy (compatibleRHSecondTimeDensity q t x i) =
      compatibleUpperSecondTimeCorrection q t x i := by
  rw [compatibleRHSecondTimeDensity_lower,compatibleUpperSecondTimeCorrection,add_comm]

end
end RHTower.FokasLenells
