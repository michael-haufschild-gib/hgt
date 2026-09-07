import GaloisForLFunctions.RHTower.ThetaCuspExactCompletedC5SeamFarTail

/-!
# All-order cooling of the literal higher-likelihood source

Every source derivative of the higher-likelihood partition decays faster than
any fixed power of the reflection scale. The finite derivative recurrence retains
all higher atoms through their fixed positive spectral measure.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

/-- A scale-weighted moment of the literal higher-likelihood measure. -/
def thetaCuspCoolingMoment (m : ℕ) (x : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectionScale 1 x^m *
    thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m

/-- Finite triangular derivative recurrence for the scale-weighted moments. -/
def thetaCuspCoolingJet : ℕ → ℕ → ℝ → ℝ
  | 0, m, x => thetaCuspCoolingMoment m x
  | n+1, m, x => 2*(m : ℝ)*thetaCuspCoolingJet n m x - 2*thetaCuspCoolingJet n (m+1) x

/-- Logarithmic source differentiation closes on adjacent weighted moments. -/
theorem hasDerivAt_thetaCuspCoolingMoment (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspCoolingMoment m)
      (2*(m : ℝ)*thetaCuspCoolingMoment m x - 2*thetaCuspCoolingMoment (m+1) x) x := by
  have hq := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hM := (hasDerivAt_thetaCuspHigherLikelihoodSpectralMoment m
    (thetaCuspLikelihoodCoordinate_pos hx.le)).comp x (hasDerivAt_thetaCuspLikelihoodCoordinate x)
  have h := (hq.pow m).mul hM
  apply h.congr_deriv
  cases m with
  | zero => simp [thetaCuspCoolingMoment]; ring
  | succ m =>
    simp only [thetaCuspCoolingMoment, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply, Function.comp_apply, pow_succ]
    ring

/-- Every finite cooling jet differentiates to its successor. -/
theorem hasDerivAt_thetaCuspCoolingJet (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspCoolingJet n m) (thetaCuspCoolingJet (n+1) m x) x := by
  induction n generalizing m with
  | zero => exact hasDerivAt_thetaCuspCoolingMoment m hx
  | succ n ih =>
    exact ((ih m).const_mul (2*(m : ℝ))).sub ((ih (m+1)).const_mul 2)

/-- The finite recurrence is the actual all-order source derivative. -/
theorem iteratedDeriv_thetaCuspCoolingMoment (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (thetaCuspCoolingMoment m) x = thetaCuspCoolingJet n m x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have he : iteratedDeriv n (thetaCuspCoolingMoment m) =ᶠ[𝓝 x] thetaCuspCoolingJet n m := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (hasDerivAt_thetaCuspCoolingJet n m hx).deriv

/-- Every weighted moment decays faster than any fixed power of the source scale. -/
theorem thetaCuspCoolingMoment_scaled_tendsto_zero (k m : ℕ) :
    Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
      thetaCuspCoolingMoment m x) atTop (𝓝 0) := by
  have h := ((thetaCuspC5FarTail_scaled_moment_tendsto_zero (k+m) m).comp
    thetaCuspC5FarTail_coordinate_tendsto_atTop).mul
      (thetaCuspC5FarTail_scale_div_coordinate_tendsto_one.pow (k+m))
  have he : (fun x : ℝ =>
      (thetaCuspLikelihoodCoordinate x^(k+m) *
        thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) m) *
          (thetaCuspSingleAtomReflectionScale 1 x / thetaCuspLikelihoodCoordinate x)^(k+m))
      =ᶠ[atTop] (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
        thetaCuspCoolingMoment m x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hB := (thetaCuspLikelihoodCoordinate_pos hx).ne'
    unfold thetaCuspCoolingMoment
    rw [div_pow]
    field_simp [hB]
    ring
  exact (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr' he

/-- Every finite source derivative retains the full polynomial cooling reserve. -/
theorem thetaCuspCoolingJet_scaled_tendsto_zero (k n m : ℕ) :
    Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
      thetaCuspCoolingJet n m x) atTop (𝓝 0) := by
  induction n generalizing m with
  | zero => exact thetaCuspCoolingMoment_scaled_tendsto_zero k m
  | succ n ih =>
    have h := ((ih m).const_mul (2*(m : ℝ))).sub ((ih (m+1)).const_mul 2)
    convert h using 1
    · funext x
      dsimp only [thetaCuspCoolingJet]
      ring
    · simp

/-- The exact higher-likelihood source remainder. -/
def thetaCuspLikelihoodSourceRemainder (x : ℝ) : ℝ :=
  thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) - 1

/-- The source remainder is the zeroth fixed-measure moment. -/
theorem thetaCuspLikelihoodSourceRemainder_eq_coolingMoment {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceRemainder x = thetaCuspCoolingMoment 0 x := by
  unfold thetaCuspLikelihoodSourceRemainder thetaCuspCoolingMoment
  rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero (thetaCuspLikelihoodCoordinate_pos hx.le)]
  simp

/-- All-order derivative identification for the actual likelihood remainder. -/
theorem iteratedDeriv_thetaCuspLikelihoodSourceRemainder (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n thetaCuspLikelihoodSourceRemainder x = thetaCuspCoolingJet n 0 x := by
  have he : thetaCuspLikelihoodSourceRemainder =ᶠ[𝓝 x] thetaCuspCoolingMoment 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact thetaCuspLikelihoodSourceRemainder_eq_coolingMoment hy
  rw [he.iteratedDeriv_eq, iteratedDeriv_thetaCuspCoolingMoment n 0 hx]

/-- Every derivative of the literal likelihood remainder decays after any fixed scale power. -/
theorem iteratedDeriv_thetaCuspLikelihoodSourceRemainder_scaled_tendsto_zero (k n : ℕ) :
    Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x^k *
      iteratedDeriv n thetaCuspLikelihoodSourceRemainder x) atTop (𝓝 0) := by
  apply (thetaCuspCoolingJet_scaled_tendsto_zero k n 0).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [iteratedDeriv_thetaCuspLikelihoodSourceRemainder n hx]

end
end RHTower
