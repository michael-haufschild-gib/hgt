import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedHawkingFlux

/-!
# Sharp quantum-energy inequality for the reflected theta Hawking flux

The reflected theta trajectory has conformal flux

`F_C = 2 C (q' ^ (2 : ℕ) - q'')`.

For a real sampling amplitude `g`, the Fewster--Hollands moving-mirror completion is the exact
identity

`g ^ (2 : ℕ) F_C + 2 C (g') ^ (2 : ℕ) + (2 C g ^ (2 : ℕ) q')' = 2 C (g q' + g') ^ (2 : ℕ)`.

Thus a nonnegative-central-charge CFT gives a nonnegative renormalized density, and integration
over an interval on which `g` vanishes at both endpoints gives the sharp sampled QEI.  This file
also proves that the literal theta mirror has a strictly negative central Hawking pulse, stationary
at the reflection center, while its flux is nondecreasing on the future displacement ray.

These are source-specific Hawking-radiation theorems, not a relabeling of the RH-equivalent tilt
form.  In particular, the QEI controls flux only after paying the sampling-gradient term; it does
not imply the raw multi-mode tilt-flux positivity.  The remaining RH producer would have to
identify the Weil even/odd channels with a canonical Bogoliubov pair strongly enough for the CCR
signed-norm law to control their cross-mode coherence.
-/

open Real

namespace RHTower

noncomputable section

/-! ## Central negative pulse and monotone recovery -/

/-- Strict positivity of the completed theta logarithmic curvature. -/
theorem thetaCuspLogCurvature_pos (x : ℝ) :
    0 < thetaCuspLogCurvature x := by
  rw [thetaCuspLogCurvature, iteratedDeriv_two_thetaCuspLogSource_eq]
  exact neg_pos.mpr <|
    div_neg_of_neg_of_pos (thetaCuspLogConcavityNumerator_neg_all x)
      (sq_pos_of_pos (thetaCuspFullSource_pos_all x))

@[simp] theorem thetaCuspReflectedLogJetOne_zero (u : ℝ) :
    thetaCuspReflectedLogJetOne u 0 = 0 := by
  simp [thetaCuspReflectedLogJetOne]

@[simp] theorem thetaCuspReflectedLogJetTwo_zero (u : ℝ) :
    thetaCuspReflectedLogJetTwo u 0 = 2 * thetaCuspLogCurvature u := by
  simp [thetaCuspReflectedLogJetTwo]
  ring

@[simp] theorem thetaCuspReflectedLogJetThree_zero (u : ℝ) :
    thetaCuspReflectedLogJetThree u 0 = 0 := by
  simp [thetaCuspReflectedLogJetThree]

/-- Exact value of the reflected conformal flux at the reflection center. -/
theorem thetaCuspReflectedHawkingFlux_zero (C u : ℝ) :
    thetaCuspReflectedHawkingFlux C u 0 =
      -4 * C * thetaCuspLogCurvature u := by
  rw [thetaCuspReflectedHawkingFlux, thetaCuspReflectedLogJetOne_zero,
    thetaCuspReflectedLogJetTwo_zero]
  ring

/-- A positive-central-charge theta mirror emits a genuinely negative central Hawking pulse. -/
theorem thetaCuspReflectedHawkingFlux_zero_neg
    {C : ℝ} (hC : 0 < C) (u : ℝ) :
    thetaCuspReflectedHawkingFlux C u 0 < 0 := by
  rw [thetaCuspReflectedHawkingFlux_zero]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hC)
    (thetaCuspLogCurvature_pos u)

/-- The central negative pulse is stationary at the reflection center. -/
theorem deriv_thetaCuspReflectedHawkingFlux_zero (C u : ℝ) :
    deriv (thetaCuspReflectedHawkingFlux C u) 0 = 0 := by
  rw [deriv_thetaCuspReflectedHawkingFlux, thetaCuspReflectedLogRiccatiMargin,
    thetaCuspReflectedLogJetOne_zero, thetaCuspReflectedLogJetThree_zero]
  ring

/-- Future theta Hawking flux is monotone: the central negative pulse can only recover after the
reflection center. -/
theorem monotoneOn_thetaCuspReflectedHawkingFlux_Ici
    {C : ℝ} (hC : 0 ≤ C) (u : ℝ) :
    MonotoneOn (thetaCuspReflectedHawkingFlux C u) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
  · exact (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspReflectedHawkingFlux C u t).continuousAt).continuousOn
  · intro t ht
    exact (hasDerivAt_thetaCuspReflectedHawkingFlux C u t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact deriv_thetaCuspReflectedHawkingFlux_nonneg hC ht.le

/-- The reflection center is a global minimum of the future theta Hawking flux. -/
theorem thetaCuspReflectedHawkingFlux_zero_le_of_nonneg
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (u : ℝ) :
    thetaCuspReflectedHawkingFlux C u 0 ≤
      thetaCuspReflectedHawkingFlux C u t := by
  exact monotoneOn_thetaCuspReflectedHawkingFlux_Ici hC u
    (show 0 ∈ Set.Ici (0 : ℝ) by simp) (show t ∈ Set.Ici (0 : ℝ) from ht) ht

/-! ## Local Fewster--Hollands square completion -/

/-- Bulk sampled Hawking flux plus the universal sampling-gradient counterterm. -/
def thetaCuspHawkingQEIBulkDensity
    (C u : ℝ) (g g' : ℝ → ℝ) (t : ℝ) : ℝ :=
  g t ^ (2 : ℕ) * thetaCuspReflectedHawkingFlux C u t + 2 * C * g' t ^ (2 : ℕ)

/-- Boundary current whose derivative separates raw Hawking flux from its QEI square. -/
def thetaCuspHawkingQEIBoundaryCurrent
    (C u : ℝ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (2 * C) • ((g ^ (2 : ℕ)) * thetaCuspReflectedLogJetOne u)

/-- Named derivative of the QEI boundary current. -/
def thetaCuspHawkingQEIBoundaryCurrentDerivative
    (C u : ℝ) (g g' : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * C *
    (2 * g t * g' t * thetaCuspReflectedLogJetOne u t +
      g t ^ (2 : ℕ) * thetaCuspReflectedLogJetTwo u t)

/-- Positive square appearing in the sharp conformal QEI. -/
def thetaCuspHawkingQEISquareDensity
    (C u : ℝ) (g g' : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * C *
    (g t * thetaCuspReflectedLogJetOne u t + g' t) ^ (2 : ℕ)

/-- The named boundary derivative is the actual derivative of the boundary current. -/
theorem hasDerivAt_thetaCuspHawkingQEIBoundaryCurrent
    (C u : ℝ) {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) (t : ℝ) :
    HasDerivAt (thetaCuspHawkingQEIBoundaryCurrent C u g)
      (thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g' t) t := by
  have hsq := (hg t).pow 2
  have hmul := hsq.mul (hasDerivAt_thetaCuspReflectedLogJetOne u t)
  unfold thetaCuspHawkingQEIBoundaryCurrent
    thetaCuspHawkingQEIBoundaryCurrentDerivative
  simpa only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      hmul.const_smul (2 * C)

/-- **Local sharp QEI identity.**  Sampled flux, sampling cost, and boundary-current derivative
complete to one nonnegative conformal square. -/
theorem thetaCuspHawkingQEIBulk_add_boundaryDerivative_eq_square
    (C u : ℝ) (g g' : ℝ → ℝ) (t : ℝ) :
    thetaCuspHawkingQEIBulkDensity C u g g' t +
        thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g' t =
      thetaCuspHawkingQEISquareDensity C u g g' t := by
  unfold thetaCuspHawkingQEIBulkDensity
    thetaCuspHawkingQEIBoundaryCurrentDerivative
    thetaCuspHawkingQEISquareDensity thetaCuspReflectedHawkingFlux
  ring

/-- Nonnegative local renormalized Hawking density for nonnegative CFT normalization. -/
theorem thetaCuspHawkingQEIRenormalizedDensity_nonneg
    {C : ℝ} (hC : 0 ≤ C) (u : ℝ) (g g' : ℝ → ℝ) (t : ℝ) :
    0 ≤ thetaCuspHawkingQEIBulkDensity C u g g' t +
      thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g' t := by
  rw [thetaCuspHawkingQEIBulk_add_boundaryDerivative_eq_square]
  exact mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _)

/-- Algebraic sharpness: the QEI square vanishes at the unique local derivative
`g' = -g q'`. -/
theorem thetaCuspHawkingQEISquareDensity_eq_zero_at_optimalDerivative
    (C u : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    thetaCuspHawkingQEISquareDensity C u g
      (fun s => -g s * thetaCuspReflectedLogJetOne u s) t = 0 := by
  simp [thetaCuspHawkingQEISquareDensity]

/-! ## Integrated sharp QEI -/

/-- Exact finite-interval Fewster--Hollands balance. -/
theorem intervalIntegral_thetaCuspHawkingQEIBulk_eq_square_sub_boundary
    (C u a b : ℝ) (g g' : ℝ → ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g') :
    (∫ t in a..b, thetaCuspHawkingQEIBulkDensity C u g g' t) =
      (∫ t in a..b, thetaCuspHawkingQEISquareDensity C u g g' t) -
        (thetaCuspHawkingQEIBoundaryCurrent C u g b -
          thetaCuspHawkingQEIBoundaryCurrent C u g a) := by
  have hgcont : Continuous g :=
    continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hfluxcont : Continuous (thetaCuspReflectedHawkingFlux C u) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspReflectedHawkingFlux C u t).continuousAt
  have hjetOneCont : Continuous (thetaCuspReflectedLogJetOne u) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspReflectedLogJetOne u t).continuousAt
  have hjetTwoCont : Continuous (thetaCuspReflectedLogJetTwo u) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspReflectedLogJetTwo u t).continuousAt
  have hbulkCont : Continuous (thetaCuspHawkingQEIBulkDensity C u g g') := by
    unfold thetaCuspHawkingQEIBulkDensity
    fun_prop
  have hsquareCont : Continuous (thetaCuspHawkingQEISquareDensity C u g g') := by
    unfold thetaCuspHawkingQEISquareDensity
    fun_prop
  have hboundaryDerivCont : Continuous
      (thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g') := by
    unfold thetaCuspHawkingQEIBoundaryCurrentDerivative
    fun_prop
  have hderivEq : deriv (thetaCuspHawkingQEIBoundaryCurrent C u g) =
      thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g' := by
    funext t
    exact (hasDerivAt_thetaCuspHawkingQEIBoundaryCurrent C u hg t).deriv
  have hboundaryIntegral :
      (∫ t in a..b, thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g' t) =
        thetaCuspHawkingQEIBoundaryCurrent C u g b -
          thetaCuspHawkingQEIBoundaryCurrent C u g a := by
    apply intervalIntegral.integral_deriv_eq_sub'
      (thetaCuspHawkingQEIBoundaryCurrent C u g) hderivEq
    · intro t ht
      exact (hasDerivAt_thetaCuspHawkingQEIBoundaryCurrent C u hg t).differentiableAt
    · exact hboundaryDerivCont.continuousOn
  have hpointwise :
      thetaCuspHawkingQEIBulkDensity C u g g' =
        thetaCuspHawkingQEISquareDensity C u g g' -
          thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g' := by
    funext t
    rw [Pi.sub_apply]
    have h := thetaCuspHawkingQEIBulk_add_boundaryDerivative_eq_square C u g g' t
    linarith
  rw [hpointwise]
  change (∫ t in a..b,
      thetaCuspHawkingQEISquareDensity C u g g' t -
        thetaCuspHawkingQEIBoundaryCurrentDerivative C u g g' t) = _
  rw [intervalIntegral.integral_sub
      (hsquareCont.intervalIntegrable a b)
      (hboundaryDerivCont.intervalIntegrable a b),
    hboundaryIntegral]

/-- **Theta moving-mirror QEI endpoint.**  If the sampling amplitude vanishes at both interval
ends, sampled theta Hawking flux plus the universal gradient cost is nonnegative. -/
theorem intervalIntegral_thetaCuspHawkingQEIBulk_nonneg
    {C a b : ℝ} (hC : 0 ≤ C) (hab : a ≤ b) (u : ℝ) (g g' : ℝ → ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (hga : g a = 0) (hgb : g b = 0) :
    0 ≤ ∫ t in a..b, thetaCuspHawkingQEIBulkDensity C u g g' t := by
  rw [intervalIntegral_thetaCuspHawkingQEIBulk_eq_square_sub_boundary
    C u a b g g' hg hg']
  have hboundaryA : thetaCuspHawkingQEIBoundaryCurrent C u g a = 0 := by
    simp [thetaCuspHawkingQEIBoundaryCurrent, hga]
  have hboundaryB : thetaCuspHawkingQEIBoundaryCurrent C u g b = 0 := by
    simp [thetaCuspHawkingQEIBoundaryCurrent, hgb]
  rw [hboundaryA, hboundaryB]
  simp only [sub_zero]
  exact intervalIntegral.integral_nonneg hab fun t ht =>
    mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _)

/-- CFT normalization of the sharp QEI square, with `C = c/(24*pi)`. -/
theorem thetaCuspHawkingQEISquareDensity_cftNormalization
    (c u : ℝ) (g g' : ℝ → ℝ) (t : ℝ) :
    thetaCuspHawkingQEISquareDensity (c / (24 * Real.pi)) u g g' t =
      c / (12 * Real.pi) *
        (g t * thetaCuspReflectedLogJetOne u t + g' t) ^ (2 : ℕ) := by
  unfold thetaCuspHawkingQEISquareDensity
  ring

end

end RHTower
