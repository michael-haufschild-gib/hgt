import GaloisForLFunctions.RHTower.GammaSewnEulerCalibratedExterior
import GaloisForLFunctions.RHTower.GammaSewnBasiswisePickMixingNoGo

/-!
# Non-diagonal Julia lift of the Gamma-sewn Möbius source

The scalar Gamma-sewn Möbius multiplier has quadratic contact with its lossless boundary.
Its canonical Julia lift is instead a two-channel rotation with a nonzero first-order defect
coordinate.  This file constructs that source transport, proves its exact norm/defect identity,
and identifies its boundary defect tangent with the prime logarithmic clock.

The lift retains the ordered compression/defect pair before scalar recombination.  It therefore
escapes the unchanged-marginal scalar and operator-Pick obstructions: the hidden Julia coordinate,
not the scalar compression, carries the first-order source current.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Canonical Julia defect of the scalar Gamma-sewn Möbius compression. -/
def gammaSewnMobiusJuliaDefect (x : ℝ) (p : Nat.Primes) : ℝ :=
  Real.sqrt (1 - gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ))

/-- The source-defined non-diagonal transport.  Its first coordinate is the old scalar
compression; its second coordinate is the Julia environment retained before recombination. -/
def gammaSewnMobiusJuliaSourceTransportV
    (x : ℝ) (p : Nat.Primes) (v : ℝ × ℝ) : ℝ × ℝ :=
  let c := gammaSewnMobiusValuationContractionMultiplier x p
  let d := gammaSewnMobiusJuliaDefect x p
  (c * v.1 - d * v.2, d * v.1 + c * v.2)

theorem gammaSewnMobiusValuationContractionMultiplier_le_one
    {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier x p ≤ 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [gammaSewnMobiusValuationContractionMultiplier_zero]
  · exact (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p).le

/-- The Julia environment is strictly active at every positive aperture. -/
theorem gammaSewnMobiusJuliaDefect_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 < gammaSewnMobiusJuliaDefect x p := by
  change 0 < Real.sqrt
    (1 - gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ))
  apply Real.sqrt_pos.2
  have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have hc1 := gammaSewnMobiusValuationContractionMultiplier_lt_one hx p
  nlinarith

theorem gammaSewnMobiusJuliaDefect_sq
    {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) :
    gammaSewnMobiusJuliaDefect x p ^ (2 : ℕ) =
      1 - gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ) := by
  rw [gammaSewnMobiusJuliaDefect, Real.sq_sqrt]
  have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have hc1 := gammaSewnMobiusValuationContractionMultiplier_le_one hx p
  nlinarith

/-- Exact Julia/defect identity: the doubled source transport is an isometry. -/
theorem gammaSewnMobiusJuliaSourceTransportV_normSq
    {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) (v : ℝ × ℝ) :
    (gammaSewnMobiusJuliaSourceTransportV x p v).1 ^ (2 : ℕ) +
        (gammaSewnMobiusJuliaSourceTransportV x p v).2 ^ (2 : ℕ) =
      v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ) := by
  rw [gammaSewnMobiusJuliaSourceTransportV]
  dsimp only
  calc
    (gammaSewnMobiusValuationContractionMultiplier x p * v.1 -
          gammaSewnMobiusJuliaDefect x p * v.2) ^ (2 : ℕ) +
        (gammaSewnMobiusJuliaDefect x p * v.1 +
          gammaSewnMobiusValuationContractionMultiplier x p * v.2) ^ (2 : ℕ) =
      (gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ) +
        gammaSewnMobiusJuliaDefect x p ^ (2 : ℕ)) *
          (v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ)) := by ring
    _ = v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ) := by
      rw [gammaSewnMobiusJuliaDefect_sq hx]
      ring

/-- An orientation-preserving real plane isometry has a unique second column once its first
orthonormal column is fixed. -/
theorem orientedPlaneIsometry_secondColumn_unique
    {c d a b : ℝ}
    (hfirst : c ^ (2 : ℕ) + d ^ (2 : ℕ) = 1)
    (hsecond : a ^ (2 : ℕ) + b ^ (2 : ℕ) = 1)
    (horth : c * a + d * b = 0)
    (horient : 0 < c * b - d * a) :
    a = -d ∧ b = c := by
  have hdetSq : (c * b - d * a) ^ (2 : ℕ) = 1 := by
    calc
      (c * b - d * a) ^ (2 : ℕ) =
          (c ^ (2 : ℕ) + d ^ (2 : ℕ)) * (a ^ (2 : ℕ) + b ^ (2 : ℕ)) -
            (c * a + d * b) ^ (2 : ℕ) := by ring
      _ = 1 := by rw [hfirst, hsecond, horth]; norm_num
  have hdet : c * b - d * a = 1 := by nlinarith
  constructor
  · calc
      a = (c ^ (2 : ℕ) + d ^ (2 : ℕ)) * a := by rw [hfirst]; ring
      _ = -d * (c * b - d * a) + c * (c * a + d * b) := by ring
      _ = -d := by rw [hdet, horth]; ring
  · calc
      b = (c ^ (2 : ℕ) + d ^ (2 : ℕ)) * b := by rw [hfirst]; ring
      _ = c * (c * b - d * a) + d * (c * a + d * b) := by ring
      _ = c := by rw [hdet, horth]; ring

/-- At positive aperture, the strict scalar compression cannot itself preserve source-axis
norm.  Hence any isometric completion retaining that coordinate needs at least one environment
dimension. -/
theorem gammaSewnMobiusValuationContractionMultiplier_not_scalar_isometry
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    ¬ ∀ u : ℝ,
      (gammaSewnMobiusValuationContractionMultiplier x p * u) ^ (2 : ℕ) = u ^ (2 : ℕ) := by
  intro h
  have h1 : gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ) = 1 := by
    simpa using h 1
  have hc0 := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have hc1 := gammaSewnMobiusValuationContractionMultiplier_lt_one hx p
  nlinarith

/-- **Unique minimal positive Julia lift.**  The Julia rotation is the unique
orientation-preserving plane isometry whose first source-axis column is the prescribed scalar
compression together with its positive defect coordinate.  Combined with the preceding scalar
no-go, one extra real channel is minimal. -/
theorem gammaSewnMobiusJuliaSourceTransportV_unique_minimal_positive_lift
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) {a b : ℝ}
    (hsecond : a ^ (2 : ℕ) + b ^ (2 : ℕ) = 1)
    (horth :
      gammaSewnMobiusValuationContractionMultiplier x p * a +
        gammaSewnMobiusJuliaDefect x p * b = 0)
    (horient :
      0 <
        gammaSewnMobiusValuationContractionMultiplier x p * b -
          gammaSewnMobiusJuliaDefect x p * a) :
    a = -gammaSewnMobiusJuliaDefect x p ∧
      b = gammaSewnMobiusValuationContractionMultiplier x p := by
  apply orientedPlaneIsometry_secondColumn_unique
  · rw [gammaSewnMobiusJuliaDefect_sq hx.le]
    ring
  · exact hsecond
  · exact horth
  · exact horient

/-- On the distinguished source axis, the two outputs are exactly the scalar compression and its
Julia defect. -/
theorem gammaSewnMobiusJuliaSourceTransportV_sourceAxis
    (x : ℝ) (p : Nat.Primes) (u : ℝ) :
    gammaSewnMobiusJuliaSourceTransportV x p (u, 0) =
      (gammaSewnMobiusValuationContractionMultiplier x p * u,
        gammaSewnMobiusJuliaDefect x p * u) := by
  simp [gammaSewnMobiusJuliaSourceTransportV]

/-- The source-axis Julia coordinate is genuinely non-diagonal at every positive aperture. -/
theorem gammaSewnMobiusJuliaSourceTransportV_sourceAxis_second_ne_zero
    {x u : ℝ} (hx : 0 < x) (hu : u ≠ 0) (p : Nat.Primes) :
    (gammaSewnMobiusJuliaSourceTransportV x p (u, 0)).2 ≠ 0 := by
  rw [gammaSewnMobiusJuliaSourceTransportV_sourceAxis]
  exact mul_ne_zero (gammaSewnMobiusJuliaDefect_pos hx p).ne' hu

/-- Exact scalar-compression/Julia-environment Pythagoras law. -/
theorem gammaSewnMobiusJuliaSourceTransportV_sourceAxis_defectIdentity
    {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) (u : ℝ) :
    (gammaSewnMobiusValuationContractionMultiplier x p * u) ^ (2 : ℕ) +
        (gammaSewnMobiusJuliaDefect x p * u) ^ (2 : ℕ) = u ^ (2 : ℕ) := by
  simpa [gammaSewnMobiusJuliaSourceTransportV_sourceAxis] using
    gammaSewnMobiusJuliaSourceTransportV_normSq hx p (u, 0)

/-- Exact aperture-factor form of the Julia defect. -/
theorem gammaSewnMobiusJuliaDefect_sq_eq_aperture_sq_mul_gain
    {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) :
    gammaSewnMobiusJuliaDefect x p ^ (2 : ℕ) =
      (1 - xiMobiusContinuousApertureDiskNode x p) ^ (2 : ℕ) *
        (gammaSewnMobiusValuationQuadraticDefectGain x p *
          (1 + gammaSewnMobiusValuationContractionMultiplier x p)) := by
  rw [gammaSewnMobiusJuliaDefect_sq hx,
    show 1 - gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ) =
      (1 - gammaSewnMobiusValuationContractionMultiplier x p) *
        (1 + gammaSewnMobiusValuationContractionMultiplier x p) by ring,
    one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain]
  ring

theorem gammaSewnMobiusValuationQuadraticDefectGain_nonneg
    (x : ℝ) (p : Nat.Primes) :
    0 ≤ gammaSewnMobiusValuationQuadraticDefectGain x p := by
  unfold gammaSewnMobiusValuationQuadraticDefectGain
  have hq := xiMobiusContinuousApertureDiskNode_pos x p
  have hc := gammaSewnMobiusValuationContractionMultiplier_pos x p
  positivity

/-- The square-root Julia defect is exactly linear in the physical aperture increment. -/
theorem gammaSewnMobiusJuliaDefect_eq_aperture_mul_sqrt_gain
    {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) :
    gammaSewnMobiusJuliaDefect x p =
      (1 - xiMobiusContinuousApertureDiskNode x p) *
        Real.sqrt
          (gammaSewnMobiusValuationQuadraticDefectGain x p *
            (1 + gammaSewnMobiusValuationContractionMultiplier x p)) := by
  have hpOne : (1 : ℝ) ≤ p := by
    exact_mod_cast p.property.one_le
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpOne
  have hqOne : xiMobiusContinuousApertureDiskNode x p ≤ 1 := by
    rw [xiMobiusContinuousApertureDiskNode]
    exact Real.exp_le_one_iff.mpr
      (by
        rw [show -x * Real.log (p : ℝ) =
          -(x * Real.log (p : ℝ)) by ring]
        exact neg_nonpos.mpr (mul_nonneg hx hlog))
  have hgap : 0 ≤ 1 - xiMobiusContinuousApertureDiskNode x p :=
    sub_nonneg.mpr hqOne
  have hgain := gammaSewnMobiusValuationQuadraticDefectGain_nonneg x p
  have hc := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have hfactor :
      0 ≤ gammaSewnMobiusValuationQuadraticDefectGain x p *
        (1 + gammaSewnMobiusValuationContractionMultiplier x p) := by positivity
  have hsqrt := Real.sq_sqrt hfactor
  have hsq := gammaSewnMobiusJuliaDefect_sq_eq_aperture_sq_mul_gain hx p
  have hd := Real.sqrt_nonneg
    (1 - gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ))
  change 0 ≤ gammaSewnMobiusJuliaDefect x p at hd
  have hrhs :
      0 ≤ (1 - xiMobiusContinuousApertureDiskNode x p) *
        Real.sqrt
          (gammaSewnMobiusValuationQuadraticDefectGain x p *
            (1 + gammaSewnMobiusValuationContractionMultiplier x p)) :=
    mul_nonneg hgap (Real.sqrt_nonneg _)
  have hrhsSq :
      ((1 - xiMobiusContinuousApertureDiskNode x p) *
        Real.sqrt
          (gammaSewnMobiusValuationQuadraticDefectGain x p *
            (1 + gammaSewnMobiusValuationContractionMultiplier x p))) ^ (2 : ℕ) =
        (1 - xiMobiusContinuousApertureDiskNode x p) ^ (2 : ℕ) *
          (gammaSewnMobiusValuationQuadraticDefectGain x p *
            (1 + gammaSewnMobiusValuationContractionMultiplier x p)) := by
    rw [mul_pow, hsqrt]
  nlinarith [sq_nonneg
    ((1 - xiMobiusContinuousApertureDiskNode x p) *
      Real.sqrt
        (gammaSewnMobiusValuationQuadraticDefectGain x p *
          (1 + gammaSewnMobiusValuationContractionMultiplier x p)))]

/-- **Prime-log Julia tangent law.**  Although the scalar compression has zero first derivative
at the boundary, its retained environment has the nonzero logarithmic tangent
`log(p) * sqrt(3/4)`. -/
theorem tendsto_gammaSewnMobiusJuliaDefect_div_nhdsGT_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaDefect x p / x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (Real.log (p : ℝ) * Real.sqrt (3 / 4 : ℝ))) := by
  let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let c : ℝ → ℝ := fun x =>
    gammaSewnMobiusValuationContractionMultiplier x p
  let g : ℝ → ℝ := fun x =>
    gammaSewnMobiusValuationQuadraticDefectGain x p
  have hgap : Tendsto (fun x : ℝ => (1 - q x) / x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Real.log (p : ℝ))) := by
    simpa only [q, mul_one, one_mul] using
      tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
        1 p
  have hc : Tendsto c (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    dsimp only [c]
    rw [← gammaSewnMobiusValuationContractionMultiplier_zero p]
    exact
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).tendsto.mono_left
        inf_le_left
  have hg : Tendsto g (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (3 / 8 : ℝ)) := by
    dsimp only [g]
    rw [← gammaSewnMobiusValuationQuadraticDefectGain_zero p]
    exact
      (continuousAt_gammaSewnMobiusValuationQuadraticDefectGain_zero p).tendsto.mono_left
        inf_le_left
  have hsqrt : Tendsto
      (fun x : ℝ => Real.sqrt (g x * (1 + c x)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (Real.sqrt (3 / 4 : ℝ))) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) :=
      tendsto_const_nhds
    have hinside : Tendsto (fun x : ℝ => g x * (1 + c x))
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds ((3 / 8 : ℝ) * (1 + 1))) :=
      hg.mul (hone.add hc)
    have hsqrt' : Tendsto (fun x : ℝ => Real.sqrt (g x * (1 + c x)))
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (Real.sqrt ((3 / 8 : ℝ) * (1 + 1)))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hinside
    have hthree : (3 / 8 : ℝ) * (1 + 1) = 3 / 4 := by norm_num
    simpa only [hthree] using hsqrt'
  have hmul := hgap.mul hsqrt
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 ≤ x := hx.le
  rw [gammaSewnMobiusJuliaDefect_eq_aperture_mul_sqrt_gain hx0 p]
  change
    ((1 - q x) / x) * Real.sqrt (g x * (1 + c x)) =
      ((1 - q x) *
        Real.sqrt (g x * (1 + c x))) / x
  ring

/-- The second coordinate of `V` has the same explicit prime-log tangent. -/
theorem tendsto_gammaSewnMobiusJuliaSourceTransportV_sourceAxis_second_div_nhdsGT_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnMobiusJuliaSourceTransportV x p (1, 0)).2 / x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (Real.log (p : ℝ) * Real.sqrt (3 / 4 : ℝ))) := by
  simpa [gammaSewnMobiusJuliaSourceTransportV_sourceAxis] using
    tendsto_gammaSewnMobiusJuliaDefect_div_nhdsGT_zero p

/-! ## The Julia environment is the missing Euler prime-log seam -/

/-- Prime-log coordinate carried by the normalized Julia environment.  This uses the actual
second coordinate of `V`; it is not a separately inserted logarithmic label. -/
def gammaSewnMobiusJuliaNormalizedPrimeLog
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  (Real.sqrt (3 / 4 : ℝ))⁻¹ *
    ((gammaSewnMobiusJuliaSourceTransportV x p (1, 0)).2 / x)

theorem gammaSewnMobiusJuliaNormalization_ne_zero :
    Real.sqrt (3 / 4 : ℝ) ≠ 0 := by
  positivity

/-- Exact finite-aperture Julia column in compression/prime-log coordinates. -/
theorem gammaSewnMobiusJuliaSourceTransportV_sourceAxis_eq_compression_primeLog
    {x : ℝ} (hx : x ≠ 0) (p : Nat.Primes) :
    gammaSewnMobiusJuliaSourceTransportV x p (1, 0) =
      (gammaSewnMobiusValuationContractionMultiplier x p,
        x * Real.sqrt (3 / 4 : ℝ) *
          gammaSewnMobiusJuliaNormalizedPrimeLog x p) := by
  apply Prod.ext
  · simp [gammaSewnMobiusJuliaSourceTransportV_sourceAxis]
  · simp only [gammaSewnMobiusJuliaNormalizedPrimeLog,
      gammaSewnMobiusJuliaSourceTransportV_sourceAxis, mul_one]
    field_simp [hx, gammaSewnMobiusJuliaNormalization_ne_zero]

/-- Exact Julia/defect identity after exposing the normalized prime-log environment coordinate. -/
theorem gammaSewnMobiusJulia_compression_primeLog_defectIdentity
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ) +
        (x * Real.sqrt (3 / 4 : ℝ) *
          gammaSewnMobiusJuliaNormalizedPrimeLog x p) ^ (2 : ℕ) = 1 := by
  have hcoordinate :
      gammaSewnMobiusJuliaDefect x p =
        x * Real.sqrt (3 / 4 : ℝ) *
          gammaSewnMobiusJuliaNormalizedPrimeLog x p := by
    have h := congrArg Prod.snd
      (gammaSewnMobiusJuliaSourceTransportV_sourceAxis_eq_compression_primeLog
        hx.ne' p)
    simpa [gammaSewnMobiusJuliaSourceTransportV_sourceAxis] using h
  have hnorm :=
    gammaSewnMobiusJuliaSourceTransportV_sourceAxis_defectIdentity hx.le p 1
  simpa [hcoordinate] using hnorm

/-- The normalized Julia environment converges to the literal prime logarithm. -/
theorem tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaNormalizedPrimeLog x p)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (Real.log (p : ℝ))) := by
  have hconstant :
      Tendsto (fun _ : ℝ => (Real.sqrt (3 / 4 : ℝ))⁻¹)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (Real.sqrt (3 / 4 : ℝ))⁻¹) :=
    tendsto_const_nhds
  have h := hconstant.mul
      (tendsto_gammaSewnMobiusJuliaSourceTransportV_sourceAxis_second_div_nhdsGT_zero p)
  have hsqrtSq :
      Real.sqrt (3 / 4 : ℝ) * Real.sqrt (3 / 4 : ℝ) = 3 / 4 := by
    rw [Real.mul_self_sqrt]
    norm_num
  have hlimit :
      (Real.sqrt (3 / 4 : ℝ))⁻¹ *
          (Real.log (p : ℝ) * Real.sqrt (3 / 4 : ℝ)) =
        Real.log (p : ℝ) := by
    field_simp [gammaSewnMobiusJuliaNormalization_ne_zero]
  rw [hlimit] at h
  simpa [gammaSewnMobiusJuliaNormalizedPrimeLog] using h

/-- The Julia-generated cross-prime environment seam on the literal Euler amplitudes. -/
def gammaSewnMobiusJuliaPrimeLogExteriorSeam
    (x u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerBoundaryRealAmplitude u i *
    xiGammaEulerBoundaryRealAmplitude u j *
      (gammaSewnMobiusJuliaNormalizedPrimeLog x i.1 -
        gammaSewnMobiusJuliaNormalizedPrimeLog x j.1)

/-- The non-diagonal Julia environment produces exactly the forced Euler prime-log seam at the
lossless boundary. -/
theorem tendsto_gammaSewnMobiusJuliaPrimeLogExteriorSeam_nhdsGT_zero
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaPrimeLogExteriorSeam x u i j)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (xiGammaEulerPrimeLogExteriorSeam u i j)) := by
  simpa [gammaSewnMobiusJuliaPrimeLogExteriorSeam,
    xiGammaEulerPrimeLogExteriorSeam] using
    (tendsto_const_nhds.mul tendsto_const_nhds).mul
      ((tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero i.1).sub
        (tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero j.1))

/-- Finite-aperture non-diagonal source current: half the recovered Gamma midpoint current plus
one quarter of the prime-log environment generated by the Julia transport itself. -/
def gammaSewnMobiusJuliaCalibratedEulerExteriorCell
    (x u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  (1 / 2 : ℝ) * gammaSewnRecoveredEulerAmplitudeExteriorCell u i j +
    (1 / 4 : ℝ) * gammaSewnMobiusJuliaPrimeLogExteriorSeam x u i j

/-- **Julia-to-Euler source transport law.**  The boundary of the non-diagonal Julia current is
exactly the literal von Mangoldt--Gamma Euler exterior current, hence its complex phase
Wronskian. -/
theorem tendsto_gammaSewnMobiusJuliaCalibratedEulerExteriorCell_nhdsGT_zero
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u i j)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (xiGammaEulerBoundaryExteriorCell u i j)) := by
  have hgamma :
      Tendsto
        (fun _ : ℝ =>
          (1 / 2 : ℝ) * gammaSewnRecoveredEulerAmplitudeExteriorCell u i j)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds ((1 / 2 : ℝ) *
          gammaSewnRecoveredEulerAmplitudeExteriorCell u i j)) :=
    tendsto_const_nhds
  have hquarter :
      Tendsto (fun _ : ℝ => (1 / 4 : ℝ))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 / 4 : ℝ)) :=
    tendsto_const_nhds
  have h := hgamma.add
    (hquarter.mul
      (tendsto_gammaSewnMobiusJuliaPrimeLogExteriorSeam_nhdsGT_zero u i j))
  have hlimit :
      (1 / 2 : ℝ) * gammaSewnRecoveredEulerAmplitudeExteriorCell u i j +
          (1 / 4 : ℝ) * xiGammaEulerPrimeLogExteriorSeam u i j =
        xiGammaEulerBoundaryExteriorCell u i j := by
    simpa [gammaSewnEulerCalibratedBoundaryExteriorCell] using
      gammaSewnEulerCalibratedBoundaryExteriorCell_eq_eulerBoundaryExterior u i j
  rw [hlimit] at h
  simpa [gammaSewnMobiusJuliaCalibratedEulerExteriorCell] using h

/-- The same boundary transport, expressed as the literal complex Euler phase Wronskian. -/
theorem tendsto_I_mul_gammaSewnMobiusJuliaCalibratedEulerExteriorCell_nhdsGT_zero
    (u : ℝ) (i j : Nat.Primes × ℕ) :
    Tendsto
      (fun x : ℝ =>
        Complex.I *
          (gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u i j : ℂ))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (xiGammaEulerHeightBoundaryWronskianAtZero u i j)) := by
  have hreal :=
    tendsto_gammaSewnMobiusJuliaCalibratedEulerExteriorCell_nhdsGT_zero u i j
  have hofReal :=
    (Complex.continuous_ofReal.tendsto
      (xiGammaEulerBoundaryExteriorCell u i j)).comp hreal
  have hI :
      Tendsto (fun _ : ℝ => Complex.I)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds Complex.I) :=
    tendsto_const_nhds
  have h := hI.mul hofReal
  rw [xiGammaEulerHeightBoundaryWronskianAtZero_eq_I_mul_exterior]
  exact h

/-! ## Singular half-weight source crossing -/

/-- Canonical soft half-weight source on a prime-power cell.  The inverse prime-log density is
part of the source coordinate; no Xi value, zero, or target response occurs in its definition. -/
def gammaSewnMobiusJuliaSoftHalfWeightSource
    (u : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  let n := xiGammaEulerValuationNat pe
  Real.sqrt
    (Real.exp (-u * Real.log n) /
      ((n : ℝ) * Real.log (pe.1 : ℝ)))

theorem gammaSewnMobiusJuliaSoftHalfWeightSource_pos
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusJuliaSoftHalfWeightSource u pe := by
  have hpLog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  have hnNat : 0 < xiGammaEulerValuationNat pe := by
    unfold xiGammaEulerValuationNat
    exact Nat.pow_pos pe.1.property.pos
  have hn : (0 : ℝ) < xiGammaEulerValuationNat pe := by
    exact_mod_cast hnNat
  unfold gammaSewnMobiusJuliaSoftHalfWeightSource
  exact Real.sqrt_pos.2 (div_pos (Real.exp_pos _) (mul_pos hn hpLog))

theorem gammaSewnMobiusJuliaSoftHalfWeightSource_sq
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    gammaSewnMobiusJuliaSoftHalfWeightSource u pe ^ (2 : ℕ) =
      Real.exp (-u * Real.log (xiGammaEulerValuationNat pe)) /
        ((xiGammaEulerValuationNat pe : ℝ) * Real.log (pe.1 : ℝ)) := by
  unfold gammaSewnMobiusJuliaSoftHalfWeightSource
  rw [Real.sq_sqrt]
  positivity

theorem xiGammaEulerBoundaryRealAmplitude_sq
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerBoundaryRealAmplitude u pe ^ (2 : ℕ) =
      Real.log (pe.1 : ℝ) / (xiGammaEulerValuationNat pe : ℝ) *
        Real.exp (-u * Real.log (xiGammaEulerValuationNat pe)) := by
  unfold xiGammaEulerBoundaryRealAmplitude
  rw [Real.sq_sqrt]
  positivity

/-- Multiplication by the prime-log Julia boundary tangent converts the canonical soft source
exactly into the literal von Mangoldt--Gamma hard half-weight amplitude. -/
theorem primeLog_mul_gammaSewnMobiusJuliaSoftHalfWeightSource
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    Real.log (pe.1 : ℝ) *
        gammaSewnMobiusJuliaSoftHalfWeightSource u pe =
      xiGammaEulerBoundaryRealAmplitude u pe := by
  have hpLog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  have hnNat : 0 < xiGammaEulerValuationNat pe := by
    unfold xiGammaEulerValuationNat
    exact Nat.pow_pos pe.1.property.pos
  have hn : (0 : ℝ) < xiGammaEulerValuationNat pe := by
    exact_mod_cast hnNat
  have hsoft := gammaSewnMobiusJuliaSoftHalfWeightSource_pos u pe
  have hhard := xiGammaEulerBoundaryRealAmplitude_pos u pe
  have hsquare :
      (Real.log (pe.1 : ℝ) *
          gammaSewnMobiusJuliaSoftHalfWeightSource u pe) ^ (2 : ℕ) =
        xiGammaEulerBoundaryRealAmplitude u pe ^ (2 : ℕ) := by
    rw [mul_pow, gammaSewnMobiusJuliaSoftHalfWeightSource_sq,
      xiGammaEulerBoundaryRealAmplitude_sq]
    field_simp [hpLog.ne', hn.ne']
  have hproduct : 0 <
      Real.log (pe.1 : ℝ) *
        gammaSewnMobiusJuliaSoftHalfWeightSource u pe :=
    mul_pos hpLog hsoft
  nlinarith [sq_nonneg
    (Real.log (pe.1 : ℝ) *
      gammaSewnMobiusJuliaSoftHalfWeightSource u pe +
        xiGammaEulerBoundaryRealAmplitude u pe)]

/-- Hard half-weight coordinate produced by the normalized environment leg of `V`. -/
def gammaSewnMobiusJuliaHardHalfWeightTransport
    (x u : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusJuliaNormalizedPrimeLog x pe.1 *
    gammaSewnMobiusJuliaSoftHalfWeightSource u pe

/-- Exact finite-aperture formula: the hard transport is the normalized second coordinate of the
actual non-diagonal source operation `V` applied to the soft source axis. -/
theorem gammaSewnMobiusJuliaHardHalfWeightTransport_eq_normalized_second
    {x : ℝ} (hx : x ≠ 0) (u : ℝ) (pe : Nat.Primes × ℕ) :
    gammaSewnMobiusJuliaHardHalfWeightTransport x u pe =
      (Real.sqrt (3 / 4 : ℝ))⁻¹ *
        ((gammaSewnMobiusJuliaSourceTransportV x pe.1
          (gammaSewnMobiusJuliaSoftHalfWeightSource u pe, 0)).2 / x) := by
  simp only [gammaSewnMobiusJuliaHardHalfWeightTransport,
    gammaSewnMobiusJuliaNormalizedPrimeLog,
    gammaSewnMobiusJuliaSourceTransportV_sourceAxis]
  field_simp [hx]

/-- Exact all-cell Julia/defect identity for the soft-to-hard half-weight crossing. -/
theorem gammaSewnMobiusJuliaSoftHard_defectIdentity
    {x : ℝ} (hx : 0 < x) (u : ℝ) (pe : Nat.Primes × ℕ) :
    (gammaSewnMobiusValuationContractionMultiplier x pe.1 *
        gammaSewnMobiusJuliaSoftHalfWeightSource u pe) ^ (2 : ℕ) +
      (x * Real.sqrt (3 / 4 : ℝ) *
        gammaSewnMobiusJuliaHardHalfWeightTransport x u pe) ^ (2 : ℕ) =
      gammaSewnMobiusJuliaSoftHalfWeightSource u pe ^ (2 : ℕ) := by
  have h :=
    gammaSewnMobiusJulia_compression_primeLog_defectIdentity hx pe.1
  unfold gammaSewnMobiusJuliaHardHalfWeightTransport
  calc
    (gammaSewnMobiusValuationContractionMultiplier x pe.1 *
          gammaSewnMobiusJuliaSoftHalfWeightSource u pe) ^ (2 : ℕ) +
        (x * Real.sqrt (3 / 4 : ℝ) *
          (gammaSewnMobiusJuliaNormalizedPrimeLog x pe.1 *
            gammaSewnMobiusJuliaSoftHalfWeightSource u pe)) ^ (2 : ℕ) =
      (gammaSewnMobiusValuationContractionMultiplier x pe.1 ^ (2 : ℕ) +
        (x * Real.sqrt (3 / 4 : ℝ) *
          gammaSewnMobiusJuliaNormalizedPrimeLog x pe.1) ^ (2 : ℕ)) *
        gammaSewnMobiusJuliaSoftHalfWeightSource u pe ^ (2 : ℕ) := by ring
    _ = gammaSewnMobiusJuliaSoftHalfWeightSource u pe ^ (2 : ℕ) := by
      rw [h]
      ring

/-- Normalized environment coordinate converges on every prime-power cell to the literal
von Mangoldt--Gamma hard half-weight amplitude. -/
theorem tendsto_gammaSewnMobiusJuliaHardHalfWeightTransport_nhdsGT_zero
    (u : ℝ) (pe : Nat.Primes × ℕ) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaHardHalfWeightTransport x u pe)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (xiGammaEulerBoundaryRealAmplitude u pe)) := by
  have h :=
    (tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero pe.1).mul
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℝ => gammaSewnMobiusJuliaSoftHalfWeightSource u pe)
          (nhdsWithin (0 : ℝ) (Ioi 0))
          (nhds (gammaSewnMobiusJuliaSoftHalfWeightSource u pe)))
  rw [primeLog_mul_gammaSewnMobiusJuliaSoftHalfWeightSource u pe] at h
  simpa [gammaSewnMobiusJuliaHardHalfWeightTransport] using h

/-- One-parameter squared mass orbit of the canonical Julia environment, extended by zero away
from prime powers. -/
def gammaSewnMobiusJuliaHardMassCoefficient
    (x u : ℝ) (n : ℕ) : ℝ :=
  if hpow : IsPrimePow n then
    gammaSewnMobiusJuliaHardHalfWeightTransport x u
      (Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩) ^ (2 : ℕ)
  else 0

/-- The exact von Mangoldt Mellin orbit reached at the Julia boundary. -/
def gammaSewnMobiusJuliaMellinBoundaryMass (u : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / (n : ℝ) *
    Real.exp (-u * Real.log n)

/-- Prime-clock covariance of the boundary mass: changing damping translates the entire
von Mangoldt source by the diagonal logarithmic clock. -/
theorem gammaSewnMobiusJuliaMellinBoundaryMass_add
    (u v : ℝ) (n : ℕ) :
    gammaSewnMobiusJuliaMellinBoundaryMass (u + v) n =
      Real.exp (-v * Real.log n) *
        gammaSewnMobiusJuliaMellinBoundaryMass u n := by
  unfold gammaSewnMobiusJuliaMellinBoundaryMass
  rw [show -(u + v) * Real.log n =
      (-v * Real.log n) + (-u * Real.log n) by ring,
    Real.exp_add]
  ring

/-- The damping `u = -1` face is the undamped von Mangoldt source itself. -/
theorem gammaSewnMobiusJuliaMellinBoundaryMass_neg_one
    (n : ℕ) :
    gammaSewnMobiusJuliaMellinBoundaryMass (-1) n =
      ArithmeticFunction.vonMangoldt n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [gammaSewnMobiusJuliaMellinBoundaryMass]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [gammaSewnMobiusJuliaMellinBoundaryMass,
      show -(-1 : ℝ) * Real.log n = Real.log n by ring,
      Real.exp_log hnpos]
    exact div_mul_cancel₀ _ (by exact_mod_cast hn)

/-- **Universal Julia--Mellin boundary law.**  At every real damping, the squared normal
coordinate converges coefficientwise to the corresponding Mellin translate of the von Mangoldt
source.  The Euler-logarithm and critical Weil faces are the specializations `u = -1` and
`u = -1/2`. -/
theorem tendsto_gammaSewnMobiusJuliaHardMassCoefficient_nhdsGT_zero
    (u : ℝ) (n : ℕ) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusJuliaHardMassCoefficient x u n)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (gammaSewnMobiusJuliaMellinBoundaryMass u n)) := by
  by_cases hpow : IsPrimePow n
  · let pe : Nat.Primes × ℕ := Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
    have hn :
        xiGammaEulerValuationNat pe = n := by
      have hx : (Nat.Primes.prodNatEquiv pe : ℕ) = n := by
        exact congrArg Subtype.val
          (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
      rw [xiGammaEulerValuationNat,
        ← Nat.Primes.coe_prodNatEquiv_apply]
      exact hx
    have hlim :=
      (tendsto_gammaSewnMobiusJuliaHardHalfWeightTransport_nhdsGT_zero
        u pe).pow 2
    rw [xiGammaEulerBoundaryRealAmplitude_sq] at hlim
    have hvm :
        ArithmeticFunction.vonMangoldt n = Real.log (pe.1 : ℝ) := by
      rw [← hn]
      exact vonMangoldt_prime_pow_succ_eq_log pe
    have htarget :
        Real.log (pe.1 : ℝ) / (xiGammaEulerValuationNat pe : ℝ) *
            Real.exp (-u * Real.log (xiGammaEulerValuationNat pe)) =
          gammaSewnMobiusJuliaMellinBoundaryMass u n := by
      rw [gammaSewnMobiusJuliaMellinBoundaryMass, hvm, hn]
    rw [htarget] at hlim
    have hcoefficient :
        (fun x : ℝ => gammaSewnMobiusJuliaHardMassCoefficient x u n) =
          (fun x : ℝ =>
            gammaSewnMobiusJuliaHardHalfWeightTransport x u pe ^ (2 : ℕ)) := by
      funext x
      unfold gammaSewnMobiusJuliaHardMassCoefficient
      rw [dif_pos hpow]
    rw [hcoefficient]
    exact hlim
  · have hvm : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
    simp only [gammaSewnMobiusJuliaHardMassCoefficient, hpow, hvm,
      gammaSewnMobiusJuliaMellinBoundaryMass, zero_div, zero_mul]
    exact tendsto_const_nhds

/-- **Gamma-sewn scalar-Pick obstruction/Julia--Euler escape universality law.**  No
dimension-dependent operator mixing can preserve the scalar Gamma-sewn prime marginals and the
common-aperture Pick inequalities.  The canonical two-channel Julia lift is instead an exact
isometry retaining that scalar compression as its first coordinate, activating a nonzero second
coordinate at every positive aperture, recovering the literal prime logarithm at the boundary,
and transporting the calibrated exterior current to the Euler phase Wronskian. -/
theorem gammaSewn_scalarPickNoGo_JuliaEulerEscapeUniversality
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Nonempty ι] (b : HilbertBasis ι ℝ E) (prime : ι → Nat.Primes) :
    (¬ ∃ T : ℝ → E →L[ℝ] E,
        (∀ i, Tendsto (fun y : ℝ => T y (b i))
          (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (b i))) ∧
        (∀ x, 0 < x → ∀ i,
          ‖T x (b i)‖ =
            gammaSewnMobiusValuationContractionMultiplier x (prime i)) ∧
        (∀ x y, 0 < x → 0 < y → ∀ u v,
          HTGeometry.operatorPickCross (T x) (T y)
                (Real.exp (-x)) (Real.exp (-y)) u v ^ (2 : ℕ) ≤
            HTGeometry.operatorPickDiagonal (T x) (Real.exp (-x)) u *
              HTGeometry.operatorPickDiagonal (T y) (Real.exp (-y)) v)) ∧
    (∀ (x : ℝ), 0 < x → ∀ p : Nat.Primes,
      (∀ v : ℝ × ℝ,
        (gammaSewnMobiusJuliaSourceTransportV x p v).1 ^ (2 : ℕ) +
            (gammaSewnMobiusJuliaSourceTransportV x p v).2 ^ (2 : ℕ) =
          v.1 ^ (2 : ℕ) + v.2 ^ (2 : ℕ)) ∧
      gammaSewnMobiusJuliaSourceTransportV x p (1, 0) =
        (gammaSewnMobiusValuationContractionMultiplier x p,
          gammaSewnMobiusJuliaDefect x p) ∧
      (gammaSewnMobiusJuliaSourceTransportV x p (1, 0)).2 ≠ 0 ∧
      gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ) +
          (x * Real.sqrt (3 / 4 : ℝ) *
            gammaSewnMobiusJuliaNormalizedPrimeLog x p) ^ (2 : ℕ) = 1) ∧
    (∀ p : Nat.Primes,
      Tendsto
        (fun x : ℝ => gammaSewnMobiusJuliaNormalizedPrimeLog x p)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (Real.log (p : ℝ)))) ∧
    ∀ (u : ℝ) (i j : Nat.Primes × ℕ),
      Tendsto
        (fun x : ℝ => gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u i j)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (xiGammaEulerBoundaryExteriorCell u i j)) ∧
      Tendsto
        (fun x : ℝ =>
          Complex.I *
            (gammaSewnMobiusJuliaCalibratedEulerExteriorCell x u i j : ℂ))
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (xiGammaEulerHeightBoundaryWronskianAtZero u i j)) := by
  refine ⟨
    not_exists_gammaSewnMobius_basisMarginal_commonAperturePickFamily b prime,
    ?_, ?_, ?_⟩
  · intro x hx p
    refine ⟨
      gammaSewnMobiusJuliaSourceTransportV_normSq hx.le p, ?_,
      gammaSewnMobiusJuliaSourceTransportV_sourceAxis_second_ne_zero hx one_ne_zero p,
      gammaSewnMobiusJulia_compression_primeLog_defectIdentity hx p⟩
    simpa using gammaSewnMobiusJuliaSourceTransportV_sourceAxis x p 1
  · exact tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero
  · intro u i j
    exact ⟨
      tendsto_gammaSewnMobiusJuliaCalibratedEulerExteriorCell_nhdsGT_zero u i j,
      tendsto_I_mul_gammaSewnMobiusJuliaCalibratedEulerExteriorCell_nhdsGT_zero u i j⟩

end

end RHTower
