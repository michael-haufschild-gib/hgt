import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction

/-!
# Gamma-sewn exterior aperture height current

The Gamma-sewn prime/valuation ray has a universal singular aperture velocity at the lossless
boundary.  That scalar mode disappears in the antisymmetric two-cell current before a norm is
formed.  On one prime tower the surviving boundary current is exactly the difference of the
physical midpoint heights `(e + 1/2) * log p`.

This module records the source object, proves its exact cross-depth law at every positive aperture,
and proves the renormalized boundary limit.  It also packages the finite positive exterior energy.
No Xi zero, target eigenvector, or RH-equivalent positivity assumption enters these definitions.
-/

open scoped BigOperators
open Filter Set

namespace RHTower

noncomputable section

/-- Closed logarithmic velocity of a Gamma-sewn prime/valuation cell. -/
def gammaSewnMobiusApertureCellVelocity
    (x : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  let q := xiMobiusContinuousApertureDiskNode x p
  Real.log (p : ℝ) *
    (2 * q ^ 2 / (1 - q ^ 2) + q ^ 4 / (1 + q ^ 4) - e)

/-- Antisymmetric two-cell current obtained by removing the common aperture velocity before
squaring. -/
def gammaSewnMobiusApertureExteriorCell
    (x : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusContinuousApertureFeature x i.1 i.2 *
    gammaSewnMobiusContinuousApertureFeature x j.1 j.2 *
      (gammaSewnMobiusApertureCellVelocity x j.1 j.2 -
        gammaSewnMobiusApertureCellVelocity x i.1 i.2)

/-- Physical midpoint height of a prime-power valuation cell. -/
def gammaSewnMobiusApertureCellMidHeight
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  ((e : ℝ) + 1 / 2) * Real.log (p : ℝ)

/-- The prime-dependent regular error left after subtracting the universal aperture pole and the
physical midpoint height from the closed cell velocity.  Its definition is source-forced; no
response or target datum enters. -/
def gammaSewnMobiusAperturePrimeCenteringError
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSewnMobiusApertureCellVelocity x p 0 - 1 / x +
    (1 / 2) * Real.log (p : ℝ)

/-- Boundary amplitude retained by the first Gamma-sewn Rees symbol. -/
def gammaSewnMobiusApertureBoundaryAmplitude (p : Nat.Primes) : ℝ :=
  gammaSewnMobiusReesPrincipalSymbol 0 p

/-- Boundary exterior current exposed after cancellation of the universal aperture pole. -/
def gammaSewnMobiusApertureBoundaryExteriorCell
    (i j : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusApertureBoundaryAmplitude i.1 *
    gammaSewnMobiusApertureBoundaryAmplitude j.1 *
      (gammaSewnMobiusApertureCellMidHeight i.1 i.2 -
        gammaSewnMobiusApertureCellMidHeight j.1 j.2)

theorem gammaSewnMobiusApertureBoundaryAmplitude_pos
    (p : Nat.Primes) :
    0 < gammaSewnMobiusApertureBoundaryAmplitude p := by
  unfold gammaSewnMobiusApertureBoundaryAmplitude
    gammaSewnMobiusReesPrincipalSymbol
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.one_lt
  exact mul_pos (div_pos hq (by positivity)) (by
    simpa using Real.log_pos hp1)

theorem gammaSewnMobiusContinuousApertureFeature_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (e : ℕ) :
    0 < gammaSewnMobiusContinuousApertureFeature x p e := by
  rw [gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  have hu := xiMobiusContinuousApertureDiskNode_pos x p
  have hu1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  exact mul_pos
    (gammaSewnMobiusValuationContractionMultiplier_pos x p)
    (mul_pos (mul_pos (div_pos hq (by positivity)) (sub_pos.mpr hu1))
      (pow_pos hu e))

/-- Logarithmic derivative of the Gamma-sewn contraction multiplier.  This is extracted from its
exact fourth-power law, using positivity to remove the fourth power without choosing a branch. -/
theorem hasDerivAt_gammaSewnMobiusValuationContractionMultiplier
    {x : ℝ} (p : Nat.Primes) :
    HasDerivAt
      (fun y : ℝ => gammaSewnMobiusValuationContractionMultiplier y p)
      (gammaSewnMobiusValuationContractionMultiplier x p * Real.log (p : ℝ) *
        (-xiMobiusContinuousApertureDiskNode x p /
            (1 + xiMobiusContinuousApertureDiskNode x p) +
          xiMobiusContinuousApertureDiskNode x p ^ 4 /
            (1 + xiMobiusContinuousApertureDiskNode x p ^ 4))) x := by
  let q : ℝ → ℝ := fun y => xiMobiusContinuousApertureDiskNode y p
  let C : ℝ → ℝ := fun y => gammaSewnMobiusValuationContractionMultiplier y p
  let L := Real.log (p : ℝ)
  have hq : HasDerivAt q (-L * q x) x := by
    dsimp only [q, L]
    unfold xiMobiusContinuousApertureDiskNode
    apply (((Real.hasDerivAt_exp (-x * Real.log (p : ℝ))).comp x
      ((hasDerivAt_neg x).mul_const (Real.log (p : ℝ)))).congr_deriv (by
        ring)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => by
      simp only [Function.comp_apply]
  have hCdiff : DifferentiableAt ℝ C x := by
    have hbase : DifferentiableAt ℝ
        (fun y : ℝ => Real.cosh (2 * y * Real.log (p : ℝ))) x := by
      fun_prop
    have hchar : DifferentiableAt ℝ
        (fun y : ℝ => semilocalArchimedeanCharacteristic
          (2 * y * Real.log (p : ℝ))) x := by
      unfold semilocalArchimedeanCharacteristic
      exact hbase.rpow_const (Or.inl (Real.cosh_pos _).ne')
    have hcharPos : 0 < semilocalArchimedeanCharacteristic
        (2 * x * Real.log (p : ℝ)) :=
      Real.rpow_pos_of_pos (Real.cosh_pos _) _
    have hsqrtChar := hchar.sqrt hcharPos.ne'
    have hqDiff := hq.differentiableAt
    have hqPos := xiMobiusContinuousApertureDiskNode_pos x p
    have hsqrtq := hqDiff.sqrt hqPos.ne'
    have hrec := ((differentiableAt_const (c := (1 : ℝ))).add hqDiff).div
      hsqrtq (Real.sqrt_pos.2 hqPos).ne'
    dsimp only [C, q] at hrec ⊢
    unfold gammaSewnMobiusValuationContractionMultiplier
      xiMobiusPrimeSchurApertureValuationRecovery
    exact ((differentiableAt_const (c := (1 / 2 : ℝ))).mul hsqrtChar).mul hrec
  have hCpow := hCdiff.hasDerivAt.pow 4
  have hden : 8 * (1 + q x ^ 4) ≠ 0 := by positivity
  have hrightRaw := ((hq.const_add 1).pow 4).div
    ((hq.pow 4).const_add 1 |>.const_mul 8) hden
  simp only [Pi.pow_apply] at hrightRaw
  have hright : HasDerivAt (fun y => C y ^ 4)
      (4 * C x ^ 4 * L *
        (-q x / (1 + q x) + q x ^ 4 / (1 + q x ^ 4))) x := by
    have hrightDeriv : HasDerivAt _
        (4 * C x ^ 4 * L *
          (-q x / (1 + q x) + q x ^ 4 / (1 + q x ^ 4))) x :=
      hrightRaw.congr_deriv (by
        have hqpos := xiMobiusContinuousApertureDiskNode_pos x p
        have hqplus : 1 + q x ≠ 0 := by positivity
        have hqfourplus : 1 + q x ^ 4 ≠ 0 := by positivity
        have hC4 := gammaSewnMobiusValuationContractionMultiplier_pow_four x p
        change C x ^ 4 = (1 + q x) ^ 4 / (8 * (1 + q x ^ 4)) at hC4
        rw [hC4]
        field_simp [hqpos.ne', hqplus, hqfourplus]
        ring)
    exact hrightDeriv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by
        simpa only [C, q, Pi.div_apply, Pi.pow_apply] using
          gammaSewnMobiusValuationContractionMultiplier_pow_four y p)
  have hderiv := hCpow.unique hright
  have hCpos := gammaSewnMobiusValuationContractionMultiplier_pos x p
  have htarget :
      gammaSewnMobiusValuationContractionMultiplier x p * Real.log (p : ℝ) *
          (-xiMobiusContinuousApertureDiskNode x p /
              (1 + xiMobiusContinuousApertureDiskNode x p) +
            xiMobiusContinuousApertureDiskNode x p ^ 4 /
              (1 + xiMobiusContinuousApertureDiskNode x p ^ 4)) =
        deriv (fun y => gammaSewnMobiusValuationContractionMultiplier y p) x := by
    dsimp only [C, q, L] at hderiv
    have hfactor :
        4 * gammaSewnMobiusValuationContractionMultiplier x p ^ 3 ≠ 0 := by
      exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hCpos.ne')
    apply (mul_left_cancel₀ hfactor)
    norm_num at hderiv
    calc
      4 * gammaSewnMobiusValuationContractionMultiplier x p ^ 3 *
          (gammaSewnMobiusValuationContractionMultiplier x p * Real.log (p : ℝ) *
            (-xiMobiusContinuousApertureDiskNode x p /
                (1 + xiMobiusContinuousApertureDiskNode x p) +
              xiMobiusContinuousApertureDiskNode x p ^ 4 /
                (1 + xiMobiusContinuousApertureDiskNode x p ^ 4))) =
        4 * gammaSewnMobiusValuationContractionMultiplier x p ^ 4 *
          Real.log (p : ℝ) *
            (-xiMobiusContinuousApertureDiskNode x p /
                (1 + xiMobiusContinuousApertureDiskNode x p) +
              xiMobiusContinuousApertureDiskNode x p ^ 4 /
                (1 + xiMobiusContinuousApertureDiskNode x p ^ 4)) := by ring
      _ = 4 * gammaSewnMobiusValuationContractionMultiplier x p ^ 3 *
          deriv (fun y => gammaSewnMobiusValuationContractionMultiplier y p) x := hderiv.symm
  simpa only [C] using hCdiff.hasDerivAt.congr_deriv htarget.symm

/-- The closed cell velocity is the actual logarithmic aperture derivative of the literal
Gamma-sewn prime/valuation feature. -/
theorem hasDerivAt_gammaSewnMobiusContinuousApertureFeature
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) (e : ℕ) :
    HasDerivAt
      (fun y : ℝ => gammaSewnMobiusContinuousApertureFeature y p e)
      (gammaSewnMobiusApertureCellVelocity x p e *
        gammaSewnMobiusContinuousApertureFeature x p e) x := by
  let q : ℝ → ℝ := fun y => xiMobiusContinuousApertureDiskNode y p
  let C : ℝ → ℝ := fun y => gammaSewnMobiusValuationContractionMultiplier y p
  let L := Real.log (p : ℝ)
  let a := xiTransversePrimeApertureDiskNode 1 p /
    (1 + xiTransversePrimeApertureDiskNode 1 p)
  have hq : HasDerivAt q (-L * q x) x := by
    dsimp only [q, L]
    unfold xiMobiusContinuousApertureDiskNode
    apply (((Real.hasDerivAt_exp (-x * Real.log (p : ℝ))).comp x
      ((hasDerivAt_neg x).mul_const (Real.log (p : ℝ)))).congr_deriv (by
        ring)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => by
      simp only [Function.comp_apply]
  have hC := hasDerivAt_gammaSewnMobiusValuationContractionMultiplier (x := x) p
  have hgap : HasDerivAt (fun y : ℝ => 1 - q y) (L * q x) x := by
    apply (((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub hq).congr_deriv (by
      ring)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hqpos := xiMobiusContinuousApertureDiskNode_pos x p
  have hqone := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hqminus : 1 - q x ≠ 0 := (sub_pos.mpr hqone).ne'
  have hgeomRaw := hgap.mul (hq.pow e)
  simp only [Pi.pow_apply] at hgeomRaw
  have hgeom : HasDerivAt
      (fun y : ℝ => (1 - q y) * q y ^ e)
      (L * (q x / (1 - q x) - e) * ((1 - q x) * q x ^ e)) x := by
    have hgeomDeriv : HasDerivAt _
        (L * (q x / (1 - q x) - e) * ((1 - q x) * q x ^ e)) x :=
      hgeomRaw.congr_deriv (by
        cases e with
        | zero =>
            simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one]
            field_simp [hqminus]
            ring
        | succ e =>
            simp only [Nat.cast_succ, pow_succ, Nat.succ_sub_one]
            field_simp [hqpos.ne', hqminus]
            ring)
    exact hgeomDeriv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsource := (hC.mul hgeom).const_mul a
  simp only [Pi.mul_apply] at hsource
  have hsourceDeriv : HasDerivAt _
      (gammaSewnMobiusApertureCellVelocity x p e *
        gammaSewnMobiusContinuousApertureFeature x p e) x :=
    hsource.congr_deriv (by
      have hqplus : 1 + q x ≠ 0 := by positivity
      have hqfourplus : 1 + q x ^ 4 ≠ 0 := by positivity
      have hqSq : 1 - q x ^ 2 ≠ 0 := by
        have hprod : 0 < (1 - q x) * (1 + q x) :=
          mul_pos (sub_pos.mpr hqone) (by linarith)
        nlinarith
      have hvelocity : gammaSewnMobiusApertureCellVelocity x p e =
          L *
            ((-q x / (1 + q x) + q x ^ 4 / (1 + q x ^ 4)) +
              (q x / (1 - q x) - e)) := by
        have hfrac :
            -q x / (1 + q x) + q x / (1 - q x) =
              2 * q x ^ 2 / (1 - q x ^ 2) := by
          field_simp [hqminus, hqplus, hqSq]
          ring
        unfold gammaSewnMobiusApertureCellVelocity
        simp only [q, L]
        rw [← hfrac]
        ring
      rw [hvelocity, gammaSewnMobiusContinuousApertureFeature,
        xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
      simp only [q, L, a]
      ring)
  exact hsourceDeriv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by
      simp only [gammaSewnMobiusContinuousApertureFeature,
        xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric, q, a]
      ring)

@[simp] theorem gammaSewnMobiusApertureExteriorCell_self
    (x : ℝ) (i : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureExteriorCell x i i = 0 := by
  simp [gammaSewnMobiusApertureExteriorCell]

theorem gammaSewnMobiusApertureExteriorCell_swap
    (x : ℝ) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureExteriorCell x j i =
      -gammaSewnMobiusApertureExteriorCell x i j := by
  unfold gammaSewnMobiusApertureExteriorCell
  ring

/-- Before taking a Gram square, the normalized exterior current is exactly the pairwise velocity
reporter.  Positivity of the literal source features makes the normalization source-intrinsic. -/
theorem gammaSewnMobiusApertureExteriorCell_div_features
    {x : ℝ} (hx : 0 < x) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureExteriorCell x i j /
        (gammaSewnMobiusContinuousApertureFeature x i.1 i.2 *
          gammaSewnMobiusContinuousApertureFeature x j.1 j.2) =
      gammaSewnMobiusApertureCellVelocity x j.1 j.2 -
        gammaSewnMobiusApertureCellVelocity x i.1 i.2 := by
  have hi := gammaSewnMobiusContinuousApertureFeature_pos hx i.1 i.2
  have hj := gammaSewnMobiusContinuousApertureFeature_pos hx j.1 j.2
  unfold gammaSewnMobiusApertureExteriorCell
  field_simp [hi.ne', hj.ne']

/-- A single rooted velocity plus the exterior current reconstructs every cell velocity.  This is
the pointed repair of the common-mode loss inherent in an unrooted pairwise reporter. -/
theorem gammaSewnMobiusApertureCellVelocity_eq_root_add_exterior
    {x : ℝ} (hx : 0 < x) (root i : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureCellVelocity x i.1 i.2 =
      gammaSewnMobiusApertureCellVelocity x root.1 root.2 +
        gammaSewnMobiusApertureExteriorCell x root i /
          (gammaSewnMobiusContinuousApertureFeature x root.1 root.2 *
            gammaSewnMobiusContinuousApertureFeature x i.1 i.2) := by
  rw [gammaSewnMobiusApertureExteriorCell_div_features hx]
  ring

/-- The complicated Gamma/aperture velocity is common to every depth on one prime tower; its
difference is exactly the logarithmic depth gap. -/
theorem gammaSewnMobiusApertureCellVelocity_samePrime_sub
    (x : ℝ) (p : Nat.Primes) (e f : ℕ) :
    gammaSewnMobiusApertureCellVelocity x p e -
        gammaSewnMobiusApertureCellVelocity x p f =
      ((f : ℝ) - e) * Real.log (p : ℝ) := by
  unfold gammaSewnMobiusApertureCellVelocity
  ring

/-- Exact separation of every cell velocity into a common singular pole, the physical midpoint
height, and a prime-only regular error.  The pole therefore cancels before any exterior norm is
formed, including across different prime towers. -/
theorem gammaSewnMobiusApertureCellVelocity_eq_universalPole_sub_midHeight_add_error
    (x : ℝ) (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusApertureCellVelocity x p e =
      1 / x - gammaSewnMobiusApertureCellMidHeight p e +
        gammaSewnMobiusAperturePrimeCenteringError x p := by
  rw [gammaSewnMobiusApertureCellMidHeight,
    gammaSewnMobiusAperturePrimeCenteringError]
  have h := gammaSewnMobiusApertureCellVelocity_samePrime_sub x p e 0
  norm_num at h ⊢
  linarith

/-- Cross-prime velocity differences contain no universal aperture pole.  What survives is the
signed midpoint-height gap plus a difference of prime-centering errors. -/
theorem gammaSewnMobiusApertureCellVelocity_sub_eq_midHeight_sub_add_error_sub
    (x : ℝ) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureCellVelocity x j.1 j.2 -
        gammaSewnMobiusApertureCellVelocity x i.1 i.2 =
      gammaSewnMobiusApertureCellMidHeight i.1 i.2 -
          gammaSewnMobiusApertureCellMidHeight j.1 j.2 +
        (gammaSewnMobiusAperturePrimeCenteringError x j.1 -
          gammaSewnMobiusAperturePrimeCenteringError x i.1) := by
  rw [gammaSewnMobiusApertureCellVelocity_eq_universalPole_sub_midHeight_add_error,
    gammaSewnMobiusApertureCellVelocity_eq_universalPole_sub_midHeight_add_error]
  ring

/-- Exact all-cell decomposition of the source exterior current.  Unlike a post-hoc Gram
factorization, this identity occurs before squaring and visibly removes the universal pole. -/
theorem gammaSewnMobiusApertureExteriorCell_eq_midHeight_current_add_centering_error
    (x : ℝ) (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureExteriorCell x i j =
      gammaSewnMobiusContinuousApertureFeature x i.1 i.2 *
        gammaSewnMobiusContinuousApertureFeature x j.1 j.2 *
          (gammaSewnMobiusApertureCellMidHeight i.1 i.2 -
              gammaSewnMobiusApertureCellMidHeight j.1 j.2 +
            (gammaSewnMobiusAperturePrimeCenteringError x j.1 -
              gammaSewnMobiusAperturePrimeCenteringError x i.1)) := by
  unfold gammaSewnMobiusApertureExteriorCell
  rw [gammaSewnMobiusApertureCellVelocity_sub_eq_midHeight_sub_add_error_sub]

/-- Exact positive-aperture cross-depth exterior current. -/
theorem gammaSewnMobiusApertureExteriorCell_samePrime
    (x : ℝ) (p : Nat.Primes) (e f : ℕ) :
    gammaSewnMobiusApertureExteriorCell x (p, e) (p, f) =
      gammaSewnMobiusContinuousApertureFeature x p e *
        gammaSewnMobiusContinuousApertureFeature x p f *
          (((e : ℝ) - f) * Real.log (p : ℝ)) := by
  rw [gammaSewnMobiusApertureExteriorCell]
  simp only
  rw [gammaSewnMobiusApertureCellVelocity_samePrime_sub]

/-- Every two distinct depths on one prime tower carry nonzero connected exterior area. -/
theorem gammaSewnMobiusApertureExteriorCell_samePrime_ne_zero
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) {e f : ℕ} (hef : e ≠ f) :
    gammaSewnMobiusApertureExteriorCell x (p, e) (p, f) ≠ 0 := by
  rw [gammaSewnMobiusApertureExteriorCell_samePrime]
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hcast : (f : ℝ) ≠ (e : ℝ) := by exact_mod_cast hef.symm
  exact mul_ne_zero
    (mul_ne_zero
      (gammaSewnMobiusContinuousApertureFeature_pos hx p e).ne'
      (gammaSewnMobiusContinuousApertureFeature_pos hx p f).ne')
    (mul_ne_zero (sub_ne_zero.mpr hcast.symm)
      (Real.log_pos hp1).ne')

@[simp] theorem gammaSewnMobiusApertureBoundaryExteriorCell_self
    (i : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureBoundaryExteriorCell i i = 0 := by
  simp [gammaSewnMobiusApertureBoundaryExteriorCell]

theorem gammaSewnMobiusApertureBoundaryExteriorCell_swap
    (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureBoundaryExteriorCell j i =
      -gammaSewnMobiusApertureBoundaryExteriorCell i j := by
  unfold gammaSewnMobiusApertureBoundaryExteriorCell
  ring

/-- The normalized boundary current is exactly the signed physical midpoint-height difference. -/
theorem gammaSewnMobiusApertureBoundaryExteriorCell_div_amplitudes
    (i j : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureBoundaryExteriorCell i j /
        (gammaSewnMobiusApertureBoundaryAmplitude i.1 *
          gammaSewnMobiusApertureBoundaryAmplitude j.1) =
      gammaSewnMobiusApertureCellMidHeight i.1 i.2 -
        gammaSewnMobiusApertureCellMidHeight j.1 j.2 := by
  have hi := gammaSewnMobiusApertureBoundaryAmplitude_pos i.1
  have hj := gammaSewnMobiusApertureBoundaryAmplitude_pos j.1
  unfold gammaSewnMobiusApertureBoundaryExteriorCell
  field_simp [hi.ne', hj.ne']

/-- One rooted midpoint height plus the boundary exterior current reconstructs every physical cell
height.  The pole-cancelling current is therefore not a scalar collapse when kept pointed. -/
theorem gammaSewnMobiusApertureCellMidHeight_eq_root_sub_boundaryExterior
    (root i : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureCellMidHeight i.1 i.2 =
      gammaSewnMobiusApertureCellMidHeight root.1 root.2 -
        gammaSewnMobiusApertureBoundaryExteriorCell root i /
          (gammaSewnMobiusApertureBoundaryAmplitude root.1 *
            gammaSewnMobiusApertureBoundaryAmplitude i.1) := by
  rw [gammaSewnMobiusApertureBoundaryExteriorCell_div_amplitudes]
  ring

theorem gammaSewnMobiusApertureBoundaryExteriorCell_ne_zero_of_midHeight_ne
    {i j : Nat.Primes × ℕ}
    (hheight : gammaSewnMobiusApertureCellMidHeight i.1 i.2 ≠
      gammaSewnMobiusApertureCellMidHeight j.1 j.2) :
    gammaSewnMobiusApertureBoundaryExteriorCell i j ≠ 0 := by
  unfold gammaSewnMobiusApertureBoundaryExteriorCell
  exact mul_ne_zero
    (mul_ne_zero
      (gammaSewnMobiusApertureBoundaryAmplitude_pos i.1).ne'
      (gammaSewnMobiusApertureBoundaryAmplitude_pos j.1).ne')
    (sub_ne_zero.mpr hheight)

/-- Every fixed valuation cell has the first Rees symbol as its lossless boundary amplitude. -/
theorem tendsto_gammaSewnMobiusContinuousApertureFeature_div_aperture
    (p : Nat.Primes) (e : ℕ) :
    Tendsto
      (fun x : ℝ => gammaSewnMobiusContinuousApertureFeature x p e / x)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (gammaSewnMobiusApertureBoundaryAmplitude p)) := by
  simpa [gammaSewnMobiusApertureBoundaryAmplitude,
    gammaSewnMobiusContinuousApertureDepthDifference] using!
    (tendsto_gammaSewnMobiusContinuousApertureDepthDifference_div_pow 0 p e)

/-- On one prime tower the renormalized exterior aperture current converges to the exact
mid-height boundary area.  The universal aperture pole has cancelled before this limit. -/
theorem tendsto_gammaSewnMobiusApertureExteriorCell_samePrime_div_sq
    (p : Nat.Primes) (e f : ℕ) :
    Tendsto
      (fun x : ℝ =>
        gammaSewnMobiusApertureExteriorCell x (p, e) (p, f) / x ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (gammaSewnMobiusApertureBoundaryExteriorCell (p, e) (p, f))) := by
  have he := tendsto_gammaSewnMobiusContinuousApertureFeature_div_aperture p e
  have hf := tendsto_gammaSewnMobiusContinuousApertureFeature_div_aperture p f
  have hlim := (he.mul hf).mul
    (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => ((e : ℝ) - f) * Real.log (p : ℝ))
      (nhdsWithin (0 : ℝ) (Ioi 0)) _)
  have heq :
      (gammaSewnMobiusApertureBoundaryAmplitude p *
          gammaSewnMobiusApertureBoundaryAmplitude p) *
          (((e : ℝ) - f) * Real.log (p : ℝ)) =
        gammaSewnMobiusApertureBoundaryExteriorCell (p, e) (p, f) := by
    unfold gammaSewnMobiusApertureBoundaryExteriorCell
      gammaSewnMobiusApertureCellMidHeight
    simp only
    ring
  rw [← heq]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [gammaSewnMobiusApertureExteriorCell_samePrime]
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp [hx0]

/-- Ordered finite exterior energy.  The diagonal is automatically absent because the current is
antisymmetric. -/
def gammaSewnMobiusApertureBoundaryExteriorEnergy
    (S : Finset (Nat.Primes × ℕ)) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S,
    gammaSewnMobiusApertureBoundaryExteriorCell i j ^ 2

theorem gammaSewnMobiusApertureBoundaryExteriorEnergy_nonneg
    (S : Finset (Nat.Primes × ℕ)) :
    0 ≤ gammaSewnMobiusApertureBoundaryExteriorEnergy S := by
  unfold gammaSewnMobiusApertureBoundaryExteriorEnergy
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A height-localized packet has strict exterior energy as soon as it contains two distinct
physical midpoint heights. -/
theorem gammaSewnMobiusApertureBoundaryExteriorEnergy_pos_of_pair
    {S : Finset (Nat.Primes × ℕ)} {i j : Nat.Primes × ℕ}
    (hi : i ∈ S) (hj : j ∈ S)
    (hheight : gammaSewnMobiusApertureCellMidHeight i.1 i.2 ≠
      gammaSewnMobiusApertureCellMidHeight j.1 j.2) :
    0 < gammaSewnMobiusApertureBoundaryExteriorEnergy S := by
  unfold gammaSewnMobiusApertureBoundaryExteriorEnergy
  apply Finset.sum_pos'
  · intro a _ha
    exact Finset.sum_nonneg fun b _hb => sq_nonneg _
  · refine ⟨i, hi, ?_⟩
    apply Finset.sum_pos'
    · intro a _ha
      exact sq_nonneg _
    · exact ⟨j, hj, sq_pos_of_ne_zero
        (gammaSewnMobiusApertureBoundaryExteriorCell_ne_zero_of_midHeight_ne
          hheight)⟩

end

end RHTower
