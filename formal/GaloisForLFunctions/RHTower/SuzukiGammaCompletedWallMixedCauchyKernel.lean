import GaloisForLFunctions.RHTower.SuzukiWardAtomicContinuousLightWeld

/-!
# Mixed Cauchy covariance in the literal completed Suzuki wall

The finite prime wall is made from anchored one-depth atoms, while the regular
screw wall is made from two-depth secants.  This file isolates their actual
mixed Cauchy covariance.  It deliberately does not replace that pair by the
secant--secant covariance used for the raw reporter packet.
-/

open Complex MeasureTheory Set
open Filter
open scoped BigOperators ComplexConjugate Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Literal anchored prime atom at source lag `p`. -/
def suzukiCauchyAnchoredWallAtom (p t : ℝ) : ℂ :=
  1 - suzukiCauchyWallPhase (-p) t

/-- Literal two-depth regular-screw secant at source lag `q`. -/
def suzukiCauchyWallSecantAtLag (q t : ℝ) : ℂ :=
  suzukiCauchyWallPhase (-q) t - suzukiCauchyWallPhase (-2 * q) t

/-- Cauchy covariance of the actual anchored atom against the actual secant. -/
def suzukiCauchyAnchoredSecantWallGram (p q : ℝ) : ℂ :=
  suzukiCauchyWallPhaseInner 0 (-q) -
    suzukiCauchyWallPhaseInner 0 (-2 * q) -
    suzukiCauchyWallPhaseInner (-p) (-q) +
      suzukiCauchyWallPhaseInner (-p) (-2 * q)

/-- Real form of the literal anchored--secant Cauchy covariance. -/
def suzukiCauchyAnchoredSecantGram (p q : ℝ) : ℝ :=
  Real.exp (-|q| / 2) - Real.exp (-|2 * q| / 2) -
    Real.exp (-|p - q| / 2) + Real.exp (-|p - 2 * q| / 2)

/-- Real translation kernel induced directly by the literal Cauchy wall
phase pairing. -/
def suzukiCauchyWallPhaseRealKernel (x : ℝ) : ℝ :=
  Real.exp (-|x| / 2)

theorem suzukiCauchyWallPhaseInner_eq_realKernel
    (x y : ℝ) :
    suzukiCauchyWallPhaseInner x y =
      (suzukiCauchyWallPhaseRealKernel (x - y) : ℂ) := by
  rw [suzukiCauchyWallPhaseInner_eq, suzukiCauchyWallPhaseRealKernel]

/-- Cauchy self-Gram of one literal anchored prime atom. -/
def suzukiCauchyAnchoredWallAtomGram (p : ℝ) : ℝ :=
  2 * (1 - Real.exp (-|p| / 2))

/-- Cauchy self-Gram of one literal two-depth regular-screw secant. -/
def suzukiCauchyWallSecantGram (q : ℝ) : ℝ :=
  2 * (1 - Real.exp (-|q| / 2))

/-- The three literal Cauchy phase nodes for an anchored atom minus a
midpoint regular screw: `φ₀ - λ φ_{-p/2} + (λ - 1) φ_{-p}`. -/
def suzukiCauchyAnchoredSecantMidpointAffineNodes (p : ℝ) : Fin 3 → ℝ :=
  Fin.cases 0 (Fin.cases (-p / 2) (fun _ => -p))

/-- Coefficients of the literal midpoint affine prime--regular packet. -/
def suzukiCauchyAnchoredSecantMidpointAffineCoefficients
    (a : ℝ) : Fin 3 → ℝ :=
  Fin.cases 1 (Fin.cases (-a) (fun _ => a - 1))

/-- Exact finite Cauchy Gram energy of one literal prime atom after payment
by one regular screw at its favourable midpoint.  This is a finite packet of
the actual Cauchy wall phases, not an auxiliary reporter norm. -/
def suzukiCauchyAnchoredSecantMidpointAffineCauchyEnergy
    (p a : ℝ) : ℝ :=
  realKernelPacketEnergy suzukiCauchyWallPhaseRealKernel
    (suzukiCauchyAnchoredSecantMidpointAffineNodes p)
    (suzukiCauchyAnchoredSecantMidpointAffineCoefficients a)

/-- Source-level quadratic expansion of the literal midpoint packet. -/
def suzukiCauchyAnchoredSecantMidpointAffineQuadratic
    (p a : ℝ) : ℝ :=
  suzukiCauchyAnchoredWallAtomGram p -
    2 * a * suzukiCauchyAnchoredSecantGram p (p / 2) +
      a ^ 2 * suzukiCauchyWallSecantGram (p / 2)

/-- Projection scalar for the one-secant Cauchy payment at the canonical
interior midpoint. -/
def suzukiCauchyAnchoredSecantMidpointOptimalCoefficient (p : ℝ) : ℝ :=
  (1 + Real.exp (-p / 4)) / 2

theorem suzukiCauchyAnchoredSecantGram_half_eq
    {p : ℝ} (hp : 0 ≤ p) :
    suzukiCauchyAnchoredSecantGram p (p / 2) =
      1 - Real.exp (-p / 2) := by
  rw [suzukiCauchyAnchoredSecantGram]
  have hhalf : 0 ≤ p / 2 := by linarith
  rw [abs_of_nonneg hhalf]
  have htwo : |2 * (p / 2)| = p := by
    rw [show 2 * (p / 2) = p by ring, abs_of_nonneg hp]
  rw [htwo]
  have hsub : |p - p / 2| = p / 2 := by
    rw [show p - p / 2 = p / 2 by ring, abs_of_nonneg hhalf]
  rw [hsub]
  have hlast : |p - 2 * (p / 2)| = 0 := by
    rw [show p - 2 * (p / 2) = 0 by ring]
    norm_num
  rw [hlast]
  norm_num
  ring

theorem suzukiCauchyAnchoredWallAtomGram_eq
    {p : ℝ} (hp : 0 ≤ p) :
    suzukiCauchyAnchoredWallAtomGram p =
      2 * (1 - Real.exp (-p / 2)) := by
  rw [suzukiCauchyAnchoredWallAtomGram, abs_of_nonneg hp]

theorem suzukiCauchyWallSecantGram_half_eq
    {p : ℝ} (hp : 0 ≤ p) :
    suzukiCauchyWallSecantGram (p / 2) =
      2 * (1 - Real.exp (-p / 4)) := by
  rw [suzukiCauchyWallSecantGram,
    abs_of_nonneg (by linarith : 0 ≤ p / 2)]
  congr 3
  ring

/-- The finite Cauchy packet is exactly the literal anchored--secant Gram
quadratic.  Hence the affine experiment retains the phase-level source
rather than replacing it by an unrelated Hilbert-space proxy. -/
theorem suzukiCauchyAnchoredSecantMidpointAffineCauchyEnergy_eq_quadratic
    {p a : ℝ} (hp : 0 ≤ p) :
    suzukiCauchyAnchoredSecantMidpointAffineCauchyEnergy p a =
      suzukiCauchyAnchoredSecantMidpointAffineQuadratic p a := by
  rw [suzukiCauchyAnchoredSecantMidpointAffineCauchyEnergy,
    realKernelPacketEnergy]
  simp only [Fin.sum_univ_succ, suzukiCauchyAnchoredSecantMidpointAffineNodes,
    suzukiCauchyAnchoredSecantMidpointAffineCoefficients,
    Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_zero, add_zero,
    sub_zero, sub_self, zero_sub, neg_neg]
  rw [show -p - -p / 2 = -p / 2 by ring,
    show -p / 2 - -p = p / 2 by ring]
  simp only [suzukiCauchyWallPhaseRealKernel, abs_zero, neg_zero,
    abs_neg, abs_of_nonneg hp,
    abs_of_nonneg (by linarith : 0 ≤ p / 2)]
  rw [
    suzukiCauchyAnchoredSecantMidpointAffineQuadratic,
    suzukiCauchyAnchoredWallAtomGram_eq hp,
    suzukiCauchyWallSecantGram_half_eq hp,
    suzukiCauchyAnchoredSecantGram_half_eq hp]
  have habs : |p * ((-1 : ℝ) / 2)| = p / 2 := by
    rw [show p * ((-1 : ℝ) / 2) = -(p / 2) by ring,
      abs_neg, abs_of_nonneg (by linarith : 0 ≤ p / 2)]
  ring_nf
  rw [habs, Real.exp_zero]
  ring

theorem suzukiCauchyAnchoredSecantMidpointAffineQuadratic_complete_square
    {p a : ℝ} (hp : 0 ≤ p) :
    suzukiCauchyAnchoredSecantMidpointAffineQuadratic p a =
      suzukiCauchyAnchoredSecantMidpointAffineQuadratic p
        (suzukiCauchyAnchoredSecantMidpointOptimalCoefficient p) +
        suzukiCauchyWallSecantGram (p / 2) *
          (a - suzukiCauchyAnchoredSecantMidpointOptimalCoefficient p) ^ 2 := by
  have hexp : Real.exp (-p / 2) = Real.exp (-p / 4) ^ 2 := by
    rw [show -p / 2 = -p / 4 + -p / 4 by ring, Real.exp_add]
    ring
  simp only [suzukiCauchyAnchoredSecantMidpointAffineQuadratic,
    suzukiCauchyAnchoredSecantMidpointOptimalCoefficient,
    suzukiCauchyAnchoredWallAtomGram_eq hp,
    suzukiCauchyWallSecantGram_half_eq hp,
    suzukiCauchyAnchoredSecantGram_half_eq hp]
  rw [hexp]
  ring

theorem suzukiCauchyAnchoredSecantMidpointAffineQuadratic_optimal_eq
    {p : ℝ} (hp : 0 ≤ p) :
    suzukiCauchyAnchoredSecantMidpointAffineQuadratic p
      (suzukiCauchyAnchoredSecantMidpointOptimalCoefficient p) =
      (1 - Real.exp (-p / 2)) *
        (3 - Real.exp (-p / 4)) / 2 := by
  have hexp : Real.exp (-p / 2) = Real.exp (-p / 4) ^ 2 := by
    rw [show -p / 2 = -p / 4 + -p / 4 by ring, Real.exp_add]
    ring
  simp only [suzukiCauchyAnchoredSecantMidpointAffineQuadratic,
    suzukiCauchyAnchoredSecantMidpointOptimalCoefficient,
    suzukiCauchyAnchoredWallAtomGram_eq hp,
    suzukiCauchyWallSecantGram_half_eq hp,
    suzukiCauchyAnchoredSecantGram_half_eq hp]
  rw [hexp]
  ring

theorem suzukiCauchyWallSecantGram_nonneg
    (q : ℝ) :
    0 ≤ suzukiCauchyWallSecantGram q := by
  rw [suzukiCauchyWallSecantGram]
  apply mul_nonneg (by norm_num)
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  have hq : 0 ≤ |q| := abs_nonneg q
  linarith

/-- Exact dyadic telescope in the literal Cauchy wall.  A one-depth anchored
atom is a finite cascade of two-depth regular secants plus an anchored atom
at the shrinking dyadic scale. -/
theorem suzukiCauchyAnchoredWallAtom_eq_dyadicSecant_sum
    (p t : ℝ) (n : ℕ) :
    suzukiCauchyAnchoredWallAtom p t =
      suzukiCauchyAnchoredWallAtom (p / (2 : ℝ) ^ n) t +
        ∑ j ∈ Finset.range n,
          suzukiCauchyWallSecantAtLag (p / (2 : ℝ) ^ (j + 1)) t := by
  induction n with
  | zero => simp [suzukiCauchyAnchoredWallAtom]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hdouble : 2 * (p / (2 : ℝ) ^ (n + 1)) =
          p / (2 : ℝ) ^ n := by
        rw [pow_succ]
        field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
      have hsplit : suzukiCauchyAnchoredWallAtom (p / (2 : ℝ) ^ n) t =
          suzukiCauchyAnchoredWallAtom (p / (2 : ℝ) ^ (n + 1)) t +
            suzukiCauchyWallSecantAtLag (p / (2 : ℝ) ^ (n + 1)) t := by
        have hneg : -2 * (p / (2 : ℝ) ^ (n + 1)) =
            -(p / (2 : ℝ) ^ n) := by linarith
        simp only [suzukiCauchyAnchoredWallAtom,
          suzukiCauchyWallSecantAtLag]
        rw [hneg]
        ring
      rw [hsplit]
      ring

/-- The exact Cauchy self-Gram of the dyadic telescope remainder is the
anchored atom Gram already used in the mixed-wall analysis. -/
theorem suzukiCauchyAnchoredWallAtomGram_eq_wallSelfGram
    (p : ℝ) :
    suzukiCauchyAnchoredWallGram 0 (-p) (-p) =
      (suzukiCauchyAnchoredWallAtomGram p : ℂ) := by
  rw [suzukiCauchyAnchoredWallGram,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyAnchoredWallAtomGram]
  simp only [sub_self, abs_zero, neg_zero]
  rw [show |0 - -p| = |p| by ring,
    show |-p - 0| = |p| by
      rw [show -p - 0 = -p by ring, abs_neg]]
  push_cast
  norm_num
  ring

/-- Dyadic secant cascades converge in exact Cauchy self-Gram to the literal
anchored atom: their only remainder has vanishing Cauchy energy. -/
theorem tendsto_suzukiCauchyAnchoredWallAtomGram_dyadic
    (p : ℝ) :
    Tendsto (fun n : ℕ =>
      suzukiCauchyAnchoredWallAtomGram (p / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscale : Tendsto (fun n : ℕ => p / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h := hpow.const_mul p
    have hident : (fun n : ℕ => p / (2 : ℝ) ^ n) =
        fun n : ℕ => p * (1 / 2 : ℝ) ^ n := by
      funext n
      rw [div_eq_mul_inv, ← inv_pow]
      norm_num
    rw [hident]
    simpa using h
  have hcont : Continuous suzukiCauchyAnchoredWallAtomGram := by
    unfold suzukiCauchyAnchoredWallAtomGram
    fun_prop
  have hlim := hcont.continuousAt.tendsto.comp hscale
  rw [show (0 : ℝ) = suzukiCauchyAnchoredWallAtomGram 0 by
    simp [suzukiCauchyAnchoredWallAtomGram]]
  change Tendsto (suzukiCauchyAnchoredWallAtomGram ∘
    fun n : ℕ => p / (2 : ℝ) ^ n) atTop
      (𝓝 (suzukiCauchyAnchoredWallAtomGram 0))
  exact hlim

/-- A literal regular-screw secant is the dilation coboundary of the
anchored prime-wall atom.  This is an identity before any scalar readout. -/
theorem suzukiCauchyWallSecantAtLag_eq_anchored_dilation
    (q t : ℝ) :
    suzukiCauchyWallSecantAtLag q t =
      suzukiCauchyAnchoredWallAtom (2 * q) t -
        suzukiCauchyAnchoredWallAtom q t := by
  simp only [suzukiCauchyWallSecantAtLag, suzukiCauchyAnchoredWallAtom]
  ring

/-- Exact dilation transfer for a regular-screw continuum.  It does not
allocate any coefficient: the fixed secant density is carried to the signed
anchored density forced by the dilation coboundary. -/
theorem intervalIntegral_suzukiCauchyWallSecantAtLag_eq_anchored_dilation
    (F : ℝ → ℂ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hF : ContinuousOn F (Icc 0 Q)) (t : ℝ) :
    (∫ q in 0..Q, suzukiCauchyWallSecantAtLag q t * F q) =
      (((2 : ℝ)⁻¹) •
        (∫ r in 0..Q * 2,
          suzukiCauchyAnchoredWallAtom r t * F (r / 2))) -
        ∫ r in 0..Q, suzukiCauchyAnchoredWallAtom r t * F r := by
  have hA : Continuous (fun r : ℝ => suzukiCauchyAnchoredWallAtom r t) := by
    unfold suzukiCauchyAnchoredWallAtom
    simp_rw [suzukiCauchyWallPhase_eq]
    fun_prop
  have hfirst : IntervalIntegrable
      (fun q : ℝ => suzukiCauchyAnchoredWallAtom (2 * q) t * F q)
      volume 0 Q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hQ]
    exact ((hA.comp (continuous_const.mul continuous_id)).continuousOn).mul hF
  have hsecond : IntervalIntegrable
      (fun q : ℝ => suzukiCauchyAnchoredWallAtom q t * F q)
      volume 0 Q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hQ]
    exact hA.continuousOn.mul hF
  have hscale := intervalIntegral.integral_comp_mul_right
    (a := (0 : ℝ)) (b := Q) (c := (2 : ℝ))
    (fun r : ℝ => suzukiCauchyAnchoredWallAtom r t * F (r / 2)) (by norm_num)
  have hscale' :
      (∫ q in 0..Q, suzukiCauchyAnchoredWallAtom (2 * q) t * F q) =
        ((2 : ℝ)⁻¹) •
          ∫ r in 0..Q * 2,
            suzukiCauchyAnchoredWallAtom r t * F (r / 2) := by
    calc
      _ = ∫ q in 0..Q,
          suzukiCauchyAnchoredWallAtom (q * 2) t * F (q * 2 / 2) := by
            apply intervalIntegral.integral_congr
            intro q hq
            change suzukiCauchyAnchoredWallAtom (2 * q) t * F q =
              suzukiCauchyAnchoredWallAtom (q * 2) t * F (q * 2 / 2)
            rw [show q * 2 = 2 * q by ring,
              show (2 * q) / 2 = q by ring]
      _ = _ := by
            simpa only [zero_mul] using hscale
  calc
    (∫ q in 0..Q, suzukiCauchyWallSecantAtLag q t * F q) =
        ∫ q in 0..Q,
          (suzukiCauchyAnchoredWallAtom (2 * q) t * F q -
            suzukiCauchyAnchoredWallAtom q t * F q) := by
          apply intervalIntegral.integral_congr
          intro q hq
          change suzukiCauchyWallSecantAtLag q t * F q =
            suzukiCauchyAnchoredWallAtom (2 * q) t * F q -
              suzukiCauchyAnchoredWallAtom q t * F q
          rw [suzukiCauchyWallSecantAtLag_eq_anchored_dilation]
          ring
    _ = (∫ q in 0..Q, suzukiCauchyAnchoredWallAtom (2 * q) t * F q) -
          ∫ q in 0..Q, suzukiCauchyAnchoredWallAtom q t * F q := by
          rw [intervalIntegral.integral_sub hfirst hsecond]
    _ = (((2 : ℝ)⁻¹) •
          (∫ r in 0..Q * 2,
            suzukiCauchyAnchoredWallAtom r t * F (r / 2))) -
          ∫ r in 0..Q, suzukiCauchyAnchoredWallAtom r t * F r := by
          rw [hscale']

/-- **Local affine no-go.**  At a nonzero literal prime lag, every scalar
payment by the single regular screw at the canonical interior midpoint leaves
at least half of the prime atom's Cauchy energy.  Hence this literal
one-regular-lag midpoint transport cannot be the missing producer; any
successful construction must use different or genuinely nonlocal source
coupling. -/
theorem suzukiCauchyAnchoredSecantMidpointAffineCauchyEnergy_half_atom_lower
    {p a : ℝ} (hp : 0 < p) :
    suzukiCauchyAnchoredWallAtomGram p / 2 ≤
      suzukiCauchyAnchoredSecantMidpointAffineCauchyEnergy p a := by
  rw [suzukiCauchyAnchoredSecantMidpointAffineCauchyEnergy_eq_quadratic hp.le,
    suzukiCauchyAnchoredSecantMidpointAffineQuadratic_complete_square hp.le,
    suzukiCauchyAnchoredSecantMidpointAffineQuadratic_optimal_eq hp.le,
    suzukiCauchyAnchoredWallAtomGram_eq hp.le]
  have hsq : 0 ≤ suzukiCauchyWallSecantGram (p / 2) *
      (a - suzukiCauchyAnchoredSecantMidpointOptimalCoefficient p) ^ 2 :=
    mul_nonneg (suzukiCauchyWallSecantGram_nonneg _) (sq_nonneg _)
  have hExp : Real.exp (-p / 4) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hhalf : 0 ≤ 1 - Real.exp (-p / 2) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hproduct : 0 ≤
      (1 - Real.exp (-p / 2)) * (1 - Real.exp (-p / 4)) :=
    mul_nonneg hhalf (sub_nonneg.mpr hExp)
  nlinarith

/-- The finite prime side of the literal completed wall is a finite sum of
anchored atoms at every real Cauchy height. -/
theorem suzukiUnitRieszPrimeWardWall_ofReal_eq_sum_anchored
    (N : ℕ) (t : ℝ) :
    suzukiUnitRieszPrimeWardWall N (t : ℂ) =
      ∑ k ∈ Finset.Icc 2 N,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt N : ℂ) *
          suzukiCauchyAnchoredWallAtom (Real.log N - Real.log k) t := by
  rw [suzukiUnitRieszPrimeWardWall]
  apply Finset.sum_congr rfl
  intro k hk
  rw [suzukiCauchyAnchoredWallAtom,
    suzukiCauchyWallPhaseComplex_ofReal]

/-- The regular-screw integrand is a two-depth secant at real Cauchy height. -/
theorem suzukiUnitRieszReporterWallSecant_ofReal_eq_secantAtLag
    (H h t : ℝ) :
    suzukiUnitRieszReporterWallSecant H h (t : ℂ) =
      suzukiCauchyWallSecantAtLag (H - h) t := by
  rw [suzukiUnitRieszReporterWallSecant,
    suzukiCauchyWallPhaseComplex_two_mul,
    suzukiCauchyWallPhaseComplex_ofReal,
    suzukiCauchyWallPhaseComplex_ofReal,
    suzukiCauchyWallSecantAtLag]
  congr 2 <;> ring

/-- The continuous regular side of the literal completed wall is an integral
of the same two-depth secants that enter the mixed covariance. -/
theorem suzukiUnitRieszRegularWardWall_ofReal_eq_integral_secantAtLag
    (H t : ℝ) :
    suzukiUnitRieszRegularWardWall H (t : ℂ) =
      ∫ h in _root_.RHTower.unitRieszSuzukiBase..H,
        suzukiCauchyWallSecantAtLag (H - h) t *
          (screwRegularKernel h : ℂ) := by
  rw [suzukiUnitRieszRegularWardWall]
  apply intervalIntegral.integral_congr
  intro h hh
  change suzukiUnitRieszReporterWallSecant H h (t : ℂ) *
      (screwRegularKernel h : ℂ) =
    suzukiCauchyWallSecantAtLag (H - h) t *
      (screwRegularKernel h : ℂ)
  rw [suzukiUnitRieszReporterWallSecant_ofReal_eq_secantAtLag]

/-- **Source-normal form for the literal regular wall.**  Dilation carries
the fixed positive regular-screw density to a signed density on the same
anchored atoms as the literal prime wall.  This is an exact pre-scalar
identity; it neither discards the residual regular mass nor chooses a
quadrature or a transport coefficient. -/
theorem suzukiUnitRieszRegularWardWall_ofReal_eq_anchored_dilation
    {H : ℝ} (hH : _root_.RHTower.unitRieszSuzukiBase ≤ H) (t : ℝ) :
    suzukiUnitRieszRegularWardWall H (t : ℂ) =
      (((2 : ℝ)⁻¹) •
        (∫ r in 0..(H - _root_.RHTower.unitRieszSuzukiBase) * 2,
          suzukiCauchyAnchoredWallAtom r t *
            (screwRegularKernel (H - r / 2) : ℂ))) -
        ∫ r in 0..H - _root_.RHTower.unitRieszSuzukiBase,
          suzukiCauchyAnchoredWallAtom r t *
            (screwRegularKernel (H - r) : ℂ) := by
  have hQ : 0 ≤ H - _root_.RHTower.unitRieszSuzukiBase := sub_nonneg.mpr hH
  have hKR : ContinuousOn
      (fun q : ℝ => screwRegularKernel (H - q))
      (Icc 0 (H - _root_.RHTower.unitRieszSuzukiBase)) := by
    refine continuousOn_screwRegularKernel.comp
      (continuous_const.sub continuous_id).continuousOn ?_
    intro q hq
    have hbase : _root_.RHTower.unitRieszSuzukiBase ≤ H - q := by
      linarith [hq.2]
    exact _root_.RHTower.unitRieszSuzukiBase_pos.trans_le hbase
  have hF : ContinuousOn
      (fun q : ℝ => (screwRegularKernel (H - q) : ℂ))
      (Icc 0 (H - _root_.RHTower.unitRieszSuzukiBase)) := by
    change ContinuousOn
      (Complex.ofReal ∘ fun q : ℝ => screwRegularKernel (H - q))
      (Icc 0 (H - _root_.RHTower.unitRieszSuzukiBase))
    exact Complex.continuous_ofReal.comp_continuousOn hKR
  have hmain := intervalIntegral_suzukiCauchyWallSecantAtLag_eq_anchored_dilation
    (F := fun q : ℝ => (screwRegularKernel (H - q) : ℂ)) hQ hF t
  rw [suzukiUnitRieszRegularWardWall_ofReal_eq_integral_secantAtLag]
  have hrev := intervalIntegral.integral_comp_sub_mul
    (a := (0 : ℝ)) (b := H - _root_.RHTower.unitRieszSuzukiBase)
    (c := (1 : ℝ))
    (fun h : ℝ => suzukiCauchyWallSecantAtLag (H - h) t *
      (screwRegularKernel h : ℂ)) one_ne_zero H
  have hrev' :
      (∫ q in 0..H - _root_.RHTower.unitRieszSuzukiBase,
        suzukiCauchyWallSecantAtLag q t *
          (screwRegularKernel (H - q) : ℂ)) =
      ∫ h in _root_.RHTower.unitRieszSuzukiBase..H,
        suzukiCauchyWallSecantAtLag (H - h) t *
          (screwRegularKernel h : ℂ) := by
    simpa only [one_mul, inv_one, one_smul, sub_zero, sub_sub_cancel] using hrev
  rw [← hrev']
  exact hmain

/-- At the lower Hardy readout, a unit-Riesz secant is the dilation
coboundary of the anchored scalar atom. -/
theorem unitRieszSuzukiReporter_eq_anchored_dilation
    (H h : ℝ) :
    _root_.RHTower.unitRieszSuzukiReporter H h =
      (1 - Real.exp (-(2 * (H - h)) / 2)) -
        (1 - Real.exp (-(H - h) / 2)) := by
  unfold _root_.RHTower.unitRieszSuzukiReporter
  have htwo : -(2 * (H - h)) / 2 = h - H := by ring
  have hone : -(H - h) / 2 = (h - H) / 2 := by ring
  rw [htwo, hone]
  ring

/-- The actual regular mass in Suzuki's completed lower-Hardy amplitude is
an exact signed anchored dilation measure.  This is the scalar readout of
the literal wall normal form, not a replacement reporter. -/
theorem suzukiUnitRieszRegularWardMass_eq_anchored_dilation
    {H : ℝ} (hH : _root_.RHTower.unitRieszSuzukiBase ≤ H) :
    suzukiUnitRieszRegularWardMass H =
      (1 / 2 : ℝ) *
        (∫ r in 0..(H - _root_.RHTower.unitRieszSuzukiBase) * 2,
          (1 - Real.exp (-r / 2)) * screwRegularKernel (H - r / 2)) -
      ∫ r in 0..H - _root_.RHTower.unitRieszSuzukiBase,
        (1 - Real.exp (-r / 2)) * screwRegularKernel (H - r) := by
  let Q : ℝ := H - _root_.RHTower.unitRieszSuzukiBase
  let A : ℝ → ℝ := fun r => 1 - Real.exp (-r / 2)
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    linarith
  have hK : ContinuousOn (fun q : ℝ => screwRegularKernel (H - q)) (Icc 0 Q) := by
    refine continuousOn_screwRegularKernel.comp
      (continuous_const.sub continuous_id).continuousOn ?_
    intro q hq
    have hbase : _root_.RHTower.unitRieszSuzukiBase ≤ H - q := by
      dsimp only [Q] at hq ⊢
      linarith [hq.2]
    exact _root_.RHTower.unitRieszSuzukiBase_pos.trans_le hbase
  have hA : Continuous A := by
    dsimp only [A]
    fun_prop
  have hfirst : IntervalIntegrable
      (fun q : ℝ => A (2 * q) * screwRegularKernel (H - q)) volume 0 Q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hQ]
    exact (hA.comp (continuous_const.mul continuous_id)).continuousOn.mul hK
  have hsecond : IntervalIntegrable
      (fun q : ℝ => A q * screwRegularKernel (H - q)) volume 0 Q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hQ]
    exact hA.continuousOn.mul hK
  have hscale := intervalIntegral.integral_comp_mul_right
    (a := (0 : ℝ)) (b := Q) (c := (2 : ℝ))
    (fun r : ℝ => A r * screwRegularKernel (H - r / 2)) (by norm_num)
  have hscale' :
      (∫ q in 0..Q, A (2 * q) * screwRegularKernel (H - q)) =
        (1 / 2 : ℝ) *
          ∫ r in 0..Q * 2, A r * screwRegularKernel (H - r / 2) := by
    calc
      _ = ∫ q in 0..Q,
          A (q * 2) * screwRegularKernel (H - (q * 2) / 2) := by
            apply intervalIntegral.integral_congr
            intro q _hq
            ring
      _ = _ := by
            rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
            simpa only [zero_mul, smul_eq_mul] using hscale
  have hrev := intervalIntegral.integral_comp_sub_mul
    (a := (0 : ℝ)) (b := Q) (c := (1 : ℝ))
    (fun h : ℝ =>
      (A (2 * (H - h)) - A (H - h)) * screwRegularKernel h)
    one_ne_zero H
  have hrev' :
      (∫ q in 0..Q,
        (A (2 * q) - A q) * screwRegularKernel (H - q)) =
      ∫ h in _root_.RHTower.unitRieszSuzukiBase..H,
        (A (2 * (H - h)) - A (H - h)) * screwRegularKernel h := by
    dsimp only [Q] at hrev ⊢
    simpa [smul_eq_mul] using hrev
  rw [suzukiUnitRieszRegularWardMass]
  calc
    _ = ∫ h in _root_.RHTower.unitRieszSuzukiBase..H,
        (A (2 * (H - h)) - A (H - h)) * screwRegularKernel h := by
          apply intervalIntegral.integral_congr
          intro h _hh
          change _root_.RHTower.unitRieszSuzukiReporter H h * screwRegularKernel h =
            (A (2 * (H - h)) - A (H - h)) * screwRegularKernel h
          rw [unitRieszSuzukiReporter_eq_anchored_dilation]
    _ = ∫ q in 0..Q,
        (A (2 * q) - A q) * screwRegularKernel (H - q) := hrev'.symm
    _ = ∫ q in 0..Q,
          A (2 * q) * screwRegularKernel (H - q) -
            A q * screwRegularKernel (H - q) := by
          apply intervalIntegral.integral_congr
          intro q _hq
          ring
    _ = (∫ q in 0..Q, A (2 * q) * screwRegularKernel (H - q)) -
          ∫ q in 0..Q, A q * screwRegularKernel (H - q) := by
            rw [intervalIntegral.integral_sub hfirst hsecond]
    _ = _ := by
      rw [hscale']

/-- The completed lower-Hardy amplitude, hence a literal sample of the
CCM-FU Xi-screw source, is exactly an anchored prime measure minus the
same signed dilation-transferred regular measure. -/
theorem unitRieszSuzukiGreen_logNat_eq_anchored_source
    (N : ℕ) :
    _root_.RHTower.unitRieszSuzukiGreen (Real.log ((N + 2 : ℕ) : ℝ)) =
      (∑ k ∈ Finset.Icc 2 (N + 2),
        (ArithmeticFunction.vonMangoldt k / Real.sqrt ((N + 2 : ℕ) : ℝ)) *
          (1 - Real.exp (-(Real.log ((N + 2 : ℕ) : ℝ) - Real.log k) / 2))) -
      ((1 / 2 : ℝ) *
        (∫ r in 0..(Real.log ((N + 2 : ℕ) : ℝ) - _root_.RHTower.unitRieszSuzukiBase) * 2,
          (1 - Real.exp (-r / 2)) *
            screwRegularKernel (Real.log ((N + 2 : ℕ) : ℝ) - r / 2)) -
        ∫ r in 0..(Real.log ((N + 2 : ℕ) : ℝ) - _root_.RHTower.unitRieszSuzukiBase),
          (1 - Real.exp (-r / 2)) *
            screwRegularKernel (Real.log ((N + 2 : ℕ) : ℝ) - r)) := by
  have hbase : _root_.RHTower.unitRieszSuzukiBase ≤ Real.log ((N + 2 : ℕ) : ℝ) :=
    (_root_.RHTower.unitRieszSuzukiBase_lt_log_of_two_le (by omega : 2 ≤ N + 2)).le
  rw [unitRieszSuzukiGreen_eq_primeCharge_sub_regularWardMass,
    unitRieszCoherentPrimeOutgoingCharge,
    suzukiUnitRieszRegularWardMass_eq_anchored_dilation hbase]

/-- Signed anchored density on the overlap interval in the exact dilation
normal form of the regular wall. -/
def suzukiCauchyAnchoredDilationInteriorDensity (H r : ℝ) : ℝ :=
  screwRegularKernel (H - r / 2) / 2 - screwRegularKernel (H - r)

/-- The dilation-transferred regular density is strictly negative at the
newest anchor.  Thus the literal completed wall has no pointwise
prime--regular cancellation there; any use of the anchored normal form must
control genuinely nonlocal Cauchy interactions. -/
theorem suzukiCauchyAnchoredDilationInteriorDensity_zero_neg
    {H : ℝ} (hH : _root_.RHTower.unitRieszSuzukiBase ≤ H) :
    suzukiCauchyAnchoredDilationInteriorDensity H 0 < 0 := by
  rw [suzukiCauchyAnchoredDilationInteriorDensity]
  simp only [zero_div, sub_zero]
  have hkernel : 0 < screwRegularKernel H :=
    screwRegularKernel_pos_of_unitRieszSuzukiBase_le hH
  nlinarith

/-- Decaying Lerch contribution removed from the growing exponential in the
literal regular screw kernel. -/
def suzukiCauchyRegularTail (t : ℝ) : ℝ :=
  Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t)))

theorem suzukiCauchyRegularTail_pos {t : ℝ} (ht : 0 < t) :
    0 < suzukiCauchyRegularTail t := by
  unfold suzukiCauchyRegularTail
  exact div_pos (Real.exp_pos _) (one_sub_exp_neg_two_mul_pos ht)

/-- The removed Lerch tail decreases along the positive screw ray. -/
theorem suzukiCauchyRegularTail_antitone {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    suzukiCauchyRegularTail t ≤ suzukiCauchyRegularTail s := by
  have ht : 0 < t := hs.trans_le hst
  have hnum : Real.exp (-(5 * t / 2)) ≤ Real.exp (-(5 * s / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hden : 1 - Real.exp (-(2 * s)) ≤ 1 - Real.exp (-(2 * t)) := by
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    nlinarith
  exact div_le_div₀ (Real.exp_nonneg _) hnum
    (one_sub_exp_neg_two_mul_pos hs) hden

/-- Exact separation of the transferred interior density into a growing
dilation term and a positive-ray Lerch-tail difference. -/
theorem suzukiCauchyAnchoredDilationInteriorDensity_eq_leading_add_tail
    (H r : ℝ) :
    suzukiCauchyAnchoredDilationInteriorDensity H r =
      Real.exp ((H - r) / 2) * (Real.exp (r / 4) / 2 - 1) +
        (suzukiCauchyRegularTail (H - r) -
          suzukiCauchyRegularTail (H - r / 2) / 2) := by
  have hexp : Real.exp ((H - r / 2) / 2) =
      Real.exp ((H - r) / 2) * Real.exp (r / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [suzukiCauchyAnchoredDilationInteriorDensity, screwRegularKernel,
    suzukiCauchyRegularTail]
  rw [hexp]
  ring

/-- The transferred interior density is nonnegative beyond the fixed
four-log-two lag.  Thus its potentially adverse support has bounded width,
independent of the aperture. -/
theorem suzukiCauchyAnchoredDilationInteriorDensity_nonneg_of_four_log_two_le
    {H r : ℝ} (hr0 : 0 ≤ r)
    (hrH : r ≤ H - _root_.RHTower.unitRieszSuzukiBase)
    (hfour : 4 * Real.log 2 ≤ r) :
    0 ≤ suzukiCauchyAnchoredDilationInteriorDensity H r := by
  have hs : 0 < H - r := by
    have hbase : _root_.RHTower.unitRieszSuzukiBase ≤ H - r := by
      linarith
    exact _root_.RHTower.unitRieszSuzukiBase_pos.trans_le hbase
  have hst : H - r ≤ H - r / 2 := by linarith
  have htail : suzukiCauchyRegularTail (H - r / 2) / 2 ≤
      suzukiCauchyRegularTail (H - r) := by
    have hmono := suzukiCauchyRegularTail_antitone hs hst
    have htailpos : 0 ≤ suzukiCauchyRegularTail (H - r / 2) :=
      (suzukiCauchyRegularTail_pos (hs.trans_le hst)).le
    nlinarith
  have hlog : Real.log 2 ≤ r / 4 := by linarith
  have hexp : (2 : ℝ) ≤ Real.exp (r / 4) := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (r / 4) := Real.exp_le_exp.mpr hlog
  rw [suzukiCauchyAnchoredDilationInteriorDensity_eq_leading_add_tail]
  have hlead : 0 ≤ Real.exp ((H - r) / 2) *
      (Real.exp (r / 4) / 2 - 1) := by
    apply mul_nonneg (Real.exp_nonneg _)
    linarith
  linarith

/-- Any negative interior density lies below the fixed four-log-two lag. -/
theorem suzukiCauchyAnchoredDilationInteriorDensity_neg_lt_four_log_two
    {H r : ℝ} (hr0 : 0 ≤ r)
    (hrH : r ≤ H - _root_.RHTower.unitRieszSuzukiBase)
    (hneg : suzukiCauchyAnchoredDilationInteriorDensity H r < 0) :
    r < 4 * Real.log 2 := by
  by_contra h
  have hfour : 4 * Real.log 2 ≤ r := le_of_not_gt h
  have hnonneg := suzukiCauchyAnchoredDilationInteriorDensity_nonneg_of_four_log_two_le
    hr0 hrH hfour
  linarith

/-- Cauchy Gram of two literal anchored wall atoms. -/
def suzukiCauchyAnchoredAtomGram (p r : ℝ) : ℝ :=
  1 - Real.exp (-|p| / 2) - Real.exp (-|r| / 2) +
    Real.exp (-|p - r| / 2)

/-- The real anchored Gram is exactly the Cauchy phase Gram of two literal
anchored source atoms. -/
theorem suzukiCauchyAnchoredWallGram_eq_atomGram
    (p r : ℝ) :
    suzukiCauchyAnchoredWallGram 0 (-p) (-r) =
      (suzukiCauchyAnchoredAtomGram p r : ℂ) := by
  rw [suzukiCauchyAnchoredWallGram,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq]
  have hr : |0 - -r| = |r| := by ring
  have hp : |-p - 0| = |p| := by
    rw [show -p - 0 = -p by ring, abs_neg]
  have hpr : |-p - -r| = |p - r| := by
    rw [show -p - -r = -(p - r) by ring, abs_neg]
  rw [hr, hp, hpr]
  norm_num
  simp only [suzukiCauchyAnchoredAtomGram]
  push_cast
  ring

/-- On ordered nonnegative lags, the literal anchored Gram has an explicit
positive factorization. -/
theorem suzukiCauchyAnchoredAtomGram_eq_factor_of_nonneg_le
    {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) :
    suzukiCauchyAnchoredAtomGram p r =
      (1 - Real.exp (-p / 2)) *
        (1 + Real.exp (-(r - p) / 2)) := by
  have hsub : p - r ≤ 0 := by linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hsplit : Real.exp (-r / 2) =
      Real.exp (-p / 2) * Real.exp (-(r - p) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [suzukiCauchyAnchoredAtomGram, abs_of_nonneg hp, abs_of_nonneg hr,
    abs_of_nonpos hsub, hsplit]
  ring

theorem suzukiCauchyAnchoredAtomGram_nonneg_of_nonneg_le
    {p r : ℝ} (hp : 0 ≤ p) (hpr : p ≤ r) :
    0 ≤ suzukiCauchyAnchoredAtomGram p r := by
  rw [suzukiCauchyAnchoredAtomGram_eq_factor_of_nonneg_le hp hpr]
  apply mul_nonneg
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  · positivity

/-- Every literal prime lag lies strictly below the outer tail of the
dilation-transferred regular wall. -/
theorem suzukiCauchyAnchoredPrimeLag_lt_dilationTailLower
    {H : ℝ} {k : ℕ} (hk : 2 ≤ k) :
    H - Real.log k < H - _root_.RHTower.unitRieszSuzukiBase := by
  linarith [_root_.RHTower.unitRieszSuzukiBase_lt_log_of_two_le hk]

/-- The completed prime-minus-regular cross term is favourable for every
nonnegative prime lag against every nonnegative anchored tail lag beyond its
interior cutoff.  Thus the outer dilation tail is not the arithmetic
obstruction; only the signed interior density can carry it. -/
theorem suzukiCompletedAnchoredTailCross_nonpos
    {c d p r Q : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hp : 0 ≤ p) (hpQ : p ≤ Q) (hQr : Q ≤ r) :
    -(c * suzukiCauchyAnchoredAtomGram p r * d) ≤ 0 := by
  have hgram : 0 ≤ suzukiCauchyAnchoredAtomGram p r :=
    suzukiCauchyAnchoredAtomGram_nonneg_of_nonneg_le hp (hpQ.trans hQr)
  nlinarith [mul_nonneg (mul_nonneg hc hgram) hd]

theorem suzukiCauchyAnchoredAtomGram_symm (p r : ℝ) :
    suzukiCauchyAnchoredAtomGram p r = suzukiCauchyAnchoredAtomGram r p := by
  unfold suzukiCauchyAnchoredAtomGram
  rw [abs_sub_comm r p]
  ring

theorem suzukiCauchyAnchoredAtomGram_nonneg_of_nonneg
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    0 ≤ suzukiCauchyAnchoredAtomGram p r := by
  rcases le_total p r with hpr | hrp
  · exact suzukiCauchyAnchoredAtomGram_nonneg_of_nonneg_le hp hpr
  · rw [suzukiCauchyAnchoredAtomGram_symm]
    exact suzukiCauchyAnchoredAtomGram_nonneg_of_nonneg_le hr hrp

/-- Every positive portion of the transferred interior density above the
fixed four-log-two lag has favourable completed cross sign against every
nonnegative literal prime atom. -/
theorem suzukiCompletedAnchoredPositiveInteriorCross_nonpos
    {c p r H : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) (hr0 : 0 ≤ r)
    (hrH : r ≤ H - _root_.RHTower.unitRieszSuzukiBase)
    (hfour : 4 * Real.log 2 ≤ r) :
    -(c * suzukiCauchyAnchoredAtomGram p r *
      suzukiCauchyAnchoredDilationInteriorDensity H r) ≤ 0 := by
  have hgram : 0 ≤ suzukiCauchyAnchoredAtomGram p r :=
    suzukiCauchyAnchoredAtomGram_nonneg_of_nonneg hp hr0
  have hdensity : 0 ≤ suzukiCauchyAnchoredDilationInteriorDensity H r :=
    suzukiCauchyAnchoredDilationInteriorDensity_nonneg_of_four_log_two_le
      hr0 hrH hfour
  nlinarith [mul_nonneg (mul_nonneg hc hgram) hdensity]

/-- Cauchy averaging of literal prime and regular wall shapes is the mixed
kernel, rather than the reporter's secant--secant kernel. -/
theorem suzukiCauchyAnchoredSecantWallGram_eq
    (p q : ℝ) :
    suzukiCauchyAnchoredSecantWallGram p q =
      (suzukiCauchyAnchoredSecantGram p q : ℂ) := by
  rw [suzukiCauchyAnchoredSecantWallGram,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq]
  have hq : |0 - -q| = |q| := by ring
  have htwoq : |0 - -2 * q| = |2 * q| := by ring
  have hpq : |-p - -q| = |p - q| := by
    rw [show -p - -q = -(p - q) by ring, abs_neg]
  have hptwoq : |-p - -2 * q| = |p - 2 * q| := by
    rw [show -p - -2 * q = -(p - 2 * q) by ring, abs_neg]
  rw [hq, htwoq, hpq, hptwoq]
  simp only [suzukiCauchyAnchoredSecantGram]
  push_cast
  ring

/-- On the source-faithful lower wedge `2q ≤ p`, the mixed covariance is
nonnegative.  Thus the completed prime-minus-regular cross term has the
favourable sign there. -/
theorem suzukiCauchyAnchoredSecantGram_nonneg_of_two_mul_le
    {p q : ℝ} (hq : 0 ≤ q) (hpq : 2 * q ≤ p) :
    0 ≤ suzukiCauchyAnchoredSecantGram p q := by
  have hpq' : q ≤ p := by linarith
  have hp_sub_q : 0 ≤ p - q := sub_nonneg.mpr hpq'
  have hp_sub_twoq : 0 ≤ p - 2 * q := sub_nonneg.mpr hpq
  have htwoq : 0 ≤ 2 * q := by linarith
  have hfirst : 0 ≤ Real.exp (-q / 2) - Real.exp (-q) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith
  have hsecond : 0 ≤
      Real.exp (-(p - 2 * q) / 2) - Real.exp (-(p - q) / 2) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith
  rw [suzukiCauchyAnchoredSecantGram,
    abs_of_nonneg hq,
    abs_of_nonneg htwoq,
    abs_of_nonneg hp_sub_q,
    abs_of_nonneg hp_sub_twoq]
  have htwo : Real.exp (-(2 * q) / 2) = Real.exp (-q) := by
    congr 1
    ring
  rw [htwo]
  linarith

/-- On the opposite cone `p ≤ q`, the literal mixed covariance has an exact
factorization.  This is the obstruction side of the source geometry: deeper
regular lags cannot furnish a favourable completed cross term for an earlier
prime atom. -/
theorem suzukiCauchyAnchoredSecantGram_eq_factor_of_le
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    suzukiCauchyAnchoredSecantGram p q =
      (1 - Real.exp (-q / 2)) *
        (Real.exp (-q / 2) - Real.exp (-(q - p) / 2)) := by
  have hq : 0 ≤ q := hp.trans hpq
  have htwoq : 0 ≤ 2 * q := by linarith
  have hp_sub_q : p - q ≤ 0 := by linarith
  have hp_sub_twoq : p - 2 * q ≤ 0 := by linarith
  have htwo : Real.exp (-(2 * q) / 2) = Real.exp (-q) := by
    congr 1
    ring
  have hsq : Real.exp (-q) = Real.exp (-q / 2) * Real.exp (-q / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hthird : -(-(p - q)) / 2 = -(q - p) / 2 := by ring
  have hfourth : -(-(p - 2 * q)) / 2 = -(2 * q - p) / 2 := by ring
  have hsplit : Real.exp (-(2 * q - p) / 2) =
      Real.exp (-(q - p) / 2) * Real.exp (-q / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [suzukiCauchyAnchoredSecantGram,
    abs_of_nonneg hq,
    abs_of_nonneg htwoq,
    abs_of_nonpos hp_sub_q,
    abs_of_nonpos hp_sub_twoq,
    htwo, hthird, hfourth, hsplit, hsq]
  ring

/-- Every nonzero earlier prime lag sees an adverse mixed cross contribution
from every regular lag at least as deep. -/
theorem suzukiCauchyAnchoredSecantGram_neg_of_pos_le
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    suzukiCauchyAnchoredSecantGram p q < 0 := by
  rw [suzukiCauchyAnchoredSecantGram_eq_factor_of_le hp.le hpq]
  have hq : 0 < q := hp.trans_le hpq
  have hone : 0 < 1 - Real.exp (-q / 2) := by
    apply sub_pos.mpr
    have : Real.exp (-q / 2) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by linarith)
    simpa using this
  have hsecond : Real.exp (-q / 2) - Real.exp (-(q - p) / 2) < 0 := by
    apply sub_neg.mpr
    apply Real.exp_lt_exp.mpr
    linarith
  exact mul_neg_of_pos_of_neg hone hsecond

/-- Transition polynomial for the literal anchored--secant covariance.  The
coordinate is `q = p / 2 + r`; unlike the reporter-secant polynomial, its
prime factor is anchored at depth zero. -/
def suzukiCauchyAnchoredSecantTransitionPolynomial (p r : ℝ) : ℝ :=
  (1 - Real.exp (-p / 2)) * Real.exp (-3 * r / 2) +
    Real.exp (-p / 4) * (Real.exp (-r) - 1)

/-- Exact transition factorization for the literal mixed covariance. -/
theorem suzukiCauchyAnchoredSecant_transition_factorization
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hrp : r ≤ p / 2) :
    Real.exp (-r / 2) *
        suzukiCauchyAnchoredSecantGram p (p / 2 + r) =
      suzukiCauchyAnchoredSecantTransitionPolynomial p r := by
  have hq : 0 ≤ p / 2 + r := by linarith
  have htwoq : 0 ≤ 2 * (p / 2 + r) := by linarith
  have hmid : 0 ≤ p - (p / 2 + r) := by linarith
  have hlast : p - 2 * (p / 2 + r) ≤ 0 := by linarith
  have e1 : Real.exp (-(p / 2 + r) / 2) =
      Real.exp (-p / 4) * Real.exp (-r / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(2 * (p / 2 + r)) / 2) =
      Real.exp (-p / 2) * Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (-(p - (p / 2 + r)) / 2) =
      Real.exp (-p / 4) * Real.exp (r / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e4 : Real.exp (-(-(p - 2 * (p / 2 + r))) / 2) =
      Real.exp (-r) := by
    congr 1
    ring
  have ehalf_sq : Real.exp (-r / 2) * Real.exp (-r / 2) = Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ehalf_cancel : Real.exp (-r / 2) * Real.exp (r / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show -r / 2 + r / 2 = 0 by ring, Real.exp_zero]
  have ethree : Real.exp (-r / 2) * Real.exp (-r) = Real.exp (-3 * r / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [suzukiCauchyAnchoredSecantGram,
    abs_of_nonneg hq,
    abs_of_nonneg htwoq,
    abs_of_nonneg hmid,
    abs_of_nonpos hlast,
    e1, e2, e3, e4,
    suzukiCauchyAnchoredSecantTransitionPolynomial]
  calc
    Real.exp (-r / 2) *
        (Real.exp (-p / 4) * Real.exp (-r / 2) -
          Real.exp (-p / 2) * Real.exp (-r) -
          Real.exp (-p / 4) * Real.exp (r / 2) + Real.exp (-r)) =
      Real.exp (-p / 4) * (Real.exp (-r / 2) * Real.exp (-r / 2)) -
        Real.exp (-p / 2) * (Real.exp (-r / 2) * Real.exp (-r)) -
        Real.exp (-p / 4) * (Real.exp (-r / 2) * Real.exp (r / 2)) +
          Real.exp (-r / 2) * Real.exp (-r) := by ring
    _ = Real.exp (-p / 4) * Real.exp (-r) -
        Real.exp (-p / 2) * Real.exp (-3 * r / 2) -
        Real.exp (-p / 4) * 1 + Real.exp (-3 * r / 2) := by
          rw [ehalf_sq, ehalf_cancel, ethree]
    _ = _ := by ring

theorem continuous_suzukiCauchyAnchoredSecantTransitionPolynomial
    (p : ℝ) :
    Continuous (suzukiCauchyAnchoredSecantTransitionPolynomial p) := by
  unfold suzukiCauchyAnchoredSecantTransitionPolynomial
  fun_prop

/-- The literal mixed transition polynomial is strictly decreasing at every
positive prime lag. -/
theorem strictAnti_suzukiCauchyAnchoredSecantTransitionPolynomial
    {p : ℝ} (hp : 0 < p) :
    StrictAnti (suzukiCauchyAnchoredSecantTransitionPolynomial p) := by
  intro a b hab
  have hcoef : 0 < 1 - Real.exp (-p / 2) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hfirst : Real.exp (-3 * b / 2) < Real.exp (-3 * a / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hsecond : Real.exp (-b) < Real.exp (-a) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hfirst' :
      (1 - Real.exp (-p / 2)) * Real.exp (-3 * b / 2) <
        (1 - Real.exp (-p / 2)) * Real.exp (-3 * a / 2) :=
    mul_lt_mul_of_pos_left hfirst hcoef
  have hsecond' :
      Real.exp (-p / 4) * (Real.exp (-b) - 1) <
        Real.exp (-p / 4) * (Real.exp (-a) - 1) := by
    apply mul_lt_mul_of_pos_left
    · linarith
    · exact Real.exp_pos _
  unfold suzukiCauchyAnchoredSecantTransitionPolynomial
  linarith

theorem suzukiCauchyAnchoredSecantTransitionPolynomial_zero
    (p : ℝ) :
    suzukiCauchyAnchoredSecantTransitionPolynomial p 0 =
      1 - Real.exp (-p / 2) := by
  rw [suzukiCauchyAnchoredSecantTransitionPolynomial]
  norm_num

/-- The literal midpoint lag is strictly favourable for every positive prime
lag.  This is an interior source coordinate, not an endpoint artefact. -/
theorem suzukiCauchyAnchoredSecantGram_half_pos
    {p : ℝ} (hp : 0 < p) :
    0 < suzukiCauchyAnchoredSecantGram p (p / 2) := by
  have hfactor := suzukiCauchyAnchoredSecant_transition_factorization
    (p := p) (r := 0) hp.le (by norm_num) (by linarith)
  norm_num at hfactor
  rw [hfactor, suzukiCauchyAnchoredSecantTransitionPolynomial_zero]
  apply sub_pos.mpr
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- Every genuine finite-prime atom has a strictly favourable regular-screw
midpoint inside the literal unit-Riesz aperture.  Thus the favourable mixed
cone is physically present in the actual completed source; constructing a
uniform mass coupling inside it remains the quantitative problem. -/
theorem exists_suzukiUnitRieszActualPrimeRegularFavourableMidpoint
    {N k : ℕ} (hk2 : 2 ≤ k) (hkN : k < N) :
    ∃ h ∈ Set.Ioo _root_.RHTower.unitRieszSuzukiBase (Real.log N),
      0 < suzukiCauchyAnchoredSecantGram
        (Real.log N - Real.log k) (Real.log N - h) := by
  have hkpos : 0 < (k : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_trans (by omega : 0 < k) hkN)
  have hkNreal : (k : ℝ) < N := by exact_mod_cast hkN
  have hlog : Real.log (k : ℝ) < Real.log N :=
    Real.strictMonoOn_log hkpos hNpos hkNreal
  have hp : 0 < Real.log N - Real.log k := by linarith
  refine ⟨(Real.log N + Real.log k) / 2, ?_, ?_⟩
  · constructor
    · have hbase : _root_.RHTower.unitRieszSuzukiBase < Real.log k :=
        _root_.RHTower.unitRieszSuzukiBase_lt_log_of_two_le hk2
      linarith
    · linarith
  · have hlag : Real.log N - (Real.log N + Real.log k) / 2 =
        (Real.log N - Real.log k) / 2 := by ring
    rw [hlag]
    exact suzukiCauchyAnchoredSecantGram_half_pos hp

theorem suzukiCauchyAnchoredSecantTransitionPolynomial_half_neg
    {p : ℝ} (hp : 0 < p) :
    suzukiCauchyAnchoredSecantTransitionPolynomial p (p / 2) < 0 := by
  have hfactor := suzukiCauchyAnchoredSecant_transition_factorization
    (p := p) (r := p / 2) hp.le (by linarith) (by linarith)
  have hfactor' :
      Real.exp (-(p / 2) / 2) * suzukiCauchyAnchoredSecantGram p p =
        suzukiCauchyAnchoredSecantTransitionPolynomial p (p / 2) := by
    convert hfactor using 1; ring
  rw [← hfactor']
  exact mul_neg_of_pos_of_neg (Real.exp_pos _)
    (suzukiCauchyAnchoredSecantGram_neg_of_pos_le hp le_rfl)

/-- Every positive anchored prime lag has one and only one regular lag in the
literal transition band where its mixed Cauchy covariance vanishes. -/
theorem existsUnique_suzukiCauchyAnchoredSecantTransitionResidual
    (p : {p : ℝ // 0 < p}) :
    ∃! r : ℝ, r ∈ Set.Ioo 0 (p.1 / 2) ∧
      suzukiCauchyAnchoredSecantTransitionPolynomial p.1 r = 0 := by
  have hleft : 0 < suzukiCauchyAnchoredSecantTransitionPolynomial p.1 0 := by
    rw [suzukiCauchyAnchoredSecantTransitionPolynomial_zero]
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith [p.2])
  have hright : suzukiCauchyAnchoredSecantTransitionPolynomial p.1 (p.1 / 2) < 0 :=
    suzukiCauchyAnchoredSecantTransitionPolynomial_half_neg p.2
  have hcont : ContinuousOn (suzukiCauchyAnchoredSecantTransitionPolynomial p.1)
      (Set.Icc 0 (p.1 / 2)) :=
    (continuous_suzukiCauchyAnchoredSecantTransitionPolynomial p.1).continuousOn
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Ioo'
    (show (0 : ℝ) ≤ p.1 / 2 by linarith [p.2]) hcont ⟨hright, hleft⟩
  refine ⟨r, ⟨hr, hzero⟩, fun s hs => ?_⟩
  exact (strictAnti_suzukiCauchyAnchoredSecantTransitionPolynomial p.2).injective
    (hs.2.trans hzero.symm)

/-- Canonical regular-lag residual which nulls the literal anchored--secant
covariance of one positive prime lag. -/
def suzukiCauchyAnchoredSecantTransitionResidual
    (p : {p : ℝ // 0 < p}) : ℝ :=
  Classical.choose (existsUnique_suzukiCauchyAnchoredSecantTransitionResidual p)

theorem suzukiCauchyAnchoredSecantTransitionResidual_mem
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantTransitionResidual p ∈ Set.Ioo 0 (p.1 / 2) :=
  (Classical.choose_spec (existsUnique_suzukiCauchyAnchoredSecantTransitionResidual p)).1.1

theorem suzukiCauchyAnchoredSecantTransitionResidual_eq_zero
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantTransitionPolynomial p.1
      (suzukiCauchyAnchoredSecantTransitionResidual p) = 0 :=
  (Classical.choose_spec (existsUnique_suzukiCauchyAnchoredSecantTransitionResidual p)).1.2

/-- Canonical regular lag at which one positive prime atom has zero literal
mixed covariance. -/
def suzukiCauchyAnchoredSecantTransitionLag
    (p : {p : ℝ // 0 < p}) : ℝ :=
  p.1 / 2 + suzukiCauchyAnchoredSecantTransitionResidual p

theorem suzukiCauchyAnchoredSecantTransitionLag_mem
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantTransitionLag p ∈ Set.Ioo (p.1 / 2) p.1 := by
  have hr := suzukiCauchyAnchoredSecantTransitionResidual_mem p
  constructor
  · dsimp [suzukiCauchyAnchoredSecantTransitionLag]
    linarith [hr.1]
  · dsimp [suzukiCauchyAnchoredSecantTransitionLag]
    linarith [hr.2]

theorem suzukiCauchyAnchoredSecantGram_transitionLag_eq_zero
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantGram p.1
      (suzukiCauchyAnchoredSecantTransitionLag p) = 0 := by
  let r := suzukiCauchyAnchoredSecantTransitionResidual p
  have hr := suzukiCauchyAnchoredSecantTransitionResidual_mem p
  have hfactor := suzukiCauchyAnchoredSecant_transition_factorization
    (p := p.1) (r := r) p.2.le hr.1.le hr.2.le
  have hroot := suzukiCauchyAnchoredSecantTransitionResidual_eq_zero p
  change Real.exp (-r / 2) *
      suzukiCauchyAnchoredSecantGram p.1 (p.1 / 2 + r) =
    suzukiCauchyAnchoredSecantTransitionPolynomial p.1 r at hfactor
  rw [hroot] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left (Real.exp_ne_zero _)

/-- The literal transition lag is the complete sign boundary: every regular
lag at or beyond it has nonpositive anchored--secant covariance. -/
theorem suzukiCauchyAnchoredSecantGram_nonpos_of_transitionLag_le
    (p : {p : ℝ // 0 < p}) {q : ℝ}
    (hq : suzukiCauchyAnchoredSecantTransitionLag p ≤ q) :
    suzukiCauchyAnchoredSecantGram p.1 q ≤ 0 := by
  by_cases hqp : q ≤ p.1
  · let r : ℝ := q - p.1 / 2
    have hrmem := suzukiCauchyAnchoredSecantTransitionResidual_mem p
    have hrlower : suzukiCauchyAnchoredSecantTransitionResidual p ≤ r := by
      dsimp only [suzukiCauchyAnchoredSecantTransitionLag] at hq
      dsimp only [r]
      linarith
    have hrnonneg : 0 ≤ r := by linarith [hrmem.1]
    have hrupper : r ≤ p.1 / 2 := by
      dsimp [r]
      linarith
    have hfactor := suzukiCauchyAnchoredSecant_transition_factorization
      (p := p.1) (r := r) p.2.le hrnonneg hrupper
    have hsum : p.1 / 2 + r = q := by
      dsimp only [r]
      ring
    have hfactor' : Real.exp (-r / 2) *
        suzukiCauchyAnchoredSecantGram p.1 q =
      suzukiCauchyAnchoredSecantTransitionPolynomial p.1 r := by
      rw [← hsum]
      exact hfactor
    have hpoly : suzukiCauchyAnchoredSecantTransitionPolynomial p.1 r ≤ 0 := by
      have hanti :=
        (strictAnti_suzukiCauchyAnchoredSecantTransitionPolynomial p.2).antitone hrlower
      rw [suzukiCauchyAnchoredSecantTransitionResidual_eq_zero p] at hanti
      exact hanti
    by_contra hnot
    have hmixed : 0 < suzukiCauchyAnchoredSecantGram p.1 q :=
      lt_of_not_ge hnot
    have hpositive : 0 < Real.exp (-r / 2) *
        suzukiCauchyAnchoredSecantGram p.1 q :=
      mul_pos (Real.exp_pos _) hmixed
    rw [hfactor'] at hpositive
    exact (not_lt_of_ge hpoly) hpositive
  · exact (suzukiCauchyAnchoredSecantGram_neg_of_pos_le p.2
      (le_of_not_ge hqp)).le

/-- Signed prime-minus-regular mixed cross contribution. -/
def suzukiGammaCompletedWallSignedMixedCross
    (c d p q : ℝ) : ℝ :=
  -(c * suzukiCauchyAnchoredSecantGram p q * d)

/-- The literal completed mixed cross contribution is nonpositive on the
lower wedge when both source masses are positive. -/
theorem suzukiGammaCompletedWallSignedMixedCross_nonpos_of_two_mul_le
    {c d p q : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hq : 0 ≤ q) (hpq : 2 * q ≤ p) :
    suzukiGammaCompletedWallSignedMixedCross c d p q ≤ 0 := by
  rw [suzukiGammaCompletedWallSignedMixedCross]
  have hkernel : 0 ≤ suzukiCauchyAnchoredSecantGram p q :=
    suzukiCauchyAnchoredSecantGram_nonneg_of_two_mul_le hq hpq
  nlinarith [mul_nonneg (mul_nonneg hc hkernel) hd]

/-- The opposite cone is strictly adverse for strictly positive literal source
masses: subtracting the regular wall increases the mixed Cauchy energy. -/
theorem suzukiGammaCompletedWallSignedMixedCross_pos_of_pos_le
    {c d p q : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hp : 0 < p) (hpq : p ≤ q) :
    0 < suzukiGammaCompletedWallSignedMixedCross c d p q := by
  rw [suzukiGammaCompletedWallSignedMixedCross]
  apply neg_pos.mpr
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hc
      (suzukiCauchyAnchoredSecantGram_neg_of_pos_le hp hpq)) hd

/-- **Deep-reservoir no-go.**  For one positive literal prime lag `p`, every
part of the actual positive regular-screw measure lying at least `p` below
the aperture endpoint has adverse completed mixed sign.  Thus no nonlocal
producer can obtain cancellation from the whole deep regular reservoir; its
effective support must enter the transition band above `H - p`. -/
theorem intervalIntegral_suzukiGammaCompletedWallSignedMixedCross_nonneg_deepRegular
    {c p H : ℝ} (hc : 0 ≤ c) (hp : 0 < p)
    (hbase : _root_.RHTower.unitRieszSuzukiBase ≤ H - p) :
    0 ≤ ∫ h in _root_.RHTower.unitRieszSuzukiBase..(H - p),
      suzukiGammaCompletedWallSignedMixedCross c (screwRegularKernel h)
        p (H - h) := by
  apply intervalIntegral.integral_nonneg hbase
  intro h hh
  rw [suzukiGammaCompletedWallSignedMixedCross]
  have hkernel : 0 ≤ screwRegularKernel h :=
    (screwRegularKernel_pos_of_unitRieszSuzukiBase_le hh.1).le
  have hlag : p ≤ H - h := by linarith [hh.2]
  have hmixed : suzukiCauchyAnchoredSecantGram p (H - h) ≤ 0 :=
    (suzukiCauchyAnchoredSecantGram_neg_of_pos_le hp hlag).le
  have hproduct : c * suzukiCauchyAnchoredSecantGram p (H - h) *
      screwRegularKernel h ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hc hmixed) hkernel
  exact neg_nonneg.mpr hproduct

/-- **Sharp continuum support law.**  The adverse part of the actual
regular-screw measure begins at the exact literal transition lag, not merely
at the coarse depth `p`. -/
theorem intervalIntegral_suzukiGammaCompletedWallSignedMixedCross_nonneg_below_transition
    (p : {p : ℝ // 0 < p}) {c H : ℝ} (hc : 0 ≤ c)
    (hbase : _root_.RHTower.unitRieszSuzukiBase ≤
      H - suzukiCauchyAnchoredSecantTransitionLag p) :
    0 ≤ ∫ h in _root_.RHTower.unitRieszSuzukiBase..
      (H - suzukiCauchyAnchoredSecantTransitionLag p),
      suzukiGammaCompletedWallSignedMixedCross c (screwRegularKernel h)
        p.1 (H - h) := by
  apply intervalIntegral.integral_nonneg hbase
  intro h hh
  rw [suzukiGammaCompletedWallSignedMixedCross]
  have hkernel : 0 ≤ screwRegularKernel h :=
    (screwRegularKernel_pos_of_unitRieszSuzukiBase_le hh.1).le
  have hlag : suzukiCauchyAnchoredSecantTransitionLag p ≤ H - h := by
    linarith [hh.2]
  have hmixed : suzukiCauchyAnchoredSecantGram p.1 (H - h) ≤ 0 :=
    suzukiCauchyAnchoredSecantGram_nonpos_of_transitionLag_le p hlag
  have hproduct : c * suzukiCauchyAnchoredSecantGram p.1 (H - h) *
      screwRegularKernel h ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hc hmixed) hkernel
  exact neg_nonneg.mpr hproduct

end

end GaloisForLFunctions.RHTower
