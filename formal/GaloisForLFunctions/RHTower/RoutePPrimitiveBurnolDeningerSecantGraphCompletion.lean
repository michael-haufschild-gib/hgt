import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerSquaredCauchyGraphIncidence
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPrimeGammaHilbert
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeGammaEulerSectorObstruction
import GaloisForLFunctions.RHTower.XiWeilCauchyLpContinuity
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Route P primitive Burnol / Deninger secant graph completion

P-G200 identifies every primitive Burnol graph reporter with a coefficient-weighted negative
square of one upper-sector Deninger Cauchy evaluation.  A square is not an algebraic source atom.
This file constructs it as a genuine source-selected graph completion.

Move the upper source pole by the real step `1/(n+1)`.  The divided difference of the original
and moved Cauchy atoms is exactly their product.  These explicit two-atom upper prime--Gamma
packets converge in the multiplicity-exact Xi `ell^(2 : ℕ)` carrier to the squared Cauchy column.  The
primitive specialization retains the exact resolved von Mangoldt amplitude and reports the
P-G200 Burnol integral at every strict-right zero.  Meanwhile each nonzero raw packet coefficient
has norm `||A||(n+1)` and diverges.  Thus the landing exists precisely as an unbounded graph
completion, not as a bounded algebraic packet operation.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Canonical source-side coalescence step. -/
def routePDeningerUpperSecantStep (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

theorem routePDeningerUpperSecantStep_pos (n : ℕ) :
    0 < routePDeningerUpperSecantStep n := by
  unfold routePDeningerUpperSecantStep
  positivity

theorem tendsto_routePDeningerUpperSecantStep_zero :
    Tendsto routePDeningerUpperSecantStep atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Real tangential displacement of an upper absolute-Euler point. -/
def routePDeningerUpperSecantPoint
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    DeningerPrimeGammaUpperPoint :=
  ⟨(w : ℂ) + (routePDeningerUpperSecantStep n : ℂ), by
    simpa [routePDeningerUpperSecantStep, Complex.mul_re] using w.property⟩

@[simp]
theorem routePDeningerUpperSecantPoint_coe
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    (routePDeningerUpperSecantPoint w n : ℂ) =
      (w : ℂ) + (routePDeningerUpperSecantStep n : ℂ) := rfl

theorem routePDeningerUpperSecantPoint_ne
    (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    routePDeningerUpperSecantPoint w n ≠ w := by
  intro h
  have hre := congrArg (fun u : DeningerPrimeGammaUpperPoint => (u : ℂ).re) h
  simp only [routePDeningerUpperSecantPoint_coe, Complex.add_re,
    Complex.ofReal_re] at hre
  linarith [routePDeningerUpperSecantStep_pos n]

theorem tendsto_routePDeningerUpperSecantPoint_coe
    (w : DeningerPrimeGammaUpperPoint) :
    Tendsto (fun n => (routePDeningerUpperSecantPoint w n : ℂ))
      atTop (nhds (w : ℂ)) := by
  have hstep : Tendsto
      (fun n => (routePDeningerUpperSecantStep n : ℂ)) atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      tendsto_routePDeningerUpperSecantStep_zero
  simpa using tendsto_const_nhds.add hstep

/-- A two-atom upper source packet whose Cauchy realization is a product of two resolvents. -/
def routePDeningerUpperSecantPacket
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    DeningerPrimeGammaUpperPacket :=
  let u := routePDeningerUpperSecantPoint w n
  let c := ((w : ℂ) - (u : ℂ))⁻¹
  Finsupp.single w ((starRingEnd ℂ) (A * c)) +
    Finsupp.single u ((starRingEnd ℂ) (-A * c))

theorem deningerPrimeGammaUpperCauchyTest_add
    (x y : DeningerPrimeGammaUpperPacket) (a : ℂ) :
    deningerPrimeGammaUpperCauchyTest (x + y) a =
      deningerPrimeGammaUpperCauchyTest x a +
        deningerPrimeGammaUpperCauchyTest y a := by
  unfold deningerPrimeGammaUpperCauchyTest
    deningerPrimeGammaUpperSharpCauchyTest xiWeilSharp
  change (starRingEnd ℂ)
      ((x + y).sum fun w d =>
        d * xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ))
          ((starRingEnd ℂ) a)) =
    (starRingEnd ℂ)
      (x.sum fun w d =>
        d * xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ))
          ((starRingEnd ℂ) a)) +
    (starRingEnd ℂ)
      (y.sum fun w d =>
        d * xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ))
          ((starRingEnd ℂ) a))
  rw [Finsupp.sum_add_index'
    (fun _ => zero_mul _)
    (fun _ c d => add_mul c d _)]
  exact map_add (starRingEnd ℂ) _ _

/-- The finite source secant is exactly a two-Cauchy product, before coalescence. -/
theorem deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) {a : ℂ}
    (haw : a ≠ (w : ℂ))
    (hau : a ≠ (routePDeningerUpperSecantPoint w n : ℂ)) :
    deningerPrimeGammaUpperCauchyTest
        (routePDeningerUpperSecantPacket A w n) a =
      A * xiWeilCauchyTest (w : ℂ) a *
        xiWeilCauchyTest (routePDeningerUpperSecantPoint w n : ℂ) a := by
  have hwu : (w : ℂ) ≠ (routePDeningerUpperSecantPoint w n : ℂ) := by
    exact fun h => routePDeningerUpperSecantPoint_ne w n (Subtype.ext h.symm)
  rw [routePDeningerUpperSecantPacket,
    deningerPrimeGammaUpperCauchyTest_add,
    deningerPrimeGammaUpperCauchyTest_single,
    deningerPrimeGammaUpperCauchyTest_single]
  simp only [map_mul, map_neg, starRingEnd_self_apply]
  rw [xiWeilCauchyTest, xiWeilCauchyTest]
  field_simp [sub_ne_zero.mpr haw, sub_ne_zero.mpr hau,
    sub_ne_zero.mpr hwu]
  ring

theorem xiSpectralPoint_ne_deningerPrimeGammaUpperPoint
    (q : XiZeroCopy) (w : DeningerPrimeGammaUpperPoint) :
    xiSpectralPoint q ≠ (w : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  have hq := (xiSpectralPoint_im_mem_openHalf q).2
  have hw := deningerPrimeGammaUpperPoint_im_gt w
  linarith

/-- Coalesced upper-sector graph reporter. -/
def routePDeningerUpperSquaredCauchyTest
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (a : ℂ) : ℂ :=
  A * xiWeilCauchyTest (w : ℂ) a ^ (2 : ℕ)

theorem tendsto_deningerPrimeGammaUpperCauchyTest_secantPacket
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    Tendsto
      (fun n => deningerPrimeGammaUpperCauchyTest
        (routePDeningerUpperSecantPacket A w n) (xiSpectralPoint q))
      atTop
      (nhds (routePDeningerUpperSquaredCauchyTest A w
        (xiSpectralPoint q))) := by
  have hqw := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q w
  have hqu : ∀ n, xiSpectralPoint q ≠
      (routePDeningerUpperSecantPoint w n : ℂ) :=
    fun n => xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q _
  have hden : xiSpectralPoint q - (w : ℂ) ≠ 0 := sub_ne_zero.mpr hqw
  have hpole : Tendsto
      (fun n => (routePDeningerUpperSecantPoint w n : ℂ))
      atTop (nhds (w : ℂ)) :=
    tendsto_routePDeningerUpperSecantPoint_coe w
  have hinv : Tendsto
      (fun n => xiWeilCauchyTest
        (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q))
      atTop (nhds (xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q))) := by
    unfold xiWeilCauchyTest
    exact (tendsto_const_nhds.sub hpole).inv₀ hden
  have hA : Tendsto (fun _ : ℕ => A) atTop (nhds A) :=
    tendsto_const_nhds
  have hC : Tendsto
      (fun _ : ℕ => xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q))
      atTop (nhds (xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q))) :=
    tendsto_const_nhds
  have hprod := (hA.mul hC).mul hinv
  convert hprod using 1
  · funext n
    rw [deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket
      A w n hqw (hqu n)]
  · simp only [routePDeningerUpperSquaredCauchyTest]
    ring

/-- Uniform spectral separation of one upper source pole from the complete centered Xi strip. -/
def routePDeningerUpperSpectralGap
    (w : DeningerPrimeGammaUpperPoint) : ℝ :=
  (w : ℂ).im - 1 / 2

theorem routePDeningerUpperSpectralGap_pos
    (w : DeningerPrimeGammaUpperPoint) :
    0 < routePDeningerUpperSpectralGap w := by
  unfold routePDeningerUpperSpectralGap
  linarith [deningerPrimeGammaUpperPoint_im_gt w]

theorem routePDeningerUpperSpectralGap_lt_norm_sub
    (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    routePDeningerUpperSpectralGap w <
      ‖xiSpectralPoint q - (w : ℂ)‖ := by
  have hq := (xiSpectralPoint_im_mem_openHalf q).2
  have hw := deningerPrimeGammaUpperPoint_im_gt w
  have himneg : (xiSpectralPoint q - (w : ℂ)).im < 0 := by
    simp only [Complex.sub_im]
    linarith
  have habs : |(xiSpectralPoint q - (w : ℂ)).im| =
      (w : ℂ).im - (xiSpectralPoint q).im := by
    rw [abs_of_neg himneg]
    simp only [Complex.sub_im]
    ring
  have hnorm := Complex.abs_im_le_norm (xiSpectralPoint q - (w : ℂ))
  rw [habs] at hnorm
  unfold routePDeningerUpperSpectralGap
  linarith

theorem norm_xiWeilCauchyTest_upper_le_gap_inv
    (w : DeningerPrimeGammaUpperPoint) (q : XiZeroCopy) :
    ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ≤
      (routePDeningerUpperSpectralGap w)⁻¹ := by
  have hgap := routePDeningerUpperSpectralGap_pos w
  have hle :=
    (routePDeningerUpperSpectralGap_lt_norm_sub w q).le
  rw [xiWeilCauchyTest, norm_inv]
  simpa [one_div] using one_div_le_one_div_of_le hgap hle

theorem routePDeningerUpperSquaredCauchyTest_squareSummable
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    XiWeilSquareSummable (routePDeningerUpperSquaredCauchyTest A w) := by
  let M : ℝ := (routePDeningerUpperSpectralGap w)⁻¹
  have hM : 0 ≤ M := by
    dsimp [M]
    exact inv_nonneg.mpr (routePDeningerUpperSpectralGap_pos w).le
  have hbase := XiWeilSquareSummable_cauchy (w : ℂ)
  have hmajor : Summable (fun q : XiZeroCopy =>
      (‖A‖ ^ (2 : ℕ) * M ^ (2 : ℕ)) *
        ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ)) :=
    hbase.mul_left (‖A‖ ^ (2 : ℕ) * M ^ (2 : ℕ))
  unfold XiWeilSquareSummable
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_) hmajor
  have hc : ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ≤ M :=
    norm_xiWeilCauchyTest_upper_le_gap_inv w q
  rw [routePDeningerUpperSquaredCauchyTest, norm_mul, norm_pow]
  calc
    (‖A‖ * ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ)) ^ (2 : ℕ) =
        ‖A‖ ^ (2 : ℕ) *
          ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) *
          ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) := by ring
    _ ≤ ‖A‖ ^ (2 : ℕ) * M ^ (2 : ℕ) *
          ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) := by
      gcongr
    _ = (‖A‖ ^ (2 : ℕ) * M ^ (2 : ℕ)) *
          ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) := by ring

/-- Coalesced squared-Cauchy vector in the multiplicity-exact Xi jet Hilbert carrier. -/
def routePDeningerUpperSquaredCauchyJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    DeningerArithmeticJetHilbert :=
  xiWeilEvaluationLp (routePDeningerUpperSquaredCauchyTest A w)
    (routePDeningerUpperSquaredCauchyTest_squareSummable A w)

/-- The coalescing two-atom source packets converge in the actual Xi `ell^(2 : ℕ)` carrier to the
squared-Cauchy graph reporter.  Nodes and coefficients depend only on the source pole. -/
theorem tendsto_routePDeningerUpperSecantPacket_to_squaredCauchyJet
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) :
    Tendsto
      (fun n => deningerPrimeGammaUpperToJetHilbert
        (routePDeningerUpperSecantPacket A w n))
      atTop (nhds (routePDeningerUpperSquaredCauchyJet A w)) := by
  let M : ℝ := (routePDeningerUpperSpectralGap w)⁻¹
  let term : ℕ → XiZeroCopy → ℝ := fun n q =>
    ‖deningerPrimeGammaUpperToJetHilbert
        (routePDeningerUpperSecantPacket A w n) q -
      routePDeningerUpperSquaredCauchyJet A w q‖ ^ (2 : ℕ)
  let bound : XiZeroCopy → ℝ := fun q =>
    (4 * ‖A‖ ^ (2 : ℕ) * M ^ (2 : ℕ)) *
      ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact inv_nonneg.mpr (routePDeningerUpperSpectralGap_pos w).le
  have hboundsum : Summable bound :=
    (XiWeilSquareSummable_cauchy (w : ℂ)).mul_left
      (4 * ‖A‖ ^ (2 : ℕ) * M ^ (2 : ℕ))
  have hterm_tend : ∀ q, Tendsto (fun n => term n q) atTop (nhds 0) := by
    intro q
    have hpoint :=
      tendsto_deningerPrimeGammaUpperCauchyTest_secantPacket A w q
    have hzero := hpoint.sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => routePDeningerUpperSquaredCauchyTest A w
          (xiSpectralPoint q)) atTop
        (nhds (routePDeningerUpperSquaredCauchyTest A w
          (xiSpectralPoint q))))
    simpa only [term, deningerPrimeGammaUpperToJetHilbert_apply,
      routePDeningerUpperSquaredCauchyJet, xiWeilEvaluationLp_apply,
      sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hzero.norm.pow 2
  have hbound : ∀ n q, ‖term n q‖ ≤ bound q := by
    intro n q
    have hqw := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q w
    have hqu := xiSpectralPoint_ne_deningerPrimeGammaUpperPoint q
      (routePDeningerUpperSecantPoint w n)
    have hCw : ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ≤ M :=
      norm_xiWeilCauchyTest_upper_le_gap_inv w q
    have hgap_u : routePDeningerUpperSpectralGap
        (routePDeningerUpperSecantPoint w n) =
        routePDeningerUpperSpectralGap w := by
      simp [routePDeningerUpperSpectralGap,
        routePDeningerUpperSecantPoint]
    have hCu : ‖xiWeilCauchyTest
        (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q)‖ ≤ M := by
      simpa [hgap_u] using
        norm_xiWeilCauchyTest_upper_le_gap_inv
          (routePDeningerUpperSecantPoint w n) q
    have hdiff : ‖xiWeilCauchyTest
          (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q) -
        xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ≤ 2 * M := by
      calc
        _ ≤ ‖xiWeilCauchyTest
              (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q)‖ +
            ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add hCu hCw
        _ = 2 * M := by ring
    have hdiffsq : ‖xiWeilCauchyTest
          (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q) -
        xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) ≤
        4 * M ^ (2 : ℕ) := by
      calc
        _ ≤ (2 * M) ^ (2 : ℕ) := by gcongr
        _ = 4 * M ^ (2 : ℕ) := by ring
    dsimp only [term, bound]
    rw [Real.norm_of_nonneg (sq_nonneg _),
      deningerPrimeGammaUpperToJetHilbert_apply,
      routePDeningerUpperSquaredCauchyJet, xiWeilEvaluationLp_apply,
      deningerPrimeGammaUpperCauchyTest_routePDeningerUpperSecantPacket
        A w n hqw hqu]
    simp only [routePDeningerUpperSquaredCauchyTest]
    rw [show A * xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q) *
          xiWeilCauchyTest
            (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q) -
        A * xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q) ^ (2 : ℕ) =
          A * xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q) *
            (xiWeilCauchyTest
              (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q) -
              xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)) by ring,
      norm_mul, norm_mul]
    calc
      (‖A‖ * ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ *
          ‖xiWeilCauchyTest
            (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q) -
            xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖) ^ (2 : ℕ) =
        ‖A‖ ^ (2 : ℕ) * ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) *
          ‖xiWeilCauchyTest
            (routePDeningerUpperSecantPoint w n : ℂ) (xiSpectralPoint q) -
            xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) := by ring
      _ ≤ ‖A‖ ^ (2 : ℕ) * ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) *
          (4 * M ^ (2 : ℕ)) := by gcongr
      _ = (4 * ‖A‖ ^ (2 : ℕ) * M ^ (2 : ℕ)) *
          ‖xiWeilCauchyTest (w : ℂ) (xiSpectralPoint q)‖ ^ (2 : ℕ) := by ring
  have htsum : Tendsto (fun n => ∑' q, term n q) atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hboundsum hterm_tend
      (Eventually.of_forall hbound)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnormsq : ∀ n,
      ‖deningerPrimeGammaUpperToJetHilbert
          (routePDeningerUpperSecantPacket A w n) -
        routePDeningerUpperSquaredCauchyJet A w‖ ^ (2 : ℕ) =
        ∑' q, term n q := by
    intro n
    rw [HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro q
    rfl
  have hsqzero : Tendsto
      (fun n => ‖deningerPrimeGammaUpperToJetHilbert
          (routePDeningerUpperSecantPacket A w n) -
        routePDeningerUpperSquaredCauchyJet A w‖ ^ (2 : ℕ))
      atTop (nhds 0) :=
    htsum.congr' (Eventually.of_forall fun n => (hnormsq n).symm)
  have hsqrt := hsqzero.sqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

/-- Source-only coalescing packet attached to one actual primitive Burnol cell. -/
def routePPrimitiveBurnolDeningerSecantPacket
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (n : ℕ) :
    DeningerPrimeGammaUpperPacket :=
  routePDeningerUpperSecantPacket
    (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))
    (routePPrimitiveDeningerUpperPoint pe kappa) n

/-- The coalesced primitive source jet reports the exact coefficient-weighted Burnol Laplace
column at every strict-right Xi zero. -/
theorem routePPrimitiveBurnolDeningerSquaredCauchyJet_apply
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    routePDeningerUpperSquaredCauchyJet
        (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))
        (routePPrimitiveDeningerUpperPoint pe kappa) q.1 =
      (∫ L : ℝ in Set.Ioi 0,
        Complex.exp (-(xiRightCenteredZero q * (L : ℂ))) *
          routePPrimitiveBurnolWindowFeature pe kappa L) := by
  rw [routePDeningerUpperSquaredCauchyJet, xiWeilEvaluationLp_apply,
    routePDeningerUpperSquaredCauchyTest,
    integral_routePPrimitiveBurnolWindowFeature_eq_deningerSquaredEvaluation]
  ring

/-- Primitive specialization: a zero-independent sequence of two-atom upper source packets
converges in the complete divisor `ell^(2 : ℕ)` carrier to the coefficient-faithful graph reporter. -/
theorem tendsto_routePPrimitiveBurnolDeningerSecantPacket_to_graphJet
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    Tendsto
      (fun n => deningerPrimeGammaUpperToJetHilbert
        (routePPrimitiveBurnolDeningerSecantPacket pe kappa n))
      atTop
      (nhds (routePDeningerUpperSquaredCauchyJet
        (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))
        (routePPrimitiveDeningerUpperPoint pe kappa))) := by
  exact tendsto_routePDeningerUpperSecantPacket_to_squaredCauchyJet _ _

/-- Pointwise form of the primitive coalescent landing, with the exact Burnol integral as limit. -/
theorem tendsto_routePPrimitiveBurnolDeningerSecantPacket_reporter
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy) :
    Tendsto
      (fun n => deningerPrimeGammaUpperCauchyTest
        (routePPrimitiveBurnolDeningerSecantPacket pe kappa n)
        (xiSpectralPoint q.1))
      atTop
      (nhds (∫ L : ℝ in Set.Ioi 0,
        Complex.exp (-(xiRightCenteredZero q * (L : ℂ))) *
          routePPrimitiveBurnolWindowFeature pe kappa L)) := by
  have h := tendsto_deningerPrimeGammaUpperCauchyTest_secantPacket
    (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))
    (routePPrimitiveDeningerUpperPoint pe kappa) q.1
  rw [← routePPrimitiveBurnolDeningerSquaredCauchyJet_apply pe kappa q]
  simpa only [routePPrimitiveBurnolDeningerSecantPacket,
    routePDeningerUpperSquaredCauchyJet, xiWeilEvaluationLp_apply] using h

/-- Leading raw coefficient of the coalescing upper-sector source secant. -/
def routePDeningerUpperSecantCoefficient
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) : ℂ :=
  (starRingEnd ℂ)
    (A * ((w : ℂ) - (routePDeningerUpperSecantPoint w n : ℂ))⁻¹)

theorem norm_routePDeningerUpperSecantCoefficient
    (A : ℂ) (w : DeningerPrimeGammaUpperPoint) (n : ℕ) :
    ‖routePDeningerUpperSecantCoefficient A w n‖ =
      ‖A‖ * (n + 1 : ℝ) := by
  have hstep := routePDeningerUpperSecantStep_pos n
  rw [routePDeningerUpperSecantCoefficient]
  rw [show ‖(starRingEnd ℂ)
      (A * ((w : ℂ) - (routePDeningerUpperSecantPoint w n : ℂ))⁻¹)‖ =
      ‖A * ((w : ℂ) - (routePDeningerUpperSecantPoint w n : ℂ))⁻¹‖ by
    exact RCLike.norm_conj _]
  rw [norm_mul, norm_inv]
  rw [show (w : ℂ) - (routePDeningerUpperSecantPoint w n : ℂ) =
      -(routePDeningerUpperSecantStep n : ℂ) by
    rw [routePDeningerUpperSecantPoint_coe]
    ring]
  rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hstep]
  rw [routePDeningerUpperSecantStep]
  have hn : (0 : ℝ) < n + 1 := by positivity
  field_simp

/-- Nonzero graph columns require raw source coefficients diverging linearly, despite Hilbert
evaluation convergence. -/
theorem tendsto_norm_routePDeningerUpperSecantCoefficient_atTop
    {A : ℂ} (hA : A ≠ 0) (w : DeningerPrimeGammaUpperPoint) :
    Tendsto (fun n => ‖routePDeningerUpperSecantCoefficient A w n‖)
      atTop atTop := by
  have hnormA : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hcast : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop
  convert hcast.const_mul_atTop hnormA using 1
  funext n
  rw [norm_routePDeningerUpperSecantCoefficient]

theorem finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero
    (pe : Nat.Primes × ℕ) :
    finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) ≠ 0 := by
  rw [finiteVonMangoldtDepthOneAmplitude]
  norm_cast
  apply ne_of_gt
  apply Real.sqrt_pos.2
  apply div_pos
  · rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log pe]
    exact Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  · exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)

/-- The coefficient-faithful primitive graph landing has unavoidable linear raw-source blow-up. -/
theorem tendsto_norm_routePPrimitiveBurnolDeningerSecantCoefficient_atTop
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    Tendsto
      (fun n => ‖routePDeningerUpperSecantCoefficient
        (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe))
        (routePPrimitiveDeningerUpperPoint pe kappa) n‖)
      atTop atTop := by
  apply tendsto_norm_routePDeningerUpperSecantCoefficient_atTop
  exact neg_ne_zero.mpr
    (finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero pe)

end

end RHTower
