import GaloisForLFunctions.RHTower.ProlateDunsterWeakLimit
import GaloisForLFunctions.RHTower.CCMFirstRowEnvelopeTail

/-!
# Compact off-diagonal cancellation for the Dunster/Bessel profile

The first-row difference phase may have one nondegenerate stationary point; its integral is
already controlled by `abs_integral_firstRow_leading_le`.  The companion sum phase has no
stationary point.  This file supplies its weighted first-derivative estimate and combines both
phases into cancellation of the leading Bessel product on every fixed exterior interval.
-/

noncomputable section

open Filter MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-! ## Sum phase -/

/-- Sum of the two exterior Liouville phases in the first radial row. -/
def xiSumPhase (s k x : ℝ) : ℝ :=
  xiEndpointPhase s x + xiEndpointPhase s (k * x)

/-- Derivative of `xiSumPhase`. -/
def xiSumSpeed (s k x : ℝ) : ℝ :=
  xiSpeed s x + k * xiSpeed s (k * x)

/-- Second derivative of `xiSumPhase`. -/
def xiSumSecond (s k x : ℝ) : ℝ :=
  xiSpeedDeriv s x + k ^ 2 * xiSpeedDeriv s (k * x)

theorem hasDerivAt_xiSumPhase {s k x : ℝ} (hs0 : 0 ≤ s) (hx : 1 < x)
    (hkx : 1 < k * x) :
    HasDerivAt (xiSumPhase s k) (xiSumSpeed s k x) x := by
  have h1 := hasDerivAt_xiEndpointPhase hs0 hx
  have h2 := hasDerivAt_xiEndpointPhase_dilate (s := s) (r := k) (x := x) hs0 hkx
  have h2' : HasDerivAt (fun x : ℝ => xiEndpointPhase s (k * x))
      (k * xiSpeed s (k * x)) x := by
    rw [xiSpeed_mul]
    exact h2
  change HasDerivAt
    (fun y : ℝ => xiEndpointPhase s y + xiEndpointPhase s (k * y))
    (xiSpeed s x + k * xiSpeed s (k * x)) x
  exact h1.add h2'

theorem hasDerivAt_xiSumSpeed {s k x : ℝ} (hs1 : s ≤ 1) (hx : 1 < x)
    (hkx : 1 < k * x) :
    HasDerivAt (xiSumSpeed s k) (xiSumSecond s k x) x := by
  have h1 : HasDerivAt (xiSpeed s) (xiSpeedDeriv s x) x := by
    rw [xiSpeedDeriv]
    exact hasDerivAt_xiSpeed hs1 hx
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    simpa using (hasDerivAt_id x).const_mul k
  have h2 : HasDerivAt (fun t : ℝ => xiSpeed s (k * t))
      (xiSpeedDeriv s (k * x) * k) x :=
    (hasDerivAt_xiSpeed hs1 hkx).comp x hlin
  have h3 := h2.const_mul k
  change HasDerivAt (fun y : ℝ => xiSpeed s y + k * xiSpeed s (k * y))
    (xiSpeedDeriv s x + k ^ 2 * xiSpeedDeriv s (k * x)) x
  have hcoef : k ^ 2 * xiSpeedDeriv s (k * x) =
      k * (xiSpeedDeriv s (k * x) * k) := by ring
  rw [hcoef]
  exact h1.fun_add h3

theorem one_add_le_xiSumSpeed {s k x : ℝ} (hs1 : s ≤ 1) (hk : 0 ≤ k)
    (hx : 1 < x) (hkx : 1 < k * x) :
    1 + k ≤ xiSumSpeed s k x := by
  have h1 := one_le_xiSpeed (s := s) (t := x) hs1 hx
  have h2 := one_le_xiSpeed (s := s) (t := k * x) hs1 hkx
  rw [xiSumSpeed]
  nlinarith

theorem xiSumSecond_nonpos {s k x : ℝ} (hs1 : s ≤ 1 / 2) (hx : 1 < x)
    (hkx : 1 < k * x) : xiSumSecond s k x ≤ 0 := by
  have h1 := xiSpeedDeriv_nonpos hs1 hx
  have h2 := xiSpeedDeriv_nonpos hs1 hkx
  rw [xiSumSecond]
  nlinarith [sq_nonneg k]

theorem continuousOn_xiSumSecond {s k : ℝ} (hs1 : s ≤ 1) (hk : 2 ≤ k) :
    ContinuousOn (xiSumSecond s k) (Ioi 1) := by
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hfar : MapsTo (fun x : ℝ => k * x) (Ioi 1) (Ioi 1) := mapsTo_mul_left_Ioi hk
  have h1 := continuousOn_xiSpeedDeriv (s := s) hs1
  have h2 : ContinuousOn (fun x : ℝ => xiSpeedDeriv s (k * x)) (Ioi 1) :=
    h1.comp hlin hfar
  exact h1.add (continuousOn_const.mul h2)

theorem continuousOn_xiSumPhase {s k : ℝ} (hs0 : 0 ≤ s) (hk : 2 ≤ k) :
    ContinuousOn (xiSumPhase s k) (Ioi 1) := by
  intro x hx
  exact ((hasDerivAt_xiSumPhase hs0 hx (mapsTo_mul_left_Ioi hk hx)).continuousAt).continuousWithinAt

/-- The sum phase has speed at least `c(1+k)` and decreasing derivative. -/
theorem abs_integral_firstRow_sum_le {s c k a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 0 < c) (hab : a ≤ b) (ha : 1 < a) :
    |∫ x in a..b, ampFourthRoot s k x *
        Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
      ≤ 4 * ampFourthRoot s k a / (c * (1 + k)) := by
  have hk0 : 0 ≤ k := by linarith
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hx1 : ∀ x ∈ uIcc a b, 1 < x := fun x hx => hsub hx
  have hkx : ∀ x ∈ uIcc a b, 1 < k * x := fun x hx => mapsTo_mul_left_Ioi hk (hsub hx)
  let lam := c * (1 + k)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hw : ∀ x ∈ uIcc a b,
      HasDerivAt (ampFourthRoot s k) (ampFourthRootDeriv s k x) x :=
    fun x hx => hasDerivAt_ampFourthRoot hs1 hk (hx1 x hx)
  have hw'c : ContinuousOn (ampFourthRootDeriv s k) (uIcc a b) :=
    (continuousOn_ampFourthRootDeriv hs1 hk).mono hsub
  have hwnn : ∀ x ∈ uIcc a b, 0 ≤ ampFourthRoot s k x :=
    fun x hx => (ampFourthRoot_pos hs1 hk (hx1 x hx)).le
  have hwanti : ∀ x ∈ uIcc a b, ampFourthRootDeriv s k x ≤ 0 :=
    fun x hx => ampFourthRootDeriv_nonpos hs1 hk (hx1 x hx)
  have hg : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiSumPhase s k t - Real.pi / 2)
        (c * xiSumSpeed s k x) x := by
    intro x hx
    exact ((hasDerivAt_xiSumPhase hs0 (hx1 x hx) (hkx x hx)).const_mul c).sub_const _
  have hg' : ∀ x ∈ uIcc a b,
      HasDerivAt (fun t : ℝ => c * xiSumSpeed s k t)
        (c * xiSumSecond s k x) x :=
    fun x hx => (hasDerivAt_xiSumSpeed (by linarith) (hx1 x hx) (hkx x hx)).const_mul c
  have hg''c : ContinuousOn (fun x : ℝ => c * xiSumSecond s k x) (uIcc a b) :=
    continuousOn_const.mul ((continuousOn_xiSumSecond (by linarith) hk).mono hsub)
  have hg'lb : ∀ x ∈ uIcc a b, lam ≤ c * xiSumSpeed s k x := by
    intro x hx
    dsimp [lam]
    exact mul_le_mul_of_nonneg_left
      (one_add_le_xiSumSpeed (by linarith) hk0 (hx1 x hx) (hkx x hx)) hc.le
  have hg''np : ∀ x ∈ uIcc a b, c * xiSumSecond s k x ≤ 0 := by
    intro x hx
    exact mul_nonpos_of_nonneg_of_nonpos hc.le
      (xiSumSecond_nonpos hs1 (hx1 x hx) (hkx x hx))
  have hmain := _root_.RHTower.norm_integral_weight_cexp_le_anti hab hlam
    hw hw'c hwnn hwanti hg hg' hg''c hg'lb hg''np
  have hint : IntervalIntegrable
      (fun x => (ampFourthRoot s k x : ℂ) *
        Complex.exp (((c * xiSumPhase s k x - Real.pi / 2 : ℝ) : ℂ) * Complex.I))
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    have hamp : ContinuousOn (fun x : ℝ => (ampFourthRoot s k x : ℂ)) (uIcc a b) :=
      Complex.continuous_ofReal.comp_continuousOn ((continuousOn_ampFourthRoot hs1 hk).mono hsub)
    have hphase : ContinuousOn (fun x : ℝ => ((c * xiSumPhase s k x - Real.pi / 2 : ℝ) : ℂ))
        (uIcc a b) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_const.mul ((continuousOn_xiSumPhase hs0 hk).mono hsub)).sub continuousOn_const)
    exact hamp.mul (Complex.continuous_exp.comp_continuousOn (hphase.mul continuousOn_const))
  exact (abs_integral_mul_cos_le_norm hint).trans (by simpa [lam] using hmain)

/-! ## Leading product -/

/-- Product of the two leading cosine profiles in the first radial row. -/
def firstRowLeadingProduct (s c k x : ℝ) : ℝ :=
  (Real.sqrt (2 / Real.pi) * ampFourth s x *
      Real.cos (c * xiEndpointPhase s x - Real.pi / 4)) *
    (Real.sqrt (2 / Real.pi) * ampFourth s (k * x) *
      Real.cos (c * xiEndpointPhase s (k * x) - Real.pi / 4))

theorem ampFourth_mul_eq_ampFourthRoot {s k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    ampFourth s x * ampFourth s (k * x) = ampFourthRoot s k x := by
  have hkx : 1 < k * x := mapsTo_mul_left_Ioi hk hx
  have h1 := ampFourth_pos hs1 hx
  have h2 := ampFourth_pos hs1 hkx
  have hroot := ampFourthRoot_pos hs1 hk hx
  apply (sq_eq_sq₀ (mul_nonneg h1.le h2.le) hroot.le).mp
  rw [mul_pow, ampFourth_sq hs1 hx, ampFourth_sq hs1 hkx]
  rw [ampFourthRoot, div_pow, one_pow,
    Real.sq_sqrt (Real.sqrt_nonneg (ampPoly s k x))]
  have hkxsq : (k * x) ^ 2 = k ^ 2 * x ^ 2 := by ring
  rw [hkxsq, ampPoly]
  have hA : 0 < (x ^ 2 - 1) * (x ^ 2 - s) := by
    have hleft : 0 < x ^ 2 - 1 := by nlinarith
    have hright : 0 < x ^ 2 - s := by nlinarith
    exact mul_pos hleft hright
  have hB : 0 < (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) := by
    have hk0 : 0 < k := by linarith
    have hx0 : 0 < x := by linarith
    have hleft : 0 < k ^ 2 * x ^ 2 - 1 := by nlinarith [sq_nonneg (k * x)]
    have hright : 0 < k ^ 2 * x ^ 2 - s := by nlinarith [sq_nonneg (k * x)]
    exact mul_pos hleft hright
  rw [show (x ^ 2 - 1) * (x ^ 2 - s) * (k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s) =
      ((x ^ 2 - 1) * (x ^ 2 - s)) *
        ((k ^ 2 * x ^ 2 - 1) * (k ^ 2 * x ^ 2 - s)) by ring,
    Real.sqrt_mul hA.le]
  ring

theorem firstRowLeadingProduct_eq_phase_sum {s c k x : ℝ}
    (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) (hx : 1 < x) :
    firstRowLeadingProduct s c k x =
      (1 / Real.pi) * ampFourthRoot s k x *
        (Real.cos (c * xiDiffPhase s k x) +
          Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  rw [firstRowLeadingProduct, ← ampFourth_mul_eq_ampFourthRoot hs1 hk hx]
  let A := c * xiEndpointPhase s x - Real.pi / 4
  let B := c * xiEndpointPhase s (k * x) - Real.pi / 4
  have htrig := Real.two_mul_cos_mul_cos A B
  have hAB : A - B = c * xiDiffPhase s k x := by
    dsimp [A, B, xiDiffPhase]
    ring
  have hsum : A + B = c * xiSumPhase s k x - Real.pi / 2 := by
    dsimp [A, B, xiSumPhase]
    ring
  rw [hAB, hsum] at htrig
  rw [show Real.sqrt (2 / Real.pi) * ampFourth s x * Real.cos A *
      (Real.sqrt (2 / Real.pi) * ampFourth s (k * x) * Real.cos B) =
      (Real.sqrt (2 / Real.pi) ^ 2) *
        (ampFourth s x * ampFourth s (k * x)) * (Real.cos A * Real.cos B) by ring,
    hsqrt, ampFourth_mul_eq_ampFourthRoot hs1 hk hx]
  calc
    2 / Real.pi * ampFourthRoot s k x * (Real.cos A * Real.cos B)
        = (1 / Real.pi) * ampFourthRoot s k x * (2 * Real.cos A * Real.cos B) := by ring
    _ = (1 / Real.pi) * ampFourthRoot s k x *
        (Real.cos (c * xiDiffPhase s k x) +
          Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by rw [htrig]

/-- Both leading phases cancel on a fixed exterior interval. -/
theorem abs_integral_firstRowLeadingProduct_le {s c k a b : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 3 * k ≤ c) (hab : a ≤ b) (ha : 1 < a)
    (haCross : Real.sqrt (1 + 2 / k ^ 2) ≤ a) :
    |∫ x in a..b, firstRowLeadingProduct s c k x|
      ≤ (1 / Real.pi) *
        (340 / (Real.sqrt c * k ^ 2) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by
  have hc0 : 0 < c := by linarith
  have hcrossb : Real.sqrt (1 + 2 / k ^ 2) ≤ b := haCross.trans hab
  have hdiffFull := abs_integral_firstRow_leading_le hs0 hs1 hk hc hcrossb
  have hdiffLeft := abs_integral_firstRow_leading_le hs0 hs1 hk hc haCross
  have hdiff : |∫ x in a..b, ampFourthRoot s k x *
      Real.cos (c * xiDiffPhase s k x)| ≤ 340 / (Real.sqrt c * k ^ 2) := by
    have h1a : (1 : ℝ) ≤ a := ha.le
    have h1b : (1 : ℝ) ≤ b := h1a.trans hab
    let f : ℝ → ℝ := fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)
    have hint : ∀ p q : ℝ, 1 ≤ p → p ≤ q → IntervalIntegrable f volume p q := by
      intro p q hp hpq
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpq]
      have hbig : IntegrableOn (ampFourthRoot s k) (Ioc 1 q) volume :=
        integrableOn_ampFourthRoot hs0 hs1 hk (hp.trans hpq)
      have hsub : Ioc p q ⊆ Ioi 1 := fun _ hx => lt_of_le_of_lt hp hx.1
      have hdom : IntegrableOn (ampFourthRoot s k) (Ioc p q) volume :=
        hbig.mono_set (fun _ hx => ⟨lt_of_le_of_lt hp hx.1, hx.2⟩)
      have hmeas : AEStronglyMeasurable f (volume.restrict (Ioc p q)) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
        exact ((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
          (Real.continuous_cos.comp_continuousOn
            (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono hsub)))
      refine Integrable.mono' hdom hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx1 : 1 < x := lt_of_le_of_lt hp hx.1
      have hamp := (ampFourthRoot_pos hs1 hk hx1).le
      dsimp [f]
      rw [abs_mul, abs_of_nonneg hamp]
      nlinarith [Real.abs_cos_le_one (c * xiDiffPhase s k x)]
    have hsplit : (∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) =
        (∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
          ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) := by
      simpa [f] using (intervalIntegral.integral_add_adjacent_intervals
        (hint 1 a le_rfl h1a) (hint a b h1a hab)).symm
    have heq : (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) =
        (∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) -
          ∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) := by
      linarith [hsplit]
    rw [heq]
    calc
      |(∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) -
          ∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
          ≤ |∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)| +
            |∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)| :=
        abs_sub _ _
      _ ≤ 340 / (Real.sqrt c * k ^ 2) := by
        calc
          |∫ x in (1 : ℝ)..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)| +
              |∫ x in (1 : ℝ)..a, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)|
              ≤ 170 / (Real.sqrt c * k ^ 2) + 170 / (Real.sqrt c * k ^ 2) :=
            add_le_add hdiffFull hdiffLeft
          _ = 340 / (Real.sqrt c * k ^ 2) := by ring
  have hsum := abs_integral_firstRow_sum_le hs0 hs1 hk hc0 hab ha
  have hpoint : ∀ x ∈ uIcc a b, firstRowLeadingProduct s c k x =
      (1 / Real.pi) * (ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) +
        ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) := by
    intro x hx
    have hx' : 1 < x := by rw [uIcc_of_le hab] at hx; exact ha.trans_le hx.1
    rw [firstRowLeadingProduct_eq_phase_sum hs1 hk hx']
    ring
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul]
  have hsub : uIcc a b ⊆ Ioi 1 := by
    rw [uIcc_of_le hab]
    exact fun _ hx => ha.trans_le hx.1
  have hdiffInt : IntervalIntegrable
      (fun x => ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) volume a b :=
    (((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
      (Real.continuous_cos.comp_continuousOn
        (continuousOn_const.mul ((continuousOn_xiDiffPhase hs0 hk).mono hsub)))).intervalIntegrable
  have hsumInt : IntervalIntegrable
      (fun x => ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2))
      volume a b :=
    (((continuousOn_ampFourthRoot hs1 hk).mono hsub).mul
      (Real.continuous_cos.comp_continuousOn
        ((continuousOn_const.mul ((continuousOn_xiSumPhase hs0 hk).mono hsub)).sub
          continuousOn_const))).intervalIntegrable
  have hInt :
      (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x) +
        ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)) =
      (∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
        ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2) := by
    rw [intervalIntegral.integral_add hdiffInt hsumInt]
  rw [hInt, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.pi)]
  calc
    1 / Real.pi * |(∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x)) +
        ∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)|
        ≤ (1 / Real.pi) *
          (|(∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiDiffPhase s k x))| +
            |∫ x in a..b, ampFourthRoot s k x * Real.cos (c * xiSumPhase s k x - Real.pi / 2)|) := by
          gcongr
          exact abs_add_le _ _
    _ ≤ (1 / Real.pi) *
        (340 / (Real.sqrt c * k ^ 2) +
          4 * ampFourthRoot s k a / (c * (1 + k))) := by gcongr

/-- The leading first-row Bessel product vanishes on every fixed compact exterior interval. -/
theorem tendsto_integral_firstRowLeadingProduct
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i)
    {k a b : ℝ} (hk : 2 ≤ k) (hab : a ≤ b) (ha : 1 < a)
    (haCross : Real.sqrt (1 + 2 / k ^ 2) ≤ a) :
    Tendsto (fun i => ∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x)
      l (nhds 0) := by
  have hka : 1 < k * a := mapsTo_mul_left_Ioi hk ha
  have hAa := tendsto_ampFourth_fixed_radius hs ha
  have hAka := tendsto_ampFourth_fixed_radius hs hka
  have hAmp : Tendsto (fun i => ampFourthRoot (s i) k a) l
      (nhds (ampFourth 0 a * ampFourth 0 (k * a))) := by
    have hmul := hAa.mul hAka
    apply hmul.congr'
    filter_upwards [hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with i hsi
    exact ampFourth_mul_eq_ampFourthRoot hsi.le hk ha
  have hsqrt : Tendsto (fun i => Real.sqrt (c i)) l atTop :=
    Real.tendsto_sqrt_atTop.comp hc
  have hk2 : 0 < k ^ 2 := by positivity
  have hden1 : Tendsto (fun i => Real.sqrt (c i) * k ^ 2) l atTop :=
    hsqrt.atTop_mul_const hk2
  have hterm1 : Tendsto (fun i => 340 / (Real.sqrt (c i) * k ^ 2)) l (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hden1
  have h1k : 0 < 1 + k := by linarith
  have hden2 : Tendsto (fun i => c i * (1 + k)) l atTop :=
    hc.atTop_mul_const h1k
  have hnum2 : Tendsto (fun i => 4 * ampFourthRoot (s i) k a) l
      (nhds (4 * (ampFourth 0 a * ampFourth 0 (k * a)))) := hAmp.const_mul 4
  have hterm2 : Tendsto
      (fun i => 4 * ampFourthRoot (s i) k a / (c i * (1 + k))) l (nhds 0) :=
    Tendsto.div_atTop hnum2 hden2
  have hmajor : Tendsto (fun i => (1 / Real.pi) *
      (340 / (Real.sqrt (c i) * k ^ 2) +
        4 * ampFourthRoot (s i) k a / (c i * (1 + k)))) l (nhds 0) := by
    convert (hterm1.add hterm2).const_mul (1 / Real.pi) using 1 <;> ring
  have hsHalf : ∀ᶠ i in l, s i ≤ 1 / 2 :=
    (hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ hi => hi.le
  have hcLarge : ∀ᶠ i in l, 3 * k ≤ c i := hc.eventually (eventually_ge_atTop (3 * k))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero, Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun i => abs_nonneg
      (∫ x in a..b, firstRowLeadingProduct (s i) (c i) k x))
    (by
      filter_upwards [hs0, hsHalf, hcLarge] with i hsi0 hsi1 hci
      exact abs_integral_firstRowLeadingProduct_le hsi0 hsi1 hk hci hab ha haCross)
    hmajor

/-! ## Exact Bessel product on a compact interval -/

/-- The rescaled regular Dunster/Bessel profile whose square is
`radialProlateBesselDensity`. -/
def radialProlateBesselProfile (s c x : ℝ) : ℝ :=
  Real.sqrt c * xiAmplitude s x * besselJ0 (c * xiEndpointPhase s x)

/-- Product of the two regular profiles in the first radial row. -/
def firstRowBesselProduct (s c k x : ℝ) : ℝ :=
  radialProlateBesselProfile s c x * radialProlateBesselProfile s c (k * x)

/-- Uniform Bessel-symbol error beyond a fixed strict exterior radius. -/
def compactBesselProfileError (s c a : ℝ) : ℝ :=
  5 * ampFourth s a / Real.sqrt (Real.sqrt (c * xiEndpointPhase s a))

theorem continuousOn_ampFourth_exterior {s : ℝ} (hs1 : s ≤ 1 / 2) :
    ContinuousOn (ampFourth s) (Ioi 1) := by
  intro x hx
  have hleft : 0 < x ^ 2 - 1 := by nlinarith
  have hright : 0 < x ^ 2 - s := by nlinarith
  have hden : Real.sqrt (Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))) ≠ 0 := by positivity
  unfold ampFourth
  exact continuousWithinAt_const.div
    (Real.continuous_sqrt.continuousAt.comp
      (Real.continuous_sqrt.continuousAt.comp (by fun_prop))).continuousWithinAt hden

theorem continuousOn_radialProlateBesselProfile
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    ContinuousOn (radialProlateBesselProfile s c) (Ioi 1) := by
  have hamp := continuousOn_xiAmplitude hs0 hs1
  have hphase := continuousOn_xiEndpointPhase hs0
  unfold radialProlateBesselProfile
  exact (continuousOn_const.mul hamp).mul
    (continuous_besselJ0.comp_continuousOn (continuousOn_const.mul hphase))

theorem continuousOn_firstRowBesselProduct
    {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) :
    ContinuousOn (firstRowBesselProduct s c k) (Ioi 1) := by
  have hp := continuousOn_radialProlateBesselProfile hs0 hs1
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  unfold firstRowBesselProduct
  exact hp.mul (hp.comp hlin (mapsTo_mul_left_Ioi hk))

theorem continuousOn_firstRowLeadingProduct
    {s c k : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k) :
    ContinuousOn (firstRowLeadingProduct s c k) (Ioi 1) := by
  have hamp := continuousOn_ampFourth_exterior hs1
  have hphase := continuousOn_xiEndpointPhase hs0
  have hlin : ContinuousOn (fun x : ℝ => k * x) (Ioi 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hfarAmp := hamp.comp hlin (mapsTo_mul_left_Ioi hk)
  have hfarPhase := hphase.comp hlin (mapsTo_mul_left_Ioi hk)
  unfold firstRowLeadingProduct
  exact ((continuousOn_const.mul hamp).mul
    (Real.continuous_cos.comp_continuousOn
      ((continuousOn_const.mul hphase).sub continuousOn_const))).mul
    ((continuousOn_const.mul hfarAmp).mul
      (Real.continuous_cos.comp_continuousOn
        ((continuousOn_const.mul hfarPhase).sub continuousOn_const)))

theorem compactBesselProfileError_nonneg
    {s c a : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (ha : 1 < a) :
    0 ≤ compactBesselProfileError s c a := by
  rw [compactBesselProfileError]
  exact div_nonneg (mul_nonneg (by norm_num) (ampFourth_pos hs1 ha).le) (Real.sqrt_nonneg _)

/-- The Bessel asymptotic error is uniform to the right of a fixed exterior radius. -/
theorem abs_radialProlateBesselProfile_sub_leading_le
    {s c a x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hc : 0 < c) (ha : 1 < a) (hax : a ≤ x)
    (hcxi : 1 ≤ c * xiEndpointPhase s a) :
    |radialProlateBesselProfile s c x -
        Real.sqrt (2 / Real.pi) * ampFourth s x *
          Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ compactBesselProfileError s c a := by
  have hx : 1 < x := ha.trans_le hax
  have hphase : xiEndpointPhase s a ≤ xiEndpointPhase s x :=
    xiEndpointPhase_le_of_le hs0 hs1 ha.le hax
  have harg : c * xiEndpointPhase s a ≤ c * xiEndpointPhase s x :=
    mul_le_mul_of_nonneg_left hphase hc.le
  have hraw := abs_profile_sub_model_le hs0 hs1 hx hc (hcxi.trans harg)
  change |radialProlateBesselProfile s c x - _| ≤ _
  refine hraw.trans ?_
  rw [compactBesselProfileError]
  have hamp := ampFourth_le_of_le hs1 ha hax
  have hdena : 0 < Real.sqrt (Real.sqrt (c * xiEndpointPhase s a)) := by
    exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hdenx : Real.sqrt (Real.sqrt (c * xiEndpointPhase s a)) ≤
      Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt harg)
  calc
    5 * ampFourth s x / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x))
        ≤ 5 * ampFourth s a / Real.sqrt (Real.sqrt (c * xiEndpointPhase s x)) := by
          gcongr
    _ ≤ 5 * ampFourth s a / Real.sqrt (Real.sqrt (c * xiEndpointPhase s a)) := by
          exact div_le_div_of_nonneg_left (by positivity) hdena hdenx

/-- Uniform absolute size of the leading cosine profile on the compact ray. -/
theorem abs_radialProlateLeadingProfile_le
    {s c a x : ℝ} (hs1 : s ≤ 1 / 2) (ha : 1 < a) (hax : a ≤ x) :
    |Real.sqrt (2 / Real.pi) * ampFourth s x *
        Real.cos (c * xiEndpointPhase s x - Real.pi / 4)|
      ≤ Real.sqrt (2 / Real.pi) * ampFourth s a := by
  have hx : 1 < x := ha.trans_le hax
  have hamp0 := (ampFourth_pos hs1 hx).le
  have hamp := ampFourth_le_of_le hs1 ha hax
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (2 / Real.pi) * ampFourth s x)]
  have hcos := Real.abs_cos_le_one (c * xiEndpointPhase s x - Real.pi / 4)
  nlinarith [Real.sqrt_nonneg (2 / Real.pi), ampFourth_pos hs1 ha]

/-- Uniform pointwise difference between the exact Bessel product and its two-cosine leading
product on a compact first-row interval. -/
theorem abs_firstRowBesselProduct_sub_leading_le
    {s c k a x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 2 ≤ k)
    (hc : 0 < c) (ha : 1 < a) (hax : a ≤ x)
    (hcxi : 1 ≤ c * xiEndpointPhase s a) :
    |firstRowBesselProduct s c k x - firstRowLeadingProduct s c k x|
      ≤ compactBesselProfileError s c a * compactBesselProfileError s c (k * a)
        + compactBesselProfileError s c a *
            (Real.sqrt (2 / Real.pi) * ampFourth s (k * a))
        + (Real.sqrt (2 / Real.pi) * ampFourth s a) *
            compactBesselProfileError s c (k * a) := by
  have hka : 1 < k * a := mapsTo_mul_left_Ioi hk ha
  have hk0 : 0 < k := by linarith
  have hkax : k * a ≤ k * x := mul_le_mul_of_nonneg_left hax hk0.le
  have hphase : xiEndpointPhase s a ≤ xiEndpointPhase s (k * a) :=
    xiEndpointPhase_le_of_le hs0 hs1 ha.le (by nlinarith)
  have hcxiFar : 1 ≤ c * xiEndpointPhase s (k * a) :=
    hcxi.trans (mul_le_mul_of_nonneg_left hphase hc.le)
  let P := radialProlateBesselProfile s c x
  let Q := radialProlateBesselProfile s c (k * x)
  let L := Real.sqrt (2 / Real.pi) * ampFourth s x *
    Real.cos (c * xiEndpointPhase s x - Real.pi / 4)
  let M := Real.sqrt (2 / Real.pi) * ampFourth s (k * x) *
    Real.cos (c * xiEndpointPhase s (k * x) - Real.pi / 4)
  have hP : |P - L| ≤ compactBesselProfileError s c a :=
    abs_radialProlateBesselProfile_sub_leading_le hs0 hs1 hc ha hax hcxi
  have hQ : |Q - M| ≤ compactBesselProfileError s c (k * a) :=
    abs_radialProlateBesselProfile_sub_leading_le hs0 hs1 hc hka hkax hcxiFar
  have hL : |L| ≤ Real.sqrt (2 / Real.pi) * ampFourth s a :=
    abs_radialProlateLeadingProfile_le hs1 ha hax
  have hM : |M| ≤ Real.sqrt (2 / Real.pi) * ampFourth s (k * a) :=
    abs_radialProlateLeadingProfile_le hs1 hka hkax
  have hEa := compactBesselProfileError_nonneg hs0 hs1 hc ha
  have hEka := compactBesselProfileError_nonneg hs0 hs1 hc hka
  have hT : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hfac : P * Q - L * M = (P - L) * (Q - M) + (P - L) * M + L * (Q - M) := by ring
  change |P * Q - L * M| ≤ _
  rw [hfac]
  calc
    |(P - L) * (Q - M) + (P - L) * M + L * (Q - M)|
        ≤ |P - L| * |Q - M| + |P - L| * |M| + |L| * |Q - M| := by
          rw [abs_mul, abs_mul, abs_mul]
          exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ compactBesselProfileError s c a * compactBesselProfileError s c (k * a)
        + compactBesselProfileError s c a *
            (Real.sqrt (2 / Real.pi) * ampFourth s (k * a))
        + (Real.sqrt (2 / Real.pi) * ampFourth s a) *
            compactBesselProfileError s c (k * a) := by
          gcongr

theorem tendsto_compactBesselProfileError_zero
    {ι : Type*} {l : Filter ι} {c s : ι → ℝ}
    (hc : Tendsto c l atTop) (hs : Tendsto s l (nhds 0))
    (hs0 : ∀ᶠ i in l, 0 ≤ s i) {a : ℝ} (ha : 1 < a) :
    Tendsto (fun i => compactBesselProfileError (s i) (c i) a) l (nhds 0) := by
  have harg := tendsto_c_mul_xiEndpointPhase_fixed_radius_atTop hc hs hs0 ha
  have hroot : Tendsto
      (fun i => Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a))) l atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp harg)
  have hA := tendsto_ampFourth_fixed_radius hs ha
  rw [show (fun i => compactBesselProfileError (s i) (c i) a) =
      fun i => (5 * ampFourth (s i) a) /
        Real.sqrt (Real.sqrt (c i * xiEndpointPhase (s i) a)) by
    funext i
    rw [compactBesselProfileError]]
  exact Tendsto.div_atTop (hA.const_mul 5) hroot


end GaloisForLFunctions.RHTower

end
