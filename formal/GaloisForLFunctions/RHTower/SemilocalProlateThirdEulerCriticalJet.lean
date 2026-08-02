import GaloisForLFunctions.RHTower.SemilocalProlateSecondEulerCriticalJet

/-!
# Third Euler jet of the semilocal prolate critical potential

The published `q³` determinant-ratio formula has a source term absent at orders one and two.
Its direct contribution to the positive Jacobi radius is alternating of order `n^(5/2)`.
This file propagates the literal source coefficient through the four-radius Route-J weld.
-/

noncomputable section

open Filter Real
open scoped BigOperators Topology

namespace RHTower.ThirdEulerCriticalJet

open GaloisForLFunctions.HTGeometry
open FirstEulerCriticalJet SecondEulerCriticalJet

/-- Positive amplitude of the source atom `tₙ=2√2 αₙ`. -/
def positiveSemilocalFirstEulerAtom (n : ℕ) : ℝ :=
  2 * Real.sqrt 2 * normalizedCentralBinom n

theorem semilocalFirstEulerAtom_eq_signed_positive (n : ℕ) :
    semilocalFirstEulerAtom n =
      (-1 : ℝ) ^ n * positiveSemilocalFirstEulerAtom n := by
  unfold semilocalFirstEulerAtom positiveSemilocalFirstEulerAtom
    signedCentralBinom
  ring

theorem semilocalFirstEulerAtom_succ (n : ℕ) :
    semilocalFirstEulerAtom (n + 1) =
      -centralBinomRatio n * semilocalFirstEulerAtom n := by
  rw [semilocalFirstEulerAtom_eq_signed_positive,
    semilocalFirstEulerAtom_eq_signed_positive]
  unfold positiveSemilocalFirstEulerAtom
  rw [normalizedCentralBinom_succ_eq_ratio, pow_succ]
  ring

/-- Source partial parity trace in cancellation-exposing hypergeometric form. -/
def sourceParityTraceSum (n : ℕ) : ℝ :=
  1 + semilocalFirstEulerAtom n *
    ((n : ℝ) + 1 - semilocalHypergeometricTail n / 2)

/-- Previous parity trace, expressed at the same endpoint `n`. -/
def sourcePreviousParityTraceSum (n : ℕ) : ℝ :=
  1 - semilocalFirstEulerAtom n *
    ((n : ℝ) + semilocalHypergeometricTail n / 2)

/-- Polynomial `p(n)=1-(4n+1)^2/2` of the new `ℓ=1` source atom. -/
def thirdTracePolynomial (n : ℕ) : ℝ :=
  1 - (4 * (n : ℝ) + 1) ^ 2 / 2

/-- `q³` coefficient contributed by products of the first parity determinant ratios. -/
def publishedThirdBaseRelativeCoefficient (n : ℕ) : ℝ :=
  let t := semilocalFirstEulerAtom
  let s := sourceParityTraceSum n
  let sPrev := sourcePreviousParityTraceSum n
  t (n + 1) * (sPrev - 2) * sPrev -
    t n * (s - 2) * s +
    t n * t (n + 1) * (sPrev + s - 2)

/-- Direct `ℓ=1` trace contribution to the relative squared-radius `q³` coefficient. -/
def publishedThirdAdditionalRelativeCoefficient (n : ℕ) : ℝ :=
  semilocalFirstEulerAtom (n + 1) * thirdTracePolynomial (n + 1) -
    semilocalFirstEulerAtom n * thirdTracePolynomial n

/-- Literal published relative `q³` coefficient of `aₙ(q)^2`. -/
def squaredJacobiRadiusThirdRelativeCoefficient (n : ℕ) : ℝ :=
  publishedThirdBaseRelativeCoefficient n +
    publishedThirdAdditionalRelativeCoefficient n

/-- Literal published absolute `q³` coefficient of `aₙ(q)^2`. -/
def squaredJacobiRadiusThirdCoefficient (n : ℕ) : ℝ :=
  archimedeanSquaredRadius n *
    squaredJacobiRadiusThirdRelativeCoefficient n

/-- `q³` coefficient on the positive square-root Jacobi-radius branch. -/
def jacobiRadiusThirdCoefficient (n : ℕ) : ℝ :=
  (squaredJacobiRadiusThirdCoefficient n -
      2 * jacobiRadiusJet n * jacobiRadiusSecondCoefficient n) /
    (2 * semilocalArchimedeanJacobiCoefficient n)

theorem publishedThirdBaseRelativeCoefficient_eq_simplified (n : ℕ) :
    publishedThirdBaseRelativeCoefficient n =
      (1 + centralBinomRatio n) * semilocalFirstEulerAtom n -
        semilocalFirstEulerAtom n ^ 3 *
          (centralBinomRatio n *
              ((n : ℝ) + semilocalHypergeometricTail n / 2) ^ 2 +
            ((n : ℝ) + 1 - semilocalHypergeometricTail n / 2) ^ 2 +
            centralBinomRatio n *
              (1 - semilocalHypergeometricTail n)) := by
  unfold publishedThirdBaseRelativeCoefficient sourceParityTraceSum
    sourcePreviousParityTraceSum
  dsimp only
  rw [semilocalFirstEulerAtom_succ]
  ring

/-- Positive polynomial-rational amplitude exposed by the `ℓ=1` trace term. -/
def thirdAdditionalPolynomialAmplitude (n : ℕ) : ℝ :=
  16 * (n : ℝ) ^ 2 + 20 * (n : ℝ) + 5 +
    1 / (4 * ((n : ℝ) + 1))

theorem thirdAdditionalPolynomialAmplitude_eq (n : ℕ) :
    -(centralBinomRatio n * thirdTracePolynomial (n + 1) +
        thirdTracePolynomial n) =
      thirdAdditionalPolynomialAmplitude n := by
  unfold centralBinomRatio thirdTracePolynomial
    thirdAdditionalPolynomialAmplitude
  push_cast
  have hn : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  have hn' : 4 * ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hn, hn']
  ring

theorem publishedThirdAdditionalRelativeCoefficient_eq_signed (n : ℕ) :
    publishedThirdAdditionalRelativeCoefficient n =
      (-1 : ℝ) ^ n * positiveSemilocalFirstEulerAtom n *
        thirdAdditionalPolynomialAmplitude n := by
  unfold publishedThirdAdditionalRelativeCoefficient
  rw [semilocalFirstEulerAtom_succ,
    semilocalFirstEulerAtom_eq_signed_positive]
  rw [show
    -centralBinomRatio n *
          ((-1 : ℝ) ^ n * positiveSemilocalFirstEulerAtom n) *
          thirdTracePolynomial (n + 1) -
        (-1 : ℝ) ^ n * positiveSemilocalFirstEulerAtom n *
          thirdTracePolynomial n =
      (-1 : ℝ) ^ n * positiveSemilocalFirstEulerAtom n *
        (-(centralBinomRatio n * thirdTracePolynomial (n + 1) +
          thirdTracePolynomial n)) by ring]
  rw [thirdAdditionalPolynomialAmplitude_eq]

/-- Exact positive dominant amplitude of the third Jacobi-radius coefficient. -/
def thirdRadiusDominantAmplitude (n : ℕ) : ℝ :=
  semilocalArchimedeanJacobiCoefficient n *
    positiveSemilocalFirstEulerAtom n *
    thirdAdditionalPolynomialAmplitude n / 2

/-- Signed residual after removing the direct `ℓ=1` dominant amplitude. -/
def thirdRadiusRemainderAmplitude (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * jacobiRadiusThirdCoefficient n -
    thirdRadiusDominantAmplitude n

theorem jacobiRadiusThirdCoefficient_eq_signed_amplitudes (n : ℕ) :
    jacobiRadiusThirdCoefficient n =
      (-1 : ℝ) ^ n *
        (thirdRadiusDominantAmplitude n +
          thirdRadiusRemainderAmplitude n) := by
  unfold thirdRadiusRemainderAmplitude
  have hsign : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [mul_add, mul_sub]
  rw [← mul_assoc ((-1 : ℝ) ^ n) ((-1 : ℝ) ^ n)
    (jacobiRadiusThirdCoefficient n)]
  have hmul : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    simpa [pow_two] using hsign
  rw [hmul, one_mul]
  ring

/-- Terms in the critical `q³` coefficient linear in the third radius coefficient. -/
def criticalResidualThirdLinearCoefficient (n : ℕ) : ℝ :=
  let m := 2 * n
  let r := semilocalArchimedeanJacobiCoefficient
  let w := jacobiRadiusThirdCoefficient
  w m * r (m + 1) + r m * w (m + 1) -
    2 * r (m + 1) * w (m + 1) -
    2 * r (m + 2) * w (m + 2) +
    w (m + 2) * r (m + 3) + r (m + 2) * w (m + 3)

/-- Mixed first/second-radius terms in the critical `q³` coefficient. -/
def criticalResidualFirstSecondMixedCoefficient (n : ℕ) : ℝ :=
  let m := 2 * n
  let u := jacobiRadiusJet
  let v := jacobiRadiusSecondCoefficient
  v m * u (m + 1) + u m * v (m + 1) -
    2 * u (m + 1) * v (m + 1) -
    2 * u (m + 2) * v (m + 2) +
    v (m + 2) * u (m + 3) + u (m + 2) * v (m + 3)

/-- Exact `q³` coefficient of the four-radius critical residual. -/
def criticalResidualThirdCoefficient (n : ℕ) : ℝ :=
  criticalResidualThirdLinearCoefficient n +
    criticalResidualFirstSecondMixedCoefficient n

theorem criticalResidualThirdCoefficient_eq_expanded (n : ℕ) :
    criticalResidualThirdCoefficient n =
      let m := 2 * n
      let r := semilocalArchimedeanJacobiCoefficient
      let u := jacobiRadiusJet
      let v := jacobiRadiusSecondCoefficient
      let w := jacobiRadiusThirdCoefficient
      w m * r (m + 1) + v m * u (m + 1) + u m * v (m + 1) +
        r m * w (m + 1) -
        (2 * r (m + 1) * w (m + 1) +
          2 * u (m + 1) * v (m + 1)) -
        (2 * r (m + 2) * w (m + 2) +
          2 * u (m + 2) * v (m + 2)) +
        w (m + 2) * r (m + 3) + v (m + 2) * u (m + 3) +
        u (m + 2) * v (m + 3) + r (m + 2) * w (m + 3) := by
  unfold criticalResidualThirdCoefficient
    criticalResidualThirdLinearCoefficient
    criticalResidualFirstSecondMixedCoefficient
  dsimp only
  ring

/-- Natural `n^(3/2)` scale of the direct relative third coefficient. -/
def thirdRelativeScale (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)

/-- Natural `n^(3/2)` scale of the subleading third-radius amplitude. -/
def thirdRadiusRemainderScale (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)

/-- Natural `n^(5/2)` scale of the third-radius coefficient. -/
def thirdRadiusScale (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1)

/-- Natural `n^(7/2)` scale of the squared-radius third coefficient. -/
def thirdSquaredRadiusScale (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 3 * Real.sqrt ((n : ℝ) + 1)

/-- Sharp positive amplitude of the alternating third-radius leading term. -/
def thirdRadiusBoundaryAmplitude : ℝ :=
  8 * positiveEulerBoundaryAmplitude

private theorem tendsto_succ_inv_zero :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (nhds 0) := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hx

theorem tendsto_sqrt_succ_mul_positiveSemilocalFirstEulerAtom :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt ((n : ℝ) + 1) *
          positiveSemilocalFirstEulerAtom n)
      atTop (nhds positiveEulerBoundaryAmplitude) := by
  have h :=
    tendsto_sqrt_succ_mul_normalizedCentralBinom.const_mul
      (2 * Real.sqrt 2)
  convert h using 1
  · funext n
    unfold positiveSemilocalFirstEulerAtom
    ring
  · unfold positiveEulerBoundaryAmplitude
    ring

theorem tendsto_thirdAdditionalPolynomialAmplitude_div_sq :
    Tendsto
      (fun n : ℕ =>
        thirdAdditionalPolynomialAmplitude n / ((n : ℝ) + 1) ^ 2)
      atTop (nhds 16) := by
  have hi := tendsto_succ_inv_zero
  have h16 : Tendsto (fun _ : ℕ => (16 : ℝ)) atTop (nhds 16) :=
    tendsto_const_nhds
  have h :=
    (((h16.sub (hi.const_mul 12)).add (hi.pow 2)).add
      ((hi.pow 3).const_mul (1 / 4 : ℝ)))
  convert h using 1
  · funext n
    unfold thirdAdditionalPolynomialAmplitude
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hx]
    ring
  · norm_num

theorem tendsto_publishedThirdAdditionalRelativeCoefficient_signed :
    Tendsto
      (fun n : ℕ =>
        ((-1 : ℝ) ^ n *
          publishedThirdAdditionalRelativeCoefficient n) /
            thirdRelativeScale n)
      atTop (nhds (16 * positiveEulerBoundaryAmplitude)) := by
  have ht := tendsto_sqrt_succ_mul_positiveSemilocalFirstEulerAtom
  have hp := tendsto_thirdAdditionalPolynomialAmplitude_div_sq
  have h := ht.mul hp
  convert h using 1
  · funext n
    rw [publishedThirdAdditionalRelativeCoefficient_eq_signed]
    unfold thirdRelativeScale
    have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    have hsqrt : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    have hsquare :
        Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have hmul : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      simpa [pow_two] using hs
    have hcancel :
        (-1 : ℝ) ^ n *
            ((-1 : ℝ) ^ n * positiveSemilocalFirstEulerAtom n *
              thirdAdditionalPolynomialAmplitude n) =
          positiveSemilocalFirstEulerAtom n *
            thirdAdditionalPolynomialAmplitude n := by
      calc
        _ = (((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
            positiveSemilocalFirstEulerAtom n *
              thirdAdditionalPolynomialAmplitude n) := by ring
        _ = _ := by rw [hmul]; ring
    rw [hcancel]
    field_simp [hx, hsqrt]
    rw [hsquare]
  · ring

/-- Positive signed amplitude of the published base determinant-ratio term. -/
def thirdBaseRelativeAmplitude (n : ℕ) : ℝ :=
  (1 + centralBinomRatio n) * positiveSemilocalFirstEulerAtom n -
    positiveSemilocalFirstEulerAtom n ^ 3 *
      (centralBinomRatio n *
          ((n : ℝ) + semilocalHypergeometricTail n / 2) ^ 2 +
        ((n : ℝ) + 1 - semilocalHypergeometricTail n / 2) ^ 2 +
        centralBinomRatio n *
          (1 - semilocalHypergeometricTail n))

theorem publishedThirdBaseRelativeCoefficient_eq_signed (n : ℕ) :
    publishedThirdBaseRelativeCoefficient n =
      (-1 : ℝ) ^ n * thirdBaseRelativeAmplitude n := by
  rw [publishedThirdBaseRelativeCoefficient_eq_simplified,
    semilocalFirstEulerAtom_eq_signed_positive]
  unfold thirdBaseRelativeAmplitude
  have hc : (((-1 : ℝ) ^ n) *
      positiveSemilocalFirstEulerAtom n) ^ 3 =
      (-1 : ℝ) ^ n * positiveSemilocalFirstEulerAtom n ^ 3 := by
    rw [mul_pow]
    congr 1
    rw [← pow_mul, show n * 3 = n + 2 * n by omega,
      pow_add, pow_mul]
    norm_num
  rw [hc]
  ring

private theorem tendsto_tail_div_succ_zero :
    Tendsto
      (fun n : ℕ =>
        semilocalHypergeometricTail n / ((n : ℝ) + 1))
      atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using
    tendsto_semilocalHypergeometricTail.mul tendsto_succ_inv_zero

private theorem tendsto_thirdBaseFirstFactor :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + semilocalHypergeometricTail n / 2) /
          ((n : ℝ) + 1))
      atTop (nhds 1) := by
  have hi := tendsto_succ_inv_zero
  have htail := tendsto_tail_div_succ_zero.div_const 2
  have h := ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hi).add htail
  convert h using 1
  · funext n
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hx]
    ring
  · ring

private theorem tendsto_thirdBaseSecondFactor :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1 - semilocalHypergeometricTail n / 2) /
          ((n : ℝ) + 1))
      atTop (nhds 1) := by
  have htail := tendsto_tail_div_succ_zero.div_const 2
  have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub htail
  convert h using 1
  · funext n
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hx]
  · ring

private theorem tendsto_thirdBaseBracket_div_sq :
    Tendsto
      (fun n : ℕ =>
        (centralBinomRatio n *
            ((n : ℝ) + semilocalHypergeometricTail n / 2) ^ 2 +
          ((n : ℝ) + 1 - semilocalHypergeometricTail n / 2) ^ 2 +
          centralBinomRatio n *
            (1 - semilocalHypergeometricTail n)) /
          ((n : ℝ) + 1) ^ 2)
      atTop (nhds 2) := by
  have hq := tendsto_centralBinomRatio
  have hfirst := tendsto_thirdBaseFirstFactor
  have hsecond := tendsto_thirdBaseSecondFactor
  have hlast :
      Tendsto
        (fun n : ℕ =>
          (1 - semilocalHypergeometricTail n) /
            ((n : ℝ) + 1) ^ 2)
        atTop (nhds 0) := by
    have hnum := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
        tendsto_semilocalHypergeometricTail
    have h := hnum.mul (tendsto_succ_inv_zero.pow 2)
    simpa [div_eq_mul_inv] using h
  have h := (hq.mul (hfirst.pow 2)).add (hsecond.pow 2) |>.add
    (hq.mul hlast)
  convert h using 1
  · funext n
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hx]
  · norm_num

theorem tendsto_thirdBaseRelativeAmplitude_div_sqrt :
    Tendsto
      (fun n : ℕ =>
        thirdBaseRelativeAmplitude n /
          Real.sqrt ((n : ℝ) + 1))
      atTop
      (nhds (-2 * positiveEulerBoundaryAmplitude ^ 3)) := by
  have ht := tendsto_sqrt_succ_mul_positiveSemilocalFirstEulerAtom
  have hq := tendsto_centralBinomRatio
  have hfirst :
      Tendsto
        (fun n : ℕ =>
          (1 + centralBinomRatio n) *
            positiveSemilocalFirstEulerAtom n /
              Real.sqrt ((n : ℝ) + 1))
        atTop (nhds 0) := by
    have h :=
      (((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hq).mul ht).mul
        tendsto_succ_inv_zero
    convert h using 1
    · funext n
      have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
      have hsquare :
          Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      field_simp [hs]
      rw [hsquare]
    · ring
  have hsecond :=
    (ht.pow 3).mul tendsto_thirdBaseBracket_div_sq
  have hsecond' :
      Tendsto
        (fun n : ℕ =>
          positiveSemilocalFirstEulerAtom n ^ 3 *
            (centralBinomRatio n *
                ((n : ℝ) + semilocalHypergeometricTail n / 2) ^ 2 +
              ((n : ℝ) + 1 - semilocalHypergeometricTail n / 2) ^ 2 +
              centralBinomRatio n *
                (1 - semilocalHypergeometricTail n)) /
            Real.sqrt ((n : ℝ) + 1))
        atTop (nhds (2 * positiveEulerBoundaryAmplitude ^ 3)) := by
    convert hsecond using 1
    · funext n
      have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
      have hsquare :
          Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have hfour :
          Real.sqrt ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 2 := by
        rw [show 4 = 2 * 2 by norm_num, pow_mul, hsquare]
      field_simp [hs]
      rw [hfour]
      ring
    · ring
  have h := hfirst.sub hsecond'
  convert h using 1
  · funext n
    unfold thirdBaseRelativeAmplitude
    ring
  · ring

theorem tendsto_publishedThirdBaseRelativeCoefficient_signed_div_sqrt :
    Tendsto
      (fun n : ℕ =>
        ((-1 : ℝ) ^ n * publishedThirdBaseRelativeCoefficient n) /
          Real.sqrt ((n : ℝ) + 1))
      atTop
      (nhds (-2 * positiveEulerBoundaryAmplitude ^ 3)) := by
  apply tendsto_thirdBaseRelativeAmplitude_div_sqrt.congr'
  exact Filter.Eventually.of_forall fun n => by
    change thirdBaseRelativeAmplitude n / Real.sqrt ((n : ℝ) + 1) =
      ((-1 : ℝ) ^ n * publishedThirdBaseRelativeCoefficient n) /
        Real.sqrt ((n : ℝ) + 1)
    rw [publishedThirdBaseRelativeCoefficient_eq_signed]
    have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
    have hmul : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      simpa [pow_two] using hs
    have hcancel :
        (-1 : ℝ) ^ n *
            ((-1 : ℝ) ^ n * thirdBaseRelativeAmplitude n) =
          thirdBaseRelativeAmplitude n := by
      calc
        _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
            thirdBaseRelativeAmplitude n := by ring
        _ = _ := by rw [hmul, one_mul]
    rw [hcancel]

theorem thirdRadiusRemainderAmplitude_eq (n : ℕ) :
    thirdRadiusRemainderAmplitude n =
      semilocalArchimedeanJacobiCoefficient n *
          thirdBaseRelativeAmplitude n / 2 +
        positiveEulerRadiusJet n *
          jacobiRadiusSecondCoefficient n /
            semilocalArchimedeanJacobiCoefficient n := by
  unfold thirdRadiusRemainderAmplitude jacobiRadiusThirdCoefficient
    squaredJacobiRadiusThirdCoefficient
    squaredJacobiRadiusThirdRelativeCoefficient
    thirdRadiusDominantAmplitude
  rw [archimedeanSquaredRadius_eq_coefficient_sq,
    publishedThirdBaseRelativeCoefficient_eq_signed,
    publishedThirdAdditionalRelativeCoefficient_eq_signed,
    jacobiRadiusJet_eq_signed_positive]
  have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  have hr := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
  have hpow2 : (-1 : ℝ) ^ (n * 2) = 1 := by
    rw [mul_comm, pow_mul]
    norm_num
  field_simp [hr]
  rw [pow_succ]
  ring_nf
  rw [hpow2]
  ring

theorem tendsto_thirdRadiusRemainderAmplitude :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusRemainderAmplitude n /
          thirdRadiusRemainderScale n)
      atTop (nhds (-positiveEulerBoundaryAmplitude ^ 3)) := by
  have hr := tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have hb := tendsto_thirdBaseRelativeAmplitude_div_sqrt
  have hmain := (hr.mul hb).div_const 2
  have hu := tendsto_positiveEulerRadiusJet_div_sqrt_succ
  have hv := tendsto_jacobiRadiusSecondCoefficient
  have hinvr :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) /
            semilocalArchimedeanJacobiCoefficient n)
        atTop (nhds 1) := by
    simpa [inv_div] using hr.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hsmall :=
    (((hu.mul hv).mul hinvr).mul (tendsto_succ_inv_zero.pow 2))
  have hsmall' :
      Tendsto
        (fun n : ℕ =>
          (positiveEulerRadiusJet n *
              jacobiRadiusSecondCoefficient n /
                semilocalArchimedeanJacobiCoefficient n) /
            thirdRadiusRemainderScale n)
        atTop (nhds 0) := by
    convert hsmall using 1
    · funext n
      unfold thirdRadiusRemainderScale
      have hx : (n : ℝ) + 1 ≠ 0 := by positivity
      have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
      have hrn := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
      field_simp [hx, hs, hrn]
    · ring
  have h := hmain.add hsmall'
  convert h using 1
  · funext n
    rw [thirdRadiusRemainderAmplitude_eq]
    unfold thirdRadiusRemainderScale
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hx, hs]
  · ring

theorem tendsto_thirdRadiusDominantAmplitude :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusDominantAmplitude n / thirdRadiusScale n)
      atTop (nhds thirdRadiusBoundaryAmplitude) := by
  have hr := tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have ht := tendsto_sqrt_succ_mul_positiveSemilocalFirstEulerAtom
  have hp := tendsto_thirdAdditionalPolynomialAmplitude_div_sq
  have h := ((hr.mul ht).mul hp).div_const 2
  convert h using 1
  · funext n
    unfold thirdRadiusDominantAmplitude thirdRadiusScale
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    have hsquare :
        Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    field_simp [hx, hs]
    rw [hsquare]
  · unfold thirdRadiusBoundaryAmplitude
    ring

theorem tendsto_jacobiRadiusThirdCoefficient_signed :
    Tendsto
      (fun n : ℕ =>
        ((-1 : ℝ) ^ n * jacobiRadiusThirdCoefficient n) /
          thirdRadiusScale n)
      atTop (nhds thirdRadiusBoundaryAmplitude) := by
  have hdom := tendsto_thirdRadiusDominantAmplitude
  have hrem := tendsto_thirdRadiusRemainderAmplitude
  have hratio :
      Tendsto
        (fun n : ℕ =>
          thirdRadiusRemainderScale n / thirdRadiusScale n)
        atTop (nhds 0) := by
    convert tendsto_succ_inv_zero using 1
    funext n
    unfold thirdRadiusRemainderScale thirdRadiusScale
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hx, hs]
  have hsmall := hrem.mul hratio
  have h := hdom.add hsmall
  convert h using 1
  · funext n
    unfold thirdRadiusRemainderAmplitude
    have hscl : thirdRadiusScale n ≠ 0 := by
      unfold thirdRadiusScale
      positivity
    have hrscl : thirdRadiusRemainderScale n ≠ 0 := by
      unfold thirdRadiusRemainderScale
      positivity
    field_simp [hscl, hrscl]
    ring
  · ring

theorem tendsto_squaredJacobiRadiusThirdCoefficient_signed :
    Tendsto
      (fun n : ℕ =>
        ((-1 : ℝ) ^ n * squaredJacobiRadiusThirdCoefficient n) /
          thirdSquaredRadiusScale n)
      atTop (nhds (16 * positiveEulerBoundaryAmplitude)) := by
  have hbase :=
    tendsto_publishedThirdBaseRelativeCoefficient_signed_div_sqrt.mul
      tendsto_succ_inv_zero
  have hadd := tendsto_publishedThirdAdditionalRelativeCoefficient_signed
  have hrel := hbase.add hadd
  have hr := tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have h := (hr.pow 2).mul hrel
  convert h using 1
  · funext n
    unfold squaredJacobiRadiusThirdCoefficient
      squaredJacobiRadiusThirdRelativeCoefficient thirdSquaredRadiusScale
      thirdRelativeScale
    rw [archimedeanSquaredRadius_eq_coefficient_sq]
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hx, hs]
  · ring

theorem positiveSemilocalFirstEulerAtom_succ (n : ℕ) :
    positiveSemilocalFirstEulerAtom (n + 1) =
      positiveSemilocalFirstEulerAtom n * centralBinomRatio n := by
  unfold positiveSemilocalFirstEulerAtom
  rw [normalizedCentralBinom_succ_eq_ratio]
  ring

theorem thirdAdditionalPolynomialAmplitude_pos (n : ℕ) :
    0 < thirdAdditionalPolynomialAmplitude n := by
  unfold thirdAdditionalPolynomialAmplitude
  positivity

theorem positiveSemilocalFirstEulerAtom_pos (n : ℕ) :
    0 < positiveSemilocalFirstEulerAtom n := by
  unfold positiveSemilocalFirstEulerAtom normalizedCentralBinom
  exact mul_pos
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
    (div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity))

theorem thirdRadiusDominantAmplitude_pos (n : ℕ) :
    0 < thirdRadiusDominantAmplitude n := by
  unfold thirdRadiusDominantAmplitude
  exact div_pos
    (mul_pos
      (mul_pos (semilocalArchimedeanJacobiCoefficient_pos n)
        (positiveSemilocalFirstEulerAtom_pos n))
      (thirdAdditionalPolynomialAmplitude_pos n))
    (by norm_num)

private theorem tendsto_radius_shift_two_ratio :
    Tendsto
      (fun n : ℕ =>
        semilocalArchimedeanJacobiCoefficient (n + 2) /
          semilocalArchimedeanJacobiCoefficient n)
      atTop (nhds 1) := by
  have hleft :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (Filter.tendsto_add_atTop_nat 2)
  have hmiddle :
      Tendsto
        (fun n : ℕ => ((n : ℝ) + 3) / ((n : ℝ) + 1))
        atTop (nhds 1) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (3 : ℝ) 1 1 (by norm_num : (1 : ℝ) ≠ 0)) using 1
    · funext n
      ring
    · norm_num
  have hright :
      Tendsto
        (fun n : ℕ =>
          ((n : ℝ) + 1) /
            semilocalArchimedeanJacobiCoefficient n)
        atTop (nhds 1) := by
    simpa [inv_div] using
      tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.inv₀
        (by norm_num : (1 : ℝ) ≠ 0)
  have h := (hleft.mul hmiddle).mul hright
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    have h0 := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
    have h2 := (semilocalArchimedeanJacobiCoefficient_pos (n + 2)).ne'
    have hx1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hx3 : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [h0, h2, hx1, hx3]
    push_cast
    ring
  · norm_num

private theorem tendsto_radius_shift_two_ratio_firstOrder :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (semilocalArchimedeanJacobiCoefficient (n + 2) /
              semilocalArchimedeanJacobiCoefficient n - 1))
      atTop (nhds 2) := by
  let ratio := fun n : ℕ =>
    semilocalArchimedeanJacobiCoefficient (n + 2) /
      semilocalArchimedeanJacobiCoefficient n
  have hsquare :
      Tendsto
        (fun n : ℕ => ((n : ℝ) + 1) * (ratio n ^ 2 - 1))
        atTop (nhds 4) := by
    have hrat :
        Tendsto
          (fun n : ℕ =>
            (4 * (n : ℝ) + 7) / ((n : ℝ) + 1 / 2))
          atTop (nhds 4) := by
      convert
        (tendsto_add_mul_div_add_mul_atTop_nhds
          (7 : ℝ) (1 / 2 : ℝ) 4
            (by norm_num : (1 : ℝ) ≠ 0)) using 1
      · funext n
        ring
      · norm_num
    apply hrat.congr'
    exact Filter.Eventually.of_forall fun n => by
      change (4 * (n : ℝ) + 7) / ((n : ℝ) + 1 / 2) =
        ((n : ℝ) + 1) *
          ((semilocalArchimedeanJacobiCoefficient (n + 2) /
              semilocalArchimedeanJacobiCoefficient n) ^ 2 - 1)
      rw [div_pow,
        semilocalArchimedeanJacobiCoefficient_sq,
        semilocalArchimedeanJacobiCoefficient_sq]
      push_cast
      have hr := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
      have hx : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
      field_simp [hr, hx]
      ring
  have hden :=
    tendsto_radius_shift_two_ratio.add_const 1
  have h := hsquare.div hden (by norm_num)
  convert h using 1
  · funext n
    change ((n : ℝ) + 1) *
        (ratio n - 1) =
      (((n : ℝ) + 1) * (ratio n ^ 2 - 1)) /
        (semilocalArchimedeanJacobiCoefficient (n + 2) /
            semilocalArchimedeanJacobiCoefficient n + 1)
    unfold ratio
    have h0 := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
    have hsum :
        semilocalArchimedeanJacobiCoefficient (n + 2) +
            semilocalArchimedeanJacobiCoefficient n ≠ 0 :=
      (add_pos
        (semilocalArchimedeanJacobiCoefficient_pos (n + 2))
        (semilocalArchimedeanJacobiCoefficient_pos n)).ne'
    field_simp [h0, hsum]
    ring
  · norm_num

private theorem tendsto_centralBinom_twoStepRatio_firstOrder :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (centralBinomRatio n * centralBinomRatio (n + 1) - 1))
      atTop (nhds (-1)) := by
  have h :
      Tendsto
        (fun n : ℕ =>
          -(4 * (n : ℝ) + 5) / (4 * (n : ℝ) + 8))
        atTop (nhds (-1)) := by
    have hrat :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (5 : ℝ) 8 4 (by norm_num : (4 : ℝ) ≠ 0)
    convert hrat.neg using 1
    · funext n
      ring
    · norm_num
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by
    unfold centralBinomRatio
    push_cast
    have h2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    have h4 : 2 * (n : ℝ) + 4 ≠ 0 := by positivity
    field_simp [h2, h4]
    ring

private theorem tendsto_thirdAdditionalPolynomialAmplitude_shiftDifference :
    Tendsto
      (fun n : ℕ =>
        (thirdAdditionalPolynomialAmplitude (n + 2) -
            thirdAdditionalPolynomialAmplitude n) /
          ((n : ℝ) + 1))
      atTop (nhds 64) := by
  have hi := tendsto_succ_inv_zero
  have hi2 :
      Tendsto (fun n : ℕ => (((n : ℝ) + 3)⁻¹))
        atTop (nhds 0) := by
    have hx : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (nhds 3))
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hx
  have h64 : Tendsto (fun _ : ℕ => (64 : ℝ)) atTop (nhds 64) :=
    tendsto_const_nhds
  have h := (h64.add (hi.const_mul 40)).add
    (((hi2.sub hi).mul hi).const_mul (1 / 4 : ℝ))
  convert h using 1
  · funext n
    unfold thirdAdditionalPolynomialAmplitude
    push_cast
    have hx1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hx3 : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hx1, hx3]
    ring
  · ring

private theorem tendsto_thirdAdditionalPolynomialAmplitude_twoStepRatio_firstOrder :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (thirdAdditionalPolynomialAmplitude (n + 2) /
              thirdAdditionalPolynomialAmplitude n - 1))
      atTop (nhds 4) := by
  have hdiff :=
    tendsto_thirdAdditionalPolynomialAmplitude_shiftDifference
  have hden := tendsto_thirdAdditionalPolynomialAmplitude_div_sq
  have h := hdiff.div hden (by norm_num)
  convert h using 1
  · funext n
    change ((n : ℝ) + 1) *
        (thirdAdditionalPolynomialAmplitude (n + 2) /
            thirdAdditionalPolynomialAmplitude n - 1) =
      ((thirdAdditionalPolynomialAmplitude (n + 2) -
          thirdAdditionalPolynomialAmplitude n) / ((n : ℝ) + 1)) /
        (thirdAdditionalPolynomialAmplitude n / ((n : ℝ) + 1) ^ 2)
    have hp := (thirdAdditionalPolynomialAmplitude_pos n).ne'
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hp, hx]
  · norm_num

private theorem tendsto_thirdAdditionalPolynomialAmplitude_twoStepRatio :
    Tendsto
      (fun n : ℕ =>
        thirdAdditionalPolynomialAmplitude (n + 2) /
          thirdAdditionalPolynomialAmplitude n)
      atTop (nhds 1) := by
  have h :=
    tendsto_thirdAdditionalPolynomialAmplitude_twoStepRatio_firstOrder.mul
      tendsto_succ_inv_zero
  have h' := h.add_const 1
  convert h' using 1
  · funext n
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hx]
    ring
  · ring

private theorem thirdRadiusDominantAmplitude_twoStepRatio (n : ℕ) :
    thirdRadiusDominantAmplitude (n + 2) /
        thirdRadiusDominantAmplitude n =
      (semilocalArchimedeanJacobiCoefficient (n + 2) /
          semilocalArchimedeanJacobiCoefficient n) *
        (centralBinomRatio n * centralBinomRatio (n + 1)) *
        (thirdAdditionalPolynomialAmplitude (n + 2) /
          thirdAdditionalPolynomialAmplitude n) := by
  unfold thirdRadiusDominantAmplitude
  rw [show n + 2 = (n + 1) + 1 by omega,
    positiveSemilocalFirstEulerAtom_succ,
    positiveSemilocalFirstEulerAtom_succ]
  have h0 := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
  have hpp : positiveSemilocalFirstEulerAtom n ≠ 0 := by
    exact (positiveSemilocalFirstEulerAtom_pos n).ne'
  have hd := (thirdAdditionalPolynomialAmplitude_pos n).ne'
  field_simp [h0, hpp, hd]

private theorem tendsto_thirdRadiusDominantAmplitude_twoStepRatio :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusDominantAmplitude (n + 2) /
          thirdRadiusDominantAmplitude n)
      atTop (nhds 1) := by
  have hr := tendsto_radius_shift_two_ratio
  have hc :=
    tendsto_centralBinomRatio.mul
      (tendsto_centralBinomRatio.comp
        (Filter.tendsto_add_atTop_nat 1))
  have hp :=
    tendsto_thirdAdditionalPolynomialAmplitude_twoStepRatio
  have h := (hr.mul hc).mul hp
  convert h using 1
  · funext n
    exact thirdRadiusDominantAmplitude_twoStepRatio n
  · norm_num

private theorem tendsto_thirdRadiusDominantAmplitude_ratio_firstOrder :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (thirdRadiusDominantAmplitude (n + 2) /
              thirdRadiusDominantAmplitude n - 1))
      atTop (nhds 5) := by
  have ha := tendsto_radius_shift_two_ratio
  have hb := tendsto_centralBinomRatio.mul
    (tendsto_centralBinomRatio.comp
      (Filter.tendsto_add_atTop_nat 1))
  have hc :=
    tendsto_thirdAdditionalPolynomialAmplitude_twoStepRatio
  have ha1 := tendsto_radius_shift_two_ratio_firstOrder
  have hb1 := tendsto_centralBinom_twoStepRatio_firstOrder
  have hc1 :=
    tendsto_thirdAdditionalPolynomialAmplitude_twoStepRatio_firstOrder
  have h :=
    (((ha1.mul hb).mul hc).add (hb1.mul hc)).add hc1
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    rw [thirdRadiusDominantAmplitude_twoStepRatio]
    ring
  · norm_num

theorem tendsto_thirdRadiusDominantAmplitude_twoStepDifference :
    Tendsto
      (fun n : ℕ =>
        (thirdRadiusDominantAmplitude n -
            thirdRadiusDominantAmplitude (n + 2)) /
          thirdRadiusRemainderScale n)
      atTop (nhds (-5 * thirdRadiusBoundaryAmplitude)) := by
  have hmain := tendsto_thirdRadiusDominantAmplitude
  have hratio :=
    tendsto_thirdRadiusDominantAmplitude_ratio_firstOrder
  have h := hmain.mul hratio.neg
  convert h using 1
  · funext n
    have hf := (thirdRadiusDominantAmplitude_pos n).ne'
    unfold thirdRadiusScale thirdRadiusRemainderScale
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hf, hx, hs]
    ring
  · ring

private theorem tendsto_criticalBoundaryDegree_add (j : ℕ) :
    Tendsto (fun n : ℕ => criticalBoundaryDegree n + j) atTop atTop :=
  (Filter.tendsto_add_atTop_nat j).comp tendsto_criticalBoundaryDegree

private theorem tendsto_boundarySuccShiftRatio (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1) /
          ((criticalBoundaryDegree n : ℝ) + 1)))
      atTop (nhds 1) := by
  convert
    (tendsto_add_mul_div_add_mul_atTop_nhds
      ((j : ℝ) + 3) 3 2 (by norm_num : (2 : ℝ) ≠ 0)) using 1
  · funext n
    unfold criticalBoundaryDegree
    push_cast
    ring
  · norm_num

private theorem tendsto_thirdRadiusScale_shiftRatio (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusScale (criticalBoundaryDegree n + j) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds 1) := by
  have hlin := tendsto_boundarySuccShiftRatio j
  have hsqrt := hlin.sqrt
  have h := (hlin.pow 2).mul hsqrt
  convert h using 1
  · funext n
    unfold thirdRadiusScale
    have hbase : (criticalBoundaryDegree n : ℝ) + 1 ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    have hshift :
        ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    rw [Real.sqrt_div (by positivity :
      0 ≤ ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1)]
    field_simp [hbase, hshift]
  · norm_num

private theorem tendsto_thirdRadiusRemainderScale_shiftRatio (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusRemainderScale (criticalBoundaryDegree n + j) /
          thirdRadiusRemainderScale (criticalBoundaryDegree n))
      atTop (nhds 1) := by
  have hlin := tendsto_boundarySuccShiftRatio j
  have hsqrt := hlin.sqrt
  have h := hlin.mul hsqrt
  convert h using 1
  · funext n
    unfold thirdRadiusRemainderScale
    have hbase : (criticalBoundaryDegree n : ℝ) + 1 ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    have hshift :
        ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    rw [Real.sqrt_div (by positivity :
      0 ≤ ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1)]
    field_simp [hbase, hshift]
  · norm_num

private theorem tendsto_radius_boundaryShift_div_succ (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + j) /
          ((criticalBoundaryDegree n : ℝ) + 1))
      atTop (nhds 1) := by
  have hr :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (tendsto_criticalBoundaryDegree_add j)
  have hshift := tendsto_boundarySuccShiftRatio j
  have h := hr.mul hshift
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    have hbase : (criticalBoundaryDegree n : ℝ) + 1 ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    have hshift' :
        ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hbase, hshift']
  · norm_num

private theorem tendsto_dominant_boundaryShift_div_scale (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusDominantAmplitude (criticalBoundaryDegree n + j) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds thirdRadiusBoundaryAmplitude) := by
  have hmain :=
    tendsto_thirdRadiusDominantAmplitude.comp
      (tendsto_criticalBoundaryDegree_add j)
  have hshift := tendsto_thirdRadiusScale_shiftRatio j
  have h := hmain.mul hshift
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    have hbase :
        thirdRadiusScale (criticalBoundaryDegree n) ≠ 0 := by
      unfold thirdRadiusScale criticalBoundaryDegree
      positivity
    have hshift' :
        thirdRadiusScale (criticalBoundaryDegree n + j) ≠ 0 := by
      unfold thirdRadiusScale
      positivity
    field_simp [hbase, hshift']
  · ring

private theorem tendsto_remainder_boundaryShift_div_scale (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusRemainderAmplitude (criticalBoundaryDegree n + j) /
          thirdRadiusRemainderScale (criticalBoundaryDegree n))
      atTop (nhds (-positiveEulerBoundaryAmplitude ^ 3)) := by
  have hmain :=
    tendsto_thirdRadiusRemainderAmplitude.comp
      (tendsto_criticalBoundaryDegree_add j)
  have hshift := tendsto_thirdRadiusRemainderScale_shiftRatio j
  have h := hmain.mul hshift
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    have hbase :
        thirdRadiusRemainderScale (criticalBoundaryDegree n) ≠ 0 := by
      unfold thirdRadiusRemainderScale criticalBoundaryDegree
      positivity
    have hshift' :
        thirdRadiusRemainderScale (criticalBoundaryDegree n + j) ≠ 0 := by
      unfold thirdRadiusRemainderScale
      positivity
    field_simp [hbase, hshift']
  · ring

private theorem tendsto_dominant_twoStepDifference_boundaryShift (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (thirdRadiusDominantAmplitude (criticalBoundaryDegree n + j) -
            thirdRadiusDominantAmplitude
              (criticalBoundaryDegree n + j + 2)) /
          thirdRadiusRemainderScale (criticalBoundaryDegree n))
      atTop (nhds (-5 * thirdRadiusBoundaryAmplitude)) := by
  have hmain :=
    tendsto_thirdRadiusDominantAmplitude_twoStepDifference.comp
      (tendsto_criticalBoundaryDegree_add j)
  have hshift := tendsto_thirdRadiusRemainderScale_shiftRatio j
  have h := hmain.mul hshift
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    have hbase :
        thirdRadiusRemainderScale (criticalBoundaryDegree n) ≠ 0 := by
      unfold thirdRadiusRemainderScale criticalBoundaryDegree
      positivity
    have hshift' :
        thirdRadiusRemainderScale (criticalBoundaryDegree n + j) ≠ 0 := by
      unfold thirdRadiusRemainderScale
      positivity
    field_simp [hbase, hshift']
  · ring

private theorem tendsto_radius_increment :
    Tendsto
      (fun n : ℕ =>
        semilocalArchimedeanJacobiCoefficient (n + 1) -
          semilocalArchimedeanJacobiCoefficient n)
      atTop (nhds 1) := by
  have hnum :
      Tendsto
        (fun n : ℕ =>
          (2 * (n : ℝ) + 5 / 2) / ((n : ℝ) + 1))
        atTop (nhds 2) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (5 / 2 : ℝ) 1 2 (by norm_num : (1 : ℝ) ≠ 0)) using 1
    · funext n
      ring
    · norm_num
  have hr0 :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ
  have hr1raw :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hshift :
      Tendsto
        (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1))
        atTop (nhds 1) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (2 : ℝ) 1 1 (by norm_num : (1 : ℝ) ≠ 0)) using 1
    · funext n
      ring
    · norm_num
  have hr1product := hr1raw.mul hshift
  have hr1 :
      Tendsto
        (fun n : ℕ =>
          semilocalArchimedeanJacobiCoefficient (n + 1) /
            ((n : ℝ) + 1))
        atTop (nhds 1) := by
    convert hr1product using 1
    · funext n
      simp only [Function.comp_apply]
      have hx1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hx2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hx1, hx2]
      push_cast
      ring
    · norm_num
  have hden := hr1.add hr0
  have h := hnum.div hden (by norm_num)
  convert h using 1
  · funext n
    change
      semilocalArchimedeanJacobiCoefficient (n + 1) -
          semilocalArchimedeanJacobiCoefficient n =
        ((2 * (n : ℝ) + 5 / 2) / ((n : ℝ) + 1)) /
          (semilocalArchimedeanJacobiCoefficient (n + 1) /
              ((n : ℝ) + 1) +
            semilocalArchimedeanJacobiCoefficient n /
              ((n : ℝ) + 1))
    have h0 := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
    have h1 := (semilocalArchimedeanJacobiCoefficient_pos (n + 1)).ne'
    have hsum :
        semilocalArchimedeanJacobiCoefficient (n + 1) +
            semilocalArchimedeanJacobiCoefficient n ≠ 0 :=
      (add_pos
        (semilocalArchimedeanJacobiCoefficient_pos (n + 1))
        (semilocalArchimedeanJacobiCoefficient_pos n)).ne'
    have hx : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [show
      semilocalArchimedeanJacobiCoefficient (n + 1) -
          semilocalArchimedeanJacobiCoefficient n =
        (semilocalArchimedeanJacobiCoefficient (n + 1) ^ 2 -
            semilocalArchimedeanJacobiCoefficient n ^ 2) /
          (semilocalArchimedeanJacobiCoefficient (n + 1) +
            semilocalArchimedeanJacobiCoefficient n) by
              field_simp [hsum]
              ring]
    rw [semilocalArchimedeanJacobiCoefficient_sq,
      semilocalArchimedeanJacobiCoefficient_sq]
    push_cast
    field_simp [h0, h1, hsum, hx]
    ring
  · norm_num

private theorem tendsto_radiusSecondDifference_boundary
    (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + j + 1) -
          semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + j)) -
        (semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + j + 2) -
          semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + j + 1)))
      atTop (nhds 0) := by
  have h0 :=
    tendsto_radius_increment.comp
      (tendsto_criticalBoundaryDegree_add j)
  have h1 :=
    tendsto_radius_increment.comp
      (tendsto_criticalBoundaryDegree_add (j + 1))
  have h := h0.sub h1
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    congr 2
  · norm_num

/-- Alternating-sign form of the third-radius linear critical stencil. -/
def alternatingThirdLinearStencil (h : ℕ → ℝ) (m : ℕ) : ℝ :=
  let r := semilocalArchimedeanJacobiCoefficient
  h m * r (m + 1) - r m * h (m + 1) +
    2 * r (m + 1) * h (m + 1) -
    2 * r (m + 2) * h (m + 2) +
    h (m + 2) * r (m + 3) - r (m + 2) * h (m + 3)

theorem criticalResidualThirdLinearCoefficient_eq_stencil (n : ℕ) :
    criticalResidualThirdLinearCoefficient (n + 1) =
      alternatingThirdLinearStencil
        (fun k =>
          thirdRadiusDominantAmplitude k +
            thirdRadiusRemainderAmplitude k)
        (criticalBoundaryDegree n) := by
  unfold criticalResidualThirdLinearCoefficient
    alternatingThirdLinearStencil criticalBoundaryDegree
  dsimp only
  rw [jacobiRadiusThirdCoefficient_eq_signed_amplitudes,
    jacobiRadiusThirdCoefficient_eq_signed_amplitudes,
    jacobiRadiusThirdCoefficient_eq_signed_amplitudes,
    jacobiRadiusThirdCoefficient_eq_signed_amplitudes]
  norm_num [pow_add, pow_mul]
  ring

theorem alternatingThirdLinearStencil_add
    (f g : ℕ → ℝ) (m : ℕ) :
    alternatingThirdLinearStencil (fun n => f n + g n) m =
      alternatingThirdLinearStencil f m +
        alternatingThirdLinearStencil g m := by
  unfold alternatingThirdLinearStencil
  dsimp only
  ring

theorem alternatingThirdLinearStencil_eq_twoStepDifferences
    (h : ℕ → ℝ) (m : ℕ) :
    alternatingThirdLinearStencil h m =
      semilocalArchimedeanJacobiCoefficient (m + 1) *
          (h m - h (m + 2)) +
        semilocalArchimedeanJacobiCoefficient (m + 2) *
          (h (m + 1) - h (m + 3)) +
        (2 * semilocalArchimedeanJacobiCoefficient (m + 1) -
            semilocalArchimedeanJacobiCoefficient m -
            semilocalArchimedeanJacobiCoefficient (m + 2)) *
          h (m + 1) +
        (semilocalArchimedeanJacobiCoefficient (m + 1) -
            2 * semilocalArchimedeanJacobiCoefficient (m + 2) +
            semilocalArchimedeanJacobiCoefficient (m + 3)) *
          h (m + 2) := by
  unfold alternatingThirdLinearStencil
  dsimp only
  ring

private theorem
    tendsto_dominantDifference_mul_radius_boundaryShift_div_scale
    (j k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + k) *
          (thirdRadiusDominantAmplitude (criticalBoundaryDegree n + j) -
            thirdRadiusDominantAmplitude
              (criticalBoundaryDegree n + j + 2)) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds (-5 * thirdRadiusBoundaryAmplitude)) := by
  have hr := tendsto_radius_boundaryShift_div_succ k
  have hd := tendsto_dominant_twoStepDifference_boundaryShift j
  have h := hr.mul hd
  convert h using 1
  · funext n
    have hs :
        thirdRadiusRemainderScale (criticalBoundaryDegree n) ≠ 0 := by
      unfold thirdRadiusRemainderScale criticalBoundaryDegree
      positivity
    have hx : (criticalBoundaryDegree n : ℝ) + 1 ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    unfold thirdRadiusScale thirdRadiusRemainderScale
    field_simp [hs, hx]
  · ring

private theorem
    tendsto_radiusSecondDifference_mul_dominant_boundaryShift_div_scale
    (j k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((semilocalArchimedeanJacobiCoefficient
              (criticalBoundaryDegree n + j + 1) -
            semilocalArchimedeanJacobiCoefficient
              (criticalBoundaryDegree n + j)) -
          (semilocalArchimedeanJacobiCoefficient
              (criticalBoundaryDegree n + j + 2) -
            semilocalArchimedeanJacobiCoefficient
              (criticalBoundaryDegree n + j + 1))) *
          thirdRadiusDominantAmplitude
            (criticalBoundaryDegree n + k) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds 0) := by
  have hc := tendsto_radiusSecondDifference_boundary j
  have hf := tendsto_dominant_boundaryShift_div_scale k
  have h := hc.mul hf
  convert h using 1
  · funext n
    ring
  · ring

theorem tendsto_alternatingThirdLinearStencil_dominant :
    Tendsto
      (fun n : ℕ =>
        alternatingThirdLinearStencil thirdRadiusDominantAmplitude
            (criticalBoundaryDegree n) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds (-10 * thirdRadiusBoundaryAmplitude)) := by
  have h0 :=
    tendsto_dominantDifference_mul_radius_boundaryShift_div_scale 0 1
  have h1 :=
    tendsto_dominantDifference_mul_radius_boundaryShift_div_scale 1 2
  have hc0 :=
    tendsto_radiusSecondDifference_mul_dominant_boundaryShift_div_scale 0 1
  have hc1 :=
    (tendsto_radiusSecondDifference_mul_dominant_boundaryShift_div_scale 1 2).neg
  have h := ((h0.add h1).add hc0).add hc1
  convert h using 1
  · funext n
    rw [alternatingThirdLinearStencil_eq_twoStepDifferences]
    ring
  · ring

private theorem tendsto_remainder_mul_radius_boundaryShift_div_scale
    (j k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        thirdRadiusRemainderAmplitude (criticalBoundaryDegree n + j) *
          semilocalArchimedeanJacobiCoefficient
            (criticalBoundaryDegree n + k) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds (-positiveEulerBoundaryAmplitude ^ 3)) := by
  have hg := tendsto_remainder_boundaryShift_div_scale j
  have hr := tendsto_radius_boundaryShift_div_succ k
  have h := hg.mul hr
  convert h using 1
  · funext n
    unfold thirdRadiusScale thirdRadiusRemainderScale
    have hx : (criticalBoundaryDegree n : ℝ) + 1 ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    have hs : Real.sqrt ((criticalBoundaryDegree n : ℝ) + 1) ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    field_simp [hx, hs]
  · ring

theorem tendsto_alternatingThirdLinearStencil_remainder :
    Tendsto
      (fun n : ℕ =>
        alternatingThirdLinearStencil thirdRadiusRemainderAmplitude
            (criticalBoundaryDegree n) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds 0) := by
  have h01 :=
    tendsto_remainder_mul_radius_boundaryShift_div_scale 0 1
  have h10 :=
    tendsto_remainder_mul_radius_boundaryShift_div_scale 1 0
  have h11 :=
    tendsto_remainder_mul_radius_boundaryShift_div_scale 1 1
  have h22 :=
    tendsto_remainder_mul_radius_boundaryShift_div_scale 2 2
  have h23 :=
    tendsto_remainder_mul_radius_boundaryShift_div_scale 2 3
  have h32 :=
    tendsto_remainder_mul_radius_boundaryShift_div_scale 3 2
  have h :=
    (((((h01.sub h10).add (h11.const_mul 2)).sub
      (h22.const_mul 2)).add h23).sub h32)
  convert h using 1
  · funext n
    unfold alternatingThirdLinearStencil
    dsimp only
    ring
  · ring

theorem tendsto_criticalResidualThirdLinearCoefficient :
    Tendsto
      (fun n : ℕ =>
        criticalResidualThirdLinearCoefficient (n + 1) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds (-10 * thirdRadiusBoundaryAmplitude)) := by
  have h :=
    tendsto_alternatingThirdLinearStencil_dominant.add
      tendsto_alternatingThirdLinearStencil_remainder
  convert h using 1
  · funext n
    rw [criticalResidualThirdLinearCoefficient_eq_stencil,
      alternatingThirdLinearStencil_add]
    ring
  · ring

private theorem tendsto_positiveEulerRadiusJet_boundaryShift_div_sqrtSucc
    (j : ℕ) :
    Tendsto
      (fun n : ℕ =>
        positiveEulerRadiusJet (criticalBoundaryDegree n + j) /
          Real.sqrt ((criticalBoundaryDegree n : ℝ) + 1))
      atTop (nhds positiveEulerBoundaryAmplitude) := by
  have hu :=
    tendsto_positiveEulerRadiusJet_div_sqrt_succ.comp
      (tendsto_criticalBoundaryDegree_add j)
  have hratio := (tendsto_boundarySuccShiftRatio j).sqrt
  have h := hu.mul hratio
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    have hbase :
        Real.sqrt ((criticalBoundaryDegree n : ℝ) + 1) ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    have hshift :
        Real.sqrt (((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1) ≠ 0 := by
      positivity
    rw [Real.sqrt_div (by positivity :
      0 ≤ ((criticalBoundaryDegree n + j : ℕ) : ℝ) + 1)]
    field_simp [hbase, hshift]
  · norm_num

private theorem tendsto_boundarySucc_inv_sq_zero :
    Tendsto
      (fun n : ℕ =>
        (((criticalBoundaryDegree n : ℝ) + 1)⁻¹) ^ 2)
      atTop (nhds 0) := by
  have hx :
      Tendsto
        (fun n : ℕ => (criticalBoundaryDegree n : ℝ) + 1)
        atTop atTop :=
    (tendsto_natCast_atTop_iff.2 tendsto_criticalBoundaryDegree).atTop_add
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  have hi :
      Tendsto
        (fun n : ℕ => ((criticalBoundaryDegree n : ℝ) + 1)⁻¹)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp hx
  simpa using hi.pow 2

private theorem
    tendsto_positiveEulerRadiusJet_mul_second_boundaryShift_div_thirdScale
    (j k : ℕ) :
    Tendsto
      (fun n : ℕ =>
        positiveEulerRadiusJet (criticalBoundaryDegree n + j) *
          jacobiRadiusSecondCoefficient (criticalBoundaryDegree n + k) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds 0) := by
  have hu :=
    tendsto_positiveEulerRadiusJet_boundaryShift_div_sqrtSucc j
  have hv :=
    tendsto_jacobiRadiusSecondCoefficient.comp
      (tendsto_criticalBoundaryDegree_add k)
  have hi := tendsto_boundarySucc_inv_sq_zero
  have h := (hu.mul hv).mul hi
  convert h using 1
  · funext n
    simp only [Function.comp_apply]
    unfold thirdRadiusScale
    have hx : (criticalBoundaryDegree n : ℝ) + 1 ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    have hs : Real.sqrt ((criticalBoundaryDegree n : ℝ) + 1) ≠ 0 := by
      unfold criticalBoundaryDegree
      positivity
    field_simp [hx, hs]
  · ring

theorem criticalResidualFirstSecondMixedCoefficient_eq_amplitudes
    (n : ℕ) :
    criticalResidualFirstSecondMixedCoefficient (n + 1) =
      let m := criticalBoundaryDegree n
      let U := positiveEulerRadiusJet
      let v := jacobiRadiusSecondCoefficient
      v m * U (m + 1) - U m * v (m + 1) -
        2 * U (m + 1) * v (m + 1) +
        2 * U (m + 2) * v (m + 2) +
        v (m + 2) * U (m + 3) -
        U (m + 2) * v (m + 3) := by
  unfold criticalResidualFirstSecondMixedCoefficient criticalBoundaryDegree
  dsimp only
  rw [jacobiRadiusJet_even (n + 1),
    jacobiRadiusJet_odd (n + 1),
    show 2 * (n + 1) + 2 = 2 * (n + 2) by omega,
    show 2 * (n + 1) + 3 = 2 * (n + 2) + 1 by omega,
    jacobiRadiusJet_even (n + 2),
    jacobiRadiusJet_odd (n + 2)]
  ring

theorem tendsto_criticalResidualFirstSecondMixedCoefficient :
    Tendsto
      (fun n : ℕ =>
        criticalResidualFirstSecondMixedCoefficient (n + 1) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds 0) := by
  have h10 :=
    tendsto_positiveEulerRadiusJet_mul_second_boundaryShift_div_thirdScale 1 0
  have h01 :=
    tendsto_positiveEulerRadiusJet_mul_second_boundaryShift_div_thirdScale 0 1
  have h11 :=
    tendsto_positiveEulerRadiusJet_mul_second_boundaryShift_div_thirdScale 1 1
  have h22 :=
    tendsto_positiveEulerRadiusJet_mul_second_boundaryShift_div_thirdScale 2 2
  have h32 :=
    tendsto_positiveEulerRadiusJet_mul_second_boundaryShift_div_thirdScale 3 2
  have h23 :=
    tendsto_positiveEulerRadiusJet_mul_second_boundaryShift_div_thirdScale 2 3
  have h :=
    (((((h10.sub h01).sub (h11.const_mul 2)).add
      (h22.const_mul 2)).add h32).sub h23)
  convert h using 1
  · funext n
    rw [criticalResidualFirstSecondMixedCoefficient_eq_amplitudes]
    ring
  · ring

/-- **Sharp third-Euler critical boundary law.**  The new `ℓ=1` source atom breaks the
order-one/order-two `p²` pattern: the `q³` critical coefficient grows like `n^(5/2)`. -/
theorem tendsto_criticalResidualThirdCoefficient :
    Tendsto
      (fun n : ℕ =>
        criticalResidualThirdCoefficient (n + 1) /
          thirdRadiusScale (criticalBoundaryDegree n))
      atTop (nhds (-10 * thirdRadiusBoundaryAmplitude)) := by
  have h :=
    tendsto_criticalResidualThirdLinearCoefficient.add
      tendsto_criticalResidualFirstSecondMixedCoefficient
  convert h using 1
  · funext n
    unfold criticalResidualThirdCoefficient
    ring
  · ring

theorem thirdCriticalBoundaryConstant :
    -10 * thirdRadiusBoundaryAmplitude =
      -160 * Real.sqrt 2 / Real.sqrt Real.pi := by
  unfold thirdRadiusBoundaryAmplitude positiveEulerBoundaryAmplitude
  ring

theorem thirdCriticalBoundaryConstant_eq_sqrt_div :
    -10 * thirdRadiusBoundaryAmplitude =
      -160 * Real.sqrt (2 / Real.pi) := by
  rw [thirdCriticalBoundaryConstant,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end RHTower.ThirdEulerCriticalJet
