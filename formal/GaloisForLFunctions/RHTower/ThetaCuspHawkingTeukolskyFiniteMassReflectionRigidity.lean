import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyThirdMassParityJet
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow

/-!
# Fixed-radius and event-horizon reflection rigidity of the Teukolsky parity gap

At fixed radius `u = 1`, the exact Birmingham--Mokhtari scalar/vector parity gap depends on the
shifted virtual angular parameter `A = Q + 2` through

`G(A,x) = 6x ((2+3x)A + 6x + 6x^2) / (A+3x)^2`.

For positive `A`, `B`, and mass coordinate `x`, its exact secant difference is

`G(A,x)-G(B,x) = 6x(B-A)H(A,B,x) / ((A+3x)^2(B+3x)^2)`,

where `H` is strictly positive.  This is an off-shell fixed-radius response: the finite-mass event
horizon satisfies `u = 1 + x`.  On that moving horizon the gap reduces to the Stieltjes atom

`G_H(A,x) = 6x(2+3x)/(A+3x)`.

Both responses are injective in `A`.
For a Xi divisor point with `a = Re rho`, the two reflected BM shifts are
`A = a(3-a)` and `B = (1-a)(2+a)`, so `B-A = 2(1-2a)`.  The resulting reflected parity defect
therefore vanishes exactly at critical-line incidence for every positive mass, and away from the
line has the same orientation as the first BM backreaction defect.

These are exact nonperturbative statements about the diagonal BM radial potential.  They do not
identify that potential difference with the total nonlinear Einstein `(++-)` cokernel section.

**[CORPUS-ORIGINAL] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Fixed-unit-radius parity gap as a function of shifted angular parameter `A = Q + 2`. -/
def d4FixedUnitRadiusFiniteMassParityProfile (A x : ℝ) : ℝ :=
  6 * x * ((2 + 3 * x) * A + 6 * x + 6 * x ^ 2) / (A + 3 * x) ^ 2

/-- Positive cross-numerator in exact secant difference of fixed-unit-radius profile. -/
def d4FixedUnitRadiusFiniteMassParityCrossNumerator (A B x : ℝ) : ℝ :=
  (2 + 3 * x) * A * B +
    6 * x * (1 + x) * (A + B) + 18 * x ^ 2 + 9 * x ^ 3

/-- Exact finite-mass secant factorization of fixed-unit-radius parity profile. -/
theorem d4FixedUnitRadiusFiniteMassParityProfile_sub_eq
    (A B x : ℝ) (hA : A + 3 * x ≠ 0) (hB : B + 3 * x ≠ 0) :
    d4FixedUnitRadiusFiniteMassParityProfile A x -
        d4FixedUnitRadiusFiniteMassParityProfile B x =
      6 * x * (B - A) * d4FixedUnitRadiusFiniteMassParityCrossNumerator A B x /
        ((A + 3 * x) ^ 2 * (B + 3 * x) ^ 2) := by
  have hA2 : (A + 3 * x) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hB2 : (B + 3 * x) ^ 2 ≠ 0 := pow_ne_zero 2 hB
  have hden : (A + 3 * x) ^ 2 * (B + 3 * x) ^ 2 ≠ 0 :=
    mul_ne_zero hA2 hB2
  have hprofileA :
      d4FixedUnitRadiusFiniteMassParityProfile A x * (A + 3 * x) ^ 2 =
        6 * x * ((2 + 3 * x) * A + 6 * x + 6 * x ^ 2) := by
    unfold d4FixedUnitRadiusFiniteMassParityProfile
    exact div_mul_cancel₀ _ hA2
  have hprofileB :
      d4FixedUnitRadiusFiniteMassParityProfile B x * (B + 3 * x) ^ 2 =
        6 * x * ((2 + 3 * x) * B + 6 * x + 6 * x ^ 2) := by
    unfold d4FixedUnitRadiusFiniteMassParityProfile
    exact div_mul_cancel₀ _ hB2
  apply (eq_div_iff hden).2
  calc
    (d4FixedUnitRadiusFiniteMassParityProfile A x -
          d4FixedUnitRadiusFiniteMassParityProfile B x) *
          ((A + 3 * x) ^ 2 * (B + 3 * x) ^ 2) =
        (d4FixedUnitRadiusFiniteMassParityProfile A x * (A + 3 * x) ^ 2) *
            (B + 3 * x) ^ 2 -
          (d4FixedUnitRadiusFiniteMassParityProfile B x * (B + 3 * x) ^ 2) *
            (A + 3 * x) ^ 2 := by ring
    _ =
        (6 * x * ((2 + 3 * x) * A + 6 * x + 6 * x ^ 2)) *
            (B + 3 * x) ^ 2 -
          (6 * x * ((2 + 3 * x) * B + 6 * x + 6 * x ^ 2)) *
            (A + 3 * x) ^ 2 := by rw [hprofileA, hprofileB]
    _ = 6 * x * (B - A) *
        d4FixedUnitRadiusFiniteMassParityCrossNumerator A B x := by
      unfold d4FixedUnitRadiusFiniteMassParityCrossNumerator
      ring

theorem d4FixedUnitRadiusFiniteMassParityCrossNumerator_pos
    {A B x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) :
    0 < d4FixedUnitRadiusFiniteMassParityCrossNumerator A B x := by
  unfold d4FixedUnitRadiusFiniteMassParityCrossNumerator
  positivity

/-- Positive-mass fixed-unit-radius profile separates positive shifted angular parameters. -/
theorem d4FixedUnitRadiusFiniteMassParityProfile_eq_iff
    {A B x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) :
    d4FixedUnitRadiusFiniteMassParityProfile A x =
        d4FixedUnitRadiusFiniteMassParityProfile B x ↔ A = B := by
  have hAden : A + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hBden : B + 3 * x ≠ 0 := ne_of_gt (by positivity)
  rw [← sub_eq_zero,
    d4FixedUnitRadiusFiniteMassParityProfile_sub_eq A B x hAden hBden]
  have hcross := d4FixedUnitRadiusFiniteMassParityCrossNumerator_pos hA hB hx
  have hden : (A + 3 * x) ^ 2 * (B + 3 * x) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hdenzero
    · rcases mul_eq_zero.mp hnum with hprod | hcrosszero
      · rcases mul_eq_zero.mp hprod with h6x | hBA
        · exact False.elim ((mul_ne_zero (by norm_num) (ne_of_gt hx)) h6x)
        · linarith
      · exact False.elim ((ne_of_gt hcross) hcrosszero)
    · exact False.elim (hden hdenzero)
  · rintro rfl
    ring

/-- Positive shifted angular parameter `A = Q + 2` of a reflected-real-pair BM channel. -/
def d4BMXiHorizonAngularShift (q : XiZeroCopy) : ℝ :=
  d4BMXiReflectedRealPairMediatorAngularQ q + 2

theorem d4BMXiHorizonAngularShift_pos (q : XiZeroCopy) :
    0 < d4BMXiHorizonAngularShift q := by
  have hQ := d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q
  unfold d4BMXiHorizonAngularShift
  linarith [hQ.1]

theorem d4BMXiHorizonAngularShift_eq (q : XiZeroCopy) :
    d4BMXiHorizonAngularShift q =
      (q.1 : ℂ).re * (3 - (q.1 : ℂ).re) := by
  exact d4BMXiReflectedRealPairMediatorAngularQ_add_two q

theorem d4BMXiHorizonAngularShift_reflect_eq (q : XiZeroCopy) :
    d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q) =
      (1 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re) := by
  unfold d4BMXiHorizonAngularShift d4BMXiReflectedRealPairMediatorAngularQ
  rw [xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- Exact fixed-unit-radius parity gap on a Xi-reflected BM mediator. -/
def d4BMXiFixedUnitRadiusFiniteMassParityGap (q : XiZeroCopy) (x : ℝ) : ℝ :=
  d4ScalarBracket (d4BMXiReflectedRealPairMediatorAngularQ q) x 1 -
    d4VectorBracket (d4BMXiReflectedRealPairMediatorAngularQ q) x

theorem d4BMXiFixedUnitRadiusFiniteMassParityGap_eq_profile
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiFixedUnitRadiusFiniteMassParityGap q x =
      d4FixedUnitRadiusFiniteMassParityProfile (d4BMXiHorizonAngularShift q) x := by
  have hQ := d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q
  have hden : d4BMXiReflectedRealPairMediatorAngularQ q + 2 + 3 * x ≠ 0 :=
    ne_of_gt (by linarith [hQ.1])
  unfold d4BMXiFixedUnitRadiusFiniteMassParityGap
  rw [d4ParitySplit_eq_finiteMassFactor _ x 1 hden]
  unfold d4FixedUnitRadiusFiniteMassParityProfile d4BMXiHorizonAngularShift
  ring

/-- Difference between reflected fixed-unit-radius parity gaps. -/
def d4BMXiFixedUnitRadiusFiniteMassParityDefect (q : XiZeroCopy) (x : ℝ) : ℝ :=
  d4BMXiFixedUnitRadiusFiniteMassParityGap q x -
    d4BMXiFixedUnitRadiusFiniteMassParityGap (xiZeroCopyReflectEquiv q) x

/-- Strictly positive finite-mass multiplier of horizontal Xi displacement. -/
def d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility
    (q : XiZeroCopy) (x : ℝ) : ℝ :=
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  12 * x * d4FixedUnitRadiusFiniteMassParityCrossNumerator A B x /
    ((A + 3 * x) ^ 2 * (B + 3 * x) ^ 2)

theorem d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility_pos
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    0 < d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility q x := by
  have hA := d4BMXiHorizonAngularShift_pos q
  have hB := d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  have hcross := d4FixedUnitRadiusFiniteMassParityCrossNumerator_pos hA hB hx
  unfold d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility
  exact div_pos (mul_pos (mul_pos (by norm_num) hx) hcross) (by positivity)

/-- Exact factorization of reflected fixed-unit-radius parity defect. -/
theorem d4BMXiFixedUnitRadiusFiniteMassParityDefect_eq
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiFixedUnitRadiusFiniteMassParityDefect q x =
      (1 - 2 * (q.1 : ℂ).re) *
        d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility q x := by
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  have hApos : 0 < A := d4BMXiHorizonAngularShift_pos q
  have hBpos : 0 < B := d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  have hA : A + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hB : B + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hBA : B - A = 2 * (1 - 2 * (q.1 : ℂ).re) := by
    dsimp [A, B]
    rw [d4BMXiHorizonAngularShift_reflect_eq,
      d4BMXiHorizonAngularShift_eq]
    ring
  unfold d4BMXiFixedUnitRadiusFiniteMassParityDefect
  rw [d4BMXiFixedUnitRadiusFiniteMassParityGap_eq_profile q hx,
    d4BMXiFixedUnitRadiusFiniteMassParityGap_eq_profile (xiZeroCopyReflectEquiv q) hx,
    d4FixedUnitRadiusFiniteMassParityProfile_sub_eq A B x hA hB]
  unfold d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility
  dsimp only
  rw [hBA]
  ring

/-- Reflected fixed-unit-radius parity gaps agree exactly at critical-line incidence. -/
theorem d4BMXiFixedUnitRadiusFiniteMassParityDefect_eq_zero_iff
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiFixedUnitRadiusFiniteMassParityDefect q x = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiFixedUnitRadiusFiniteMassParityDefect_eq q hx]
  have hs := d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility_pos q hx
  constructor
  · intro h
    rcases mul_eq_zero.mp h with htilt | hs0
    · linarith
    · exact False.elim ((ne_of_gt hs) hs0)
  · intro h
    rw [h]
    norm_num

/-- For every positive mass, the exact reflected radial defect reinforces the first BM
backreaction orientation off the critical line. -/
theorem d4BMXiFixedUnitRadiusFiniteMassParityDefect_mul_first_pos_of_tilt
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiFixedUnitRadiusFiniteMassParityDefect q x *
      d4BMXiReflectionOddBackreactionDefect q := by
  let a : ℝ := (q.1 : ℂ).re
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha0 : 0 < a := by simpa [a] using hstrip.1
  have ha1 : a < 1 := by simpa [a] using hstrip.2
  have hD : 0 < a * (1 - a) * (3 - a) * (2 + a) := by
    exact mul_pos (mul_pos (mul_pos ha0 (by linarith)) (by linarith)) (by linarith)
  have htilt : 1 - 2 * a ≠ 0 := by
    intro h
    apply hoff
    dsimp [a] at h ⊢
    linarith
  have hs := d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility_pos q hx
  rw [d4BMXiFixedUnitRadiusFiniteMassParityDefect_eq q hx,
    d4BMXiReflectionOddBackreactionDefect_eq]
  change 0 < ((1 - 2 * a) *
      d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility q x) *
        (24 * (1 - 2 * a) / (a * (1 - a) * (3 - a) * (2 + a)))
  rw [show ((1 - 2 * a) *
          d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility q x) *
        (24 * (1 - 2 * a) / (a * (1 - a) * (3 - a) * (2 + a))) =
      (24 * d4BMXiFixedUnitRadiusFiniteMassReflectionSusceptibility q x *
        (1 - 2 * a) ^ 2) /
          (a * (1 - a) * (3 - a) * (2 + a)) by ring]
  exact div_pos (mul_pos (mul_pos (by norm_num) hs) (sq_pos_of_ne_zero htilt)) hD

/-- On-shell event-horizon relation obtained from `f(r_h)=0`: `u_h=1+x_h`. -/
def d4TopologicalEventHorizonU (x : ℝ) : ℝ := 1 + x

/-- Scale coordinate `s=u x²` on the moving event horizon. -/
def d4TopologicalEventHorizonScale (x : ℝ) : ℝ := x ^ 2 + x ^ 3

theorem d4TopologicalDarbouxRadialPolynomial_eventHorizon
    (x : ℝ) :
    d4TopologicalDarbouxRadialPolynomial (d4TopologicalEventHorizonScale x) x = 0 := by
  unfold d4TopologicalDarbouxRadialPolynomial d4TopologicalEventHorizonScale
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  ring

/-- Darboux superpotential is constant along moving event horizon. -/
theorem d4TopologicalDarbouxReducedSuperpotential_eventHorizon
    (Q x : ℝ) :
    d4TopologicalDarbouxReducedSuperpotential Q
        (d4TopologicalEventHorizonScale x) x =
      d4TopologicalDarbouxAlgebraicConstant Q := by
  unfold d4TopologicalDarbouxReducedSuperpotential
  simp only [Pi.add_apply, Pi.div_apply,
    d4TopologicalDarbouxRadialPolynomial_eventHorizon]
  ring

theorem hasDerivAt_d4TopologicalDarbouxReducedSuperpotential_eventHorizonPath
    (Q x : ℝ) :
    HasDerivAt
      (fun y : ℝ => d4TopologicalDarbouxReducedSuperpotential Q
        (d4TopologicalEventHorizonScale y) y) 0 x := by
  have heq :
      (fun y : ℝ => d4TopologicalDarbouxReducedSuperpotential Q
        (d4TopologicalEventHorizonScale y) y) =
      fun _ : ℝ => d4TopologicalDarbouxAlgebraicConstant Q := by
    funext y
    exact d4TopologicalDarbouxReducedSuperpotential_eventHorizon Q y
  rw [heq]
  exact hasDerivAt_const x _

/-- Exact moving-horizon parity profile; a single positive Stieltjes resolvent in `A`. -/
def d4EventHorizonFiniteMassParityProfile (A x : ℝ) : ℝ :=
  6 * x * (2 + 3 * x) / (A + 3 * x)

def d4EventHorizonFiniteMassParityGap (Q x : ℝ) : ℝ :=
  d4ScalarBracket Q x (d4TopologicalEventHorizonU x) -
    d4VectorBracket Q x

theorem d4EventHorizonFiniteMassParityGap_eq_profile
    (Q x : ℝ) (hden : Q + 2 + 3 * x ≠ 0) :
    d4EventHorizonFiniteMassParityGap Q x =
      d4EventHorizonFiniteMassParityProfile (Q + 2) x := by
  unfold d4EventHorizonFiniteMassParityGap d4TopologicalEventHorizonU
  rw [d4ParitySplit_eq_finiteMassFactor Q x (1 + x) hden]
  rw [show 2 * (Q + 2) + 3 * (Q + (1 + x) + 3) * x + 6 * x ^ 2 =
      (2 + 3 * x) * (Q + 2 + 3 * x) by ring]
  unfold d4EventHorizonFiniteMassParityProfile
  rw [pow_two]
  field_simp [hden]

def d4TopologicalEventHorizonShapeVelocity (x : ℝ) : ℝ :=
  2 * x + 3 * x ^ 2

def d4TopologicalDarbouxScaleNormalDerivative (Q x : ℝ) : ℝ :=
  3 / (Q + 2 + 3 * x)

/-- Moving-horizon parity gap is twice shape velocity times normal Darboux derivative. -/
theorem d4EventHorizonFiniteMassParityGap_eq_shapeFlux
    (Q x : ℝ) (hden : Q + 2 + 3 * x ≠ 0) :
    d4EventHorizonFiniteMassParityGap Q x =
      2 * d4TopologicalEventHorizonShapeVelocity x *
        d4TopologicalDarbouxScaleNormalDerivative Q x := by
  rw [d4EventHorizonFiniteMassParityGap_eq_profile Q x hden]
  unfold d4EventHorizonFiniteMassParityProfile
    d4TopologicalEventHorizonShapeVelocity
    d4TopologicalDarbouxScaleNormalDerivative
  field_simp [hden]
  ring

/-- Fixed-scale radial derivative at event horizon is minus half parity gap. -/
theorem hasDerivAt_d4TopologicalDarbouxReducedSuperpotential_fixedScale_eventHorizon
    (Q x : ℝ) (hx : x ≠ 0) (hden : Q + 2 + 3 * x ≠ 0) :
    HasDerivAt
      (d4TopologicalDarbouxReducedSuperpotential Q
        (d4TopologicalEventHorizonScale x))
      (-d4EventHorizonFiniteMassParityGap Q x / 2) x := by
  have hscale : d4TopologicalEventHorizonScale x / x ^ 2 = 1 + x := by
    unfold d4TopologicalEventHorizonScale
    field_simp [hx]
  have h := hasDerivAt_d4TopologicalDarbouxReducedSuperpotential
    Q (d4TopologicalEventHorizonScale x) x hx hden
  rw [hscale] at h
  exact h

/-- Tangential derivative vanishes because fixed-scale radial defect is exactly projected flux. -/
theorem d4EventHorizonDarbouxOpticalDecomposition
    (Q x : ℝ) (hden : Q + 2 + 3 * x ≠ 0) :
    -d4EventHorizonFiniteMassParityGap Q x / 2 +
      d4TopologicalEventHorizonShapeVelocity x *
        d4TopologicalDarbouxScaleNormalDerivative Q x = 0 := by
  rw [d4EventHorizonFiniteMassParityGap_eq_shapeFlux Q x hden]
  ring

/-- Exact secant law for two angular sectors on same event horizon. -/
theorem d4EventHorizonFiniteMassParityProfile_sub_eq
    (A B x : ℝ) (hA : A + 3 * x ≠ 0) (hB : B + 3 * x ≠ 0) :
    d4EventHorizonFiniteMassParityProfile A x -
        d4EventHorizonFiniteMassParityProfile B x =
      6 * x * (2 + 3 * x) * (B - A) /
        ((A + 3 * x) * (B + 3 * x)) := by
  let c : ℝ := 6 * x * (2 + 3 * x)
  let dA : ℝ := A + 3 * x
  let dB : ℝ := B + 3 * x
  have hdA : dA ≠ 0 := by simpa [dA] using hA
  have hdB : dB ≠ 0 := by simpa [dB] using hB
  have hdAB : dA * dB ≠ 0 := mul_ne_zero hdA hdB
  change c / dA - c / dB = c * (B - A) / (dA * dB)
  apply (eq_div_iff hdAB).2
  calc
    (c / dA - c / dB) * (dA * dB) =
        (c / dA * dA) * dB - (c / dB * dB) * dA := by ring
    _ = c * dB - c * dA := by rw [div_mul_cancel₀ c hdA, div_mul_cancel₀ c hdB]
    _ = c * (B - A) := by dsimp [dA, dB]; ring

theorem d4EventHorizonFiniteMassParityProfile_eq_iff
    {A B x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) :
    d4EventHorizonFiniteMassParityProfile A x =
        d4EventHorizonFiniteMassParityProfile B x ↔ A = B := by
  have hAden : A + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hBden : B + 3 * x ≠ 0 := ne_of_gt (by positivity)
  rw [← sub_eq_zero,
    d4EventHorizonFiniteMassParityProfile_sub_eq A B x hAden hBden]
  have hfactor : 6 * x * (2 + 3 * x) ≠ 0 := by positivity
  have hden : (A + 3 * x) * (B + 3 * x) ≠ 0 := by positivity
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hnum | hdenzero
    · rcases mul_eq_zero.mp hnum with hfactorzero | hBA
      · exact False.elim (hfactor hfactorzero)
      · linarith
    · exact False.elim (hden hdenzero)
  · rintro rfl
    ring

theorem d4EventHorizonFiniteMassParityProfile_strictAnti
    {A B x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 0 < x) (hAB : A < B) :
    d4EventHorizonFiniteMassParityProfile B x <
      d4EventHorizonFiniteMassParityProfile A x := by
  have hAden : A + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hBden : B + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hsub := d4EventHorizonFiniteMassParityProfile_sub_eq A B x hAden hBden
  have hpos : 0 < d4EventHorizonFiniteMassParityProfile A x -
      d4EventHorizonFiniteMassParityProfile B x := by
    rw [hsub]
    positivity
  linarith

theorem d4BMXiHorizonAngularShift_lt_two (q : XiZeroCopy) :
    d4BMXiHorizonAngularShift q < 2 := by
  have hQ := d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo q
  unfold d4BMXiHorizonAngularShift
  linarith [hQ.2]

def d4BMXiEventHorizonFiniteMassParityGap (q : XiZeroCopy) (x : ℝ) : ℝ :=
  d4EventHorizonFiniteMassParityGap
    (d4BMXiReflectedRealPairMediatorAngularQ q) x

theorem d4BMXiEventHorizonFiniteMassParityGap_eq_profile
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiEventHorizonFiniteMassParityGap q x =
      d4EventHorizonFiniteMassParityProfile (d4BMXiHorizonAngularShift q) x := by
  have hA := d4BMXiHorizonAngularShift_pos q
  unfold d4BMXiEventHorizonFiniteMassParityGap
  rw [d4EventHorizonFiniteMassParityGap_eq_profile]
  · rfl
  · apply ne_of_gt
    change 0 < d4BMXiHorizonAngularShift q + 3 * x
    positivity

def d4BMXiEventHorizonFiniteMassParityDefect (q : XiZeroCopy) (x : ℝ) : ℝ :=
  d4BMXiEventHorizonFiniteMassParityGap q x -
    d4BMXiEventHorizonFiniteMassParityGap (xiZeroCopyReflectEquiv q) x

def d4BMXiEventHorizonFiniteMassReflectionSusceptibility
    (q : XiZeroCopy) (x : ℝ) : ℝ :=
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  12 * x * (2 + 3 * x) / ((A + 3 * x) * (B + 3 * x))

theorem d4BMXiEventHorizonFiniteMassReflectionSusceptibility_pos
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    0 < d4BMXiEventHorizonFiniteMassReflectionSusceptibility q x := by
  have hA := d4BMXiHorizonAngularShift_pos q
  have hB := d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  unfold d4BMXiEventHorizonFiniteMassReflectionSusceptibility
  exact div_pos (by positivity) (by positivity)

/-- Reflected event-horizon defect is horizontal displacement times positive susceptibility. -/
theorem d4BMXiEventHorizonFiniteMassParityDefect_eq
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiEventHorizonFiniteMassParityDefect q x =
      (1 - 2 * (q.1 : ℂ).re) *
        d4BMXiEventHorizonFiniteMassReflectionSusceptibility q x := by
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  have hApos : 0 < A := d4BMXiHorizonAngularShift_pos q
  have hBpos : 0 < B := d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  have hA : A + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hB : B + 3 * x ≠ 0 := ne_of_gt (by positivity)
  have hBA : B - A = 2 * (1 - 2 * (q.1 : ℂ).re) := by
    dsimp [A, B]
    rw [d4BMXiHorizonAngularShift_reflect_eq,
      d4BMXiHorizonAngularShift_eq]
    ring
  unfold d4BMXiEventHorizonFiniteMassParityDefect
  rw [d4BMXiEventHorizonFiniteMassParityGap_eq_profile q hx,
    d4BMXiEventHorizonFiniteMassParityGap_eq_profile (xiZeroCopyReflectEquiv q) hx,
    d4EventHorizonFiniteMassParityProfile_sub_eq A B x hA hB]
  unfold d4BMXiEventHorizonFiniteMassReflectionSusceptibility
  dsimp only
  rw [hBA]
  ring

theorem d4BMXiEventHorizonFiniteMassParityDefect_eq_zero_iff
    (q : XiZeroCopy) {x : ℝ} (hx : 0 < x) :
    d4BMXiEventHorizonFiniteMassParityDefect q x = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiEventHorizonFiniteMassParityDefect_eq q hx]
  have hs := d4BMXiEventHorizonFiniteMassReflectionSusceptibility_pos q hx
  constructor
  · intro h
    rcases mul_eq_zero.mp h with htilt | hs0
    · linarith
    · exact False.elim ((ne_of_gt hs) hs0)
  · intro h
    rw [h]
    norm_num

/-- Continuous cubic remainder after removing first two moving-horizon mass coefficients. -/
def d4EventHorizonParityThirdJetCompletion (Q x : ℝ) : ℝ :=
  -54 * Q / ((Q + 2) ^ 2 * (Q + 2 + 3 * x))

theorem d4EventHorizonParityGap_sub_twoJets_eq_thirdJet
    (Q x : ℝ) (hQ2 : Q + 2 ≠ 0) (hden : Q + 2 + 3 * x ≠ 0) :
    d4EventHorizonFiniteMassParityGap Q x -
          (12 / (Q + 2)) * x -
        (18 * Q / (Q + 2) ^ 2) * x ^ 2 =
      x ^ 3 * d4EventHorizonParityThirdJetCompletion Q x := by
  rw [d4EventHorizonFiniteMassParityGap_eq_profile Q x hden]
  unfold d4EventHorizonFiniteMassParityProfile
    d4EventHorizonParityThirdJetCompletion
  let A : ℝ := Q + 2
  let d : ℝ := A + 3 * x
  have hA : A ≠ 0 := by simpa [A] using hQ2
  have hd : d ≠ 0 := by simpa [d, A] using hden
  change 6 * x * (2 + 3 * x) / d -
        (12 / A) * x - (18 * Q / A ^ 2) * x ^ 2 =
      x ^ 3 * (-54 * Q / (A ^ 2 * d))
  field_simp [hA, hd]
  ring

theorem d4EventHorizonParityThirdJetCompletion_zero
    (Q : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4EventHorizonParityThirdJetCompletion Q 0 =
      -54 * Q / (Q + 2) ^ 3 := by
  unfold d4EventHorizonParityThirdJetCompletion
  field_simp [hQ2]
  ring

/-- Third shape derivative along moving event horizon `u=1+x`. -/
def d4EventHorizonThirdMassParityJet (Q : ℝ) : ℝ :=
  -324 * Q / (Q + 2) ^ 3

theorem d4EventHorizonThirdMassParityJet_eq_six_mul_completion
    (Q : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4EventHorizonThirdMassParityJet Q =
      6 * d4EventHorizonParityThirdJetCompletion Q 0 := by
  rw [d4EventHorizonParityThirdJetCompletion_zero Q hQ2]
  unfold d4EventHorizonThirdMassParityJet
  ring

/-- Horizon motion contributes `108/(Q+2)^2` beyond fixed-radius partial derivative. -/
theorem d4EventHorizonThirdMassParityJet_eq_fixedRadius_add_motion
    (Q : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4EventHorizonThirdMassParityJet Q =
      d4ThirdMassParityJet Q 1 + 108 / (Q + 2) ^ 2 := by
  unfold d4EventHorizonThirdMassParityJet d4ThirdMassParityJet
  field_simp [hQ2]
  ring

theorem d4EventHorizonThirdMassParityJet_neg_physical (xi : ℝ) :
    d4EventHorizonThirdMassParityJet (d4ThetaPhysicalAngularQ xi) < 0 := by
  unfold d4EventHorizonThirdMassParityJet d4ThetaPhysicalAngularQ
  have hQ : 0 < (1 / 4 : ℝ) + xi ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hQ) (by positivity)

theorem d4EventHorizonThirdMassParityJet_pos_virtual
    {Q : ℝ} (hQ : Q ∈ Set.Ioo (-2) 0) :
    0 < d4EventHorizonThirdMassParityJet Q := by
  unfold d4EventHorizonThirdMassParityJet
  have hQ2 : 0 < Q + 2 := by linarith [hQ.1]
  exact div_pos (mul_pos_of_neg_of_neg (by norm_num) hQ.2) (by positivity)

def d4EventHorizonThirdMassParityProfile (A : ℝ) : ℝ :=
  324 * (2 - A) / A ^ 3

theorem d4EventHorizonThirdMassParityJet_eq_profile
    (Q : ℝ) :
    d4EventHorizonThirdMassParityJet Q =
      d4EventHorizonThirdMassParityProfile (Q + 2) := by
  unfold d4EventHorizonThirdMassParityJet d4EventHorizonThirdMassParityProfile
  ring

def d4EventHorizonThirdMassParityCrossNumerator (A B : ℝ) : ℝ :=
  A ^ 2 * (2 - B) + B ^ 2 * (2 - A) + 2 * A * B

theorem d4EventHorizonThirdMassParityProfile_sub_eq
    (A B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    d4EventHorizonThirdMassParityProfile A -
        d4EventHorizonThirdMassParityProfile B =
      324 * (B - A) * d4EventHorizonThirdMassParityCrossNumerator A B /
        (A ^ 3 * B ^ 3) := by
  unfold d4EventHorizonThirdMassParityProfile
    d4EventHorizonThirdMassParityCrossNumerator
  field_simp [hA, hB]
  ring

theorem d4EventHorizonThirdMassParityCrossNumerator_pos
    {A B : ℝ} (hA0 : 0 < A) (hA2 : A < 2)
    (hB0 : 0 < B) (hB2 : B < 2) :
    0 < d4EventHorizonThirdMassParityCrossNumerator A B := by
  unfold d4EventHorizonThirdMassParityCrossNumerator
  positivity

def d4BMXiEventHorizonThirdMassParityJet (q : XiZeroCopy) : ℝ :=
  d4EventHorizonThirdMassParityProfile (d4BMXiHorizonAngularShift q)

def d4BMXiEventHorizonThirdMassParityJetDefect (q : XiZeroCopy) : ℝ :=
  d4BMXiEventHorizonThirdMassParityJet q -
    d4BMXiEventHorizonThirdMassParityJet (xiZeroCopyReflectEquiv q)

def d4BMXiEventHorizonThirdMassReflectionSusceptibility (q : XiZeroCopy) : ℝ :=
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  648 * d4EventHorizonThirdMassParityCrossNumerator A B / (A ^ 3 * B ^ 3)

theorem d4BMXiEventHorizonThirdMassReflectionSusceptibility_pos
    (q : XiZeroCopy) :
    0 < d4BMXiEventHorizonThirdMassReflectionSusceptibility q := by
  have hA0 := d4BMXiHorizonAngularShift_pos q
  have hA2 := d4BMXiHorizonAngularShift_lt_two q
  have hB0 := d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  have hB2 := d4BMXiHorizonAngularShift_lt_two (xiZeroCopyReflectEquiv q)
  have hcross := d4EventHorizonThirdMassParityCrossNumerator_pos hA0 hA2 hB0 hB2
  unfold d4BMXiEventHorizonThirdMassReflectionSusceptibility
  exact div_pos (mul_pos (by norm_num) hcross) (by positivity)

theorem d4BMXiEventHorizonThirdMassParityJetDefect_eq
    (q : XiZeroCopy) :
    d4BMXiEventHorizonThirdMassParityJetDefect q =
      (1 - 2 * (q.1 : ℂ).re) *
        d4BMXiEventHorizonThirdMassReflectionSusceptibility q := by
  let A := d4BMXiHorizonAngularShift q
  let B := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  have hA0 : A ≠ 0 := ne_of_gt (d4BMXiHorizonAngularShift_pos q)
  have hB0 : B ≠ 0 := ne_of_gt
    (d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q))
  have hBA : B - A = 2 * (1 - 2 * (q.1 : ℂ).re) := by
    dsimp [A, B]
    rw [d4BMXiHorizonAngularShift_reflect_eq,
      d4BMXiHorizonAngularShift_eq]
    ring
  unfold d4BMXiEventHorizonThirdMassParityJetDefect
    d4BMXiEventHorizonThirdMassParityJet
  rw [d4EventHorizonThirdMassParityProfile_sub_eq A B hA0 hB0]
  unfold d4BMXiEventHorizonThirdMassReflectionSusceptibility
  dsimp only
  rw [hBA]
  ring

theorem d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMXiEventHorizonThirdMassParityJetDefect q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq]
  have hs := d4BMXiEventHorizonThirdMassReflectionSusceptibility_pos q
  constructor
  · intro h
    rcases mul_eq_zero.mp h with htilt | hs0
    · linarith
    · exact False.elim ((ne_of_gt hs) hs0)
  · intro h
    rw [h]
    norm_num

/-- First and moving-horizon third variants reinforce off critical line. -/
theorem d4BMXiEventHorizonThirdMassParityJetDefect_mul_first_pos_of_tilt
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiEventHorizonThirdMassParityJetDefect q *
      d4BMXiReflectionOddBackreactionDefect q := by
  let a : ℝ := (q.1 : ℂ).re
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha0 : 0 < a := by simpa [a] using hstrip.1
  have ha1 : a < 1 := by simpa [a] using hstrip.2
  have hD : 0 < a * (1 - a) * (3 - a) * (2 + a) := by
    exact mul_pos (mul_pos (mul_pos ha0 (by linarith)) (by linarith)) (by linarith)
  have htilt : 1 - 2 * a ≠ 0 := by
    intro h
    apply hoff
    dsimp [a] at h ⊢
    linarith
  have hs := d4BMXiEventHorizonThirdMassReflectionSusceptibility_pos q
  rw [d4BMXiEventHorizonThirdMassParityJetDefect_eq,
    d4BMXiReflectionOddBackreactionDefect_eq]
  change 0 < ((1 - 2 * a) *
      d4BMXiEventHorizonThirdMassReflectionSusceptibility q) *
        (24 * (1 - 2 * a) / (a * (1 - a) * (3 - a) * (2 + a)))
  rw [show ((1 - 2 * a) *
          d4BMXiEventHorizonThirdMassReflectionSusceptibility q) *
        (24 * (1 - 2 * a) / (a * (1 - a) * (3 - a) * (2 + a))) =
      (24 * d4BMXiEventHorizonThirdMassReflectionSusceptibility q *
        (1 - 2 * a) ^ 2) /
          (a * (1 - a) * (3 - a) * (2 + a)) by ring]
  exact div_pos (mul_pos (mul_pos (by norm_num) hs) (sq_pos_of_ne_zero htilt)) hD

end

end RHTower
