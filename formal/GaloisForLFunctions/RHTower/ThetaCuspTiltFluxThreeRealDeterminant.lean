import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxTwoSupportRigidity

/-!
# Three-real-node determinant wall for theta-cusp tilt flux

Strict one- and two-node positivity leaves three distinct real nodes as the first possible
real-ray geometry of a negative literal theta-cusp tilt-flux packet.  This module identifies its
complete sign law: because the first two principal minors of the full Xi Euler-response kernel
are strictly positive, the single symmetric three-point determinant is the exact wall between
nonnegative energy and a negative coefficient direction.

The proof uses a denominator-free `LDLᵀ` completion and then transports the result through the
exact Xi diagonal congruence of the literal theta source.  No zero-location hypothesis is used.

Claim labels: `[LEAN-PROVED] [BRIDGE/REDUCTION] [NOVELTY UNVERIFIED]`.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

/-- Explicit Hermitian energy of the full Xi Euler-response kernel on three real nodes. -/
def threeRealEulerResponseEnergy (x y z : ℝ) (c : Fin 3 → ℂ) : ℝ :=
  xiSquaredEulerFullKernel x x * Complex.normSq (c 0) +
    xiSquaredEulerFullKernel y y * Complex.normSq (c 1) +
    xiSquaredEulerFullKernel z z * Complex.normSq (c 2) +
    2 * xiSquaredEulerFullKernel x y * (conj (c 0) * c 1).re +
    2 * xiSquaredEulerFullKernel x z * (conj (c 0) * c 2).re +
    2 * xiSquaredEulerFullKernel y z * (conj (c 1) * c 2).re

/-- Ordered three-real-node family, viewed in the complex exterior half-plane. -/
def threeRealNodes (x y z : ℝ) : Fin 3 → ℂ :=
  ![(x : ℂ), (y : ℂ), (z : ℂ)]

/-- Xi diagonal congruence carrying literal theta coefficients to critical-kernel coefficients. -/
def threeRealXiRescaledCoefficients (x y z : ℝ) (c : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun j => c j * xiCent (threeRealNodes x y z j)

private def realThreePointEnergy
    (A B G P Q R u v w : ℝ) : ℝ :=
  A * u ^ (2 : ℕ) + B * v ^ (2 : ℕ) + G * w ^ (2 : ℕ) +
    2 * P * u * v + 2 * Q * u * w + 2 * R * v * w

private def realThreePointDet (A B G P Q R : ℝ) : ℝ :=
  A * B * G + 2 * P * Q * R - A * R ^ (2 : ℕ) - B * Q ^ (2 : ℕ) - G * P ^ (2 : ℕ)

/-- Denominator-free `LDLᵀ` completion for a general real symmetric three-point form. -/
private theorem realThreePointEnergy_scaled_completion
    (A B G P Q R u v w : ℝ) :
    A * (A * B - P ^ (2 : ℕ)) * realThreePointEnergy A B G P Q R u v w =
      (A * B - P ^ (2 : ℕ)) * (A * u + P * v + Q * w) ^ (2 : ℕ) +
        ((A * B - P ^ (2 : ℕ)) * v + (A * R - P * Q) * w) ^ (2 : ℕ) +
        A * realThreePointDet A B G P Q R * w ^ (2 : ℕ) := by
  unfold realThreePointEnergy realThreePointDet
  ring

/-- Once the first two leading principal minors are positive, the cubic determinant is the exact
wall for nonnegativity of a real symmetric three-point form. -/
private theorem forall_realThreePointEnergy_nonneg_iff
    {A B G P Q R : ℝ} (hA : 0 < A) (hminor : 0 < A * B - P ^ (2 : ℕ)) :
    (∀ u v w : ℝ, 0 ≤ realThreePointEnergy A B G P Q R u v w) ↔
      0 ≤ realThreePointDet A B G P Q R := by
  let Δ := A * B - P ^ (2 : ℕ)
  have hΔ : 0 < Δ := by simpa only [Δ] using hminor
  constructor
  · intro henergy
    by_contra hdet
    have hdetneg : realThreePointDet A B G P Q R < 0 := lt_of_not_ge hdet
    let S := A * R - P * Q
    let u := P * S - Δ * Q
    let v := -A * S
    let w := A * Δ
    have hnonneg := henergy u v w
    have hscaled := realThreePointEnergy_scaled_completion A B G P Q R u v w
    have hscaled' :
        A * Δ * realThreePointEnergy A B G P Q R u v w =
          A * realThreePointDet A B G P Q R * (A * Δ) ^ (2 : ℕ) := by
      rw [show Δ = A * B - P ^ (2 : ℕ) by rfl]
      rw [hscaled]
      dsimp only [u, v, w, S, Δ]
      ring
    have hleft :
        0 ≤ A * Δ * realThreePointEnergy A B G P Q R u v w :=
      mul_nonneg (mul_pos hA hΔ).le hnonneg
    have hright :
        A * realThreePointDet A B G P Q R * (A * Δ) ^ (2 : ℕ) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA hdetneg)
        (sq_pos_of_pos (mul_pos hA hΔ))
    rw [hscaled'] at hleft
    exact (not_lt_of_ge hleft hright).elim
  · intro hdet u v w
    have hscaled := realThreePointEnergy_scaled_completion A B G P Q R u v w
    have hrhs :
        0 ≤ (A * B - P ^ (2 : ℕ)) * (A * u + P * v + Q * w) ^ (2 : ℕ) +
            ((A * B - P ^ (2 : ℕ)) * v + (A * R - P * Q) * w) ^ (2 : ℕ) +
            A * realThreePointDet A B G P Q R * w ^ (2 : ℕ) := by
      positivity
    have hprod :
        0 ≤ A * (A * B - P ^ (2 : ℕ)) * realThreePointEnergy A B G P Q R u v w := by
      rw [hscaled]
      exact hrhs
    exact nonneg_of_mul_nonneg_right hprod (mul_pos hA hminor)

/-- The complete three-real-node Xi response is nonnegative in every complex coefficient
direction exactly when its symmetric cubic determinant is nonnegative. -/
theorem threeRealEulerResponseEnergy_nonneg_iff_det_nonneg
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (_hyz : y < z) :
    (∀ c : Fin 3 → ℂ, 0 ≤ threeRealEulerResponseEnergy x y z c) ↔
      0 ≤ symmetricThreePointDet xiSquaredEulerFullKernel x y z := by
  let A := xiSquaredEulerFullKernel x x
  let B := xiSquaredEulerFullKernel y y
  let G := xiSquaredEulerFullKernel z z
  let P := xiSquaredEulerFullKernel x y
  let Q := xiSquaredEulerFullKernel x z
  let R := xiSquaredEulerFullKernel y z
  have hA : 0 < A := xiSquaredEulerFullKernel_diag_pos hx
  have hminor : 0 < A * B - P ^ (2 : ℕ) := by
    exact xiSquaredEulerFullKernel_twoPoint_det_pos hx hxy
  have hreal := forall_realThreePointEnergy_nonneg_iff
    (G := G) (Q := Q) (R := R) hA hminor
  have hdet :
      realThreePointDet A B G P Q R =
        symmetricThreePointDet xiSquaredEulerFullKernel x y z := by
    simp only [A, B, G, P, Q, R, realThreePointDet, symmetricThreePointDet]
  rw [← hdet, ← hreal]
  constructor
  · intro hcomplex u v w
    let c : Fin 3 → ℂ := ![(u : ℂ), (v : ℂ), (w : ℂ)]
    have hc := hcomplex c
    simp only [threeRealEulerResponseEnergy, c, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Complex.normSq_ofReal, Complex.conj_ofReal,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      ] at hc
    unfold realThreePointEnergy
    dsimp only [A, B, G, P, Q, R]
    nlinarith [hc]
  · intro hrealEnergy c
    have hre := hrealEnergy (c 0).re (c 1).re (c 2).re
    have him := hrealEnergy (c 0).im (c 1).im (c 2).im
    have hsplit :
        threeRealEulerResponseEnergy x y z c =
          realThreePointEnergy A B G P Q R (c 0).re (c 1).re (c 2).re +
          realThreePointEnergy A B G P Q R (c 0).im (c 1).im (c 2).im := by
      simp only [threeRealEulerResponseEnergy, realThreePointEnergy,
        Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        A, B, G, P, Q, R]
      ring
    rw [hsplit]
    exact add_nonneg hre him

/-- Equivalently, a negative coefficient direction exists exactly on the negative side of the
single cubic determinant wall. -/
theorem exists_threeRealEulerResponseEnergy_neg_iff_det_neg
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    (∃ c : Fin 3 → ℂ, threeRealEulerResponseEnergy x y z c < 0) ↔
      symmetricThreePointDet xiSquaredEulerFullKernel x y z < 0 := by
  have hcriterion := threeRealEulerResponseEnergy_nonneg_iff_det_nonneg hx hxy hyz
  constructor
  · rintro ⟨c, hc⟩
    by_contra hdet
    have hall := hcriterion.2 (le_of_not_gt hdet)
    exact (not_lt_of_ge (hall c)) hc
  · intro hdet
    by_contra hnone
    have hall : ∀ c : Fin 3 → ℂ, 0 ≤ threeRealEulerResponseEnergy x y z c := by
      intro c
      exact le_of_not_gt (fun hc => hnone ⟨c, hc⟩)
    exact (not_lt_of_ge (hcriterion.1 hall)) hdet

private theorem xiSquaredEulerFullKernel_symm (u v : ℝ) :
    xiSquaredEulerFullKernel u v = xiSquaredEulerFullKernel v u := by
  simp [xiSquaredEulerFullKernel, eulerRayResponseKernel, add_comm]

/-- On three exterior real nodes, the critical logarithmic-derivative quadratic sum is exactly
the explicit full Xi Euler-response energy. -/
theorem criticalLogDerivKernel_threeReal_sum_re_eq_responseEnergy
    {x y z : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (hyz : y < z)
    (c : Fin 3 → ℂ) :
    (∑ j, ∑ k, c j * conj (c k) *
        criticalLogDerivKernel (threeRealNodes x y z j) (threeRealNodes x y z k)).re =
      threeRealEulerResponseEnergy x y z c := by
  have hy : 1 / 2 < y := hx.trans hxy
  have hz : 1 / 2 < z := hy.trans hyz
  simp only [Fin.sum_univ_three, threeRealNodes, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [criticalLogDerivKernel_ofReal_eq_fullKernel hx hx,
    criticalLogDerivKernel_ofReal_eq_fullKernel hx hy,
    criticalLogDerivKernel_ofReal_eq_fullKernel hx hz,
    criticalLogDerivKernel_ofReal_eq_fullKernel hy hx,
    criticalLogDerivKernel_ofReal_eq_fullKernel hy hy,
    criticalLogDerivKernel_ofReal_eq_fullKernel hy hz,
    criticalLogDerivKernel_ofReal_eq_fullKernel hz hx,
    criticalLogDerivKernel_ofReal_eq_fullKernel hz hy,
    criticalLogDerivKernel_ofReal_eq_fullKernel hz hz]
  rw [xiSquaredEulerFullKernel_symm y x,
    xiSquaredEulerFullKernel_symm z x, xiSquaredEulerFullKernel_symm z y]
  simp only [threeRealEulerResponseEnergy, Complex.add_re, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_apply]
  ring

/-- Exact three-node Xi congruence: literal theta-source flux equals full Euler-response energy
after coefficient multiplication by the nonvanishing Xi diagonal. -/
theorem thetaCuspTiltSource_threeReal_flux_eq_responseEnergy
    {x y z : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (hyz : y < z)
    (c : Fin 3 → ℂ) :
    (∑ j, ∑ k, c j * conj (c k) *
        sourceBezoutian thetaCuspTiltSource
          (threeRealNodes x y z j) (threeRealNodes x y z k)).re =
      threeRealEulerResponseEnergy x y z
        (threeRealXiRescaledCoefficients x y z c) := by
  have hnodes : ∀ j, 1 / 2 < (threeRealNodes x y z j).re := by
    intro j
    fin_cases j <;> simp [threeRealNodes] <;> linarith
  have hsum :
      (∑ j, ∑ k, c j * conj (c k) *
          sourceBezoutian thetaCuspTiltSource
            (threeRealNodes x y z j) (threeRealNodes x y z k)) =
        ∑ j, ∑ k,
          threeRealXiRescaledCoefficients x y z c j *
            conj (threeRealXiRescaledCoefficients x y z c k) *
            criticalLogDerivKernel
              (threeRealNodes x y z j) (threeRealNodes x y z k) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sourceBezoutian_thetaCuspTiltSource_eq_xiCent_mul_criticalKernel
      (hnodes j) (hnodes k)]
    simp only [threeRealXiRescaledCoefficients, map_mul]
    ring
  rw [hsum]
  exact criticalLogDerivKernel_threeReal_sum_re_eq_responseEnergy hx hxy hyz _

/-- Every derivative value of a literal three-real-node theta packet is the corresponding full
Xi Euler-response energy after diagonal rescaling. -/
theorem thetaCuspTiltSource_threeReal_tiltFlux_eq_responseEnergy
    {x y z : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (hyz : y < z)
    (c : Fin 3 → ℂ) {D : ℝ}
    (hD : HasDerivAt
      (tiltCorrelation thetaCuspTiltSource c (threeRealNodes x y z)) D 0) :
    D = threeRealEulerResponseEnergy x y z
      (threeRealXiRescaledCoefficients x y z c) := by
  have hnodes : ∀ j, 0 < (threeRealNodes x y z j).re := by
    intro j
    fin_cases j <;> simp [threeRealNodes] <;> linarith
  calc
    D = (∑ j, ∑ k, c j * conj (c k) *
        sourceBezoutian thetaCuspTiltSource
          (threeRealNodes x y z j) (threeRealNodes x y z k)).re :=
      hD.unique (hasDerivAt_tiltCorrelation thetaCuspTiltSource c
        (threeRealNodes x y z) hnodes)
    _ = threeRealEulerResponseEnergy x y z
        (threeRealXiRescaledCoefficients x y z c) :=
      thetaCuspTiltSource_threeReal_flux_eq_responseEnergy hx hxy hyz c

/-- **Minimal real-ray classification.**  A negative literal theta-cusp tilt-flux direction on
three ordered exterior real nodes exists exactly when the full Xi Euler-response cubic determinant
is negative.  Thus the entire minimal real branch has one scalar proof obligation. -/
theorem exists_threeMode_realRay_thetaCuspTiltFlux_neg_iff_det_neg
    {x y z : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (hyz : y < z) :
    (∃ (c : Fin 3 → ℂ) (D : ℝ),
        HasDerivAt
          (tiltCorrelation thetaCuspTiltSource c (threeRealNodes x y z)) D 0 ∧
        D < 0) ↔
      symmetricThreePointDet xiSquaredEulerFullKernel x y z < 0 := by
  have henergyCriterion :=
    exists_threeRealEulerResponseEnergy_neg_iff_det_neg
      (x := x) (y := y) (z := z) (by linarith) hxy hyz
  constructor
  · rintro ⟨c, D, hD, hneg⟩
    apply henergyCriterion.1
    refine ⟨threeRealXiRescaledCoefficients x y z c, ?_⟩
    rw [← thetaCuspTiltSource_threeReal_tiltFlux_eq_responseEnergy hx hxy hyz c hD]
    exact hneg
  · intro hdet
    rcases henergyCriterion.2 hdet with ⟨d, hd⟩
    let c : Fin 3 → ℂ := fun j =>
      d j / xiCent (threeRealNodes x y z j)
    have hnodesHalf : ∀ j, 1 / 2 < (threeRealNodes x y z j).re := by
      intro j
      fin_cases j <;> simp [threeRealNodes] <;> linarith
    have hnodesPos : ∀ j, 0 < (threeRealNodes x y z j).re := fun j => by
      linarith [hnodesHalf j]
    have hrescaled : threeRealXiRescaledCoefficients x y z c = d := by
      funext j
      dsimp only [threeRealXiRescaledCoefficients, c]
      exact div_mul_cancel₀ (d j)
        (xiCent_ne_zero_of_half_lt_re (hnodesHalf j))
    have hcanonical := hasDerivAt_tiltCorrelation thetaCuspTiltSource c
      (threeRealNodes x y z) hnodesPos
    have hflux := thetaCuspTiltSource_threeReal_flux_eq_responseEnergy hx hxy hyz c
    rw [hrescaled] at hflux
    rw [hflux] at hcanonical
    exact ⟨c, threeRealEulerResponseEnergy x y z d, hcanonical, hd⟩

end

end RHTower
