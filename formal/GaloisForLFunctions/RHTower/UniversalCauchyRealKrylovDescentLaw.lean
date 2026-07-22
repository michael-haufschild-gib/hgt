import GaloisForLFunctions.RHTower.XiReciprocalFixedCauchyRealKrylovSeam

/-!
# Universal pointwise real-Krylov descent law

The real-form obstruction behind the fixed Xi Cauchy probe is independent of zeta and of Hilbert
space estimates.  For any conjugation-stable family of nonzero spectral points and any nonreal
regular pole, one common sequence of real reciprocal polynomials recovers the conjugate-adjoint
Cauchy response pointwise exactly when every spectral point is real.  The reverse implication is
realized by the single polynomial `X ^ 2`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Value of a real reciprocal-Krylov polynomial at one Cauchy coordinate. -/
def universalCauchyRealKrylovValue
    (z a : ℂ) (p : Polynomial ℝ) : ℂ :=
  evalRealPolynomial p a⁻¹ * (a - z)⁻¹

/-- Conjugate-adjoint reciprocal-square response at one Cauchy coordinate. -/
def universalCauchyAdjointResponseValue (z a : ℂ) : ℂ :=
  ((starRingEnd ℂ) a)⁻¹ ^ 2 * ((starRingEnd ℂ) a - z)⁻¹

/-- Local two-coordinate seam forced by real polynomial coefficients. -/
def universalCauchyRealKrylovSeam
    (z a va vconj : ℂ) : ℂ :=
  ((starRingEnd ℂ) a - z) * vconj -
    ((starRingEnd ℂ) a - (starRingEnd ℂ) z) *
      (starRingEnd ℂ) va

/-- Every real reciprocal polynomial satisfies the universal seam. -/
theorem universalCauchyRealKrylovSeam_polynomial_eq_zero
    (z a : ℂ) (p : Polynomial ℝ)
    (haz : a - z ≠ 0)
    (hcaz : (starRingEnd ℂ) a - z ≠ 0) :
    universalCauchyRealKrylovSeam z a
      (universalCauchyRealKrylovValue z a p)
      (universalCauchyRealKrylovValue z ((starRingEnd ℂ) a) p) = 0 := by
  have hconjDen :
      (starRingEnd ℂ) a - (starRingEnd ℂ) z ≠ 0 := by
    rw [← map_sub]
    exact (map_ne_zero (starRingEnd ℂ)).2 haz
  have heval :
      evalRealPolynomial p ((starRingEnd ℂ) a)⁻¹ =
        (starRingEnd ℂ) (evalRealPolynomial p a⁻¹) := by
    rw [← map_inv₀, evalRealPolynomial_conj]
  unfold universalCauchyRealKrylovSeam universalCauchyRealKrylovValue
  rw [heval]
  simp only [map_inv₀, map_mul, map_sub]
  field_simp [hcaz, hconjDen]
  ring

private theorem universalCauchyRealKrylovSeam_response_algebra
    (a z : ℂ) (haz : a ≠ z)
    (haconjz : a ≠ (starRingEnd ℂ) z) :
    ((starRingEnd ℂ) a - z) * (a⁻¹ ^ 2 * (a - z)⁻¹) -
        ((starRingEnd ℂ) a - (starRingEnd ℂ) z) *
          (a⁻¹ ^ 2 * (a - (starRingEnd ℂ) z)⁻¹) =
      4 * a.im * z.im * a⁻¹ ^ 2 * (a - z)⁻¹ *
        (a - (starRingEnd ℂ) z)⁻¹ := by
  have hnum :
      ((starRingEnd ℂ) a - z) * (a - (starRingEnd ℂ) z) -
          ((starRingEnd ℂ) a - (starRingEnd ℂ) z) * (a - z) =
        4 * a.im * z.im := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring
  calc
    _ = a⁻¹ ^ 2 *
        ((((starRingEnd ℂ) a - z) * (a - (starRingEnd ℂ) z) -
            ((starRingEnd ℂ) a - (starRingEnd ℂ) z) * (a - z)) *
          ((a - z) * (a - (starRingEnd ℂ) z))⁻¹) := by
      rw [mul_inv_rev]
      have hd : (a - z) * (a - z)⁻¹ = 1 :=
        mul_inv_cancel₀ (sub_ne_zero.mpr haz)
      have he : (a - (starRingEnd ℂ) z) *
          (a - (starRingEnd ℂ) z)⁻¹ = 1 :=
        mul_inv_cancel₀ (sub_ne_zero.mpr haconjz)
      calc
        _ = a⁻¹ ^ 2 *
            (((starRingEnd ℂ) a - z) * (a - z)⁻¹ -
              ((starRingEnd ℂ) a - (starRingEnd ℂ) z) *
                (a - (starRingEnd ℂ) z)⁻¹) := by ring
        _ = a⁻¹ ^ 2 *
            (((starRingEnd ℂ) a - z) *
                ((a - (starRingEnd ℂ) z) *
                  (a - (starRingEnd ℂ) z)⁻¹) * (a - z)⁻¹ -
              ((starRingEnd ℂ) a - (starRingEnd ℂ) z) *
                ((a - z) * (a - z)⁻¹) *
                  (a - (starRingEnd ℂ) z)⁻¹) := by rw [hd, he]; ring
        _ = _ := by ring
    _ = _ := by
      rw [hnum, mul_inv_rev]
      ring

/-- Exact universal seam residual of the conjugate-adjoint response. -/
theorem universalCauchyRealKrylovSeam_adjointResponse_eq
    (z a : ℂ) (haz : a ≠ z)
    (haconjz : a ≠ (starRingEnd ℂ) z) :
    universalCauchyRealKrylovSeam z a
      (universalCauchyAdjointResponseValue z a)
      (universalCauchyAdjointResponseValue z ((starRingEnd ℂ) a)) =
      4 * a.im * z.im * a⁻¹ ^ 2 * (a - z)⁻¹ *
        (a - (starRingEnd ℂ) z)⁻¹ := by
  simp only [universalCauchyRealKrylovSeam,
    universalCauchyAdjointResponseValue, map_mul, map_inv₀, map_pow,
    Complex.conj_conj, map_sub]
  exact universalCauchyRealKrylovSeam_response_algebra a z haz haconjz

/-- Pointwise recovery of one conjugate-adjoint Cauchy response by one common sequence of real
reciprocal polynomials. -/
def UniversalCauchyRealKrylovPointwiseRecovery
    {ι : Type*} (z : ℂ) (a : ι → ℂ) : Prop :=
  ∃ p : ℕ → Polynomial ℝ, ∀ i,
    Tendsto (fun n => universalCauchyRealKrylovValue z (a i) (p n)) atTop
      (nhds (universalCauchyAdjointResponseValue z (a i)))

/-- **Universal pointwise real-descent rigidity.**  For a conjugation-stable nonzero family and
one nonreal regular pole, real reciprocal-Krylov recovery of the conjugate-adjoint response is
equivalent to every spectral point being real.  No discreteness, summability, or norm convergence
assumption is required. -/
theorem universalCauchyRealKrylovPointwiseRecovery_iff_all_real
    {ι : Type*} (z : ℂ) (a : ι → ℂ) (conjEquiv : ι ≃ ι)
    (hconj : ∀ i, a (conjEquiv i) = (starRingEnd ℂ) (a i))
    (ha : ∀ i, a i ≠ 0)
    (haz : ∀ i, a i - z ≠ 0)
    (hzim : z.im ≠ 0) :
    UniversalCauchyRealKrylovPointwiseRecovery z a ↔
      ∀ i, (a i).im = 0 := by
  constructor
  · rintro ⟨p, hp⟩ i
    have hpA := hp i
    have hpConj := hp (conjEquiv i)
    rw [hconj i] at hpConj
    have hcaz : (starRingEnd ℂ) (a i) - z ≠ 0 := by
      simpa only [hconj i] using haz (conjEquiv i)
    have haconjz : a i - (starRingEnd ℂ) z ≠ 0 := by
      intro hzero
      apply hcaz
      have hmap := congrArg (starRingEnd ℂ) hzero
      simpa using hmap
    have hseamLimit : Tendsto (fun n =>
        universalCauchyRealKrylovSeam z (a i)
          (universalCauchyRealKrylovValue z (a i) (p n))
          (universalCauchyRealKrylovValue z
            ((starRingEnd ℂ) (a i)) (p n))) atTop
        (nhds (universalCauchyRealKrylovSeam z (a i)
          (universalCauchyAdjointResponseValue z (a i))
          (universalCauchyAdjointResponseValue z
            ((starRingEnd ℂ) (a i))))) := by
      unfold universalCauchyRealKrylovSeam
      exact (tendsto_const_nhds.mul hpConj).sub
        (tendsto_const_nhds.mul
          (RCLike.continuous_conj.continuousAt.tendsto.comp hpA))
    have hseamZero : Tendsto (fun n =>
        universalCauchyRealKrylovSeam z (a i)
          (universalCauchyRealKrylovValue z (a i) (p n))
          (universalCauchyRealKrylovValue z
            ((starRingEnd ℂ) (a i)) (p n))) atTop (nhds 0) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun n =>
        (universalCauchyRealKrylovSeam_polynomial_eq_zero
          z (a i) (p n) (haz i) hcaz).symm
    have hseam : universalCauchyRealKrylovSeam z (a i)
        (universalCauchyAdjointResponseValue z (a i))
        (universalCauchyAdjointResponseValue z
          ((starRingEnd ℂ) (a i))) = 0 :=
      tendsto_nhds_unique hseamLimit hseamZero
    have hres := universalCauchyRealKrylovSeam_adjointResponse_eq
      z (a i) (sub_ne_zero.mp (haz i)) (sub_ne_zero.mp haconjz)
    rw [hseam] at hres
    have hrest :
        (4 : ℂ) * z.im * (a i)⁻¹ ^ 2 * (a i - z)⁻¹ *
          (a i - (starRingEnd ℂ) z)⁻¹ ≠ 0 := by
      apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · norm_num
            · exact_mod_cast hzim
          · exact pow_ne_zero 2 (inv_ne_zero (ha i))
        · exact inv_ne_zero (haz i)
      · exact inv_ne_zero haconjz
    have himul : ((a i).im : ℂ) *
        ((4 : ℂ) * z.im * (a i)⁻¹ ^ 2 * (a i - z)⁻¹ *
          (a i - (starRingEnd ℂ) z)⁻¹) = 0 := by
      calc
        _ = 4 * (a i).im * z.im * (a i)⁻¹ ^ 2 *
            (a i - z)⁻¹ * (a i - (starRingEnd ℂ) z)⁻¹ := by ring
        _ = 0 := hres.symm
    have himComplex : ((a i).im : ℂ) = 0 :=
      (mul_eq_zero.mp himul).resolve_right hrest
    exact_mod_cast himComplex
  · intro hreal
    refine ⟨fun _ => Polynomial.X ^ 2, fun i => ?_⟩
    have hconjA : (starRingEnd ℂ) (a i) = a i := by
      apply Complex.ext
      · simp
      · simp [hreal i]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun _ => by
      simp [universalCauchyRealKrylovValue,
        universalCauchyAdjointResponseValue, evalRealPolynomial, hconjA]

end

end RHTower
