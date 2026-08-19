import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicLogMoments

/-!
# The centered Fisher tangents and their exact dyadic split

`dyadic-squarefree-euler-fock-source-factorization`, §4.

The centered critical tangents of the card,

```text
chi_E  = c (L_E  − b_σ) e_σ,
chi_sq = c (L_sq − a_σ) s_σ,
r      = 2c (L_E − b_{2σ}) e_{2σ},
```

are honest `ℓ²` vectors for every `σ > 1`, orthogonal to their own pointed states, with squared
norms `c²·Var`, and the signed arithmetic unitary splits the Euler tangent exactly:

```text
U chi_E = chi_sq ⊗ e_{2σ} + s_σ ⊗ r.
```

The card's `(12)`–`(15)` are the specialization `c = −2ε`, `ε = σ − 1`.
-/

open Complex Set
open scoped InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Centered second moments -/

theorem summable_pnat_centered_sq {σ b : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ+ => (Real.log (n : ℝ) - b) ^ 2 * (n : ℝ) ^ (-σ)) := by
  have h2 := summable_pnat_logpow_rpow 2 hσ
  have h1 := summable_pnat_logpow_rpow 1 hσ
  have h0 := summable_pnat_logpow_rpow 0 hσ
  refine ((h2.sub (h1.mul_left (2 * b))).add (h0.mul_left (b ^ 2))).congr fun n => ?_
  simp only [pow_zero, pow_one, one_mul]
  ring

theorem summable_squarefree_centered_sq {σ b : ℝ} (hσ : 1 < σ) :
    Summable (fun d : SquarefreePNat =>
      (Real.log ((d.1 : ℝ)) - b) ^ 2 * ((d.1 : ℝ)) ^ (-σ)) :=
  (summable_pnat_centered_sq (b := b) hσ).comp_injective (fun _ _ hab => Subtype.ext hab)

theorem tsum_pnat_centered_sq {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ+, (Real.log (n : ℝ) - eulerLogMean σ) ^ 2 * (n : ℝ) ^ (-σ)
      = eulerMass σ * eulerLogVariance σ := by
  have hM : eulerMass σ ≠ 0 := ne_of_gt (eulerMass_pos hσ)
  have h2 := summable_pnat_logpow_rpow 2 hσ
  have h1 := summable_pnat_logpow_rpow 1 hσ
  have h0 := summable_pnat_logpow_rpow 0 hσ
  have hexp : ∀ n : ℕ+,
      (Real.log (n : ℝ) - eulerLogMean σ) ^ 2 * (n : ℝ) ^ (-σ)
        = Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (-σ)
          - 2 * eulerLogMean σ * (Real.log (n : ℝ) ^ 1 * (n : ℝ) ^ (-σ))
          + eulerLogMean σ ^ 2 * (Real.log (n : ℝ) ^ 0 * (n : ℝ) ^ (-σ)) := by
    intro n
    simp only [pow_zero, pow_one, one_mul]
    ring
  rw [tsum_congr hexp,
    ((h2.sub (h1.mul_left (2 * eulerLogMean σ))).tsum_add (h0.mul_left (eulerLogMean σ ^ 2))),
    (h2.tsum_sub (h1.mul_left (2 * eulerLogMean σ))), tsum_mul_left, tsum_mul_left]
  rw [← eulerLogPowMass, ← eulerLogPowMass, ← eulerLogPowMass, eulerLogPowMass_zero,
    eulerLogPowMass_one, eulerLogVariance, eulerLogMean]
  field_simp
  ring

theorem tsum_squarefree_centered_sq {σ : ℝ} (hσ : 1 < σ) :
    ∑' d : SquarefreePNat,
        (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) ^ 2 * ((d.1 : ℝ)) ^ (-σ)
      = squarefreeMass σ * squarefreeLogVariance σ := by
  have hM : squarefreeMass σ ≠ 0 := ne_of_gt (squarefreeMass_pos hσ)
  have h2 := summable_squarefree_logpow_rpow 2 hσ
  have h1 := summable_squarefree_logpow_rpow 1 hσ
  have h0 := summable_squarefree_logpow_rpow 0 hσ
  have hexp : ∀ d : SquarefreePNat,
      (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) ^ 2 * ((d.1 : ℝ)) ^ (-σ)
        = Real.log ((d.1 : ℝ)) ^ 2 * ((d.1 : ℝ)) ^ (-σ)
          - 2 * squarefreeLogMean σ * (Real.log ((d.1 : ℝ)) ^ 1 * ((d.1 : ℝ)) ^ (-σ))
          + squarefreeLogMean σ ^ 2 * (Real.log ((d.1 : ℝ)) ^ 0 * ((d.1 : ℝ)) ^ (-σ)) := by
    intro d
    simp only [pow_zero, pow_one, one_mul]
    ring
  rw [tsum_congr hexp,
    ((h2.sub (h1.mul_left (2 * squarefreeLogMean σ))).tsum_add
      (h0.mul_left (squarefreeLogMean σ ^ 2))),
    (h2.tsum_sub (h1.mul_left (2 * squarefreeLogMean σ))), tsum_mul_left, tsum_mul_left]
  rw [← squarefreeLogPowMass, ← squarefreeLogPowMass, ← squarefreeLogPowMass,
    squarefreeLogPowMass_zero, squarefreeLogPowMass_one, squarefreeLogVariance,
    squarefreeLogMean]
  field_simp
  ring

/-! ## The centered tangents -/

/-- Coordinates of the centered Euler tangent with scale `c`. -/
def eulerCenteredTangentCoord (c σ : ℝ) (n : ℕ+) : ℂ :=
  ((c * (Real.log (n : ℝ) - eulerLogMean σ) : ℝ) : ℂ) * eulerStateCoord σ n

/-- Coordinates of the centered signed squarefree tangent with scale `c`. -/
def squarefreeCenteredTangentCoord (c σ : ℝ) (d : SquarefreePNat) : ℂ :=
  ((c * (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) : ℝ) : ℂ) * squarefreeStateCoord σ d

theorem norm_eulerCenteredTangentCoord {σ : ℝ} (hσ : 1 < σ) (c : ℝ) (n : ℕ+) :
    ‖eulerCenteredTangentCoord c σ n‖ ^ (2 : ℕ)
      = c ^ 2 * ((Real.log (n : ℝ) - eulerLogMean σ) ^ 2 * (n : ℝ) ^ (-σ))
        * (eulerMass σ)⁻¹ := by
  rw [eulerCenteredTangentCoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    norm_eulerStateCoord hσ n]
  ring

theorem norm_squarefreeCenteredTangentCoord {σ : ℝ} (hσ : 1 < σ) (c : ℝ) (d : SquarefreePNat) :
    ‖squarefreeCenteredTangentCoord c σ d‖ ^ (2 : ℕ)
      = c ^ 2 * ((Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) ^ 2 * ((d.1 : ℝ)) ^ (-σ))
        * (squarefreeMass σ)⁻¹ := by
  rw [squarefreeCenteredTangentCoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, norm_squarefreeStateCoord hσ d]
  ring

theorem memlp_eulerCenteredTangentCoord {σ : ℝ} (hσ : 1 < σ) (c : ℝ) :
    Memℓp (eulerCenteredTangentCoord c σ) 2 := by
  refine memlp_two_of_summable_sq ?_
  refine (((summable_pnat_centered_sq (b := eulerLogMean σ) hσ).mul_left (c ^ 2)).mul_right
    (eulerMass σ)⁻¹).congr fun n => ?_
  rw [norm_eulerCenteredTangentCoord hσ c n]

theorem memlp_squarefreeCenteredTangentCoord {σ : ℝ} (hσ : 1 < σ) (c : ℝ) :
    Memℓp (squarefreeCenteredTangentCoord c σ) 2 := by
  refine memlp_two_of_summable_sq ?_
  refine (((summable_squarefree_centered_sq (b := squarefreeLogMean σ) hσ).mul_left
    (c ^ 2)).mul_right (squarefreeMass σ)⁻¹).congr fun d => ?_
  rw [norm_squarefreeCenteredTangentCoord hσ c d]

/-- The centered Euler tangent with scale `c`. -/
def eulerCenteredTangent (c : ℝ) {σ : ℝ} (hσ : 1 < σ) : EulerPositiveL2 :=
  ⟨eulerCenteredTangentCoord c σ, memlp_eulerCenteredTangentCoord hσ c⟩

@[simp] theorem eulerCenteredTangent_apply (c : ℝ) {σ : ℝ} (hσ : 1 < σ) (n : ℕ+) :
    eulerCenteredTangent c hσ n = eulerCenteredTangentCoord c σ n := rfl

/-- The centered signed squarefree tangent with scale `c`. -/
def squarefreeCenteredTangent (c : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    lp (fun _ : SquarefreePNat => ℂ) 2 :=
  ⟨squarefreeCenteredTangentCoord c σ, memlp_squarefreeCenteredTangentCoord hσ c⟩

@[simp] theorem squarefreeCenteredTangent_apply (c : ℝ) {σ : ℝ} (hσ : 1 < σ)
    (d : SquarefreePNat) :
    squarefreeCenteredTangent c hσ d = squarefreeCenteredTangentCoord c σ d := rfl

/-! ## Norms of the tangents -/

theorem normSq_eulerCenteredTangent (c : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    ‖eulerCenteredTangent c hσ‖ ^ 2 = c ^ 2 * eulerLogVariance σ := by
  have hM : eulerMass σ ≠ 0 := ne_of_gt (eulerMass_pos hσ)
  rw [lp_two_norm_sq_eq_tsum]
  have hterm : ∀ n : ℕ+, ‖eulerCenteredTangent c hσ n‖ ^ 2
      = ((Real.log (n : ℝ) - eulerLogMean σ) ^ 2 * (n : ℝ) ^ (-σ))
        * (c ^ 2 * (eulerMass σ)⁻¹) := by
    intro n
    have h := norm_eulerCenteredTangentCoord hσ c n
    have h' : ‖eulerCenteredTangent c hσ n‖ ^ (2 : ℕ)
        = c ^ 2 * ((Real.log (n : ℝ) - eulerLogMean σ) ^ 2 * (n : ℝ) ^ (-σ))
          * (eulerMass σ)⁻¹ := h
    rw [h']; ring
  rw [tsum_congr hterm, tsum_mul_right, tsum_pnat_centered_sq hσ]
  field_simp

theorem normSq_squarefreeCenteredTangent (c : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    ‖squarefreeCenteredTangent c hσ‖ ^ 2 = c ^ 2 * squarefreeLogVariance σ := by
  have hM : squarefreeMass σ ≠ 0 := ne_of_gt (squarefreeMass_pos hσ)
  rw [lp_two_norm_sq_eq_tsum]
  have hterm : ∀ d : SquarefreePNat, ‖squarefreeCenteredTangent c hσ d‖ ^ 2
      = ((Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) ^ 2 * ((d.1 : ℝ)) ^ (-σ))
        * (c ^ 2 * (squarefreeMass σ)⁻¹) := by
    intro d
    have h' : ‖squarefreeCenteredTangent c hσ d‖ ^ (2 : ℕ)
        = c ^ 2 * ((Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) ^ 2 * ((d.1 : ℝ)) ^ (-σ))
          * (squarefreeMass σ)⁻¹ := norm_squarefreeCenteredTangentCoord hσ c d
    rw [h']; ring
  rw [tsum_congr hterm, tsum_mul_right, tsum_squarefree_centered_sq hσ]
  field_simp

/-- Variances of the logarithm are nonnegative — read off the tangent norm at scale one. -/
theorem eulerLogVariance_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ eulerLogVariance σ := by
  have h := normSq_eulerCenteredTangent 1 hσ
  rw [one_pow, one_mul] at h
  rw [← h]
  positivity

theorem squarefreeLogVariance_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ squarefreeLogVariance σ := by
  have h := normSq_squarefreeCenteredTangent 1 hσ
  rw [one_pow, one_mul] at h
  rw [← h]
  positivity

/-! ## Centeredness `(14)` -/

theorem tsum_pnat_centered {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ+, (Real.log (n : ℝ) - eulerLogMean σ) * (n : ℝ) ^ (-σ) = 0 := by
  have hM : eulerMass σ ≠ 0 := ne_of_gt (eulerMass_pos hσ)
  have h1 := summable_pnat_logpow_rpow 1 hσ
  have h0 := summable_pnat_logpow_rpow 0 hσ
  have hexp : ∀ n : ℕ+, (Real.log (n : ℝ) - eulerLogMean σ) * (n : ℝ) ^ (-σ)
      = Real.log (n : ℝ) ^ 1 * (n : ℝ) ^ (-σ)
        - eulerLogMean σ * (Real.log (n : ℝ) ^ 0 * (n : ℝ) ^ (-σ)) := by
    intro n
    simp only [pow_zero, pow_one, one_mul]
    ring
  rw [tsum_congr hexp, h1.tsum_sub (h0.mul_left (eulerLogMean σ)), tsum_mul_left,
    ← eulerLogPowMass, ← eulerLogPowMass, eulerLogPowMass_zero, eulerLogPowMass_one,
    eulerLogMean]
  field_simp
  ring

theorem tsum_squarefree_centered {σ : ℝ} (hσ : 1 < σ) :
    ∑' d : SquarefreePNat,
      (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) * ((d.1 : ℝ)) ^ (-σ) = 0 := by
  have hM : squarefreeMass σ ≠ 0 := ne_of_gt (squarefreeMass_pos hσ)
  have h1 := summable_squarefree_logpow_rpow 1 hσ
  have h0 := summable_squarefree_logpow_rpow 0 hσ
  have hexp : ∀ d : SquarefreePNat,
      (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) * ((d.1 : ℝ)) ^ (-σ)
        = Real.log ((d.1 : ℝ)) ^ 1 * ((d.1 : ℝ)) ^ (-σ)
          - squarefreeLogMean σ * (Real.log ((d.1 : ℝ)) ^ 0 * ((d.1 : ℝ)) ^ (-σ)) := by
    intro d
    simp only [pow_zero, pow_one, one_mul]
    ring
  rw [tsum_congr hexp, h1.tsum_sub (h0.mul_left (squarefreeLogMean σ)), tsum_mul_left,
    ← squarefreeLogPowMass, ← squarefreeLogPowMass, squarefreeLogPowMass_zero,
    squarefreeLogPowMass_one, squarefreeLogMean]
  field_simp
  ring

/-- **Equation (14), Euler side.**  The centered Euler tangent is orthogonal to its own state. -/
theorem inner_eulerPointedState_eulerCenteredTangent (c : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (inner ℂ (eulerPointedState hσ) (eulerCenteredTangent c hσ) : ℂ) = 0 := by
  have hM : eulerMass σ ≠ 0 := ne_of_gt (eulerMass_pos hσ)
  have hterm : ∀ n : ℕ+,
      (inner ℂ (eulerPointedState hσ n) (eulerCenteredTangent c hσ n) : ℂ)
        = (((Real.log (n : ℝ) - eulerLogMean σ) * (n : ℝ) ^ (-σ)
            * (c * (eulerMass σ)⁻¹) : ℝ) : ℂ) := by
    intro n
    have hr2 : ((n : ℝ) ^ (-σ / 2) / Real.sqrt (eulerMass σ)) ^ 2
        = (n : ℝ) ^ (-σ) * (eulerMass σ)⁻¹ := by
      have h := norm_eulerStateCoord hσ n
      rwa [eulerStateCoord, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    show (inner ℂ (eulerStateCoord σ n) (eulerCenteredTangentCoord c σ n) : ℂ) = _
    rw [eulerCenteredTangentCoord, eulerStateCoord, RCLike.inner_apply, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hrw : (Real.log (n : ℝ) - eulerLogMean σ) * ((n : ℝ) ^ (-σ)) * (c * (eulerMass σ)⁻¹)
        = (c * (Real.log (n : ℝ) - eulerLogMean σ))
          * ((n : ℝ) ^ (-σ) * (eulerMass σ)⁻¹) := by ring
    rw [hrw, ← hr2]
    ring
  have hsum : HasSum
      (fun n : ℕ+ => (Real.log (n : ℝ) - eulerLogMean σ) * (n : ℝ) ^ (-σ)
        * (c * (eulerMass σ)⁻¹)) 0 := by
    have hs : Summable (fun n : ℕ+ => (Real.log (n : ℝ) - eulerLogMean σ) * (n : ℝ) ^ (-σ)) := by
      have h1 := summable_pnat_logpow_rpow 1 hσ
      have h0 := summable_pnat_logpow_rpow 0 hσ
      refine (h1.sub (h0.mul_left (eulerLogMean σ))).congr fun n => ?_
      simp only [pow_zero, pow_one, one_mul]
      ring
    have := (hs.hasSum.mul_right (c * (eulerMass σ)⁻¹))
    rwa [(hs.hasSum.tsum_eq).trans (tsum_pnat_centered hσ), zero_mul] at this
  have hcx := hsum.map (Complex.ofRealHom.toAddMonoidHom) Complex.continuous_ofReal
  rw [lp.inner_eq_tsum, tsum_congr hterm]
  simpa using hcx.tsum_eq

/-- **Equation (14), squarefree side.** -/
theorem inner_squarefreePointedState_squarefreeCenteredTangent (c : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (inner ℂ (squarefreePointedState hσ) (squarefreeCenteredTangent c hσ) : ℂ) = 0 := by
  have hM : squarefreeMass σ ≠ 0 := ne_of_gt (squarefreeMass_pos hσ)
  have hterm : ∀ d : SquarefreePNat,
      (inner ℂ (squarefreePointedState hσ d) (squarefreeCenteredTangent c hσ d) : ℂ)
        = (((Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) * ((d.1 : ℝ)) ^ (-σ)
            * (c * (squarefreeMass σ)⁻¹) : ℝ) : ℂ) := by
    intro d
    have hr2 : ((ArithmeticFunction.moebius (d.1 : ℕ) : ℝ)
          * ((d.1 : ℝ) ^ (-σ / 2) / Real.sqrt (squarefreeMass σ))) ^ 2
        = ((d.1 : ℝ)) ^ (-σ) * (squarefreeMass σ)⁻¹ := by
      have h := norm_squarefreeStateCoord hσ d
      rwa [squarefreeStateCoord, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    show (inner ℂ (squarefreeStateCoord σ d) (squarefreeCenteredTangentCoord c σ d) : ℂ) = _
    rw [squarefreeCenteredTangentCoord, squarefreeStateCoord, RCLike.inner_apply,
      Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hrw : (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) * (((d.1 : ℝ)) ^ (-σ))
          * (c * (squarefreeMass σ)⁻¹)
        = (c * (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ))
          * (((d.1 : ℝ)) ^ (-σ) * (squarefreeMass σ)⁻¹) := by ring
    rw [hrw, ← hr2]
    ring
  have hsum : HasSum
      (fun d : SquarefreePNat => (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ)
        * ((d.1 : ℝ)) ^ (-σ) * (c * (squarefreeMass σ)⁻¹)) 0 := by
    have hs : Summable (fun d : SquarefreePNat =>
        (Real.log ((d.1 : ℝ)) - squarefreeLogMean σ) * ((d.1 : ℝ)) ^ (-σ)) := by
      have h1 := summable_squarefree_logpow_rpow 1 hσ
      have h0 := summable_squarefree_logpow_rpow 0 hσ
      refine (h1.sub (h0.mul_left (squarefreeLogMean σ))).congr fun d => ?_
      simp only [pow_zero, pow_one, one_mul]
      ring
    have := (hs.hasSum.mul_right (c * (squarefreeMass σ)⁻¹))
    rwa [(hs.hasSum.tsum_eq).trans (tsum_squarefree_centered hσ), zero_mul] at this
  have hcx := hsum.map (Complex.ofRealHom.toAddMonoidHom) Complex.continuous_ofReal
  rw [lp.inner_eq_tsum, tsum_congr hterm]
  simpa using hcx.tsum_eq

/-! ## The tangent transport `(13)` -/

/-- **Equation (13), coordinate form.** -/
theorem dyadicSignedUnitary_eulerCenteredTangent_apply (c : ℝ) {σ : ℝ} (hσ : 1 < σ)
    (q : SquarefreePNat × ℕ+) :
    dyadicSquarefreeSignedUnitary (eulerCenteredTangent c hσ) q
      = squarefreeCenteredTangentCoord c σ q.1 * eulerStateCoord (2 * σ) q.2
        + squarefreeStateCoord σ q.1 * eulerCenteredTangentCoord (2 * c) (2 * σ) q.2 := by
  have hσ2 : 1 < 2 * σ := by linarith
  have hstate := dyadicSquarefreeSignedUnitary_eulerPointedState hσ q
  rw [dyadicSquarefreeSignedUnitary_apply, eulerPointedState_apply] at hstate
  have hlog := dyadicSquarefreeSquareEquiv_log (dyadicSquarefreeSquareEquiv.symm q)
  rw [Equiv.apply_symm_apply] at hlog
  have hmean := eulerLogMean_split hσ
  rw [dyadicSquarefreeSignedUnitary_apply, eulerCenteredTangent_apply, eulerCenteredTangentCoord,
    squarefreeCenteredTangentCoord, eulerCenteredTangentCoord]
  have hscalar : (c * (Real.log ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ)
        - eulerLogMean σ) : ℝ)
      = c * (Real.log ((q.1.1 : ℝ)) - squarefreeLogMean σ)
        + 2 * c * (Real.log ((q.2 : ℝ)) - eulerLogMean (2 * σ)) := by
    rw [hlog, hmean]; ring
  calc dyadicMoebiusPhase q
        * (((c * (Real.log ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ)
              - eulerLogMean σ) : ℝ) : ℂ)
          * eulerStateCoord σ (dyadicSquarefreeSquareEquiv.symm q))
      = ((c * (Real.log ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ)
              - eulerLogMean σ) : ℝ) : ℂ)
          * (dyadicMoebiusPhase q * eulerStateCoord σ (dyadicSquarefreeSquareEquiv.symm q)) := by
        ring
    _ = ((c * (Real.log ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ)
              - eulerLogMean σ) : ℝ) : ℂ)
          * (squarefreeStateCoord σ q.1 * eulerStateCoord (2 * σ) q.2) := by rw [hstate]
    _ = _ := by
        rw [hscalar]
        push_cast
        ring

/-- **Equation (13), vector form.**  `U χ_E = χ_sq ⊗ e_{2σ} + s_σ ⊗ r`. -/
theorem dyadicSignedUnitary_eulerCenteredTangent (c : ℝ) {σ : ℝ} (hσ : 1 < σ)
    (hσ2 : 1 < 2 * σ) :
    dyadicSquarefreeSignedUnitary (eulerCenteredTangent c hσ)
      = lpTensor (squarefreeCenteredTangent c hσ) (eulerPointedState hσ2)
        + lpTensor (squarefreePointedState hσ) (eulerCenteredTangent (2 * c) hσ2) := by
  refine lp.ext (funext fun q => ?_)
  have h := dyadicSignedUnitary_eulerCenteredTangent_apply c hσ q
  simpa using h

end RHTower
