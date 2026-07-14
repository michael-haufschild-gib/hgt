import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProuhetPacket
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailHaarResidualRankTwo

/-!
# Phase-adapted Prouhet packets

The two endpoint constraints in the theta-tail Prouhet packet control the critical decaying and
growing characters, while divisibility by `(X - 1)^m` annihilates every finite translation
polynomial below depth `m`.  Neither condition controls a prescribed off-diagonal logarithmic
phase.  This module inserts the real quadratic with roots `u` and `conj u` before performing the
same endpoint interpolation.

The resulting real signed packet simultaneously has:

* the two prescribed real endpoint values;
* the full Prouhet zero of order `m` at one; and
* an exact zero at the chosen complex phase `u` and its conjugate.

No sign, Xi zero, or limiting argument is used.  The only obstruction to using the packet at an
endpoint is the necessary resonance in which the chosen phase itself equals that endpoint.
-/

open Polynomial Complex

namespace RHTower

noncomputable section

/-- The real quadratic whose complex roots are `u` and `conj u`. -/
def conjugatePhaseRealQuadratic (u : ℂ) : ℝ[X] :=
  X ^ 2 - C (2 * u.re) * X + C (Complex.normSq u)

/-- Evaluation on the real line is the squared Euclidean distance from the chosen phase. -/
theorem conjugatePhaseRealQuadratic_eval_real (u : ℂ) (q : ℝ) :
    (conjugatePhaseRealQuadratic u).eval q =
      (q - u.re) ^ 2 + u.im ^ 2 := by
  simp [conjugatePhaseRealQuadratic, Complex.normSq_apply]
  ring

/-- A real endpoint is nonresonant whenever it is not the chosen complex phase. -/
theorem conjugatePhaseRealQuadratic_eval_pos
    (u : ℂ) (q : ℝ) (hphase : u ≠ (q : ℂ)) :
    0 < (conjugatePhaseRealQuadratic u).eval q := by
  rw [conjugatePhaseRealQuadratic_eval_real]
  have hne : q - u.re ≠ 0 ∨ u.im ≠ 0 := by
    by_contra h
    push Not at h
    apply hphase
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      linarith [h.1]
    · simp [h.2]
  rcases hne with hre | him
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hre) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero him)

/-- The chosen phase is an exact complex root after mapping the real quadratic to `ℂ`. -/
theorem conjugatePhaseRealQuadratic_map_eval_eq_zero (u : ℂ) :
    ((conjugatePhaseRealQuadratic u).map (algebraMap ℝ ℂ)).eval u = 0 := by
  have hre : (algebraMap ℝ ℂ) (2 * u.re) =
      u + (starRingEnd ℂ) u := by
    apply Complex.ext
    · simp
      ring
    · simp
  have hnorm : u * (starRingEnd ℂ) u =
      (algebraMap ℝ ℂ) (Complex.normSq u) := by
    simpa using Complex.mul_conj u
  simp only [conjugatePhaseRealQuadratic, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul,
    eval_sub, eval_add, eval_pow, eval_X, eval_C, eval_mul]
  rw [hre]
  calc
    u ^ 2 - (u + (starRingEnd ℂ) u) * u +
          (algebraMap ℝ ℂ) (Complex.normSq u) =
        (algebraMap ℝ ℂ) (Complex.normSq u) -
          u * (starRingEnd ℂ) u := by ring
    _ = 0 := by rw [hnorm]; ring

/-- Thue--Morse flatness with one prescribed conjugate phase pair inserted. -/
def phaseAdaptedProuhetBase (m : ℕ) (u : ℂ) : ℝ[X] :=
  thueMorseRealPolynomial m * conjugatePhaseRealQuadratic u

theorem phaseAdaptedProuhetBase_eval_ne_zero
    (m : ℕ) (u : ℂ) (q : ℝ)
    (hflat : (thueMorseRealPolynomial m).eval q ≠ 0)
    (hphase : u ≠ (q : ℂ)) :
    (phaseAdaptedProuhetBase m u).eval q ≠ 0 := by
  rw [phaseAdaptedProuhetBase, eval_mul]
  exact mul_ne_zero hflat
    (ne_of_gt (conjugatePhaseRealQuadratic_eval_pos u q hphase))

/-- Affine interpolation of the phase-adapted base at two real endpoint characters. -/
def phaseAdaptedTwoEndpointProuhetPolynomial
    (m : ℕ) (u : ℂ) (q r τ : ℝ) : ℝ[X] :=
  let B := phaseAdaptedProuhetBase m u
  let left := (B.eval q)⁻¹
  let right := τ * (B.eval r)⁻¹
  let β := (right - left) / (r - q)
  let α := left - β * q
  B * (C α + C β * X)

theorem phaseAdaptedTwoEndpointProuhetPolynomial_eval_left
    (m : ℕ) (u : ℂ) {q r τ : ℝ}
    (hBq : (phaseAdaptedProuhetBase m u).eval q ≠ 0) :
    (phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ).eval q = 1 := by
  let B := phaseAdaptedProuhetBase m u
  let left := (B.eval q)⁻¹
  let right := τ * (B.eval r)⁻¹
  let β := (right - left) / (r - q)
  let α := left - β * q
  have hlin : α + β * q = left := by simp only [α]; ring
  have hunit : B.eval q * left = 1 := by
    simpa only [B, left] using mul_inv_cancel₀ hBq
  change (B * (C α + C β * X)).eval q = 1
  rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_X, hlin, hunit]

theorem phaseAdaptedTwoEndpointProuhetPolynomial_eval_right
    (m : ℕ) (u : ℂ) {q r τ : ℝ}
    (hBr : (phaseAdaptedProuhetBase m u).eval r ≠ 0)
    (hsep : r - q ≠ 0) :
    (phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ).eval r = τ := by
  let B := phaseAdaptedProuhetBase m u
  let left := (B.eval q)⁻¹
  let right := τ * (B.eval r)⁻¹
  let β := (right - left) / (r - q)
  let α := left - β * q
  have hlin : α + β * r = right := by
    simp only [α, β]
    field_simp [hsep]
    ring
  have htarget : B.eval r * right = τ := by
    simp only [right, inv_eq_one_div]
    calc
      B.eval r * (τ * (1 / B.eval r)) = τ * (B.eval r / B.eval r) := by ring
      _ = τ := by rw [div_self (by simpa only [B] using hBr), mul_one]
  change (B * (C α + C β * X)).eval r = τ
  rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_X, hlin, htarget]

/-- Inserting the phase roots does not consume any of the order-`m` Prouhet flatness at one. -/
theorem X_sub_one_pow_dvd_phaseAdaptedTwoEndpointProuhetPolynomial
    (m : ℕ) (u : ℂ) (q r τ : ℝ) :
    (X - 1 : ℝ[X]) ^ m ∣
      phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ := by
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (X_sub_one_pow_dvd_thueMorseRealPolynomial m) _) _

/-- The completed packet still vanishes at the prescribed off-diagonal phase. -/
theorem phaseAdaptedTwoEndpointProuhetPolynomial_phaseRoot
    (m : ℕ) (u : ℂ) (q r τ : ℝ) :
    ((phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ).map
      (algebraMap ℝ ℂ)).eval u = 0 := by
  have hdiv : conjugatePhaseRealQuadratic u ∣
      phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ := by
    unfold phaseAdaptedTwoEndpointProuhetPolynomial phaseAdaptedProuhetBase
    dsimp only
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, Polynomial.map_mul, eval_mul,
    conjugatePhaseRealQuadratic_map_eval_eq_zero, zero_mul]

/-- Every ordinary translate-index moment below the Prouhet depth still vanishes. -/
theorem phaseAdaptedTwoEndpointProuhetPolynomial_power_moment_eq_zero
    (m : ℕ) (u : ℂ) (q r τ : ℝ) {k : ℕ} (hk : k < m) :
    ∑ i ∈ (phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ).support,
        (i : ℝ) ^ k *
          (phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ).coeff i = 0 := by
  exact GaloisForLFunctions.power_moment_eq_zero_of_sub_one_pow_dvd
    (X_sub_one_pow_dvd_phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ) hk

/-- The phase root is the exact vanishing of the corresponding finite exponential coefficient
packet. -/
theorem phaseAdaptedTwoEndpointProuhetPolynomial_exponential_sum_eq_zero
    (m : ℕ) (u : ℂ) (q r τ : ℝ) :
    ∑ i ∈ (phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ).support,
        ((phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ).coeff i : ℂ) * u ^ i = 0 := by
  have hroot := phaseAdaptedTwoEndpointProuhetPolynomial_phaseRoot m u q r τ
  simpa [eval_map, eval₂_eq_sum] using hroot

/-- A phase-adapted packet annihilates the entire real cosine coefficient packet on the selected
arithmetic fibre, including an arbitrary base shift. -/
theorem phaseAdaptedProuhet_cosine_sum_eq_zero
    (m : ℕ) (q r τ a L x : ℝ) :
    let u : ℂ := Complex.exp (((2 * L * x : ℝ) : ℂ) * I)
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ
    ∑ j ∈ P.support,
      P.coeff j * Real.cos (2 * (a + (j : ℝ) * L) * x) = 0 := by
  dsimp only
  let u : ℂ := Complex.exp (((2 * L * x : ℝ) : ℂ) * I)
  let v : ℂ := Complex.exp (((2 * a * x : ℝ) : ℂ) * I)
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ
  have hroot : ∑ j ∈ P.support, (P.coeff j : ℂ) * u ^ j = 0 := by
    simpa only [P] using
      phaseAdaptedTwoEndpointProuhetPolynomial_exponential_sum_eq_zero m u q r τ
  have hmul := congrArg Complex.re (congrArg (fun w : ℂ => v * w) hroot)
  dsimp only at hmul
  rw [mul_zero, map_zero] at hmul
  rw [Finset.mul_sum] at hmul
  simp only [map_sum, map_mul, Complex.ofReal_re] at hmul
  have hterm (j : ℕ) :
      (v * ((P.coeff j : ℂ) * u ^ j)).re =
        P.coeff j * Real.cos (2 * (a + (j : ℝ) * L) * x) := by
    have hphase : v * u ^ j =
        Complex.exp ((((2 * (a + (j : ℝ) * L) * x : ℝ) : ℂ) * I)) := by
      dsimp only [u, v]
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [show v * ((P.coeff j : ℂ) * u ^ j) =
        (P.coeff j : ℂ) * (v * u ^ j) by ring, hphase,
      Complex.exp_mul_I]
    simp
  simpa only [hterm] using hmul

/-- Exact phase-selective cancellation of the complete signed off-diagonal Hermitian current.
The opposite logarithmic drifts first cancel inside each cross, and the remaining rotated current
is then annihilated by the prescribed conjugate phase roots of the Prouhet symbol. -/
theorem phaseAdaptedProuhet_oppositeTranslationCross_sum_eq_zero
    (F F' : ℂ) (m : ℕ) (q r τ a L : ℝ) (z : ℂ) :
    let u : ℂ := Complex.exp (((2 * L * z.re : ℝ) : ℂ) * I)
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ
    ∑ j ∈ P.support, P.coeff j *
      ((spectralTranslationPhase (a + (j : ℝ) * L) z *
            (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) *
            (starRingEnd ℂ)
              (spectralTranslationPhase (-(a + (j : ℝ) * L)) z * F) +
          spectralTranslationPhase (-(a + (j : ℝ) * L)) z *
            (F' - (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) *
            (starRingEnd ℂ)
              (spectralTranslationPhase (a + (j : ℝ) * L) z * F))).im = 0 := by
  dsimp only
  let u : ℂ := Complex.exp (((2 * L * z.re : ℝ) : ℂ) * I)
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ
  have hcos := phaseAdaptedProuhet_cosine_sum_eq_zero m q r τ a L z.re
  dsimp only at hcos
  rw [show Complex.exp (((2 * L * z.re : ℝ) : ℂ) * I) = u by rfl] at hcos
  change ∑ j ∈ P.support, _ = 0
  rw [show (∑ j ∈ P.support, P.coeff j *
      ((spectralTranslationPhase (a + (j : ℝ) * L) z *
            (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) *
            (starRingEnd ℂ)
              (spectralTranslationPhase (-(a + (j : ℝ) * L)) z * F) +
          spectralTranslationPhase (-(a + (j : ℝ) * L)) z *
            (F' - (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) *
            (starRingEnd ℂ)
              (spectralTranslationPhase (a + (j : ℝ) * L) z * F))).im) =
      ∑ j ∈ P.support, P.coeff j *
        (2 * Real.cos (2 * (a + (j : ℝ) * L) * z.re) *
          (F' * (starRingEnd ℂ) F).im) by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hermitianCrossCurrent_spectralTranslationPhase]
  rw [← Finset.sum_mul]
  linear_combination 2 * (F' * (starRingEnd ℂ) F).im * hcos

/-- The symmetric value--derivative current between two transform vectors. -/
def symmetricHermitianCrossCurrentData
    (U U' E E' : ℂ) : ℝ :=
  (U' * (starRingEnd ℂ) E + E' * (starRingEnd ℂ) U).im

/-- Right-endpoint value which makes the general Prouhet seam current vanish at one prescribed
value--derivative fibre.  The factor `2^N` is the growing completion character at base depth `N`.
-/
def orientedProuhetSeamEndpoint
    (N : ℕ) (U U' E E' : ℂ) : ℝ :=
  (2 *
      (symmetricHermitianCrossCurrentData U U' E E' /
        (E' * (starRingEnd ℂ) E).im) - 1) /
    (2 : ℝ) ^ N

/-- The orientation-sensitive endpoint is exact: the completion-square coefficient becomes the
ratio which cancels the entire symmetric seam cross, without estimating either factor. -/
theorem orientedProuhetSeamEndpoint_cancels
    (N : ℕ) (U U' E E' : ℂ)
    (hE : (E' * (starRingEnd ℂ) E).im ≠ 0) :
    (((((2 : ℝ) ^ N * orientedProuhetSeamEndpoint N U U' E E' + 1) / 2) *
          (E' * (starRingEnd ℂ) E).im) -
        symmetricHermitianCrossCurrentData U U' E E') = 0 := by
  unfold orientedProuhetSeamEndpoint
  have hpow : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp [hpow, hE]
  ring

/-- Finite coefficient capstone.  Away from the two unavoidable endpoint resonances, one real
packet simultaneously preserves the left endpoint, takes the orientation-sensitive right
endpoint, retains every Prouhet moment below `m`, kills the selected logarithmic phase, and
cancels the associated seam current exactly. -/
theorem exists_phaseAdaptedProuhet_orientation_packet
    (m N : ℕ) (u : ℂ) (q r : ℝ) (U U' E E' : ℂ)
    (hflatq : (thueMorseRealPolynomial m).eval q ≠ 0)
    (hflatr : (thueMorseRealPolynomial m).eval r ≠ 0)
    (huq : u ≠ (q : ℂ)) (hur : u ≠ (r : ℂ))
    (hsep : r - q ≠ 0)
    (hE : (E' * (starRingEnd ℂ) E).im ≠ 0) :
    ∃ P : ℝ[X],
      P.eval q = 1 ∧
      P.eval r = orientedProuhetSeamEndpoint N U U' E E' ∧
      (X - 1 : ℝ[X]) ^ m ∣ P ∧
      (P.map (algebraMap ℝ ℂ)).eval u = 0 ∧
      (((((2 : ℝ) ^ N * P.eval r + 1) / 2) *
          (E' * (starRingEnd ℂ) E).im) -
        symmetricHermitianCrossCurrentData U U' E E') = 0 := by
  let τ := orientedProuhetSeamEndpoint N U U' E E'
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ
  have hBq := phaseAdaptedProuhetBase_eval_ne_zero m u q hflatq huq
  have hBr := phaseAdaptedProuhetBase_eval_ne_zero m u r hflatr hur
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · exact phaseAdaptedTwoEndpointProuhetPolynomial_eval_left m u hBq
  · exact phaseAdaptedTwoEndpointProuhetPolynomial_eval_right m u hBr hsep
  · exact X_sub_one_pow_dvd_phaseAdaptedTwoEndpointProuhetPolynomial m u q r τ
  · exact phaseAdaptedTwoEndpointProuhetPolynomial_phaseRoot m u q r τ
  · rw [phaseAdaptedTwoEndpointProuhetPolynomial_eval_right m u hBr hsep]
    exact orientedProuhetSeamEndpoint_cancels N U U' E E' hE

end

end RHTower
