import GaloisForLFunctions.RHTower.XiShiftedHardEdgeAngularNorm
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCosineParseval
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeModeContourShift

/-!
# The rational prime information cone

The Fourier transform of the square of the rational hard-edge test is the Cayley phase integral of a
squared cosine polynomial:

`∫_ℝ g_{a,p}(x)² e^{-iLx} dx = (a/2)·∫_{-π}^{π} q_{a,p}(θ)²·e^{-iaL·tan(θ/2)} dθ`.

The amplitude is entire and `2π`-periodic, so the contour shift applies, and the Chebyshev
coefficients bound its growth on the strip of depth `σ` by its own `L²` norm on the axis.  The
result is the coefficient-uniform cone

`|ĝ²(L)| ≤ 2(N+1)·e^{2Nσ}·e^{-aL(e^σ-1)/(e^σ+1)}·‖g_{a,p}‖₂²`,

valid at every depth `σ > 0` and every degree `N ≥ deg p`.  Scaled degree `N/a` therefore permits
only a bounded prime-log aperture, uniformly over every coefficient vector.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- The Fourier transform of the squared rational hard-edge test. -/
def routeUHardEdgeFourierSq (a : ℝ) (p : Polynomial ℝ) (L : ℝ) : ℂ :=
  ∫ x : ℝ, ((routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ)
    * Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I)

/-- The squared amplitude of the angular polynomial, as an entire function. -/
def routeUHardEdgeAngularAmplitude (a : ℝ) (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  (evalRealPolynomial (routeUHardEdgeAngularPoly a p) (Complex.cos z)) ^ (2 : ℕ)

theorem differentiable_routeUHardEdgeAngularAmplitude (a : ℝ) (p : Polynomial ℝ) :
    Differentiable ℂ (routeUHardEdgeAngularAmplitude a p) := by
  intro z
  have hcos : DifferentiableAt ℂ Complex.cos z := Complex.differentiable_cos z
  have hpoly : DifferentiableAt ℂ
      (fun w : ℂ => evalRealPolynomial (routeUHardEdgeAngularPoly a p) w)
      (Complex.cos z) := (Polynomial.differentiable _).differentiableAt
  exact (hpoly.comp z hcos).pow 2

theorem routeUHardEdgeAngularAmplitude_periodic (a : ℝ) (p : Polynomial ℝ) (z : ℂ) :
    routeUHardEdgeAngularAmplitude a p (z + ((2 * Real.pi : ℝ) : ℂ))
      = routeUHardEdgeAngularAmplitude a p z := by
  rw [routeUHardEdgeAngularAmplitude, routeUHardEdgeAngularAmplitude]
  congr 2
  rw [show ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) by push_cast; ring]
  exact Complex.cos_add_two_pi z

theorem routeUHardEdgeAngularAmplitude_ofReal (a : ℝ) (p : Polynomial ℝ) (θ : ℝ) :
    routeUHardEdgeAngularAmplitude a p (θ : ℂ)
      = (((routeUHardEdgeAngularPoly a p).eval (Real.cos θ) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [routeUHardEdgeAngularAmplitude, ← Complex.ofReal_cos, evalRealPolynomial_ofReal]
  push_cast
  ring

/-- **(CSHC.9) The angular form of the hard-edge Fourier transform.** -/
theorem routeUHardEdgeFourierSq_eq {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) (L : ℝ) :
    routeUHardEdgeFourierSq a p L
      = ((a / 2 : ℝ) : ℂ) * ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          routeUHardEdgeAngularAmplitude a p (θ : ℂ) * routeUCayleyPhase (a * L) (θ : ℂ) := by
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioo (-Real.pi) Real.pi)
    (f := routeUHardEdgeAngularChart a) (f' := routeUHardEdgeAngularJacobian a)
    measurableSet_Ioo
    (fun θ hθ => (hasDerivAt_routeUHardEdgeAngularChart
      (ne_of_gt (cos_half_pos_of_mem_Ioo hθ))).hasDerivWithinAt)
    (injOn_routeUHardEdgeAngularChart ha)
    (fun x : ℝ => ((routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ)
      * Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I))
  rw [image_routeUHardEdgeAngularChart ha, setIntegral_univ] at hchange
  rw [routeUHardEdgeFourierSq, hchange, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hcos := cos_half_pos_of_mem_Ioo hθ
  have hcosne : Real.cos (θ / 2) ≠ 0 := ne_of_gt hcos
  have hjac : |routeUHardEdgeAngularJacobian a θ| = a * (1 / Real.cos (θ / 2) ^ (2 : ℕ) * (1 / 2)) := by
    rw [routeUHardEdgeAngularJacobian, abs_of_pos (by positivity)]
  have hval : routeUHardEdgeRationalTest a p (routeUHardEdgeAngularChart a θ)
      = Real.cos (θ / 2) * (routeUHardEdgeAngularPoly a p).eval (Real.cos θ) :=
    routeUHardEdgeRationalTest_tan ha p hcos
  have hphase : Complex.exp ((((-(L * routeUHardEdgeAngularChart a θ)) : ℝ) : ℂ) * Complex.I)
      = routeUCayleyPhase (a * L) (θ : ℂ) := by
    rw [routeUCayleyPhase, routeUCayleyMobius_ofReal hcosne, routeUHardEdgeAngularChart]
    congr 1
    push_cast
    ring
  rw [Complex.real_smul, hjac, hval, hphase, routeUHardEdgeAngularAmplitude_ofReal]
  have hne : Real.cos (θ / 2) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hcosne
  have hscalar : ((a * (1 / Real.cos (θ / 2) ^ (2 : ℕ) * (1 / 2)) : ℝ) : ℂ)
      * (((Real.cos (θ / 2) * (routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ) : ℝ) : ℂ)
      = ((a / 2 : ℝ) : ℂ)
        * (((routeUHardEdgeAngularPoly a p).eval (Real.cos θ) ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [← mul_assoc, hscalar, mul_assoc]

/-- **The strip bound for the angular amplitude.**  Chebyshev coefficients turn a degree bound into
growth control off the axis in terms of the `L²` norm on the axis. -/
theorem norm_routeUHardEdgeAngularAmplitude_le {a : ℝ} (p : Polynomial ℝ) {N : ℕ}
    (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N) {σ : ℝ} (hσ : 0 < σ) {z : ℂ}
    (h1 : -σ ≤ z.im) (h2 : z.im ≤ 0) :
    ‖routeUHardEdgeAngularAmplitude a p z‖
      ≤ (Real.exp ((N : ℝ) * σ) ^ (2 : ℕ) * ((N : ℝ) + 1) / Real.pi)
          * ∫ θ in (-Real.pi)..Real.pi,
              ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ) := by
  obtain ⟨b, hb⟩ := exists_chebyshev_expansion N (routeUHardEdgeAngularPoly a p) hN
  have hcosPoly : ∀ θ : ℝ,
      (routeUHardEdgeAngularPoly a p).eval (Real.cos θ) = cosPoly N b θ := by
    intro θ
    rw [cosPoly]
    exact eval_cos_of_chebyshev_expansion hb θ
  have hI : Real.pi * ∑ j ∈ Finset.range (N + 1), b j ^ (2 : ℕ)
      ≤ ∫ θ in (-Real.pi)..Real.pi,
          ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_congr (g := fun θ : ℝ => cosPoly N b θ ^ (2 : ℕ))
      (fun θ _ => by rw [hcosPoly θ])]
    exact sum_sq_le_integral_cosPoly_sq N b
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ θ in (-Real.pi)..Real.pi,
      ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ) := ⟨_, rfl⟩
  rw [← hIdef] at hI ⊢
  have hsumsq : ∑ j ∈ Finset.range (N + 1), b j ^ (2 : ℕ) ≤ I / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [hI]
  have hsumsq0 : 0 ≤ ∑ j ∈ Finset.range (N + 1), b j ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hl1 : ∑ j ∈ Finset.range (N + 1), |b j|
      ≤ Real.sqrt ((N : ℝ) + 1) * Real.sqrt (I / Real.pi) := by
    refine le_trans (sum_abs_le_sqrt_card_mul N b) ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumsq) (Real.sqrt_nonneg _)
  have hstrip : ‖evalRealPolynomial (routeUHardEdgeAngularPoly a p) (Complex.cos z)‖
      ≤ Real.exp ((N : ℝ) * σ) * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt (I / Real.pi)) := by
    rw [show evalRealPolynomial (routeUHardEdgeAngularPoly a p) (Complex.cos z)
        = ((routeUHardEdgeAngularPoly a p).map (algebraMap ℝ ℂ)).eval (Complex.cos z) from rfl,
      eval_ccos_of_chebyshev_expansion hb z]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ j ∈ Finset.range (N + 1),
        ‖(b j : ℂ) * Complex.cos ((j : ℂ) * z)‖ ≤ Real.exp ((N : ℝ) * σ) * |b j| := by
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hcosz : ‖Complex.cos ((j : ℂ) * z)‖ ≤ Real.exp ((N : ℝ) * σ) := by
        refine le_trans (norm_ccos_le _) (Real.exp_le_exp.2 ?_)
        have him : ((j : ℂ) * z).im = (j : ℝ) * z.im := by
          simp [Complex.mul_im]
        rw [him, abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
        have habs : |z.im| ≤ σ := abs_le.2 ⟨h1, h2.trans hσ.le⟩
        have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hj
        nlinarith [abs_nonneg z.im, Nat.cast_nonneg (α := ℝ) j]
      calc |b j| * ‖Complex.cos ((j : ℂ) * z)‖ ≤ |b j| * Real.exp ((N : ℝ) * σ) :=
            mul_le_mul_of_nonneg_left hcosz (abs_nonneg _)
        _ = Real.exp ((N : ℝ) * σ) * |b j| := mul_comm _ _
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hl1 (Real.exp_nonneg _)
  have hI0 : 0 ≤ I := le_trans (by positivity) hI
  have hsq : Real.sqrt (I / Real.pi) ^ (2 : ℕ) = I / Real.pi :=
    Real.sq_sqrt (by positivity)
  have hcard : Real.sqrt ((N : ℝ) + 1) ^ (2 : ℕ) = (N : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  rw [routeUHardEdgeAngularAmplitude, norm_pow]
  calc ‖evalRealPolynomial (routeUHardEdgeAngularPoly a p) (Complex.cos z)‖ ^ (2 : ℕ)
      ≤ (Real.exp ((N : ℝ) * σ) * (Real.sqrt ((N : ℝ) + 1) * Real.sqrt (I / Real.pi))) ^ (2 : ℕ) := by
        exact pow_le_pow_left₀ (norm_nonneg _) hstrip 2
    _ = Real.exp ((N : ℝ) * σ) ^ (2 : ℕ) * ((N : ℝ) + 1) / Real.pi * I := by
        rw [mul_pow, mul_pow, hsq, hcard]
        field_simp

/-- **(CSHC.11) The rational prime information cone.**  Uniformly over every coefficient vector, the
Fourier transform of the squared hard-edge test decays exponentially in `aL` beyond an aperture set
by the scaled degree. -/
theorem norm_routeUHardEdgeFourierSq_le {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) {N : ℕ}
    (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N) {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 < σ) :
    ‖routeUHardEdgeFourierSq a p L‖
      ≤ (2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ (2 : ℕ)
            * Real.exp (-(a * L * routeUCayleyDecayRate σ)))
          * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ (2 : ℕ) := by
  obtain ⟨I, hIdef⟩ : ∃ I : ℝ, I = ∫ θ in (-Real.pi)..Real.pi,
      ((routeUHardEdgeAngularPoly a p).eval (Real.cos θ)) ^ (2 : ℕ) := ⟨_, rfl⟩
  have hcone := norm_integral_cayleyPhase_le
    (F := routeUHardEdgeAngularAmplitude a p)
    (differentiable_routeUHardEdgeAngularAmplitude a p)
    (routeUHardEdgeAngularAmplitude_periodic a p)
    (m := a * L) (σ := σ)
    (B := (Real.exp ((N : ℝ) * σ) ^ (2 : ℕ) * ((N : ℝ) + 1) / Real.pi) * I)
    (by positivity) hσ
    (fun z h1 h2 => by
      rw [hIdef]
      exact norm_routeUHardEdgeAngularAmplitude_le p hN hσ h1 h2)
  have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hFourier := routeUHardEdgeFourierSq_eq ha p L
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle] at hFourier
  rw [hFourier, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hnorm : ‖∫ θ in (-Real.pi)..Real.pi,
      routeUHardEdgeAngularAmplitude a p (θ : ℂ) * routeUCayleyPhase (a * L) (θ : ℂ)‖
      ≤ 2 * Real.pi * ((Real.exp ((N : ℝ) * σ) ^ (2 : ℕ) * ((N : ℝ) + 1) / Real.pi) * I
          * Real.exp (-(a * L * routeUCayleyDecayRate σ))) := hcone
  have hnormL2 : (∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ (2 : ℕ)) = a / 2 * I := by
    rw [integral_routeUHardEdgeRationalTest_sq ha p, hIdef,
      intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  rw [hnormL2]
  have hIpos : 0 ≤ I := by
    rw [hIdef, intervalIntegral.integral_of_le hle]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun θ _ => sq_nonneg _
  have hstep : a / 2 * (2 * Real.pi * ((Real.exp ((N : ℝ) * σ) ^ (2 : ℕ) * ((N : ℝ) + 1) / Real.pi) * I
        * Real.exp (-(a * L * routeUCayleyDecayRate σ))))
      = (2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ (2 : ℕ)
          * Real.exp (-(a * L * routeUCayleyDecayRate σ))) * (a / 2 * I) := by
    field_simp
  calc a / 2 * ‖∫ θ in (-Real.pi)..Real.pi,
        routeUHardEdgeAngularAmplitude a p (θ : ℂ) * routeUCayleyPhase (a * L) (θ : ℂ)‖
      ≤ a / 2 * (2 * Real.pi * ((Real.exp ((N : ℝ) * σ) ^ (2 : ℕ) * ((N : ℝ) + 1) / Real.pi) * I
          * Real.exp (-(a * L * routeUCayleyDecayRate σ)))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * σ) ^ (2 : ℕ)
          * Real.exp (-(a * L * routeUCayleyDecayRate σ))) * (a / 2 * I) := hstep

end RHTower

end
