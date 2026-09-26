import GaloisForLFunctions.RHTower.ThetaCuspQuadraticMeanSquare

/-!
# Compact mean-square control of the actual charged theta source

Identifies the full source along charged horizontal rays with damped quadratic
series, then transfers the quadratic frequency bound through the exponential
clock. Compact source energy is at most a fixed constant times `N^9`.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower.ThetaCuspBoundaryAudit

def chargedSeries (N k : ℕ) (u : ℝ) : ℂ :=
  ∑' n, gaussianQuadraticCoefficient (Real.pi/(N:ℝ)^2) (-2*Real.pi) k n*
    dampedQuadraticMode (Real.pi/(N:ℝ)^2) (-2*Real.pi) n u

theorem chargedSeries_continuousOn (N : ℕ) (hN : 0<N) (k : ℕ) :
    ContinuousOn (chargedSeries N k) (Ici 0) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<Real.pi/(N:ℝ)^2 := by positivity
  refine continuousOn_tsum ?_ (gaussianQuadraticCoefficient_summable ha (-2*Real.pi) k) ?_
  · intro n
    apply Continuous.continuousOn
    unfold dampedQuadraticMode
    fun_prop
  · intro n u hu
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (dampedQuadraticMode_norm_le ha.le (-2*Real.pi) n hu) (norm_nonneg _)

theorem chargedSeries_integral_le (N : ℕ) (hN : 0<N) {T : ℝ} (hT : 0≤T)
    (k : ℕ) (hk : 0<k) :
    (∫ u in (0:ℝ)..T, ‖chargedSeries N k u‖^2) ≤
      (T+(1/Real.pi)*quadraticRowConstant)*
        ((k.factorial:ℝ)/(2*Real.pi^k)*(N:ℝ)^(2*k+1)) := by
  have h := gaussianQuadraticSeries_integral_le N hN
    (b := -2*Real.pi) (by positivity) hT k hk
  have he : 2/|(-2*Real.pi)| = 1/Real.pi := by
    rw [abs_of_neg (by nlinarith only [Real.pi_pos])]
    ring
  simpa only [chargedSeries, he] using h

theorem exp_clock_nonneg {s : ℝ} (hs : 0 ≤ s) : 0≤Real.exp (2*s)-1 := by
  exact sub_nonneg.mpr (Real.one_le_exp (by positivity))

theorem chargedSeries_horizontal_integral_le (N : ℕ) (hN : 0<N)
    {S : ℝ} (hS : 0≤S) (k : ℕ) (hk : 0<k) :
    (∫ s in (0:ℝ)..S, ‖chargedSeries N k (Real.exp (2*s)-1)‖^2) ≤
      (Real.exp (2*S)-1+(1/Real.pi)*quadraticRowConstant)*
        ((k.factorial:ℝ)/(2*Real.pi^k)*(N:ℝ)^(2*k+1)) := by
  let u : ℝ → ℝ := fun s => Real.exp (2*s)-1
  let g : ℝ → ℝ := fun t => ‖chargedSeries N k t‖^2
  have hg : ContinuousOn g (Ici 0) := (chargedSeries_continuousOn N hN k).norm.pow 2
  have hu (s : ℝ) : HasDerivAt u (2*Real.exp (2*s)) s := by
    simpa [u, mul_comm] using (((hasDerivAt_id s).const_mul 2).exp.sub_const 1)
  have hgu : ContinuousOn (g ∘ u) (uIcc 0 S) := by
    apply hg.comp (by dsimp [u]; fun_prop)
    intro s hs
    rw [uIcc_of_le hS] at hs
    exact exp_clock_nonneg hs.1
  have hint : IntervalIntegrable (g ∘ u) volume 0 S := hgu.intervalIntegrable
  have hint2 : IntervalIntegrable (fun s => (g ∘ u) s*(2*Real.exp (2*s))) volume 0 S :=
    (hgu.mul (by fun_prop)).intervalIntegrable
  have hcv := intervalIntegral.integral_comp_mul_deriv' (fun s hs => hu s)
    (show ContinuousOn (fun s => 2*Real.exp (2*s)) (uIcc 0 S) by fun_prop)
    (hg.mono (by
      rintro t ⟨s, hs, rfl⟩
      rw [uIcc_of_le hS] at hs
      exact exp_clock_nonneg hs.1))
  calc
    _ ≤ ∫ s in (0:ℝ)..S, (g ∘ u) s*(2*Real.exp (2*s)) := by
      apply intervalIntegral.integral_mono_on hS hint hint2
      intro s hs
      have he : 1≤2*Real.exp (2*s) := by
        have h := Real.one_le_exp (show 0≤2*s by exact mul_nonneg (by norm_num) hs.1)
        linarith only [h]
      exact le_mul_of_one_le_right (sq_nonneg _) he
    _ = ∫ t in (0:ℝ)..(Real.exp (2*S)-1), ‖chargedSeries N k t‖^2 := by
      simpa [u, g] using hcv
    _ ≤ _ := chargedSeries_integral_le N hN (exp_clock_nonneg hS) k hk

theorem chargedSeries_term_eq (N : ℕ) (hN : 0<N) (k n : ℕ) (s : ℝ) :
    gaussianQuadraticCoefficient (Real.pi/(N:ℝ)^2) (-2*Real.pi) k n*
      dampedQuadraticMode (Real.pi/(N:ℝ)^2) (-2*Real.pi) n (Real.exp (2*s)-1) =
    (n:ℂ)^k*Complex.exp (-(Real.pi:ℂ)*
      ((n:ℂ)*Complex.exp (chargedPoint (1/(N:ℝ)^2)+(s:ℂ)))^2) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have he := chargedPoint_exp (show 0<1/(N:ℝ)^2 by positivity)
  have htwo : Complex.exp (2*(chargedPoint (1/(N:ℝ)^2)+(s:ℂ))) =
      (((1/(N:ℝ)^2:ℝ):ℂ)+2*Complex.I)*(Real.exp (2*s):ℂ) := by
    rw [mul_add, Complex.exp_add, he]
    congr 1
    norm_cast
  have hsq : ((n:ℂ)*Complex.exp (chargedPoint (1/(N:ℝ)^2)+(s:ℂ)))^2 =
      (n:ℂ)^2*((((1/(N:ℝ)^2:ℝ):ℂ)+2*Complex.I)*(Real.exp (2*s):ℂ)) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [htwo]
  unfold gaussianQuadraticCoefficient dampedQuadraticMode
  rw [mul_assoc, ← Complex.exp_add, hsq]
  congr 2
  push_cast
  ring


theorem chargedSource_series_identity (N : ℕ) (hN : 0<N) {s : ℝ} (hs : 0 ≤ s) :
    thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ)) =
      Complex.exp ((chargedPoint (1/(N:ℝ)^2)+(s:ℂ))/2)*
        (4*(Real.pi:ℂ)^2*((((1/(N:ℝ)^2:ℝ):ℂ)+2*Complex.I)*(Real.exp (2*s):ℂ))^2*
          chargedSeries N 4 (Real.exp (2*s)-1)-
        6*(Real.pi:ℂ)*((((1/(N:ℝ)^2:ℝ):ℂ)+2*Complex.I)*(Real.exp (2*s):ℂ))*
          chargedSeries N 2 (Real.exp (2*s)-1)) := by
  let z := chargedPoint (1/(N:ℝ)^2)+(s:ℂ)
  let Q : ℂ := (((1/(N:ℝ)^2:ℝ):ℂ)+2*Complex.I)*(Real.exp (2*s):ℂ)
  let F (k n : ℕ) := gaussianQuadraticCoefficient (Real.pi/(N:ℝ)^2) (-2*Real.pi) k n*
    dampedQuadraticMode (Real.pi/(N:ℝ)^2) (-2*Real.pi) n (Real.exp (2*s)-1)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have ha : 0<Real.pi/(N:ℝ)^2 := by positivity
  have hsum (k : ℕ) : Summable (F k) :=
    summable_dampedQuadraticMode (gaussianQuadraticCoefficient_summable ha (-2*Real.pi) k)
      ha.le _ (exp_clock_nonneg hs)
  have htwo : Complex.exp (2*z) = Q := by
    dsimp [z, Q]
    rw [mul_add, Complex.exp_add, chargedPoint_exp (by positivity)]
    congr 1
    norm_cast
  have hterm (n : ℕ) : thetaCuspComplexTerm z n = Complex.exp (z/2)*
      (4*(Real.pi:ℂ)^2*Q^2*F 4 n-6*(Real.pi:ℂ)*Q*F 2 n) := by
    dsimp only [F]
    rw [chargedSeries_term_eq N hN, chargedSeries_term_eq N hN]
    have hsq : ((n:ℂ)*Complex.exp z)^2 = (n:ℂ)^2*Q := by
      rw [mul_pow, ← Complex.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [htwo]
    have hfour : ((n:ℂ)*Complex.exp z)^4 = ((n:ℂ)^2*Q)^2 := by
      rw [← hsq]; ring
    unfold thetaCuspComplexTerm thetaCuspComplexSeed
    rw [hfour, hsq]
    ring
  change thetaCuspStripSource z = _
  unfold thetaCuspStripSource
  simp_rw [hterm]
  rw [tsum_mul_left, ((hsum 4).mul_left _).tsum_sub ((hsum 2).mul_left _),
    tsum_mul_left, tsum_mul_left]
  rfl



private theorem chargedPoint_parameters (N : ℕ) (hN : 0 < N) :
    0 < 1/(N:ℝ)^2 ∧ 1/(N:ℝ)^2 ≤ 1 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  exact ⟨by positivity, (div_le_one (by positivity)).mpr
    (one_le_pow₀ hN1)⟩

private theorem chargedSource_continuousOn (N : ℕ) (hN : 0 < N) (S : ℝ) :
    ContinuousOn (fun s : ℝ => thetaCuspStripSource
      (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))) (uIcc 0 S) := by
  apply differentiableOn_thetaCuspStripSource.continuousOn.comp (by fun_prop)
  intro s hs
  have hz := chargedPoint_mem_strip (chargedPoint_parameters N hN).1
  simpa only [thetaCuspStrip, mem_setOf_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hz

private theorem chargedSeries_clock_continuousOn (N : ℕ) (hN : 0 < N)
    (k : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    ContinuousOn (fun s : ℝ => chargedSeries N k (Real.exp (2*s)-1)) (uIcc 0 S) := by
  apply (chargedSeries_continuousOn N hN k).comp (by fun_prop)
  intro s hs
  rw [uIcc_of_le hS] at hs
  exact exp_clock_nonneg hs.1

private theorem chargedSource_compact_pointwise (S : ℝ) (N : ℕ) (hN : 0 < N)
    {s : ℝ} (hs : s ∈ Icc 0 S) :
    ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖ ≤
      (Real.exp ((1+S)/2)*(4*Real.pi^2*(3*Real.exp (2*S))^2+
        6*Real.pi*(3*Real.exp (2*S))))*
      (‖chargedSeries N 4 (Real.exp (2*s)-1)‖+
       ‖chargedSeries N 2 (Real.exp (2*s)-1)‖) := by
  let z := chargedPoint (1/(N:ℝ)^2)+(s:ℂ)
  let Q : ℂ := (((1/(N:ℝ)^2:ℝ):ℂ)+2*Complex.I)*(Real.exp (2*s):ℂ)
  let R := 3*Real.exp (2*S)
  let H := Real.exp ((1+S)/2)
  let A := 4*Real.pi^2*R^2
  let B := 6*Real.pi*R
  have hp := chargedPoint_parameters N hN
  have hq : ‖Q‖ ≤ R := by
    have hq0 : ‖(((1/(N:ℝ)^2:ℝ):ℂ)+2*Complex.I)‖ ≤ 3 := by
      calc
        _ ≤ ‖((1/(N:ℝ)^2:ℝ):ℂ)‖+‖(2:ℂ)*Complex.I‖ := norm_add_le _ _
        _ ≤ 3 := by
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1, norm_mul,
            Complex.norm_ofNat, Complex.norm_I, mul_one]
          linarith only [hp.2]
    dsimp [Q, R]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hq0 (Real.exp_le_exp.mpr (by linarith only [hs.2]))
      (by positivity) (by norm_num)
  have he : ‖Complex.exp (z/2)‖ ≤ H := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr := (chargedPoint_re_bounds hp.1 hp.2).2
    dsimp [z, H]
    simp only [Complex.div_ofNat_re, Complex.add_re, Complex.ofReal_re]
    linarith only [hr, hs.2]
  have ha : ‖4*(Real.pi:ℂ)^2*Q^2‖ ≤ A := by
    simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg Q) hq 2)
      (by positivity)
  have hb : ‖6*(Real.pi:ℂ)*Q‖ ≤ B := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B, R]; positivity
  have hH : 0 ≤ H := (Real.exp_pos _).le
  rw [chargedSource_series_identity N hN hs.1, norm_mul]
  change ‖Complex.exp (z/2)‖ *
    ‖4*(Real.pi:ℂ)^2*Q^2*chargedSeries N 4 (Real.exp (2*s)-1)-
      6*(Real.pi:ℂ)*Q*chargedSeries N 2 (Real.exp (2*s)-1)‖ ≤ _
  calc
    _ ≤ H*(A*‖chargedSeries N 4 (Real.exp (2*s)-1)‖+
      B*‖chargedSeries N 2 (Real.exp (2*s)-1)‖) := by
      apply mul_le_mul he _ (norm_nonneg _) hH
      exact (norm_sub_le _ _).trans (by
        simpa only [norm_mul] using add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
    _ ≤ _ := by
      change H*(A*_+B*_) ≤ H*(A+B)*(_+_)
      have hx := norm_nonneg (chargedSeries N 4 (Real.exp (2*s)-1))
      have hy := norm_nonneg (chargedSeries N 2 (Real.exp (2*s)-1))
      have hm : A*‖chargedSeries N 4 (Real.exp (2*s)-1)‖+
          B*‖chargedSeries N 2 (Real.exp (2*s)-1)‖ ≤
          (A+B)*(‖chargedSeries N 4 (Real.exp (2*s)-1)‖+
            ‖chargedSeries N 2 (Real.exp (2*s)-1)‖) := by
        rw [mul_add]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hx)
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hy)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm hH

/-- The actual charged source has compact horizontal energy of order at most `N^9`. -/
theorem chargedSource_compact_integral_le {S : ℝ} (hS : 0 ≤ S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 0 < N →
      (∫ s in (0:ℝ)..S, ‖thetaCuspStripSource
        (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖^2) ≤ B*(N:ℝ)^9 := by
  let C := Real.exp ((1+S)/2)*(4*Real.pi^2*(3*Real.exp (2*S))^2+
    6*Real.pi*(3*Real.exp (2*S)))
  let D := Real.exp (2*S)-1+(1/Real.pi)*quadraticRowConstant
  let E4 := (Nat.factorial 4:ℝ)/(2*Real.pi^4)
  let E2 := (Nat.factorial 2:ℝ)/(2*Real.pi^2)
  have hD : 0 ≤ D := add_nonneg (exp_clock_nonneg hS)
    (mul_nonneg (by positivity) quadraticRowConstant_nonneg)
  have hE2 : 0 ≤ E2 := by dsimp [E2]; positivity
  have hE4 : 0 ≤ E4 := by dsimp [E4]; positivity
  refine ⟨2*C^2*D*(E4+E2), by positivity, ?_⟩
  intro N hN
  let f4 := fun s : ℝ => ‖chargedSeries N 4 (Real.exp (2*s)-1)‖^2
  let f2 := fun s : ℝ => ‖chargedSeries N 2 (Real.exp (2*s)-1)‖^2
  have hi4 : IntervalIntegrable f4 volume 0 S :=
    ((chargedSeries_clock_continuousOn N hN 4 hS).norm.pow 2).intervalIntegrable
  have hi2 : IntervalIntegrable f2 volume 0 S :=
    ((chargedSeries_clock_continuousOn N hN 2 hS).norm.pow 2).intervalIntegrable
  have h4 := chargedSeries_horizontal_integral_le N hN hS 4 (by decide)
  have h2 := chargedSeries_horizontal_integral_le N hN hS 2 (by decide)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N:ℝ)^5 ≤ (N:ℝ)^9 := pow_le_pow_right₀ hN1 (by decide)
  have hsum : (∫ s in (0:ℝ)..S, f4 s)+(∫ s in (0:ℝ)..S, f2 s) ≤
      D*(E4+E2)*(N:ℝ)^9 := by
    change (∫ s in (0:ℝ)..S, f4 s) ≤ D*(E4*(N:ℝ)^9) at h4
    change (∫ s in (0:ℝ)..S, f2 s) ≤ D*(E2*(N:ℝ)^5) at h2
    have h2' := h2.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpow hE2) hD)
    calc
      _ ≤ D*(E4*(N:ℝ)^9)+D*(E2*(N:ℝ)^9) := add_le_add h4 h2'
      _ = _ := by
        rw [mul_add D E4 E2, add_mul (D*E4) (D*E2), mul_assoc D E4, mul_assoc D E2]
  calc
    _ ≤ ∫ s in (0:ℝ)..S, 2*C^2*(f4 s+f2 s) := by
      apply intervalIntegral.integral_mono_on hS
        ((chargedSource_continuousOn N hN S).norm.pow 2).intervalIntegrable
        ((hi4.add hi2).const_mul _)
      intro s hs
      have h := pow_le_pow_left₀ (norm_nonneg _) (chargedSource_compact_pointwise S N hN hs) 2
      rw [mul_pow] at h
      apply h.trans
      change C^2*(_+_)^2 ≤ 2*C^2*(_+_)
      have hsq : (‖chargedSeries N 4 (Real.exp (2*s)-1)‖+
          ‖chargedSeries N 2 (Real.exp (2*s)-1)‖)^2 ≤
          2*(f4 s+f2 s) := by
        exact add_sq_le
      simpa only [← mul_assoc, mul_comm (C^2) 2] using
        mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
    _ = 2*C^2*((∫ s in (0:ℝ)..S, f4 s)+(∫ s in (0:ℝ)..S, f2 s)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi4 hi2]
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*C^2 by positivity)

end RHTower.ThetaCuspBoundaryAudit
