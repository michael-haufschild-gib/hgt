import GaloisForLFunctions.RHTower.XiReciprocalTranslationSeamNormLaw
import GaloisForLFunctions.RHTower.PrimeSeamDampingAperture
import GaloisForLFunctions.RHTower.XiOuterEulerModulusPrimeSeamAntialignment
import GaloisForLFunctions.HTGeometry.GeneralDirichletLandau
import GaloisForLFunctions.HTGeometry.ClockSecondMoment

/-!
# One global Gamma--Meixner shape trace has a Landau boundary exactly off RH

The complete Xi divisor and the canonical prime seam define one nonnegative general Dirichlet
series in the archimedean Gamma convolution-time variable

`G(z) = Σ_p A_p exp(-z λ_p)`,   `λ_p = (1/2) log cosh (2 log p)`.

Its coefficients are finite, nonnegative, and vanish identically exactly under RH.  The series
converges for `Re z > 1`, while one off-critical divisor point makes it diverge at every small
positive real shape.  Landau's theorem for general Dirichlet series therefore converts holomorphic
continuation of the safe germ to the half plane `Re z > 0` into the Riemann hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The Gamma--Meixner frequency -/

/-- The archimedean Gamma-shape frequency of an integer scale. -/
def xiMeixnerFrequency (n : ℕ) : ℝ := (1 / 2) * Real.log (Real.cosh (2 * Real.log n))

theorem cosh_two_log_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 / 2 ≤ Real.cosh (2 * Real.log n) ∧
      Real.cosh (2 * Real.log n) ≤ (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hn0]
    norm_num
  have hexpneg : Real.exp (-(2 * Real.log n)) = ((n : ℝ) ^ 2)⁻¹ := by
    rw [Real.exp_neg, hexp]
  have hcosh : Real.cosh (2 * Real.log n) =
      ((n : ℝ) ^ 2 + ((n : ℝ) ^ 2)⁻¹) / 2 := by
    rw [Real.cosh_eq, hexp, hexpneg]
  have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hinv : ((n : ℝ) ^ 2)⁻¹ ≤ (n : ℝ) ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith
  have hinvpos : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
  constructor <;> rw [hcosh] <;> linarith

theorem xiMeixnerFrequency_nonneg (n : ℕ) : 0 ≤ xiMeixnerFrequency n := by
  rw [xiMeixnerFrequency]
  have h := Real.one_le_cosh (2 * Real.log n)
  have := Real.log_nonneg h
  linarith

theorem exp_neg_xiMeixnerFrequency_eq (n : ℕ) (θ : ℝ) :
    Real.exp (-(θ * xiMeixnerFrequency n)) =
      Real.cosh (2 * Real.log n) ^ (-(θ / 2)) := by
  have hpos : (0 : ℝ) < Real.cosh (2 * Real.log n) := Real.cosh_pos _
  rw [Real.rpow_def_of_pos hpos, xiMeixnerFrequency]
  congr 1
  ring

theorem rpow_le_exp_neg_xiMeixnerFrequency {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) :
    (n : ℝ) ^ (-θ) ≤ Real.exp (-(θ * xiMeixnerFrequency n)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨_, hupper⟩ := cosh_two_log_bounds hn
  have hpos : (0 : ℝ) < Real.cosh (2 * Real.log n) := Real.cosh_pos _
  rw [exp_neg_xiMeixnerFrequency_eq]
  have hmono : Real.cosh (2 * Real.log n) ^ (-(θ / 2)) ≥ ((n : ℝ) ^ 2) ^ (-(θ / 2)) :=
    Real.rpow_le_rpow_of_nonpos hpos hupper (by linarith)
  have hsq : ((n : ℝ) ^ 2) ^ (-(θ / 2)) = (n : ℝ) ^ (-θ) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  rw [hsq] at hmono
  exact hmono

theorem exp_neg_xiMeixnerFrequency_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.exp (-(θ * xiMeixnerFrequency n)) ≤ (2 : ℝ) ^ (θ / 2) * (n : ℝ) ^ (-θ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hlower, _⟩ := cosh_two_log_bounds hn
  have hhalfpos : (0 : ℝ) < (n : ℝ) ^ 2 / 2 := by positivity
  rw [exp_neg_xiMeixnerFrequency_eq]
  have hmono : Real.cosh (2 * Real.log n) ^ (-(θ / 2)) ≤ ((n : ℝ) ^ 2 / 2) ^ (-(θ / 2)) :=
    Real.rpow_le_rpow_of_nonpos hhalfpos hlower (by linarith)
  have hsq : ((n : ℝ) ^ 2) ^ (-(θ / 2)) = (n : ℝ) ^ (-θ) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  have hsplit : ((n : ℝ) ^ 2 / 2) ^ (-(θ / 2)) = (2 : ℝ) ^ (θ / 2) * (n : ℝ) ^ (-θ) := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (θ / 2) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.div_rpow (by positivity) (by norm_num), hsq,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  rw [hsplit] at hmono
  exact hmono

/-! ## The global divisor coefficients -/

theorem xiSeamDivisorCoefficient_nonneg (n : ℕ) : 0 ≤ xiSeamDivisorCoefficient n :=
  tsum_nonneg (fun q => by positivity)

theorem norm_orbitwiseNatPrimeSeamCharge_sq_le {n : ℕ} (hn : 1 < n) (q : XiZeroCopy) :
    ‖orbitwiseNatPrimeSeamCharge n ((q.1 : ℂ))‖ ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := xiZeroCopy_re_mem_open_unit q
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR.le
  rw [orbitwiseNatPrimeSeamCharge_eq_character_mul_amplitude hn, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, Complex.norm_exp,
    Complex.norm_real, Real.norm_eq_abs]
  have hchar : (Complex.I * (((((q.1 : ℂ)).im * Real.log (n : ℝ) : ℝ)) : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  rw [hchar, Real.exp_zero, mul_one]
  have hamp : |primeClockReflectionAmplitude ((q.1 : ℂ)).re n| ≤ 1 := by
    rw [primeClockReflectionAmplitude, abs_le]
    have h1 : (n : ℝ) ^ (-((q.1 : ℂ)).re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnR.le (by linarith)
    have h2 : (n : ℝ) ^ (-(1 - ((q.1 : ℂ)).re)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnR.le (by linarith)
    have h3 : (0 : ℝ) < (n : ℝ) ^ (-((q.1 : ℂ)).re) := Real.rpow_pos_of_pos (by linarith) _
    have h4 : (0 : ℝ) < (n : ℝ) ^ (-(1 - ((q.1 : ℂ)).re)) := Real.rpow_pos_of_pos (by linarith) _
    constructor <;> linarith
  have hsq : |primeClockReflectionAmplitude ((q.1 : ℂ)).re n| ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (primeClockReflectionAmplitude ((q.1 : ℂ)).re n)]
  have hexp : (Real.log (n : ℝ) * |primeClockReflectionAmplitude ((q.1 : ℂ)).re n|) ^ 2 =
      (Real.log (n : ℝ)) ^ 2 * |primeClockReflectionAmplitude ((q.1 : ℂ)).re n| ^ 2 := by ring
  rw [hexp]
  nlinarith [sq_nonneg (Real.log (n : ℝ))]

theorem xiSeamDivisorCoefficient_le {n : ℕ} (hn : 1 < n) :
    xiSeamDivisorCoefficient n ≤ (Real.log (n : ℝ)) ^ 2 * xiReciprocalHermitianMass := by
  rw [xiSeamDivisorCoefficient, xiReciprocalHermitianMass, ← tsum_mul_left]
  refine (summable_seamDivisorTerm hn).tsum_mono
    (((summable_norm_xiSpectralPoint_inv_sq).mul_left _)) (fun q => ?_)
  have hden : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by
    have := xiSpectralPoint_ne_zero q
    positivity
  have hne : ‖xiSpectralPoint q‖ ≠ 0 := norm_ne_zero_iff.mpr (xiSpectralPoint_ne_zero q)
  rw [div_le_iff₀ hden]
  have hinv : ‖xiReciprocalCoordinate q‖ ^ 2 = 1 / ‖xiSpectralPoint q‖ ^ 2 := by
    rw [xiReciprocalCoordinate, norm_inv, inv_pow, one_div]
  rw [hinv]
  have hbound := norm_orbitwiseNatPrimeSeamCharge_sq_le hn q
  field_simp
  exact hbound

/-! ## The global Gamma--Meixner shape trace -/

/-- The global seam coefficient at a prime scale. -/
def xiGammaShapeCoefficient (p : Nat.Primes) : ℝ := xiSeamDivisorCoefficient (p : ℕ)

/-- The Gamma--Meixner frequency at a prime scale. -/
def xiGammaShapeFrequency (p : Nat.Primes) : ℝ := xiMeixnerFrequency (p : ℕ)

/-- The one global Gamma-shape trace of the Xi divisor. -/
def xiGammaShapeTrace (s : ℂ) : ℂ :=
  GaloisForLFunctions.HTGeometry.gdSeries xiGammaShapeCoefficient xiGammaShapeFrequency s

theorem xiGammaShapeCoefficient_nonneg (p : Nat.Primes) : 0 ≤ xiGammaShapeCoefficient p :=
  xiSeamDivisorCoefficient_nonneg _

theorem xiGammaShapeFrequency_nonneg (p : Nat.Primes) : 0 ≤ xiGammaShapeFrequency p :=
  xiMeixnerFrequency_nonneg _

/-! ## Convergence on the safe shape half plane -/

theorem summable_logSq_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (Real.log n ^ 2 * (1 : ℝ)) * (n : ℝ) ^ (-σ)) := by
  apply GaloisForLFunctions.HTGeometry.summable_logSq_mul_rpow (σ := σ) (g := fun _ => 1)
  have h : (fun n : ℕ => (((1 : ℝ) : ℝ) : ℂ)) = (1 : ℕ → ℂ) := by funext n; simp
  rw [h, LSeries.abscissaOfAbsConv_one]
  simp only [Complex.ofReal_re]
  exact_mod_cast hσ

/-- **Safe convergence.**  The global Gamma-shape trace converges absolutely at every real shape
above one. -/
theorem summable_xiGammaShapeTwist {σ : ℝ} (hσ : 1 < σ) :
    Summable (GaloisForLFunctions.HTGeometry.gdTwistTerm
      xiGammaShapeCoefficient xiGammaShapeFrequency σ 0) := by
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hmaj : Summable (fun p : Nat.Primes =>
      (2 : ℝ) ^ (σ / 2) * xiReciprocalHermitianMass *
        ((Real.log (p : ℕ) ^ 2 * (1 : ℝ)) * ((p : ℕ) : ℝ) ^ (-σ))) :=
    (((summable_logSq_rpow hσ).subtype {p : ℕ | p.Prime}).mul_left _)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmaj
  · exact GaloisForLFunctions.HTGeometry.gdTwistTerm_nonneg
      xiGammaShapeCoefficient_nonneg xiGammaShapeFrequency_nonneg σ 0 p
  · have hp1 : 1 < (p : ℕ) := p.prop.one_lt
    have hple := xiSeamDivisorCoefficient_le hp1
    have hexp := exp_neg_xiMeixnerFrequency_le (le_of_lt hp1) hσ0
    have hexpnn : 0 ≤ Real.exp (-(σ * xiMeixnerFrequency (p : ℕ))) := (Real.exp_pos _).le
    have hMnn : 0 ≤ xiReciprocalHermitianMass := by
      rw [xiReciprocalHermitianMass]
      exact tsum_nonneg (fun q => by positivity)
    rw [GaloisForLFunctions.HTGeometry.gdTwistTerm, pow_zero, mul_one,
      xiGammaShapeCoefficient, xiGammaShapeFrequency]
    calc xiSeamDivisorCoefficient (p : ℕ) * Real.exp (-(σ * xiMeixnerFrequency (p : ℕ)))
        ≤ (Real.log ((p : ℕ) : ℝ) ^ 2 * xiReciprocalHermitianMass) *
            ((2 : ℝ) ^ (σ / 2) * ((p : ℕ) : ℝ) ^ (-σ)) := by
          apply mul_le_mul hple hexp hexpnn
          positivity
      _ = (2 : ℝ) ^ (σ / 2) * xiReciprocalHermitianMass *
            ((Real.log ((p : ℕ) : ℝ) ^ 2 * (1 : ℝ)) * ((p : ℕ) : ℝ) ^ (-σ)) := by ring

theorem summable_xiGammaShapeTwist_two :
    Summable (GaloisForLFunctions.HTGeometry.gdTwistTerm
      xiGammaShapeCoefficient xiGammaShapeFrequency 2 0) :=
  summable_xiGammaShapeTwist (by norm_num)

/-! ## Divergence forced by one off-line divisor point -/

theorem not_summable_xiGammaShapeTwist_of_offLine {q₀ : XiZeroCopy}
    (hoff : ((q₀.1 : ℂ)).re ≠ 1 / 2) :
    ¬ Summable (GaloisForLFunctions.HTGeometry.gdTwistTerm
      xiGammaShapeCoefficient xiGammaShapeFrequency
      (|2 * ((q₀.1 : ℂ)).re - 1| / 2) 0) := by
  intro hcon
  set σ₀ : ℝ := ((q₀.1 : ℂ)).re with hσ₀
  set δ : ℝ := |2 * σ₀ - 1| with hδ
  have hδpos : 0 < δ := by
    rw [hδ, abs_pos]
    intro h
    apply hoff
    linarith
  set θ : ℝ := δ / 2 with hθ
  set θ' : ℝ := 3 * δ / 4 with hθ'
  have hθpos : 0 < θ := by rw [hθ]; linarith
  have hθ'lt : θ' < δ := by rw [hθ']; linarith
  have hnormpos : (0 : ℝ) < ‖xiSpectralPoint q₀‖ ^ 2 := by
    have := xiSpectralPoint_ne_zero q₀
    positivity
  set c : ℝ := (Real.log 2) ^ 2 / ‖xiSpectralPoint q₀‖ ^ 2 with hc
  have hcpos : 0 < c := by
    rw [hc]
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hdiv : ¬ Summable (weightedPrimeClockReflectionEnergy θ' σ₀) := by
    rw [summable_weightedPrimeClockReflectionEnergy_iff]
    push Not
    refine ⟨fun h => hoff h, ?_⟩
    rw [← hδ]
    linarith
  apply hdiv
  have hlow : ∀ p : Nat.Primes,
      c * weightedPrimeClockReflectionEnergy θ' σ₀ p ≤
        GaloisForLFunctions.HTGeometry.gdTwistTerm
          xiGammaShapeCoefficient xiGammaShapeFrequency θ 0 p := by
    intro p
    have hp1 : 1 < (p : ℕ) := p.prop.one_lt
    have hpR : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp1
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
    -- one term of the divisor sum
    have hterm : ‖orbitwiseNatPrimeSeamCharge (p : ℕ) ((q₀.1 : ℂ))‖ ^ 2 /
        ‖xiSpectralPoint q₀‖ ^ 2 ≤ xiSeamDivisorCoefficient (p : ℕ) :=
      (summable_seamDivisorTerm hp1).le_tsum q₀ (fun j _ => by positivity)
    have hseam : ‖orbitwiseNatPrimeSeamCharge (p : ℕ) ((q₀.1 : ℂ))‖ ^ 2 =
        (Real.log ((p : ℕ) : ℝ)) ^ 2 * primeClockReflectionEnergy σ₀ p :=
      norm_sq_orbitwiseNatPrimeSeamCharge_eq_log_sq_mul_primeClockReflectionEnergy _ p
    have hexp : ((p : ℕ) : ℝ) ^ (-θ) ≤ Real.exp (-(θ * xiMeixnerFrequency (p : ℕ))) :=
      rpow_le_exp_neg_xiMeixnerFrequency (le_of_lt hp1) hθpos.le
    have henergy : 0 ≤ primeClockReflectionEnergy σ₀ p := sq_nonneg _
    have hlogp : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hp2
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpowcmp : ((p : ℕ) : ℝ) ^ (-θ') ≤ ((p : ℕ) : ℝ) ^ (-θ) := by
      apply Real.rpow_le_rpow_of_exponent_le hpR.le
      rw [hθ, hθ']
      linarith
    have hlogcmp : (Real.log 2) ^ 2 ≤ (Real.log ((p : ℕ) : ℝ)) ^ 2 := by nlinarith
    calc c * weightedPrimeClockReflectionEnergy θ' σ₀ p
        = ((Real.log 2) ^ 2 * primeClockReflectionEnergy σ₀ p / ‖xiSpectralPoint q₀‖ ^ 2) *
            ((p : ℕ) : ℝ) ^ (-θ') := by
          rw [hc, weightedPrimeClockReflectionEnergy]
          ring
      _ ≤ (((Real.log ((p : ℕ) : ℝ)) ^ 2 * primeClockReflectionEnergy σ₀ p) /
            ‖xiSpectralPoint q₀‖ ^ 2) * ((p : ℕ) : ℝ) ^ (-θ) := by
          apply mul_le_mul _ hpowcmp (Real.rpow_nonneg (by linarith) _) (by positivity)
          refine (div_le_div_iff_of_pos_right hnormpos).mpr ?_
          nlinarith
      _ ≤ xiSeamDivisorCoefficient (p : ℕ) *
            Real.exp (-(θ * xiMeixnerFrequency (p : ℕ))) := by
          apply mul_le_mul _ hexp (Real.rpow_nonneg (by linarith) _)
            (xiSeamDivisorCoefficient_nonneg _)
          rw [← hseam]
          exact hterm
      _ = GaloisForLFunctions.HTGeometry.gdTwistTerm
            xiGammaShapeCoefficient xiGammaShapeFrequency θ 0 p := by
          rw [GaloisForLFunctions.HTGeometry.gdTwistTerm, pow_zero, mul_one,
            xiGammaShapeCoefficient, xiGammaShapeFrequency]
  have hscaled : Summable (fun p : Nat.Primes =>
      c * weightedPrimeClockReflectionEnergy θ' σ₀ p) :=
    Summable.of_nonneg_of_le (fun p => by
      have := sq_nonneg ((((p : ℕ) : ℝ)) ^ (-σ₀) - (((p : ℕ) : ℝ)) ^ (-(1 - σ₀)))
      rw [weightedPrimeClockReflectionEnergy, primeClockReflectionEnergy]
      have hpp : (0 : ℝ) < ((p : ℕ) : ℝ) := by
        have := p.prop.pos
        exact_mod_cast this
      positivity) hlow hcon
  have := hscaled.mul_left c⁻¹
  refine this.congr (fun p => ?_)
  rw [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]

/-! ## The Landau criterion -/

/-- **The Gamma--Meixner shape Landau criterion.**  Holomorphic continuation of the safe germ to
the half plane `Re z > 0` is the Riemann hypothesis. -/
theorem riemannHypothesis_of_xiGammaShapeTrace_continuation
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s : ℂ | 0 < s.re})
    (hagree : ∀ s : ℂ, 1 < s.re → G s = xiGammaShapeTrace s) :
    RiemannHypothesis := by
  by_contra hcon
  rw [xiSpectralPoint_im_eq_zero_iff_rh] at hcon
  push Not at hcon
  obtain ⟨q₀, hq₀⟩ := hcon
  have hoff : ((q₀.1 : ℂ)).re ≠ 1 / 2 := by
    intro h
    apply hq₀
    rw [xiSpectralPoint_im_eq, h]
    ring
  have hδpos : 0 < |2 * ((q₀.1 : ℂ)).re - 1| / 2 := by
    have : |2 * ((q₀.1 : ℂ)).re - 1| ≠ 0 := by
      rw [abs_ne_zero]
      intro h
      exact hoff (by linarith)
    have := abs_nonneg (2 * ((q₀.1 : ℂ)).re - 1)
    positivity
  apply not_summable_xiGammaShapeTwist_of_offLine hoff
  refine GaloisForLFunctions.HTGeometry.general_landau_summable_of_halfPlane_analytic
    xiGammaShapeCoefficient_nonneg xiGammaShapeFrequency_nonneg
    summable_xiGammaShapeTwist_two (by norm_num) hGd (fun s hs => hagree s (by linarith)) hδpos

theorem xiGammaShapeCoefficient_eq_zero_of_rh (hRH : RiemannHypothesis) (p : Nat.Primes) :
    xiGammaShapeCoefficient p = 0 :=
  (xiSeamDivisorCoefficient_eq_zero_iff_rh p.prop.one_lt).mpr hRH

theorem xiGammaShapeTrace_eq_zero_of_rh (hRH : RiemannHypothesis) (s : ℂ) :
    xiGammaShapeTrace s = 0 := by
  rw [xiGammaShapeTrace, GaloisForLFunctions.HTGeometry.gdSeries]
  have hzero : ∀ p : Nat.Primes,
      ((xiGammaShapeCoefficient p : ℝ) : ℂ) *
        Complex.exp (-(s * (xiGammaShapeFrequency p : ℂ))) = 0 := by
    intro p
    rw [xiGammaShapeCoefficient_eq_zero_of_rh hRH p]
    simp
  rw [tsum_congr hzero, tsum_zero]

/-- **The one-scalar Landau criterion.**  The Riemann hypothesis is exactly holomorphic
continuation of the safe Gamma-shape germ to the half plane `Re z > 0`. -/
theorem riemannHypothesis_iff_xiGammaShapeTrace_continuation :
    RiemannHypothesis ↔
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 0 < s.re} ∧
        ∀ s : ℂ, 1 < s.re → G s = xiGammaShapeTrace s := by
  constructor
  · intro hRH
    refine ⟨fun _ => 0, differentiableOn_const 0, fun s _ => ?_⟩
    rw [xiGammaShapeTrace_eq_zero_of_rh hRH]
  · rintro ⟨G, hGd, hagree⟩
    exact riemannHypothesis_of_xiGammaShapeTrace_continuation hGd hagree

end

end RHTower
