import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTraceIsAJacobiMultipleOfThetaSquaresUpToABoundedRemainder

/-!
# The conjugate cubic twist and the q-coprime squares share the double pole

For an odd primary prime q (ρ = |q|, N = N(q), J the cubic–quadratic Jacobi sum of O/q), the bounded remainder
R_q = Tr G − (N² + N + (N − 1)J)θ_s² has constant term

|P| (−NJ R_{cop}(v) + N²χ(−4)χ(9)⁻¹ R_{g}(v/N))   (`cuspConstantTerm_fracRemainder`),

with the Bessel series of the coefficients

* T(h)² on h coprime to q (`coprimeCoeff`),
* g(h)T(h)², g(h) = Σ_u χ(u)ψ(uh) = χ̄(h)g_χ the cubic Gauss sum at h (`gaussCoeff`).

Its Mellin transform is |P|M(s)(N²χ(−4)χ(9)⁻¹N^{s−2}D_g(s) − NJ D_{cop}(s)) (`integral_fracRemainder_mul_eisenstein`),
and since R_q has at most a simple pole at 4/3, **the Gauss-weighted conjugate twist D_g and the q-coprime squares
D_{cop} carry the same double pole up to the Jacobi factor** (`conjugateTwist_relation`):

(s − 4/3)² M(s)(N²χ(−4)χ(9)⁻¹N^{s−2}D_g(s) − NJ D_{cop}(s)) → 0.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

theorem besselRemainder_const_mul (c : ℂ) (Q : O → ℂ) (v : ℝ) :
    besselRemainder (fun h => c * Q h) v = c * besselRemainder Q v := by
  rw [besselRemainder, besselRemainder, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  split_ifs <;> ring

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- T(h)² on h coprime to q. -/
def coprimeCoeff (h : O) : ℂ := if P.p ∣ h then 0 else rationalSourceResidualFourierCoefficient h ^ 2

/-- The Gauss sum at h, g(h) = Σ_u χ(u)ψ(uh). -/
def gaussAt (h : O) : ℂ := ∑ u : P.Res, P.chi u * P.traceChar (u * P.res h)

/-- g(h)T(h)². -/
def gaussCoeff (h : O) : ℂ := P.gaussAt h * rationalSourceResidualFourierCoefficient h ^ 2

theorem gaussAt_zero : P.gaussAt 0 = 0 := by
  simp only [gaussAt, map_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one P.chi_ne_one

theorem norm_gaussAt_le (h : O) : ‖P.gaussAt h‖ ≤ Fintype.card P.Res := P.norm_sum_chi_traceChar_le _ _

theorem summable_coprimeCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.coprimeCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) (summable_sq_coeff hσ)
  · split_ifs <;> positivity
  · split_ifs with hh
    · exact le_rfl
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      unfold coprimeCoeff
      split_ifs <;> simp

theorem summable_gaussCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.gaussCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) ((summable_sq_coeff hσ).mul_left (Fintype.card P.Res : ℝ))
  · split_ifs <;> positivity
  · split_ifs with hh
    · simp
    · rw [gaussCoeff, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (P.norm_gaussAt_le h) (by positivity)

/-- Σ_h b(v, h)b(v, −h)φ(h) is the Bessel series of φT² when φ(0) = 0. -/
theorem tsum_amplitude_phase (φ : O → ℂ) (hφ : φ 0 = 0) (v : ℝ) (hv : 0 < v) :
    ∑' h : O, rationalSourceModeAmplitude v h * rationalSourceModeAmplitude v (-h) * φ h =
      besselRemainder (fun h => φ h * rationalSourceResidualFourierCoefficient h ^ 2) v := by
  rw [besselRemainder]
  refine tsum_congr fun h => ?_
  by_cases hh : h = 0
  · simp [hh, hφ]
  · rw [if_neg hh, sourceAmplitude_mul_neg v hv h hh, besselSq]
    ring

theorem fracWeight_sub (k : O) : P.fracWeight k - P.fracMain =
    -(P.normC * P.fracJacobi) * (if P.p ∣ k then 0 else 1) := by
  unfold fracWeight fracMain
  split_ifs <;> ring

/-- **The constant term of R_q.** -/
theorem cuspConstantTerm_fracRemainder (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm P.fracRemainder v = periodArea *
      (-(P.normC * P.fracJacobi) * besselRemainder P.coprimeCoeff v +
        P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) *
          besselRemainder P.gaussCoeff (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)) := by
  have hn := P.norm_pos
  set b := rationalSourceModeAmplitude v with hbdef
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z => cuspCoordinateLift_positive v z hv
  have hc1 : Continuous (fun z : ℂ => P.sourceFracTrace (upperPoint z v hv)) :=
    P.sourceFracTrace_continuous.comp (continuous_upperPoint_z v hv)
  have hc2 : Continuous (fun z : ℂ => sourceTheta (upperPoint z v hv) ^ 2) :=
    (cubicSourceResidualFunction_continuous.comp (continuous_upperPoint_z v hv)).pow 2
  have hθ2 : ∫ z in periodDomain, sourceTheta (upperPoint z v hv) ^ 2 = periodArea * ∑' k : O, b k * b (-k) := by
    simp_rw [sourceTheta, cubicSourceResidualFunction_fourier_expansion]
    exact integral_cuspCharacterSeries_sq _ hb
  rw [cuspConstantTerm]
  simp_rw [hlift, fracRemainder]
  rw [integral_sub (integrableOn_periodDomain_of_continuous _ hc1)
    ((integrableOn_periodDomain_of_continuous _ hc2).const_mul _), integral_const_mul,
    P.integral_sourceFracTrace h2 v hv, hθ2]
  have hW : ∀ k : O, ‖P.fracWeight k‖ ≤ ‖P.normC ^ 2 + P.normC - P.fracJacobi‖ + ‖P.normC * P.fracJacobi‖ := by
    intro k
    unfold fracWeight
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    split_ifs <;> simp
    positivity
  have s1 := summable_mul_neg_bdd hb hb _ _ hW
  have s2 := summable_mul_neg_bdd hb hb (fun _ => (1 : ℂ)) 1 (fun _ => by simp)
  have hsplit : ∑' k : O, b k * b (-k) * P.fracWeight k - P.fracMain * ∑' k : O, b k * b (-k) =
      -(P.normC * P.fracJacobi) * besselRemainder P.coprimeCoeff v := by
    have e : ∑' k : O, b k * b (-k) * P.fracWeight k - P.fracMain * ∑' k : O, b k * b (-k) =
        ∑' k : O, b k * b (-k) * (P.fracWeight k - P.fracMain) := by
      rw [← tsum_mul_left, ← s1.tsum_sub (by simpa using s2.mul_left P.fracMain)]
      refine tsum_congr fun k => ?_
      ring
    rw [e]
    simp_rw [P.fracWeight_sub]
    rw [tsum_amplitude_phase _ (by simp) v hv, ← besselRemainder_const_mul]
    congr 1
    funext h
    unfold coprimeCoeff
    split_ifs <;> ring
  have hgauss : ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
      rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) *
        ∑ u : P.Res, P.chi u * P.traceChar (u * P.res k) =
      besselRemainder P.gaussCoeff (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) :=
    tsum_amplitude_phase P.gaussAt P.gaussAt_zero _ (div_pos (div_pos hv hn) hn)
  rw [hgauss]
  linear_combination periodArea * hsplit

theorem real_cpow_sq_inv (ρ : ℝ) (hρ : 0 < ρ) (s : ℂ) :
    (((1 / (ρ * ρ) : ℝ)) : ℂ) ^ (2 - s) = ((ρ * ρ : ℝ) : ℂ) ^ (s - 2) := by
  have hρ2 : 0 < ρ * ρ := mul_pos hρ hρ
  have harg : ((ρ * ρ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hρ2.le]
    exact Real.pi_ne_zero.symm
  rw [show (((1 / (ρ * ρ) : ℝ)) : ℂ) = ((ρ * ρ : ℝ) : ℂ)⁻¹ by push_cast; ring, Complex.inv_cpow _ _ harg,
    ← Complex.cpow_neg]
  congr 1
  ring

/-- **The Mellin identity of R_q.** For 4 < Re s < 13/3:
∫ R_q E(s) = |P| M(s)(N²χ(−4)χ(9)⁻¹N^{s−2}D_g(s) − NJ D_{cop}(s)). -/
theorem integral_fracRemainder_mul_eisenstein (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, P.fracRemainder w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      periodArea * (besselSqMellin s *
        (P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) *
            besselDirichlet P.gaussCoeff s -
          P.normC * P.fracJacobi * besselDirichlet P.coprimeCoeff s)) := by
  have hG := P.fracRemainder_remainderData h2
  have hn := P.norm_pos
  set ρ := ‖ringComplex P.p‖ with hρ
  have hs23 : 2 / 3 < s.re := by linarith
  have hb : 0 < 1 / (ρ * ρ) := one_div_pos.mpr (mul_pos hn hn)
  rw [hG.integral_mul_eisenstein s (by linarith) hs]
  set RC := besselRemainder P.coprimeCoeff
  set RG := besselRemainder P.gaussCoeff
  set κ : ℂ := P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹)
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      (v : ℂ) ^ s * (∫ z in periodDomain, P.fracRemainder (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        periodArea * (κ * ((v : ℂ) ^ s * RG (1 / (ρ * ρ) * v) / (v : ℂ) ^ 3) -
          P.normC * P.fracJacobi * ((v : ℂ) ^ s * RC v / (v : ℂ) ^ 3)) := by
    intro v (hv : 0 < v)
    have hc := P.cuspConstantTerm_fracRemainder h2 v hv
    rw [cuspConstantTerm] at hc
    rw [hc, show v / ρ / ρ = 1 / (ρ * ρ) * v by field_simp]
    ring
  have hIG := integrableOn_mellin_comp_mul RG s hb
    (integrableOn_besselRemainder P.gaussCoeff s hs23 (P.summable_gaussCoeff hs4))
  have hIC := integrableOn_besselRemainder P.coprimeCoeff s hs23 (P.summable_coprimeCoeff hs4)
  have J1 : IntegrableOn (fun v : ℝ => κ * ((v : ℂ) ^ s * RG (1 / (ρ * ρ) * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hIG.const_mul _
  have J2 : IntegrableOn (fun v : ℝ => P.normC * P.fracJacobi * ((v : ℂ) ^ s * RC v / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hIC.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_sub J1 J2, integral_const_mul,
    integral_const_mul, integral_mellin_comp_mul RG s hb,
    integral_besselRemainder P.gaussCoeff s hs23 (P.summable_gaussCoeff hs4),
    integral_besselRemainder P.coprimeCoeff s hs23 (P.summable_coprimeCoeff hs4), real_cpow_sq_inv ρ hn s]
  ring

/-- **The conjugate-twist relation at q.** The Gauss-weighted conjugate twist and the q-coprime squares share
their double pole: (s − 4/3)² M(s)(N²χ(−4)χ(9)⁻¹N^{s−2}D_g(s) − NJ D_{cop}(s)) → 0. -/
theorem conjugateTwist_relation (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s *
          (P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) *
              besselDirichlet P.gaussCoeff s -
            P.normC * P.fracJacobi * besselDirichlet P.coprimeCoeff s)) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 0) := by
  have hG := P.fracRemainder_remainderData h2
  have hq : (periodArea : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  refine ⟨fun s => periodArea⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_⟩
  · show periodArea⁻¹ * hG.pairing s = _
    rw [← hG.pairing_eq s hs4 hs hi, P.integral_fracRemainder_mul_eisenstein h2 s hs4 hs, inv_mul_cancel_left₀ hq]
  · exact (hG.pairing_differentiableAt s hs1 hs hi).const_mul _
  · filter_upwards [hG.pairing_near_four_thirds.1] with s h
    exact h.const_mul _
  · have h := hG.pairing_near_four_thirds.2.const_mul (periodArea⁻¹ : ℂ)
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun s => ?_)
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
