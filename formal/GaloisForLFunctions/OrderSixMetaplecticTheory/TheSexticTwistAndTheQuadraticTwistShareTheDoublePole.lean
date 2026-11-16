import GaloisForLFunctions.OrderSixMetaplecticTheory.TheQuadraticFractionalTraceIsABoundedRemainder

/-!
# The sextic twist and the quadratic twist share the double pole

Let q be an odd primary prime, λ = λ_q its quadratic character, χ = χ_q its cubic character, ρ = |q|, N = ρ².
The bounded remainder Tr G_λ (`sourceFracTraceW_remainderData`) has constant term
(`cuspConstantTerm_sourceFracTraceW`)

|P| (g_λJ₆ R_quad(v) + N²χ(−4)χ(9)⁻¹λ(−2) R_sext(v/N)),

with the Bessel series of λ(2h)T(h)² (`quadCoeff`) and of g_{χλ}(h)T(h)² (`sexticCoeff`). Since
g_{χλ}(h) = (χ̄λ)(h)g_{χλ} (`sexticGaussAt_eq`), the Mellin transform gives the **sextic-twist relation**
(`sexticTwist_relation`): with the quadratic twist L_λ = Σ_hλ(h)T(h)²(4π|ξ_h|)^{−s} and the conjugate sextic twist
L_{χ̄λ} = Σ_h(χ̄λ)(h)T(h)²(4π|ξ_h|)^{−s},

(s − 4/3)² M(s)(g_λJ₆λ(2) L_λ(s) + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2} L_{χ̄λ}(s)) → 0.

Every constant is nonzero; in particular J₆ = Σ_s(χλ)(1 − s²) is the Jacobi sum J(λ, χλ) (`lamJacobi_eq`). Hence
(`sexticTwist_double_pole_iff`): **M·L_{χ̄λ} continues to a punctured neighbourhood of 4/3 with leading
coefficient c·L if and only if M·L_λ does with leading coefficient L**, c = −g_λJ₆λ(2)/(N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{−2/3}).
The double pole of the conjugate sextic twist at q is the double pole of the quadratic twist at q.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The coefficients -/

/-- λ(2h)T(h)². -/
def quadCoeff (h : O) : ℂ := P.lam (2 * P.res h) * rationalSourceResidualFourierCoefficient h ^ 2

/-- g_{χλ}(h)T(h)². -/
def sexticCoeff (h : O) : ℂ := P.sexticGaussAt h * rationalSourceResidualFourierCoefficient h ^ 2

/-- The quadratic twist λ(h)T(h)². -/
def quadTwistCoeff (h : O) : ℂ := P.lam (P.res h) * rationalSourceResidualFourierCoefficient h ^ 2

/-- The conjugate sextic twist (χ̄λ)(h)T(h)², χ̄ = χ². -/
def sexticTwistCoeff (h : O) : ℂ :=
  (P.chi ^ 2) (P.res h) * P.lam (P.res h) * rationalSourceResidualFourierCoefficient h ^ 2

theorem chi_mul_lam_ne_one (h2 : (2 : P.Res) ≠ 0) : P.chi * P.lam ≠ 1 := by
  simpa using P.chi_pow_mul_lam_ne_one h2 1

theorem sexticGaussAt_zero (h2 : (2 : P.Res) ≠ 0) : P.sexticGaussAt 0 = 0 := by
  have h := MulChar.sum_eq_zero_of_ne_one (P.chi_mul_lam_ne_one h2)
  simp only [MulChar.mul_apply] at h
  simp only [sexticGaussAt, map_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]
  exact h

/-- **The sextic Gauss sum at h.** g_{χλ}(h) = (χ̄λ)(h)g_{χλ}. -/
theorem sexticGaussAt_eq (h2 : (2 : P.Res) ≠ 0) (h : O) :
    P.sexticGaussAt h = (P.chi ^ 2) (P.res h) * P.lam (P.res h) * gaussSum (P.chi * P.lam) P.traceChar := by
  by_cases hh : P.res h = 0
  · have h0 := MulChar.sum_eq_zero_of_ne_one (P.chi_mul_lam_ne_one h2)
    simp only [MulChar.mul_apply] at h0
    simp only [sexticGaussAt, hh, mul_zero, AddChar.map_zero_eq_one, mul_one, MulChar.map_zero, zero_mul]
    exact h0
  · have hs := P.sum_mulChar_shift (P.chi * P.lam) (P.res h) 1 hh
    simp only [mul_one, MulChar.mul_apply] at hs
    rw [sexticGaussAt, hs, mul_inv, P.chi_inv_eq, P.lam_inv _ hh, gaussSum]
    simp only [MulChar.mul_apply]

theorem norm_sexticGaussAt_le (h : O) : ‖P.sexticGaussAt h‖ ≤ Fintype.card P.Res := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ u : P.Res, ‖P.chi u * P.lam u * P.traceChar (u * P.res h)‖ ≤ ∑ _u : P.Res, (1 : ℝ) := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [mul_comm (P.chi u), mul_assoc]
        exact P.norm_lam_chi_traceChar_le _ _ _
    _ = Fintype.card P.Res := by simp

theorem summable_weightedCoeff {σ : ℝ} (hσ : 4 < σ) (φ : O → ℂ) (C : ℝ) (hφ : ∀ h, ‖φ h‖ ≤ C) :
    Summable (fun h : O => if h = 0 then 0 else
      ‖φ h * rationalSourceResidualFourierCoefficient h ^ 2‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) ((summable_sq_coeff hσ).mul_left C)
  · split_ifs <;> positivity
  · split_ifs with hh
    · simp
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hφ h) (by positivity)

theorem summable_quadCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.quadCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) :=
  summable_weightedCoeff hσ (fun h => P.lam (2 * P.res h)) 1 (fun _ => P.norm_lam_le _)

theorem summable_sexticCoeff {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.sexticCoeff h‖ * ‖cuspFrequency h‖ ^ (-σ)) :=
  summable_weightedCoeff hσ P.sexticGaussAt _ P.norm_sexticGaussAt_le

/-! ### The constant term and the Mellin identity -/

/-- **The constant term of Tr G_λ.** -/
theorem cuspConstantTerm_sourceFracTraceW (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm P.sourceFracTraceW v = periodArea *
      (gaussSum P.lam P.traceChar * P.lamJacobi * besselRemainder P.quadCoeff v +
        P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2)) *
          besselRemainder P.sexticCoeff (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)) := by
  have hn := P.norm_pos
  have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z => cuspCoordinateLift_positive v z hv
  rw [cuspConstantTerm]
  simp_rw [hlift]
  rw [P.integral_sourceFracTraceW h2 v hv]
  have hq : ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) * P.lam (2 * P.res k) =
      besselRemainder P.quadCoeff v :=
    tsum_amplitude_phase (fun h => P.lam (2 * P.res h)) (by simp) v hv
  have hs : ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
      rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) * P.sexticGaussAt k =
      besselRemainder P.sexticCoeff (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) :=
    tsum_amplitude_phase P.sexticGaussAt (P.sexticGaussAt_zero h2) _ (div_pos (div_pos hv hn) hn)
  rw [hq, hs]

/-- **The Mellin identity of Tr G_λ.** For 4 < Re s < 13/3:
∫ Tr G_λ E(s) = |P| M(s)(g_λJ₆ D_quad(s) + N²χ(−4)χ(9)⁻¹λ(−2)N^{s−2}D_sext(s)). -/
theorem integral_sourceFracTraceW_mul_eisenstein (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs4 : 4 < s.re)
    (hs : s.re < 13 / 3) :
    ∫ w in levelSet, P.sourceFracTraceW w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      periodArea * (besselSqMellin s *
        (gaussSum P.lam P.traceChar * P.lamJacobi * besselDirichlet P.quadCoeff s +
          P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2)) *
            ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) * besselDirichlet P.sexticCoeff s)) := by
  have hG := P.sourceFracTraceW_remainderData h2
  have hn := P.norm_pos
  set ρ := ‖ringComplex P.p‖ with hρ
  have hs23 : 2 / 3 < s.re := by linarith
  have hb : 0 < 1 / (ρ * ρ) := one_div_pos.mpr (mul_pos hn hn)
  rw [hG.integral_mul_eisenstein s (by linarith) hs]
  set RQ := besselRemainder P.quadCoeff
  set RS := besselRemainder P.sexticCoeff
  set A : ℂ := gaussSum P.lam P.traceChar * P.lamJacobi
  set κ : ℂ := P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2))
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      (v : ℂ) ^ s * (∫ z in periodDomain, P.sourceFracTraceW (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        periodArea * (A * ((v : ℂ) ^ s * RQ v / (v : ℂ) ^ 3) +
          κ * ((v : ℂ) ^ s * RS (1 / (ρ * ρ) * v) / (v : ℂ) ^ 3)) := by
    intro v (hv : 0 < v)
    have hc := P.cuspConstantTerm_sourceFracTraceW h2 v hv
    rw [cuspConstantTerm] at hc
    rw [hc, show v / ρ / ρ = 1 / (ρ * ρ) * v by field_simp]
    ring
  have hIS := integrableOn_mellin_comp_mul RS s hb
    (integrableOn_besselRemainder P.sexticCoeff s hs23 (P.summable_sexticCoeff hs4))
  have hIQ := integrableOn_besselRemainder P.quadCoeff s hs23 (P.summable_quadCoeff hs4)
  have J1 : IntegrableOn (fun v : ℝ => A * ((v : ℂ) ^ s * RQ v / (v : ℂ) ^ 3)) (Set.Ioi 0) := hIQ.const_mul _
  have J2 : IntegrableOn (fun v : ℝ => κ * ((v : ℂ) ^ s * RS (1 / (ρ * ρ) * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hIS.const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_add J1 J2, integral_const_mul,
    integral_const_mul, integral_mellin_comp_mul RS s hb,
    integral_besselRemainder P.sexticCoeff s hs23 (P.summable_sexticCoeff hs4),
    integral_besselRemainder P.quadCoeff s hs23 (P.summable_quadCoeff hs4), real_cpow_sq_inv ρ hn s]
  ring

/-! ### The relation and the twists -/

theorem besselDirichlet_eq_const_mul (Q R : O → ℂ) (c : ℂ) (hQR : ∀ h, h ≠ 0 → Q h = c * R h) (s : ℂ) :
    besselDirichlet Q s = c * besselDirichlet R s := by
  rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  split_ifs with hh
  · ring
  · rw [hQR h hh]
    ring

theorem quadDirichlet_eq (s : ℂ) : besselDirichlet P.quadCoeff s = P.lam 2 * besselDirichlet P.quadTwistCoeff s :=
  besselDirichlet_eq_const_mul _ _ _ (fun h _ => by rw [quadCoeff, quadTwistCoeff, map_mul]; ring) s

theorem sexticDirichlet_eq (h2 : (2 : P.Res) ≠ 0) (s : ℂ) :
    besselDirichlet P.sexticCoeff s = gaussSum (P.chi * P.lam) P.traceChar * besselDirichlet P.sexticTwistCoeff s :=
  besselDirichlet_eq_const_mul _ _ _ (fun h _ => by rw [sexticCoeff, sexticTwistCoeff, P.sexticGaussAt_eq h2]; ring) s

/-- The coefficient of the quadratic twist: g_λJ₆λ(2). -/
def quadFactor : ℂ := gaussSum P.lam P.traceChar * P.lamJacobi * P.lam 2

/-- The coefficient of the conjugate sextic twist: N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}. -/
def sexticFactor (s : ℂ) : ℂ :=
  P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2)) * gaussSum (P.chi * P.lam) P.traceChar *
    ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2)

/-- **The sextic-twist relation at q.** The quadratic twist and the conjugate sextic twist share their double pole:
(s − 4/3)²M(s)(g_λJ₆λ(2)L_λ(s) + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}L_{χ̄λ}(s)) → 0. -/
theorem sexticTwist_relation (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * (P.quadFactor * besselDirichlet P.quadTwistCoeff s +
          P.sexticFactor s * besselDirichlet P.sexticTwistCoeff s)) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 0) := by
  have hG := P.sourceFracTraceW_remainderData h2
  have hq : (periodArea : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  refine ⟨fun s => periodArea⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_⟩
  · show periodArea⁻¹ * hG.pairing s = _
    rw [← hG.pairing_eq s hs4 hs hi, P.integral_sourceFracTraceW_mul_eisenstein h2 s hs4 hs, inv_mul_cancel_left₀ hq,
      P.quadDirichlet_eq, P.sexticDirichlet_eq h2, quadFactor, sexticFactor]
    ring
  · exact (hG.pairing_differentiableAt s hs1 hs hi).const_mul _
  · filter_upwards [hG.pairing_near_four_thirds.1] with s h
    exact h.const_mul _
  · have h := hG.pairing_near_four_thirds.2.const_mul (periodArea⁻¹ : ℂ)
    rw [mul_zero] at h
    refine h.congr' (Eventually.of_forall fun s => ?_)
    ring

/-! ### Nonvanishing of the factors -/

/-- J₆ is the Jacobi sum J(λ, χλ): Σ_s f(1 − s²) = Σ_y f(1 − y)(1 + λ(y)) and Σ_y(χλ)(1 − y) = 0. -/
theorem lamJacobi_eq (h2 : (2 : P.Res) ≠ 0) : P.lamJacobi = jacobiSum P.lam (P.chi * P.lam) := by
  have hF := P.ringChar_ne_two h2
  have hcount : ∀ y : P.Res, ((Finset.univ.filter (fun s : P.Res => s ^ 2 = y)).card : ℂ) = P.lam y + 1 := by
    intro y
    have h := quadraticChar_card_sqrts hF y
    simp only [Set.toFinset_setOf] at h
    simp only [lam, MulChar.ringHomComp_apply, eq_intCast]
    exact_mod_cast h
  have hfib : ∑ s : P.Res, P.chi (1 - s ^ 2) * P.lam (1 - s ^ 2) = ∑ y : P.Res,
      ∑ s ∈ Finset.univ.filter (fun s : P.Res => s ^ 2 = y), (P.chi (1 - y) * P.lam (1 - y)) :=
    (Finset.sum_fiberwise' Finset.univ (fun s : P.Res => s ^ 2) (fun y => P.chi (1 - y) * P.lam (1 - y))).symm
  have hz : ∑ y : P.Res, P.chi (1 - y) * P.lam (1 - y) = 0 := by
    have h0 := MulChar.sum_eq_zero_of_ne_one (P.chi_mul_lam_ne_one h2)
    rw [← (Equiv.subLeft (1 : P.Res)).sum_comp] at h0
    simpa only [MulChar.mul_apply, Equiv.subLeft_apply] using h0
  rw [lamJacobi, hfib]
  simp_rw [Finset.sum_const, nsmul_eq_mul, hcount, add_mul, one_mul]
  rw [Finset.sum_add_distrib, hz, add_zero, jacobiSum]
  exact Finset.sum_congr rfl fun y _ => by rw [MulChar.mul_apply]

theorem lamJacobi_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.lamJacobi ≠ 0 := by
  have hring : ringChar ℂ ≠ ringChar P.Res := by
    rw [ringChar.eq_zero]
    exact (CharP.ringChar_ne_zero_of_finite (R := P.Res)).symm
  have hprod : P.lam * (P.chi * P.lam) ≠ 1 := by
    rw [mul_left_comm, ← pow_two, P.lam_sq_eq_one, mul_one]
    exact P.chi_ne_one
  have h := jacobiSum_mul_jacobiSum_inv hring (P.lam_ne_one h2) (P.chi_mul_lam_ne_one h2) hprod
  rw [P.lamJacobi_eq h2]
  intro h0
  rw [h0, zero_mul] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h.symm

theorem gaussSum_ne_zero' (χ' : MulChar P.Res ℂ) (hχ : χ' ≠ 1) : gaussSum χ' P.traceChar ≠ 0 := by
  intro h0
  have h := P.norm_gaussSum_traceChar χ' hχ
  rw [h0, norm_zero] at h
  exact P.norm_pos.ne h

theorem lam_ne_zero (x : P.Res) (hx : x ≠ 0) : P.lam x ≠ 0 := by
  intro h0
  have h := P.lam_sq x hx
  rw [h0] at h
  norm_num at h

theorem quadFactor_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.quadFactor ≠ 0 :=
  mul_ne_zero (mul_ne_zero (P.gaussSum_ne_zero' _ (P.lam_ne_one h2)) (P.lamJacobi_ne_zero h2)) (P.lam_ne_zero 2 h2)

theorem sexticFactor_ne_zero (h2 : (2 : P.Res) ≠ 0) (s : ℂ) : P.sexticFactor s ≠ 0 := by
  have hN : P.normC ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h4 : (-4 : P.Res) ≠ 0 := by
    rw [show (-4 : P.Res) = -(2 * 2) by norm_num]
    exact neg_ne_zero.mpr (mul_ne_zero h2 h2)
  have hm2 : (-2 : P.Res) ≠ 0 := neg_ne_zero.mpr h2
  have hb : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos P.norm_pos P.norm_pos).ne'
  have hc : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hb]
    exact Complex.exp_ne_zero _
  unfold sexticFactor
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hN) (mul_ne_zero (mul_ne_zero
    (P.chi_ne_zero_of_ne _ h4) (inv_ne_zero (P.chi_ne_zero_of_ne _ P.nine_ne_zero'))) (P.lam_ne_zero _ hm2)))
    (P.gaussSum_ne_zero' _ (P.chi_mul_lam_ne_one h2))) hc

theorem sexticFactor_differentiableAt (s : ℂ) : DifferentiableAt ℂ P.sexticFactor s := by
  have hb : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos P.norm_pos P.norm_pos).ne'
  exact (differentiableAt_const _).mul
    (DifferentiableAt.const_cpow (f := fun s : ℂ => s - 2) (differentiableAt_id.sub_const 2) (Or.inl hb))

/-- The ratio of the double-pole coefficients: −g_λJ₆λ(2)/(N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{−2/3}). -/
def sexticRatio : ℂ := -P.quadFactor / P.sexticFactor (4 / 3)

/-- **The double pole of the conjugate sextic twist is the double pole of the quadratic twist.** For every L:
M·L_λ continues to {1 < Re s < 13/3, Im s > 0} and a punctured neighbourhood of 4/3 with (s − 4/3)²M(s)L_λ(s) → L
if and only if M·L_{χ̄λ} does with (s − 4/3)²M(s)L_{χ̄λ}(s) → cL, c = `sexticRatio` ≠ 0. -/
theorem sexticTwist_double_pole_iff (h2 : (2 : P.Res) ≠ 0) (L : ℂ) :
    (∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * besselDirichlet P.quadTwistCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 L)) ↔
    (∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet P.sexticTwistCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.sexticRatio * L))) := by
  obtain ⟨Λr, hre, hrd, hrn, hrl⟩ := P.sexticTwist_relation h2
  have ha := P.quadFactor_ne_zero h2
  have hc := P.sexticFactor_ne_zero h2
  have hcd := P.sexticFactor_differentiableAt
  have hct : Tendsto (fun s => (P.sexticFactor s)⁻¹) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.sexticFactor (4 / 3))⁻¹) :=
    ((hcd (4 / 3)).continuousAt.tendsto.inv₀ (hc _)).mono_left nhdsWithin_le_nhds
  have hct' : Tendsto P.sexticFactor (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.sexticFactor (4 / 3))) :=
    (hcd (4 / 3)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · rintro ⟨Λ₁, h1e, h1d, h1n, h1l⟩
    refine ⟨fun s => (P.sexticFactor s)⁻¹ * (Λr s - P.quadFactor * Λ₁ s), fun s hs4 hs hi => ?_,
      fun s hs1 hs hi => ?_, ?_, ?_⟩
    · show (P.sexticFactor s)⁻¹ * (Λr s - P.quadFactor * Λ₁ s) = _
      rw [hre s hs4 hs hi, h1e s hs4 hs hi, inv_mul_eq_iff_eq_mul₀ (hc s)]
      ring
    · exact ((hcd s).inv (hc s)).mul ((hrd s hs1 hs hi).sub ((differentiableAt_const _).mul (h1d s hs1 hs hi)))
    · filter_upwards [hrn, h1n] with s ha' hb'
      exact ((hcd s).inv (hc s)).mul (ha'.sub ((differentiableAt_const _).mul hb'))
    · have h := hct.mul (hrl.sub (h1l.const_mul P.quadFactor))
      have hv : (P.sexticFactor (4 / 3))⁻¹ * (0 - P.quadFactor * L) = P.sexticRatio * L := by
        rw [sexticRatio]
        field_simp [hc (4 / 3)]
        ring
      rw [hv] at h
      refine h.congr' (Eventually.of_forall fun s => ?_)
      ring
  · rintro ⟨Λ₂, h2e, h2d, h2n, h2l⟩
    refine ⟨fun s => P.quadFactor⁻¹ * (Λr s - P.sexticFactor s * Λ₂ s), fun s hs4 hs hi => ?_,
      fun s hs1 hs hi => ?_, ?_, ?_⟩
    · show P.quadFactor⁻¹ * (Λr s - P.sexticFactor s * Λ₂ s) = _
      rw [hre s hs4 hs hi, h2e s hs4 hs hi, inv_mul_eq_iff_eq_mul₀ ha]
      ring
    · exact (differentiableAt_const _).mul ((hrd s hs1 hs hi).sub ((hcd s).mul (h2d s hs1 hs hi)))
    · filter_upwards [hrn, h2n] with s ha' hb'
      exact (differentiableAt_const _).mul (ha'.sub ((hcd s).mul hb'))
    · have h := (hrl.sub (hct'.mul h2l)).const_mul P.quadFactor⁻¹
      have hv : P.quadFactor⁻¹ * (0 - P.sexticFactor (4 / 3) * (P.sexticRatio * L)) = L := by
        rw [sexticRatio]
        field_simp [hc (4 / 3)]
        ring
      rw [hv] at h
      refine h.congr' (Eventually.of_forall fun s => ?_)
      ring

theorem sexticRatio_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.sexticRatio ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr (P.quadFactor_ne_zero h2)) (P.sexticFactor_ne_zero h2 _)

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
