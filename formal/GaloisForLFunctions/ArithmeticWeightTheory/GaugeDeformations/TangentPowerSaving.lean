import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PoleResidueCurvature
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.NoSurrogateAnnihilator

/-!
# Power saving for prime-phase tangents

A bounded holomorphic prime-phase family with an actual jointly holomorphic
pole regularization has square-summable tangent energy at an exponent strictly
below one. Its positive prime-power curvature series agrees near the pole with
the Schwarz-paired parameter curvature. Landau's theorem prevents one from
being the abscissa of that series.

The summability conclusion follows from the family itself; no convergence or
continuation hypothesis on the tangent series is assumed.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Positive prime-power coefficients of the phase curvature. -/
def primeTangentCoefficient (a : Nat.Primes → ℝ) (z : Nat.Primes × ℕ) : ℝ :=
  (z.2 + 1 : ℝ) * a z.1 ^ 2

def primeTangentSeries (a : Nat.Primes → ℝ) : ℂ → ℂ :=
  gdSeries (primeTangentCoefficient a) _root_.RHTower.eulerPrimePowerEnergy

theorem primeTangentCoefficient_nonneg (a : Nat.Primes → ℝ) (z : Nat.Primes × ℕ) :
    0 ≤ primeTangentCoefficient a z := by unfold primeTangentCoefficient; positivity

theorem primePowerEnergy_nonneg (z : Nat.Primes × ℕ) :
    0 ≤ _root_.RHTower.eulerPrimePowerEnergy z := Real.log_natCast_nonneg _

theorem primePowerEnergy_eq (p : Nat.Primes) (n : ℕ) :
    _root_.RHTower.eulerPrimePowerEnergy (p, n) = (n + 1 : ℝ) * primeFrequency p := by
  unfold _root_.RHTower.eulerPrimePowerEnergy _root_.RHTower.eulerPrimePowerNat primeFrequency
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  rfl

theorem primePower_exp_decay (σ : ℝ) (z : Nat.Primes × ℕ) :
    Real.exp (-(σ * _root_.RHTower.eulerPrimePowerEnergy z)) =
      (_root_.RHTower.eulerPrimePowerNat z : ℝ) ^ (-σ) := by
  have hn : (0 : ℝ) < _root_.RHTower.eulerPrimePowerNat z := by
    dsimp [_root_.RHTower.eulerPrimePowerNat]
    exact_mod_cast pow_pos z.1.2.pos (z.2 + 1)
  rw [Real.rpow_def_of_pos hn, _root_.RHTower.eulerPrimePowerEnergy]
  congr 1
  ring

theorem primePower_exp_eq_pow (σ : ℝ) (p : Nat.Primes) (n : ℕ) :
    Real.exp (-(σ * _root_.RHTower.eulerPrimePowerEnergy (p, n))) =
      primeDamping σ p ^ (n + 1) := by
  rw [primePowerEnergy_eq, primeDamping, ← prime_exp_decay, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Bounded phase speeds are dominated by the logarithmic prime-power spectrum. -/
theorem primeTangentCoefficient_le_log {a : Nat.Primes → ℝ} {K : ℝ}
    (ha : ∀ p, |a p| ≤ K) (z : Nat.Primes × ℕ) :
    primeTangentCoefficient a z ≤
      (K ^ 2 / Real.log 2) * _root_.RHTower.eulerPrimePowerEnergy z := by
  rcases z with ⟨p, n⟩
  have hs : a p ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a p)) (ha p) 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : Real.log 2 ≤ primeFrequency p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  have hr : 1 ≤ primeFrequency p / Real.log 2 := by
    apply (le_div_iff₀ hlog).mpr
    simpa only [one_mul] using hp
  have hn : 0 ≤ (n + 1 : ℝ) * K ^ 2 := by positivity
  calc primeTangentCoefficient a (p, n) ≤ (n + 1 : ℝ) * K ^ 2 :=
         mul_le_mul_of_nonneg_left hs (by positivity)
       _ = ((n + 1 : ℝ) * K ^ 2) * 1 := by rw [mul_one]
       _ ≤ ((n + 1 : ℝ) * K ^ 2) * (primeFrequency p / Real.log 2) :=
         mul_le_mul_of_nonneg_left hr hn
       _ = (K ^ 2 / Real.log 2) * _root_.RHTower.eulerPrimePowerEnergy (p, n) := by
         rw [primePowerEnergy_eq]
         ring

/-- The positive curvature series converges throughout the Euler half-plane. -/
theorem summable_primeTangentSeries_term {a : Nat.Primes → ℝ} {K σ : ℝ}
    (ha : ∀ p, |a p| ≤ K) (hσ : 1 < σ) :
    Summable (gdTwistTerm (primeTangentCoefficient a) _root_.RHTower.eulerPrimePowerEnergy σ 0) := by
  have hs := (_root_.RHTower.summable_abs_log_natCast_pow_mul_rpow_neg 1 σ hσ).comp_injective
    _root_.RHTower.eulerPrimePowerNat_injective
  refine (hs.mul_left (K ^ 2 / Real.log 2)).of_nonneg_of_le
    (gdTwistTerm_nonneg (primeTangentCoefficient_nonneg a) primePowerEnergy_nonneg σ 0) ?_
  intro z
  rw [gdTwistTerm, pow_zero, mul_one, primePower_exp_decay]
  simp only [Function.comp_apply, pow_one, abs_of_nonneg (Real.log_natCast_nonneg _)]
  calc primeTangentCoefficient a z * (_root_.RHTower.eulerPrimePowerNat z : ℝ) ^ (-σ) ≤
      ((K ^ 2 / Real.log 2) * _root_.RHTower.eulerPrimePowerEnergy z) *
        (_root_.RHTower.eulerPrimePowerNat z : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (primeTangentCoefficient_le_log ha z) (by positivity)
       _ = _ := by unfold _root_.RHTower.eulerPrimePowerEnergy; ring

theorem primeTangentTerm_eq (a : Nat.Primes → ℝ) (σ : ℝ) (p : Nat.Primes) (n : ℕ) :
    gdTwistTerm (primeTangentCoefficient a) _root_.RHTower.eulerPrimePowerEnergy σ 0 (p, n) =
      a p ^ 2 * ((n + 1 : ℝ) * primeDamping σ p ^ (n + 1)) := by
  rw [gdTwistTerm, pow_zero, mul_one, primePower_exp_eq_pow]
  unfold primeTangentCoefficient
  ring

theorem hasSum_primeTangent_row (a : Nat.Primes → ℝ) {σ : ℝ} (hσ : 1 < σ)
    (p : Nat.Primes) :
    HasSum (fun n : ℕ =>
      gdTwistTerm (primeTangentCoefficient a) _root_.RHTower.eulerPrimePowerEnergy σ 0 (p, n))
      (a p ^ 2 * primeDamping σ p / (1 - primeDamping σ p) ^ 2) := by
  have hq : ‖primeDamping σ p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (primeDamping_pos σ p)]
    exact (primeDamping_le_half hσ.le p).trans_lt (by norm_num)
  have hg := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have hshift : HasSum (fun n : ℕ => (n + 1 : ℝ) * primeDamping σ p ^ (n + 1))
      (primeDamping σ p / (1 - primeDamping σ p) ^ 2) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hg
  have h := hshift.mul_left (a p ^ 2)
  simpa only [primeTangentTerm_eq, mul_div_assoc] using h

/-- Summing the prime powers recovers the Euler phase-curvature weights. -/
theorem primeTangentSeries_real {a : Nat.Primes → ℝ} {K σ : ℝ}
    (ha : ∀ p, |a p| ≤ K) (hσ : 1 < σ) :
    primeTangentSeries a (σ : ℂ) =
      ((∑' p : Nat.Primes, a p ^ 2 * primeDamping σ p / (1 - primeDamping σ p) ^ 2 : ℝ) : ℂ) := by
  have hs := summable_primeTangentSeries_term ha hσ
  rw [primeTangentSeries, _root_.RHTower.gdSeries_ofReal
    (primeTangentCoefficient_nonneg a) primePowerEnergy_nonneg hs le_rfl]
  congr 1
  rw [hs.tsum_prod]
  exact tsum_congr fun p => (hasSum_primeTangent_row a hσ p).tsum_eq

/-- The first prime powers recover the ordinary quadratic prime energy. -/
theorem summable_prime_energy_of_primeTangentSeries {a : Nat.Primes → ℝ} {σ : ℝ}
    (hs : Summable (gdTwistTerm (primeTangentCoefficient a)
      _root_.RHTower.eulerPrimePowerEnergy σ 0)) :
    Summable (fun p : Nat.Primes => a p ^ 2 * primeDamping σ p) := by
  have h := hs.comp_injective
    (show Function.Injective (fun p : Nat.Primes => (p, (0 : ℕ))) from
      fun p q h => congrArg Prod.fst h)
  change Summable (fun p : Nat.Primes => gdTwistTerm (primeTangentCoefficient a)
    _root_.RHTower.eulerPrimePowerEnergy σ 0 (p, 0)) at h
  simpa only [primeTangentTerm_eq, Nat.cast_zero, zero_add, pow_one, one_mul] using h


/-- The holomorphic complex parameter curvature before taking its real part. -/
def complexParameterCurvature (U : ℂ × ℂ → ℂ) (s : ℂ) : ℂ :=
  -parameterDeriv (parameterDeriv (fun p => Complex.log (U p))) (0, s)

/-- Schwarz pairing makes the real phase energy holomorphic in the spectral variable. -/
def pairedParameterCurvature (U : ℂ × ℂ → ℂ) (s : ℂ) : ℂ :=
  (complexParameterCurvature U s + schwarzConjugate (complexParameterCurvature U) s) / 2

private theorem analyticAt_schwarzConjugate_one {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 1) :
    AnalyticAt ℂ (schwarzConjugate f) 1 := by
  obtain ⟨r, hr, hb⟩ := hf.exists_ball_analyticOnNhd
  have hconj {z : ℂ} (hz : z ∈ ball 1 r) : conj z ∈ ball 1 r := by
    have he : conj z - 1 = conj (z - 1) := by rw [map_sub, map_one]
    rw [mem_ball, dist_eq_norm, he, norm_conj]
    simpa only [mem_ball, dist_eq_norm] using hz
  have hd : DifferentiableOn ℂ (schwarzConjugate f) (ball 1 r) := by
    intro z hz
    have h := (hb (conj z) (hconj hz)).differentiableAt.conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))

theorem analyticAt_complexParameterCurvature {U : ℂ × ℂ → ℂ}
    (hU : AnalyticAt ℂ U (0, 1)) (hsl : U (0, 1) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (complexParameterCurvature U) 1 := by
  have hh := analyticAt_parameterDeriv (analyticAt_parameterDeriv (hU.clog hsl))
  have hc : AnalyticAt ℂ (fun s : ℂ =>
      parameterDeriv (parameterDeriv (fun p => Complex.log (U p))) (0, s)) 1 :=
    hh.comp (f := fun s : ℂ => ((0 : ℂ), s)) (analyticAt_const.prod analyticAt_id)
  exact hc.neg

theorem analyticAt_pairedParameterCurvature {U : ℂ × ℂ → ℂ}
    (hU : AnalyticAt ℂ U (0, 1)) (hsl : U (0, 1) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (pairedParameterCurvature U) 1 := by
  have hh := analyticAt_complexParameterCurvature hU hsl
  exact (hh.add (analyticAt_schwarzConjugate_one hh)).div analyticAt_const (by norm_num)

theorem pairedParameterCurvature_real (U : ℂ × ℂ → ℂ) (σ : ℝ) :
    pairedParameterCurvature U (σ : ℂ) = (residueCurvature U (σ : ℂ) : ℂ) := by
  have he (z : ℂ) : (z + conj z) / 2 = (z.re : ℂ) := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
  unfold pairedParameterCurvature schwarzConjugate
  rw [Complex.conj_ofReal, he]
  rfl

/-- Actual gauge regularization identifies the spectral curvature on the Euler side. -/
theorem gauge_curvature_real_eq_sum {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R M σ : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hσ : 1 < σ)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
    (hu0 : ∀ p, u p 0 = 1)
    (hunit : ∀ p, ∀ᶠ t : ℝ in 𝓝 0, ‖u p (t : ℂ)‖ = 1)
    (hphase : ∀ᶠ t : ℝ in 𝓝 0, ∀ p, u p (t : ℂ) = twist (x t) p)
    (hU : AnalyticAt ℂ U (0, (σ : ℂ)))
    (hsl : U (0, (σ : ℂ)) ∈ Complex.slitPlane)
    (hagree : ∀ᶠ t : ℝ in 𝓝 0,
      U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x t) (σ : ℂ)) :
    residueCurvature U (σ : ℂ) = ∑' p : Nat.Primes,
      (deriv (u p) 0).im ^ 2 * primeDamping σ p / (1 - primeDamping σ p) ^ 2 := by
  have hs := hasSum_phaseEulerLog_curvature hR hM hu hbd hu0 hunit
    (fun p => (primeDamping_pos σ p).le) (primeDamping_le_half hσ.le)
    (summable_primeDamping hσ)
  have hG := (phaseEulerLog_tsum_regular hR hM hu hbd hu0
    (fun p => (primeDamping_pos σ p).le) (primeDamping_le_half hσ.le)
    (summable_primeDamping hσ)).1
  rw [residueCurvature_eq_real_second hU hsl,
    real_second_logNorm_of_const_exp
      (show (σ : ℂ) - 1 ≠ 0 by exact_mod_cast (sub_pos.mpr hσ).ne') hG (by
        filter_upwards [hphase, hagree] with t hp ht
        rw [ht, exp_phaseEulerLog_eq_gaugeFibre hσ hp])]
  exact hs.tsum_eq.symm

private theorem real_mem_pole_ball {σ r : ℝ} (hσ : 1 < σ) (hσr : σ < 1 + r) :
    (σ : ℂ) ∈ ball 1 r := by
  have he : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [mem_ball, dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hσ)]
  linarith only [hσr]

/-- Real agreement determines a holomorphic function on the right half of a pole disk. -/
private theorem eqOn_pole_halfBall_of_real {F G : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (ball 1 r ∩ {s : ℂ | 1 < s.re}))
    (hG : AnalyticOnNhd ℂ G (ball 1 r ∩ {s : ℂ | 1 < s.re}))
    (he : ∀ σ : ℝ, 1 < σ → σ < 1 + r → F (σ : ℂ) = G (σ : ℂ)) :
    EqOn F G (ball 1 r ∩ {s : ℂ | 1 < s.re}) := by
  let c : ℝ := 1 + r / 2
  have hc : 1 < c := by dsimp [c]; linarith only [hr]
  have hcr : c < 1 + r := by dsimp [c]; linarith only [hr]
  have hmem : (c : ℂ) ∈ ball 1 r ∩ {s : ℂ | 1 < s.re} :=
    ⟨real_mem_pole_ball hc hcr, hc⟩
  have ht : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] c) (𝓝[≠] (c : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (Complex.continuous_ofReal.tendsto c).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      show (σ : ℂ) ≠ (c : ℂ)
      exact_mod_cast ne_of_gt hσ
  have hI : ∀ᶠ σ : ℝ in 𝓝 c, σ ∈ Ioo 1 (1 + r) := Ioo_mem_nhds hc hcr
  have her : ∀ᶠ σ : ℝ in 𝓝[>] c, F (σ : ℂ) = G (σ : ℂ) := by
    filter_upwards [hI.filter_mono nhdsWithin_le_nhds] with σ hσ
    exact he σ hσ.1 hσ.2
  exact hF.eqOn_of_preconnected_of_frequently_eq hG
    ((convex_ball (1 : ℂ) r).inter (convex_halfSpace_re_gt 1)).isPreconnected
    hmem (ht.frequently her.frequently)


/-- Bounded prime speeds give a holomorphic positive curvature series to the right of one. -/
theorem analyticOnNhd_primeTangentSeries {a : Nat.Primes → ℝ} {K : ℝ}
    (ha : ∀ p, |a p| ≤ K) :
    AnalyticOnNhd ℂ (primeTangentSeries a) {s : ℂ | 1 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (primeTangentSeries a) {s : ℂ | 1 < s.re} := by
    intro s hs
    have hmid : 1 < (1 + s.re) / 2 := by change 1 < s.re at hs; linarith only [hs]
    exact (_root_.RHTower.differentiableAt_gdSeries
      (primeTangentCoefficient_nonneg a) primePowerEnergy_nonneg
      (summable_primeTangentSeries_term ha hmid) (by
        change 1 < s.re at hs
        linarith only [hs])).differentiableWithinAt
  intro s hs
  exact hd.analyticAt (hopen.mem_nhds hs)

/-- A local holomorphic continuation forces quadratic prime energy below exponent one. -/
theorem prime_energy_below_one_of_continuation {a : Nat.Primes → ℝ} {K r : ℝ}
    {Q : ℂ → ℂ} (ha : ∀ p, |a p| ≤ K) (hr : 0 < r)
    (hQ : AnalyticOnNhd ℂ Q (ball 1 r))
    (he : ∀ σ : ℝ, 1 < σ → σ < 1 + r → Q (σ : ℂ) = primeTangentSeries a (σ : ℂ)) :
    ∃ σ : ℝ, σ < 1 ∧ Summable (fun p : Nat.Primes => a p ^ 2 * primeDamping σ p) := by
  by_contra hn
  have hdiv (σ : ℝ) (hσ : σ < 1) :
      ¬Summable (gdTwistTerm (primeTangentCoefficient a)
        _root_.RHTower.eulerPrimePowerEnergy σ 0) := by
    intro hs
    exact hn ⟨σ, hσ, summable_prime_energy_of_primeTangentSeries hs⟩
  have heq := eqOn_pole_halfBall_of_real hr (hQ.mono inter_subset_left)
    ((analyticOnNhd_primeTangentSeries ha).mono inter_subset_right) he
  exact _root_.RHTower.gdSeries_no_continuation_at_abscissa
    (primeTangentCoefficient_nonneg a) primePowerEnergy_nonneg
    (fun σ hσ => summable_primeTangentSeries_term ha hσ) hdiv hr hQ.differentiableOn
    (fun s hs hσ => heq ⟨hs, hσ⟩)

/-- Joint holomorphic regularization gives a power saving in the prime-phase tangent energy. -/
theorem gauge_tangent_power_saving {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hx0 : x 0 = 0)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hU : AnalyticAt ℂ U (0, 1))
    (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + R → ∀ t : ℝ, |t| < R →
      U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x t) (σ : ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      Summable (fun p : Nat.Primes => (deriv (u p) 0).im ^ 2 * (p : ℝ) ^ (-(1 - δ))) := by
  have ht0 : |(0 : ℝ)| < R := by simpa using hR
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hbd (⟨2, Nat.prime_two⟩ : Nat.Primes) 0 (mem_ball_self hR))
  have hu0 : ∀ p, u p 0 = 1 := by
    intro p
    simpa only [Complex.ofReal_zero, hx0, twist_trivial] using hphase 0 ht0 p
  have hphaseNear : ∀ᶠ t : ℝ in 𝓝 0, ∀ p, u p (t : ℂ) = twist (x t) p := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR : (0 : ℝ) ∈ ball 0 R)] with t ht
    exact hphase t (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht)
  have hunit : ∀ p, ∀ᶠ t : ℝ in 𝓝 0, ‖u p (t : ℂ)‖ = 1 := by
    intro p
    filter_upwards [hphaseNear] with t ht
    rw [ht p, norm_twist]
  let a : Nat.Primes → ℝ := fun p => (deriv (u p) 0).im
  have ha (p : Nat.Primes) : |a p| ≤ 2 * M / R :=
    (Complex.abs_im_le_norm _).trans
      (Bottcher.norm_deriv_le_of_bounded_on_ball hR (hu p) (hbd p) 0
        (mem_ball_self (by linarith only [hR])))
  have hU0 : U (0, 1) = 1 := regularized_gauge_initial_residue hR hx0 hU.continuousAt
    (fun σ hσ hσR => by simpa only [Complex.ofReal_zero] using hagree σ hσ hσR 0 ht0)
  have hsl : U (0, 1) ∈ Complex.slitPlane := by rw [hU0]; exact Or.inl (by norm_num)
  have hQ := analyticAt_pairedParameterCurvature hU hsl
  have hp : ContinuousAt (fun s : ℂ => ((0 : ℂ), s)) 1 :=
    continuousAt_const.prodMk continuousAt_id
  have hUa : ∀ᶠ s : ℂ in 𝓝 1, AnalyticAt ℂ U (0, s) :=
    hp.tendsto.eventually hU.eventually_analyticAt
  have hUs : ∀ᶠ s : ℂ in 𝓝 1, U (0, s) ∈ Complex.slitPlane :=
    (hU.continuousAt.tendsto.comp hp.tendsto).eventually
      (Complex.isOpen_slitPlane.mem_nhds hsl)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (hQ.eventually_analyticAt.and (hUa.and hUs))
  let r : ℝ := min ε R
  have hr : 0 < r := lt_min hε hR
  have hb' (s : ℂ) (hs : s ∈ ball 1 r) :
      AnalyticAt ℂ (pairedParameterCurvature U) s ∧
        AnalyticAt ℂ U (0, s) ∧ U (0, s) ∈ Complex.slitPlane :=
    hb ((ball_subset_ball (min_le_left ε R)) hs)
  have hQr : AnalyticOnNhd ℂ (pairedParameterCurvature U) (ball 1 r) :=
    fun s hs => (hb' s hs).1
  have he (σ : ℝ) (hσ : 1 < σ) (hσr : σ < 1 + r) :
      pairedParameterCurvature U (σ : ℂ) = primeTangentSeries a (σ : ℂ) := by
    have hs := (hb' (σ : ℂ) (real_mem_pole_ball hσ hσr)).2
    have hσR : σ < 1 + R := by
      have hrR : r ≤ R := min_le_right ε R
      linarith only [hσr, hrR]
    rw [pairedParameterCurvature_real, primeTangentSeries_real ha hσ,
      gauge_curvature_real_eq_sum hR hM hσ hu hbd hu0 hunit hphaseNear hs.1 hs.2 (by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR : (0 : ℝ) ∈ ball 0 R)] with t ht
        exact hagree σ hσ hσR t (by
          simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht))]
  obtain ⟨σ, hσ, hsum⟩ := prime_energy_below_one_of_continuation ha hr hQr he
  let τ : ℝ := max σ (3 / 4)
  have hστ : σ ≤ τ := le_max_left _ _
  have hτ : τ < 1 := max_lt hσ (by norm_num)
  have hτ0 : (3 / 4 : ℝ) ≤ τ := le_max_right _ _
  have hsτ : Summable (fun p : Nat.Primes => a p ^ 2 * primeDamping τ p) := by
    apply hsum.of_nonneg_of_le
      (fun p => mul_nonneg (sq_nonneg _) (primeDamping_pos τ p).le)
    intro p
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast p.2.one_lt.le : (1 : ℝ) ≤ (p : ℝ)) (neg_le_neg hστ)
  refine ⟨1 - τ, sub_pos.mpr hτ, by linarith only [hτ0], ?_⟩
  simpa only [sub_sub_cancel, a, primeDamping] using hsτ

#print axioms primeTangentSeries_real
#print axioms prime_energy_below_one_of_continuation
#print axioms gauge_tangent_power_saving
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
