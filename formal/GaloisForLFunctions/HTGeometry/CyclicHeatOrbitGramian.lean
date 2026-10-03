import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp
import GaloisForLFunctions.HTGeometry.SquareSummableFrameSynthesis
import GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The cyclic heat-orbit Gramian

A heat source is a spectrum `λ : ι → ℝ` with a uniform positive gap `λ_j ≥ λ₀ > 0` together with
a marked vector `v ∈ ℓ²(ι)`.  The heat semigroup `S_t = e^{-tL}` is diagonal, `S_t e_j =
e^{-tλ_j} e_j`.  The orbit Gramian

`G = ∫_0^∞ |S_t v⟩⟨S_t v| dt`   (**(OG.7)**)

is a Bochner integral in the Schatten-one Banach space.  It equals `W W^*` for the reachability
map `W u = ∫_0^∞ u(t) S_t v dt`, with kernel `⟨e_i, G e_j⟩ = v_i v̄_j / (λ_i + λ_j)` (**(OG.9)**),
trace `Σ_j |v_j|²/(2λ_j) = ∫_0^∞ ‖S_t v‖² dt` (**(OG.8)**), and it is the unique bounded solution
of the weak Lyapunov law `LG + GL = |v⟩⟨v|` (**(OG.10)**).

For a simple spectrum tending to infinity and a fully supported `v`,
`⟨x, Gx⟩ = ∫_0^∞ |⟨x, S_t v⟩|² dt` (**(OG.25)**) vanishes only at `x = 0` (**(OG.11)**).  The
function `t ↦ ⟨x, S_t v⟩` is the exponential sum `Σ_j a_j e^{-λ_j t}` with absolutely summable
coefficients, and such a sum vanishing on `(0, ∞)` has all coefficients zero: multiplying by
`e^{λ_{j₀} t}` for the least exponent with `a_{j₀} ≠ 0` and letting `t → ∞` isolates `a_{j₀}`.
Finally the reporter `D = (1 + L)^{-1}` is compact and the common commutant of `D` and `P = |v⟩⟨v|`
is scalar (**(OG.17)**).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*}

local notation "ℓ²ι" => lp (fun _ : ι => ℂ) 2

/-! ## The orbit Gramian of a path of operators -/

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The orbit Gramian `∫_0^∞ |S_t v⟩⟨S_t v| dt` of a path `S` of operators, as a Schatten-one
Bochner integral. -/
def orbitGramianOf (S : ℝ → H →L[ℂ] H) (v : H) : SchattenOneOperator H :=
  ∫ t in Ioi (0 : ℝ), positiveRankOneSchattenOne (S t v)

/-- The matrix coefficient `X ↦ ⟨x, X y⟩` as a continuous functional on `𝒮₁`. -/
def schattenOnePairing (x y : H) : SchattenOneOperator H →L[ℂ] ℂ :=
  (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ H y).comp schattenOneCoeCLM)

theorem schattenOnePairing_apply (x y : H) (X : SchattenOneOperator H) :
    schattenOnePairing x y X = ⟪x, (X : H →L[ℂ] H) y⟫_ℂ := rfl

theorem schattenOnePairing_positiveRankOne (x y a : H) :
    schattenOnePairing x y (positiveRankOneSchattenOne a) = ⟪x, a⟫_ℂ * ⟪a, y⟫_ℂ := by
  rw [schattenOnePairing_apply, positiveRankOneSchattenOne, rankOneSchattenOne_coe,
    InnerProductSpace.rankOne_apply, inner_smul_right, mul_comm]

end General

/-! ## Heat sources -/

/-- A heat source: a spectrum with a uniform positive gap, and a marked vector. -/
structure HeatSource (ι : Type*) where
  lam : ι → ℝ
  gap : ℝ
  gap_pos : 0 < gap
  gap_le : ∀ j, gap ≤ lam j
  v : lp (fun _ : ι => ℂ) 2

namespace HeatSource

variable (s : HeatSource ι)

theorem lam_pos (j : ι) : 0 < s.lam j := s.gap_pos.trans_le (s.gap_le j)

theorem lam_nonneg (j : ι) : 0 ≤ s.lam j := (s.lam_pos j).le

/-- Simple spectrum. -/
def Simple : Prop := Function.Injective s.lam

/-- The spectrum tends to infinity (compact resolvent). -/
def Proper : Prop := Tendsto s.lam cofinite atTop

/-- The marked vector has nonzero coefficient in every source coordinate. -/
def FullSupport : Prop := ∀ j, s.v j ≠ 0

theorem summable_norm_sq : Summable fun j => ‖s.v j‖ ^ 2 := by
  have h := (lp.memℓp s.v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using h

end HeatSource

theorem inner_single_one_left [DecidableEq ι] (x : ℓ²ι) (i : ι) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), x⟫_ℂ = x i := by
  rw [lp.inner_single_left]
  simp

theorem inner_single_one_right [DecidableEq ι] (x : ℓ²ι) (j : ι) :
    ⟪x, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ = starRingEnd ℂ (x j) := by
  rw [← inner_conj_symm, inner_single_one_left]

/-! ## The heat semigroup -/

/-- The heat factor `e^{-tλ_j}`, with time clipped at `0`. -/
def heatFactor (lam : ι → ℝ) (t : ℝ) (j : ι) : ℂ :=
  (Real.exp (-(max t 0 * lam j)) : ℂ)

theorem norm_heatFactor_le {lam : ι → ℝ} (hlam : ∀ j, 0 ≤ lam j) (t : ℝ) (j : ι) :
    ‖heatFactor lam t j‖ ≤ 1 := by
  rw [heatFactor, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), Real.exp_le_one_iff]
  have := mul_nonneg (le_max_right t 0) (hlam j)
  linarith

theorem heatFactor_of_nonneg (lam : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (j : ι) :
    heatFactor lam t j = (Real.exp (-(t * lam j)) : ℂ) := by
  rw [heatFactor, max_eq_left ht]

theorem continuous_heatFactor (lam : ι → ℝ) (j : ι) : Continuous fun t => heatFactor lam t j := by
  unfold heatFactor
  fun_prop

/-- The heat semigroup `S_t = e^{-tL}`, diagonal in the source basis. -/
def heatSemigroup {lam : ι → ℝ} (hlam : ∀ j, 0 ≤ lam j) (t : ℝ) : ℓ²ι →L[ℂ] ℓ²ι :=
  LpDiagonal.lpDiag (heatFactor lam t) 1 zero_le_one (norm_heatFactor_le hlam t)

theorem heatSemigroup_apply {lam : ι → ℝ} (hlam : ∀ j, 0 ≤ lam j) (t : ℝ) (x : ℓ²ι) (j : ι) :
    heatSemigroup hlam t x j = heatFactor lam t j * x j :=
  LpDiagonal.lpDiag_coe _ _ _ _ _ _

/-! ## Exponential integrals -/

theorem integral_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(a * t)) = 1 / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at h
  rw [show (fun t : ℝ => Real.exp (-(a * t))) = fun t => Real.exp (-a * t) by
    funext t; ring_nf, h]
  field_simp

theorem integrableOn_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-(a * t))) (Ioi 0) := by
  have h := exp_neg_integrableOn_Ioi 0 ha
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  ring_nf

/-- Every heat trajectory `t ↦ S_t x` is norm continuous. -/
theorem continuous_heatSemigroup_apply {lam : ι → ℝ} (hlam : ∀ j, 0 ≤ lam j) (x : ℓ²ι) :
    Continuous fun t => heatSemigroup hlam t x := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun t => ‖heatSemigroup hlam t x - heatSemigroup hlam t₀ x‖ ^ 2) (𝓝 t₀)
      (𝓝 0) := by
    have hrw : ∀ t, ‖heatSemigroup hlam t x - heatSemigroup hlam t₀ x‖ ^ 2 =
        ∑' j, ‖(heatFactor lam t j - heatFactor lam t₀ j) * x j‖ ^ 2 := fun t => by
      rw [lp_two_norm_sq_eq_tsum]
      refine tsum_congr fun j => ?_
      rw [lp.coeFn_sub, Pi.sub_apply, heatSemigroup_apply, heatSemigroup_apply, sub_mul]
    simp_rw [hrw]
    rw [show (0 : ℝ) = ∑' _ : ι, (0 : ℝ) by simp]
    refine tendsto_tsum_of_dominated_convergence (bound := fun j => 4 * ‖x j‖ ^ 2)
      ((summable_norm_sq_lp x).mul_left 4) (fun j => ?_) (Eventually.of_forall fun t j => ?_)
    · have hc : Continuous fun t => ‖(heatFactor lam t j - heatFactor lam t₀ j) * x j‖ ^ 2 :=
        ((((continuous_heatFactor lam j).sub continuous_const).mul continuous_const).norm).pow 2
      have h' := hc.tendsto t₀
      simpa using h'
    · rw [norm_pow, norm_norm, norm_mul]
      have h1 := norm_heatFactor_le hlam t j
      have h2 := norm_heatFactor_le hlam t₀ j
      have h3 : ‖heatFactor lam t j - heatFactor lam t₀ j‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by linarith)
      have h4 := norm_nonneg (heatFactor lam t j - heatFactor lam t₀ j)
      have h5 := norm_nonneg (x j)
      calc (‖heatFactor lam t j - heatFactor lam t₀ j‖ * ‖x j‖) ^ 2
          ≤ (2 * ‖x j‖) ^ 2 := pow_le_pow_left₀ (by positivity) (by nlinarith) 2
        _ = 4 * ‖x j‖ ^ 2 := by ring
  have h := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [Real.sqrt_sq (norm_nonneg _)]

namespace HeatSource

variable (s : HeatSource ι)

/-- The heat orbit `t ↦ S_t v`. -/
def heatOrbit (t : ℝ) : ℓ²ι := heatSemigroup s.lam_nonneg t s.v

theorem heatOrbit_apply (t : ℝ) (j : ι) : s.heatOrbit t j = heatFactor s.lam t j * s.v j :=
  heatSemigroup_apply _ _ _ _

theorem norm_heatOrbit_sq {t : ℝ} (ht : 0 ≤ t) :
    ‖s.heatOrbit t‖ ^ 2 = ∑' j, Real.exp (-(2 * s.lam j * t)) * ‖s.v j‖ ^ 2 := by
  rw [lp_two_norm_sq_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [heatOrbit_apply, heatFactor_of_nonneg _ ht, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _), mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem norm_heatOrbit_sq_le {t : ℝ} (ht : 0 ≤ t) :
    ‖s.heatOrbit t‖ ^ 2 ≤ Real.exp (-(2 * s.gap * t)) * ‖s.v‖ ^ 2 := by
  rw [norm_heatOrbit_sq s ht, lp_two_norm_sq_eq_tsum, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) ?_ (s.summable_norm_sq.mul_left _)
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
    have := s.gap_le j
    nlinarith
  · refine (s.summable_norm_sq.mul_left 1).of_nonneg_of_le (fun j => by positivity) fun j => ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Real.exp_le_one_iff]
    have := s.lam_nonneg j
    nlinarith

/-- The heat orbit is norm continuous. -/
theorem continuous_heatOrbit : Continuous s.heatOrbit :=
  continuous_heatSemigroup_apply s.lam_nonneg s.v

/-- The reachability column `t ↦ v̄_j e^{-λ_j t}` in `L²((0,∞))`. -/
def heatFrame (j : ι) : HalfLineL2 :=
  (starRingEnd ℂ (s.v j) * ((Real.sqrt (2 * s.lam j))⁻¹ : ℝ)) • gammaCoherentVector 1 (s.lam_pos j)

theorem norm_sq_heatFrame (j : ι) : ‖s.heatFrame j‖ ^ 2 = ‖s.v j‖ ^ 2 / (2 * s.lam j) := by
  have hl := s.lam_pos j
  rw [heatFrame, norm_smul, norm_gammaCoherentVector, mul_one, norm_mul, Complex.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, inv_pow,
    Real.sq_sqrt (by positivity)]
  ring

theorem inner_heatFrame (i j : ι) :
    ⟪s.heatFrame i, s.heatFrame j⟫_ℂ = s.v i * starRingEnd ℂ (s.v j) / ((s.lam i + s.lam j : ℝ) : ℂ) := by
  have hi := s.lam_pos i
  have hj := s.lam_pos j
  rw [heatFrame, heatFrame, inner_smul_left, inner_smul_right, inner_gammaCoherentVector, map_mul,
    Complex.conj_conj, Complex.conj_ofReal, pow_one]
  have hsi := Real.sqrt_pos.2 (show 0 < 2 * s.lam i by positivity)
  have hsj := Real.sqrt_pos.2 (show 0 < 2 * s.lam j by positivity)
  have hprod : Real.sqrt (2 * s.lam i) * Real.sqrt (2 * s.lam j) = 2 * Real.sqrt (s.lam i * s.lam j) := by
    rw [← Real.sqrt_mul (by positivity), show 2 * s.lam i * (2 * s.lam j) = 2 ^ 2 * (s.lam i * s.lam j) by
      ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hS : (0 : ℝ) < s.lam i + s.lam j := by linarith
  have hkey : (Real.sqrt (2 * s.lam i))⁻¹ * (Real.sqrt (2 * s.lam j))⁻¹ *
      (2 * Real.sqrt (s.lam i * s.lam j) / (s.lam i + s.lam j)) = 1 / (s.lam i + s.lam j) := by
    rw [← hprod]
    field_simp
  have hkeyC := congrArg (fun x : ℝ => (x : ℂ)) hkey
  push_cast at hkeyC
  have hSC : ((s.lam i : ℂ) + s.lam j) ≠ 0 := by exact_mod_cast hS.ne'
  push_cast
  linear_combination (s.v i * starRingEnd ℂ (s.v j)) * hkeyC

theorem summable_norm_sq_heatFrame : Summable fun j => ‖s.heatFrame j‖ ^ 2 := by
  simp_rw [norm_sq_heatFrame]
  refine (s.summable_norm_sq.mul_left (1 / (2 * s.gap))).of_nonneg_of_le
    (fun j => by have := s.lam_pos j; positivity) fun j => ?_
  have hl := s.lam_pos j
  have hg := s.gap_pos
  rw [div_eq_mul_one_div, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact one_div_le_one_div_of_le (by positivity) (by linarith [s.gap_le j])

/-- **(OG.8)** `tr G ≤ ‖v‖²/(2λ₀)`; for a unit vector `tr G ≤ 1/(2λ₀)`. -/
theorem tsum_le_gap : ∑' j, ‖s.v j‖ ^ 2 / (2 * s.lam j) ≤ ‖s.v‖ ^ 2 / (2 * s.gap) := by
  rw [lp_two_norm_sq_eq_tsum, ← tsum_div_const]
  refine Summable.tsum_le_tsum (fun j => ?_) ?_ (s.summable_norm_sq.div_const _)
  · have hl := s.lam_pos j
    exact div_le_div_of_nonneg_left (by positivity) (by linarith [s.gap_pos])
      (by linarith [s.gap_le j])
  · have h := s.summable_norm_sq_heatFrame
    simp_rw [norm_sq_heatFrame] at h
    exact h

/-- The orbit integrand `t ↦ |S_t v⟩⟨S_t v|` in `𝒮₁`. -/
def orbitIntegrand (t : ℝ) : SchattenOneOperator ℓ²ι := positiveRankOneSchattenOne (s.heatOrbit t)

theorem continuous_orbitIntegrand : Continuous s.orbitIntegrand :=
  continuous_positiveRankOneSchattenOne.comp s.continuous_heatOrbit

theorem integrableOn_norm_heatOrbit_sq :
    IntegrableOn (fun t => ‖s.heatOrbit t‖ ^ 2) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_mul (by linarith [s.gap_pos] :
      (0 : ℝ) < 2 * s.gap)).mul_const (‖s.v‖ ^ 2))
    ((continuous_norm.comp s.continuous_heatOrbit).pow 2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact s.norm_heatOrbit_sq_le (le_of_lt ht)

theorem integrableOn_orbitIntegrand : IntegrableOn s.orbitIntegrand (Ioi 0) :=
  Integrable.mono' s.integrableOn_norm_heatOrbit_sq s.continuous_orbitIntegrand.aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [orbitIntegrand, norm_positiveRankOneSchattenOne])

/-- **(OG.7)** The orbit Gramian as a Schatten-one Bochner integral. -/
def orbitGramianS1 : SchattenOneOperator ℓ²ι := orbitGramianOf (heatSemigroup s.lam_nonneg) s.v

theorem orbitGramianS1_eq_integral :
    s.orbitGramianS1 = ∫ t in Ioi (0 : ℝ), s.orbitIntegrand t := rfl

theorem schattenOnePairing_orbitGramianS1 (x y : ℓ²ι) :
    schattenOnePairing x y s.orbitGramianS1 =
      ∫ t in Ioi (0 : ℝ), ⟪x, s.heatOrbit t⟫_ℂ * ⟪s.heatOrbit t, y⟫_ℂ := by
  rw [orbitGramianS1_eq_integral, ← (schattenOnePairing x y).integral_comp_comm
    s.integrableOn_orbitIntegrand]
  simp_rw [orbitIntegrand, schattenOnePairing_positiveRankOne]

/-- The source projection `P = |v⟩⟨v|`. -/
def heatProjection : ℓ²ι →L[ℂ] ℓ²ι := InnerProductSpace.rankOne ℂ s.v s.v

section Countable

variable [Countable ι]

/-- **(OG.8)** `∫_0^∞ ‖S_t v‖² dt = Σ_j |v_j|²/(2λ_j)`. -/
theorem integral_norm_heatOrbit_sq :
    ∫ t in Ioi (0 : ℝ), ‖s.heatOrbit t‖ ^ 2 = ∑' j, ‖s.v j‖ ^ 2 / (2 * s.lam j) := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖s.heatOrbit t‖ ^ 2 =
      ∑' j, Real.exp (-(2 * s.lam j * t)) * ‖s.v j‖ ^ 2 := fun t ht =>
    s.norm_heatOrbit_sq (le_of_lt ht)
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : ∀ j, ∫ t in Ioi (0 : ℝ), Real.exp (-(2 * s.lam j * t)) * ‖s.v j‖ ^ 2 =
      ‖s.v j‖ ^ 2 / (2 * s.lam j) := fun j => by
    have hl := s.lam_pos j
    rw [integral_mul_const, integral_exp_neg_mul (by positivity)]
    ring
  have hintg : ∀ j, Integrable (fun t => Real.exp (-(2 * s.lam j * t)) * ‖s.v j‖ ^ 2)
      (volume.restrict (Ioi 0)) := fun j =>
    (integrableOn_exp_neg_mul (by have := s.lam_pos j; positivity)).mul_const _
  rw [← integral_tsum_of_summable_integral_norm hintg]
  · exact tsum_congr hint
  · simp_rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)), hint]
    have h := s.summable_norm_sq_heatFrame
    simp_rw [norm_sq_heatFrame] at h
    exact h

end Countable

section DecidableEq

variable [DecidableEq ι]

/-- The analysis map `W^* : x ↦ (t ↦ ⟨S_t v, x⟩)`. -/
def heatAnalysis : ℓ²ι →L[ℂ] HalfLineL2 :=
  squareSummableSynthesis s.heatFrame s.summable_norm_sq_heatFrame

/-- **(OG.15)** The reachability map `W u = ∫_0^∞ u(t) S_t v dt`. -/
def heatReachability : HalfLineL2 →L[ℂ] ℓ²ι := ContinuousLinearMap.adjoint s.heatAnalysis

/-- **(OG.7)–(OG.9)** The orbit Gramian `G = W W^*`. -/
def orbitGramian : ℓ²ι →L[ℂ] ℓ²ι := s.heatReachability ∘L s.heatAnalysis

theorem heatAnalysis_single (j : ι) : s.heatAnalysis (lp.single 2 j 1) = s.heatFrame j := by
  rw [heatAnalysis, squareSummableSynthesis_single, one_smul]

/-- **(OG.9)** `⟨e_i, G e_j⟩ = v_i v̄_j / (λ_i + λ_j)`. -/
theorem inner_single_orbitGramian (i j : ι) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), s.orbitGramian (lp.single 2 j 1)⟫_ℂ =
      s.v i * starRingEnd ℂ (s.v j) / ((s.lam i + s.lam j : ℝ) : ℂ) := by
  rw [orbitGramian, heatReachability, heatAnalysis, inner_single_rightGram_single, inner_heatFrame]

/-- **(OG.8)** `G ≥ 0`, `G ∈ 𝒮₁`, `tr G = ‖G‖₁ = Σ_j |v_j|²/(2λ_j)`. -/
theorem orbitGramian_traceClass :
    s.orbitGramian.IsPositive ∧ MemSchattenClass 1 s.orbitGramian ∧
      s.orbitGramian.opTrace = ((∑' j, ‖s.v j‖ ^ 2 / (2 * s.lam j) : ℝ) : ℂ) ∧
      traceNorm ℓ²ι s.orbitGramian = ∑' j, ‖s.v j‖ ^ 2 / (2 * s.lam j) := by
  obtain ⟨hpos, hS, htr⟩ := rightGram_traceClass s.summable_norm_sq_heatFrame
  simp_rw [norm_sq_heatFrame] at htr
  refine ⟨hpos, hS, htr, ?_⟩
  exact (traceNorm_eq_re_opTrace_of_isPositive hS hpos).trans (by rw [htr, Complex.ofReal_re])

/-- **(OG.7) = (OG.9)** The Bochner integral is the Gram operator `W W^*`. -/
theorem orbitGramianS1_eq : (s.orbitGramianS1 : ℓ²ι →L[ℂ] ℓ²ι) = s.orbitGramian := by
  refine ext_of_inner_single fun i j => ?_
  rw [← schattenOnePairing_apply, schattenOnePairing_orbitGramianS1, inner_single_orbitGramian]
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), s.heatOrbit t⟫_ℂ *
      ⟪s.heatOrbit t, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ =
      s.v i * starRingEnd ℂ (s.v j) * ((Real.exp (-((s.lam i + s.lam j) * t)) : ℝ) : ℂ) := by
    intro t ht
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    rw [inner_single_one_left, inner_single_one_right, s.heatOrbit_apply,
      s.heatOrbit_apply, heatFactor_of_nonneg _ ht', heatFactor_of_nonneg _ ht', map_mul,
      Complex.conj_ofReal]
    rw [show -((s.lam i + s.lam j) * t) = -(t * s.lam i) + -(t * s.lam j) by ring, Real.exp_add]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_complex_ofReal,
    integral_exp_neg_mul (by linarith [s.lam_pos i, s.lam_pos j])]
  push_cast
  ring

/-- **(OG.25)** `⟨x, G x⟩ = ∫_0^∞ |⟨x, S_t v⟩|² dt`. -/
theorem inner_orbitGramian_self (x : ℓ²ι) :
    ⟪x, s.orbitGramian x⟫_ℂ = ((∫ t in Ioi (0 : ℝ), ‖⟪x, s.heatOrbit t⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← s.orbitGramianS1_eq, ← schattenOnePairing_apply, schattenOnePairing_orbitGramianS1,
    ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [← inner_conj_symm (s.heatOrbit t) x, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem inner_single_heatProjection (i j : ι) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), s.heatProjection (lp.single 2 j 1)⟫_ℂ =
      s.v i * starRingEnd ℂ (s.v j) := by
  rw [heatProjection, InnerProductSpace.rankOne_apply, inner_smul_right, inner_single_one_left,
    inner_single_one_right, mul_comm]

/-- **(OG.10)** `⟨L e_i, G e_j⟩ + ⟨e_i, G L e_j⟩ = ⟨e_i, P e_j⟩`. -/
theorem lyapunov_orbitGramian (i j : ι) :
    ⟪(s.lam i : ℂ) • (lp.single 2 i (1 : ℂ) : ℓ²ι), s.orbitGramian (lp.single 2 j 1)⟫_ℂ +
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), s.orbitGramian ((s.lam j : ℂ) • lp.single 2 j 1)⟫_ℂ =
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), s.heatProjection (lp.single 2 j 1)⟫_ℂ := by
  rw [inner_smul_left, map_smul, inner_smul_right, inner_single_orbitGramian,
    inner_single_heatProjection, Complex.conj_ofReal]
  have hS : ((s.lam i : ℂ) + s.lam j) ≠ 0 := by
    exact_mod_cast (show (0 : ℝ) < s.lam i + s.lam j by linarith [s.lam_pos i, s.lam_pos j]).ne'
  push_cast
  field_simp

/-- **(OG.10) Uniqueness.**  `G` is the only bounded operator obeying the weak Lyapunov law. -/
theorem eq_orbitGramian_of_lyapunov (X : ℓ²ι →L[ℂ] ℓ²ι)
    (h : ∀ i j, ⟪(s.lam i : ℂ) • (lp.single 2 i (1 : ℂ) : ℓ²ι), X (lp.single 2 j 1)⟫_ℂ +
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), X ((s.lam j : ℂ) • lp.single 2 j 1)⟫_ℂ =
      ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), s.heatProjection (lp.single 2 j 1)⟫_ℂ) :
    X = s.orbitGramian := by
  refine ext_of_inner_single fun i j => ?_
  have hij := h i j
  rw [inner_smul_left, map_smul, inner_smul_right, inner_single_heatProjection,
    Complex.conj_ofReal] at hij
  rw [inner_single_orbitGramian]
  have hS : ((s.lam i : ℂ) + s.lam j) ≠ 0 := by
    exact_mod_cast (show (0 : ℝ) < s.lam i + s.lam j by linarith [s.lam_pos i, s.lam_pos j]).ne'
  push_cast
  rw [eq_div_iff hS]
  linear_combination hij



end DecidableEq

end HeatSource

/-! ## Complete heat observation -/

/-- An absolutely summable exponential sum `Σ_j a_j e^{-λ_j t}` with simple exponents tending to
infinity that vanishes for every `t > 0` has all coefficients zero. -/
theorem eq_zero_of_tsum_exp_eq_zero {lam : ι → ℝ} (hinj : Function.Injective lam)
    (hprop : Tendsto lam cofinite atTop) {a : ι → ℂ} (ha : Summable fun j => ‖a j‖)
    (h : ∀ t : ℝ, 0 < t → ∑' j, a j * (Real.exp (-(t * lam j)) : ℂ) = 0) : a = 0 := by
  classical
  by_contra hne
  obtain ⟨j₁, hj₁⟩ : ∃ j, a j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have hfin : {j | lam j ≤ lam j₁}.Finite := by
    have := hprop.eventually (eventually_gt_atTop (lam j₁))
    rw [Filter.eventually_cofinite] at this
    simpa using this
  set F := (hfin.toFinset.filter fun j => a j ≠ 0) with hF
  have hFne : F.Nonempty := ⟨j₁, by simp [hF, hj₁]⟩
  obtain ⟨j₀, hj₀F, hmin⟩ := F.exists_min_image lam hFne
  have ha₀ : a j₀ ≠ 0 := (Finset.mem_filter.1 hj₀F).2
  have hj₀le : lam j₀ ≤ lam j₁ := by
    have := (Finset.mem_filter.1 hj₀F).1
    simpa using this
  have hgt : ∀ j, a j ≠ 0 → j ≠ j₀ → lam j₀ < lam j := by
    intro j hj hjne
    by_cases hjF : lam j ≤ lam j₁
    · have hle := hmin j (by simp [hF, hjF, hj])
      exact lt_of_le_of_ne hle fun heq => hjne (hinj heq.symm)
    · push Not at hjF
      linarith
  have hlim : Tendsto (fun t : ℝ => ∑' j, a j * (Real.exp (-(t * (lam j - lam j₀))) : ℂ))
      atTop (𝓝 (∑' j, if j = j₀ then a j₀ else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun j => ‖a j‖) ha (fun j => ?_)
      ((eventually_ge_atTop 0).mono fun t ht j => ?_)
    · by_cases hj : j = j₀
      · subst hj
        simp
      · rw [if_neg hj]
        by_cases haj : a j = 0
        · simp [haj]
        · have hpos := sub_pos.2 (hgt j haj hj)
          have hexp : Tendsto (fun t : ℝ => Real.exp (-(t * (lam j - lam j₀)))) atTop (𝓝 0) :=
            Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
              (tendsto_id.atTop_mul_const hpos))
          have := (Complex.continuous_ofReal.tendsto 0).comp hexp
          simpa using this.const_mul (a j)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      by_cases haj : a j = 0
      · simp [haj]
      · have hle : lam j₀ ≤ lam j := by
          by_cases hj : j = j₀
          · rw [hj]
          · exact (hgt j haj hj).le
        have : Real.exp (-(t * (lam j - lam j₀))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith
        calc ‖a j‖ * Real.exp (-(t * (lam j - lam j₀))) ≤ ‖a j‖ * 1 :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = ‖a j‖ := mul_one _
  rw [tsum_ite_eq] at hlim
  have hzero : ∀ t : ℝ, 0 < t → ∑' j, a j * (Real.exp (-(t * (lam j - lam j₀))) : ℂ) = 0 := by
    intro t ht
    have hrw : ∀ j, a j * (Real.exp (-(t * (lam j - lam j₀))) : ℂ) =
        (Real.exp (t * lam j₀) : ℂ) * (a j * (Real.exp (-(t * lam j)) : ℂ)) := fun j => by
      rw [show -(t * (lam j - lam j₀)) = t * lam j₀ + -(t * lam j) by ring, Real.exp_add]
      push_cast
      ring
    simp_rw [hrw]
    rw [tsum_mul_left, h t ht, mul_zero]
  have hev : (fun t : ℝ => ∑' j, a j * (Real.exp (-(t * (lam j - lam j₀))) : ℂ)) =ᶠ[atTop]
      fun _ => 0 := (eventually_gt_atTop 0).mono fun t ht => hzero t ht
  exact ha₀ (tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds)

namespace HeatSource

variable (s : HeatSource ι) [DecidableEq ι]

omit [DecidableEq ι] in
theorem inner_heatOrbit_eq_tsum (x : ℓ²ι) {t : ℝ} (ht : 0 ≤ t) :
    ⟪x, s.heatOrbit t⟫_ℂ = ∑' j, starRingEnd ℂ (x j) * s.v j * (Real.exp (-(t * s.lam j)) : ℂ) := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [s.heatOrbit_apply, heatFactor_of_nonneg _ ht]
  simp only [inner, starRingEnd_apply]
  ring

omit [DecidableEq ι] in
/-- **(OG.11) Complete heat observation.**  `∫_0^∞ |⟨x, S_t v⟩|² dt = 0` forces `x = 0`. -/
theorem eq_zero_of_integral_heatObservation_eq_zero (hS : s.Simple) (hP : s.Proper)
    (hF : s.FullSupport) (x : ℓ²ι) (h : ∫ t in Ioi (0 : ℝ), ‖⟪x, s.heatOrbit t⟫_ℂ‖ ^ 2 = 0) :
    x = 0 := by
  have hcont : Continuous fun t => ‖⟪x, s.heatOrbit t⟫_ℂ‖ ^ 2 :=
    ((continuous_const.inner s.continuous_heatOrbit).norm).pow 2
  have hint : IntegrableOn (fun t => ‖⟪x, s.heatOrbit t⟫_ℂ‖ ^ 2) (Ioi 0) := by
    refine Integrable.mono' (s.integrableOn_norm_heatOrbit_sq.const_mul (‖x‖ ^ 2))
      hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun t => sq_nonneg _) hint).1 h
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont.continuousOn continuousOn_const
  have hobs : ∀ t : ℝ, 0 < t → ⟪x, s.heatOrbit t⟫_ℂ = 0 := fun t ht => by
    have := heq ht
    simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
    exact this
  have hsum : Summable fun j => ‖starRingEnd ℂ (x j) * s.v j‖ := by
    have hx : Summable fun j => ‖x j‖ ^ 2 := by
      have h := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa using h
    refine ((hx.add s.summable_norm_sq).div_const 2).of_nonneg_of_le (fun _ => norm_nonneg _)
      fun j => ?_
    rw [norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖x j‖ - ‖s.v j‖)]
  have hcoef := eq_zero_of_tsum_exp_eq_zero hS hP hsum fun t ht => by
    rw [← s.inner_heatOrbit_eq_tsum x (le_of_lt ht)]
    exact hobs t ht
  refine lp.ext (funext fun j => ?_)
  have hj := congrFun hcoef j
  simp only [Pi.zero_apply, mul_eq_zero, map_eq_zero] at hj
  rcases hj with hj | hj
  · simpa using hj
  · exact absurd hj (hF j)

/-- **(OG.11)** `G` is injective. -/
theorem orbitGramian_injective (hS : s.Simple) (hP : s.Proper) (hF : s.FullSupport) :
    Function.Injective s.orbitGramian := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine s.eq_zero_of_integral_heatObservation_eq_zero hS hP hF x ?_
  have h := s.inner_orbitGramian_self x
  rw [hx, inner_zero_right] at h
  exact_mod_cast h.symm

/-! ## The reporter and the scalar common commutant -/

omit [DecidableEq ι] in
theorem norm_reporterFactor_le (j : ι) : ‖((1 + s.lam j)⁻¹ : ℝ)‖ ≤ 1 := by
  have hl := s.lam_nonneg j
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_le_one_of_one_le₀ (by linarith)

/-- **(OG.6)** The reporter `D = (1 + L)^{-1}`. -/
def heatReporter : ℓ²ι →L[ℂ] ℓ²ι :=
  LpDiagonal.lpDiag (fun j => (((1 + s.lam j)⁻¹ : ℝ) : ℂ)) 1 zero_le_one fun j => by
    rw [Complex.norm_real]
    exact s.norm_reporterFactor_le j

omit [DecidableEq ι] in
theorem heatReporter_apply (x : ℓ²ι) (j : ι) :
    s.heatReporter x j = (((1 + s.lam j)⁻¹ : ℝ) : ℂ) * x j :=
  LpDiagonal.lpDiag_coe _ _ _ _ _ _

/-- **(OG.6)** The reporter is compact. -/
theorem isCompactOperator_heatReporter (hP : s.Proper) : IsCompactOperator s.heatReporter := by
  refine LpDiagonal.isCompactOperator_lpDiag _ _ _ _ ?_
  have h : Tendsto (fun j => (1 + s.lam j)⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 hP)
  have h' := h.norm
  rw [norm_zero] at h'
  refine h'.congr fun j => ?_
  rw [Complex.norm_real]

omit [DecidableEq ι] in
/-- **(OG.6)** The reporter has simple eigenvalues `(1 + λ_j)^{-1}`. -/
theorem reporterEigenvalue_injective (hS : s.Simple) :
    Function.Injective fun j => (1 + s.lam j)⁻¹ := by
  intro i j h
  have h' : 1 + s.lam i = 1 + s.lam j := inv_injective h
  exact hS (by linarith)

theorem inner_single_heatReporter (x : ℓ²ι) (i : ι) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), s.heatReporter x⟫_ℂ =
      (((1 + s.lam i)⁻¹ : ℝ) : ℂ) * ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), x⟫_ℂ := by
  rw [inner_single_one_left, inner_single_one_left, s.heatReporter_apply]

/-- **(OG.17)** An operator commuting with `D` and `P` is scalar. -/
theorem eq_smul_one_of_commute (hS : s.Simple) (hF : s.FullSupport) {T : ℓ²ι →L[ℂ] ℓ²ι}
    (hD : Commute T s.heatReporter) (hP : Commute T s.heatProjection) :
    ∃ c : ℂ, T = c • 1 := by
  set t : ι → ι → ℂ := fun i j => ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), T (lp.single 2 j 1)⟫_ℂ with ht
  have hoff : ∀ i j, i ≠ j → t i j = 0 := by
    intro i j hij
    have h0 : T (s.heatReporter (lp.single 2 j 1)) = s.heatReporter (T (lp.single 2 j 1)) :=
      DFunLike.congr_fun hD.eq _
    have h1 := congrArg (fun y : ℓ²ι => ⟪(lp.single 2 i (1 : ℂ) : ℓ²ι), y⟫_ℂ) h0
    have hDj : s.heatReporter (lp.single 2 j (1 : ℂ)) =
        (((1 + s.lam j)⁻¹ : ℝ) : ℂ) • (lp.single 2 j (1 : ℂ) : ℓ²ι) := by
      refine lp.ext (funext fun k => ?_)
      rw [s.heatReporter_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
      by_cases hk : k = j
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    rw [hDj, map_smul, inner_smul_right, s.inner_single_heatReporter] at h1
    have hne : (((1 + s.lam j)⁻¹ : ℝ) : ℂ) ≠ (((1 + s.lam i)⁻¹ : ℝ) : ℂ) := by
      intro heq
      exact hij (s.reporterEigenvalue_injective hS (by exact_mod_cast heq.symm))
    have h2 : ((((1 + s.lam j)⁻¹ : ℝ) : ℂ) - (((1 + s.lam i)⁻¹ : ℝ) : ℂ)) * t i j = 0 := by
      rw [ht]; linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne)
  have hcol : ∀ j, T (lp.single 2 j (1 : ℂ)) = t j j • (lp.single 2 j (1 : ℂ) : ℓ²ι) := by
    intro j
    refine lp.ext (funext fun i => ?_)
    have hi : (T (lp.single 2 j (1 : ℂ))) i = t i j := (inner_single_one_left _ _).symm
    rw [hi, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [hoff i j hij, Pi.single_eq_of_ne hij]
      simp
  have hTv : ∀ j, T s.v = t j j • s.v := by
    intro j
    have h1 : T (s.heatProjection (lp.single 2 j 1)) = s.heatProjection (T (lp.single 2 j 1)) :=
      DFunLike.congr_fun hP.eq _
    rw [hcol j, map_smul, heatProjection, InnerProductSpace.rankOne_apply, map_smul,
      smul_smul] at h1
    have hvj : ⟪s.v, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ ≠ 0 := by
      rw [inner_single_one_right, map_ne_zero]
      exact hF j
    have := congrArg (fun y : ℓ²ι => (⟪s.v, (lp.single 2 j (1 : ℂ) : ℓ²ι)⟫_ℂ)⁻¹ • y) h1
    simp only [smul_smul, inv_mul_cancel₀ hvj, one_smul] at this
    rw [this]
    congr 1
    field_simp
  have hdiag : ∀ i j, t i i = t j j := by
    intro i j
    have h := (hTv i).symm.trans (hTv j)
    have hi := congrArg (fun y : ℓ²ι => y i) h
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hi
    exact mul_right_cancel₀ (hF i) hi
  by_cases hne : Nonempty ι
  · obtain ⟨j₀⟩ := hne
    refine ⟨t j₀ j₀, ext_of_inner_single fun i j => ?_⟩
    rw [hcol j, inner_smul_right, smul_apply, one_apply_eq_self, inner_smul_right, hdiag j j₀]
  · refine ⟨0, ContinuousLinearMap.ext fun x => ?_⟩
    have hx : x = 0 := lp.ext (funext fun j => absurd ⟨j⟩ hne)
    simp [hx]

/-- **(OG.17)** `{D, P}' = ℂ 1`. -/
theorem commutant_reporter_projection (hS : s.Simple) (hF : s.FullSupport) :
    {T : ℓ²ι →L[ℂ] ℓ²ι | Commute T s.heatReporter ∧ Commute T s.heatProjection} =
      Set.range fun c : ℂ => c • (1 : ℓ²ι →L[ℂ] ℓ²ι) := by
  ext T
  constructor
  · rintro ⟨hD, hP⟩
    obtain ⟨c, rfl⟩ := s.eq_smul_one_of_commute hS hF hD hP
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨(Commute.one_left _).smul_left c, (Commute.one_left _).smul_left c⟩

end HeatSource

end GaloisForLFunctions.HTGeometry
