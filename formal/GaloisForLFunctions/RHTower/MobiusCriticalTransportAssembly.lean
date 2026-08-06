import GaloisForLFunctions.RHTower.MobiusFixedCurrentVonMangoldt
import GaloisForLFunctions.RHTower.InfiniteMobiusCriticalBoundaryLayer
import GaloisForLFunctions.RHTower.GammaDampedScaledSpectralLimit
import GaloisForLFunctions.HTGeometry.SquarefreeClockLaw
import GaloisForLFunctions.HTGeometry.HalfLineScaling
import GaloisForLFunctions.HTGeometry.ExponentialLaplaceValue
import GaloisForLFunctions.HTGeometry.ClockSecondMoment
import GaloisForLFunctions.HTGeometry.PairGiniLaw

/-!
# The critical Euler clock meets its boundary layer

The Laplace transform of the thermally scaled Euler clock is the moving ratio of von Mangoldt
currents, and that ratio is the object whose boundary-layer limit the fixed-current layer computes.
This file records the resulting limit of the clock's Laplace transform, which is one of the two
hypotheses the critical transport statement consumes.
-/

open Filter Topology MeasureTheory ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real von Mangoldt Dirichlet total is the von Mangoldt current. -/
theorem ofReal_tsum_vonMangoldt_eq_current {σ : ℝ} (hσ : 1 < σ) :
    ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
      = RHTower.vonMangoldtCurrent (σ : ℂ) :=
  ofReal_tsum_vonMangoldt_eq hσ

/-- **`(11)`, exact form for the Euler clock.**  At every nonnegative argument the Laplace
transform of the scaled Euler clock is the moving ratio of von Mangoldt currents
`A(σ + uε)/A(σ)`. -/
theorem ofReal_integral_exp_neg_scaledEulerClockLaw_eq {ε u : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) :
    ((∫ y, Real.exp (-(u * y)) ∂(scaledEulerClockLaw (1 + ε)) : ℝ) : ℂ)
      = RHTower.vonMangoldtCurrent (((1 + ε + u * ε : ℝ)) : ℂ)
        / RHTower.vonMangoldtCurrent (((1 + ε : ℝ)) : ℂ) := by
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  have hσ' : (1 : ℝ) < 1 + ε + u * ε := by nlinarith
  have harg : (1 + ε) + u * ((1 + ε) - 1) = 1 + ε + u * ε := by ring
  rw [integral_exp_neg_scaledEulerClockLaw hσ hu, harg, Complex.ofReal_div,
    ofReal_tsum_vonMangoldt_eq_current hσ', ofReal_tsum_vonMangoldt_eq_current hσ]

/-- **`(11)`, exact form for the squarefree clock.**  At every nonnegative argument the Laplace
transform of the scaled squarefree clock is the moving ratio `Z(σ + uε)/Z(σ)` of the squarefree
Dirichlet series `Z(s) = ζ(s)/ζ(2s)`. -/
theorem ofReal_integral_exp_neg_scaledSquarefreeClockLaw_eq {ε u : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) :
    ((∫ y, Real.exp (-(u * y)) ∂(scaledSquarefreeClockLaw (1 + ε)) : ℝ) : ℂ)
      = (riemannZeta (((1 + ε + u * ε : ℝ)) : ℂ)
            / riemannZeta (2 * (((1 + ε + u * ε : ℝ)) : ℂ)))
        / (riemannZeta (((1 + ε : ℝ)) : ℂ) / riemannZeta (2 * (((1 + ε : ℝ)) : ℂ))) := by
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  have hσ' : (1 : ℝ) < 1 + ε + u * ε := by nlinarith
  have harg : (1 + ε) + u * ((1 + ε) - 1) = 1 + ε + u * ε := by ring
  rw [integral_exp_neg_scaledSquarefreeClockLaw hσ hu, harg, Complex.ofReal_div,
    ofReal_dirichletTotal_squarefreeWeight_eq hσ', ofReal_dirichletTotal_squarefreeWeight_eq hσ]

/-- **The Laplace transform of the scaled Euler clock reaches the exponential value.**  Along the
critical scaling the clock's Laplace transform at a natural argument tends to the mean-one
exponential value. -/
theorem tendsto_integral_exp_neg_scaledEulerClockLaw (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ y, Real.exp (-((k : ℝ) * y)) ∂(scaledEulerClockLaw (1 + ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (1 + (k : ℝ)))) := by
  have hcorpus := RHTower.tendsto_eulerClockLaplace (u := (k : ℝ)) (by positivity)
  have hre := (Complex.continuous_re.tendsto _).comp hcorpus
  have hval : ((1 : ℂ) / (1 + ((k : ℝ) : ℂ))).re = 1 / (1 + (k : ℝ)) := by
    have hcast : ((1 : ℂ) / (1 + ((k : ℝ) : ℂ))) = (((1 / (1 + (k : ℝ)) : ℝ)) : ℂ) := by
      push_cast
      ring_nf
    rw [hcast, Complex.ofReal_re]
  rw [hval] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  have hσ' : (1 : ℝ) < 1 + (1 + (k : ℝ)) * ε := by nlinarith
  have hden : ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε)) : ℝ) : ℂ)
      = RHTower.vonMangoldtCurrent (1 + ((1 : ℝ) : ℂ) * (ε : ℂ)) := by
    rw [ofReal_tsum_vonMangoldt_eq_current hσ]
    norm_num
  have hnum : ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + (1 + (k : ℝ)) * ε)) : ℝ) : ℂ)
      = RHTower.vonMangoldtCurrent (1 + ((1 + (k : ℝ) : ℝ) : ℂ) * (ε : ℂ)) := by
    rw [ofReal_tsum_vonMangoldt_eq_current hσ']
    congr 1
    push_cast
    ring_nf
  have hclock : (∫ y, Real.exp (-((k : ℝ) * y)) ∂(scaledEulerClockLaw (1 + ε)))
      = (∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + (1 + (k : ℝ)) * ε)))
        / ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε)) := by
    rw [integral_exp_neg_scaledEulerClockLaw hσ (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    congr 2
    ring_nf
  have hquot : (((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + (1 + (k : ℝ)) * ε)))
      / ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε)) : ℝ) : ℂ)
      = RHTower.vonMangoldtCurrent (1 + ((1 + (k : ℝ) : ℝ) : ℂ) * (ε : ℂ))
        / RHTower.vonMangoldtCurrent (1 + ((1 : ℝ) : ℂ) * (ε : ℂ)) := by
    rw [← hden, ← hnum]
    push_cast
    ring_nf
  rw [hclock]
  simpa using (congrArg Complex.re hquot).symm

/-- The `L`-series of the von Mangoldt weight and the von Mangoldt current have the same
derivative past the abscissa one, since they agree on an open half plane. -/
theorem deriv_lseries_vonMangoldt_eq {σ : ℝ} (hσ : 1 < σ) :
    deriv (LSeries fun n => (vonMangoldt n : ℂ)) (σ : ℂ)
      = deriv RHTower.vonMangoldtCurrent (σ : ℂ) := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (σ : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hσ
  filter_upwards [hopen.mem_nhds hmem] with s hs
  exact LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- **`(13)`, exact form.**  The mean of the scaled Euler clock is the escape parameter times the
normalized logarithmic derivative of the von Mangoldt current. -/
theorem ofReal_integral_id_scaledEulerClockLaw_eq {ε : ℝ} (hε : 0 < ε) :
    ((∫ y, y ∂(scaledEulerClockLaw (1 + ε)) : ℝ) : ℂ)
      = -(ε : ℂ) * deriv RHTower.vonMangoldtCurrent (1 + (ε : ℂ))
        / RHTower.vonMangoldtCurrent (1 + (ε : ℂ)) := by
  have hεpos : (0 : ℝ) < ε := hε
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  have hmean : (∫ y, y ∂(scaledEulerClockLaw (1 + ε)))
      = ε * ((∑' n : ℕ, (Real.log n * vonMangoldt n) * (n : ℝ) ^ (-(1 + ε)))
        / ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε))) := by
    rw [integral_id_scaledEulerClockLaw hσ]
    congr 1
    ring
  have hcast : ((ε * ((∑' n : ℕ, (Real.log n * vonMangoldt n) * (n : ℝ) ^ (-(1 + ε)))
      / ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε))) : ℝ) : ℂ)
      = -(ε : ℂ) * deriv RHTower.vonMangoldtCurrent (1 + (ε : ℂ))
        / RHTower.vonMangoldtCurrent (1 + (ε : ℂ)) := by
    have hnum : ((∑' n : ℕ, (Real.log n * vonMangoldt n) * (n : ℝ) ^ (-(1 + ε)) : ℝ) : ℂ)
        = -deriv RHTower.vonMangoldtCurrent (1 + (ε : ℂ)) := by
      rw [ofReal_tsum_vonMangoldt_logMul_eq hσ, deriv_lseries_vonMangoldt_eq hσ]
      congr 2
      push_cast
      ring_nf
    have hden : ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε)) : ℝ) : ℂ)
        = RHTower.vonMangoldtCurrent (1 + (ε : ℂ)) := by
      rw [ofReal_tsum_vonMangoldt_eq_current hσ]
      congr 1
      push_cast
      ring_nf
    rw [Complex.ofReal_mul, Complex.ofReal_div, hnum, hden]
    ring_nf
  rw [hmean]
  exact hcast

/-- **The mean of the scaled Euler clock reaches one.**  Along the critical scaling the clock's
first moment tends to the mean-one exponential value. -/
theorem tendsto_integral_id_scaledEulerClockLaw :
    Tendsto (fun ε : ℝ => ∫ y, y ∂(scaledEulerClockLaw (1 + ε))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcorpus := RHTower.tendsto_eulerClockFirstMoment
  have hre := (Complex.continuous_re.tendsto _).comp hcorpus
  have hval : ((1 : ℂ)).re = (1 : ℝ) := Complex.one_re
  rw [hval] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  simpa using (congrArg Complex.re (ofReal_integral_id_scaledEulerClockLaw_eq hεpos)).symm

/-- The squarefree Dirichlet total of the transport layer is the squarefree Möbius total of the
boundary-layer layer. -/
theorem dirichletTotal_squarefreeWeight_eq_total (σ : ℝ) :
    dirichletTotal squarefreeWeight σ = RHTower.squarefreeMobiusTotal σ := by
  rw [dirichletTotal, RHTower.squarefreeMobiusTotal]
  refine tsum_congr fun n => ?_
  rw [squarefreeWeight_eq_indicator, RHTower.squarefreeMobiusMass]
  by_cases h : Squarefree n
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]

theorem tendsto_one_add_nhdsGT :
    Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hlim : Tendsto (fun ε : ℝ => 1 + ε) (𝓝 (0 : ℝ)) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa using hlim.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa using hε

/-- **The Laplace transform of the scaled squarefree clock reaches the exponential value.** -/
theorem tendsto_integral_exp_neg_scaledSquarefreeClockLaw (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ y, Real.exp (-((k : ℝ) * y)) ∂(scaledSquarefreeClockLaw (1 + ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (1 + (k : ℝ)))) := by
  have hcorpus := (RHTower.tendsto_squarefreeMobiusBoundaryLayerLaplace
    (u := (k : ℝ)) (by positivity)).comp tendsto_one_add_nhdsGT
  have hre := (Complex.continuous_re.tendsto _).comp hcorpus
  have hval : ((((1 + (k : ℝ) : ℝ)) : ℂ))⁻¹.re = 1 / (1 + (k : ℝ)) := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [hval] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  have hclock : (∫ y, Real.exp (-((k : ℝ) * y)) ∂(scaledSquarefreeClockLaw (1 + ε)))
      = RHTower.squarefreeMobiusTotal (RHTower.mobiusCriticalBoundaryParameter (1 + ε) (k : ℝ))
        / RHTower.squarefreeMobiusTotal (1 + ε) := by
    rw [integral_exp_neg_scaledSquarefreeClockLaw hσ (by positivity : (0 : ℝ) ≤ (k : ℝ)),
      dirichletTotal_squarefreeWeight_eq_total, dirichletTotal_squarefreeWeight_eq_total]
    congr 2
  rw [hclock]
  simp [Function.comp_def, RHTower.squarefreeMobiusBoundaryLayerLaplace]

/-- The transport layer's squarefree mean is the boundary layer's first logarithmic moment. -/
theorem squarefree_logMean_eq_logMoment (σ : ℝ) :
    (∑' n : ℕ, (Real.log n * squarefreeWeight n) * (n : ℝ) ^ (-σ))
        / dirichletTotal squarefreeWeight σ
      = RHTower.squarefreeMobiusLogMoment 1 σ := by
  rw [RHTower.squarefreeMobiusLogMoment, dirichletTotal_squarefreeWeight_eq_total,
    ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [RHTower.squarefreeMobiusProbability, RHTower.squarefreeMobiusMass,
    squarefreeWeight_eq_indicator]
  by_cases h : Squarefree n
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    simp

/-- **The logarithmically weighted squarefree sum is minus the derivative of its `L`-series.** -/
theorem ofReal_tsum_squarefreeWeight_logMul_eq {σ : ℝ} (hσ : 1 < σ) :
    ((∑' n : ℕ, (Real.log n * squarefreeWeight n) * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
      = -deriv (LSeries fun n => (squarefreeWeight n : ℂ)) (σ : ℂ) := by
  rw [LSeries_deriv (abscissa_squarefreeWeight_lt hσ), neg_neg,
    ofReal_tsum_eq_lseries (f := fun n => Real.log n * squarefreeWeight n) (by simp)]
  refine congrArg (fun g => LSeries g (σ : ℂ)) ?_
  funext n
  have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp only [LSeries.logMul, hlogn]
  push_cast
  ring

/-- **`(13)`, exact form for the squarefree clock.**  Its mean is the escape parameter times the
normalized logarithmic derivative of the squarefree Dirichlet series `Z(s) = ζ(s)/ζ(2s)`. -/
theorem ofReal_integral_id_scaledSquarefreeClockLaw_eq {ε : ℝ} (hε : 0 < ε) :
    ((∫ y, y ∂(scaledSquarefreeClockLaw (1 + ε)) : ℝ) : ℂ)
      = -(ε : ℂ) * deriv (LSeries fun n => (squarefreeWeight n : ℂ)) (((1 + ε : ℝ) : ℂ))
        / (riemannZeta ((1 + ε : ℝ) : ℂ) / riemannZeta (2 * ((1 + ε : ℝ) : ℂ))) := by
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  rw [integral_id_scaledSquarefreeClockLaw hσ, Complex.ofReal_mul, Complex.ofReal_div,
    ofReal_tsum_squarefreeWeight_logMul_eq hσ, ofReal_dirichletTotal_squarefreeWeight_eq hσ,
    show (((1 + ε - 1 : ℝ)) : ℂ) = (ε : ℂ) by push_cast; ring]
  ring

/-- **The mean of the scaled squarefree clock reaches one.** -/
theorem tendsto_integral_id_scaledSquarefreeClockLaw :
    Tendsto (fun ε : ℝ => ∫ y, y ∂(scaledSquarefreeClockLaw (1 + ε))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine RHTower.tendsto_mul_squarefreeMobiusLogMoment.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  rw [integral_id_scaledSquarefreeClockLaw hσ, squarefree_logMean_eq_logMoment]
  congr 1
  ring

/-- The escape parameter of the thermal scaling, kept inside the strict Euler half-plane at every
index so that the clock laws are probability laws throughout. -/
def escape (ε : ℝ) : ℝ := if 0 < ε then 1 + ε else 2

theorem one_lt_escape (ε : ℝ) : 1 < escape ε := by
  unfold escape
  split <;> linarith

theorem escape_eq_of_pos {ε : ℝ} (hε : 0 < ε) : escape ε = 1 + ε := if_pos hε

/-- **The critical two-clock transport statement for the arithmetic clocks.**  The monotone
coupling of the thermally scaled squarefree clock with the thermally scaled Euler clock carries
vanishing transport cost at criticality.  Both clocks are the Dirichlet clocks of the fixed-current
layer, and both hypotheses the transport layer needs — the boundary-layer Laplace limits and the
first-moment limits — are the four limits established above. -/
theorem tendsto_integral_monotoneCoupling_criticalClocks :
    Tendsto (fun ε : ℝ => ∫ z, |z.1 - z.2|
        ∂(monotoneCoupling (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI hprobS : ∀ ε : ℝ, IsProbabilityMeasure (scaledSquarefreeClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledSquarefreeClockLaw (one_lt_escape ε)
  haveI hprobE : ∀ ε : ℝ, IsProbabilityMeasure (scaledEulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledEulerClockLaw (one_lt_escape ε)
  refine Filter.Tendsto.congr' ?_
    (tendsto_integral_monotoneCoupling_pair_of_tendsto_laplace_value
      (fun ε : ℝ => scaledSquarefreeClockLaw (escape ε))
      (fun ε : ℝ => scaledEulerClockLaw (escape ε))
      (fun ε => scaledSquarefreeClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => scaledEulerClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => integrable_id_scaledSquarefreeClockLaw (one_lt_escape ε))
      (fun ε => integrable_id_scaledEulerClockLaw (one_lt_escape ε))
      ?_ ?_ ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledSquarefreeClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledEulerClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_id_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_id_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]

/-! ### The second-order critical transport statement -/

/-- The `L`-series of the von Mangoldt weight and the von Mangoldt current have the same derivative
at every point of the open half plane past abscissa one. -/
theorem deriv_lseries_vonMangoldt_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries fun n => (vonMangoldt n : ℂ)) s = deriv RHTower.vonMangoldtCurrent s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : s ∈ {z : ℂ | 1 < z.re} := hs
  filter_upwards [hopen.mem_nhds hmem] with z hz
  exact LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz

/-- Their second derivatives agree as well, since their first derivatives agree on the whole open
half plane. -/
theorem deriv2_lseries_vonMangoldt_eq {σ : ℝ} (hσ : 1 < σ) :
    deriv (deriv (LSeries fun n => (vonMangoldt n : ℂ))) (σ : ℂ)
      = deriv (deriv RHTower.vonMangoldtCurrent) (σ : ℂ) := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (σ : ℂ) ∈ {z : ℂ | 1 < z.re} := by simpa using hσ
  filter_upwards [hopen.mem_nhds hmem] with z hz
  exact deriv_lseries_vonMangoldt_eq_of_one_lt_re hz

/-- **`(15a)`, exact form.**  The second moment of the scaled Euler clock is the squared escape
parameter times the normalized second derivative of the von Mangoldt current. -/
theorem ofReal_integral_sq_scaledEulerClockLaw_eq {ε : ℝ} (hε : 0 < ε) :
    ((∫ y, y ^ 2 ∂(scaledEulerClockLaw (1 + ε)) : ℝ) : ℂ)
      = (ε : ℂ) ^ 2 * deriv (deriv RHTower.vonMangoldtCurrent) (1 + (ε : ℂ))
        / RHTower.vonMangoldtCurrent (1 + (ε : ℂ)) := by
  have hεpos : (0 : ℝ) < ε := hε
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  have hmom : (∫ y, y ^ 2 ∂(scaledEulerClockLaw (1 + ε)))
      = ε ^ 2 * ((∑' n : ℕ, (Real.log n ^ 2 * vonMangoldt n) * (n : ℝ) ^ (-(1 + ε)))
        / ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε))) := by
    rw [integral_sq_scaledEulerClockLaw hσ]
    congr 1
    ring
  have hcast : ((ε ^ 2 * ((∑' n : ℕ, (Real.log n ^ 2 * vonMangoldt n) * (n : ℝ) ^ (-(1 + ε)))
      / ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε))) : ℝ) : ℂ)
      = (ε : ℂ) ^ 2 * deriv (deriv RHTower.vonMangoldtCurrent) (1 + (ε : ℂ))
        / RHTower.vonMangoldtCurrent (1 + (ε : ℂ)) := by
    have hnum : ((∑' n : ℕ, (Real.log n ^ 2 * vonMangoldt n) * (n : ℝ) ^ (-(1 + ε)) : ℝ) : ℂ)
        = deriv (deriv RHTower.vonMangoldtCurrent) (1 + (ε : ℂ)) := by
      rw [ofReal_tsum_vonMangoldt_logSq_eq hσ, deriv2_lseries_vonMangoldt_eq hσ]
      congr 2
      push_cast
      ring_nf
    have hden : ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + ε)) : ℝ) : ℂ)
        = RHTower.vonMangoldtCurrent (1 + (ε : ℂ)) := by
      rw [ofReal_tsum_vonMangoldt_eq_current hσ]
      congr 1
      push_cast
      ring_nf
    rw [Complex.ofReal_mul, Complex.ofReal_div, hnum, hden, Complex.ofReal_pow]
    ring_nf
  rw [hmom]
  exact hcast

/-- **The second moment of the scaled Euler clock reaches two.**  Along the critical scaling the
clock's second moment tends to the second moment of the mean-one exponential law. -/
theorem tendsto_integral_sq_scaledEulerClockLaw :
    Tendsto (fun ε : ℝ => ∫ y, y ^ 2 ∂(scaledEulerClockLaw (1 + ε))) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have hcorpus := RHTower.tendsto_eulerClockSecondMoment
  have hre := (Complex.continuous_re.tendsto _).comp hcorpus
  have hval : ((2 : ℂ)).re = (2 : ℝ) := by norm_num
  rw [hval] at hre
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  simpa [← Complex.ofReal_pow] using
    (congrArg Complex.re (ofReal_integral_sq_scaledEulerClockLaw_eq hεpos)).symm

/-- The transport layer's squarefree second moment is the boundary layer's second logarithmic
moment. -/
theorem squarefree_logSqMean_eq_logMoment (σ : ℝ) :
    (∑' n : ℕ, (Real.log n ^ 2 * squarefreeWeight n) * (n : ℝ) ^ (-σ))
        / dirichletTotal squarefreeWeight σ
      = RHTower.squarefreeMobiusLogMoment 2 σ := by
  rw [RHTower.squarefreeMobiusLogMoment, dirichletTotal_squarefreeWeight_eq_total,
    ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [RHTower.squarefreeMobiusProbability, RHTower.squarefreeMobiusMass,
    squarefreeWeight_eq_indicator]
  by_cases h : Squarefree n
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    simp

/-- **The second moment of the scaled squarefree clock reaches two.** -/
theorem tendsto_integral_sq_scaledSquarefreeClockLaw :
    Tendsto (fun ε : ℝ => ∫ y, y ^ 2 ∂(scaledSquarefreeClockLaw (1 + ε))) (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  refine (RHTower.tendsto_squarefreeMobiusLogMoment_two_critical.comp
    tendsto_one_add_nhdsGT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  rw [integral_sq_scaledSquarefreeClockLaw hσ, squarefree_logSqMean_eq_logMoment]
  simp

/-- **The second-order critical two-clock transport statement.**  The monotone coupling of the
thermally scaled squarefree clock with the thermally scaled Euler clock carries vanishing quadratic
transport cost at criticality, so the two critical clocks agree in the joint `L²` space and both
converge to the mean-one exponential law in `W₂`. -/
theorem tendsto_integral_monotoneCoupling_sq_criticalClocks :
    Tendsto (fun ε : ℝ => ∫ z, |z.1 - z.2| ^ 2
        ∂(monotoneCoupling (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI hprobS : ∀ ε : ℝ, IsProbabilityMeasure (scaledSquarefreeClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledSquarefreeClockLaw (one_lt_escape ε)
  haveI hprobE : ∀ ε : ℝ, IsProbabilityMeasure (scaledEulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledEulerClockLaw (one_lt_escape ε)
  refine Filter.Tendsto.congr' ?_
    (tendsto_integral_monotoneCoupling_pair_sq_of_tendsto_laplace_value
      (fun ε : ℝ => scaledSquarefreeClockLaw (escape ε))
      (fun ε : ℝ => scaledEulerClockLaw (escape ε))
      (fun ε => scaledSquarefreeClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => scaledEulerClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => integrable_sq_scaledSquarefreeClockLaw (one_lt_escape ε))
      (fun ε => integrable_sq_scaledEulerClockLaw (one_lt_escape ε))
      ?_ ?_ ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledSquarefreeClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledEulerClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_sq_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_sq_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]

/-- **The centered second-order two-clock statement.**  The centered thermal scores of the two
critical clocks are coupled in `L²`: the monotone coupling makes their centered variables agree in
the joint `L²` space at criticality. -/
theorem tendsto_integral_monotoneCoupling_centered_sq_criticalClocks :
    Tendsto (fun ε : ℝ => ∫ z, |(z.1 - ∫ x, x ∂(scaledSquarefreeClockLaw (1 + ε)))
        - (z.2 - ∫ x, x ∂(scaledEulerClockLaw (1 + ε)))| ^ 2
        ∂(monotoneCoupling (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI hprobS : ∀ ε : ℝ, IsProbabilityMeasure (scaledSquarefreeClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledSquarefreeClockLaw (one_lt_escape ε)
  haveI hprobE : ∀ ε : ℝ, IsProbabilityMeasure (scaledEulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledEulerClockLaw (one_lt_escape ε)
  have hcost : Tendsto (fun ε : ℝ => ∫ z, |z.1 - z.2| ^ 2
      ∂(monotoneCoupling (scaledSquarefreeClockLaw (escape ε)) (scaledEulerClockLaw (escape ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_integral_monotoneCoupling_sq_criticalClocks.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  have hmeanS : Tendsto (fun ε : ℝ => ∫ x, x ∂(scaledSquarefreeClockLaw (escape ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine tendsto_integral_id_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  have hmeanE : Tendsto (fun ε : ℝ => ∫ x, x ∂(scaledEulerClockLaw (escape ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine tendsto_integral_id_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  have hmean : Tendsto (fun ε : ℝ => |(∫ x, x ∂(scaledSquarefreeClockLaw (escape ε)))
      - ∫ x, x ∂(scaledEulerClockLaw (escape ε))|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hmeanS.sub hmeanE).abs
  refine Filter.Tendsto.congr' ?_
    (tendsto_integral_monotoneCoupling_centered_sq _ _
      (fun ε => integrable_sq_scaledSquarefreeClockLaw (one_lt_escape ε))
      (fun ε => integrable_sq_scaledEulerClockLaw (one_lt_escape ε)) hcost hmean)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [escape_eq_of_pos hε]

/-! ### The transport distance to the exponential law -/

/-- **The squarefree clock converges to the mean-one exponential law in the half-line transport
distance.** -/
theorem tendsto_halfLineW1_scaledSquarefreeClockLaw :
    Tendsto (fun ε : ℝ => halfLineW1 (scaledSquarefreeClockLaw (1 + ε)) (ProbabilityTheory.expMeasure 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (scaledSquarefreeClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledSquarefreeClockLaw (one_lt_escape ε)
  refine Filter.Tendsto.congr' ?_
    (tendsto_halfLineW1_expMeasure_one_of_tendsto_laplace_value
      (fun ε : ℝ => scaledSquarefreeClockLaw (escape ε))
      (fun ε => scaledSquarefreeClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => integrable_id_scaledSquarefreeClockLaw (one_lt_escape ε)) ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledSquarefreeClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_id_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]

/-- **The Euler clock converges to the mean-one exponential law in the half-line transport
distance.** -/
theorem tendsto_halfLineW1_scaledEulerClockLaw :
    Tendsto (fun ε : ℝ => halfLineW1 (scaledEulerClockLaw (1 + ε)) (ProbabilityTheory.expMeasure 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (scaledEulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledEulerClockLaw (one_lt_escape ε)
  refine Filter.Tendsto.congr' ?_
    (tendsto_halfLineW1_expMeasure_one_of_tendsto_laplace_value
      (fun ε : ℝ => scaledEulerClockLaw (escape ε))
      (fun ε => scaledEulerClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => integrable_id_scaledEulerClockLaw (one_lt_escape ε)) ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledEulerClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_id_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]

/-! ### The four-unit incidence energy of the two clocks -/

/-- **The mean pairwise distance of two independent critical Euler clocks tends to one.**  This is
the four-unit law for the von Mangoldt current: the mean distance between two independent copies of
the thermally scaled clock reaches the mean pairwise distance of two independent mean-one
exponential variables. -/
theorem tendsto_integral_abs_sub_prod_scaledEulerClockLaw :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ, |w.1 - w.2|
        ∂((scaledEulerClockLaw (1 + ε)).prod (scaledEulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (scaledEulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledEulerClockLaw (one_lt_escape ε)
  have hmean : Tendsto (fun ε : ℝ => ∫ x, x ∂(scaledEulerClockLaw (escape ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine tendsto_integral_id_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  have hW1 : Tendsto (fun ε : ℝ => halfLineW1 (scaledEulerClockLaw (escape ε))
      (ProbabilityTheory.expMeasure 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_halfLineW1_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  refine Filter.Tendsto.congr' ?_
    (tendsto_integral_abs_sub_prod (fun ε : ℝ => scaledEulerClockLaw (escape ε))
      (fun ε => integrable_id_scaledEulerClockLaw (one_lt_escape ε))
      (fun ε => scaledEulerClockLaw_Iio_zero (one_lt_escape ε)) hmean hW1)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [escape_eq_of_pos hε]

/-- **The four-unit incidence energy of the von Mangoldt current tends to four.** -/
theorem tendsto_fourUnitEnergy_scaledEulerClockLaw :
    Tendsto (fun ε : ℝ => 4 * ∫ w : ℝ × ℝ, |w.1 - w.2|
        ∂((scaledEulerClockLaw (1 + ε)).prod (scaledEulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  simpa using tendsto_integral_abs_sub_prod_scaledEulerClockLaw.const_mul 4

/-- **The mean pairwise distance of two independent critical squarefree clocks tends to one.** -/
theorem tendsto_integral_abs_sub_prod_scaledSquarefreeClockLaw :
    Tendsto (fun ε : ℝ => ∫ w : ℝ × ℝ, |w.1 - w.2|
        ∂((scaledSquarefreeClockLaw (1 + ε)).prod (scaledSquarefreeClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (scaledSquarefreeClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledSquarefreeClockLaw (one_lt_escape ε)
  have hmean : Tendsto (fun ε : ℝ => ∫ x, x ∂(scaledSquarefreeClockLaw (escape ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine tendsto_integral_id_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  have hW1 : Tendsto (fun ε : ℝ => halfLineW1 (scaledSquarefreeClockLaw (escape ε))
      (ProbabilityTheory.expMeasure 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_halfLineW1_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  refine Filter.Tendsto.congr' ?_
    (tendsto_integral_abs_sub_prod (fun ε : ℝ => scaledSquarefreeClockLaw (escape ε))
      (fun ε => integrable_id_scaledSquarefreeClockLaw (one_lt_escape ε))
      (fun ε => scaledSquarefreeClockLaw_Iio_zero (one_lt_escape ε)) hmean hW1)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [escape_eq_of_pos hε]

/-- **The four-unit incidence energy of the squarefree clock tends to four.** -/
theorem tendsto_fourUnitEnergy_scaledSquarefreeClockLaw :
    Tendsto (fun ε : ℝ => 4 * ∫ w : ℝ × ℝ, |w.1 - w.2|
        ∂((scaledSquarefreeClockLaw (1 + ε)).prod (scaledSquarefreeClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  simpa using tendsto_integral_abs_sub_prod_scaledSquarefreeClockLaw.const_mul 4

/-! ### The fixed current as a clock Laplace transform -/

/-- **`(4)`, second equality.**  The shifted von Mangoldt current is the current at the base point
times the Laplace transform of the thermally scaled Euler clock: the fixed current is the clock's
moment generating function. -/
theorem vonMangoldtCurrent_shift_eq_mul_clockLaplace {σ : ℝ} (hσ : 1 < σ) {u : ℝ} (hu : 0 ≤ u) :
    RHTower.vonMangoldtCurrent ((σ + u * (σ - 1) : ℝ) : ℂ)
      = RHTower.vonMangoldtCurrent (σ : ℂ)
        * (((∫ y, Real.exp (-(u * y)) ∂(scaledEulerClockLaw σ)) : ℝ) : ℂ) := by
  have hσ' : (1 : ℝ) < σ + u * (σ - 1) := by nlinarith
  have hpos : (0 : ℝ) < ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-σ) := tsum_vonMangoldt_rpow_pos hσ
  have hden := ofReal_tsum_vonMangoldt_eq_current hσ
  have hnum := ofReal_tsum_vonMangoldt_eq_current hσ'
  have hne : RHTower.vonMangoldtCurrent (σ : ℂ) ≠ 0 := by
    rw [← hden]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  rw [integral_exp_neg_scaledEulerClockLaw hσ hu, Complex.ofReal_div, hnum, hden]
  field_simp

/-! ### The normalized Suzuki normal derivative -/

/-- **`(9)`, exact form.**  Half the thermal parameter times the normal derivative of the packet
Dirichlet series is the thermally scaled fixed current. -/
theorem half_mul_deriv_suzukiPacketDirichlet_eq {ε : ℝ} (hε : 0 < ε) :
    ((ε : ℂ) / 2) * deriv (fun a : ℝ => RHTower.suzukiPacketDirichlet a ((1 + ε : ℝ) : ℂ)) 0
      = (ε : ℂ) * RHTower.vonMangoldtCurrent ((1 + ε : ℝ) : ℂ) := by
  have hre : (1 : ℝ) < (((1 + ε : ℝ) : ℂ)).re := by
    simpa using hε
  have hderiv := RHTower.hasDerivAt_suzukiPacketDirichlet hre
  rw [hderiv.deriv]
  ring

/-- **`(9)`.**  The normalized normal derivative of the packet connection reaches one along the
critical scaling. -/
theorem tendsto_half_mul_deriv_suzukiPacketDirichlet :
    Tendsto (fun ε : ℝ =>
        ((ε : ℂ) / 2) * deriv (fun a : ℝ => RHTower.suzukiPacketDirichlet a ((1 + ε : ℝ) : ℂ)) 0)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcorpus := RHTower.tendsto_mul_vonMangoldtCurrent_scaled (c := 1) one_pos
  refine hcorpus.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  rw [half_mul_deriv_suzukiPacketDirichlet_eq hεpos]
  push_cast
  ring_nf

/-! ### `W₂` convergence of each clock to the exponential law -/

/-- **The squarefree clock converges to the mean-one exponential law in the quadratic transport
cost.**  This is the `W₂` half of `(15a)` for the ground clock. -/
theorem tendsto_integral_monotoneCoupling_sq_expMeasure_one_scaledSquarefreeClockLaw :
    Tendsto (fun ε : ℝ => ∫ z, |z.1 - z.2| ^ 2
        ∂(monotoneCoupling (scaledSquarefreeClockLaw (1 + ε))
          (ProbabilityTheory.expMeasure 1))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (scaledSquarefreeClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledSquarefreeClockLaw (one_lt_escape ε)
  refine Filter.Tendsto.congr' ?_
    (tendsto_integral_monotoneCoupling_sq_of_tendsto_laplace_value
      (fun ε : ℝ => scaledSquarefreeClockLaw (escape ε))
      (fun ε => scaledSquarefreeClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => integrable_sq_scaledSquarefreeClockLaw (one_lt_escape ε)) ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledSquarefreeClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_sq_scaledSquarefreeClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]

/-- **The Euler clock converges to the mean-one exponential law in the quadratic transport
cost.**  This is the `W₂` half of `(15a)` for the prime current. -/
theorem tendsto_integral_monotoneCoupling_sq_expMeasure_one_scaledEulerClockLaw :
    Tendsto (fun ε : ℝ => ∫ z, |z.1 - z.2| ^ 2
        ∂(monotoneCoupling (scaledEulerClockLaw (1 + ε))
          (ProbabilityTheory.expMeasure 1))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI hprob : ∀ ε : ℝ, IsProbabilityMeasure (scaledEulerClockLaw (escape ε)) :=
    fun ε => isProbabilityMeasure_scaledEulerClockLaw (one_lt_escape ε)
  refine Filter.Tendsto.congr' ?_
    (tendsto_integral_monotoneCoupling_sq_of_tendsto_laplace_value
      (fun ε : ℝ => scaledEulerClockLaw (escape ε))
      (fun ε => scaledEulerClockLaw_Iio_zero (one_lt_escape ε))
      (fun ε => integrable_sq_scaledEulerClockLaw (one_lt_escape ε)) ?_ ?_)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · intro k
    refine (tendsto_integral_exp_neg_scaledEulerClockLaw k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]
  · refine tendsto_integral_sq_scaledEulerClockLaw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [escape_eq_of_pos hε]

/-- **`(14)`, third line: the mutual half-line transport distance of the two clocks vanishes.**  It
is bounded by the two distances to the exponential law, both of which vanish. -/
theorem tendsto_halfLineW1_criticalClocks :
    Tendsto (fun ε : ℝ =>
        halfLineW1 (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos
  have hsum : Tendsto (fun ε : ℝ =>
      halfLineW1 (scaledSquarefreeClockLaw (1 + ε)) (ProbabilityTheory.expMeasure 1)
        + halfLineW1 (scaledEulerClockLaw (1 + ε)) (ProbabilityTheory.expMeasure 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_halfLineW1_scaledSquarefreeClockLaw.add
      tendsto_halfLineW1_scaledEulerClockLaw
  refine squeeze_zero' (Filter.Eventually.of_forall fun ε => halfLineW1_nonneg _ _) ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  have hσ : (1 : ℝ) < 1 + ε := by linarith
  haveI := isProbabilityMeasure_scaledSquarefreeClockLaw hσ
  haveI := isProbabilityMeasure_scaledEulerClockLaw hσ
  have hP : IntegrableOn (survival (scaledSquarefreeClockLaw (1 + ε))) (Set.Ioi (0 : ℝ)) :=
    integrableOn_survival (integrable_id_scaledSquarefreeClockLaw hσ)
      (ae_nonneg_of_Iio_zero (scaledSquarefreeClockLaw_Iio_zero hσ))
  have hE : IntegrableOn (survival (scaledEulerClockLaw (1 + ε))) (Set.Ioi (0 : ℝ)) :=
    integrableOn_survival (integrable_id_scaledEulerClockLaw hσ)
      (ae_nonneg_of_Iio_zero (scaledEulerClockLaw_Iio_zero hσ))
  have hexp : IntegrableOn (survival (ProbabilityTheory.expMeasure 1)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_survival integrable_id_expMeasure_one expMeasure_one_nonneg_ae
  have htri := halfLineW1_triangle (μ := scaledSquarefreeClockLaw (1 + ε))
    (ν := ProbabilityTheory.expMeasure 1) (ρ := scaledEulerClockLaw (1 + ε)) hP hexp hE
  rw [halfLineW1_symm (ProbabilityTheory.expMeasure 1)] at htri
  exact htri

/-! ### The diagonal shortcut diverges -/

/-- Doubling maps the right-hand punctured neighbourhood of the origin to itself. -/
theorem tendsto_two_mul_nhdsGT : Tendsto (fun a : ℝ => 2 * a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hlim : Tendsto (fun a : ℝ => 2 * a) (𝓝 (0 : ℝ)) (𝓝 (2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    simpa using hlim.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have hapos : (0 : ℝ) < a := ha
    simpa using by linarith

/-- **The diagonal shortcut diverges.**  Between `(8)` and `(9)` the card records that the naive
normalized difference on the old diagonal has no limit: its numerator tends to two while its
denominator vanishes, so the quotient leaves every bounded set. -/
theorem tendsto_norm_diagonalShortcutQuotient_atTop :
    Tendsto (fun a : ℝ =>
        ‖(RHTower.suzukiPacketDirichlet a (1 + 2 * (a : ℂ)) - 1) / (2 * (a : ℂ))‖)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hnum : Tendsto (fun a : ℝ => ‖RHTower.suzukiPacketDirichlet a (1 + 2 * (a : ℂ)) - 1‖)
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    have h := (RHTower.tendsto_suzukiPacketDirichlet_diagonal.sub_const (1 : ℂ)).norm
    have hval : ‖(3 : ℂ) - 1‖ = (2 : ℝ) := by norm_num
    rwa [hval] at h
  have hden : Tendsto (fun a : ℝ => ‖(2 : ℂ) * (a : ℂ)‖⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
    have hbase : Tendsto (fun a : ℝ => (2 * a)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp tendsto_two_mul_nhdsGT
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hapos : (0 : ℝ) < a := ha
    have hnorm : ‖(2 : ℂ) * (a : ℂ)‖ = 2 * a := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hapos]
    rw [hnorm]
  have hprod := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 2) hnum hden
  refine hprod.congr fun a => ?_
  rw [norm_div, div_eq_mul_inv]

/-- **The orientation no-go in one statement.**  At every finite scale the two critical clocks are
distinct laws, yet their transport distance vanishes at criticality: the critical metric class
contains more than one realization, and the fixed current is what selects inside it. -/
theorem criticalClocks_distinct_but_asymptotically_indistinguishable :
    (∀ ε : ℝ, 0 < ε →
        scaledSquarefreeClockLaw (1 + ε) ≠ scaledEulerClockLaw (1 + ε)) ∧
      Tendsto (fun ε : ℝ =>
          halfLineW1 (scaledSquarefreeClockLaw (1 + ε)) (scaledEulerClockLaw (1 + ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ⟨fun ε hε => scaledSquarefreeClockLaw_ne_scaledEulerClockLaw (by linarith),
    tendsto_halfLineW1_criticalClocks⟩

/-! ### `(16)` and `(17)` in the card's own variables -/

/-- **`(16)` for the prime current, unscaled.**  The card writes the four-unit input as
`ε E|H_E - H_E'|`; that is the mean pairwise distance of the unscaled Euler clock multiplied by the
escape parameter. -/
theorem tendsto_mul_integral_abs_sub_prod_eulerClockLaw :
    Tendsto (fun ε : ℝ => ε * ∫ w : ℝ × ℝ, |w.1 - w.2|
        ∂((eulerClockLaw (1 + ε)).prod (eulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine tendsto_integral_abs_sub_prod_scaledEulerClockLaw.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  haveI := isProbabilityMeasure_eulerClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  rw [scaledEulerClockLaw, show (1 : ℝ) + ε - 1 = ε by ring,
    integral_abs_sub_prod_scaleLaw hεpos]

/-- **`(17)` in the card's own variables.**  The four-unit incidence energy of the von Mangoldt
current is `4 ε E|H_E - H_E'|`, and it reaches four. -/
theorem tendsto_fourUnitEnergy_eulerClockLaw :
    Tendsto (fun ε : ℝ => 4 * (ε * ∫ w : ℝ × ℝ, |w.1 - w.2|
        ∂((eulerClockLaw (1 + ε)).prod (eulerClockLaw (1 + ε)))))
      (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  simpa using tendsto_mul_integral_abs_sub_prod_eulerClockLaw.const_mul 4

/-- **`(16)` for the ground clock, unscaled.** -/
theorem tendsto_mul_integral_abs_sub_prod_squarefreeClockLaw :
    Tendsto (fun ε : ℝ => ε * ∫ w : ℝ × ℝ, |w.1 - w.2|
        ∂((squarefreeClockLaw (1 + ε)).prod (squarefreeClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine tendsto_integral_abs_sub_prod_scaledSquarefreeClockLaw.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  haveI := isProbabilityMeasure_squarefreeClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  rw [scaledSquarefreeClockLaw, show (1 : ℝ) + ε - 1 = ε by ring,
    integral_abs_sub_prod_scaleLaw hεpos]

/-! ### `(15)` and `(15b)` in the card's own variables -/

/-- **`(15)` as the card writes it.**  With the escape parameter explicit and the clocks unscaled,
the monotone coupling of the two critical clocks has vanishing transport cost. -/
theorem tendsto_mul_integral_monotoneCoupling_criticalClocks :
    Tendsto (fun ε : ℝ => ε * ∫ z, |z.1 - z.2|
        ∂(monotoneCoupling (squarefreeClockLaw (1 + ε)) (eulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_integral_monotoneCoupling_criticalClocks.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  haveI := isProbabilityMeasure_squarefreeClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  haveI := isProbabilityMeasure_eulerClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  rw [scaledSquarefreeClockLaw, scaledEulerClockLaw, show (1 : ℝ) + ε - 1 = ε by ring,
    integral_monotoneCoupling_abs_sub_scaleLaw hεpos]

/-- **`(15b)` as the card writes it.**  The second-order cost carries the square of the escape
parameter. -/
theorem tendsto_sq_mul_integral_monotoneCoupling_sq_criticalClocks :
    Tendsto (fun ε : ℝ => ε ^ 2 * ∫ z, |z.1 - z.2| ^ 2
        ∂(monotoneCoupling (squarefreeClockLaw (1 + ε)) (eulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_integral_monotoneCoupling_sq_criticalClocks.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  haveI := isProbabilityMeasure_squarefreeClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  haveI := isProbabilityMeasure_eulerClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  rw [scaledSquarefreeClockLaw, scaledEulerClockLaw, show (1 : ℝ) + ε - 1 = ε by ring,
    integral_monotoneCoupling_sq_sub_scaleLaw hεpos]

/-- **`(15c)` as the card writes it.**  The centered thermal scores of the two clocks, with the
escape parameter explicit and the clocks unscaled, are coupled in `L²`. -/
theorem tendsto_sq_mul_integral_monotoneCoupling_centered_sq_criticalClocks :
    Tendsto (fun ε : ℝ => ε ^ 2 * ∫ z, |(z.1 - ∫ x, x ∂(squarefreeClockLaw (1 + ε)))
        - (z.2 - ∫ x, x ∂(eulerClockLaw (1 + ε)))| ^ 2
        ∂(monotoneCoupling (squarefreeClockLaw (1 + ε)) (eulerClockLaw (1 + ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_integral_monotoneCoupling_centered_sq_criticalClocks.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0 : ℝ) < ε := hε
  haveI := isProbabilityMeasure_squarefreeClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  haveI := isProbabilityMeasure_eulerClockLaw (show (1 : ℝ) < 1 + ε by linarith)
  rw [scaledSquarefreeClockLaw, scaledEulerClockLaw, show (1 : ℝ) + ε - 1 = ε by ring,
    integral_monotoneCoupling_centered_sq_scaleLaw hεpos]

/-- **The two currents are the same arithmetic object.**  The logarithmic current of the signed
moving multiplier at the base point and the normalized normal derivative of the packet connection
agree: both are the escape parameter times the von Mangoldt current. -/
theorem logDeriv_mobiusMovingMultiplier_eq_half_mul_deriv_suzukiPacketDirichlet
    {σ ε : ℝ} (hσ : 1 < σ) (hε : 0 < ε) :
    logDeriv (fun v : ℝ => RHTower.mobiusMovingMultiplier σ ε v) 0
      = ((ε : ℂ) / 2) * deriv (fun a : ℝ => RHTower.suzukiPacketDirichlet a (σ : ℂ)) 0 := by
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hpacket := (RHTower.hasDerivAt_suzukiPacketDirichlet hre).deriv
  have hcurrent := RHTower.logDeriv_mobiusMovingMultiplier hσ hε (le_refl (0 : ℝ))
  rw [hpacket, hcurrent]
  push_cast
  ring_nf

/-- **The ordered two-clock law.**  The source has two geometrically distinct clocks, and the order
of their limits is forced.  Differentiating the packet connection in the shift at fixed escape and
only then letting the escape vanish returns the von Mangoldt unit; tying the shift to the thermal
parameter first returns `3` instead, and the correspondingly normalized quotient diverges. -/
theorem orderedTwoClockLaw :
    Tendsto (fun ε : ℝ =>
        ((ε : ℂ) / 2) * deriv (fun a : ℝ => RHTower.suzukiPacketDirichlet a ((1 + ε : ℝ) : ℂ)) 0)
      (𝓝[>] (0 : ℝ)) (𝓝 1)
    ∧ Tendsto (fun a : ℝ => RHTower.suzukiPacketDirichlet a (1 + 2 * (a : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 3)
    ∧ Tendsto (fun a : ℝ =>
        ‖(RHTower.suzukiPacketDirichlet a (1 + 2 * (a : ℂ)) - 1) / (2 * (a : ℂ))‖)
      (𝓝[>] (0 : ℝ)) atTop :=
  ⟨tendsto_half_mul_deriv_suzukiPacketDirichlet,
    RHTower.tendsto_suzukiPacketDirichlet_diagonal,
    tendsto_norm_diagonalShortcutQuotient_atTop⟩

end

end GaloisForLFunctions.HTGeometry
