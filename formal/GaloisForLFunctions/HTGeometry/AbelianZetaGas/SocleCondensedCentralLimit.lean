import GaloisForLFunctions.HTGeometry.AbelianZetaGas.QGammaCumulantExpansion
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The central limit theorem strictly inside the condensed chamber

For `1/2 < σ < 1` let `S_P = ∑_{p ≤ P} ξ_p` be the sum of the independent socle coordinates, each
with the q-Gamma law of the prime nome `q_p = p^{-σ}`.  Its characteristic function is
`exp ∑_{p ≤ P} Φ_{q_p}`, so its mean is `m_P = ∑ κ₁(q_p)` and its variance is
`s_P² = ∑ κ₂(q_p)`.  The cubic cumulant bound, the comparison `K₃(q) ≤ 512 κ₂(q)/ℓ²` valid for
`q < 3/4`, and `|ℓ_p| = σ log p ≤ σ log P` give

`log φ_{(S_P - m_P)/s_P}(t) = -t²/2 + O(σ |t|³ log P / s_P)`.

Chebyshev's `θ(P) ≥ P/2` gives `s_P² ≥ (σ² log 2/2) P^{1-σ}`, so `log P / s_P → 0` and the
standardized sums converge in law to the standard Gaussian.
-/

open Complex Filter MeasureTheory ProbabilityTheory Asymptotics
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

theorem mem_primeCutoff {P : ℕ} {p : Nat.Primes} : p ∈ primeCutoff P ↔ (p : ℕ) ≤ P := by
  constructor
  · intro hp
    rw [primeCutoff, Finset.mem_map] at hp
    obtain ⟨i, -, rfl⟩ := hp
    exact (Nat.mem_primesLE.mp i.2).1
  · intro hp
    rw [primeCutoff, Finset.mem_map]
    exact ⟨⟨p, Nat.mem_primesLE.mpr ⟨hp, p.2⟩⟩, Finset.mem_univ _, rfl⟩

theorem sum_primeCutoff (P : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ primeCutoff P, f (p : ℕ) = ∑ n ∈ Nat.primesLE P, f n := by
  rw [primeCutoff, Finset.sum_map]
  exact Finset.sum_coe_sort (Nat.primesLE P) f

theorem log_primeNome {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    Real.log (primeNome hσ p).val = -(σ * Real.log ((p : ℕ) : ℝ)) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [primeNome_val, Real.log_rpow hp]
  ring

/-- The law of `S_P = ∑_{p ≤ P} ξ_p`. -/
def condensedSocleLaw {σ : ℝ} (hσ : 0 < σ) (P : ℕ) : Measure ℝ :=
  soclePrimePartialMeasure hσ (fun _ => 0) P

instance {σ : ℝ} (hσ : 0 < σ) (P : ℕ) : IsProbabilityMeasure (condensedSocleLaw hσ P) := by
  rw [condensedSocleLaw]
  infer_instance

/-- `m_P = ∑_{p ≤ P} κ₁(q_p)`. -/
def condensedSocleMean {σ : ℝ} (hσ : 0 < σ) (P : ℕ) : ℝ :=
  ∑ p ∈ primeCutoff P, (primeNome hσ p).lawMean

/-- `s_P² = ∑_{p ≤ P} κ₂(q_p)`. -/
def condensedSocleVariance {σ : ℝ} (hσ : 0 < σ) (P : ℕ) : ℝ :=
  ∑ p ∈ primeCutoff P, (primeNome hσ p).lawVariance

/-- The cubic constant `∑_{p ≤ P} 2|ℓ_p|³ K₃(q_p)`. -/
def condensedSocleCubic {σ : ℝ} (hσ : 0 < σ) (P : ℕ) : ℝ :=
  ∑ p ∈ primeCutoff P, 2 * |Real.log (primeNome hσ p).val| ^ 3 * (primeNome hσ p).cubeSeries

theorem charFun_condensedSocleLaw {σ : ℝ} (hσ : 0 < σ) (P : ℕ) (t : ℝ) :
    charFun (condensedSocleLaw hσ P) t
      = cexp (∑ p ∈ primeCutoff P, (primeNome hσ p).cumulant t) := by
  rw [condensedSocleLaw, charFun_soclePrimePartialMeasure, Complex.exp_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← qChar_eq_qGammaOn_one_add_I, RealEulerNome.qChar_eq_cexp_cumulant]
  simp

theorem norm_condensedSocleCumulant_sub_le {σ : ℝ} (hσ : 0 < σ) (P : ℕ) (t : ℝ) :
    ‖∑ p ∈ primeCutoff P, (primeNome hσ p).cumulant t
        - ((condensedSocleMean hσ P : ℂ) * (t : ℂ) * I
          - (condensedSocleVariance hσ P : ℂ) * (t : ℂ) ^ 2 / 2)‖
      ≤ condensedSocleCubic hσ P * |t| ^ 3 := by
  have hsplit : ∑ p ∈ primeCutoff P, (primeNome hσ p).cumulant t
        - ((condensedSocleMean hσ P : ℂ) * (t : ℂ) * I
          - (condensedSocleVariance hσ P : ℂ) * (t : ℂ) ^ 2 / 2)
      = ∑ p ∈ primeCutoff P, ((primeNome hσ p).cumulant t
        - (((primeNome hσ p).lawMean : ℂ) * (t : ℂ) * I
          - ((primeNome hσ p).lawVariance : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    simp only [condensedSocleMean, condensedSocleVariance, Complex.ofReal_sum, Finset.sum_mul,
      Finset.sum_div, Finset.sum_sub_distrib]
  rw [hsplit, condensedSocleCubic, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  exact (primeNome hσ p).norm_cumulant_sub_le t

theorem memLp_two_condensedSocleLaw {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    MemLp id 2 (condensedSocleLaw hσ P) := by
  rw [condensedSocleLaw, soclePrimePartialMeasure,
    memLp_map_measure_iff measurable_id.aestronglyMeasurable
      (measurable_soclePrimePartialSum _ P).aemeasurable]
  change MemLp (fun x : SoclePrimeIndex P → ℝ =>
    ∑ p : SoclePrimeIndex P, (x p - 0)) 2 _
  refine memLp_finsetSum Finset.univ fun p _ => ?_
  have h := (primeNome hσ (soclePrimeIndexPrime p)).memLp_two_qLaw.comp_measurePreserving
    (measurePreserving_eval (fun p : SoclePrimeIndex P =>
      qLaw (primeNome hσ (soclePrimeIndexPrime p))) p)
  simpa using h

/-- **Mean and variance of `S_P`.**  `E S_P = m_P` and `Var S_P = s_P²`. -/
theorem moments_condensedSocleLaw {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    ∫ x, x ∂(condensedSocleLaw hσ P) = condensedSocleMean hσ P ∧
      Var[id; condensedSocleLaw hσ P] = condensedSocleVariance hσ P := by
  have h := moments_of_charFun_cubic (memLp_two_condensedSocleLaw hσ P)
    (charFun_condensedSocleLaw hσ P) (norm_condensedSocleCumulant_sub_le hσ P)
  refine ⟨h.1, ?_⟩
  rw [variance_eq_sub (memLp_two_condensedSocleLaw hσ P)]
  simp only [id, Pi.pow_apply]
  rw [h.1, h.2]
  ring

theorem condensedSocleVariance_nonneg {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    0 ≤ condensedSocleVariance hσ P := by
  have h := (moments_condensedSocleLaw hσ P).2
  rw [← h]
  exact variance_nonneg _ _

/-! ## Standardization -/

/-- The standard deviation `s_P`. -/
def condensedSocleScale {σ : ℝ} (hσ : 0 < σ) (P : ℕ) : ℝ :=
  Real.sqrt (condensedSocleVariance hσ P)

/-- The law of the standardized sum `(S_P - m_P)/s_P`. -/
def condensedSocleStandardized {σ : ℝ} (hσ : 0 < σ) (P : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(condensedSocleLaw hσ P).map
      (fun x => (x - condensedSocleMean hσ P) / condensedSocleScale hσ P),
    Measure.isProbabilityMeasure_map (by fun_prop)⟩

theorem charFun_condensedSocleStandardized {σ : ℝ} (hσ : 0 < σ) (P : ℕ) (t : ℝ) :
    charFun (condensedSocleStandardized hσ P : Measure ℝ) t
      = cexp (∑ p ∈ primeCutoff P,
          (primeNome hσ p).cumulant (t / condensedSocleScale hσ P)
        - ((t / condensedSocleScale hσ P * condensedSocleMean hσ P : ℝ) : ℂ) * I) := by
  set s := condensedSocleScale hσ P
  set m := condensedSocleMean hσ P
  have hmap : charFun (condensedSocleStandardized hσ P : Measure ℝ) t
      = ∫ x, cexp ((t : ℂ) * (((x - m) / s : ℝ) : ℂ) * I) ∂(condensedSocleLaw hσ P) := by
    rw [charFun_apply_real]
    change ∫ x, cexp ((t : ℂ) * (x : ℂ) * I) ∂((condensedSocleLaw hσ P).map
      (fun x => (x - m) / s)) = _
    rw [integral_map (by fun_prop) (by fun_prop)]
  have hsplit : ∀ x : ℝ, cexp ((t : ℂ) * (((x - m) / s : ℝ) : ℂ) * I)
      = cexp (-(((t / s * m : ℝ) : ℂ) * I)) * cexp (((t / s : ℝ) : ℂ) * (x : ℂ) * I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hmap]
  simp only [hsplit]
  rw [integral_const_mul, ← charFun_apply_real, charFun_condensedSocleLaw, ← Complex.exp_add]
  congr 1
  ring

/-! ## The Lyapunov ratio -/

theorem cubeSeries_le_varSeries_of_lt {q : RealEulerNome} (hq : q.val < 3 / 4) :
    q.cubeSeries ≤ 512 * q.varSeries := by
  have h1 := q.cubeSeries_le
  have h2 := q.le_varSeries
  have hq0 := q.pos
  have hq1 : 1 / 4 < 1 - q.val := by linarith
  have h4 : (1 / 4 : ℝ) ^ 4 ≤ (1 - q.val) ^ 4 := pow_le_pow_left₀ (by norm_num) hq1.le 4
  have hbound : 2 * q.val / (1 - q.val) ^ 4 ≤ 512 * q.val := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem abs_log_primeNome {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    |Real.log (primeNome hσ p).val| = σ * Real.log ((p : ℕ) : ℝ) := by
  have hlog : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  rw [log_primeNome, abs_neg, abs_of_nonneg (mul_nonneg hσ.le hlog)]

/-- `∑ 2|ℓ_p|³ K₃(q_p) ≤ 1024 σ log P · s_P²`. -/
theorem condensedSocleCubic_le {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (P : ℕ) :
    condensedSocleCubic hσ P
      ≤ 1024 * σ * Real.log (P : ℝ) * condensedSocleVariance hσ P := by
  rw [condensedSocleCubic, condensedSocleVariance, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpP : (p : ℕ) ≤ P := mem_primeCutoff.mp hp
  have hlogp : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  have hlogP : Real.log ((p : ℕ) : ℝ) ≤ Real.log (P : ℝ) :=
    Real.log_le_log (by exact_mod_cast p.2.pos) (by exact_mod_cast hpP)
  have hcube := cubeSeries_le_varSeries_of_lt (primeNome_lt_three_quarters hσ hhalf p)
  have hvar0 : 0 ≤ (primeNome hσ p).varSeries := le_trans (primeNome hσ p).pos.le
    (primeNome hσ p).le_varSeries
  rw [RealEulerNome.lawVariance, abs_log_primeNome]
  have hlq : Real.log (primeNome hσ p).val ^ 2 = (σ * Real.log ((p : ℕ) : ℝ)) ^ 2 := by
    rw [← sq_abs, abs_log_primeNome]
  rw [hlq]
  have hA : 0 ≤ σ * Real.log ((p : ℕ) : ℝ) := mul_nonneg hσ.le hlogp
  calc 2 * (σ * Real.log ((p : ℕ) : ℝ)) ^ 3 * (primeNome hσ p).cubeSeries
      ≤ 2 * (σ * Real.log ((p : ℕ) : ℝ)) ^ 3 * (512 * (primeNome hσ p).varSeries) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 1024 * (σ * Real.log ((p : ℕ) : ℝ)) * ((σ * Real.log ((p : ℕ) : ℝ)) ^ 2
          * (primeNome hσ p).varSeries) := by ring
    _ ≤ 1024 * (σ * Real.log (P : ℝ)) * ((σ * Real.log ((p : ℕ) : ℝ)) ^ 2
          * (primeNome hσ p).varSeries) := by
        gcongr
    _ = _ := by ring

/-! ## Growth of the variance -/

/-- `s_P² ≥ σ² log 2 · P^{-σ} θ(P)`. -/
theorem condensedSocleVariance_ge_theta {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    σ ^ 2 * Real.log 2 * (P : ℝ) ^ (-σ) * Chebyshev.theta (P : ℝ)
      ≤ condensedSocleVariance hσ P := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, ← sum_primeCutoff P (fun n => Real.log (n : ℝ)),
    Finset.mul_sum, condensedSocleVariance]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpP : (p : ℕ) ≤ P := mem_primeCutoff.mp hp
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2p : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log (by norm_num) hp2
  have hpow : (P : ℝ) ^ (-σ) ≤ ((p : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by exact_mod_cast hpP) (by linarith)
  have hvar := (primeNome hσ p).le_varSeries
  rw [primeNome_val] at hvar
  rw [RealEulerNome.lawVariance]
  have hlq : Real.log (primeNome hσ p).val ^ 2 = σ ^ 2 * Real.log ((p : ℕ) : ℝ) ^ 2 := by
    rw [← sq_abs, abs_log_primeNome]
    ring
  rw [hlq]
  have hP0 : 0 ≤ (P : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlogp0 : 0 ≤ Real.log ((p : ℕ) : ℝ) := by linarith
  have hsq : Real.log 2 * Real.log ((p : ℕ) : ℝ) ≤ Real.log ((p : ℕ) : ℝ) ^ 2 := by nlinarith
  calc σ ^ 2 * Real.log 2 * (P : ℝ) ^ (-σ) * Real.log ((p : ℕ) : ℝ)
      = σ ^ 2 * (Real.log 2 * Real.log ((p : ℕ) : ℝ)) * (P : ℝ) ^ (-σ) := by ring
    _ ≤ σ ^ 2 * Real.log ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-σ) := by gcongr
    _ ≤ σ ^ 2 * Real.log ((p : ℕ) : ℝ) ^ 2 * (primeNome hσ p).varSeries := by gcongr
    _ = _ := by ring

theorem eventually_theta_ge_half : ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.theta x := by
  have h := (isEquivalent_iff_tendsto_one (eventually_ne_atTop 0)).mp chebyshev_asymptotic
  filter_upwards [h.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop 0] with x hx hx0
  simp only [Pi.div_apply] at hx
  rw [lt_div_iff₀ hx0] at hx
  linarith

/-- **Growth of the variance.**  Eventually `s_P² ≥ (σ² log 2/2) P^{1-σ}`. -/
theorem eventually_condensedSocleVariance_ge {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ P : ℕ in atTop, σ ^ 2 * Real.log 2 / 2 * (P : ℝ) ^ (1 - σ)
      ≤ condensedSocleVariance hσ P := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually eventually_theta_ge_half,
    eventually_gt_atTop 0] with P hP hP0
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP0
  have hθ := condensedSocleVariance_ge_theta hσ P
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrp : (P : ℝ) ^ (1 - σ) = (P : ℝ) ^ (-σ) * P := by
    rw [sub_eq_neg_add, Real.rpow_add hPpos, Real.rpow_one]
  have hc : 0 ≤ σ ^ 2 * Real.log 2 * (P : ℝ) ^ (-σ) := by positivity
  calc σ ^ 2 * Real.log 2 / 2 * (P : ℝ) ^ (1 - σ)
      = σ ^ 2 * Real.log 2 * (P : ℝ) ^ (-σ) * ((P : ℝ) / 2) := by rw [hrp]; ring
    _ ≤ σ ^ 2 * Real.log 2 * (P : ℝ) ^ (-σ) * Chebyshev.theta (P : ℝ) :=
        mul_le_mul_of_nonneg_left hP hc
    _ ≤ _ := hθ

/-- `s_P² → ∞` throughout `0 < σ < 1`. -/
theorem tendsto_condensedSocleVariance_atTop {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (condensedSocleVariance hσ) atTop atTop := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : Tendsto (fun P : ℕ => σ ^ 2 * Real.log 2 / 2 * (P : ℝ) ^ (1 - σ)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by positivity)
  exact tendsto_atTop_mono' atTop (eventually_condensedSocleVariance_ge hσ) hpow

/-- **The Lyapunov ratio vanishes.**  `log P / s_P → 0` for `0 < σ < 1`. -/
theorem tendsto_log_div_condensedSocleScale {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun P : ℕ => Real.log (P : ℝ) / condensedSocleScale hσ P) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.sqrt (σ ^ 2 * Real.log 2 / 2) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hr : 0 < (1 - σ) / 2 := by linarith
  have hlo := (isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hbound := hlo.def (show 0 < ε / 2 * c by positivity)
  filter_upwards [hbound, eventually_condensedSocleVariance_ge hσ, eventually_gt_atTop 1]
    with P hPb hPv hP1
  have hP1' : (1 : ℝ) < P := by exact_mod_cast hP1
  have hPpos : (0 : ℝ) < P := by linarith
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos hP1'
  simp only [Function.comp_apply, Real.norm_eq_abs] at hPb
  rw [abs_of_pos hlogP, abs_of_pos (Real.rpow_pos_of_pos hPpos _)] at hPb
  have hscale : c * (P : ℝ) ^ ((1 - σ) / 2) ≤ condensedSocleScale hσ P := by
    rw [condensedSocleScale]
    have hpow2 : ((P : ℝ) ^ ((1 - σ) / 2)) ^ 2 = (P : ℝ) ^ (1 - σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le]
      norm_num
    have hsq : (c * (P : ℝ) ^ ((1 - σ) / 2)) ^ 2 = σ ^ 2 * Real.log 2 / 2 * (P : ℝ) ^ (1 - σ) := by
      rw [mul_pow, hcdef, Real.sq_sqrt (by positivity), hpow2]
    rw [← hsq] at hPv
    exact Real.le_sqrt_of_sq_le hPv
  have hspos : 0 < condensedSocleScale hσ P :=
    lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos hPpos _)) hscale
  rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hlogP hspos), div_lt_iff₀ hspos]
  calc Real.log (P : ℝ) ≤ ε / 2 * c * (P : ℝ) ^ ((1 - σ) / 2) := hPb
    _ = ε / 2 * (c * (P : ℝ) ^ ((1 - σ) / 2)) := by ring
    _ ≤ ε / 2 * condensedSocleScale hσ P := by gcongr
    _ < ε * condensedSocleScale hσ P := by nlinarith

/-! ## The central limit theorem -/

theorem condensedSocleScale_sq {σ : ℝ} (hσ : 0 < σ) (P : ℕ) :
    condensedSocleScale hσ P ^ 2 = condensedSocleVariance hσ P :=
  Real.sq_sqrt (condensedSocleVariance_nonneg hσ P)

/-- The standardized log-characteristic function is `-t²/2` up to `1024σ|t|³ log P/s_P`. -/
theorem norm_standardizedExponent_sub_le {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (P : ℕ)
    (hs : 0 < condensedSocleScale hσ P) (t : ℝ) :
    ‖(∑ p ∈ primeCutoff P, (primeNome hσ p).cumulant (t / condensedSocleScale hσ P)
        - ((t / condensedSocleScale hσ P * condensedSocleMean hσ P : ℝ) : ℂ) * I)
        - (-(t : ℂ) ^ 2 / 2)‖
      ≤ 1024 * σ * |t| ^ 3 * (Real.log (P : ℝ) / condensedSocleScale hσ P) := by
  set s := condensedSocleScale hσ P with hsdef
  set a : ℝ := t / s with hadef
  have h := norm_condensedSocleCumulant_sub_le hσ P a
  have hv : condensedSocleVariance hσ P = s ^ 2 := (condensedSocleScale_sq hσ P).symm
  have heq : (∑ p ∈ primeCutoff P, (primeNome hσ p).cumulant a
        - ((a * condensedSocleMean hσ P : ℝ) : ℂ) * I) - (-(t : ℂ) ^ 2 / 2)
      = ∑ p ∈ primeCutoff P, (primeNome hσ p).cumulant a
        - ((condensedSocleMean hσ P : ℂ) * (a : ℂ) * I
          - (condensedSocleVariance hσ P : ℂ) * (a : ℂ) ^ 2 / 2) := by
    rw [hv, hadef]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
    ring
  rw [heq]
  refine h.trans ?_
  have hC := condensedSocleCubic_le hσ hhalf P
  have hlogP : 0 ≤ Real.log (P : ℝ) := Real.log_natCast_nonneg P
  have ha3 : |a| ^ 3 = |t| ^ 3 / s ^ 3 := by
    rw [hadef, abs_div, abs_of_pos hs, div_pow]
  rw [ha3, hv] at *
  calc condensedSocleCubic hσ P * (|t| ^ 3 / s ^ 3)
      ≤ 1024 * σ * Real.log (P : ℝ) * s ^ 2 * (|t| ^ 3 / s ^ 3) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
    _ = 1024 * σ * |t| ^ 3 * (Real.log (P : ℝ) / s) := by
        field_simp

theorem eventually_condensedSocleScale_pos {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ P : ℕ in atTop, 0 < condensedSocleScale hσ P := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_condensedSocleVariance_ge hσ, eventually_gt_atTop 0] with P hP hP0
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP0
  have hpos : 0 < σ ^ 2 * Real.log 2 / 2 * (P : ℝ) ^ (1 - σ) := by
    have := Real.rpow_pos_of_pos hPpos (1 - σ)
    positivity
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le hpos hP)

/-- **Theorem 3.1 (GAS3.5): central limit theorem in the condensed chamber.**  For
`1/2 < σ < 1`, `(S_P - E S_P)/s_P` converges in law to the standard Gaussian. -/
theorem tendsto_condensedSocleStandardized_gaussian {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ)
    (hσ1 : σ < 1) :
    Tendsto (condensedSocleStandardized hσ) atTop
      (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun t => ?_
  have hG : charFun (gaussianReal 0 1) t = cexp (-(t : ℂ) ^ 2 / 2) := by
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  change Tendsto (fun P => charFun (condensedSocleStandardized hσ P : Measure ℝ) t) atTop
    (𝓝 (charFun (gaussianReal 0 1) t))
  rw [hG]
  simp_rw [charFun_condensedSocleStandardized]
  refine (Complex.continuous_exp.tendsto _).comp ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmaj : Tendsto (fun P : ℕ => 1024 * σ * |t| ^ 3 *
      (Real.log (P : ℝ) / condensedSocleScale hσ P)) atTop (𝓝 0) := by
    simpa using (tendsto_log_div_condensedSocleScale hσ hσ1).const_mul (1024 * σ * |t| ^ 3)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_condensedSocleScale_pos hσ] with P hP
  exact norm_standardizedExponent_sub_le hσ hhalf P hP t

end GaloisForLFunctions.HTGeometry
