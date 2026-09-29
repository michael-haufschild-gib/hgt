import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SoclePrimePartialLaw
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCharFun
import GaloisForLFunctions.HTGeometry.CharFunCubicMoments
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic

/-!
# The cumulant expansion of the q-Gamma law

For a nome `0 < q < 1` with `ℓ = log q`, the characteristic function of the atomic q-Gamma law
(atoms `nℓ - log(1-q)`, weights `(q;q)_∞ qⁿ/(q;q)_n`) is `exp Φ_q(t)` with

`Φ_q(t) = -it log(1-q) + ∑_{j,r ≥ 0} q^{(j+1)(r+1)} (e^{i(r+1)tℓ} - 1)/(r+1)`.

Each depth factor `(1 - q^{j+1})/(1 - q^{j+1}e^{itℓ})` is the exponential of its harmonic series,
and the depth product is the exponential of the double series.  Expanding
`e^{ix} - 1 = ix - x²/2 + O(|x|³)` termwise gives

`Φ_q(t) = i κ₁ t - κ₂ t²/2 + O(|ℓ|³ K₃ |t|³)`,

with `κ₁ = -log(1-q) + ℓ ∑ q^{(j+1)(r+1)}`, `κ₂ = ℓ² ∑ (r+1) q^{(j+1)(r+1)}` and
`K₃ = ∑ (r+1)² q^{(j+1)(r+1)}`.  Hence `κ₁` is the mean and `κ₂` the variance of the law.  The
variance series satisfies `q ≤ ∑ (r+1) q^{(j+1)(r+1)} ≤ q/(1-q)³`, and the cubic series is at most
`2q/(1-q)⁴`.
-/

open Complex Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace RealEulerNome

variable (q : RealEulerNome)

/-- The `(depth, harmonic)` term `q^{(j+1)(r+1)} (e^{i(r+1)tℓ} - 1)/(r+1)` of the cumulant. -/
def cumulantTerm (t : ℝ) (jr : ℕ × ℕ) : ℂ :=
  ((q.val ^ ((jr.1 + 1) * (jr.2 + 1)) / ((jr.2 : ℝ) + 1) : ℝ) : ℂ) *
    (cexp ((((jr.2 : ℝ) + 1) * t * Real.log q.val : ℝ) * I) - 1)

/-- The weighted ladder `(r+1)^k q^{(j+1)(r+1)}`. -/
def ladderWeight (k : ℕ) (jr : ℕ × ℕ) : ℝ :=
  ((jr.2 : ℝ) + 1) ^ k * q.val ^ ((jr.1 + 1) * (jr.2 + 1))

theorem ladderWeight_nonneg (k : ℕ) (jr : ℕ × ℕ) : 0 ≤ q.ladderWeight k jr := by
  have := q.pos
  unfold ladderWeight
  positivity

theorem pow_ladder_le (jr : ℕ × ℕ) :
    q.val ^ ((jr.1 + 1) * (jr.2 + 1)) ≤ q.val ^ (jr.1 + 1) * q.val ^ jr.2 := by
  rw [← pow_add]
  refine pow_le_pow_of_le_one q.pos.le q.lt_one.le ?_
  nlinarith

theorem summable_succ_pow_mul_nome (k : ℕ) :
    Summable fun r : ℕ => ((r : ℝ) + 1) ^ k * q.val ^ r :=
  (summable_succ_pow_mul_geometric k q.pos.le q.lt_one).congr fun r => by push_cast; ring

theorem summable_ladderMajorant (k : ℕ) :
    Summable fun jr : ℕ × ℕ => q.val ^ (jr.1 + 1) * (((jr.2 : ℝ) + 1) ^ k * q.val ^ jr.2) := by
  have hj : Summable fun j : ℕ => q.val ^ (j + 1) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one q.pos.le q.lt_one)
  exact hj.mul_of_nonneg (q.summable_succ_pow_mul_nome k)
    (fun j => by have := q.pos; positivity) (fun r => by have := q.pos; positivity)

theorem ladderWeight_le_majorant (k : ℕ) (jr : ℕ × ℕ) :
    q.ladderWeight k jr ≤ q.val ^ (jr.1 + 1) * (((jr.2 : ℝ) + 1) ^ k * q.val ^ jr.2) := by
  have h := q.pow_ladder_le jr
  have hk : (0 : ℝ) ≤ ((jr.2 : ℝ) + 1) ^ k := by positivity
  unfold ladderWeight
  nlinarith

theorem summable_ladderWeight (k : ℕ) : Summable (q.ladderWeight k) :=
  Summable.of_nonneg_of_le (q.ladderWeight_nonneg k) (q.ladderWeight_le_majorant k)
    (q.summable_ladderMajorant k)

/-- `∑ q^{(j+1)(r+1)}`. -/
def meanSeries : ℝ := ∑' jr, q.ladderWeight 0 jr

/-- `∑ (r+1) q^{(j+1)(r+1)}`. -/
def varSeries : ℝ := ∑' jr, q.ladderWeight 1 jr

/-- `∑ (r+1)² q^{(j+1)(r+1)}`. -/
def cubeSeries : ℝ := ∑' jr, q.ladderWeight 2 jr

/-- The mean `κ₁ = -log(1-q) + ℓ ∑ q^{(j+1)(r+1)}` of the q-Gamma law. -/
def lawMean : ℝ := -Real.log (1 - q.val) + Real.log q.val * q.meanSeries

/-- The variance `κ₂ = ℓ² ∑ (r+1) q^{(j+1)(r+1)}` of the q-Gamma law. -/
def lawVariance : ℝ := Real.log q.val ^ 2 * q.varSeries

/-- The cumulant exponent `Φ_q(t)`. -/
def cumulant (t : ℝ) : ℂ :=
  ((-(t * Real.log (1 - q.val)) : ℝ) : ℂ) * I + ∑' jr, q.cumulantTerm t jr

theorem norm_cumulantTerm_le (t : ℝ) (jr : ℕ × ℕ) :
    ‖q.cumulantTerm t jr‖ ≤ 2 * (q.val ^ (jr.1 + 1) * q.val ^ jr.2) := by
  have hq := q.pos
  have hr : (1 : ℝ) ≤ (jr.2 : ℝ) + 1 := by linarith [(Nat.cast_nonneg jr.2 : (0 : ℝ) ≤ jr.2)]
  have hexp : ‖cexp ((((jr.2 : ℝ) + 1) * t * Real.log q.val : ℝ) * I) - 1‖ ≤ 2 := by
    calc _ ≤ ‖cexp ((((jr.2 : ℝ) + 1) * t * Real.log q.val : ℝ) * I)‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hcoef : ‖((q.val ^ ((jr.1 + 1) * (jr.2 + 1)) / ((jr.2 : ℝ) + 1) : ℝ) : ℂ)‖
      ≤ q.val ^ (jr.1 + 1) * q.val ^ jr.2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc q.val ^ ((jr.1 + 1) * (jr.2 + 1)) / ((jr.2 : ℝ) + 1)
        ≤ q.val ^ ((jr.1 + 1) * (jr.2 + 1)) := div_le_self (by positivity) hr
      _ ≤ _ := q.pow_ladder_le jr
  rw [cumulantTerm, norm_mul]
  calc _ ≤ (q.val ^ (jr.1 + 1) * q.val ^ jr.2) * 2 :=
        mul_le_mul hcoef hexp (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem summable_norm_cumulantTerm (t : ℝ) : Summable fun jr => ‖q.cumulantTerm t jr‖ := by
  have hmaj : Summable fun jr : ℕ × ℕ => 2 * (q.val ^ (jr.1 + 1) * q.val ^ jr.2) := by
    have := (q.summable_ladderMajorant 0).mul_left 2
    simpa using this
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (q.norm_cumulantTerm_le t) hmaj

theorem summable_cumulantTerm (t : ℝ) : Summable (q.cumulantTerm t) :=
  (q.summable_norm_cumulantTerm t).of_norm

/-- One depth factor is the exponential of its harmonic series. -/
theorem hasSum_cumulantTerm_depth (t : ℝ) (j : ℕ) :
    HasSum (fun r => q.cumulantTerm t (j, r))
      (-Complex.log (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t))
        + Complex.log (((1 - q.val ^ (j + 1) : ℝ) : ℂ))) := by
  set x : ℝ := q.val ^ (j + 1) with hxdef
  set u : ℂ := modePhase (phaseAngle q t) with hudef
  have hx0 : 0 < x := pow_pos q.pos _
  have hx1 : x < 1 := pow_lt_one₀ q.pos.le q.lt_one (by omega)
  have hu : ‖u‖ = 1 := norm_modePhase _
  have hxu : ‖(x : ℂ) * u‖ < 1 := by
    rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    exact hx1
  have hxr : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]
    exact hx1
  have h1 := Complex.hasSum_taylorSeries_neg_log hxu
  have h2 := Complex.hasSum_taylorSeries_neg_log hxr
  have hsub := h1.sub h2
  have hsub' := (hasSum_nat_add_iff' 1).mpr hsub
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
    sub_self, sub_zero] at hsub'
  have hlog : Complex.log (((1 - x : ℝ) : ℂ)) = Complex.log (1 - (x : ℂ)) := by
    push_cast
    rfl
  have hval : -Complex.log (1 - (x : ℂ) * u) + Complex.log (1 - (x : ℂ))
      = -Complex.log (1 - (x : ℂ) * u) - -Complex.log (1 - (x : ℂ)) := by ring
  have key : (fun r => q.cumulantTerm t (j, r))
      = fun n : ℕ => ((x : ℂ) * u) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)
        - (x : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ) := by
    funext r
    have hu' : u ^ (r + 1)
        = cexp ((((r : ℝ) + 1) * t * Real.log q.val : ℝ) * I) := by
      rw [hudef, modePhase, phaseAngle, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hxpow : (x : ℂ) ^ (r + 1) = ((q.val ^ ((j + 1) * (r + 1)) : ℝ) : ℂ) := by
      rw [hxdef, pow_mul]
      push_cast
      ring
    have hr' : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    rw [cumulantTerm, mul_pow, hu', hxpow]
    push_cast
    field_simp
  rw [hlog, hval, key]
  exact hsub'

theorem cexp_depth_eq (t : ℝ) (j : ℕ) :
    cexp (-Complex.log (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t))
        + Complex.log (((1 - q.val ^ (j + 1) : ℝ) : ℂ)))
      = ((1 - q.val ^ (j + 1) : ℝ) : ℂ)
          / (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t)) := by
  have hne1 : (1 : ℂ) - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t) ≠ 0 :=
    defectFactor_ne_zero q _ j
  have hne2 : (((1 - q.val ^ (j + 1) : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (realQFactorial_factor_pos q j).ne'
  rw [Complex.exp_add, Complex.exp_neg, Complex.exp_log hne1, Complex.exp_log hne2]
  field_simp

/-- **The characteristic function is the exponential of the cumulant.** -/
theorem qChar_eq_cexp_cumulant (t : ℝ) : qChar q t = cexp (q.cumulant t) := by
  have hsum : HasSum (q.cumulantTerm t) (∑' jr, q.cumulantTerm t jr) :=
    (q.summable_cumulantTerm t).hasSum
  have hfib := hsum.prod_fiberwise fun j => q.hasSum_cumulantTerm_depth t j
  have hprod := hfib.cexp
  have hprod' : HasProd (fun j : ℕ => ((1 - q.val ^ (j + 1) : ℝ) : ℂ)
      / (1 - ((q.val ^ (j + 1) : ℝ) : ℂ) * modePhase (phaseAngle q t)))
      (cexp (∑' jr, q.cumulantTerm t jr)) := by
    refine hprod.congr_fun fun j => ?_
    simp only [Function.comp_apply]
    exact (q.cexp_depth_eq t j).symm
  rw [qChar_eq_qGammaOn_one_add_I, qGammaOn_eq_centered_tprod, hprod'.tprod_eq, cumulant,
    Complex.exp_add]

/-- The cubic remainder of one ladder term. -/
theorem norm_cumulantTerm_sub_le (t : ℝ) (jr : ℕ × ℕ) :
    ‖q.cumulantTerm t jr - (((q.ladderWeight 0 jr : ℝ) : ℂ) * ((t * Real.log q.val : ℝ) : ℂ) * I
        - ((q.ladderWeight 1 jr : ℝ) : ℂ) * ((t * Real.log q.val : ℝ) : ℂ) ^ 2 / 2)‖
      ≤ 2 * |t * Real.log q.val| ^ 3 * q.ladderWeight 2 jr := by
  obtain ⟨j, r⟩ := jr
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hc0 : 0 ≤ q.val ^ ((j + 1) * (r + 1)) := by have := q.pos; positivity
  have hexpand : q.cumulantTerm t (j, r)
      - (((q.ladderWeight 0 (j, r) : ℝ) : ℂ) * ((t * Real.log q.val : ℝ) : ℂ) * I
        - ((q.ladderWeight 1 (j, r) : ℝ) : ℂ) * ((t * Real.log q.val : ℝ) : ℂ) ^ 2 / 2)
      = ((q.val ^ ((j + 1) * (r + 1)) / ((r : ℝ) + 1) : ℝ) : ℂ) *
        (cexp (((((r : ℝ) + 1) * (t * Real.log q.val) : ℝ) : ℂ) * I)
          - (1 + ((((r : ℝ) + 1) * (t * Real.log q.val) : ℝ) : ℂ) * I
            - ((((r : ℝ) + 1) * (t * Real.log q.val) : ℝ) : ℂ) ^ 2 / 2)) := by
    have harg : ((((r : ℝ) + 1) * t * Real.log q.val : ℝ) : ℂ)
        = ((((r : ℝ) + 1) * (t * Real.log q.val) : ℝ) : ℂ) := by
      congr 1
      ring
    have hr' : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    simp only [cumulantTerm, ladderWeight]
    rw [harg]
    push_cast
    field_simp
    ring
  rw [hexpand, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb := norm_cexp_mul_I_sub_quadratic_le (((r : ℝ) + 1) * (t * Real.log q.val))
  have hxabs : |((r : ℝ) + 1) * (t * Real.log q.val)| ^ 3
      = ((r : ℝ) + 1) ^ 3 * |t * Real.log q.val| ^ 3 := by
    rw [abs_mul, abs_of_pos hr, mul_pow]
  calc q.val ^ ((j + 1) * (r + 1)) / ((r : ℝ) + 1) * ‖cexp (((((r : ℝ) + 1)
          * (t * Real.log q.val) : ℝ) : ℂ) * I) - (1 + ((((r : ℝ) + 1)
          * (t * Real.log q.val) : ℝ) : ℂ) * I - ((((r : ℝ) + 1)
          * (t * Real.log q.val) : ℝ) : ℂ) ^ 2 / 2)‖
      ≤ q.val ^ ((j + 1) * (r + 1)) / ((r : ℝ) + 1)
          * (2 * |((r : ℝ) + 1) * (t * Real.log q.val)| ^ 3) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 * |t * Real.log q.val| ^ 3 * q.ladderWeight 2 (j, r) := by
        rw [hxabs, ladderWeight]
        field_simp

/-- **Cubic cumulant bound.**  `‖Φ_q(t) - (i κ₁ t - κ₂ t²/2)‖ ≤ 2 |ℓ|³ K₃ |t|³`. -/
theorem norm_cumulant_sub_le (t : ℝ) :
    ‖q.cumulant t - ((q.lawMean : ℂ) * (t : ℂ) * I - (q.lawVariance : ℂ) * (t : ℂ) ^ 2 / 2)‖
      ≤ 2 * |Real.log q.val| ^ 3 * q.cubeSeries * |t| ^ 3 := by
  set y : ℝ := t * Real.log q.val with hy
  set R : ℕ × ℕ → ℂ := fun jr => q.cumulantTerm t jr
    - (((q.ladderWeight 0 jr : ℝ) : ℂ) * (y : ℂ) * I
      - ((q.ladderWeight 1 jr : ℝ) : ℂ) * (y : ℂ) ^ 2 / 2) with hRdef
  have hs0 : Summable fun jr => ((q.ladderWeight 0 jr : ℝ) : ℂ) :=
    Complex.ofRealCLM.summable (q.summable_ladderWeight 0)
  have hs1 : Summable fun jr => ((q.ladderWeight 1 jr : ℝ) : ℂ) :=
    Complex.ofRealCLM.summable (q.summable_ladderWeight 1)
  have hlin : HasSum (fun jr => ((q.ladderWeight 0 jr : ℝ) : ℂ) * (y : ℂ) * I
      - ((q.ladderWeight 1 jr : ℝ) : ℂ) * (y : ℂ) ^ 2 / 2)
      ((q.meanSeries : ℂ) * (y : ℂ) * I - (q.varSeries : ℂ) * (y : ℂ) ^ 2 / 2) := by
    have ha := (hs0.hasSum.mul_right ((y : ℂ) * I))
    have hb := (hs1.hasSum.mul_right ((y : ℂ) ^ 2 / 2))
    rw [← Complex.ofReal_tsum] at ha hb
    have hab := ha.sub hb
    have hv : ((∑' jr, q.ladderWeight 0 jr : ℝ) : ℂ) * ((y : ℂ) * I)
        - ((∑' jr, q.ladderWeight 1 jr : ℝ) : ℂ) * ((y : ℂ) ^ 2 / 2)
        = (q.meanSeries : ℂ) * (y : ℂ) * I - (q.varSeries : ℂ) * (y : ℂ) ^ 2 / 2 := by
      rw [meanSeries, varSeries]
      ring
    rw [hv] at hab
    exact hab.congr_fun fun jr => by ring
  have hR : HasSum R (∑' jr, q.cumulantTerm t jr
      - ((q.meanSeries : ℂ) * (y : ℂ) * I - (q.varSeries : ℂ) * (y : ℂ) ^ 2 / 2)) :=
    (q.summable_cumulantTerm t).hasSum.sub hlin
  have hRnorm : ∀ jr, ‖R jr‖ ≤ 2 * |y| ^ 3 * q.ladderWeight 2 jr := fun jr =>
    q.norm_cumulantTerm_sub_le t jr
  have hmaj : Summable fun jr => 2 * |y| ^ 3 * q.ladderWeight 2 jr :=
    (q.summable_ladderWeight 2).mul_left _
  have hRsum : Summable fun jr => ‖R jr‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hRnorm hmaj
  have heq : q.cumulant t - ((q.lawMean : ℂ) * (t : ℂ) * I
      - (q.lawVariance : ℂ) * (t : ℂ) ^ 2 / 2) = ∑' jr, R jr := by
    rw [hR.tsum_eq, cumulant, lawMean, lawVariance, hy]
    push_cast
    ring
  rw [heq]
  calc ‖∑' jr, R jr‖ ≤ ∑' jr, ‖R jr‖ := norm_tsum_le_tsum_norm hRsum
    _ ≤ ∑' jr, 2 * |y| ^ 3 * q.ladderWeight 2 jr := hRsum.tsum_le_tsum hRnorm hmaj
    _ = 2 * |Real.log q.val| ^ 3 * q.cubeSeries * |t| ^ 3 := by
        rw [tsum_mul_left, cubeSeries, hy, abs_mul, mul_pow]
        ring

/-! ## Moments of the q-Gamma law -/

theorem summable_qGammaWeight_mul_atom_sq :
    Summable fun n : ℕ => qGammaWeight q n * qGammaAtom q n ^ 2 := by
  set a : ℝ := Real.log q.val
  set b : ℝ := Real.log (1 - q.val)
  have hq : ‖q.val‖ < 1 := by rw [Real.norm_of_nonneg q.pos.le]; exact q.lt_one
  have hmaj : Summable fun n : ℕ =>
      2 * a ^ 2 * ((n : ℝ) ^ 2 * q.val ^ n) + 2 * b ^ 2 * q.val ^ n :=
    ((summable_pow_mul_geometric_of_norm_lt_one 2 hq).mul_left _).add
      ((summable_geometric_of_lt_one q.pos.le q.lt_one).mul_left _)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (qGammaWeight_nonneg q n) (sq_nonneg _))
    (fun n => ?_) hmaj
  have hw := qGammaWeight_le_pow q n
  have hw0 := qGammaWeight_nonneg q n
  have hatom : qGammaAtom q n ^ 2 ≤ 2 * a ^ 2 * (n : ℝ) ^ 2 + 2 * b ^ 2 := by
    rw [qGammaAtom]
    nlinarith [sq_nonneg ((n : ℝ) * a + b)]
  have hqn : 0 ≤ q.val ^ n := pow_nonneg q.pos.le n
  calc qGammaWeight q n * qGammaAtom q n ^ 2
      ≤ q.val ^ n * (2 * a ^ 2 * (n : ℝ) ^ 2 + 2 * b ^ 2) :=
        mul_le_mul hw hatom (sq_nonneg _) hqn
    _ = _ := by ring

theorem memLp_two_qLaw : MemLp id 2 (qLaw q) := by
  rw [memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable, qLaw,
    integrable_sum_measure_iff]
  refine ⟨fun n => ?_, ?_⟩
  · refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    exact integrable_dirac (by simp)
  · refine (q.summable_qGammaWeight_mul_atom_sq).congr fun n => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (qGammaWeight_nonneg q n),
      smul_eq_mul, id, Real.norm_of_nonneg (sq_nonneg _)]

theorem charFun_qLaw_eq_cexp (t : ℝ) : charFun (qLaw q) t = cexp (q.cumulant t) := by
  rw [charFun_qLaw, q.qChar_eq_cexp_cumulant]

/-- **Mean and second moment of the q-Gamma law.** -/
theorem moments_qLaw :
    ∫ x, x ∂(qLaw q) = q.lawMean ∧ ∫ x, x ^ 2 ∂(qLaw q) = q.lawVariance + q.lawMean ^ 2 :=
  moments_of_charFun_cubic q.memLp_two_qLaw q.charFun_qLaw_eq_cexp q.norm_cumulant_sub_le

theorem integral_qLaw : ∫ x, x ∂(qLaw q) = q.lawMean := q.moments_qLaw.1

/-- **Variance of the q-Gamma law.** -/
theorem variance_qLaw : Var[id; qLaw q] = q.lawVariance := by
  rw [variance_eq_sub q.memLp_two_qLaw]
  have h := q.moments_qLaw
  simp only [id, Pi.pow_apply] at h ⊢
  rw [h.1, h.2]
  ring

/-! ## Bounds on the variance and cubic series -/

theorem le_varSeries : q.val ≤ q.varSeries := by
  have h := (q.summable_ladderWeight 1).le_tsum (0, 0) (fun jr _ => q.ladderWeight_nonneg 1 jr)
  rw [varSeries]
  simpa [ladderWeight] using h

theorem hasSum_ladderMajorant_one :
    HasSum (fun jr : ℕ × ℕ => q.val ^ (jr.1 + 1) * (((jr.2 : ℝ) + 1) ^ 1 * q.val ^ jr.2))
      (q.val / (1 - q.val) * (1 / (1 - q.val) ^ 2)) := by
  have hq : ‖q.val‖ < 1 := by rw [Real.norm_of_nonneg q.pos.le]; exact q.lt_one
  have hj : HasSum (fun j : ℕ => q.val ^ (j + 1)) (q.val / (1 - q.val)) := by
    have h := (hasSum_geometric_of_lt_one q.pos.le q.lt_one).mul_left q.val
    rw [← div_eq_mul_inv] at h
    exact h.congr_fun fun j => by ring
  have hr : HasSum (fun r : ℕ => ((r : ℝ) + 1) ^ 1 * q.val ^ r) (1 / (1 - q.val) ^ 2) := by
    have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hq
    rw [show (1 : ℕ) + 1 = 2 from rfl] at h
    exact h.congr_fun fun r => by simp [Nat.choose_one_right]
  exact hj.mul hr (q.summable_ladderMajorant 1)

theorem varSeries_le : q.varSeries ≤ q.val / (1 - q.val) ^ 3 := by
  have h1 := q.hasSum_ladderMajorant_one
  have hle : q.varSeries ≤ q.val / (1 - q.val) * (1 / (1 - q.val) ^ 2) := by
    rw [varSeries, ← h1.tsum_eq]
    exact (q.summable_ladderWeight 1).tsum_le_tsum (q.ladderWeight_le_majorant 1)
      (q.summable_ladderMajorant 1)
  have hq1 : 0 < 1 - q.val := by linarith [q.lt_one]
  calc q.varSeries ≤ _ := hle
    _ = q.val / (1 - q.val) ^ 3 := by field_simp

/-- `0 ≤ ∑ (r+1) q^{(j+1)(r+1)} - q ≤ 3q²/(1-q)³`. -/
theorem varSeries_sub_le : q.varSeries - q.val ≤ 3 * q.val ^ 2 / (1 - q.val) ^ 3 := by
  have h := q.varSeries_le
  have hq0 := q.pos
  have hq1 : 0 < 1 - q.val := by linarith [q.lt_one]
  have hkey : q.val / (1 - q.val) ^ 3 - q.val ≤ 3 * q.val ^ 2 / (1 - q.val) ^ 3 := by
    rw [div_sub' (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    have h3 : 0 ≤ q.val ^ 3 * (3 - q.val) := mul_nonneg (by positivity) (by linarith [q.lt_one])
    nlinarith [h3]
  linarith

theorem cubeSeries_le : q.cubeSeries ≤ 2 * q.val / (1 - q.val) ^ 4 := by
  have hq : ‖q.val‖ < 1 := by rw [Real.norm_of_nonneg q.pos.le]; exact q.lt_one
  have hq1 : 0 < 1 - q.val := by linarith [q.lt_one]
  have hj : HasSum (fun j : ℕ => q.val ^ (j + 1)) (q.val / (1 - q.val)) := by
    have h := (hasSum_geometric_of_lt_one q.pos.le q.lt_one).mul_left q.val
    rw [← div_eq_mul_inv] at h
    exact h.congr_fun fun j => by ring
  have hr := (q.summable_succ_pow_mul_nome 2).hasSum
  have hprod := hj.mul hr (q.summable_ladderMajorant 2)
  have hle : q.cubeSeries ≤ q.val / (1 - q.val) * ∑' r : ℕ, ((r : ℝ) + 1) ^ 2 * q.val ^ r := by
    rw [cubeSeries, ← hprod.tsum_eq]
    exact (q.summable_ladderWeight 2).tsum_le_tsum (q.ladderWeight_le_majorant 2)
      (q.summable_ladderMajorant 2)
  have hchoose := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hq
  have hr2 : ∑' r : ℕ, ((r : ℝ) + 1) ^ 2 * q.val ^ r ≤ 2 * (1 / (1 - q.val) ^ (2 + 1)) := by
    rw [← hchoose.tsum_eq, ← tsum_mul_left]
    refine (q.summable_succ_pow_mul_nome 2).tsum_le_tsum (fun r => ?_)
      (hchoose.summable.mul_left 2)
    have hc : (((r + 2).choose 2 : ℕ) : ℝ) = ((r : ℝ) + 2) * ((r : ℝ) + 1) / 2 := by
      rw [Nat.cast_choose_two]
      push_cast
      ring
    rw [hc]
    have hqr : 0 ≤ q.val ^ r := pow_nonneg q.pos.le r
    have h1 : ((r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) + 2) * ((r : ℝ) + 1) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 hqr
    linarith
  calc q.cubeSeries ≤ _ := hle
    _ ≤ q.val / (1 - q.val) * (2 * (1 / (1 - q.val) ^ (2 + 1))) :=
        mul_le_mul_of_nonneg_left hr2 (div_nonneg q.pos.le hq1.le)
    _ = 2 * q.val / (1 - q.val) ^ 4 := by field_simp

end RealEulerNome

end GaloisForLFunctions.HTGeometry
