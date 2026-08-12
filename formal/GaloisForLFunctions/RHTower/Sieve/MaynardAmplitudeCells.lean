import GaloisForLFunctions.RHTower.Sieve.MaynardPointwiseExclusion
import GaloisForLFunctions.RHTower.Sieve.MaynardFactorTrivial
import GaloisForLFunctions.RHTower.Sieve.MaynardGroupedFactor
import GaloisForLFunctions.RHTower.Sieve.MaynardBoxFactorization
import GaloisForLFunctions.RHTower.Sieve.MaynardLongFactorAbsorption

/-!
# Exact Maynard amplitude coordinates

Maynard's factor exponents are logarithmic coordinates of actual factor magnitudes at one fixed
Perron abscissa.  This file constructs those coordinates and proves their finite-product weighted
mean and deficit-rigidity laws.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped zeta

/-- Exact amplitude exponent of magnitude `V` at length `N` and fixed Perron abscissa `c`. -/
def maynardAmplitude (c N V : ℝ) : ℝ := c + Real.log V / Real.log N

theorem rpow_maynardAmplitude_sub_abscissa
    {c N V : ℝ} (hN : 1 < N) (hV : 0 < V) :
    N ^ (maynardAmplitude c N V - c) = V := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hlogN : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  rw [maynardAmplitude]
  have hexp : c + Real.log V / Real.log N - c =
      Real.log V / Real.log N := by ring
  rw [hexp, Real.rpow_def_of_pos hN0]
  rw [show Real.log N * (Real.log V / Real.log N) = Real.log V by
    field_simp]
  exact Real.exp_log hV

/-- Global amplitude exponent of a positive product at total length `x`. -/
def maynardGlobalAmplitude (c x V : ℝ) : ℝ := maynardAmplitude c x V

theorem rpow_maynardGlobalAmplitude_sub_abscissa
    {c x V : ℝ} (hx : 1 < x) (hV : 0 < V) :
    x ^ (maynardGlobalAmplitude c x V - c) = V := by
  exact rpow_maynardAmplitude_sub_abscissa hx hV

/-- A lower magnitude threshold is exactly a lower bound on the logarithmic amplitude. -/
theorem le_maynardAmplitude_of_rpow_le
    {c N V alpha : ℝ} (hN : 1 < N)
    (hlower : N ^ (alpha - c) ≤ V) :
    alpha ≤ maynardAmplitude c N V := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hleft0 : 0 < N ^ (alpha - c) := Real.rpow_pos_of_pos hN0 _
  have hV : 0 < V := hleft0.trans_le hlower
  have hlogs := Real.log_le_log hleft0 hlower
  rw [Real.log_rpow hN0] at hlogs
  rw [maynardAmplitude]
  have hdiv : alpha - c ≤ Real.log V / Real.log N := by
    rw [le_div_iff₀ hlogN]
    exact hlogs
  linarith

/-- Pointwise upper bounds become upper bounds on the exact logarithmic amplitude coordinate. -/
theorem maynardAmplitude_le_of_pointwise_power_saving
    {c N V C Delta : ℝ} (hN : 1 < N) (hV : 0 < V) (hC : 0 < C)
    (hupper : V ≤ C * N ^ (1 - c) * N ^ (-Delta)) :
    maynardAmplitude c N V ≤
      1 - Delta + Real.log C / Real.log N := by
  refine exponent_le_of_pointwise_power_saving
    (c := c) (α := maynardAmplitude c N V) (δ := Delta) (V := V)
      hN hC ?_ hupper
  have hid := rpow_maynardAmplitude_sub_abscissa (c := c) hN hV
  simpa [sub_eq_add_neg, add_comm] using hid.le

theorem maynardAmplitude_le_one_sub_half_of_pointwise_power_saving
    {c N V C Delta : ℝ} (hN : 1 < N) (hV : 0 < V) (hC : 1 ≤ C)
    (hsize : 2 * Real.log C ≤ Delta * Real.log N)
    (hupper : V ≤ C * N ^ (1 - c) * N ^ (-Delta)) :
    maynardAmplitude c N V ≤ 1 - Delta / 2 := by
  refine exponent_le_one_sub_half_of_pointwise_power_saving
    (c := c) (α := maynardAmplitude c N V) (δ := Delta) (V := V)
      hN hC hsize ?_ hupper
  have hid := rpow_maynardAmplitude_sub_abscissa (c := c) hN hV
  simpa [sub_eq_add_neg, add_comm] using hid.le

/-- Exact harmless amplitude slack of one literal Heath--Brown factor.  Möbius and zeta atoms
have zero slack; the unique logarithm atom pays only `log log(2N) / log N`. -/
def heathBrownFactorAmplitudeSlack (kind : HeathBrownFactorKind) (q : ℕ) : ℝ :=
  match kind with
  | .moebius => 0
  | .zeta => 0
  | .log =>
      Real.log (Real.log (((2 ^ (q + 1) : ℕ) : ℝ))) /
        Real.log (((2 ^ q : ℕ) : ℝ))

theorem heathBrownFactorAmplitudeSlack_nonneg
    (kind : HeathBrownFactorKind) {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ heathBrownFactorAmplitudeSlack kind q := by
  cases kind with
  | moebius => simp [heathBrownFactorAmplitudeSlack]
  | zeta => simp [heathBrownFactorAmplitudeSlack]
  | log =>
      have hN : (1 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < 2 ^ q by
          exact pow_lt_pow_right₀ (by norm_num) hq)
      have htop4 : (4 : ℝ) ≤ ((2 ^ (q + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 4 ≤ 2 ^ (q + 1) by
          calc
            4 = 2 ^ (2 : ℕ) := by norm_num
            _ ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
      have hexp : Real.exp 1 < ((2 ^ (q + 1) : ℕ) : ℝ) :=
        Real.exp_one_lt_three.trans_le (by linarith)
      have hlogTop : 1 < Real.log (((2 ^ (q + 1) : ℕ) : ℝ)) :=
        (Real.lt_log_iff_exp_lt (by positivity)).mpr hexp
      exact div_nonneg (Real.log_nonneg hlogTop.le) (Real.log_nonneg hN.le)

/-- A literal box has exactly one nonzero amplitude slack, so its total logarithmic slack mass is
exactly `log log(2^(q+1))`, independent of packet degree and every Möbius/zeta exponent. -/
theorem sum_heathBrownBoxFactorAmplitudeSlack_mul_log
    {k m q : ℕ} (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ)
    (hq : 1 ≤ q) :
    ∑ i : HeathBrownBoxFactorIndex k m,
        heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k m i)
          (heathBrownBoxFactorExponent a b q i) *
          Real.log (((2 ^ heathBrownBoxFactorExponent a b q i : ℕ) : ℝ)) =
      Real.log (Real.log (((2 ^ (q + 1) : ℕ) : ℝ))) := by
  classical
  have hlogN : Real.log (((2 ^ q : ℕ) : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (show 1 < 2 ^ q by
      exact pow_lt_pow_right₀ (by norm_num) hq)
  have hden : (q : ℝ) * Real.log 2 ≠ 0 := by
    simpa using hlogN
  simp [HeathBrownBoxFactorIndex, heathBrownBoxFactorKind,
    heathBrownBoxFactorExponent, heathBrownFactorAmplitudeSlack]
  exact div_mul_cancel₀ _ hden

/-- `log(8 log T)` is eventually smaller than any positive multiple of `log T`. -/
theorem eventually_log_eight_mul_log_le {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in Filter.atTop,
      Real.log (8 * Real.log T) ≤ eps * Real.log T := by
  have hU : Filter.Tendsto (fun T : ℝ => 8 * Real.log T)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto hU).def
    (show 0 < eps / 8 by positivity)
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 0] with T hs hlog
  have hU0 : 0 ≤ 8 * Real.log T := mul_nonneg (by norm_num) hlog
  change |Real.log (8 * Real.log T)| ≤ (eps / 8) * |8 * Real.log T| at hs
  rw [abs_of_nonneg hU0] at hs
  calc
    Real.log (8 * Real.log T) ≤ |Real.log (8 * Real.log T)| := le_abs_self _
    _ ≤ (eps / 8) * (8 * Real.log T) := hs
    _ = eps * Real.log T := by ring

/-- The exact logarithmic-factor amplitude slack is uniformly `o(log T)` for every Maynard
cutoff `X ≤ T^mu`, uniformly over `mu ≤ 19/9`. -/
theorem eventually_log_maynardLongPolylogEnvelope_le
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
        Real.log (maynardLongPolylogEnvelope X) ≤ eps * Real.log T := by
  filter_upwards [eventually_log_eight_mul_log_le heps,
    Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hsmall hT hlogT
  intro X hX mu hmu hXscale
  have hE := maynardLongPolylogEnvelope_le_eight_log
    hX hT hlogT hmu hXscale
  have hEpos : 0 < maynardLongPolylogEnvelope X :=
    lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
  have hlogT0 : 0 < Real.log T := lt_of_lt_of_le zero_lt_one hlogT
  have hlogE : Real.log (maynardLongPolylogEnvelope X) ≤
      Real.log (8 * Real.log T) := by
    exact Real.log_le_log hEpos hE
  exact hlogE.trans hsmall

theorem log_heathBrown_log_trivialConstant_le_log_polylogEnvelope
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k)
    (hX : 1 ≤ X) (hq : 1 ≤ c.q) :
    Real.log (Real.log (((2 ^ (c.q + 1) : ℕ) : ℝ))) ≤
      Real.log (maynardLongPolylogEnvelope X) := by
  have htop : (1 : ℝ) < ((2 ^ (c.q + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 ^ (c.q + 1) by
      exact one_lt_pow₀ (by norm_num) (by omega))
  have hinner : 0 < Real.log (((2 ^ (c.q + 1) : ℕ) : ℝ)) :=
    Real.log_pos htop
  exact Real.log_le_log hinner
    (heathBrown_log_trivialConstant_le_polylogEnvelope c hX)

/-- Uniform eventual bound for the complete amplitude-slack mass of every literal box. -/
theorem eventually_sum_heathBrownBoxFactorAmplitudeSlack_mul_log_le
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
        ∀ L k : ℕ, ∀ c : HeathBrownBoxChoice L X k, 1 ≤ c.q →
          ∑ i : HeathBrownBoxFactorIndex k c.m,
              heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k c.m i)
                (heathBrownBoxFactorExponent c.a c.b c.q i) *
                Real.log (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ≤
            eps * Real.log T := by
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le heps] with T hT
  intro X hX mu hmu hXscale L k c hq
  rw [sum_heathBrownBoxFactorAmplitudeSlack_mul_log c.a c.b hq]
  exact (log_heathBrown_log_trivialConstant_le_log_polylogEnvelope c hX hq).trans
    (hT X hX mu hmu hXscale)

/-- Every positive literal factor magnitude at fixed abscissa has amplitude at most its exact
trivial cap. -/
theorem maynard_heathBrownFactor_amplitude_le_one_add_slack
    (L X q : ℕ) (kind : HeathBrownFactorKind) {c y : ℝ}
    (hc : 0 ≤ c) (hq : 1 ≤ q)
    (hV : 0 < ‖LSeries (complexCoeff
      (arithmeticDyadicBlock (heathBrownFactorBase L X kind) q))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖) :
    maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
        ‖LSeries (complexCoeff
          (arithmeticDyadicBlock (heathBrownFactorBase L X kind) q))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤
      1 + heathBrownFactorAmplitudeSlack kind q := by
  have hN : (1 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 ^ q by
      exact pow_lt_pow_right₀ (by norm_num) hq)
  cases kind with
  | moebius =>
      change 0 < ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (truncatedMoebius L) q))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ at hV
      change maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
          ‖LSeries (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) q))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ 1 + 0
      have hupper := norm_LSeries_moebiusDyadicBlock_le_rpow L q hc y
      have h := maynardAmplitude_le_of_pointwise_power_saving
        (c := c) hN hV (by norm_num : (0 : ℝ) < 1) (Delta := 0) (C := 1) (by
          simpa using hupper)
      simpa using h
  | zeta =>
      change 0 < ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ at hV
      change maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
          ‖LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ 1 + 0
      have hupper := norm_LSeries_zetaDyadicBlock_le_rpow X q hc y
      have h := maynardAmplitude_le_of_pointwise_power_saving
        (c := c) hN hV (by norm_num : (0 : ℝ) < 1) (Delta := 0) (C := 1) (by
          simpa using hupper)
      simpa using h
  | log =>
      change 0 < ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ at hV
      change maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
          ‖LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤
        1 + Real.log (Real.log (((2 ^ (q + 1) : ℕ) : ℝ))) /
          Real.log (((2 ^ q : ℕ) : ℝ))
      let C : ℝ := Real.log (((2 ^ (q + 1) : ℕ) : ℝ))
      have htop : (1 : ℝ) < ((2 ^ (q + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < 2 ^ (q + 1) by
          exact one_lt_pow₀ (by norm_num) (by omega))
      have hC : 0 < C := Real.log_pos htop
      have hupper := norm_LSeries_logDyadicBlock_le_rpow_mul_log X q hc y
      have h := maynardAmplitude_le_of_pointwise_power_saving
        (c := c) hN hV hC (Delta := 0) (C := C) (by
          dsimp [C]
          simpa [mul_comm] using hupper)
      simpa [C] using h

/-- Exact logarithmic coordinate identity for a finite product. -/
theorem maynardAmplitude_mul_log
    {c N V : ℝ} (hN : 1 < N) :
    maynardAmplitude c N V * Real.log N =
      c * Real.log N + Real.log V := by
  have hlogN : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  rw [maynardAmplitude]
  calc
    (c + Real.log V / Real.log N) * Real.log N =
        c * Real.log N + (Real.log V / Real.log N) * Real.log N := by ring
    _ = c * Real.log N + Real.log V := by rw [div_mul_cancel₀ _ hlogN]

/-- Product amplitudes are the length-logarithmic weighted mean of factor amplitudes. -/
theorem maynardGlobalAmplitude_weighted_mean
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {c x V : ℝ} (N W : ι → ℝ)
    (hN : ∀ i, 1 < N i) (hW : ∀ i, 0 < W i)
    (hx : x = ∏ i, N i) (hV : V = ∏ i, W i) :
    maynardGlobalAmplitude c x V * Real.log x =
      ∑ i, maynardAmplitude c (N i) (W i) * Real.log (N i) := by
  classical
  have hx1 : 1 < x := by
    rw [hx]
    calc
      1 = ∏ _i : ι, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hV0 : 0 < V := by
    rw [hV]
    exact Finset.prod_pos fun i _ => hW i
  rw [maynardGlobalAmplitude, maynardAmplitude_mul_log hx1]
  rw [hx, Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i))),
    hV, Real.log_prod (fun i _ => ne_of_gt (hW i))]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (maynardAmplitude_mul_log (hN i)).symm

/-- Finite-family one-factor rigidity.  If every local amplitude is at most `1`, one factor has
deficit `Delta`, and that factor occupies logarithmic length at least `ell`, then global amplitude
has deficit at least `ell*Delta`. -/
theorem maynard_finite_one_factor_deficit
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {x alpha ell Delta : ℝ} (N a : ι → ℝ) (j : ι)
    (hx : 1 < x) (hN : ∀ i, 1 ≤ N i)
    (hlogTotal : Real.log x = ∑ i, Real.log (N i))
    (hweighted : alpha * Real.log x = ∑ i, a i * Real.log (N i))
    (hDelta : 0 ≤ Delta) (hall : ∀ i, a i ≤ 1)
    (hj : a j ≤ 1 - Delta) (hlength : x ^ ell ≤ N j) :
    alpha ≤ 1 - ell * Delta := by
  classical
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogN : ∀ i, 0 ≤ Real.log (N i) := fun i => Real.log_nonneg (hN i)
  have hlogLength : ell * Real.log x ≤ Real.log (N j) := by
    have hpow0 : 0 < x ^ ell := Real.rpow_pos_of_pos hx0 _
    have h := Real.log_le_log hpow0 hlength
    rwa [Real.log_rpow hx0] at h
  have hterm : ∀ i, a i * Real.log (N i) ≤
      Real.log (N i) - (if i = j then Delta * Real.log (N j) else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      have := mul_le_mul_of_nonneg_right hj (hlogN j)
      simp only [ite_true]
      nlinarith
    · simp only [if_neg hij, sub_zero]
      simpa using mul_le_mul_of_nonneg_right (hall i) (hlogN i)
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hdeltaLength : Delta * (ell * Real.log x) ≤
      Delta * Real.log (N j) := mul_le_mul_of_nonneg_left hlogLength hDelta
  have hgoal : alpha * Real.log x ≤ (1 - ell * Delta) * Real.log x := by
    calc
      alpha * Real.log x = ∑ i, a i * Real.log (N i) := hweighted
      _ ≤ ∑ i, Real.log (N i) - Delta * Real.log (N j) := by
        simpa [Finset.sum_sub_distrib] using hsum
      _ = Real.log x - Delta * Real.log (N j) := by rw [← hlogTotal]
      _ ≤ Real.log x - Delta * (ell * Real.log x) :=
        sub_le_sub_left hdeltaLength _
      _ = (1 - ell * Delta) * Real.log x := by ring
  exact le_of_mul_le_mul_right hgoal hlogx

/-- Exact product version of one-factor rigidity for amplitudes constructed from actual positive
factor magnitudes. -/
theorem maynard_globalAmplitude_one_factor_deficit
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {c ell Delta : ℝ} (N W : ι → ℝ) (j : ι)
    (hN : ∀ i, 1 < N i) (hW : ∀ i, 0 < W i)
    (hDelta : 0 ≤ Delta)
    (hall : ∀ i, maynardAmplitude c (N i) (W i) ≤ 1)
    (hj : maynardAmplitude c (N j) (W j) ≤ 1 - Delta)
    (hlength : (∏ i, N i) ^ ell ≤ N j) :
    maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) ≤
      1 - ell * Delta := by
  classical
  have hx : 1 < ∏ i, N i := by
    calc
      1 = ∏ _i : ι, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hlogTotal : Real.log (∏ i, N i) = ∑ i, Real.log (N i) :=
    Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))
  have hweighted := maynardGlobalAmplitude_weighted_mean (c := c) N W hN hW rfl rfl
  exact maynard_finite_one_factor_deficit N
    (fun i => maynardAmplitude c (N i) (W i)) j hx (fun i => (hN i).le)
      hlogTotal hweighted hDelta hall hj hlength

/-- **Actual-product amplitude exclusion.**  If a product is large at exponent `alpha`, all local
factor amplitudes are at most `1`, and one sufficiently long factor has deficit `Delta`, then the
global large-value exponent itself satisfies `alpha ≤ 1-ell*Delta`.  No amplitude bins or chosen
complement exponent are assumptions. -/
theorem maynard_product_threshold_one_factor_deficit
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {c alpha ell Delta : ℝ} (N W : ι → ℝ) (j : ι)
    (hN : ∀ i, 1 < N i) (hW : ∀ i, 0 < W i)
    (hDelta : 0 ≤ Delta)
    (hall : ∀ i, maynardAmplitude c (N i) (W i) ≤ 1)
    (hj : maynardAmplitude c (N j) (W j) ≤ 1 - Delta)
    (hlength : (∏ i, N i) ^ ell ≤ N j)
    (hlarge : (∏ i, N i) ^ (alpha - c) ≤ ∏ i, W i) :
    alpha ≤ 1 - ell * Delta := by
  classical
  have hx : 1 < ∏ i, N i := by
    calc
      1 = ∏ _i : ι, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hglobal : alpha ≤ maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) :=
    le_maynardAmplitude_of_rpow_le hx hlarge
  exact hglobal.trans
    (maynard_globalAmplitude_one_factor_deficit N W j hN hW hDelta hall hj hlength)

/-- One-factor rigidity with a uniform harmless local slack.  The exact surviving global deficit
is `ell*Delta - (1-ell)*eps`: slack on the distinguished factor is not paid twice. -/
theorem maynard_finite_one_factor_deficit_with_slack
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {x alpha ell Delta eps : ℝ} (N a : ι → ℝ) (j : ι)
    (hx : 1 < x) (hN : ∀ i, 1 ≤ N i)
    (hlogTotal : Real.log x = ∑ i, Real.log (N i))
    (hweighted : alpha * Real.log x = ∑ i, a i * Real.log (N i))
    (hDelta : 0 ≤ Delta) (heps : 0 ≤ eps)
    (hall : ∀ i, a i ≤ 1 + eps)
    (hj : a j ≤ 1 - Delta) (hlength : x ^ ell ≤ N j) :
    alpha ≤ 1 - (ell * Delta - (1 - ell) * eps) := by
  classical
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogN : ∀ i, 0 ≤ Real.log (N i) := fun i => Real.log_nonneg (hN i)
  have hlogLength : ell * Real.log x ≤ Real.log (N j) := by
    have hpow0 : 0 < x ^ ell := Real.rpow_pos_of_pos hx0 _
    have h := Real.log_le_log hpow0 hlength
    rwa [Real.log_rpow hx0] at h
  have hterm : ∀ i, a i * Real.log (N i) ≤
      (1 + eps) * Real.log (N i) -
        (if i = j then (Delta + eps) * Real.log (N j) else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      have hmul := mul_le_mul_of_nonneg_right hj (hlogN j)
      simp only [ite_true]
      nlinarith
    · simp only [if_neg hij, sub_zero]
      exact mul_le_mul_of_nonneg_right (hall i) (hlogN i)
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hde : 0 ≤ Delta + eps := add_nonneg hDelta heps
  have hdeltaLength : (Delta + eps) * (ell * Real.log x) ≤
      (Delta + eps) * Real.log (N j) :=
    mul_le_mul_of_nonneg_left hlogLength hde
  have hgoal : alpha * Real.log x ≤
      (1 - (ell * Delta - (1 - ell) * eps)) * Real.log x := by
    calc
      alpha * Real.log x = ∑ i, a i * Real.log (N i) := hweighted
      _ ≤ (1 + eps) * (∑ i, Real.log (N i)) -
          (Delta + eps) * Real.log (N j) := by
        simpa [Finset.mul_sum, Finset.sum_sub_distrib] using hsum
      _ = (1 + eps) * Real.log x -
          (Delta + eps) * Real.log (N j) := by rw [← hlogTotal]
      _ ≤ (1 + eps) * Real.log x -
          (Delta + eps) * (ell * Real.log x) :=
        sub_le_sub_left hdeltaLength _
      _ = (1 - (ell * Delta - (1 - ell) * eps)) * Real.log x := by ring
  exact le_of_mul_le_mul_right hgoal hlogx

/-- Actual-product threshold form of the slack-rigidity law. -/
theorem maynard_product_threshold_one_factor_deficit_with_slack
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {c alpha ell Delta eps : ℝ} (N W : ι → ℝ) (j : ι)
    (hN : ∀ i, 1 < N i) (hW : ∀ i, 0 < W i)
    (hDelta : 0 ≤ Delta) (heps : 0 ≤ eps)
    (hall : ∀ i, maynardAmplitude c (N i) (W i) ≤ 1 + eps)
    (hj : maynardAmplitude c (N j) (W j) ≤ 1 - Delta)
    (hlength : (∏ i, N i) ^ ell ≤ N j)
    (hlarge : (∏ i, N i) ^ (alpha - c) ≤ ∏ i, W i) :
    alpha ≤ 1 - (ell * Delta - (1 - ell) * eps) := by
  classical
  have hx : 1 < ∏ i, N i := by
    calc
      1 = ∏ _i : ι, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hlogTotal : Real.log (∏ i, N i) = ∑ i, Real.log (N i) :=
    Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))
  have hweighted := maynardGlobalAmplitude_weighted_mean (c := c) N W hN hW rfl rfl
  have hglobal : alpha ≤ maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) :=
    le_maynardAmplitude_of_rpow_le hx hlarge
  exact hglobal.trans
    (maynard_finite_one_factor_deficit_with_slack N
      (fun i => maynardAmplitude c (N i) (W i)) j hx (fun i => (hN i).le)
        hlogTotal hweighted hDelta heps hall hj hlength)

/-- Finite one-factor rigidity with nonuniform local amplitude slacks.  Only their exact
length-logarithmic mass matters. -/
theorem maynard_finite_one_factor_deficit_with_log_slack
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {x alpha ell Delta E : ℝ} (N a slack : ι → ℝ) (j : ι)
    (hx : 1 < x) (hN : ∀ i, 1 ≤ N i)
    (hlogTotal : Real.log x = ∑ i, Real.log (N i))
    (hweighted : alpha * Real.log x = ∑ i, a i * Real.log (N i))
    (hDelta : 0 ≤ Delta) (hslack : ∀ i, 0 ≤ slack i)
    (hall : ∀ i, a i ≤ 1 + slack i)
    (hj : a j ≤ 1 - Delta) (hlength : x ^ ell ≤ N j)
    (hslackMass : ∑ i, slack i * Real.log (N i) ≤ E * Real.log x) :
    alpha ≤ 1 - (ell * Delta - E) := by
  classical
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogN : ∀ i, 0 ≤ Real.log (N i) := fun i => Real.log_nonneg (hN i)
  have hlogLength : ell * Real.log x ≤ Real.log (N j) := by
    have hpow0 : 0 < x ^ ell := Real.rpow_pos_of_pos hx0 _
    have h := Real.log_le_log hpow0 hlength
    rwa [Real.log_rpow hx0] at h
  have hterm : ∀ i, a i * Real.log (N i) ≤
      Real.log (N i) + slack i * Real.log (N i) -
        (if i = j then Delta * Real.log (N j) else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      have hmul := mul_le_mul_of_nonneg_right hj (hlogN j)
      have hslackTerm : 0 ≤ slack j * Real.log (N j) :=
        mul_nonneg (hslack j) (hlogN j)
      simp only [ite_true]
      nlinarith
    · simp only [if_neg hij, sub_zero]
      have hmul := mul_le_mul_of_nonneg_right (hall i) (hlogN i)
      nlinarith
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hdeltaLength : Delta * (ell * Real.log x) ≤
      Delta * Real.log (N j) := mul_le_mul_of_nonneg_left hlogLength hDelta
  have hgoal : alpha * Real.log x ≤
      (1 - (ell * Delta - E)) * Real.log x := by
    calc
      alpha * Real.log x = ∑ i, a i * Real.log (N i) := hweighted
      _ ≤ (∑ i, Real.log (N i)) +
          (∑ i, slack i * Real.log (N i)) - Delta * Real.log (N j) := by
        simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib] using hsum
      _ ≤ Real.log x + E * Real.log x - Delta * Real.log (N j) := by
        rw [← hlogTotal]
        linarith
      _ ≤ Real.log x + E * Real.log x - Delta * (ell * Real.log x) :=
        sub_le_sub_left hdeltaLength _
      _ = (1 - (ell * Delta - E)) * Real.log x := by ring
  exact le_of_mul_le_mul_right hgoal hlogx

/-- Actual-product threshold form of nonuniform log-slack rigidity. -/
theorem maynard_product_threshold_one_factor_deficit_with_log_slack
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {c alpha ell Delta E : ℝ} (N W slack : ι → ℝ) (j : ι)
    (hN : ∀ i, 1 < N i) (hW : ∀ i, 0 < W i)
    (hDelta : 0 ≤ Delta) (hslack : ∀ i, 0 ≤ slack i)
    (hall : ∀ i, maynardAmplitude c (N i) (W i) ≤ 1 + slack i)
    (hj : maynardAmplitude c (N j) (W j) ≤ 1 - Delta)
    (hlength : (∏ i, N i) ^ ell ≤ N j)
    (hslackMass : ∑ i, slack i * Real.log (N i) ≤
      E * Real.log (∏ i, N i))
    (hlarge : (∏ i, N i) ^ (alpha - c) ≤ ∏ i, W i) :
    alpha ≤ 1 - (ell * Delta - E) := by
  classical
  have hx : 1 < ∏ i, N i := by
    calc
      1 = ∏ _i : ι, (1 : ℝ) := by simp
      _ < ∏ i, N i := Finset.prod_lt_prod_of_nonempty
        (fun _i _hi => by norm_num) (fun i _hi => hN i) Finset.univ_nonempty
  have hlogTotal : Real.log (∏ i, N i) = ∑ i, Real.log (N i) :=
    Real.log_prod (fun i _ => ne_of_gt (lt_trans zero_lt_one (hN i)))
  have hweighted := maynardGlobalAmplitude_weighted_mean (c := c) N W hN hW rfl rfl
  have hglobal : alpha ≤ maynardGlobalAmplitude c (∏ i, N i) (∏ i, W i) :=
    le_maynardAmplitude_of_rpow_le hx hlarge
  exact hglobal.trans
    (maynard_finite_one_factor_deficit_with_log_slack N
      (fun i => maynardAmplitude c (N i) (W i)) slack j hx
        (fun i => (hN i).le) hlogTotal hweighted hDelta hslack hall hj hlength hslackMass)

/-- **Literal Heath--Brown box amplitude exclusion.**  This is the concrete bridge from an actual
large box core at fixed Perron abscissa to a global Maynard exponent deficit.  Factor amplitudes,
trivial caps, unique logarithmic slack, and product normalization are all constructed internally. -/
theorem maynard_heathBrownBox_threshold_one_factor_deficit
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    {c y alpha ell Delta E : ℝ}
    (hc : 0 ≤ c)
    (hqpos : ∀ i : HeathBrownBoxFactorIndex k box.m,
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i)
    (hDelta : 0 ≤ Delta)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hj : maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖LSeries (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (heathBrownBoxFactorKind k box.m j))
          (heathBrownBoxFactorExponent box.a box.b box.q j)))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ 1 - Delta)
    (hlength :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ ell ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        E * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ))
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖) :
    alpha ≤ 1 - (ell * Delta - E) := by
  classical
  let I := HeathBrownBoxFactorIndex k box.m
  let q : I → ℕ := heathBrownBoxFactorExponent box.a box.b box.q
  let kind : I → HeathBrownFactorKind := heathBrownBoxFactorKind k box.m
  let N : I → ℝ := fun i => (((2 ^ q i : ℕ) : ℝ))
  let Z : I → ℂ := fun i => LSeries (complexCoeff
    (arithmeticDyadicBlock (heathBrownFactorBase L X (kind i)) (q i)))
      ((c : ℂ) + (y : ℝ) * Complex.I)
  let W : I → ℝ := fun i => ‖Z i‖
  let slack : I → ℝ := fun i => heathBrownFactorAmplitudeSlack (kind i) (q i)
  have hN : ∀ i, 1 < N i := by
    intro i
    dsimp [N, q]
    exact_mod_cast (show 1 < 2 ^ heathBrownBoxFactorExponent box.a box.b box.q i by
      exact pow_lt_pow_right₀ (by norm_num) (hqpos i))
  have hNprod : (∏ i, N i) =
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    change (∏ i : I, (((2 ^ q i : ℕ) : ℝ))) =
      (((∏ i : I, 2 ^ q i) : ℕ) : ℝ)
    norm_cast
  have hZprod : (∏ i, Z i) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((c : ℂ) + (y : ℝ) * Complex.I) := by
    simpa [Z, q, kind, I] using heathBrownBoxFactorProduct_eq_core
      L X k box.m box.a box.b box.q ((c : ℂ) + (y : ℝ) * Complex.I)
  have hWprod : (∏ i, W i) =
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
    rw [← hZprod]
    simp [W]
  have hNprodPos : 0 < ∏ i, N i := Finset.prod_pos fun i _ => (hN i).trans' zero_lt_one
  have hthreshold : 0 < (∏ i, N i) ^ (alpha - c) :=
    Real.rpow_pos_of_pos hNprodPos _
  have hWprodPos : 0 < ∏ i, W i := by
    rw [hWprod]
    exact hthreshold.trans_le (by simpa [hNprod] using hlarge)
  have hW : ∀ i, 0 < W i := by
    intro i
    by_contra hi
    have hi0 : W i = 0 := le_antisymm (le_of_not_gt hi) (norm_nonneg _)
    have hzero : ∏ r, W r = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi0
    rw [hzero] at hWprodPos
    exact (lt_irrefl 0) hWprodPos
  have hslack : ∀ i, 0 ≤ slack i := by
    intro i
    exact heathBrownFactorAmplitudeSlack_nonneg (kind i) (hqpos i)
  have hall : ∀ i, maynardAmplitude c (N i) (W i) ≤ 1 + slack i := by
    intro i
    exact maynard_heathBrownFactor_amplitude_le_one_add_slack
      L X (q i) (kind i) hc (hqpos i) (hW i)
  apply maynard_product_threshold_one_factor_deficit_with_log_slack
    N W slack j hN hW hDelta hslack hall
  · simpa [N, W, Z, q, kind] using hj
  · rw [hNprod]
    simpa only [N, q] using hlength
  · rw [hNprod]
    simpa only [N, q, kind, slack] using hslackMass
  · rw [hNprod, hWprod]
    exact hlarge

end RHTower.Sieve
