import GaloisForLFunctions.HTGeometry.PrimeHodgeGammaProjectiveConnection
import GaloisForLFunctions.HTGeometry.PrimeGammaRelativeModularTransport
import GaloisForLFunctions.HTGeometry.PrimeHodgeSteinGramian
import GaloisForLFunctions.HTGeometry.HodgeSurvivalShiftDynamics
import GaloisForLFunctions.HTGeometry.CfcEigenvectorRankOneAssembly
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCompletedXiHellingerGammaGradedVerticalObstruction
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift

/-!
# The Gamma-residue regrading of the prime–Hodge history metric

* The aperture curvature `κ_n ~ 3/(4n²)` and the history tails `m_n ~ 105/(8n³)` are summable,
  while the double-log sequence `3/(n log n)` is not; neither differs from a nonzero multiple of
  it by a summable sequence.
* **Theorem PPTI-I (PPTI.53)–(PPTI.55).**  The completed Hellinger–Gamma vertex
  `v_n(a,x) = η_n (e^{aL(n+1)} x, e^{-aL(n+1)} x)`, `η_n = 1/(2n)!`, `L = log p + log q`, has
  two-channel energy `η_n² · 2cosh(2aL(n+1)) ‖x‖²`, and its energy in the inverse history metric
  `Φ^{-1} = diag(1/w_n)` still tends to zero.
* **(PPTI.56)–(PPTI.57).**  The Gamma-residue metric `G_Γ = diag(η_n²)` is positive, nuclear and
  faithful; it is the continuous functional calculus `f_Γ(Φ)` of the history marginal for a
  continuous `f_Γ` with `f_Γ(0) = 0`, `f_Γ(w_n) = η_n²`, and every function continuous on the
  spectrum with these values gives the same operator and vanishes at `0`.  The normalized prime
  extension `Z⁻¹ G_Γ ⊗ A_d` is positive, prime-mixed, nuclear with trace one.
* **(PPTI.58).**  In the inverse Gamma metric the vertex energy is `2Z cosh(2aL(n+1)) ‖x‖²`:
  constant `2Z‖x‖²` at `a = 0` and divergent for every `a ≠ 0`.
-/

open Real Filter Topology Set ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower
open _root_.RHTower.PrimitivePromotedHellingerGammaPureHodgeCoface
open _root_.RHTower.CompletedXiHellingerGammaPureHodgeCoface

/-! ## Summability and the double-log comparison -/

theorem apertureCurvature_le (n : ℕ) : apertureCurvature n ≤ 3 / ((n : ℝ) + 1) ^ 2 := by
  rw [apertureCurvature_eq]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem summable_apertureCurvature : Summable apertureCurvature := by
  have h : Summable fun n : ℕ => 3 / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using this.mul_left 3
  exact h.of_nonneg_of_le (fun n => (apertureCurvature_pos n).le) apertureCurvature_le

theorem tendsto_sq_mul_apertureCurvature :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * apertureCurvature n) atTop (𝓝 (3 / 4)) := by
  have h3 : Tendsto (fun n : ℕ => (3 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 3
  have h5 : Tendsto (fun n : ℕ => (5 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 5
  have h := ((tendsto_const_nhds (x := (2 : ℝ))).add h3).mul
    ((tendsto_const_nhds (x := (2 : ℝ))).add h5)
  have h' : Tendsto (fun n : ℕ => (3 : ℝ) / ((2 + 3 / (n : ℝ)) * (2 + 5 / (n : ℝ)))) atTop
      (𝓝 (3 / ((2 + 0) * (2 + 0)))) :=
    (tendsto_const_nhds (x := (3 : ℝ))).div h (by norm_num)
  rw [show (3 : ℝ) / ((2 + 0) * (2 + 0)) = 3 / 4 by norm_num] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [apertureCurvature_eq]
  field_simp

theorem tendsto_cube_mul_historyTail :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * PrimeHodgeHistory.m n) atTop (𝓝 (105 / 8)) := by
  have hk : ∀ k : ℝ, Tendsto (fun n : ℕ => k / (n : ℝ)) atTop (𝓝 0) := fun k =>
    tendsto_const_div_atTop_nhds_zero_nat k
  have h := (((tendsto_const_nhds (x := (2 : ℝ))).add (hk 3)).mul
    ((tendsto_const_nhds (x := (2 : ℝ))).add (hk 5))).mul
    ((tendsto_const_nhds (x := (2 : ℝ))).add (hk 7))
  have h' : Tendsto (fun n : ℕ => (105 : ℝ) /
      ((2 + 3 / (n : ℝ)) * (2 + 5 / (n : ℝ)) * (2 + 7 / (n : ℝ)))) atTop
      (𝓝 (105 / ((2 + 0) * (2 + 0) * (2 + 0)))) :=
    (tendsto_const_nhds (x := (105 : ℝ))).div h (by norm_num)
  rw [show (105 : ℝ) / ((2 + 0) * (2 + 0) * (2 + 0)) = 105 / 8 by norm_num] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [historyTail_eq]
  field_simp

/-- The double-log transgression sequence `3/(n log n)`, indexed from `n = 2`. -/
def doubleLogTransgression (n : ℕ) : ℝ := 3 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2))

/-- `1/(x log x)` at `x = max n 2`. -/
def condensedDoubleLog (n : ℕ) : ℝ :=
  1 / ((max (n : ℝ) 2) * Real.log (max (n : ℝ) 2))

theorem condensedDoubleLog_pos (n : ℕ) : 0 < condensedDoubleLog n := by
  have h2 : (2 : ℝ) ≤ max (n : ℝ) 2 := le_max_right _ _
  have hlog : 0 < Real.log (max (n : ℝ) 2) := Real.log_pos (by linarith)
  exact one_div_pos.2 (mul_pos (by linarith) hlog)

theorem condensedDoubleLog_anti {m n : ℕ} (hmn : m ≤ n) :
    condensedDoubleLog n ≤ condensedDoubleLog m := by
  have h2 : (2 : ℝ) ≤ max (m : ℝ) 2 := le_max_right _ _
  have hle : max (m : ℝ) 2 ≤ max (n : ℝ) 2 := max_le_max (by exact_mod_cast hmn) le_rfl
  have hlogm : 0 < Real.log (max (m : ℝ) 2) := Real.log_pos (by linarith)
  have hlogle : Real.log (max (m : ℝ) 2) ≤ Real.log (max (n : ℝ) 2) :=
    Real.log_le_log (by linarith) hle
  apply one_div_le_one_div_of_le (mul_pos (by linarith) hlogm)
  exact mul_le_mul hle hlogle hlogm.le (by linarith)

theorem not_summable_condensedDoubleLog : ¬ Summable condensedDoubleLog := by
  rw [← summable_condensed_iff_of_nonneg (fun n => (condensedDoubleLog_pos n).le)
    (fun m n _ hmn => condensedDoubleLog_anti hmn)]
  intro hs
  have hs1 := (summable_nat_add_iff 1).2 hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hharm : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    refine (hs1.mul_left (Real.log 2)).congr fun k => ?_
    have hk : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hmax : max (((2 ^ (k + 1) : ℕ) : ℝ)) 2 = (2 : ℝ) ^ (k + 1) := by
      push_cast
      exact max_eq_left hk
    rw [condensedDoubleLog, hmax, Real.log_pow]
    have hp : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    push_cast
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 (by
    simpa [Nat.cast_add, Nat.cast_one] using hharm))

/-- The double-log sequence `3/(n log n)` is not summable. -/
theorem not_summable_doubleLogTransgression : ¬ Summable doubleLogTransgression := by
  intro hs
  refine not_summable_condensedDoubleLog ((summable_nat_add_iff 2).1 ?_)
  refine (hs.div_const 3).congr fun n => ?_
  have hmax : max (((n + 2 : ℕ) : ℝ)) 2 = (n : ℝ) + 2 := by
    push_cast
    exact max_eq_left (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  rw [doubleLogTransgression, condensedDoubleLog, hmax]
  ring

/-- **The false bridge.**  A summable sequence cannot differ from a nonzero multiple of the
double-log transgression by a summable sequence. -/
theorem not_summable_sub_doubleLogTransgression {u : ℕ → ℝ} (hu : Summable u) {c : ℝ}
    (hc : c ≠ 0) : ¬ Summable fun n => u n - c * doubleLogTransgression n := by
  intro h
  refine not_summable_doubleLogTransgression ?_
  have := (hu.sub h).mul_left c⁻¹
  refine this.congr fun n => ?_
  field_simp
  ring

/-! ## The completed Hellinger–Gamma vertex in the history metrics -/

/-- `L_{pq} = log p + log q`. -/
def pairClockLength (p q : Nat.Primes) : ℝ := Real.log (p : ℝ) + Real.log (q : ℝ)

theorem pairClockLength_pos (p q : Nat.Primes) : 0 < pairClockLength p q :=
  add_pos (Real.log_pos (by exact_mod_cast p.prop.one_lt))
    (Real.log_pos (by exact_mod_cast q.prop.one_lt))

/-- **(PPTI.54), scalar form.**  The gauged modular coefficient is
`η_n e^{-a L_{pq}(n+1)}`. -/
theorem hellingerGammaGaugedModularCoefficient_eq (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    hellingerGammaGaugedModularCoefficient a p q n =
      hellingerEvenGammaResidueGauge n * Real.exp (-(a * pairClockLength p q * ((n : ℝ) + 1))) := by
  rw [hellingerGammaGaugedModularCoefficient, xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight, xiGammaEulerBoundaryHalfHeight,
    xiGammaEulerBoundaryHalfHeight, pairClockLength]
  congr 2
  ring

theorem abs_add_one_le_two_mul_cosh (y : ℝ) : |y| + 1 ≤ 2 * Real.cosh y := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 := Real.add_one_le_exp |y|
  have h2 := Real.exp_pos (-|y|)
  linarith

theorem historyFlux_tendsto_zero : Tendsto PrimeHodgeHistory.w atTop (𝓝 0) :=
  squeeze_zero (fun n => (PrimeHodgeHistory.w_pos n).le)
    (fun n => by
      rw [PrimeHodgeHistory.w]
      linarith [(PrimeHodgeHistory.m_pos (n + 1))]) PrimeHodgeHistory.m_tendsto_zero

/-- The two-channel (Hilbert) energy `‖z₁‖² + ‖z₂‖²` of a pair. -/
def channelEnergy {X : Type*} [NormedAddCommGroup X] (z : X × X) : ℝ := ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

theorem hellingerEvenGammaResidueGauge_pos (n : ℕ) : 0 < hellingerEvenGammaResidueGauge n := by
  unfold hellingerEvenGammaResidueGauge
  positivity

/-- **(PPTI.54).**  `‖v_n(a,x)‖² = η_n² · 2cosh(2aL(n+1)) ‖x‖²`. -/
theorem channelEnergy_balancedPrimitive {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    channelEnergy (hellingerGammaCompletedBalancedPrimitive hpq a n x) =
      hellingerEvenGammaResidueGauge n ^ 2 *
        (2 * Real.cosh (2 * a * pairClockLength p q * ((n : ℝ) + 1))) * ‖x‖ ^ 2 := by
  rw [channelEnergy, hellingerGammaCompletedBalancedPrimitive]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [hellingerGammaGaugedModularCoefficient_eq, hellingerGammaGaugedModularCoefficient_eq,
    abs_of_pos (mul_pos (hellingerEvenGammaResidueGauge_pos n) (Real.exp_pos _)),
    abs_of_pos (mul_pos (hellingerEvenGammaResidueGauge_pos n) (Real.exp_pos _)), Real.cosh_eq]
  have e1 : Real.exp (-(-a * pairClockLength p q * ((n : ℝ) + 1))) ^ 2 =
      Real.exp (2 * a * pairClockLength p q * ((n : ℝ) + 1)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e2 : Real.exp (-(a * pairClockLength p q * ((n : ℝ) + 1))) ^ 2 =
      Real.exp (-(2 * a * pairClockLength p q * ((n : ℝ) + 1))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, mul_pow, mul_pow, e1, e2]
  ring

theorem two_mul_add_nine_le_pow (n : ℕ) : 2 * (n : ℝ) + 9 ≤ 9 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    push_cast
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith

/-- **Theorem PPTI-I (PPTI.55).**  The completed vertices still collapse in the inverse history
metric: `‖Φ^{-1/2} v_n(a,x)‖² = ‖v_n(a,x)‖²/w_n → 0`. -/
theorem tendsto_steinInverseEnergy_balancedPrimitive {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    Tendsto (fun n : ℕ => channelEnergy (hellingerGammaCompletedBalancedPrimitive hpq a n x) /
      PrimeHodgeHistory.w n) atTop (𝓝 0) := by
  set B := Real.exp (2 * |a| * pairClockLength p q)
  have hB : 0 < B := Real.exp_pos _
  set K : ℝ := 2 * B * 9 ^ 4 / 630 * ‖x‖ ^ 2
  have hmaj : Tendsto (fun n : ℕ => K * ((B * 16) ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (B * 16)).const_mul K
    rwa [mul_zero] at this
  refine squeeze_zero (fun n => div_nonneg (by rw [channelEnergy]; positivity)
    (PrimeHodgeHistory.w_pos n).le) (fun n => ?_) hmaj
  rw [channelEnergy_balancedPrimitive, PrimeHodgeHistory.w_formula]
  push_cast
  have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos n)
  have hη : hellingerEvenGammaResidueGauge n ≤ 1 / (n.factorial : ℝ) := by
    unfold hellingerEvenGammaResidueGauge
    rw [one_div]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (by omega))
  have hη0 := hellingerEvenGammaResidueGauge_pos n
  have hcosh : 2 * Real.cosh (2 * a * pairClockLength p q * ((n : ℝ) + 1)) ≤ 2 * (B * B ^ n) := by
    have h1 : Real.cosh (2 * a * pairClockLength p q * ((n : ℝ) + 1)) ≤
        Real.exp |2 * a * pairClockLength p q * ((n : ℝ) + 1)| := cosh_le_exp_abs _
    have h2 : |2 * a * pairClockLength p q * ((n : ℝ) + 1)| =
        2 * |a| * pairClockLength p q * ((n : ℝ) + 1) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pairClockLength_pos p q),
        abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity), abs_two]
    have h3 : Real.exp (2 * |a| * pairClockLength p q * ((n : ℝ) + 1)) = B * B ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [h2, h3] at h1
    linarith
  have hpoly : (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7) * (2 * (n : ℝ) + 9) ≤
      9 ^ 4 * 16 ^ n := by
    have h9 := two_mul_add_nine_le_pow n
    have h16 : (16 : ℝ) ^ n = (2 ^ n) ^ 4 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h16]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7) * (2 * (n : ℝ) + 9)
        ≤ (2 * (n : ℝ) + 9) ^ 4 := by
          rw [pow_succ, pow_succ, pow_succ, pow_one]
          gcongr <;> linarith
      _ ≤ (9 * 2 ^ n) ^ 4 := by gcongr
      _ = 9 ^ 4 * (2 ^ n) ^ 4 := by ring
  have hx := sq_nonneg ‖x‖
  rw [div_div_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 630)]
  have hfacpos : (0 : ℝ) < n.factorial := by positivity
  have hη2 : hellingerEvenGammaResidueGauge n ^ 2 ≤ 1 / (n.factorial : ℝ) := by
    calc hellingerEvenGammaResidueGauge n ^ 2 ≤ (1 / (n.factorial : ℝ)) ^ 2 := by
          gcongr
      _ ≤ 1 / (n.factorial : ℝ) := by
          rw [one_div, inv_pow]
          exact inv_anti₀ hfacpos (by nlinarith)
  calc hellingerEvenGammaResidueGauge n ^ 2 *
        (2 * Real.cosh (2 * a * pairClockLength p q * ((n : ℝ) + 1))) * ‖x‖ ^ 2 *
        ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7) * (2 * (n : ℝ) + 9))
      ≤ (1 / (n.factorial : ℝ)) * (2 * (B * B ^ n)) * ‖x‖ ^ 2 * (9 ^ 4 * 16 ^ n) := by
        gcongr
    _ = K * ((B * 16) ^ n / (n.factorial : ℝ)) * 630 := by
        simp only [K]
        rw [mul_pow]
        field_simp

/-! ## The Gamma-residue metric -/

/-- The Gamma-residue weight `η_n = 1/(2n)!` as a scalar. -/
def gammaResidueWeight (n : ℕ) : ℂ := ((hellingerEvenGammaResidueGauge n : ℝ) : ℂ)

theorem norm_gammaResidueWeight_sq (n : ℕ) :
    ‖gammaResidueWeight n‖ ^ 2 = hellingerEvenGammaResidueGauge n ^ 2 := by
  rw [gammaResidueWeight, Complex.norm_real, Real.norm_of_nonneg
    (hellingerEvenGammaResidueGauge_pos n).le]

theorem summable_gammaResidueGauge_sq : Summable fun n => hellingerEvenGammaResidueGauge n ^ 2 := by
  refine (Real.summable_pow_div_factorial 1).of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
  rw [one_pow]
  have hfacpos : (0 : ℝ) < n.factorial := by positivity
  have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos n)
  have hη : hellingerEvenGammaResidueGauge n ≤ 1 / (n.factorial : ℝ) := by
    unfold hellingerEvenGammaResidueGauge
    rw [one_div]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.factorial_le (by omega))
  have hη0 := (hellingerEvenGammaResidueGauge_pos n).le
  have h1 : hellingerEvenGammaResidueGauge n ≤ 1 := hη.trans (by
    rw [one_div]; exact inv_le_one_of_one_le₀ hfac)
  nlinarith

theorem summable_norm_gammaResidueWeight_sq : Summable fun n => ‖gammaResidueWeight n‖ ^ 2 := by
  simp_rw [norm_gammaResidueWeight_sq]
  exact summable_gammaResidueGauge_sq

/-- **(PPTI.56).**  The Gamma-residue metric `G_Γ = diag(η_n²)`. -/
def gammaResidueMetric : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  recordOp (E := ℂ) gammaResidueWeight summable_norm_gammaResidueWeight_sq

/-- The Gamma-residue mass `Z = ∑ η_n²`. -/
def gammaResidueMass : ℝ := ∑' n, hellingerEvenGammaResidueGauge n ^ 2

theorem gammaResidueMass_pos : 0 < gammaResidueMass :=
  summable_gammaResidueGauge_sq.tsum_pos (fun _ => sq_nonneg _) 0
    (pow_pos (hellingerEvenGammaResidueGauge_pos 0) 2)

theorem gammaResidueMetric_apply (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    gammaResidueMetric f n = ((hellingerEvenGammaResidueGauge n ^ 2 : ℝ) : ℂ) * f n := by
  rw [gammaResidueMetric, recordOp_apply, gammaResidueWeight, RCLike.inner_apply,
    Complex.conj_ofReal, smul_eq_mul]
  push_cast
  ring

/-- **(PPTI.56).**  `G_Γ` is positive, nuclear with trace `Z`, and has trivial kernel. -/
theorem gammaResidueMetric_properties :
    gammaResidueMetric.IsPositive ∧ MemSchattenClass 1 gammaResidueMetric ∧
      gammaResidueMetric.opTrace = (gammaResidueMass : ℂ) ∧
      Function.Injective gammaResidueMetric := by
  obtain ⟨h1, h2, h3⟩ := recordOp_traceClass (E := ℂ) gammaResidueWeight
    summable_norm_gammaResidueWeight_sq
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [gammaResidueMetric, h3, gammaResidueMass]
    simp_rw [norm_gammaResidueWeight_sq]
  · refine (injective_iff_map_eq_zero _).2 fun f hf => lp.ext (funext fun n => ?_)
    have hn := congrArg (fun g : lp (fun _ : ℕ => ℂ) 2 => g n) hf
    simp only [gammaResidueMetric_apply, lp.coeFn_zero, Pi.zero_apply] at hn
    rw [lp.coeFn_zero, Pi.zero_apply]
    exact (mul_eq_zero.1 hn).resolve_left (Complex.ofReal_ne_zero.2
      (pow_pos (hellingerEvenGammaResidueGauge_pos n) 2).ne')

theorem gammaResidueMetric_basis (n : ℕ) :
    gammaResidueMetric (historyCoord n) =
      ((hellingerEvenGammaResidueGauge n ^ 2 : ℝ) : ℂ) • historyCoord n := by
  refine lp.ext (funext fun k => ?_)
  rw [gammaResidueMetric_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, historyCoord_eq,
    lp.single_apply]
  by_cases h : k = n
  · subst h
    simp
  · simp [h]

/-! ## The regrading as functional calculus of the history marginal -/

/-- The real continuous functional calculus of self-adjoint operators on `ℓ²(ℕ)`; instance search
does not find it unaided on this concrete space. -/
instance ellTwoNatSelfAdjointCFC :
    ContinuousFunctionalCalculus ℝ (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
      IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

theorem w_strictAnti : StrictAnti PrimeHodgeHistory.w := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  rw [PrimeHodgeHistory.w_formula, PrimeHodgeHistory.w_formula]
  push_cast
  apply div_lt_div_of_pos_left (by norm_num) (by positivity)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (2 * ((n : ℝ) + 1) + 3) * (2 * ((n : ℝ) + 1) + 5) * (2 * ((n : ℝ) + 1) + 7) *
      (2 * ((n : ℝ) + 1) + 9) - (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7) *
        (2 * (n : ℝ) + 9) = 8 * ((2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7) * (2 * (n : ℝ) + 9)) := by
    ring
  have : 0 < 8 * ((2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7) * (2 * (n : ℝ) + 9)) := by positivity
  linarith

theorem w_mem_spectrum (n : ℕ) : PrimeHodgeHistory.w n ∈ spectrum ℝ steinIncidence :=
  mem_spectrum_of_eigenvector steinIncidence (steinIncidence_basis n) (historyCoord.orthonormal.ne_zero n)

theorem zero_mem_spectrum_steinIncidence : (0 : ℝ) ∈ spectrum ℝ steinIncidence :=
  (spectrum.isClosed steinIncidence).mem_of_tendsto historyFlux_tendsto_zero
    (Eventually.of_forall w_mem_spectrum)

theorem isSelfAdjoint_steinIncidence : IsSelfAdjoint steinIncidence :=
  steinIncidence_nuclear.1.isSelfAdjoint

/-- **(PPTI.57).**  Every function continuous on the spectrum of `Φ` with `f(w_n) = η_n²` gives
`f(Φ) = G_Γ`. -/
theorem cfc_steinIncidence_eq_gammaResidueMetric {f : ℝ → ℝ}
    (hf : ContinuousOn f (spectrum ℝ steinIncidence))
    (hfw : ∀ n, f (PrimeHodgeHistory.w n) = hellingerEvenGammaResidueGauge n ^ 2) :
    cfc f steinIncidence = gammaResidueMetric := by
  refine ContinuousLinearMap.ext_on (dense_span_lp_single (ι := ℕ)
    |> Submodule.dense_iff_topologicalClosure_eq_top.2) ?_
  rintro _ ⟨n, rfl⟩
  have h := cfc_apply_eigenvector_rankOne steinIncidence isSelfAdjoint_steinIncidence
    (steinIncidence_basis n) hf
  rw [historyCoord_eq] at h
  have h' : cfc f steinIncidence (lp.single 2 n 1) =
      ((f (PrimeHodgeHistory.w n) : ℝ) : ℂ) • lp.single 2 n 1 := h
  show cfc f steinIncidence (lp.single 2 n 1) = gammaResidueMetric (lp.single 2 n 1)
  rw [h', hfw, ← historyCoord_eq, gammaResidueMetric_basis]

/-- Such a function necessarily vanishes at the bottom `0` of the spectrum. -/
theorem regrading_zero_of {f : ℝ → ℝ} (hf : ContinuousOn f (spectrum ℝ steinIncidence))
    (hfw : ∀ n, f (PrimeHodgeHistory.w n) = hellingerEvenGammaResidueGauge n ^ 2) : f 0 = 0 := by
  have hcont := hf 0 zero_mem_spectrum_steinIncidence
  have hw : Tendsto PrimeHodgeHistory.w atTop (𝓝[spectrum ℝ steinIncidence] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨historyFlux_tendsto_zero,
      Eventually.of_forall w_mem_spectrum⟩
  have h1 := hcont.tendsto.comp hw
  have h2 : Tendsto (fun n => hellingerEvenGammaResidueGauge n ^ 2) atTop (𝓝 0) :=
    summable_gammaResidueGauge_sq.tendsto_atTop_zero
  have h1' : Tendsto (fun n => hellingerEvenGammaResidueGauge n ^ 2) atTop (𝓝 (f 0)) :=
    h1.congr fun n => hfw n
  exact tendsto_nhds_unique h1' h2

/-- The prescribed values on `{0} ∪ {w_n}`. -/
def regradingOnSpectrum (x : ℝ) : ℝ := by
  classical
  exact if h : ∃ n, PrimeHodgeHistory.w n = x then hellingerEvenGammaResidueGauge (Nat.find h) ^ 2
    else 0

theorem regradingOnSpectrum_w (n : ℕ) :
    regradingOnSpectrum (PrimeHodgeHistory.w n) = hellingerEvenGammaResidueGauge n ^ 2 := by
  classical
  have h : ∃ k, PrimeHodgeHistory.w k = PrimeHodgeHistory.w n := ⟨n, rfl⟩
  rw [regradingOnSpectrum, dif_pos h]
  congr 2
  exact w_strictAnti.injective (Nat.find_spec h)

theorem regradingOnSpectrum_zero : regradingOnSpectrum 0 = 0 := by
  classical
  have h : ¬ ∃ n, PrimeHodgeHistory.w n = 0 := fun ⟨n, hn⟩ =>
    (PrimeHodgeHistory.w_pos n).ne' hn
  rw [regradingOnSpectrum, dif_neg h]

/-- The spectral point set `{0} ∪ {w_n}`. -/
def historySpectralSet : Set ℝ := insert 0 (Set.range PrimeHodgeHistory.w)

theorem isClosed_historySpectralSet : IsClosed historySpectralSet :=
  historyFlux_tendsto_zero.isCompact_insert_range.isClosed

theorem continuousOn_regradingOnSpectrum : ContinuousOn regradingOnSpectrum historySpectralSet := by
  rw [Metric.continuousOn_iff]
  rintro b hb ε hε
  rcases hb with rfl | ⟨n, rfl⟩
  · have h2 : Tendsto (fun n => hellingerEvenGammaResidueGauge n ^ 2) atTop (𝓝 0) :=
      summable_gammaResidueGauge_sq.tendsto_atTop_zero
    obtain ⟨N, hN⟩ := (h2.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    refine ⟨PrimeHodgeHistory.w N, PrimeHodgeHistory.w_pos N, ?_⟩
    rintro a (rfl | ⟨m, rfl⟩) ha
    · simpa [regradingOnSpectrum_zero] using hε
    · rw [Real.dist_eq, sub_zero, abs_of_pos (PrimeHodgeHistory.w_pos m)] at ha
      have hmN : N < m := by
        by_contra hc
        exact absurd ha (not_lt.2 (w_strictAnti.antitone (not_lt.1 hc)))
      rw [regradingOnSpectrum_w, regradingOnSpectrum_zero, Real.dist_eq, sub_zero,
        abs_of_nonneg (sq_nonneg _)]
      exact hN m hmN.le
  · set δ : ℝ := min (PrimeHodgeHistory.w n - PrimeHodgeHistory.w (n + 1))
      (min (PrimeHodgeHistory.w n)
        (if n = 0 then PrimeHodgeHistory.w 0 else
          PrimeHodgeHistory.w (n - 1) - PrimeHodgeHistory.w n))
    have hgap : 0 < PrimeHodgeHistory.w n - PrimeHodgeHistory.w (n + 1) :=
      sub_pos.2 (w_strictAnti (Nat.lt_succ_self n))
    have hprev : 0 < (if n = 0 then PrimeHodgeHistory.w 0 else
        PrimeHodgeHistory.w (n - 1) - PrimeHodgeHistory.w n) := by
      split_ifs with h
      · exact PrimeHodgeHistory.w_pos 0
      · exact sub_pos.2 (w_strictAnti (by omega))
    refine ⟨δ, lt_min hgap (lt_min (PrimeHodgeHistory.w_pos n) hprev), ?_⟩
    rintro a (rfl | ⟨m, rfl⟩) ha
    · exfalso
      rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (PrimeHodgeHistory.w_pos n)] at ha
      exact absurd ha (not_lt.2 ((min_le_right _ _).trans (min_le_left _ _)))
    · rcases lt_trichotomy m n with hmn | rfl | hmn
      · exfalso
        have hn0 : n ≠ 0 := by omega
        have hle : PrimeHodgeHistory.w (n - 1) ≤ PrimeHodgeHistory.w m :=
          w_strictAnti.antitone (by omega)
        have hδ : δ ≤ PrimeHodgeHistory.w (n - 1) - PrimeHodgeHistory.w n := by
          have h1 : δ ≤ min (PrimeHodgeHistory.w n) (if n = 0 then PrimeHodgeHistory.w 0 else
              PrimeHodgeHistory.w (n - 1) - PrimeHodgeHistory.w n) := min_le_right _ _
          have h2 := h1.trans (min_le_right _ _)
          simpa [hn0] using h2
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 (w_strictAnti hmn))] at ha
        linarith
      · simpa using hε
      · exfalso
        have hle : PrimeHodgeHistory.w m ≤ PrimeHodgeHistory.w (n + 1) :=
          w_strictAnti.antitone hmn
        have hδ : δ ≤ PrimeHodgeHistory.w n - PrimeHodgeHistory.w (n + 1) := min_le_left _ _
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 (w_strictAnti hmn))] at ha
        linarith

/-- **(PPTI.57).**  A continuous regrading `f_Γ : ℝ → ℝ` with `f_Γ(0) = 0` and
`f_Γ(w_n) = η_n²` exists (Tietze extension from the closed set `{0} ∪ {w_n}`). -/
theorem exists_gammaRegrading :
    ∃ f : ℝ → ℝ, Continuous f ∧ f 0 = 0 ∧
      ∀ n, f (PrimeHodgeHistory.w n) = hellingerEvenGammaResidueGauge n ^ 2 := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq isClosed_historySpectralSet
    ⟨historySpectralSet.restrict regradingOnSpectrum,
      continuousOn_regradingOnSpectrum.restrict⟩
  have hval : ∀ x (hx : x ∈ historySpectralSet), g x = regradingOnSpectrum x := fun x hx =>
    congrArg (fun F : C(historySpectralSet, ℝ) => F ⟨x, hx⟩) hg
  refine ⟨g, g.continuous, ?_, fun n => ?_⟩
  · rw [hval 0 (Set.mem_insert _ _), regradingOnSpectrum_zero]
  · rw [hval _ (Set.mem_insert_of_mem _ ⟨n, rfl⟩), regradingOnSpectrum_w]

/-- **(PPTI.57).**  `G_Γ = f_Γ(Φ)` for a continuous regrading `f_Γ` with `f_Γ(0) = 0`. -/
theorem gammaResidueMetric_eq_cfc :
    ∃ f : ℝ → ℝ, Continuous f ∧ f 0 = 0 ∧
      (∀ n, f (PrimeHodgeHistory.w n) = hellingerEvenGammaResidueGauge n ^ 2) ∧
      cfc f steinIncidence = gammaResidueMetric := by
  obtain ⟨f, hf, h0, hw⟩ := exists_gammaRegrading
  exact ⟨f, hf, h0, hw, cfc_steinIncidence_eq_gammaResidueMetric hf.continuousOn hw⟩

/-! ## The normalized prime extension -/

/-- The normalized weights `η_n²/Z`. -/
def normalizedGammaResidueWeight (n : ℕ) : ℝ := hellingerEvenGammaResidueGauge n ^ 2 / gammaResidueMass

theorem normalizedGammaResidueWeight_pos (n : ℕ) : 0 < normalizedGammaResidueWeight n :=
  div_pos (pow_pos (hellingerEvenGammaResidueGauge_pos n) 2) gammaResidueMass_pos

theorem summable_normalizedGammaResidueWeight : Summable normalizedGammaResidueWeight :=
  summable_gammaResidueGauge_sq.div_const _

theorem tsum_normalizedGammaResidueWeight : ∑' n, normalizedGammaResidueWeight n = 1 := by
  rw [show (fun n => normalizedGammaResidueWeight n) =
    fun n => hellingerEvenGammaResidueGauge n ^ 2 / gammaResidueMass from rfl, tsum_div_const,
    ← gammaResidueMass, div_self gammaResidueMass_pos.ne']

theorem summable_normalizedGammaResidueWeight_sq :
    Summable fun n => normalizedGammaResidueWeight n ^ 2 :=
  summable_normalizedGammaResidueWeight.of_nonneg_of_le (fun n => sq_nonneg _) fun n => by
    have h0 := (normalizedGammaResidueWeight_pos n).le
    have h1 : normalizedGammaResidueWeight n ≤ 1 := by
      rw [← tsum_normalizedGammaResidueWeight]
      exact summable_normalizedGammaResidueWeight.le_tsum n fun k _ =>
        (normalizedGammaResidueWeight_pos k).le
    nlinarith

/-- **(PPTI.57).**  The normalized prime extension `Z⁻¹ G_Γ ⊗ A_d` is positive, nuclear with trace
one, and prime-mixed on every history slice. -/
theorem gammaResiduePrimeExtension_properties {d : ℝ} (hd : 0 < d) :
    (historyStokesOperator normalizedGammaResidueWeight
        (fun n => (normalizedGammaResidueWeight_pos n).le)
        summable_normalizedGammaResidueWeight_sq hd).IsPositive ∧
      MemSchattenClass 1 (historyStokesOperator normalizedGammaResidueWeight
        (fun n => (normalizedGammaResidueWeight_pos n).le)
        summable_normalizedGammaResidueWeight_sq hd) ∧
      ContinuousLinearMap.opTrace (historyStokesOperator normalizedGammaResidueWeight
        (fun n => (normalizedGammaResidueWeight_pos n).le)
        summable_normalizedGammaResidueWeight_sq hd) = 1 ∧
      ∀ n p q, historyStokesKernel normalizedGammaResidueWeight d ((n, p), (n, q)) ≠ 0 := by
  refine ⟨historyStokesOperator_isPositive _ _ _ hd,
    historyStokesOperator_memSchattenClass_one _ _ summable_normalizedGammaResidueWeight _ hd,
    ?_, fun n p q => historyStokesKernel_sameHistory_ne_zero _ normalizedGammaResidueWeight_pos
      hd n p q⟩
  rw [opTrace_historyStokesOperator _ _ summable_normalizedGammaResidueWeight _ hd,
    tsum_normalizedGammaResidueWeight, Complex.ofReal_one]

/-! ## (PPTI.58): properness in the Gamma metric -/

/-- **(PPTI.58).**  In the inverse normalized Gamma metric the vertex energy is
`‖(Z⁻¹ G_Γ)^{-1/2} v_n‖² = 2Z cosh(2aL(n+1)) ‖x‖²`. -/
theorem gammaInverseEnergy_balancedPrimitive {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    channelEnergy (hellingerGammaCompletedBalancedPrimitive hpq a n x) /
        normalizedGammaResidueWeight n =
      2 * gammaResidueMass * Real.cosh (2 * a * pairClockLength p q * ((n : ℝ) + 1)) * ‖x‖ ^ 2 := by
  rw [channelEnergy_balancedPrimitive, normalizedGammaResidueWeight]
  have hη := (hellingerEvenGammaResidueGauge_pos n).ne'
  have hZ := gammaResidueMass_pos.ne'
  field_simp

/-- At neutral displacement `a = 0` the energy is the constant `2Z‖x‖²`. -/
theorem gammaInverseEnergy_neutral {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ)
    (x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq) :
    channelEnergy (hellingerGammaCompletedBalancedPrimitive hpq 0 n x) /
        normalizedGammaResidueWeight n = 2 * gammaResidueMass * ‖x‖ ^ 2 := by
  rw [gammaInverseEnergy_balancedPrimitive]
  simp

/-- At every nonzero displacement the energy of a nonzero vertex diverges. -/
theorem tendsto_gammaInverseEnergy_atTop {p q : Nat.Primes} (hpq : p ≠ q) {a : ℝ} (ha : a ≠ 0)
    {x : DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => channelEnergy (hellingerGammaCompletedBalancedPrimitive hpq a n x) /
      normalizedGammaResidueWeight n) atTop atTop := by
  simp_rw [gammaInverseEnergy_balancedPrimitive]
  have hc : 0 < 2 * gammaResidueMass * ‖x‖ ^ 2 :=
    mul_pos (mul_pos two_pos gammaResidueMass_pos) (pow_pos (norm_pos_iff.2 hx) 2)
  have hlin : Tendsto (fun n : ℕ => (|2 * a * pairClockLength p q| * ((n : ℝ) + 1) + 1) / 2)
      atTop atTop :=
    (tendsto_atTop_add_const_right _ 1
      ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
        (abs_pos.2 (mul_ne_zero (mul_ne_zero two_ne_zero ha)
          (pairClockLength_pos p q).ne')))).atTop_div_const two_pos
  have hcosh : Tendsto (fun n : ℕ => Real.cosh (2 * a * pairClockLength p q * ((n : ℝ) + 1)))
      atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) hlin
    have h := abs_add_one_le_two_mul_cosh (2 * a * pairClockLength p q * ((n : ℝ) + 1))
    rw [abs_mul (2 * a * pairClockLength p q),
      abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)] at h
    linarith
  refine (hcosh.const_mul_atTop hc).congr fun n => ?_
  ring

end GaloisForLFunctions.HTGeometry
