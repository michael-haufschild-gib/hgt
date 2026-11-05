import GaloisForLFunctions.FiniteFreeProbability.PoleSideInstability
import GaloisForLFunctions.RHTower.FriableMomentGammaDerivative
import GaloisForLFunctions.RHTower.XiMassJetIntegrand
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerWindowFoldTransfer

/-!
# The Gamma piece has no Hermite–Biehler normalization

`Γ(1/4 + iw/2) = ∫_0^∞ x^{−3/4} e^{−x} e^{iw (log x)/2} dx` is a positive mixture of exponentials.
In the variable `u = log x` its weight is `e^{u/4 − e^u}`: double-exponentially small as `u → +∞`
but only exponentially small as `u → −∞` (the pole of `Γ` at `0`). The translated piece
`e^{icw}Γ(1/4 + iw/2)` has Taylor coefficients `i^k ∫ e^{u/4−e^u}(c + u/2)^k du / k!`, so its reversed
Jensen polynomials satisfy `R_d(iy) = i^d ∫ e^{u/4−e^u}(y + c + u/2)^d du`.

Substituting `u = −2c + 2v` and folding `v ↦ −v` gives, for odd `d`,

`∫ e^{u/4−e^u}(c + u/2)^d du = 2e^{−c/2} ∫_0^∞ v^d (e^{v/2 − Ae^{2v}} − e^{−v/2 − Ae^{−2v}}) dv`,
`A = e^{−2c}`.

The bracket is negative for `v > 1/(2A)`, and a window at twice that distance outweighs the bounded
positive part, so the odd moments are eventually negative while the zeroth moment is positive.

**Theorem.** For every translation `c`, the reversed Jensen polynomials of the Taylor series of
`e^{icw}Γ(1/4 + iw/2)` have a root in the open upper half-plane at all large odd degrees.
-/

open Polynomial Filter Topology Complex MeasureTheory Set

namespace FiniteFreeProbability

noncomputable section

/-! ## Integrability of doubly exponential weights -/

/-- `f(u) e^{βu − Ae^{γu}}` is integrable when `|f|` grows at most polynomially. -/
theorem integrable_mul_exp_sub_mul_exp {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} {m : ℕ}
    (hfK : ∀ u, |f u| ≤ K * (1 + |u|) ^ m) {β A γ : ℝ} (hβ : 0 < β) (hA : 0 < A) (hγ : 0 < γ) :
    Integrable fun u : ℝ => f u * Real.exp (β * u - A * Real.exp (γ * u)) := by
  set C := 2 * β ^ 2 / (A * γ ^ 2)
  have hD : 0 < A * γ ^ 2 := by positivity
  refine ((RHTower.integrable_polyAbs_mul_exp_neg_abs m hβ).const_mul (K * Real.exp C)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  have hexp : β * u - A * Real.exp (γ * u) ≤ C - β * |u| := by
    have hpos : 0 < A * Real.exp (γ * u) := by positivity
    have hC : 0 ≤ C := by positivity
    rcases le_or_gt u 0 with hu | hu
    · rw [abs_of_nonpos hu]; linarith
    · rw [abs_of_pos hu]
      have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ γ * u)
      have hγu : 0 < γ * u := mul_pos hγ hu
      have hAe : A * ((γ * u) ^ 2 / 2) ≤ A * Real.exp (γ * u) :=
        mul_le_mul_of_nonneg_left (by linarith) hA.le
      have hsq : 0 ≤ (A * γ ^ 2 / 2) * (u - 2 * β / (A * γ ^ 2)) ^ 2 := by positivity
      have hid : (A * γ ^ 2 / 2) * (u - 2 * β / (A * γ ^ 2)) ^ 2 =
          A * ((γ * u) ^ 2 / 2) - 2 * β * u + C := by
        simp only [C]; field_simp; ring
      linarith
  have hK : 0 ≤ K := le_trans (abs_nonneg _) ((hfK 0).trans (by simp))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc |f u| * Real.exp (β * u - A * Real.exp (γ * u))
      ≤ (K * (1 + |u|) ^ m) * Real.exp (C - β * |u|) :=
        mul_le_mul (hfK u) (Real.exp_le_exp.2 hexp) (Real.exp_pos _).le (by positivity)
    _ = K * Real.exp C * ((1 + |u|) ^ m * Real.exp (-(β * |u|))) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring

/-! ## The Gamma piece -/

/-- The log-variable Gamma weight `e^{u/4 − e^u}`. -/
def gammaWeight (u : ℝ) : ℝ := Real.exp (u / 4 - Real.exp u)

/-- The translated moments `∫ e^{u/4 − e^u} (c + u/2)^k du`. -/
def gammaMoment (c : ℝ) (k : ℕ) : ℝ := ∫ u, gammaWeight u * (c + u / 2) ^ k

theorem integrable_gammaWeight_mul_pow (c : ℝ) (k : ℕ) :
    Integrable fun u : ℝ => gammaWeight u * (c + u / 2) ^ k := by
  have h := integrable_mul_exp_sub_mul_exp (f := fun u : ℝ => (c + u / 2) ^ k) (by fun_prop)
    (K := (|c| + 1) ^ k) (m := k) (fun u => by
      rw [abs_pow, ← mul_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ k
      have := abs_add_le c (u / 2)
      rw [abs_div, abs_two] at this
      nlinarith [abs_nonneg c, abs_nonneg u])
    (by norm_num : (0 : ℝ) < 1 / 4) one_pos one_pos
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [gammaWeight, one_mul]
  rw [mul_comm]; congr 2; ring

/-- The translated Gamma piece `Σ_k i^k ∫ e^{u/4−e^u}(c + u/2)^k du / k! · w^k`. -/
def gammaMixture (c : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun k =>
    ∫ u, (gammaWeight u : ℂ) * PowerSeries.coeff k (expSeries (I * ((c + u / 2 : ℝ) : ℂ)))

theorem coeff_gammaMixture (c : ℝ) (k : ℕ) :
    PowerSeries.coeff k (gammaMixture c) =
      I ^ k * ((gammaMoment c k / (k.factorial : ℝ) : ℝ) : ℂ) := by
  have h : ∀ u : ℝ, (gammaWeight u : ℂ) *
      PowerSeries.coeff k (expSeries (I * ((c + u / 2 : ℝ) : ℂ))) =
      I ^ k * ((gammaWeight u * (c + u / 2) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := fun u => by
    rw [coeff_expSeries, mul_pow]; push_cast; ring
  rw [gammaMixture, PowerSeries.coeff_mk, funext h, integral_const_mul, integral_complex_ofReal,
    gammaMoment, integral_div]

theorem integrable_gammaMixture_term (c : ℝ) (k : ℕ) :
    Integrable fun u : ℝ =>
      (gammaWeight u : ℂ) * PowerSeries.coeff k (expSeries (I * ((c + u / 2 : ℝ) : ℂ))) :=
  ((Complex.ofRealCLM.integrable_comp
    ((integrable_gammaWeight_mul_pow c k).div_const (k.factorial : ℝ))).const_mul
    (I ^ k : ℂ)).congr (Filter.Eventually.of_forall fun u => by
      simp only [Complex.ofRealCLM_apply]; rw [coeff_expSeries, mul_pow]; push_cast; ring)

/-- Multiplying by `e^{ic'w}` translates the Gamma piece. -/
theorem expSeries_mul_gammaMixture (c c' : ℝ) :
    expSeries (I * c') * gammaMixture c = gammaMixture (c + c') := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [gammaMixture, PowerSeries.coeff_mk]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum (f := fun (p : ℕ × ℕ) (u : ℝ) =>
      PowerSeries.coeff p.1 (expSeries (I * (c' : ℂ))) * ((gammaWeight u : ℂ) *
        PowerSeries.coeff p.2 (expSeries (I * ((c + u / 2 : ℝ) : ℂ)))))
    _ fun p _ => (integrable_gammaMixture_term c p.2).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  simp_rw [mul_left_comm _ (gammaWeight u : ℂ)]
  rw [← Finset.mul_sum, ← PowerSeries.coeff_mul, expSeries_add]
  congr 3
  push_cast; ring

/-- The Taylor series at `0` of `w ↦ Γ(1/4 + iw/2)`. -/
def gammaTaylor : PowerSeries ℂ :=
  PowerSeries.mk fun k =>
    (I / 2) ^ k * iteratedDeriv k Complex.Gamma (1 / 4 : ℂ) / (k.factorial : ℂ)

/-- `Γ^{(k)}(1/4) = ∫ e^{u/4 − e^u} u^k du`. -/
theorem iteratedDeriv_Gamma_quarter (k : ℕ) :
    iteratedDeriv k Complex.Gamma (1 / 4 : ℂ) = ((∫ u, gammaWeight u * u ^ k : ℝ) : ℂ) := by
  rw [RHTower.iteratedDeriv_Gamma_eq_integral k (by norm_num),
    GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.integral_Ioi_zero_exp_subst,
    ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [RHTower.gammaLogIntegrand, RHTower.gammaLogIntegrandReal, Real.log_exp,
    Complex.real_smul]
  rw [show (1 / 4 : ℂ) - 1 = ((-3 / 4 : ℝ) : ℂ) by push_cast; norm_num,
    ← Complex.ofReal_cpow (Real.exp_pos u).le, ← Real.exp_mul, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul]
  congr 1
  rw [gammaWeight, ← mul_assoc, ← Real.exp_add, mul_comm (u ^ k), ← mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- The Gamma piece at translation `0` is the Taylor series of `Γ(1/4 + iw/2)`. -/
theorem gammaMixture_zero : gammaMixture 0 = gammaTaylor := by
  ext k
  rw [coeff_gammaMixture, gammaTaylor, PowerSeries.coeff_mk, iteratedDeriv_Gamma_quarter, gammaMoment]
  simp only [zero_add, div_pow, ← mul_div_assoc, integral_div]
  push_cast
  field_simp

/-- **The translated Gamma piece is `e^{icw}Γ(1/4 + iw/2)`.** -/
theorem gammaMixture_eq (c : ℝ) : gammaMixture c = expSeries (I * c) * gammaTaylor := by
  rw [← gammaMixture_zero, expSeries_mul_gammaMixture, zero_add]

/-! ## Odd moments are eventually negative -/

/-- **A far negative window dominates.** If `k ≤ B` on `(0, V]` and `k < 0` beyond `V`, then
`∫_0^∞ v^d k(v) dv < 0` for all large `d`: the window `[2V, 2V + 1]` contributes `≤ −κ(2V)^d`,
the positive part at most `BV·V^d`. -/
theorem eventually_setIntegral_pow_mul_neg {k : ℝ → ℝ} (hk : Continuous k) {V B : ℝ}
    (hV : 0 < V) (hB : ∀ v ∈ Ioc 0 V, k v ≤ B) (hneg : ∀ v, V < v → k v < 0)
    (hint : ∀ d : ℕ, IntegrableOn (fun v => v ^ d * k v) (Ioi 0)) :
    ∀ᶠ d : ℕ in atTop, ∫ v in Ioi 0, v ^ d * k v < 0 := by
  obtain ⟨v₀, hv₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by linarith : 2 * V ≤ 2 * V + 1)) hk.continuousOn
  set κ := -k v₀
  have hκ : 0 < κ := by
    have := hneg v₀ (by linarith [hv₀.1]); simp only [κ]; linarith
  set B' := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  have hev : ∀ᶠ d : ℕ in atTop, B' * V < κ * 2 ^ d :=
    ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_gt_atTop (B' * V / κ)).mono
      fun d hd => by rw [div_lt_iff₀ hκ] at hd; linarith
  filter_upwards [hev] with d hd
  have hsplit : ∫ v in Ioi 0, v ^ d * k v =
      (∫ v in Ioc 0 V, v ^ d * k v) + ∫ v in Ioi V, v ^ d * k v := by
    have h := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((hint d).mono_set Ioc_subset_Ioi_self) ((hint d).mono_set (Ioi_subset_Ioi hV.le))
    rwa [Ioc_union_Ioi_eq_Ioi hV.le] at h
  have h1 : ∫ v in Ioc 0 V, v ^ d * k v ≤ V * (V ^ d * B') := by
    have := setIntegral_mono_on ((hint d).mono_set Ioc_subset_Ioi_self)
      (integrableOn_const (C := V ^ d * B') measure_Ioc_lt_top.ne) measurableSet_Ioc
      fun v hv => by
        have hv0 : 0 ≤ v ^ d := pow_nonneg hv.1.le d
        calc v ^ d * k v ≤ v ^ d * B' := mul_le_mul_of_nonneg_left
              ((hB v hv).trans (le_max_left _ _)) hv0
          _ ≤ V ^ d * B' := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv.1.le hv.2 d) hB'
    rwa [setIntegral_const, Real.volume_real_Ioc_of_le hV.le, sub_zero, smul_eq_mul] at this
  have h2 : ∫ v in Ioi V, v ^ d * k v ≤ ∫ v in Icc (2 * V) (2 * V + 1), v ^ d * k v := by
    have := setIntegral_mono_set (f := fun v => -(v ^ d * k v))
      ((hint d).mono_set (Ioi_subset_Ioi hV.le)).neg
      (ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => by
        simp only [Pi.zero_apply, Left.nonneg_neg_iff]
        exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (by linarith [mem_Ioi.1 hv]) d)
          (hneg v hv).le)
      ((Icc_subset_Ioi_iff (a₁ := 2 * V) (b₁ := 2 * V + 1) (a₂ := V) (by linarith)).2
        (by linarith)).eventuallyLE
    rw [integral_neg, integral_neg] at this
    linarith
  have h3 : ∫ v in Icc (2 * V) (2 * V + 1), v ^ d * k v ≤ -(κ * (2 * V) ^ d) := by
    have := setIntegral_mono_on
      ((hint d).mono_set ((Icc_subset_Ioi_iff (a₁ := 2 * V) (b₁ := 2 * V + 1) (a₂ := 0)
        (by linarith)).2 (by linarith)))
      (integrableOn_const (C := -(κ * (2 * V) ^ d)) measure_Icc_lt_top.ne) measurableSet_Icc
      fun v hv => by
        have hkv : k v ≤ -κ := by simp only [κ, neg_neg]; exact hmax hv
        have hv2 : (2 * V) ^ d ≤ v ^ d := pow_le_pow_left₀ (by linarith) hv.1 d
        nlinarith [pow_nonneg (by linarith [hv.1] : (0 : ℝ) ≤ v) d]
    rwa [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), add_sub_cancel_left,
      one_smul] at this
  have hVd : 0 < V ^ d := pow_pos hV d
  have hlt := mul_lt_mul_of_pos_left hd hVd
  rw [mul_pow] at h3
  rw [hsplit]
  nlinarith

/-- After the substitution `u = −2c + 2v`, the moment is a two-sided integral of
`v^d e^{v/2 − Ae^{2v}}`. -/
theorem gammaMoment_eq (c : ℝ) (d : ℕ) :
    gammaMoment c d = 2 * Real.exp (-c / 2) *
      ∫ v, v ^ d * Real.exp (v / 2 - Real.exp (-2 * c) * Real.exp (2 * v)) := by
  set F : ℝ → ℝ := fun u => gammaWeight u * (c + u / 2) ^ d
  have hsub : ∫ v, F (-2 * c + 2 * v) = (1 / 2) * ∫ u, F u := by
    have h1 := Measure.integral_comp_mul_left (fun y => F (-2 * c + y)) 2
    rw [integral_add_left_eq_self F (-2 * c)] at h1
    rw [h1, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), smul_eq_mul]; norm_num
  have hpt : ∀ v : ℝ, F (-2 * c + 2 * v) = Real.exp (-c / 2) *
      (v ^ d * Real.exp (v / 2 - Real.exp (-2 * c) * Real.exp (2 * v))) := fun v => by
    simp only [F, gammaWeight]
    rw [show c + (-2 * c + 2 * v) / 2 = v by ring,
      show Real.exp (-2 * c) * Real.exp (2 * v) = Real.exp (-2 * c + 2 * v) from
        (Real.exp_add _ _).symm, mul_comm (v ^ d), ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [gammaMoment, show (∫ u, gammaWeight u * (c + u / 2) ^ d) = ∫ u, F u from rfl]
  have : ∫ u, F u = 2 * ∫ v, F (-2 * c + 2 * v) := by rw [hsub]; ring
  rw [this, funext hpt, integral_const_mul]
  ring

theorem eventually_gammaMoment_neg (c : ℝ) :
    ∀ᶠ d : ℕ in atTop, Odd d → gammaMoment c d < 0 := by
  set A := Real.exp (-2 * c)
  have hA : 0 < A := Real.exp_pos _
  set g : ℕ → ℝ → ℝ := fun d v => v ^ d * Real.exp (v / 2 - A * Real.exp (2 * v))
  have hg : ∀ d, Integrable (g d) := fun d =>
    (integrable_mul_exp_sub_mul_exp (f := fun v : ℝ => v ^ d) (by fun_prop) (K := 1) (m := d)
      (fun u => by
        rw [abs_pow, one_mul]
        exact pow_le_pow_left₀ (abs_nonneg u) (by linarith) d)
      (by norm_num : (0 : ℝ) < 1 / 2) hA two_pos).congr
      (Filter.Eventually.of_forall fun v => by simp only [g]; congr 2; ring)
  set k : ℝ → ℝ := fun v =>
    Real.exp (v / 2 - A * Real.exp (2 * v)) - Real.exp (-v / 2 - A * Real.exp (-2 * v))
  have hgneg : ∀ d v, Odd d → g d (-v) = -(v ^ d * Real.exp (-v / 2 - A * Real.exp (-2 * v))) :=
    fun d v hd => by
      show (-v) ^ d * Real.exp (-v / 2 - A * Real.exp (2 * -v)) = _
      rw [hd.neg_pow, show (2 : ℝ) * -v = -2 * v by ring]; ring
  have hfold : ∀ d : ℕ, Odd d → ∫ v, g d v = ∫ v in Ioi 0, v ^ d * k v := fun d hd => by
    rw [← intervalIntegral.integral_Iic_add_Ioi (hg d).integrableOn (hg d).integrableOn]
    have hneg := integral_comp_neg_Iic 0 (fun y => g d (-y))
    simp only [neg_neg, neg_zero] at hneg
    rw [hneg, ← integral_add ((hg d).comp_neg).integrableOn (hg d).integrableOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [k]
    rw [hgneg d v hd]; simp only [g]; ring
  -- the bracket `k` is bounded on `(0, V]` and negative beyond `V = 1/(2A)`
  set V := 1 / (2 * A)
  have hV : 0 < V := by positivity
  have hkB : ∀ v ∈ Ioc 0 V, k v ≤ Real.exp (V / 2) := fun v hv => by
    simp only [k]
    have h1 : Real.exp (v / 2 - A * Real.exp (2 * v)) ≤ Real.exp (V / 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.exp_pos (2 * v), hv.2])
    linarith [Real.exp_pos (-v / 2 - A * Real.exp (-2 * v))]
  have hkneg : ∀ v, V < v → k v < 0 := fun v hv => by
    have hv0 : 0 < v := hV.trans hv
    have h2Av : 1 < 2 * A * v := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * A)).1 hv; linarith
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * v)
    have he : Real.exp (-2 * v) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hlt : v / 2 - A * Real.exp (2 * v) < -v / 2 - A * Real.exp (-2 * v) := by
      have : v < 2 * A * v * v := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hq hA.le, mul_le_mul_of_nonneg_left he hA.le]
    simp only [k]
    linarith [Real.exp_lt_exp.2 hlt]
  have hk : Continuous k := by simp only [k]; fun_prop
  have hint' : ∀ d : ℕ, IntegrableOn (fun v => v ^ d * k v) (Ioi 0) := fun d => by
    have h1 := (hg d).integrableOn (s := Ioi 0)
    have h2 : IntegrableOn (fun v => v ^ d * Real.exp (-v / 2 - A * Real.exp (-2 * v))) (Ioi 0) := by
      have := ((hg d).comp_neg.const_mul ((-1 : ℝ) ^ d)).integrableOn (s := Ioi 0)
      refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
      simp only [g]
      rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, show (2 : ℝ) * -v = -2 * v by ring]
    refine (h1.sub h2).congr_fun (fun v _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, g, k]; ring
  have hev := eventually_setIntegral_pow_mul_neg hk hV hkB hkneg hint'
  filter_upwards [hev] with d hd hodd
  rw [gammaMoment_eq, show (∫ v, v ^ d * Real.exp (v / 2 - Real.exp (-2 * c) * Real.exp (2 * v)))
    = ∫ v, g d v from rfl, hfold d hodd]
  exact mul_neg_of_pos_of_neg (by positivity) hd

/-- **No translation stabilizes the Gamma piece.** For every `c`, the reversed Jensen polynomials of
the Taylor series of `e^{icw}Γ(1/4 + iw/2)` have a root in the open upper half-plane for all large
odd degrees. -/
theorem eventually_exists_upper_root_gammaMixture (c : ℝ) :
    ∀ᶠ d : ℕ in atTop, Odd d →
      ∃ x : ℂ, (jensenRev d (expSeries (I * c) * gammaTaylor)).IsRoot x ∧ 0 < x.im := by
  filter_upwards [eventually_gammaMoment_neg c] with d hd hodd
  rw [← gammaMixture_eq]
  refine exists_upper_root_of_coeff (fun k => gammaMoment c k / (k.factorial : ℝ))
    (coeff_gammaMixture c) hodd.pos ?_ (div_neg_of_neg_of_pos (hd hodd) (by positivity))
  simp only [gammaMoment, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
    gammaWeight]
  exact integral_exp_pos (by
    simpa [gammaWeight] using integrable_gammaWeight_mul_pow c 0)

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_exists_upper_root_gammaMixture
#print axioms FiniteFreeProbability.gammaMixture_eq
