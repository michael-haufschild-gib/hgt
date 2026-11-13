import GaloisForLFunctions.EulerFETransportTheory.DecayingTentErrorsAreSmall
import GaloisForLFunctions.EulerFETransportTheory.RecurrenceThroughSparseErrors

/-!
# Decaying defects vanish in the unit gap

Let `ν_B` satisfy the defective theta law with `‖g(t)‖ ≤ C (1 + |t|)^{-a}`, `a > 0`, and let
`E_h(y) = tentAtomMass − tentRecurrentPart` be the tent error (`tendsto_tentDefect`).

* `tentError_sparse` — Fatou and the dyadic-shell bound give `∫_W^{2W} (E_h² + E_{h/2}²) = o(W)`.
* `tentRecurrentPart_half_eq_zero_of_decay` — the recurrence through sparse errors:
  `P_h(y) < 1/4 ⇒ P_{h/2}(y) = 0`.
* `eventually_tentRecurrentPart_eq_zero_of_decay` — inside `[η, 1 - η]` the small-width bound makes
  `P_{2δ} = -E_{2δ} < 1/4`, hence `P_δ = 0` and `E_δ = 0` for all small `δ`.
-/

open Complex MeasureTheory Filter Topology Set Function
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ExactEventTheory
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- **Fatou on an interval**: nonnegative continuous `U_k → V` on `[a, b]` with `∫_a^b U_k ≤ M`
give `∫⁻_{[a,b]} V ≤ M`. -/
theorem lintegral_le_of_tendsto {U : ℕ → ℝ → ℝ} {V : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hU : ∀ k, Continuous (U k)) (hU0 : ∀ k t, 0 ≤ U k t)
    (hlim : ∀ t ∈ Icc a b, Tendsto (fun k => U k t) atTop (𝓝 (V t)))
    (hM : ∀ k, ∫ t in a..b, U k t ≤ M) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (V t) ≤ ENNReal.ofReal M := by
  have hV : EqOn (fun t => ENNReal.ofReal (V t))
      (fun t => liminf (fun k => ENNReal.ofReal (U k t)) atTop) (Icc a b) := fun t ht =>
    (((ENNReal.continuous_ofReal.tendsto _).comp (hlim t ht)).liminf_eq).symm
  rw [setLIntegral_congr_fun measurableSet_Icc hV]
  refine (lintegral_liminf_le fun k => (hU k).measurable.ennreal_ofReal).trans ?_
  refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
  have hint : IntegrableOn (U k) (Icc a b) := (hU k).integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => hU0 k t),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact ENNReal.ofReal_le_ofReal (hM k)

/-- The error of the tent identity. -/
def tentError (B : RHTower.BeurlingSystem) [Countable B.Label] (β h y : ℝ) : ℝ :=
  tentAtomMass B.intNorm h y - tentRecurrentPart B.intNorm β h y

theorem eventually_le_mul_of_rpow_lt_one {K α c : ℝ} (hα : α < 1) (hc : 0 < c) :
    ∀ᶠ W in atTop, K * W ^ α ≤ c * W := by
  have ht := (tendsto_rpow_neg_atTop (show 0 < 1 - α by linarith)).const_mul K
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hc), eventually_gt_atTop 0] with W hW hW0
  have e : K * W ^ α = K * W ^ (-(1 - α)) * W := by
    rw [mul_assoc, ← Real.rpow_add_one hW0.ne']; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hW.le hW0.le

/-- **The tent errors are sparse**: `∫_W^{2W} (E_h² + E_{h/2}²) = o(W)`. -/
theorem tentError_sparse (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ W in atTop, ∫⁻ t in Icc W (2 * W),
      ENNReal.ofReal (tentError B β h t ^ 2 + tentError B β (h / 2) t ^ 2) ≤
        ENNReal.ofReal (c * W) := by
  have hgb := poly_of_decay ha.le hgd
  obtain ⟨K₁, α₁, hα₁, hK₁⟩ := exists_integral_sq_tentDefect_shell_le hgm ha hgd hh hh1
  obtain ⟨K₂, α₂, hα₂, hK₂⟩ := exists_integral_sq_tentDefect_shell_le hgm ha hgd
    (half_pos hh) (by linarith)
  -- `ε_k = 1/(k + 2) → 0⁺`
  have hεk : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => by
      show (0 : ℝ) < 1 / ((k : ℝ) + 2); positivity⟩
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hεk1 : ∀ k : ℕ, 1 / ((k : ℝ) + 2) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hεk0 : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 2) := fun k => by positivity
  filter_upwards [eventually_le_mul_of_rpow_lt_one (K := K₁) hα₁ (half_pos hc),
    eventually_le_mul_of_rpow_lt_one (K := K₂) hα₂ (half_pos hc), eventually_ge_atTop 2]
    with W hW₁ hW₂ hW2
  have hW1 : (1 : ℝ) ≤ W := by linarith
  refine (lintegral_le_of_tendsto (U := fun k t => tentDefect g h t (1 / ((k : ℝ) + 2)) ^ 2 +
    tentDefect g (h / 2) t (1 / ((k : ℝ) + 2)) ^ 2) (by linarith)
    (fun k => ((continuous_tentDefect hgm hgb hh (hεk0 k)).pow 2).add
      ((continuous_tentDefect hgm hgb (half_pos hh) (hεk0 k)).pow 2))
    (fun k t => by positivity) (fun t ht => ?_) (fun k => ?_)).trans
    (ENNReal.ofReal_le_ofReal (show K₁ * W ^ α₁ + K₂ * W ^ α₂ ≤ c * W by linarith))
  · have h1 := (tendsto_tentDefect B hBsum hgm hgb hθ hh hh1 (show h < t by linarith [ht.1])).comp
      hεk
    have h2 := (tendsto_tentDefect B hBsum hgm hgb hθ (half_pos hh) (by linarith)
      (show h / 2 < t by linarith [ht.1])).comp hεk
    exact (h1.pow 2).add (h2.pow 2)
  · have i1 : IntervalIntegrable (fun t => tentDefect g h t (1 / ((k : ℝ) + 2)) ^ 2) volume W
        (2 * W) := ((continuous_tentDefect hgm hgb hh (hεk0 k)).pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => tentDefect g (h / 2) t (1 / ((k : ℝ) + 2)) ^ 2) volume W
        (2 * W) :=
      ((continuous_tentDefect hgm hgb (half_pos hh) (hεk0 k)).pow 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2]
    exact add_le_add (hK₁ W _ hW1 (hεk0 k) (hεk1 k)) (hK₂ W _ hW1 (hεk0 k) (hεk1 k))

/-- **Recurrence for decaying defects**: `P_h(y) < 1/4 ⇒ P_{h/2}(y) = 0`. -/
theorem tentRecurrentPart_half_eq_zero_of_decay (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h y : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hy : tentRecurrentPart B.intNorm β h y < 1 / 4) :
    tentRecurrentPart B.intNorm β (h / 2) y = 0 := by
  have hsum := summable_beurling_inv_sq B hBsum
  have hh2 : 0 < h / 2 := by positivity
  refine recurrent_threshold_of_sparse_errors
    (continuous_tentRecurrentPart B.intNorm_pos hsum hh β)
    (isBohrAlmostPeriodic_tentRecurrentPart B.intNorm_pos hsum hh β)
    (continuous_tentRecurrentPart B.intNorm_pos hsum hh2 β)
    (isBohrAlmostPeriodic_tentRecurrentPart B.intNorm_pos hsum hh2 β)
    (E := tentError B β h) (F := tentError B β (h / 2))
    (fun c hc => tentError_sparse B hBsum hgm ha hgd hθ hh hh1 c hc) (T₀ := 0) (fun t _ ht => ?_) hy
  simp only [tentError, add_sub_cancel] at ht ⊢
  exact tentAtomMass_half_eq_zero_of_lt B.intNorm_pos hsum hh ht

/-- **Vanishing in the unit gap**: for `0 < η ≤ 1/4`, eventually as `δ → 0⁺` the recurrent part and
the atomic mass of the tent of width `δ` vanish at every centre `y ∈ [η, 1 - η]`. -/
theorem eventually_tentRecurrentPart_eq_zero_of_decay (B : RHTower.BeurlingSystem)
    [Countable B.Label] (hBsum : Summable fun i : B.Integer => B.intNorm i ^ (-(3 / 2 : ℝ)))
    {β : ℝ} {g : ℝ → ℂ} (hgm : Measurable g) {C a : ℝ} (ha : 0 < a)
    (hgd : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ (-a))
    (hθ : ∀ x : ℝ, 0 < x → measureTheta (beurlingSystemIntegerMeasure B) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingSystemIntegerMeasure B) x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ∀ᶠ δ in 𝓝[>] 0, ∀ y ∈ Icc η (1 - η),
      tentRecurrentPart B.intNorm β δ y = 0 ∧ tentAtomMass B.intNorm δ y = 0 := by
  have hgb := poly_of_decay ha.le hgd
  obtain ⟨K, ρ, hK, hρ, hsmall⟩ := exists_abs_tentDefect_le_smallWidth hgm ha hgd
  have hlim : Tendsto (fun δ : ℝ => K * (η ^ (-(1 / 2 : ℝ)) + 1) * (2 * δ) ^ ρ) (𝓝[>] 0)
      (𝓝 0) := by
    have hc : Continuous fun δ : ℝ => K * (η ^ (-(1 / 2 : ℝ)) + 1) * (2 * δ) ^ ρ :=
      continuous_const.mul ((continuous_const.mul continuous_id).rpow_const fun _ => Or.inr hρ.le)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Real.zero_rpow hρ.ne'] using this
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)),
    Ioo_mem_nhdsGT (show (0 : ℝ) < η / 4 by positivity)] with δ hδK hδ y hy
  have hδ0 : 0 < δ := hδ.1
  have hsum := summable_beurling_inv_sq B hBsum
  have hlam : ∀ i, 1 ≤ B.intNorm i := B.one_le_intNorm
  -- the error of width `2δ` is small
  have hE : |tentError B β (2 * δ) y| ≤ K * (η ^ (-(1 / 2 : ℝ)) + 1) * (2 * δ) ^ ρ := by
    have ht := tendsto_tentDefect B hBsum hgm hgb hθ (by positivity : (0 : ℝ) < 2 * δ)
      (by linarith [hδ.2]) (show 2 * δ < y by linarith [hδ.2, hy.1])
    refine le_of_tendsto ht.abs ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hsmall η (2 * δ) y ε (by positivity) (by linarith [hδ.2]) (by linarith [hδ.2]) hy.1
      (by linarith [hy.2]) hε.1 hε.2
  have hatom2 : tentAtomMass B.intNorm (2 * δ) y = 0 :=
    tentAtomMass_eq_zero_in_unit_gap hlam (by positivity) (by linarith [hδ.2, hy.2])
  have hP2 : tentRecurrentPart B.intNorm β (2 * δ) y < 1 / 4 := by
    have : tentRecurrentPart B.intNorm β (2 * δ) y = -tentError B β (2 * δ) y := by
      rw [tentError, hatom2]; ring
    rw [this]
    linarith [neg_le_abs (tentError B β (2 * δ) y)]
  have hP := tentRecurrentPart_half_eq_zero_of_decay B hBsum hgm ha hgd hθ (by positivity)
    (by linarith [hδ.2]) hP2
  rw [show 2 * δ / 2 = δ by ring] at hP
  exact ⟨hP, tentAtomMass_eq_zero_in_unit_gap hlam hδ0 (by linarith [hδ.2, hy.2])⟩

end GaloisForLFunctions.EulerFETransportTheory
