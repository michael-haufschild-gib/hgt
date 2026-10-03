import GaloisForLFunctions.RHTower.WeilLockPhasePositivity

/-!
# Lock phases of sublinear variation around a line

Let `G` be a Herglotz producer for the weights `lam` with lower-line lock

`G(1 − s) = κ₀ e^{iθ(x)} G(s)`,  `s = ½ − 2ix`, `x > 0`,

where `θ` is `C¹` and deviates from a line by a function of sublinear variation:
`θ(x) = ηx + Θ(V(x))` with `Θ` Lipschitz and `V` monotone, `V(x) = O(x^α)`, `α < 1`.

**Theorem** (`lock_phase_variation_rigidity`).  Then `η = 0`, `lam(n) = Λ(n)` for `n ≥ 2`, and
RH holds.

The hypothesis covers every `C¹` phase `θ = ηx + ψ` whose deviation `ψ` has total variation
`O(x^α)` on `[0, x]` (take `V` = the variation and `Θ` its 1-Lipschitz inverse profile).  It
contains the monotone twists (`abelian_twist_power_rigidity`, `linear_twist_rigidity`), the
two-sided fractional phases (`fractional_two_sided_power_growth_rigidity`) when `C¹`, and the
sublinear `C¹` phases (`lock_phase_rigidity`).

**Proof.**
* Positivity (`deriv_lock_phase_nonneg`) makes `θ` nondecreasing.  If `η < 0`, then
  `θ(x) ≤ ηx + O(x^α) → −∞`, which is impossible.  So `η ≥ 0`.
* `e^{iΘ}` is a Lipschitz profile (`lipProfile_eq_add_setIntegral`), so the quantization theorem
  in profile form (`linear_twist_quantization_profile`) gives `e^{−η/2} ∈ ℕ`, i.e. `η ≤ 0`.
* With `η = 0` the phase `θ = Θ ∘ V` is `C¹` of power growth `α < 1`, and lock-phase rigidity
  (`lock_phase_rigidity`) applies.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### Lipschitz profiles -/

/-- The density of the profile `e^{iΘ}`: `(cos Θ)' + i (sin Θ)'`. -/
def lipDensity (Θ : ℝ → ℝ) (x : ℝ) : ℂ :=
  ((deriv (fun v => Real.cos (Θ v)) x : ℝ) : ℂ) + ((deriv (fun v => Real.sin (Θ v)) x : ℝ) : ℂ) * I

theorem measurable_lipDensity (Θ : ℝ → ℝ) : Measurable (lipDensity Θ) := by
  unfold lipDensity
  exact (Complex.measurable_ofReal.comp (measurable_deriv _)).add
    ((Complex.measurable_ofReal.comp (measurable_deriv _)).mul_const _)

theorem norm_lipDensity_le {Θ : ℝ → ℝ} {K : NNReal} (hΘ : LipschitzWith K Θ) (x : ℝ) :
    ‖lipDensity Θ x‖ ≤ 2 * K := by
  unfold lipDensity
  have h1 := norm_deriv_le_of_lipschitz (x₀ := x) (Real.lipschitzWith_cos.comp hΘ)
  have h2 := norm_deriv_le_of_lipschitz (x₀ := x) (Real.lipschitzWith_sin.comp hΘ)
  simp only [one_mul] at h1 h2
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
  have e1 : (fun v => Real.cos (Θ v)) = Real.cos ∘ Θ := rfl
  have e2 : (fun v => Real.sin (Θ v)) = Real.sin ∘ Θ := rfl
  rw [e1, e2]
  linarith

/-- **The fundamental theorem for a Lipschitz profile**: `e^{iΘ(b)} = e^{iΘ(a)} + ∫_{a < x ≤ b} ψ`. -/
theorem lipProfile_eq_add_setIntegral {Θ : ℝ → ℝ} {K : NNReal} (hΘ : LipschitzWith K Θ)
    {a b : ℝ} (hab : a ≤ b) :
    cexp ((Θ b : ℂ) * I) = cexp ((Θ a : ℂ) * I) +
      ∫ x in Ioi a, (if x ≤ b then lipDensity Θ x else 0) := by
  have hRe : LipschitzWith (1 * K) (fun v => Real.cos (Θ v)) := Real.lipschitzWith_cos.comp hΘ
  have hIm : LipschitzWith (1 * K) (fun v => Real.sin (Θ v)) := Real.lipschitzWith_sin.comp hΘ
  have fRe := (hRe.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have fIm := (hIm.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hset : ∫ x in Ioi a, (if x ≤ b then lipDensity Θ x else 0) = ∫ x in a..b, lipDensity Θ x := by
    rw [intervalIntegral.integral_of_le hab]
    have e1 : (fun x => if x ≤ b then lipDensity Θ x else 0) = (Iic b).indicator (lipDensity Θ) := by
      funext x; simp [Set.indicator_apply]
    rw [e1, setIntegral_indicator measurableSet_Iic]
    congr 1
  rw [hset]
  have hI1 := intervalIntegrable_deriv_profile hRe a b
  have hI2 := intervalIntegrable_deriv_profile hIm a b
  have hsplit : ∫ x in a..b, lipDensity Θ x =
      ((∫ x in a..b, deriv (fun v => Real.cos (Θ v)) x : ℝ) : ℂ) +
        ((∫ x in a..b, deriv (fun v => Real.sin (Θ v)) x : ℝ) : ℂ) * I := by
    unfold lipDensity
    have hI1' : IntervalIntegrable (fun x => ((deriv (fun v => Real.cos (Θ v)) x : ℝ) : ℂ))
        volume a b := ⟨hI1.1.ofReal, hI1.2.ofReal⟩
    have hI2' : IntervalIntegrable (fun x => ((deriv (fun v => Real.sin (Θ v)) x : ℝ) : ℂ))
        volume a b := ⟨hI2.1.ofReal, hI2.2.ofReal⟩
    rw [intervalIntegral.integral_add hI1' (hI2'.mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  rw [hsplit, fRe, fIm]
  have hdecomp : ∀ v : ℝ, cexp ((Θ v : ℂ) * I) =
      ((Real.cos (Θ v) : ℝ) : ℂ) + ((Real.sin (Θ v) : ℝ) : ℂ) * I := by
    intro v
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hdecomp, hdecomp]
  push_cast
  ring

/-! ### The theorem -/

/-- **Lock phases of sublinear variation around a line.**  Let `G` be a Herglotz producer for the
weights `lam` with lower-line lock `G(1 − s) = κ₀ e^{iθ(−τ)} G(s)`, `s = ½ + 2iτ`, `τ < 0`, where
`θ` is `C¹` and `θ(x) = ηx + Θ(V(x))` for `x > 0`, with `Θ` Lipschitz, `V` monotone and
`V(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`.  Then `η = 0`, `lam(n) = Λ(n)` for all `n ≥ 2`,
and RH holds. -/
theorem lock_phase_variation_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {θ : ℝ → ℝ} (hθd : Differentiable ℝ θ) (hθc : Continuous (deriv θ))
    {η : ℝ} {Θ : ℝ → ℝ} {KΘ : NNReal} (hΘ : LipschitzWith KΘ Θ) {V : ℝ → ℝ} (hV : Monotone V)
    (hVg : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → V x ≤ K * x ^ α)
    (hθ : ∀ x : ℝ, 0 < x → θ x = η * x + Θ (V x)) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * cexp ((θ (-τ) : ℂ) * I) * G (lineS τ)) :
    η = 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  obtain ⟨α, K, hα1, hVK⟩ := hVg
  -- a common sublinear bound for `Θ ∘ V`
  set α' : ℝ := max α 0 with hα'
  have hα'1 : α' < 1 := max_lt hα1 (by norm_num)
  set K₃ : ℝ := |Θ (V 1)| + KΘ * (|V 1| + |K|) with hK₃
  have hΘV : ∀ x : ℝ, 1 ≤ x → Θ (V x) ≤ K₃ * x ^ α' := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hp : 1 ≤ x ^ α' := Real.one_le_rpow hx (le_max_right _ _)
    have hpα : x ^ α ≤ x ^ α' := Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
    have h1 : |Θ (V x) - Θ (V 1)| ≤ KΘ * |V x - V 1| := by
      have := hΘ.dist_le_mul (V x) (V 1)
      rwa [Real.dist_eq, Real.dist_eq] at this
    have h2 : |V x - V 1| ≤ |V 1| + |K| * x ^ α' := by
      have hV1 : V 1 ≤ V x := hV hx
      rw [abs_of_nonneg (by linarith)]
      have := hVK x hx
      have h3 : K * x ^ α ≤ |K| * x ^ α' :=
        (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hx0.le _)).trans
          (mul_le_mul_of_nonneg_left hpα (abs_nonneg K))
      linarith [neg_abs_le (V 1)]
    have hK0 : (0 : ℝ) ≤ KΘ := KΘ.2
    calc Θ (V x) ≤ Θ (V 1) + KΘ * |V x - V 1| := by linarith [(abs_le.mp h1).2]
      _ ≤ |Θ (V 1)| + KΘ * (|V 1| + |K| * x ^ α') := by
          gcongr
          exact le_abs_self _
      _ ≤ |Θ (V 1)| * x ^ α' + KΘ * (|V 1| * x ^ α' + |K| * x ^ α') := by
          gcongr
          · exact le_mul_of_one_le_right (abs_nonneg _) hp
          · exact le_mul_of_one_le_right (abs_nonneg _) hp
      _ = K₃ * x ^ α' := by rw [hK₃]; ring
  -- positivity: `θ` is nondecreasing
  have hlock' : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) =
      κ₀ * cexp ((θ x : ℂ) * I) * G (vpt (1 / 2) x) := by
    intro x hx
    have h := hlock (-x) (by linarith)
    rwa [neg_neg, lineS_neg_eq_vpt] at h
  have hmono : MonotoneOn θ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hθd.continuous.continuousOn
      hθd.differentiableOn fun x hx => ?_
    rw [interior_Ici] at hx
    exact deriv_lock_phase_nonneg hsl hΦd hΦre hidT hGc hGd hG2 hθd hθc hlock' hx
  -- `η ≥ 0`
  have hη0 : 0 ≤ η := by
    by_contra hneg
    push Not at hneg
    have hc : 0 < -η / 2 := by linarith
    obtain ⟨Y, hY⟩ := eventually_sublinear_lt (C := fun x => Θ (V x)) hα'1 hΘV hc 1
    set y : ℝ := max Y (2 + 2 * (|θ 1| + |Θ (V 1)| + 1) / (-η)) with hy
    have hyY : Y ≤ y := le_max_left _ _
    have hy2 : 2 + 2 * (|θ 1| + |Θ (V 1)| + 1) / (-η) ≤ y := le_max_right _ _
    have hy1 : 1 ≤ y := by
      have : 0 ≤ 2 * (|θ 1| + |Θ (V 1)| + 1) / (-η) := div_nonneg (by positivity) (by linarith)
      linarith
    have h1 := hY y hyY
    have h2 : θ 1 ≤ θ y := hmono (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ y by linarith) hy1
    rw [hθ y (by linarith), hθ 1 one_pos] at h2
    have h3 : (-η) * (y - 2) ≥ 2 * (|θ 1| + |Θ (V 1)| + 1) := by
      have hη' : (0 : ℝ) < -η := by linarith
      have h4 : 2 * (|θ 1| + |Θ (V 1)| + 1) / (-η) ≤ y - 2 := by linarith
      rw [div_le_iff₀ hη'] at h4
      linarith
    nlinarith [abs_nonneg (θ 1), abs_nonneg (Θ (V 1)), le_abs_self (Θ (V 1)),
      neg_abs_le (Θ (V 1))]
  -- quantization: `η ≤ 0`
  have hlockΨ : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * cexp ((Θ (V (-τ)) : ℂ) * I) * G (lineS τ) := by
    intro τ hτ
    rw [hlock τ hτ, hθ (-τ) (by linarith)]
    have e : cexp ((((η * -τ + Θ (V (-τ)) : ℝ)) : ℂ) * I) =
        cexp (((η * (-τ) : ℝ) : ℂ) * I) * cexp ((Θ (V (-τ)) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  obtain ⟨n, hn⟩ := linear_twist_quantization_profile hsl hΦd hΦre hid hGc hGd hG2 hV
    ⟨α, K, hα1, hVK⟩ (Ψ := fun v => cexp ((Θ v : ℂ) * I)) (ψ := lipDensity Θ) (L := 2 * KΘ)
    (M := 1) (by positivity) (measurable_lipDensity Θ) (norm_lipDensity_le hΘ)
    (fun _ _ huv => lipProfile_eq_add_setIntegral hΘ huv)
    (by have := hΘ.continuous; fun_prop) (fun v => (Complex.norm_exp_ofReal_mul_I _).le)
    hlockΨ
  have hpos : (0 : ℝ) < n := by rw [hn]; exact Real.exp_pos _
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hpos
    exact_mod_cast this
  have hηle : η ≤ 0 := by
    have : 0 ≤ -(η / 2) := by rw [← Real.exp_le_exp, Real.exp_zero, ← hn]; exact hn1
    linarith
  have hη : η = 0 := le_antisymm hηle hη0
  -- the sublinear case
  refine ⟨hη, lock_phase_rigidity hsl hΦd hΦre hid hGc hGd hG2 hθd hθc
    ⟨α', K₃, hα'1, fun x hx => ?_⟩ hlock |>.2⟩
  rw [hθ x (by linarith), hη, zero_mul, zero_add]
  exact hΘV x hx

end

end AbelianTwist

end RHTower
