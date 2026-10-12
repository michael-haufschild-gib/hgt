import GaloisForLFunctions.RHTower.XiGaussianHeatSharpWitness
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowWeilMarginAsymptotics

/-!
# The sharp witness: asymptotic bounds

With `t` the moment ratio at index `n + 1`, order `k` and radius `X` (`heatMomentRatio`), and
`E = 4eπ e^{X²}`, for an even polynomial `Q` of degree `≤ 2n`, `g = Q e^{-x²/(2a)}`:

* `(∫_{|x| ≥ X} |g| e^{|x|/2})² ≤ E tᵏ ∫ g²` (`sq_stripMassOn_tail_le`);
* `(∫ |g''| e^{|x|/2})² ≤ E (4β(2n+3))² ∫ g²`, `β = 1/(2a)` (`sq_stripMass_dd_le`);

and for the smoothed source `∫ |u_a| e^{|x|/2} ≤ 2X ‖u‖_∞ e^{X/2} + 4‖u‖₁` (`stripMass_heatSmooth_le`).
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly sq_setIntegral_tail_abs_gaussPolyFun_mul_exp_half_le
  sq_integral_abs_gaussPolyFun_mul_exp_half_le integral_gaussPolyFun_derivPoly_sq_le)

namespace RHTower

noncomputable section

theorem sq_stripMassOn_tail_le {Q : ℝ[X]} {n : ℕ} (hQ : Q.natDegree ≤ 2 * n) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) {X : ℝ} (hX : 0 < X) (k : ℕ)
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) :
    stripMassOn (gaussPolyFun Q (1 / (2 * a))) (heatTailSet X) ^ 2 ≤
      heatStripConstant X * heatMomentRatio (n + 1) k a X ^ k *
        ∫ x, gaussPolyFun Q (1 / (2 * a)) x ^ 2 := by
  have hβ : 1 / 2 < 1 / (2 * a) := half_lt_inv_two_mul ha ha1
  have hd : Q.natDegree ≤ 2 * (n + 1) + 1 := by omega
  have hr : ((Q.natDegree + k) / ((1 / (2 * a) - 1 / 2) * X ^ 2) : ℝ) ^ k ≤
      heatMomentRatio (n + 1) k a X ^ k :=
    pow_le_pow_left₀ (by have : 0 < 1 / (2 * a) - 1 / 2 := by linarith
                         positivity) (ratio_le_heatMomentRatio hd ha ha1 hX) k
  have h : (1 - ((Q.natDegree + k) / ((1 / (2 * a) - 1 / 2) * X ^ 2) : ℝ) ^ k) *
      stripMassOn (gaussPolyFun Q (1 / (2 * a))) (heatTailSet X) ^ 2 ≤
      2 * Real.exp 1 * π * ((Q.natDegree + k) / ((1 / (2 * a) - 1 / 2) * X ^ 2) : ℝ) ^ k *
        Real.exp (X ^ 2) * ∫ x, gaussPolyFun Q (1 / (2 * a)) x ^ 2 :=
    (sq_setIntegral_tail_abs_gaussPolyFun_mul_exp_half_le Q hβ hX k ((hr.trans hk).trans_lt
      (by norm_num))).2
  have hc : 0 ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) := by positivity
  have hV : 0 ≤ ∫ x, gaussPolyFun Q (1 / (2 * a)) x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h' := sq_le_of_one_sub_mul_le (c := 2 * Real.exp 1 * π * Real.exp (X ^ 2))
    (h.trans_eq (by ring)) hr hk hc hV
  have hE : heatStripConstant X = 2 * (2 * Real.exp 1 * π * Real.exp (X ^ 2)) := by
    unfold heatStripConstant; ring
  rw [hE]
  exact h'.trans_eq (by ring)

theorem sq_stripMass_dd_le {Q : ℝ[X]} {n : ℕ} (hQ : Q.natDegree ≤ 2 * n) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) {X : ℝ} (hX : 0 < X) (k : ℕ)
    (hk : heatMomentRatio (n + 1) k a X ^ k ≤ 1 / 2) :
    stripMass (gaussPolyFun (gaussPolyDerivPoly (gaussPolyDerivPoly Q (1 / (2 * a))) (1 / (2 * a)))
        (1 / (2 * a))) ^ 2 ≤
      heatStripConstant X * (4 * (1 / (2 * a)) * (2 * n + 3)) ^ 2 *
        ∫ x, gaussPolyFun Q (1 / (2 * a)) x ^ 2 := by
  have hβ : 1 / 2 < 1 / (2 * a) := half_lt_inv_two_mul ha ha1
  have hβ0 : 0 < 1 / (2 * a) := by linarith
  set β := 1 / (2 * a) with hβ_def
  set Q₁ := gaussPolyDerivPoly Q β
  set Q₂ := gaussPolyDerivPoly Q₁ β
  have hd1 : Q₁.natDegree ≤ 2 * n + 1 := (natDegree_gaussPolyDerivPoly_le Q β).trans (by omega)
  have hd2 : Q₂.natDegree ≤ 2 * (n + 1) + 1 :=
    (natDegree_gaussPolyDerivPoly_le Q₁ β).trans (by omega)
  have hr : ((Q₂.natDegree + k) / ((β - 1 / 2) * X ^ 2) : ℝ) ^ k ≤
      heatMomentRatio (n + 1) k a X ^ k :=
    pow_le_pow_left₀ (by have : 0 < β - 1 / 2 := by linarith
                         positivity) (ratio_le_heatMomentRatio hd2 ha ha1 hX) k
  have h : (1 - ((Q₂.natDegree + k) / ((β - 1 / 2) * X ^ 2) : ℝ) ^ k) *
      stripMass (gaussPolyFun Q₂ β) ^ 2 ≤
      2 * Real.exp 1 * π * Real.exp (X ^ 2) * ∫ x, gaussPolyFun Q₂ β x ^ 2 :=
    (sq_integral_abs_gaussPolyFun_mul_exp_half_le Q₂ hβ hX k).2
  have h' := sq_le_of_one_sub_mul_le' h (hr.trans hk)
  have hV1 : ∫ x, gaussPolyFun Q₂ β x ^ 2 ≤ 4 * β * (Q₁.natDegree + 1) *
      ∫ x, gaussPolyFun Q₁ β x ^ 2 := integral_gaussPolyFun_derivPoly_sq_le Q₁ hβ0
  have hV2 : ∫ x, gaussPolyFun Q₁ β x ^ 2 ≤ 4 * β * (Q.natDegree + 1) *
      ∫ x, gaussPolyFun Q β x ^ 2 := integral_gaussPolyFun_derivPoly_sq_le Q hβ0
  have hV : 0 ≤ ∫ x, gaussPolyFun Q β x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hV1' : 0 ≤ ∫ x, gaussPolyFun Q₁ β x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hd1' : ((Q₁.natDegree : ℝ) + 1) ≤ 2 * n + 3 := by
    have : (Q₁.natDegree : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hd1
    linarith
  have hd0' : ((Q.natDegree : ℝ) + 1) ≤ 2 * n + 3 := by
    have : (Q.natDegree : ℝ) ≤ 2 * n := by exact_mod_cast hQ
    linarith
  have hc : 0 ≤ 2 * Real.exp 1 * π * Real.exp (X ^ 2) := by positivity
  have hY : 0 ≤ 4 * β * (2 * n + 3) := by positivity
  have hchain : ∫ x, gaussPolyFun Q₂ β x ^ 2 ≤ (4 * β * (2 * n + 3)) ^ 2 *
      ∫ x, gaussPolyFun Q β x ^ 2 := by
    calc ∫ x, gaussPolyFun Q₂ β x ^ 2 ≤ 4 * β * (Q₁.natDegree + 1) * ∫ x, gaussPolyFun Q₁ β x ^ 2 :=
          hV1
      _ ≤ 4 * β * (2 * n + 3) * ∫ x, gaussPolyFun Q₁ β x ^ 2 := by gcongr
      _ ≤ 4 * β * (2 * n + 3) * (4 * β * (Q.natDegree + 1) * ∫ x, gaussPolyFun Q β x ^ 2) := by
          gcongr
      _ ≤ 4 * β * (2 * n + 3) * (4 * β * (2 * n + 3) * ∫ x, gaussPolyFun Q β x ^ 2) := by gcongr
      _ = _ := by ring
  have hE : heatStripConstant X = 2 * (2 * Real.exp 1 * π * Real.exp (X ^ 2)) := by
    unfold heatStripConstant; ring
  rw [hE]
  calc stripMass (gaussPolyFun Q₂ β) ^ 2 ≤ 2 * (2 * Real.exp 1 * π * Real.exp (X ^ 2)) *
        ∫ x, gaussPolyFun Q₂ β x ^ 2 := h'
    _ ≤ 2 * (2 * Real.exp 1 * π * Real.exp (X ^ 2)) *
        ((4 * β * (2 * n + 3)) ^ 2 * ∫ x, gaussPolyFun Q β x ^ 2) := by gcongr
    _ = _ := by ring

variable {u : ℝ → ℝ} {A a : ℝ}

/-- `∫ |u_a| e^{|x|/2} ≤ 2X B e^{X/2} + 4‖u‖₁` for `|u| ≤ B`, `a ≤ 1/16`, `X ≥ max(1, 2A)`. -/
theorem stripMass_heatSmooth_le (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) (ha : 0 < a) (ha16 : a ≤ 1 / 16) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) {X : ℝ} (hX1 : 1 ≤ X) (hXA : 2 * A ≤ X) :
    stripMass (heatSmooth a u) ≤ 2 * X * (B * Real.exp (X / 2)) + 4 * ∫ t, |u t| := by
  have hint := integrable_abs_heatSmooth_mul_exp ha ha16 hu hcpt hsupp
  obtain ⟨-, htail⟩ := integrableOn_tail_heatSmooth hu hcpt hsupp ha ha16 hX1 hXA
  have hsplit := integral_add_compl (measurableSet_heatTailSet X) hint
  rw [heatTailSet_compl] at hsplit
  have hinner : ∫ x in Ioo (-X) X, |heatSmooth a u x| * Real.exp (|x| / 2) ≤
      ∫ x in Ioo (-X) X, B * Real.exp (X / 2) := by
    refine setIntegral_mono_on hint.integrableOn (integrableOn_const measure_Ioo_lt_top.ne)
      measurableSet_Ioo fun x hx => ?_
    have hxX : |x| ≤ X := (abs_lt.2 ⟨hx.1, hx.2⟩).le
    have h1 := abs_heatSmooth_le_sup ha hB x
    have h2 : Real.exp (|x| / 2) ≤ Real.exp (X / 2) := Real.exp_le_exp.2 (by linarith)
    exact mul_le_mul h1 h2 (Real.exp_pos _).le ((abs_nonneg _).trans h1)
  rw [setIntegral_const, Real.volume_real_Ioo, smul_eq_mul,
    show X - -X = 2 * X by ring, max_eq_left (by linarith)] at hinner
  have he : Real.exp (-(X ^ 2 / (32 * a))) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ X ^ 2 / (32 * a) := by positivity
    linarith)
  have hU : 0 ≤ ∫ t, |u t| := integral_nonneg fun _ => abs_nonneg _
  rw [stripMass, ← hsplit]
  have h4 : 4 * (∫ t, |u t|) * Real.exp (-(X ^ 2 / (32 * a))) ≤ 4 * ∫ t, |u t| := by
    have := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 4 * ∫ t, |u t|)
    linarith
  linarith

/-- `∫ u_a² ≤ B ∫ |u_a| e^{|x|/2}`. -/
theorem integral_heatSmooth_sq_le (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    (hsupp : ∀ t : ℝ, A < |t| → u t = 0) (ha : 0 < a) (ha16 : a ≤ 1 / 16) {B : ℝ}
    (hB : ∀ t, |u t| ≤ B) :
    Integrable (fun x => heatSmooth a u x ^ 2) ∧
      ∫ x, heatSmooth a u x ^ 2 ≤ B * stripMass (heatSmooth a u) := by
  have hint := integrable_abs_heatSmooth_mul_exp ha ha16 hu hcpt hsupp
  have hpt : ∀ x, heatSmooth a u x ^ 2 ≤ B * (|heatSmooth a u x| * Real.exp (|x| / 2)) := fun x => by
    have h1 := abs_heatSmooth_le_sup ha hB x
    have h2 : 1 ≤ Real.exp (|x| / 2) := Real.one_le_exp (by positivity)
    rw [← sq_abs]
    have h3 := abs_nonneg (heatSmooth a u x)
    calc |heatSmooth a u x| ^ 2 = |heatSmooth a u x| * |heatSmooth a u x| := sq _
      _ ≤ B * |heatSmooth a u x| := mul_le_mul_of_nonneg_right h1 h3
      _ ≤ B * (|heatSmooth a u x| * Real.exp (|x| / 2)) := by
          have hB0 : 0 ≤ B := h3.trans h1
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h3 h2) hB0
  have hi : Integrable (fun x => heatSmooth a u x ^ 2) :=
    (hint.const_mul B).mono' ((continuous_heatSmooth hu hcpt ha).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt x)
  refine ⟨hi, ?_⟩
  rw [stripMass, ← integral_const_mul]
  exact integral_mono hi (hint.const_mul B) hpt

/-- `∫ |u(sτ)| dτ = ‖u‖₁/s`. -/
theorem integral_norm_scaledSource (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u)
    {s : ℝ} (hs : 0 < s) :
    ∫ τ : ℝ, ‖scaledSource u hu hcpt hs.ne' τ‖ = (∫ t, |u t|) / s := by
  simp only [scaledSource_apply, Complex.norm_real, Real.norm_eq_abs]
  have h := Measure.integral_comp_mul_left (fun t : ℝ => |u t|) s
  rw [h, smul_eq_mul, abs_inv, abs_of_pos hs, inv_mul_eq_div]

/-- Splitting the strip mass of a difference at `|x| = X`. -/
theorem stripMass_sub_le {f₁ f₂ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (i₁ : Integrable (fun x => |f₁ x| * Real.exp (|x| / 2)))
    (i₂ : Integrable (fun x => |f₂ x| * Real.exp (|x| / 2))) (X : ℝ) :
    stripMass (fun x => f₁ x - f₂ x) ≤ (∫ x in Ioo (-X) X, |f₁ x - f₂ x| * Real.exp (|x| / 2)) +
      stripMassOn f₁ (heatTailSet X) + stripMassOn f₂ (heatTailSet X) := by
  have hi : Integrable (fun x => |f₁ x - f₂ x| * Real.exp (|x| / 2)) := by
    refine (i₁.add i₂).mono' ((continuous_abs.comp (h₁.sub h₂)).mul (Real.continuous_exp.comp
      (continuous_abs.div_const 2))).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_sub _ _) (Real.exp_pos _).le
  have hsplit := integral_add_compl (measurableSet_heatTailSet X) hi
  rw [heatTailSet_compl] at hsplit
  have htail : ∫ x in heatTailSet X, |f₁ x - f₂ x| * Real.exp (|x| / 2) ≤
      stripMassOn f₁ (heatTailSet X) + stripMassOn f₂ (heatTailSet X) := by
    rw [stripMassOn, stripMassOn, ← integral_add i₁.integrableOn i₂.integrableOn]
    refine setIntegral_mono_on hi.integrableOn (i₁.integrableOn.add i₂.integrableOn)
      (measurableSet_heatTailSet X) fun x _ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_sub _ _) (Real.exp_pos _).le
  rw [stripMass, ← hsplit]
  linarith

/-- **Collecting the error.**  With `N ≤ ι + τ_g + τ_u`, `τ_g ≤ √E σ G`, `M ≤ √E Y G`, `n/K ≤ Y`,
the comparison error is at most
`(√E G (ιY + τ_u Y) + E G² σY)(1 + 2c) S₂ + (ι + τ_u + √E G σ) c U S₂ + 3(ι²(1+Y) + τ_u²(1+Y) + E G² (σ² + σ·σY)) e S`,
`c = e^{1/8}`, `e = e^{1/2}`. -/
theorem comparison_error_le {N M ι τg τu σ Y G E U S₂ S n K c e : ℝ} (hN0 : 0 ≤ N)
    (hι : 0 ≤ ι) (hτu : 0 ≤ τu) (hσ : 0 ≤ σ) (hG : 0 ≤ G)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hS₂ : 0 ≤ S₂) (hS : 0 ≤ S) (hc : 0 ≤ c) (he : 0 ≤ e) (hn : 0 ≤ n / K)
    (hnY : n / K ≤ Y) (hN : N ≤ ι + τg + τu) (hτg : τg ≤ Real.sqrt E * σ * G)
    (hM : M ≤ Real.sqrt E * Y * G) (hM0 : 0 ≤ M) :
    N * (M + c * U) * S₂ + N * (2 * (c * M * S₂) + N * (e * (1 + n / K) * S)) ≤
      (Real.sqrt E * G * (ι * Y + τu * Y) + E * G ^ 2 * (σ * Y)) * (1 + 2 * c) * S₂ +
        (ι + τu + Real.sqrt E * G * σ) * c * U * S₂ +
        3 * (ι ^ 2 * (1 + Y) + τu ^ 2 * (1 + Y) + E * G ^ 2 * (σ ^ 2 + σ * (σ * Y))) * e * S := by
  have hsE : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have hsE0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hNM : N * M ≤ Real.sqrt E * G * (ι * Y + τu * Y) + E * G ^ 2 * (σ * Y) := by
    calc N * M ≤ (ι + Real.sqrt E * σ * G + τu) * (Real.sqrt E * Y * G) :=
          mul_le_mul (hN.trans (by linarith)) hM hM0 (by positivity)
      _ = Real.sqrt E * G * (ι * Y + τu * Y) + Real.sqrt E ^ 2 * G ^ 2 * (σ * Y) := by ring
      _ = _ := by rw [hsE]
  have hN' : N ≤ ι + τu + Real.sqrt E * G * σ := by nlinarith
  have hN2 : N ^ 2 * (1 + n / K) ≤ 3 * (ι ^ 2 * (1 + Y) + τu ^ 2 * (1 + Y) +
      E * G ^ 2 * (σ ^ 2 + σ * (σ * Y))) := by
    have h1 : N ^ 2 ≤ 3 * (ι ^ 2 + τu ^ 2 + E * G ^ 2 * σ ^ 2) := by
      have h3 : N ^ 2 ≤ (ι + τu + Real.sqrt E * G * σ) ^ 2 := pow_le_pow_left₀ hN0 hN' 2
      have h4 : (ι + τu + Real.sqrt E * G * σ) ^ 2 ≤ 3 * (ι ^ 2 + τu ^ 2 + (Real.sqrt E * G * σ) ^ 2) := by
        nlinarith [sq_nonneg (ι - τu), sq_nonneg (ι - Real.sqrt E * G * σ),
          sq_nonneg (τu - Real.sqrt E * G * σ)]
      have h5 : (Real.sqrt E * G * σ) ^ 2 = E * G ^ 2 * σ ^ 2 := by
        rw [mul_pow, mul_pow, hsE]
      linarith
    have h6 : 1 + n / K ≤ 1 + Y := by linarith
    have h7 : E * G ^ 2 * σ ^ 2 * (1 + Y) = E * G ^ 2 * (σ ^ 2 + σ * (σ * Y)) := by ring
    calc N ^ 2 * (1 + n / K) ≤ 3 * (ι ^ 2 + τu ^ 2 + E * G ^ 2 * σ ^ 2) * (1 + Y) :=
          mul_le_mul h1 h6 (by positivity) (by positivity)
      _ = _ := by rw [show 3 * (ι ^ 2 + τu ^ 2 + E * G ^ 2 * σ ^ 2) * (1 + Y) =
            3 * (ι ^ 2 * (1 + Y) + τu ^ 2 * (1 + Y) + E * G ^ 2 * σ ^ 2 * (1 + Y)) by ring, h7]
  have e1 : N * (M + c * U) * S₂ + N * (2 * (c * M * S₂) + N * (e * (1 + n / K) * S)) =
      N * M * (1 + 2 * c) * S₂ + N * c * U * S₂ + N ^ 2 * (1 + n / K) * e * S := by ring
  rw [e1]
  have t1 : N * M * (1 + 2 * c) * S₂ ≤
      (Real.sqrt E * G * (ι * Y + τu * Y) + E * G ^ 2 * (σ * Y)) * (1 + 2 * c) * S₂ := by gcongr
  have t2 : N * c * U * S₂ ≤ (ι + τu + Real.sqrt E * G * σ) * c * U * S₂ := by gcongr
  have t3 : N ^ 2 * (1 + n / K) * e * S ≤ 3 * (ι ^ 2 * (1 + Y) + τu ^ 2 * (1 + Y) +
      E * G ^ 2 * (σ ^ 2 + σ * (σ * Y))) * e * S := by gcongr
  linarith

end

end RHTower
