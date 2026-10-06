import GaloisForLFunctions.RHTower.KuznetsovEisensteinGrowth
import GaloisForLFunctions.RHTower.SmoothHeightProfileMellin
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# Shifting the Poincaré–Eisenstein line integral to the critical line

For a smooth height profile `ψ`, `F(s) = ψ̂(s) Φ(s)` with the explicit Poincaré–Eisenstein pairing
`Φ` is holomorphic on `½ < Re s < Re s₁` (the Eisenstein coefficients `D_n(s)` are holomorphic there
and the frequency `μ ≠ 0` coefficient carries no pole at `s = 1`) and `O((1+t²)⁻¹)` uniformly on
`½ < Re s ≤ σ₀` (super-polynomial decay of `ψ̂` against polynomial growth of `Φ`).  Cauchy's theorem
moves the line `Re s = σ₀` to `Re s = ½ + ε`, and dominated convergence lets `ε → 0`:

`∫ ψ̂(σ₀+it) Φ(σ₀+it) dt = ∫ ψ̂(½+it) Φ(½+it) dt` (`integral_line_eq_integral_half`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

theorem differentiableAt_eisCoeff (v w : DeckSpace N) (n : ℤ) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hs1 : s ≠ 1 / 2) : DifferentiableAt ℂ (fun s => eisCoeff s v w n) s := by
  unfold eisCoeff
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun q _ =>
    DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun g _ =>
      DifferentiableAt.const_mul ?_ _) _) _
  refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_)
    (SelbergEisensteinCoefficientSeries.differentiableAt_Dn_of_half_le (N + 1) _ n hs hs1)
  · exact (differentiableAt_id.neg.mul_const _).cexp
  · refine DifferentiableAt.mul (DifferentiableAt.mul ((differentiableAt_id.const_cpow
      (Or.inl hpi)).const_mul 2) ?_) ?_
    · have h := (Complex.differentiable_one_div_Gamma s)
      simpa only [one_div] using h
    · by_cases hn : n = 0
      · subst hn
        simp only [Int.cast_zero, abs_zero, Complex.ofReal_zero]
        refine DifferentiableAt.mul_const ?_ _
        exact ((differentiableAt_id.sub_const _).const_cpow (Or.inr (by
          intro h; exact hs1 (sub_eq_zero.mp h))))
      · have hne : (((|(n : ℝ)| : ℝ) : ℂ)) ≠ 0 := by
          exact_mod_cast (abs_pos.mpr (by exact_mod_cast hn : (n : ℝ) ≠ 0)).ne'
        exact (((differentiableAt_id.sub_const _).const_cpow (Or.inl hne))).mul_const _

theorem differentiableAt_poincEisPairing {s₁ : ℂ} (μ : ℝ) (v w : DeckSpace N) (n : ℤ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1 / 2) (hss : s.re < s₁.re) :
    DifferentiableAt ℂ (poincEisPairing s₁ μ v w n) s := by
  unfold poincEisPairing
  have hG1 : DifferentiableAt ℂ (fun s => Complex.Gamma (conj s₁ - 1 / 2 + (s - 1 / 2))) s := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp s
      ((differentiableAt_id.sub_const _).const_add _)
    have := congrArg Complex.re h
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG2 : DifferentiableAt ℂ (fun s => Complex.Gamma (conj s₁ - 1 / 2 - (s - 1 / 2))) s := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp s
      ((differentiableAt_id.sub_const _).const_sub _)
    have := congrArg Complex.re h
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  refine DifferentiableAt.const_mul (DifferentiableAt.mul (DifferentiableAt.mul_const
    (differentiableAt_eisCoeff v w n hs hs1) _) ?_) _
  exact ((((differentiableAt_const _).mul hG1).mul hG2).div_const _)

/-- **Decay of `ψ̂ Φ`** on `½ < Re s ≤ σ₀`: `‖ψ̂(s)Φ(s)‖ ≤ C (1 + (Im s)²)⁻¹`. -/
theorem exists_bound_hMellin_mul_poincEisPairing {s₁ : ℂ} (hs₁ : 1 < s₁.re) (μ : ℝ)
    (v w : DeckSpace N) {n : ℤ} (hn : n ≠ 0) (ψ : SmoothHeightProfile) {σ₀ : ℝ}
    (hσ₀s : σ₀ < s₁.re) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ σ₀ →
      ‖hMellin ψ.toFun s * poincEisPairing s₁ μ v w n s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨CΦ, K, hCΦ, hΦ⟩ := exists_bound_poincEisPairing hs₁ μ v w hn hσ₀s
  obtain ⟨Cψ, hCψ, hψ⟩ := ψ.exists_bound_hMellin_pow (K + 2) (1 / 2) σ₀
  refine ⟨Cψ * CΦ, by positivity, fun s hs hsσ => ?_⟩
  have h1 := hΦ s hs hsσ
  have h2 := hψ s hs.le hsσ
  set x := 1 + |s.im|
  have hx : 1 ≤ x := by simp only [x]; linarith [abs_nonneg s.im]
  have hxK : 0 < x ^ K := by positivity
  have hsq : 1 + s.im ^ 2 ≤ x ^ 2 := by
    simp only [x]; nlinarith [abs_nonneg s.im, sq_abs s.im]
  rw [norm_mul]
  have hA : ‖hMellin ψ.toFun s‖ ≤ Cψ / x ^ (K + 2) := by
    rw [le_div_iff₀ (by positivity)]; exact h2
  have h1' : ‖poincEisPairing s₁ μ v w n s‖ ≤ CΦ * x ^ K := by
    refine h1.trans ?_
    have : Real.exp (-(Real.pi * |s.im| / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := Real.pi_pos; have := abs_nonneg s.im; nlinarith)
    have : 0 ≤ CΦ * x ^ K := by positivity
    nlinarith
  calc ‖hMellin ψ.toFun s‖ * ‖poincEisPairing s₁ μ v w n s‖
      ≤ Cψ / x ^ (K + 2) * (CΦ * x ^ K) :=
        mul_le_mul hA h1' (norm_nonneg _) (by positivity)
    _ = Cψ * CΦ / x ^ 2 := by
        rw [pow_add]; field_simp
    _ ≤ Cψ * CΦ * (1 + s.im ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        gcongr

/-- **The line integral moves to the critical line.** -/
theorem integral_line_eq_integral_half {s₁ : ℂ} (hs₁ : 1 < s₁.re) (μ : ℝ) (v w : DeckSpace N)
    {n : ℤ} (hn : n ≠ 0) (ψ : SmoothHeightProfile) {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀)
    (hσ₀s : σ₀ < s₁.re) :
    ∫ t : ℝ, hMellin ψ.toFun ((σ₀ : ℂ) + t * Complex.I) *
        poincEisPairing s₁ μ v w n ((σ₀ : ℂ) + t * Complex.I) =
      ∫ t : ℝ, hMellin ψ.toFun (1 / 2 + t * Complex.I) *
        poincEisPairing s₁ μ v w n (1 / 2 + t * Complex.I) := by
  set F : ℂ → ℂ := fun s => hMellin ψ.toFun s * poincEisPairing s₁ μ v w n s with hFdef
  obtain ⟨C, hC0, hC⟩ := exists_bound_hMellin_mul_poincEisPairing hs₁ μ v w hn ψ hσ₀s
  have hdiff : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ σ₀ → s ≠ 1 / 2 → DifferentiableAt ℂ F s :=
    fun s hs hsσ hs1 => (ψ.toHeightProfile.differentiable_hMellin s).mul
      (differentiableAt_poincEisPairing μ v w n hs hs1 (by linarith))
  have hline : ∀ x : ℝ, 1 / 2 < x → x ≤ σ₀ →
      Integrable fun t : ℝ => F ((x : ℂ) + t * Complex.I) := fun x hx hxσ => by
    refine integrable_line_of_bound (T₀ := 0) (C := C) (fun t => ?_) (fun t _ => ?_)
    · refine (hdiff _ (by simp; linarith) (by simp; linarith) fun h => ?_).continuousAt
      have := congrArg Complex.re h; simp at this; linarith
    · have := hC ((x : ℂ) + t * Complex.I) (by simpa using hx) (by simpa using hxσ)
      simpa [hFdef] using this
  have hshift : ∀ ε : ℝ, 0 < ε → ε ≤ σ₀ - 1 / 2 →
      ∫ t : ℝ, F ((σ₀ : ℂ) + t * Complex.I) = ∫ t : ℝ, F (((1 / 2 + ε : ℝ) : ℂ) + t * Complex.I) := by
    intro ε hε hεσ
    refine integral_vertical_line_eq_of_horizontal_tendsto (by linarith) (fun s hs => ?_)
      (hline _ (by linarith) (by linarith)) (hline _ hσ₀ le_rfl) ?_ ?_
    · rw [mem_verticalStrip] at hs
      refine (hdiff s (by linarith [hs.1]) hs.2 fun h => ?_).differentiableWithinAt
      have := congrArg Complex.re h; simp at this; linarith [hs.1]
    · refine tendsto_intervalIntegral_of_tendsto_bound (M := fun T => C * (1 + T ^ 2)⁻¹)
        (hgt := fun T => -T) (Eventually.of_forall fun T u hu => ?_) ?_
      · rw [uIoc_of_le (by linarith)] at hu
        have := hC ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) (by simp; linarith [hu.1])
          (by simp; linarith [hu.2])
        simpa [hFdef] using this
      · have h := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1
          (tendsto_pow_atTop (n := 2) two_ne_zero))).const_mul C
        simpa using h
    · refine tendsto_intervalIntegral_of_tendsto_bound (M := fun T => C * (1 + T ^ 2)⁻¹)
        (hgt := fun T => T) (Eventually.of_forall fun T u hu => ?_) ?_
      · rw [uIoc_of_le (by linarith)] at hu
        have := hC ((u : ℂ) + ((T : ℝ) : ℂ) * Complex.I) (by simp; linarith [hu.1])
          (by simp; linarith [hu.2])
        simpa [hFdef] using this
      · have h := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1
          (tendsto_pow_atTop (n := 2) two_ne_zero))).const_mul C
        simpa using h
  -- the limit `ε → 0`
  set ε : ℕ → ℝ := fun k => (σ₀ - 1 / 2) / (k + 1)
  have hε : ∀ k, 0 < ε k := fun k => div_pos (by linarith) (by positivity)
  have hεle : ∀ k, ε k ≤ σ₀ - 1 / 2 := fun k =>
    div_le_self (by linarith) (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (σ₀ - 1 / 2)
    refine (this.comp (tendsto_add_atTop_nat 1)).congr fun k => ?_
    simp [ε]
  have hlim : Tendsto (fun k => ∫ t : ℝ, F (((1 / 2 + ε k : ℝ) : ℂ) + t * Complex.I)) atTop
      (𝓝 (∫ t : ℝ, F (1 / 2 + t * Complex.I))) := by
    refine tendsto_integral_of_dominated_convergence (fun t => C * (1 + t ^ 2)⁻¹) (fun k => ?_)
      (integrable_inv_one_add_sq.const_mul C) (fun k => Eventually.of_forall fun t => ?_) ?_
    · exact (hline _ (by linarith [hε k]) (by linarith [hεle k])).aestronglyMeasurable
    · have := hC (((1 / 2 + ε k : ℝ) : ℂ) + t * Complex.I) (by simp; linarith [hε k])
        (by simp; linarith [hεle k])
      simpa [hFdef] using this
    · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hne] with t ht
      have hcont : ContinuousAt F (1 / 2 + t * Complex.I) := by
        refine (hdiff _ (by simp) (by simp; linarith) fun h => ht ?_).continuousAt
        have := congrArg Complex.im h; simpa using this
      have hpath : Tendsto (fun k => (((1 / 2 + ε k : ℝ) : ℂ) + t * Complex.I)) atTop
          (𝓝 (1 / 2 + t * Complex.I)) := by
        have h := ((Complex.continuous_ofReal.tendsto 0).comp hεlim).const_add
          ((1 / 2 : ℂ) + t * Complex.I)
        refine h.congr' (Eventually.of_forall fun k => ?_) |>.trans ?_
        · simp only [Function.comp_apply]; push_cast; ring
        · simp
      exact hcont.tendsto.comp hpath
  have hconst : (fun k => ∫ t : ℝ, F (((1 / 2 + ε k : ℝ) : ℂ) + t * Complex.I)) =
      fun _ => ∫ t : ℝ, F ((σ₀ : ℂ) + t * Complex.I) :=
    funext fun k => (hshift (ε k) (hε k) (hεle k)).symm
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end

end GaloisForLFunctions.RHTower.DeckPointPair
