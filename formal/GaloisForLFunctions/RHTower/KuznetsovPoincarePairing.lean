import GaloisForLFunctions.RHTower.KuznetsovPoincareRows

/-!
# The geometric side of Kuznetsov's formula

For `Re s₁, Re s₂ > 1`, `μ, ν > 0`, a cusp vector `v` of frequency `μ` and a cusp vector `w` of
frequency `−ν`, the pairing of the deck Poincaré series `U(·| s₁, μ, v)` with the conjugate series
`P(·| h̄_{s₂,ν}, w)` is

`∫_𝒟 ⟨U, P⟩ = 2 Σ_{(c,d) reduced} ⟨v, ρ(M_{c,d})⁻¹ w⟩ e((μd − νa)/c) (c²)^{−s̄₂}
  V(s̄₁, s̄₂; μ, ν, c²)`,

with Kuznetsov's value `V = 2 P^{α/2}(2πμ)^{−α} K_α(4π√(μν)/|c|) · π 2^{2−s̄₁−s̄₂} Γ(s̄₁+s̄₂−1)/
(Γ(s̄₁)Γ(s̄₂))`, `α = s̄₁ − s̄₂`, `P = 4π²μν/c²` (`kuzValue`).  The diagonal term vanishes; the
interchange of the row sum with the `y`-integral uses the bound `∫∫|K| ≤ C (c²)^δ` of Kuznetsov's kernel
with `max(0, Re s₂ − Re s₁) < δ < Re s₂ − 1` against `Σ_{(c,d) reduced} |c|^{−2 Re s₂ + 2δ} < ∞`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

instance : Countable ReducedRow := by unfold ReducedRow; infer_instance

/-- For a reduced row `0 ≤ d < |c|` the sup norm of `(c, d)` is `|c|`. -/
theorem norm_reducedRow (r : ReducedRow) : ‖r.1.1‖ = |(r.1.1 0 : ℝ)| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_) ?_
  · fin_cases i
    · simp [Int.norm_eq_abs]
    · simp only [Fin.mk_one, Fin.isValue, Int.norm_eq_abs]
      have h0 := r.2.2.1
      have h1 := r.2.2.2
      rw [← Int.cast_abs]
      exact_mod_cast (abs_of_nonneg h0).le.trans h1.le
  · have := norm_le_pi_norm r.1.1 0
    simpa [Int.norm_eq_abs] using this

/-- `Σ_{(c,d) reduced} (c²)^{−τ} < ∞` for `τ > 1`. -/
theorem summable_reducedRow_rpow {τ : ℝ} (hτ : 1 < τ) :
    Summable fun r : ReducedRow => (((r.1.1 0 : ℝ)) ^ 2) ^ (-τ) := by
  have hinj : Function.Injective fun r : ReducedRow => r.1.1 :=
    Subtype.val_injective.comp Subtype.val_injective
  refine ((summable_one_div_norm_rpow (k := 2 * τ) (by linarith)).comp_injective hinj).congr
    fun r => ?_
  simp only [Function.comp_apply, norm_reducedRow]
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  ring

/-- **The geometric side of Kuznetsov's formula.** -/
theorem integral_inner_poincSeries_conjProfile {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re) (hs₂ : 1 < s₂.re)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v)
    (hw : IsCuspEigen (-ν) w) :
    ∫ z in fd, ⟪poincSeries (poincProfile s₁ μ) v z, poincSeries (conjProfile s₂ ν) w z⟫_ℂ =
      2 * ∑' r : ReducedRow, rowWeight μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-conj s₂) *
        Kuznetsov.kuzValue (conj s₁) (conj s₂) μ ν ((r.1.1 0 : ℝ) ^ 2) := by
  have hGc := continuous_poincSeries_conjProfile hs₂ hν.le w
  have hGe := deckEquivariant_poincSeries (cuspCompatible_conjProfile s₂ hw)
  have hGL := memLp_poincSeries_conjProfile hs₂ hν w
  rw [integral_inner_poincSeries_eq_deckCuspCoeff hs₁ hμ hv hGc hGe hGL]
  congr 1
  have ha₁ : (conj s₁).re = s₁.re := Complex.conj_re s₁
  have ha₂ : (conj s₂).re = s₂.re := Complex.conj_re s₂
  -- the exponent `δ`
  set δ := (max 0 (s₂.re - s₁.re) + (s₂.re - 1)) / 2 with hδdef
  have hm0 := le_max_left 0 (s₂.re - s₁.re)
  have hm1 := le_max_right 0 (s₂.re - s₁.re)
  have hm2 : max 0 (s₂.re - s₁.re) < s₂.re - 1 := max_lt (by linarith) (by linarith)
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ₁ : (conj s₂).re - (conj s₁).re < δ := by rw [ha₁, ha₂, hδdef]; linarith
  have hδ₂ : δ < (conj s₂).re - 1 / 2 := by rw [ha₂, hδdef]; linarith
  have hδ₃ : 1 < s₂.re - δ := by rw [hδdef]; linarith
  have hc2 : ∀ r : ReducedRow, 0 < ((r.1.1 0 : ℝ)) ^ 2 := fun r => by
    have : (r.1.1 0 : ℝ) ≠ 0 := by exact_mod_cast r.2.1
    positivity
  -- the row functions
  set F : ReducedRow → ℝ → ℂ := fun r y => rowWeight μ ν v w r.1 *
    (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-conj s₂) *
      ∫ ξ, Kuznetsov.kuzKernel (conj s₁) (conj s₂) μ ν ((r.1.1 0 : ℝ) ^ 2) (y, ξ) with hFdef
  have hpt : ∀ y ∈ Ioi (0 : ℝ), (y ^ 2)⁻¹ • ((y : ℂ) ^ (conj s₁) *
      (Real.exp (-(2 * Real.pi * μ * y)) : ℂ) *
        deckCuspCoeff μ v (poincSeries (conjProfile s₂ ν) w) y) = ∑' r, F r y := by
    intro y (hy : 0 < y)
    rw [deckCuspCoeff_poincSeries hy (cuspCompatible_conjProfile s₂ hw) hv
      (continuous_conjProfile s₂ ν) (summable_norm_conjProfile hs₂ hν.le)
      (continuous_tsum_norm_conjProfile hs₂ hν.le), diagonal_conjProfile_eq_zero hμ hν s₂ hv hw hy,
      zero_add, Complex.real_smul, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [← Complex.real_smul, integral_coeffTerm_conjProfile hμ s₁ s₂ v w r.2.1 hy]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  -- interchange of the row sum and the `y`-integral
  have hker : ∀ r : ReducedRow, Integrable
      (Kuznetsov.kuzKernel (conj s₁) (conj s₂) μ ν ((r.1.1 0 : ℝ) ^ 2))
      ((volume.restrict (Ioi 0)).prod volume) := fun r =>
    Kuznetsov.integrable_kuzKernel hμ hν (hc2 r) hδ hδ₁ hδ₂
  have hint : ∀ r, Integrable (F r) (volume.restrict (Ioi 0)) := fun r =>
    (hker r).integral_prod_left.const_mul _
  set B := δ ^ δ * (2 * Real.pi * ν)⁻¹ ^ δ *
    ((∫ y in Ioi (0 : ℝ), y ^ ((conj s₁ - conj s₂).re + δ - 1) *
      Real.exp (-(2 * Real.pi * μ * y))) * ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - (conj s₂).re)) with hB
  have hbound : ∀ r : ReducedRow, ∫ y in Ioi (0 : ℝ), ‖F r y‖ ≤
      ‖v‖ * ‖w‖ * B * (((r.1.1 0 : ℝ)) ^ 2) ^ (-(s₂.re - δ)) := fun r => by
    have hq := hc2 r
    set q := ((r.1.1 0 : ℝ)) ^ 2
    have hcp : ‖((q : ℝ) : ℂ) ^ (-conj s₂)‖ = q ^ (-s₂.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, ha₂]
    have hle : ∀ y, ‖F r y‖ ≤ ‖v‖ * ‖w‖ * q ^ (-s₂.re) *
        ∫ ξ, ‖Kuznetsov.kuzKernel (conj s₁) (conj s₂) μ ν q (y, ξ)‖ := fun y => by
      rw [hFdef, norm_mul, norm_mul, hcp]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (norm_rowWeight_le μ ν v w r.1)
        (Real.rpow_nonneg hq.le _)) (norm_integral_le_integral_norm _) (norm_nonneg _)
        (by positivity)
    calc ∫ y in Ioi (0 : ℝ), ‖F r y‖
        ≤ ∫ y in Ioi (0 : ℝ), ‖v‖ * ‖w‖ * q ^ (-s₂.re) *
            ∫ ξ, ‖Kuznetsov.kuzKernel (conj s₁) (conj s₂) μ ν q (y, ξ)‖ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
            ((hker r).integral_norm_prod_left.const_mul _) (Filter.Eventually.of_forall hle)
      _ = ‖v‖ * ‖w‖ * q ^ (-s₂.re) *
            ∫ p, ‖Kuznetsov.kuzKernel (conj s₁) (conj s₂) μ ν q p‖
              ∂((volume.restrict (Ioi 0)).prod volume) := by
          rw [integral_const_mul, integral_prod _ (hker r).norm]
      _ ≤ ‖v‖ * ‖w‖ * q ^ (-s₂.re) * (B * q ^ δ) :=
          mul_le_mul_of_nonneg_left (Kuznetsov.integral_norm_kuzKernel_le hμ hν hq hδ hδ₁ hδ₂)
            (by positivity)
      _ = ‖v‖ * ‖w‖ * B * q ^ (-(s₂.re - δ)) := by
          rw [show -(s₂.re - δ) = -s₂.re + δ by ring, Real.rpow_add hq]
          ring
  have hsum : Summable fun r => ∫ y in Ioi (0 : ℝ), ‖F r y‖ :=
    ((summable_reducedRow_rpow hδ₃).mul_left (‖v‖ * ‖w‖ * B)).of_nonneg_of_le
      (fun r => integral_nonneg fun y => norm_nonneg _) hbound
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  refine tsum_congr fun r => ?_
  rw [hFdef, integral_const_mul, Kuznetsov.integral_integral_kuzKernel (by rw [ha₁]; linarith)
    (by rw [ha₂]; exact hs₂) hμ hν (hc2 r)]

end

end GaloisForLFunctions.RHTower.DeckPointPair
