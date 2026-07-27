import GaloisForLFunctions.RHTower.MobiusBinaryExcursion

/-!
# The character-twisted Möbius--Laplace source

The conductor-one development uses the Mellin--Dirichlet identity
`mellin A s = Γ(s) / ζ(s)` on `Re s > 1`.  The same identity holds for the source twisted by a
Dirichlet character, with `ζ` replaced by `L(s, χ)`, because mathlib supplies both the Mellin
interchange (`hasSum_mellin`) and the inverse relation `L(χ) · L(χ·μ) = 1`.

This is the analytic input `(R9)` of the order law at arbitrary conductor.
-/

open Complex Filter Set MeasureTheory
open scoped ArithmeticFunction.Moebius LSeries.notation Topology

namespace RHTower

variable {N : ℕ}

/-- The character-twisted Möbius--Laplace source `∑ χ(n) μ(n) e^{-n x}`. -/
noncomputable def twistedMobiusLaplaceTransform (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑' n : ℕ, (↗χ * ↗μ) n * Complex.exp (-((n : ℝ) * x : ℝ))

theorem norm_twistedMobiusCoeff_le_one (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖(↗χ * ↗μ) n‖ ≤ 1 := by
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one n
  have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  simpa [norm_mul] using mul_le_one₀ hχ (norm_nonneg _) hμ

theorem summable_twistedMobiusLaplaceTerm (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => (↗χ * ↗μ) n * Complex.exp (-((n : ℝ) * x : ℝ)) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_pow_mul_exp_neg 0 hx)
  rw [norm_mul, Complex.norm_exp]
  have hexp : 0 ≤ Real.exp (-((n : ℝ) * x)) := (Real.exp_pos _).le
  simpa using mul_le_mul_of_nonneg_right (norm_twistedMobiusCoeff_le_one χ n) hexp

theorem twistedMobiusLaplaceTerm_hasSum (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (↗χ * ↗μ) n * Complex.exp (-((n : ℝ) * x : ℝ)))
      (twistedMobiusLaplaceTransform χ x) :=
  (summable_twistedMobiusLaplaceTerm χ hx).hasSum

/-- The weighted twisted coefficients are summable on `Re s > 1`. -/
theorem twistedMobiusMellin_weight_summable (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖(↗χ * ↗μ) n‖ / (n : ℝ) ^ s.re := by
  have h := (DirichletCharacter.LSeriesSummable_mul χ
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

/-- **Mellin--Dirichlet identity, twisted form.**  On the half-plane of absolute convergence the
Mellin transform of the twisted source is `Γ(s)` times the twisted Möbius L-series. -/
theorem mellin_twistedMobiusLaplaceTransform_eq_gamma_mul_LSeries
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    mellin (twistedMobiusLaplaceTransform χ) s = Complex.Gamma s * L (↗χ * ↗μ) s := by
  have hp : ∀ n : ℕ, (↗χ * ↗μ) n = 0 ∨ 0 < (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · left
      subst n
      simp
    · right
      exact_mod_cast Nat.pos_of_ne_zero hn
  have hs0 : 0 < s.re := by linarith
  have hF : ∀ t ∈ Ioi (0 : ℝ),
      HasSum (fun n : ℕ => (↗χ * ↗μ) n * Real.exp (-(n : ℝ) * t))
        (twistedMobiusLaplaceTransform χ t) := by
    intro t ht
    convert twistedMobiusLaplaceTerm_hasSum χ ht using 2 with n
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  have hmellin : HasSum (fun n : ℕ => Complex.Gamma s * (↗χ * ↗μ) n / (n : ℂ) ^ s)
      (mellin (twistedMobiusLaplaceTransform χ) s) :=
    hasSum_mellin hp hs0 hF (twistedMobiusMellin_weight_summable χ hs)
  rw [← hmellin.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def₀ (by simp) s n, div_eq_mul_inv, Complex.cpow_neg]
  ring

/-- The twisted source has Mellin transform `Γ(s)/L(s,χ)` on `Re s > 1`. -/
theorem mellin_twistedMobiusLaplaceTransform_eq_gamma_div_LSeries
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    mellin (twistedMobiusLaplaceTransform χ) s = Complex.Gamma s * (L ↗χ s)⁻¹ := by
  rw [mellin_twistedMobiusLaplaceTransform_eq_gamma_mul_LSeries χ hs]
  congr 1
  have hone := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hne : L ↗χ s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  field_simp
  linear_combination hone

/-! ### Analytic groundwork for the twisted source

The estimates the Mellin analyticity criterion needs use only `‖χ(n) μ(n)‖ ≤ 1`, so they transfer
from the untwisted development with the coefficient bound swapped. -/

theorem continuousOn_twistedMobiusLaplaceTransform (χ : DirichletCharacter ℂ N) :
    ContinuousOn (twistedMobiusLaplaceTransform χ) (Ioi 0) := by
  intro x hx
  set a : ℝ := x / 2 with ha_def
  have hxpos : 0 < x := hx
  have ha : 0 < a := by rw [ha_def]; linarith
  have hax : a < x := by rw [ha_def]; linarith
  have hmajor : Summable fun n : ℕ => Real.exp (-((n : ℝ) * a)) := by
    simpa using summable_pow_mul_exp_neg 0 ha
  have hcontinuous : ContinuousOn
      (fun y : ℝ => ∑' n : ℕ, (↗χ * ↗μ) n * Complex.exp (-((n : ℝ) * y : ℝ))) (Ici a) := by
    refine continuousOn_tsum (fun n => ?_) hmajor (fun n y hy => ?_)
    · fun_prop
    · rw [norm_mul, Complex.norm_exp]
      have hexp : Real.exp (-((n : ℝ) * y)) ≤ Real.exp (-((n : ℝ) * a)) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hmul : (n : ℝ) * a ≤ (n : ℝ) * y := mul_le_mul_of_nonneg_left hy hn
        linarith
      calc ‖(↗χ * ↗μ) n‖ * Real.exp (-((n : ℝ) * y))
          ≤ 1 * Real.exp (-((n : ℝ) * y)) :=
            mul_le_mul_of_nonneg_right (norm_twistedMobiusCoeff_le_one χ n) (Real.exp_pos _).le
        _ ≤ Real.exp (-((n : ℝ) * a)) := by simpa using hexp
  exact (hcontinuous x hax.le).continuousAt (Ici_mem_nhds hax) |>.continuousWithinAt

theorem twistedMobiusLaplaceTransform_locallyIntegrableOn (χ : DirichletCharacter ℂ N) :
    LocallyIntegrableOn (twistedMobiusLaplaceTransform χ) (Ioi 0) :=
  (continuousOn_twistedMobiusLaplaceTransform χ).locallyIntegrableOn measurableSet_Ioi

theorem norm_twistedMobiusLaplaceTransform_le_exp_neg (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖twistedMobiusLaplaceTransform χ x‖ ≤
      Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hsum := summable_twistedMobiusLaplaceTerm χ hxpos
  have hshift : twistedMobiusLaplaceTransform χ x =
      ∑' n : ℕ, (↗χ * ↗μ) (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ)) := by
    have hsplit := hsum.sum_add_tsum_nat_add 1
    rw [twistedMobiusLaplaceTransform]
    simpa using hsplit.symm
  have hshiftSum : Summable
      fun n : ℕ => (↗χ * ↗μ) (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ)) :=
    hsum.comp_injective Nat.succ_injective
  have hgeom : Summable fun n : ℕ => Real.exp (-x) * Real.exp (-(n : ℝ)) :=
    Real.summable_exp_neg_nat.mul_left _
  rw [hshift]
  calc ‖∑' n : ℕ, (↗χ * ↗μ) (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ))‖
      ≤ ∑' n : ℕ, ‖(↗χ * ↗μ) (n + 1) * Complex.exp (-(((n + 1 : ℕ) : ℝ) * x : ℝ))‖ :=
        norm_tsum_le_tsum_norm hshiftSum.norm
    _ ≤ ∑' n : ℕ, Real.exp (-x) * Real.exp (-(n : ℝ)) := by
        refine hshiftSum.norm.tsum_le_tsum (fun n => ?_) hgeom
        rw [norm_mul, Complex.norm_exp]
        have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) * x)) ≤
            Real.exp (-x) * Real.exp (-(n : ℝ)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          push_cast
          nlinarith
        exact (mul_le_mul_of_nonneg_right (norm_twistedMobiusCoeff_le_one χ (n + 1))
          (Real.exp_pos _).le).trans (by simpa using hexp)
    _ = Real.exp (-x) * ∑' n : ℕ, Real.exp (-(n : ℝ)) := by rw [tsum_mul_left]

theorem twistedMobiusLaplaceTransform_isBigO_exp_neg (χ : DirichletCharacter ℂ N) :
    twistedMobiusLaplaceTransform χ =O[atTop] fun x : ℝ => Real.exp (-1 * x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' n : ℕ, Real.exp (-(n : ℝ)), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have h := norm_twistedMobiusLaplaceTransform_le_exp_neg χ hx
  rw [neg_one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa [mul_comm] using h

/-- Decay of the twisted source at exponent `b` near the origin. -/
def TwistedMobiusLaplaceDecay (χ : DirichletCharacter ℂ N) (b : ℝ) : Prop :=
  ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
    ∀ x : ℝ, 0 < x → x < delta →
      ‖twistedMobiusLaplaceTransform χ x‖ ≤ C * x ^ (-b)

theorem TwistedMobiusLaplaceDecay.isBigO {χ : DirichletCharacter ℂ N} {b : ℝ}
    (hdecay : TwistedMobiusLaplaceDecay χ b) :
    twistedMobiusLaplaceTransform χ =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
  rcases hdecay with ⟨C, delta, hC, hdelta, hbound⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < delta :=
    (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxd
  have hxpos : 0 < x := hx
  calc ‖twistedMobiusLaplaceTransform χ x‖
      ≤ C * x ^ (-b) := hbound x hxpos hxd
    _ = C * ‖x ^ (-b)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos _)]

/-- **Analyticity of the twisted Mellin transform.** -/
theorem analyticOnNhd_mellin_of_twistedMobiusLaplaceDecay
    {χ : DirichletCharacter ℂ N} {b : ℝ} (hdecay : TwistedMobiusLaplaceDecay χ b) :
    AnalyticOnNhd ℂ (mellin (twistedMobiusLaplaceTransform χ)) {s : ℂ | b < s.re} := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) (isOpen_decayHalfPlane b)
  exact (mellin_differentiableAt_of_isBigO_rpow_exp
    (a := 1) (b := b) (by norm_num)
    (twistedMobiusLaplaceTransform_locallyIntegrableOn χ)
    (twistedMobiusLaplaceTransform_isBigO_exp_neg χ) hdecay.isBigO hs).differentiableWithinAt

/-! ### The coefficient side at arbitrary conductor

The radial bound of `MixedConvolutionSubpowerAbelBound` is generic in the coefficient sequence, so
it specializes to the twisted sequence with no new analysis. -/

theorem twistedMobiusLaplaceTransform_eq_tsum_pow (χ : DirichletCharacter ℂ N) (x : ℝ) :
    twistedMobiusLaplaceTransform χ x =
      ∑' n : ℕ, (↗χ * ↗μ) n * ((Real.exp (-x) : ℝ) : ℂ) ^ n := by
  rw [twistedMobiusLaplaceTransform]
  refine tsum_congr fun n => ?_
  rw [← Complex.ofReal_pow, exp_neg_pow, Complex.ofReal_exp]
  push_cast
  ring

theorem summable_norm_twistedCoeff_mul_pow (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => ‖(↗χ * ↗μ) n * ((Real.exp (-x) : ℝ) : ℂ) ^ n‖ := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hpow : (0 : ℝ) ≤ Real.exp (-x) ^ n := pow_nonneg hr0 n
  simpa using mul_le_mul_of_nonneg_right (norm_twistedMobiusCoeff_le_one χ n) hpow

/-- **Discharge at arbitrary conductor.**  A subpower bound on the twisted Hermitian mixed
convolution coefficients gives twisted source decay at exponent `(α+1)/(2k)`. -/
theorem twistedMobiusLaplaceDecay_of_subpower (χ : DirichletCharacter ℂ N)
    {k : ℕ} (hk : 0 < k) {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hupper : ∀ M : ℕ,
      (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re ≤ C * ((M : ℝ) + 1) ^ α) :
    TwistedMobiusLaplaceDecay χ ((α + 1) / (2 * (k : ℝ))) := by
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  refine ⟨(C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹), 1, ?_, one_pos, ?_⟩
  · exact Real.rpow_nonneg (mul_nonneg hC hAbel) _
  · intro x hx hx1
    have hbound := norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower
      hk hα hC hx hx1.le (summable_norm_twistedCoeff_mul_pow χ hx) hupper
    rw [twistedMobiusLaplaceTransform_eq_tsum_pow]
    refine hbound.trans (le_of_eq ?_)
    congr 1
    rw [one_div x, ← Real.rpow_neg_one x, ← Real.rpow_mul hx.le]
    congr 1
    ring

end RHTower
