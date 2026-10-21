import GaloisForLFunctions.RHTower.Sieve.GuthMaynardAffineIteration
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSelfBound

set_option autoImplicit false

/-!
# Equidistribution over affine transformations (Guth–Maynard, Proposition 9.1)

**Proposition 9.1** (arXiv 2405.20552, §9, in the paper's precise reading): let `f ≥ 0` be
continuous, supported on `[1/C, C]`, and suppose that for every `ε > 0` and `j ≥ 0`
`|ξ|^j |f̂(ξ)| ≤ c(j, ε) T^ε T^j ‖f‖_∞` for all `ξ`. Then for every `δ > 0` there is `c'(δ)`,
depending only on `C` and the `c(j, ε)`, with

`J_M(f) ≤ c'(δ) T^δ (M⁶ ‖f‖₁² + M⁴ ‖f‖₂²)`   for all `M > 0`, `T ≥ 1`

(`prop91_affineEquidistribution`). Only the instance `j = 2`, `ε = 1` of the decay hypothesis is
used, and `c'` depends on `δ` and `c(2, 1)` alone (`affineSup_le_of_fourier_decay`).

Proof.
1. *Sup norm* (`iSup_le_of_fourier_decay`): Fourier inversion gives `‖f‖_∞ ≤ ∫ |f̂|`; with
   `|f̂| ≤ ∫ f` and `ξ² |f̂| ≤ A ‖f‖_∞` this forces `‖f‖_∞ ≤ 16π² A ∫ f`. Hence `B = AT³ ‖f‖_∞`
   satisfies `B ≤ 16π² A² T⁶ ∫ f`, and with `Ξ = T⁴` the tail term of Lemma 9.2 is `≪ μ⁶ (∫ f)²`.
2. *Iteration* (`affineEnergy_le_iteration`, `ε = δ/8`):
   `E(t) ≤ α μ(t)⁶ (∫ f)² + β μ(t)² ‖f‖₂ E(σ t)^{1/2}` with `σ(M₁, M₂, M₃) = (M₂, M₂, 2⌊M₃⌋ + 1)`,
   `μ(σ t) ≤ 4 μ(t)`, `β = 3072 (1 + C_ε (3T⁴)^ε)`.
3. *Bootstrapping* (`bootstrap_affine_bound`): the ratio `Φ = sup_t E(t)/(μ⁶ (∫f)² + μ⁴ ∫ f²)`
   is finite by the trivial bound, and the iteration gives `Φ ≤ α + 64 β √Φ`, i.e.
   `Φ ≤ 2α + 4096 β² ≪_δ T^δ`. This replaces the paper's downward induction on the exponent.

Also recorded: Lemma 9.2 in `T^δ` form (`affineSup_le_iteration_of_decay`),
`J_M(f) ≤ c T^δ (M⁶ (∫ f)² + M² ‖f‖₂ J_{4M}(f)^{1/2})`.
-/

open MeasureTheory Finset Real
open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

open RHTower.Sieve (divisorBoundConst)
open GaloisForLFunctions.HTGeometry (lorentzF lorentzF_nonneg)

variable {f : ℝ → ℝ}

/-! ### The sup norm from Fourier decay -/

/-- **Sup norm from Fourier decay.** If `f ≥ 0` is continuous with compact support and
`ξ² |f̂(ξ)| ≤ A sup f` for all `ξ`, then `sup f ≤ 16π² A ∫ f`. -/
theorem iSup_le_of_fourier_decay (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {A : ℝ} (hA : 0 ≤ A)
    (hdec : ∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ A * ⨆ x, f x) :
    (⨆ x, f x) ≤ 16 * π ^ 2 * A * ∫ x, f x := by
  obtain ⟨S, hSdef⟩ : ∃ S, S = ⨆ x, f x := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁def⟩ : ∃ F₁, F₁ = ∫ x, f x := ⟨_, rfl⟩
  rw [← hSdef, ← hF₁def]
  rw [← hSdef] at hdec
  have hbdd := hf.bddAbove_range_of_hasCompactSupport hfc
  have hS0 : 0 ≤ S := hSdef ▸ le_trans (hf0 0) (le_ciSup hbdd 0)
  have hF0 : 0 ≤ F₁ := hF₁def ▸ integral_nonneg hf0
  have hfi : Integrable (complexify f) :=
    integrable_complexify (hf.memLp_of_hasCompactSupport hfc)
  have hFt : ∀ ξ, ‖𝓕 (complexify f) ξ‖ ≤ F₁ := fun ξ => hF₁def ▸ norm_fourier_complexify_le hf0 ξ
  have hcont : Continuous (𝓕 (complexify f)) :=
    GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hfi
  have hFint : Integrable (𝓕 (complexify f)) := by
    refine Integrable.mono' ((integrable_lorentzF one_pos).const_mul (F₁ + A * S))
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    have h1 := hFt ξ
    have h2 := hdec ξ
    have hn := norm_nonneg (𝓕 (complexify f) ξ)
    show ‖𝓕 (complexify f) ξ‖ ≤ (F₁ + A * S) * (1 ^ 2 / (1 ^ 2 + ξ ^ 2))
    rw [one_pow, mul_div_assoc', mul_one, le_div_iff₀ (by positivity)]
    nlinarith
  -- Fourier inversion: `f x ≤ ∫ |f̂|`
  have hcf : Continuous (complexify f) := Complex.continuous_ofReal.comp hf
  have hinv : ∀ x, f x ≤ ∫ ξ, ‖𝓕 (complexify f) ξ‖ := fun x => by
    have h := congrFun (Continuous.fourierInv_fourier_eq hcf hfi hFint) x
    have hx : f x = ‖𝓕⁻ (𝓕 (complexify f)) x‖ := by
      rw [h]
      simp [complexify, abs_of_nonneg (hf0 x)]
    rw [hx, Real.fourierInv_eq_fourier_neg]
    exact GaloisForLFunctions.HTGeometry.norm_fourierReal_le_integral_norm _ _
  have hSle : S ≤ ∫ ξ, ‖𝓕 (complexify f) ξ‖ := by
    rw [hSdef]
    exact ciSup_le hinv
  rcases hS0.eq_or_lt with hS | hS
  · rw [← hS]
    positivity
  rcases hF0.eq_or_lt with hF | hF
  · exfalso
    have h0 : ∀ ξ, ‖𝓕 (complexify f) ξ‖ = 0 := fun ξ =>
      le_antisymm (by rw [hF]; exact hFt ξ) (norm_nonneg _)
    have hz : ∫ ξ, ‖𝓕 (complexify f) ξ‖ = 0 := by simp [h0]
    linarith
  -- the scale `λ = S/(4π F₁)`
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = S / (4 * π * F₁) := ⟨_, rfl⟩
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  by_cases hcase : A * S ≤ F₁ * lam ^ 2
  · exfalso
    have hpt : ∀ ξ, ‖𝓕 (complexify f) ξ‖ ≤ 2 * F₁ * lorentzF lam ξ := fun ξ => by
      have h1 := hFt ξ
      have h2 := hdec ξ
      have hn := norm_nonneg (𝓕 (complexify f) ξ)
      show ‖𝓕 (complexify f) ξ‖ ≤ 2 * F₁ * (lam ^ 2 / (lam ^ 2 + ξ ^ 2))
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith
    have hint : ∫ ξ, ‖𝓕 (complexify f) ξ‖ ≤ 2 * F₁ * (π * lam) := by
      calc ∫ ξ, ‖𝓕 (complexify f) ξ‖ ≤ ∫ ξ, 2 * F₁ * lorentzF lam ξ :=
            integral_mono hFint.norm ((integrable_lorentzF hlam).const_mul _) hpt
        _ = 2 * F₁ * (π * lam) := by rw [integral_const_mul, integral_lorentzF_univ hlam]
    have he : 2 * F₁ * (π * lam) = S / 2 := by
      rw [hlamdef]
      field_simp
      ring
    linarith
  · rw [not_le] at hcase
    have he : F₁ * lam ^ 2 = S ^ 2 / (16 * π ^ 2 * F₁) := by
      rw [hlamdef]
      field_simp
      ring
    rw [he, div_lt_iff₀ (by positivity)] at hcase
    by_contra hcon
    rw [not_le] at hcon
    have := mul_lt_mul_of_pos_left hcon hS
    nlinarith

/-! ### Closing the iteration -/

/-- **Bootstrapping.** Let `E ≥ 0` on an index set with scales `ν ≥ 1/2` and a successor map
`σ` with `ν(σ t) ≤ 4 ν(t)`. If `E` is bounded by a multiple of `D(ν) = ν⁶ F₁² + ν⁴ F₂`
(`F₁ > 0`) and satisfies the iteration `E(t) ≤ α ν⁶ F₁² + β ν² √F₂ √E(σ t)`, then
`E(t) ≤ (2α + 4096 β²) D(ν(t))`. -/
theorem bootstrap_affine_bound {ι : Type*} [Nonempty ι] (E ν : ι → ℝ) (σ : ι → ι)
    {F₁ F₂ α β X : ℝ} (hF₁ : 0 < F₁) (hF₂ : 0 ≤ F₂) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hν : ∀ t, 1 / 2 ≤ ν t) (hσ : ∀ t, ν (σ t) ≤ 4 * ν t) (hE0 : ∀ t, 0 ≤ E t)
    (hX : ∀ t, E t ≤ X * (ν t ^ 6 * F₁ ^ 2 + ν t ^ 4 * F₂))
    (hit : ∀ t, E t ≤ α * ν t ^ 6 * F₁ ^ 2 + β * ν t ^ 2 * (√F₂ * √(E (σ t)))) (t : ι) :
    E t ≤ (2 * α + 4096 * β ^ 2) * (ν t ^ 6 * F₁ ^ 2 + ν t ^ 4 * F₂) := by
  set D : ι → ℝ := fun t => ν t ^ 6 * F₁ ^ 2 + ν t ^ 4 * F₂ with hD
  have hν0 : ∀ t, 0 < ν t := fun t => by linarith [hν t]
  have hD0 : ∀ t, 0 < D t := fun t => by
    have := hν0 t
    simp only [hD]
    positivity
  set r : ι → ℝ := fun t => E t / D t with hr
  have hbdd : BddAbove (Set.range r) := ⟨X, by
    rintro _ ⟨t, rfl⟩
    simp only [hr]
    rw [div_le_iff₀ (hD0 t)]
    exact hX t⟩
  set Φ := ⨆ t, r t with hΦ
  have hrΦ : ∀ t, r t ≤ Φ := fun t => le_ciSup hbdd t
  have hEΦ : ∀ t, E t ≤ Φ * D t := fun t => by
    have := hrΦ t
    simp only [hr] at this
    rwa [div_le_iff₀ (hD0 t)] at this
  have hΦ0 : 0 ≤ Φ := by
    obtain ⟨t⟩ := ‹Nonempty ι›
    exact le_trans (div_nonneg (hE0 t) (hD0 t).le) (hrΦ t)
  -- one step of the iteration in ratio form
  have hstep : ∀ t, r t ≤ α + 64 * β * √Φ := fun t => by
    have hDσ : D (σ t) ≤ 4 ^ 6 * D t := by
      simp only [hD]
      have h0 : 0 ≤ ν (σ t) := (hν0 _).le
      have h6 : ν (σ t) ^ 6 ≤ (4 * ν t) ^ 6 := pow_le_pow_left₀ h0 (hσ t) 6
      have h4 : ν (σ t) ^ 4 ≤ (4 * ν t) ^ 4 := pow_le_pow_left₀ h0 (hσ t) 4
      have hν4 : 0 ≤ ν t ^ 4 := by have := hν0 t; positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 (sq_nonneg F₁), mul_le_mul_of_nonneg_right h4 hF₂]
    have hEσ : E (σ t) ≤ Φ * (4 ^ 6 * D t) :=
      (hEΦ (σ t)).trans (mul_le_mul_of_nonneg_left hDσ hΦ0)
    have hsq : √F₂ * √(E (σ t)) ≤ 64 * √Φ * (√F₂ * √(D t)) := by
      have : √(E (σ t)) ≤ 64 * √Φ * √(D t) := by
        calc √(E (σ t)) ≤ √(Φ * (4 ^ 6 * D t)) := Real.sqrt_le_sqrt hEσ
          _ = 64 * √Φ * √(D t) := by
              rw [Real.sqrt_mul hΦ0, Real.sqrt_mul (by norm_num), show (4 : ℝ) ^ 6 = 64 ^ 2 by norm_num,
                Real.sqrt_sq (by norm_num)]
              ring
      calc √F₂ * √(E (σ t)) ≤ √F₂ * (64 * √Φ * √(D t)) :=
            mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
        _ = 64 * √Φ * (√F₂ * √(D t)) := by ring
    have hνF : ν t ^ 2 * (√F₂ * √(D t)) ≤ D t := by
      have h1 : ν t ^ 2 * √F₂ ≤ √(D t) := by
        have : ν t ^ 2 * √F₂ = √(ν t ^ 4 * F₂) := by
          rw [Real.sqrt_mul (by have := hν0 t; positivity), show ν t ^ 4 = (ν t ^ 2) ^ 2 by ring,
            Real.sqrt_sq (by have := hν0 t; positivity)]
        rw [this]
        refine Real.sqrt_le_sqrt ?_
        simp only [hD]
        have : 0 ≤ ν t ^ 6 * F₁ ^ 2 := by have := hν0 t; positivity
        linarith
      calc ν t ^ 2 * (√F₂ * √(D t)) = (ν t ^ 2 * √F₂) * √(D t) := by ring
        _ ≤ √(D t) * √(D t) := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ = D t := Real.mul_self_sqrt (hD0 t).le
    have hE := hit t
    have hα6 : α * ν t ^ 6 * F₁ ^ 2 ≤ α * D t := by
      have : ν t ^ 6 * F₁ ^ 2 ≤ D t := by
        simp only [hD]
        have : 0 ≤ ν t ^ 4 * F₂ := by have := hν0 t; positivity
        linarith
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left this hα
    have hfin : E t ≤ (α + 64 * β * √Φ) * D t := by
      have h3 : β * ν t ^ 2 * (√F₂ * √(E (σ t))) ≤ 64 * β * √Φ * D t := by
        calc β * ν t ^ 2 * (√F₂ * √(E (σ t)))
            ≤ β * ν t ^ 2 * (64 * √Φ * (√F₂ * √(D t))) := by
              have : 0 ≤ β * ν t ^ 2 := by have := hν0 t; positivity
              exact mul_le_mul_of_nonneg_left hsq this
          _ = 64 * β * √Φ * (ν t ^ 2 * (√F₂ * √(D t))) := by ring
          _ ≤ 64 * β * √Φ * D t :=
              mul_le_mul_of_nonneg_left hνF (by positivity)
      nlinarith
    simp only [hr]
    rw [div_le_iff₀ (hD0 t)]
    exact hfin
  have hΦle : Φ ≤ α + 64 * β * √Φ := ciSup_le hstep
  have hΦ2 : Φ ≤ 2 * α + (64 * β) ^ 2 := by
    have h := RHTower.Sieve.le_two_mul_add_sq_mul_of_le_add_of_sq_le_mul (k := 1) hΦ0
      (Real.sqrt_nonneg Φ) (by positivity) zero_le_one (by linarith : Φ ≤ α + 64 * β * √Φ)
      (by rw [Real.sq_sqrt hΦ0, one_mul])
    simpa using h
  calc E t ≤ Φ * D t := hEΦ t
    _ ≤ (2 * α + (64 * β) ^ 2) * D t := mul_le_mul_of_nonneg_right hΦ2 (hD0 t).le
    _ = (2 * α + 4096 * β ^ 2) * (ν t ^ 6 * F₁ ^ 2 + ν t ^ 4 * F₂) := by simp only [hD]; ring

/-! ### Proposition 9.1 -/

/-- A continuous nonnegative compactly supported function with zero integral vanishes. -/
theorem eq_zero_of_integral_eq_zero (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) (h : ∫ x, f x = 0) (x : ℝ) : f x = 0 := by
  by_contra hx
  have := hf.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := (volume : Measure ℝ)) hfc
    (fun y => hf0 y) hx
  linarith

/-- The successor scales of the iteration, `σ(M₁, M₂, M₃) = (M₂, M₂, 2⌊M₃⌋ + 1)`. -/
def affineSucc (t : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (t.2.1, t.2.1, 2 * ⌊t.2.2⌋₊ + 1)

theorem affineScale_succ_le (t : ℝ × ℝ × ℝ) :
    affineScale (affineSucc t).1 (affineSucc t).2.1 (affineSucc t).2.2 ≤
      4 * affineScale t.1 t.2.1 t.2.2 := by
  have hμ := half_le_affineScale t.1 t.2.1 t.2.2
  obtain ⟨-, h2, h3⟩ := le_affineScale t.1 t.2.1 t.2.2
  have h3' : (2 * ⌊t.2.2⌋₊ + 1 : ℝ) ≤ 4 * affineScale t.1 t.2.1 t.2.2 := by
    rcases le_or_gt 0 t.2.2 with h | h
    · have := Nat.floor_le h
      linarith
    · rw [Nat.floor_eq_zero.mpr (by linarith)]
      push_cast
      linarith
  show max (max t.2.1 t.2.1) (max (2 * ⌊t.2.2⌋₊ + 1 : ℝ) (1 / 2)) ≤ _
  refine max_le (max_le ?_ ?_) (max_le h3' ?_) <;> linarith

/-- **Lemma 9.2 under the decay hypothesis.** If `ξ² |f̂(ξ)| ≤ A T³ sup f`, then for every
triple `t` (with `μ = μ(t)`, `ε > 0`):
`E(t) ≤ (124416π + 95551488π⁵A⁴) μ⁶ (∫ f)² + 3072 (1 + C_ε (3T⁴)^ε) μ² ‖f‖₂ E(σ t)^{1/2}`. -/
theorem affineEnergy_le_iteration_of_decay (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {A T : ℝ} (hA : 0 ≤ A) (hT : 1 ≤ T)
    (hdec : ∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ A * T ^ 3 * ⨆ x, f x) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ × ℝ × ℝ) :
    affineEnergy f t.1 t.2.1 t.2.2 ≤
      (124416 * π + 95551488 * π ^ 5 * A ^ 4) * affineScale t.1 t.2.1 t.2.2 ^ 6 *
          (∫ x, f x) ^ 2 +
        3072 * (1 + divisorBoundConst ε * (3 * T ^ 4) ^ ε) * affineScale t.1 t.2.1 t.2.2 ^ 2 *
          (√(∫ x, f x ^ 2) *
            √(affineEnergy f (affineSucc t).1 (affineSucc t).2.1 (affineSucc t).2.2)) := by
  have hT0 : 0 < T := by linarith
  have hF0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  have hS0 : 0 ≤ ⨆ x, f x :=
    le_trans (hf0 0) (le_ciSup (hf.bddAbove_range_of_hasCompactSupport hfc) 0)
  have hSle : (⨆ x, f x) ≤ 16 * π ^ 2 * (A * T ^ 3) * ∫ x, f x :=
    iSup_le_of_fourier_decay hf hfc hf0 (by positivity) hdec
  -- the tail `B² Ξ⁻³ ≤ 256 π⁴ A⁴ (∫ f)²` for `B = A T³ sup f`, `Ξ = T⁴`
  have hB0 : 0 ≤ A * T ^ 3 * ⨆ x, f x := by positivity
  have hBle : A * T ^ 3 * (⨆ x, f x) ≤ 16 * π ^ 2 * A ^ 2 * T ^ 6 * ∫ x, f x := by
    calc A * T ^ 3 * (⨆ x, f x) ≤ A * T ^ 3 * (16 * π ^ 2 * (A * T ^ 3) * ∫ x, f x) := by gcongr
      _ = 16 * π ^ 2 * A ^ 2 * T ^ 6 * ∫ x, f x := by ring
  have htail : (A * T ^ 3 * ⨆ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3 ≤
      256 * π ^ 4 * A ^ 4 * (∫ x, f x) ^ 2 := by
    calc (A * T ^ 3 * ⨆ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3
        ≤ (16 * π ^ 2 * A ^ 2 * T ^ 6 * ∫ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3 := by
          gcongr
      _ = 256 * π ^ 4 * A ^ 4 * (∫ x, f x) ^ 2 := by
          field_simp
          ring
  have h := affineEnergy_le_iteration hf hfc hf0 (B := A * T ^ 3 * ⨆ x, f x) hdec
    (by positivity : (0 : ℝ) < T ^ 4) hε t.1 t.2.1 t.2.2
  -- opaque abbreviations keep the final linear step small
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = affineScale t.1 t.2.1 t.2.2 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (A * T ^ 3 * ⨆ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 3072 * (1 + divisorBoundConst ε * (3 * T ^ 4) ^ ε) *
      affineScale t.1 t.2.1 t.2.2 ^ 2 *
        (√(∫ x, f x ^ 2) *
          √(affineEnergy f (affineSucc t).1 (affineSucc t).2.1 (affineSucc t).2.2)) := ⟨_, rfl⟩
  have hW' : 3072 * (1 + divisorBoundConst ε * (3 * T ^ 4) ^ ε) * affineScale t.1 t.2.1 t.2.2 ^ 2 *
      (√(∫ x, f x ^ 2) * √(affineEnergy f t.2.1 t.2.1 (2 * ⌊t.2.2⌋₊ + 1))) = W := by
    rw [hW]
    rfl
  rw [hW', ← hY, ← hμ] at h
  rw [← hW, ← hμ]
  rw [← hY] at htail
  have hμ6 : 0 ≤ μ ^ 6 := by rw [hμ]; have := half_le_affineScale t.1 t.2.1 t.2.2; positivity
  have h3 := mul_le_mul_of_nonneg_left htail
    (by positivity : (0 : ℝ) ≤ 373248 * π * μ ^ 6)
  have e : (124416 * π + 95551488 * π ^ 5 * A ^ 4) * μ ^ 6 * (∫ x, f x) ^ 2 =
      124416 * π * μ ^ 6 * (∫ x, f x) ^ 2 +
        373248 * π * μ ^ 6 * (256 * π ^ 4 * A ^ 4 * (∫ x, f x) ^ 2) := by ring
  linarith

/-- `((3T⁴)^{δ/8})² = 3^{δ/4} T^δ`. -/
theorem sq_rpow_three_mul_pow_four {T : ℝ} (hT : 0 < T) (δ : ℝ) :
    ((3 * T ^ 4) ^ (δ / 8)) ^ 2 = 3 ^ (δ / 4) * T ^ δ := by
  rw [← Real.rpow_natCast ((3 * T ^ 4) ^ (δ / 8)) 2, ← Real.rpow_mul (by positivity),
    Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast T 4,
    ← Real.rpow_mul hT.le]
  push_cast
  ring_nf

/-- The constant of the bootstrap is `≪_δ T^δ`:
`2α + 4096 (3072 (1 + C_δ (3T⁴)^{δ/8}))² ≤ (2α + 8192 · 3072² (1 + C_δ² 3^{δ/4}) + 1) T^δ`. -/
theorem bootstrap_constant_le {α Cε T δ : ℝ} (hα : 0 ≤ α) (hT : 1 ≤ T)
    (hδ : 0 < δ) :
    2 * α + 4096 * (3072 * (1 + Cε * (3 * T ^ 4) ^ (δ / 8))) ^ 2 ≤
      (2 * α + 8192 * 3072 ^ 2 * (1 + Cε ^ 2 * 3 ^ (δ / 4)) + 1) * T ^ δ := by
  have hT0 : 0 < T := by linarith
  have hTδ : 1 ≤ T ^ δ := Real.one_le_rpow hT hδ.le
  obtain ⟨C, hC⟩ : ∃ C, C = Cε * (3 * T ^ 4) ^ (δ / 8) := ⟨_, rfl⟩
  have hC2 : C ^ 2 = Cε ^ 2 * 3 ^ (δ / 4) * T ^ δ := by
    rw [hC, mul_pow, sq_rpow_three_mul_pow_four hT0]
    ring
  rw [← hC]
  have h1 : (3072 * (1 + C)) ^ 2 ≤ 3072 ^ 2 * (2 + 2 * C ^ 2) := by
    nlinarith [sq_nonneg (1 - C)]
  have h3 : 0 ≤ Cε ^ 2 * 3 ^ (δ / 4) := by positivity
  rw [hC2] at h1
  have h4 : 2 + 2 * (Cε ^ 2 * 3 ^ (δ / 4) * T ^ δ) ≤ 2 * (1 + Cε ^ 2 * 3 ^ (δ / 4)) * T ^ δ := by
    nlinarith
  have h5 : 2 * α ≤ 2 * α * T ^ δ := by nlinarith
  nlinarith

/-- **Proposition 9.1, core form.** For `δ > 0` and `A ≥ 0` there is `c` such that for every
continuous compactly supported `f ≥ 0` and `T ≥ 1` with `ξ² |f̂(ξ)| ≤ A T³ sup f` for all `ξ`,
and every `M > 0`: `J_M(f) ≤ c T^δ (M⁶ (∫ f)² + M⁴ ∫ f²)`. -/
theorem affineSup_le_of_fourier_decay {δ : ℝ} (hδ : 0 < δ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℝ → ℝ) (T M : ℝ), 1 ≤ T → 0 < M → Continuous f →
      HasCompactSupport f → (∀ x, 0 ≤ f x) →
      (∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ A * T ^ 3 * ⨆ x, f x) →
      affineSup f M ≤ c * T ^ δ * (M ^ 6 * (∫ x, f x) ^ 2 + M ^ 4 * ∫ x, f x ^ 2) := by
  have hε : 0 < δ / 8 := by positivity
  obtain ⟨α, hα⟩ : ∃ α, α = 124416 * π + 95551488 * π ^ 5 * A ^ 4 := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hCε0 := divisorBoundConst_nonneg hε
  refine ⟨2 * α + 8192 * 3072 ^ 2 * (1 + divisorBoundConst (δ / 8) ^ 2 * 3 ^ (δ / 4)) + 1,
    by positivity, fun f T M hT hM hf hfc hf0 hdec => ?_⟩
  have hF0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  have hF20 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hTδ : 0 ≤ T ^ δ := Real.rpow_nonneg (by linarith) _
  have hRHS0 : 0 ≤ (2 * α + 8192 * 3072 ^ 2 * (1 + divisorBoundConst (δ / 8) ^ 2 * 3 ^ (δ / 4)) +
      1) * T ^ δ * (M ^ 6 * (∫ x, f x) ^ 2 + M ^ 4 * ∫ x, f x ^ 2) := by positivity
  -- the zero function
  rcases hF0.eq_or_lt with hz | hpos
  · have hf_zero : ∀ x, f x = 0 := eq_zero_of_integral_eq_zero hf hfc hf0 hz.symm
    refine affineSup_le hM fun t _ => ?_
    have : affineEnergy f t.1 t.2.1 t.2.2 = 0 := by
      simp [affineEnergy, affineSum, hf_zero]
    rw [this]
    exact hRHS0
  -- the bootstrap
  obtain ⟨β, hβ⟩ : ∃ β, β = 3072 * (1 + divisorBoundConst (δ / 8) * (3 * T ^ 4) ^ (δ / 8)) :=
    ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by
    rw [hβ]
    have : 0 ≤ (3 * T ^ 4) ^ (δ / 8) := Real.rpow_nonneg (by positivity) _
    positivity
  have hit : ∀ t : ℝ × ℝ × ℝ, affineEnergy f t.1 t.2.1 t.2.2 ≤
      α * affineScale t.1 t.2.1 t.2.2 ^ 6 * (∫ x, f x) ^ 2 +
        β * affineScale t.1 t.2.1 t.2.2 ^ 2 * (√(∫ x, f x ^ 2) *
          √(affineEnergy f (affineSucc t).1 (affineSucc t).2.1 (affineSucc t).2.2)) := fun t => by
    rw [hα, hβ]
    exact affineEnergy_le_iteration_of_decay hf hfc hf0 hA hT hdec hε t
  have hX : ∀ t : ℝ × ℝ × ℝ, affineEnergy f t.1 t.2.1 t.2.2 ≤
      10368 * (∫ x, f x ^ 2) / (∫ x, f x) ^ 2 * (affineScale t.1 t.2.1 t.2.2 ^ 6 *
        (∫ x, f x) ^ 2 + affineScale t.1 t.2.1 t.2.2 ^ 4 * ∫ x, f x ^ 2) := fun t => by
    have h := affineEnergy_le_trivial hf hfc t.1 t.2.1 t.2.2
    have hμ0 : 0 ≤ affineScale t.1 t.2.1 t.2.2 := by
      linarith [half_le_affineScale t.1 t.2.1 t.2.2]
    have e : 10368 * (∫ x, f x ^ 2) / (∫ x, f x) ^ 2 *
        (affineScale t.1 t.2.1 t.2.2 ^ 6 * (∫ x, f x) ^ 2) =
        10368 * affineScale t.1 t.2.1 t.2.2 ^ 6 * ∫ x, f x ^ 2 := by
      field_simp
    have : 0 ≤ 10368 * (∫ x, f x ^ 2) / (∫ x, f x) ^ 2 *
        (affineScale t.1 t.2.1 t.2.2 ^ 4 * ∫ x, f x ^ 2) := by positivity
    rw [mul_add, e]
    linarith
  have hboot := bootstrap_affine_bound (ι := ℝ × ℝ × ℝ)
    (fun t => affineEnergy f t.1 t.2.1 t.2.2) (fun t => affineScale t.1 t.2.1 t.2.2) affineSucc
    hpos hF20 hα0 hβ0 (fun t => half_le_affineScale _ _ _) affineScale_succ_le
    (fun t => affineEnergy_nonneg _ _ _ _) hX hit
  have hK : 2 * α + 4096 * β ^ 2 ≤
      (2 * α + 8192 * 3072 ^ 2 * (1 + divisorBoundConst (δ / 8) ^ 2 * 3 ^ (δ / 4)) + 1) *
        T ^ δ := by
    rw [hβ]
    exact bootstrap_constant_le hα0 hT hδ
  -- the supremum over the window
  refine affineSup_le hM fun t ht => ?_
  obtain ⟨h1, h1', h2, h2', h3, h3'⟩ := ht
  by_cases hs : t.1 < 1 / 2 ∨ t.2.1 < 1 / 2 ∨ t.2.2 < 0
  · rw [affineEnergy_eq_zero_of_scales hs]
    exact hRHS0
  simp only [not_or, not_lt] at hs
  have hM2 : 1 / 2 ≤ M := by linarith [hs.1]
  have hμM : affineScale t.1 t.2.1 t.2.2 ≤ M :=
    max_le (max_le h1'.le h2'.le) (max_le h3'.le hM2)
  have hμ0 : 0 ≤ affineScale t.1 t.2.1 t.2.2 := by linarith [half_le_affineScale t.1 t.2.1 t.2.2]
  have hDle : affineScale t.1 t.2.1 t.2.2 ^ 6 * (∫ x, f x) ^ 2 +
      affineScale t.1 t.2.1 t.2.2 ^ 4 * (∫ x, f x ^ 2) ≤
      M ^ 6 * (∫ x, f x) ^ 2 + M ^ 4 * ∫ x, f x ^ 2 := by gcongr
  have hK0 : 0 ≤ 2 * α + 4096 * β ^ 2 := by positivity
  exact (hboot t).trans (mul_le_mul hK hDle (by positivity) (by positivity))

/-- `(3T⁴)^{δ/4} = 3^{δ/4} T^δ`. -/
theorem rpow_three_mul_pow_four {T : ℝ} (hT : 0 < T) (δ : ℝ) :
    (3 * T ^ 4) ^ (δ / 4) = 3 ^ (δ / 4) * T ^ δ := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast T 4,
    ← Real.rpow_mul hT.le]
  push_cast
  ring_nf

/-- **Lemma 9.2 in `T^δ` form.** For `δ > 0`, `A ≥ 0` there is `c` such that, under
`ξ² |f̂(ξ)| ≤ A T³ sup f` (`T ≥ 1`), for every `M > 0`:
`J_M(f) ≤ c T^δ (M⁶ (∫ f)² + M² ‖f‖₂ J_{4M}(f)^{1/2})`. -/
theorem affineSup_le_iteration_of_decay {δ : ℝ} (hδ : 0 < δ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : ℝ → ℝ) (T M : ℝ), 1 ≤ T → 0 < M → Continuous f →
      HasCompactSupport f → (∀ x, 0 ≤ f x) →
      (∀ ξ : ℝ, ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ A * T ^ 3 * ⨆ x, f x) →
      affineSup f M ≤ c * T ^ δ *
        (M ^ 6 * (∫ x, f x) ^ 2 + M ^ 2 * (√(∫ x, f x ^ 2) * √(affineSup f (4 * M)))) := by
  have hε : 0 < δ / 4 := by positivity
  have hCε0 := divisorBoundConst_nonneg hε
  obtain ⟨α, hα⟩ : ∃ α, α = 124416 * π + 95551488 * π ^ 5 * A ^ 4 := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  refine ⟨α + 3072 * (1 + divisorBoundConst (δ / 4) * 3 ^ (δ / 4)), by positivity,
    fun f T M hT hM hf hfc hf0 hdec => ?_⟩
  have hT0 : 0 < T := by linarith
  have hTδ : 1 ≤ T ^ δ := Real.one_le_rpow hT hδ.le
  have hF0 : 0 ≤ ∫ x, f x := integral_nonneg hf0
  have hS0 : 0 ≤ ⨆ x, f x :=
    le_trans (hf0 0) (le_ciSup (hf.bddAbove_range_of_hasCompactSupport hfc) 0)
  have hSle : (⨆ x, f x) ≤ 16 * π ^ 2 * (A * T ^ 3) * ∫ x, f x :=
    iSup_le_of_fourier_decay hf hfc hf0 (by positivity) hdec
  have htail : (A * T ^ 3 * ⨆ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3 ≤
      256 * π ^ 4 * A ^ 4 * (∫ x, f x) ^ 2 := by
    have hBle : A * T ^ 3 * (⨆ x, f x) ≤ 16 * π ^ 2 * A ^ 2 * T ^ 6 * ∫ x, f x := by
      calc A * T ^ 3 * (⨆ x, f x) ≤ A * T ^ 3 * (16 * π ^ 2 * (A * T ^ 3) * ∫ x, f x) := by
            gcongr
        _ = 16 * π ^ 2 * A ^ 2 * T ^ 6 * ∫ x, f x := by ring
    calc (A * T ^ 3 * ⨆ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3
        ≤ (16 * π ^ 2 * A ^ 2 * T ^ 6 * ∫ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3 := by gcongr
      _ = 256 * π ^ 4 * A ^ 4 * (∫ x, f x) ^ 2 := by
          field_simp
          ring
  have h := affineSup_le_iteration hf hfc hf0 (B := A * T ^ 3 * ⨆ x, f x) hdec
    (by positivity : (0 : ℝ) < T ^ 4) hε hM
  rw [rpow_three_mul_pow_four hT0] at h
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (A * T ^ 3 * ⨆ x, f x) ^ 2 * (T ^ 4)⁻¹ ^ 3 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = √(∫ x, f x ^ 2) * √(affineSup f (4 * M)) := ⟨_, rfl⟩
  rw [← hY, ← hV] at h
  rw [← hY] at htail
  rw [← hV]
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  have hM6 : 0 ≤ M ^ 6 := by positivity
  have h3 := mul_le_mul_of_nonneg_left htail (by positivity : (0 : ℝ) ≤ 373248 * π * M ^ 6)
  have hC : 1 + divisorBoundConst (δ / 4) * (3 ^ (δ / 4) * T ^ δ) ≤
      (1 + divisorBoundConst (δ / 4) * 3 ^ (δ / 4)) * T ^ δ := by
    have : 0 ≤ divisorBoundConst (δ / 4) * 3 ^ (δ / 4) := by positivity
    nlinarith
  have hW : 3072 * (1 + divisorBoundConst (δ / 4) * (3 ^ (δ / 4) * T ^ δ)) * M ^ 2 * V ≤
      3072 * ((1 + divisorBoundConst (δ / 4) * 3 ^ (δ / 4)) * T ^ δ) * M ^ 2 * V := by
    gcongr
  have hαT : α * M ^ 6 * (∫ x, f x) ^ 2 ≤ α * T ^ δ * (M ^ 6 * (∫ x, f x) ^ 2) := by
    have : 0 ≤ α * (M ^ 6 * (∫ x, f x) ^ 2) := by positivity
    nlinarith
  have e : α * M ^ 6 * (∫ x, f x) ^ 2 = 124416 * π * M ^ 6 * (∫ x, f x) ^ 2 +
      373248 * π * M ^ 6 * (256 * π ^ 4 * A ^ 4 * (∫ x, f x) ^ 2) := by rw [hα]; ring
  have e2 : (α + 3072 * (1 + divisorBoundConst (δ / 4) * 3 ^ (δ / 4))) * T ^ δ *
      (M ^ 6 * (∫ x, f x) ^ 2 + M ^ 2 * V) =
      α * T ^ δ * (M ^ 6 * (∫ x, f x) ^ 2) +
        3072 * ((1 + divisorBoundConst (δ / 4) * 3 ^ (δ / 4)) * T ^ δ) * M ^ 2 * V +
        α * T ^ δ * (M ^ 2 * V) +
        3072 * (1 + divisorBoundConst (δ / 4) * 3 ^ (δ / 4)) * T ^ δ * (M ^ 6 * (∫ x, f x) ^ 2) := by
    ring
  have hαV : 0 ≤ α * T ^ δ * (M ^ 2 * V) := by positivity
  have hextra : 0 ≤ 3072 * (1 + divisorBoundConst (δ / 4) * 3 ^ (δ / 4)) * T ^ δ *
      (M ^ 6 * (∫ x, f x) ^ 2) := by positivity
  rw [e2]
  linarith

/-- **Proposition 9.1** (Guth–Maynard, "Equidistribution over affine transformations"), in the
paper's precise reading. Let `C` and constants `c(j, ε)` be given. For every `δ > 0` there is
`c' > 0`, depending only on `δ` and the `c(j, ε)` (in fact only on `c(2, 1)`), such that: if
`f : ℝ → [0, ∞)` is continuous, supported in `[1/C, C]` (`C > 0`), and
`|ξ|^j |f̂(ξ)| ≤ c(j, ε) T^ε T^j ‖f‖_∞` for all `j ≥ 0`, `ε > 0`, `ξ`, then for all `T ≥ 1`, `M > 0`:
`J_M(f) ≤ c' T^δ (M⁶ ‖f‖₁² + M⁴ ‖f‖₂²)`, where `‖f‖₁ = ∫ f`, `‖f‖₂² = ∫ f²`,
`‖f‖_∞ = sup f`. -/
theorem prop91_affineEquidistribution (C : ℝ) (c : ℕ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ (f : ℝ → ℝ) (T M : ℝ), 0 < C → 1 ≤ T → 0 < M → Continuous f →
      (∀ x, 0 ≤ f x) → Function.support f ⊆ Set.Icc (1 / C) C →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ,
        |ξ| ^ j * ‖𝓕 (complexify f) ξ‖ ≤ c j ε * T ^ ε * T ^ j * ⨆ x, f x) →
      affineSup f M ≤ c' * T ^ δ * (M ^ 6 * (∫ x, f x) ^ 2 + M ^ 4 * ∫ x, f x ^ 2) := by
  obtain ⟨c', hc', h⟩ := affineSup_le_of_fourier_decay hδ (le_max_right (c 2 1) 0)
  refine ⟨c', hc', fun f T M _ hT hM hf hf0 hsupp hdec => ?_⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro isCompact_Icc fun x hx => by
      by_contra hne
      exact hx (hsupp hne)
  refine h f T M hT hM hf hfc hf0 fun ξ => ?_
  have hT0 : 0 ≤ T := by linarith
  have hS0 : 0 ≤ ⨆ x, f x :=
    le_trans (hf0 0) (le_ciSup (hf.bddAbove_range_of_hasCompactSupport hfc) 0)
  have h1 := hdec 2 1 one_pos ξ
  rw [sq_abs, Real.rpow_one] at h1
  calc ξ ^ 2 * ‖𝓕 (complexify f) ξ‖ ≤ c 2 1 * T * T ^ 2 * ⨆ x, f x := h1
    _ = c 2 1 * (T ^ 3 * ⨆ x, f x) := by ring
    _ ≤ max (c 2 1) 0 * (T ^ 3 * ⨆ x, f x) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max (c 2 1) 0 * T ^ 3 * ⨆ x, f x := by ring

end

end RHTower.GuthMaynard
