import GaloisForLFunctions.RHTower.ConstrainedProlateDepthSecular
import GaloisForLFunctions.RHTower.ConstrainedProlateParityExactTransfer

/-!
# The minimal leakage contract behind the exact constrained transfer

The exact constrained transfer theorems never use the sharp Fuchs asymptotic
`1 − χ_n(λ)² ~ A_n λ^(2n+1) e^(−4πλ²)`.  They use only three structural consequences of it:
an ordered leakage ladder with a floor, the collapse `d_k/d_{k+1} → 0`, and the tail rate
`λ·d_{k+1}/(d_{k+2} − d_{k+1}) → 0`.

This module isolates the weakest hypothesis producing all three.  A leakage family `D` indexed
along a step-four ladder `e` — `e (j+1) = e j + 4`, covering both the positive sector `e j = 4j`
and the negative sector `e j = 4j + 2` — is *Fuchs-enveloped* when it is nonnegative, monotone
in the index, and trapped at every fixed index between two Fuchs rates with that index:

```text
fuchsRate c_j (e j) λ ≤ D λ j ≤ fuchsRate C_j (e j) λ   eventually, with 0 < c_j, C_j.
```

Monotonicity supplies the ordering and the floor outright; the two-sided bounds supply the two
strict gap inequalities and both rates, since the common Gaussian clock cancels and one ladder
step is exactly a factor `λ⁸`.  No relation between the constants `c_j` and `C_j` at different
indices is needed, and no sharp asymptotic — only a two-sided envelope at each fixed index.

Consequently every constrained law of the cards — the `8/11` ground ratio, the `3/11` gap, the
quantified spectral gap, the negative-sector `8/13` and `5/13`, and the all-depth ladder
`μ_k/d_{k+1} → θ_k` — holds for any Fuchs-enveloped leakage family, in particular for the true
prolate leakage once a two-sided fixed-index envelope is established for it.
-/

open Filter

namespace RHTower

/-! ## Step-four comparison of Fuchs rates -/

/-- One ladder step beats any constant ratio: the Fuchs rate at index `n + 4` dominates the one
at index `n` as soon as `λ⁸` clears the constant ratio. -/
theorem fuchsRate_lt_step4 {C c : ℝ} (hc : 0 < c) {lam : ℝ} (hlam : 0 < lam)
    (n : ℕ) (hpow : C / c < lam ^ 8) :
    fuchsRate C n lam < fuchsRate c (n + 4) lam := by
  have hpow' : C < lam ^ 8 * c := (div_lt_iff₀ hc).mp hpow
  have hCc : C < c * lam ^ 8 := by linarith
  have hP : (0 : ℝ) < lam ^ (2 * n + 1) := pow_pos hlam _
  have hE : (0 : ℝ) < Real.exp (-(4 * Real.pi * lam ^ 2)) := Real.exp_pos _
  unfold fuchsRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8]
  calc C * lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))
      = C * (lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))) := by ring
    _ < c * lam ^ 8 * (lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))) :=
        mul_lt_mul_of_pos_right hCc (mul_pos hP hE)
    _ = c * (lam ^ (2 * n + 1) * lam ^ 8) * Real.exp (-(4 * Real.pi * lam ^ 2)) := by ring

/-- A ladder step beats twice any constant ratio, leaving half the higher rate as slack. -/
theorem fuchsRate_le_half_step4 {C c : ℝ} (hc : 0 < c) {lam : ℝ} (hlam : 0 < lam)
    (n : ℕ) (hpow : 2 * C / c ≤ lam ^ 8) :
    fuchsRate C n lam ≤ fuchsRate c (n + 4) lam / 2 := by
  have hpow' : 2 * C ≤ lam ^ 8 * c := (div_le_iff₀ hc).mp hpow
  have hCc : C ≤ c * lam ^ 8 / 2 := by linarith
  have hP : (0 : ℝ) < lam ^ (2 * n + 1) := pow_pos hlam _
  have hE : (0 : ℝ) < Real.exp (-(4 * Real.pi * lam ^ 2)) := Real.exp_pos _
  unfold fuchsRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8]
  calc C * lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))
      = C * (lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))) := by ring
    _ ≤ c * lam ^ 8 / 2 * (lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))) :=
        mul_le_mul_of_nonneg_right hCc (mul_pos hP hE).le
    _ = c * (lam ^ (2 * n + 1) * lam ^ 8) * Real.exp (-(4 * Real.pi * lam ^ 2)) / 2 := by ring

/-- The Gaussian clock cancels across one ladder step, leaving an exact `λ⁻⁸`. -/
theorem fuchsRate_div_step4 {C c : ℝ} (hc : c ≠ 0) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    fuchsRate C n lam / fuchsRate c (n + 4) lam = C / c * (lam ^ 8)⁻¹ := by
  have hE : Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 := Real.exp_ne_zero _
  have hP : (lam : ℝ) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hlam.ne'
  unfold fuchsRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8]
  field_simp

/-- The aperture-weighted step ratio against half the higher rate is exactly `2(C/c)λ⁻⁷`. -/
theorem fuchsRate_tail_bound_eq {C c : ℝ} (hc : c ≠ 0) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    lam * fuchsRate C n lam / (fuchsRate c (n + 4) lam / 2) = 2 * (C / c) * (lam ^ 7)⁻¹ := by
  have hE : Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 := Real.exp_ne_zero _
  have hP : (lam : ℝ) ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hlam.ne'
  have h7 : (lam : ℝ) ^ 7 ≠ 0 := pow_ne_zero _ hlam.ne'
  have h8 : (lam : ℝ) ^ 8 = lam ^ 7 * lam := by ring
  unfold fuchsRate
  rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add lam (2 * n + 1) 8, h8]
  field_simp

/-! ## The Fuchs envelope contract -/

/-- A leakage family along a step-four index ladder, trapped between two Fuchs rates at every
fixed index.  This is the entire analytic input the exact constrained transfer theorems
require. -/
structure FuchsEnvelope (D : ℝ → ℕ → ℝ) (e : ℕ → ℕ) : Prop where
  /-- One ladder step advances the Fuchs index by four. -/
  step : ∀ j, e (j + 1) = e j + 4
  /-- Leakages are nonnegative. -/
  nonneg : ∀ lam j, 0 ≤ D lam j
  /-- Leakages increase along the ladder. -/
  mono : ∀ lam {i j : ℕ}, i ≤ j → D lam i ≤ D lam j
  /-- A positive Fuchs rate of the correct index eventually bounds each leakage below. -/
  lower : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ᶠ lam in atTop, fuchsRate c (e j) lam ≤ D lam j
  /-- A positive Fuchs rate of the correct index eventually bounds each leakage above. -/
  upper : ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ᶠ lam in atTop, D lam j ≤ fuchsRate C (e j) lam

variable {D : ℝ → ℕ → ℝ} {e : ℕ → ℕ}

/-- Adjacent leakages eventually separate strictly. -/
theorem FuchsEnvelope.lt_succ (h : FuchsEnvelope D e) (j : ℕ) :
    ∀ᶠ lam in atTop, D lam j < D lam (j + 1) := by
  obtain ⟨C, hC, hup⟩ := h.upper j
  obtain ⟨c, hc, hlo⟩ := h.lower (j + 1)
  filter_upwards [hup, hlo, eventually_gt_atTop (0 : ℝ),
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num)).eventually_gt_atTop (C / c)]
    with lam hu hl hlam hpow
  have hkey : fuchsRate C (e j) lam < fuchsRate c (e (j + 1)) lam := by
    rw [h.step j]
    exact fuchsRate_lt_step4 hc hlam (e j) hpow
  linarith

/-- **The collapse rate.**  Each leakage is negligible against its successor. -/
theorem FuchsEnvelope.ratio_tendsto_zero (h : FuchsEnvelope D e) (j : ℕ) :
    Tendsto (fun lam => D lam j / D lam (j + 1)) atTop (nhds 0) := by
  obtain ⟨C, hC, hup⟩ := h.upper j
  obtain ⟨c, hc, hlo⟩ := h.lower (j + 1)
  have hbound : Tendsto (fun lam : ℝ => C / c * (lam ^ 8)⁻¹) atTop (nhds 0) := by
    have h8 := (tendsto_pow_atTop (α := ℝ) (n := 8)
      (by norm_num : (8 : ℕ) ≠ 0)).inv_tendsto_atTop
    simpa using h8.const_mul (C / c)
  refine squeeze_zero' (Eventually.of_forall fun lam =>
    div_nonneg (h.nonneg lam j) (h.nonneg lam (j + 1))) ?_ hbound
  filter_upwards [hup, hlo, eventually_gt_atTop (0 : ℝ)] with lam hu hl hlam
  have hF2pos : 0 < fuchsRate c (e (j + 1)) lam := fuchsRate_pos hc _ hlam
  have hD1pos : 0 < D lam (j + 1) := lt_of_lt_of_le hF2pos hl
  calc D lam j / D lam (j + 1)
      ≤ fuchsRate C (e j) lam / D lam (j + 1) := div_le_div_of_le_of_pos hu hD1pos
    _ ≤ fuchsRate C (e j) lam / fuchsRate c (e (j + 1)) lam :=
        div_le_div_of_nonneg_left (fuchsRate_pos hC _ hlam).le hF2pos hl
    _ = C / c * (lam ^ 8)⁻¹ := by
        rw [h.step j]
        exact fuchsRate_div_step4 hc.ne' hlam (e j)

/-- **The tail rate.**  The aperture-weighted leakage is negligible against the next gap. -/
theorem FuchsEnvelope.tail_tendsto_zero (h : FuchsEnvelope D e) (j : ℕ) :
    Tendsto (fun lam => lam * D lam (j + 1) / (D lam (j + 2) - D lam (j + 1)))
      atTop (nhds 0) := by
  obtain ⟨C, hC, hup⟩ := h.upper (j + 1)
  obtain ⟨c, hc, hlo⟩ := h.lower (j + 2)
  have hbound : Tendsto (fun lam : ℝ => 2 * (C / c) * (lam ^ 7)⁻¹) atTop (nhds 0) := by
    have h7 := (tendsto_pow_atTop (α := ℝ) (n := 7)
      (by norm_num : (7 : ℕ) ≠ 0)).inv_tendsto_atTop
    simpa using h7.const_mul (2 * (C / c))
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
    have hmon : D lam (j + 1) ≤ D lam (j + 2) := h.mono lam (by omega)
    exact div_nonneg (mul_nonneg hlam (h.nonneg lam (j + 1))) (by linarith)
  · filter_upwards [hup, hlo, eventually_gt_atTop (0 : ℝ),
      (tendsto_pow_atTop (α := ℝ) (n := 8)
        (by norm_num : (8 : ℕ) ≠ 0)).eventually_ge_atTop (2 * C / c)]
      with lam hu hl hlam hpow
    have hF1pos : 0 < fuchsRate C (e (j + 1)) lam := fuchsRate_pos hC _ hlam
    have hF2pos : 0 < fuchsRate c (e (j + 2)) lam := fuchsRate_pos hc _ hlam
    have hhalf : fuchsRate C (e (j + 1)) lam ≤ fuchsRate c (e (j + 2)) lam / 2 := by
      rw [h.step (j + 1)]
      exact fuchsRate_le_half_step4 hc hlam (e (j + 1)) hpow
    have hdenpos : 0 < fuchsRate c (e (j + 2)) lam / 2 := by linarith
    have hden : fuchsRate c (e (j + 2)) lam / 2 ≤ D lam (j + 2) - D lam (j + 1) := by
      linarith
    have hnum : lam * D lam (j + 1) ≤ lam * fuchsRate C (e (j + 1)) lam :=
      mul_le_mul_of_nonneg_left hu hlam.le
    calc lam * D lam (j + 1) / (D lam (j + 2) - D lam (j + 1))
        ≤ lam * fuchsRate C (e (j + 1)) lam / (D lam (j + 2) - D lam (j + 1)) :=
          div_le_div_of_le_of_pos hnum (lt_of_lt_of_le hdenpos hden)
      _ ≤ lam * fuchsRate C (e (j + 1)) lam / (fuchsRate c (e (j + 2)) lam / 2) :=
          div_le_div_of_nonneg_left
            (mul_nonneg hlam.le hF1pos.le) hdenpos hden
      _ = 2 * (C / c) * (lam ^ 7)⁻¹ := by
          rw [h.step (j + 1)]
          exact fuchsRate_tail_bound_eq hc.ne' hlam (e (j + 1))

/-- The first-gap structural hypothesis of the exact transfer theorems. -/
theorem FuchsEnvelope.first_struct (h : FuchsEnvelope D e) :
    ∀ᶠ lam in atTop,
      (0 ≤ D lam 0 ∧ D lam 0 < D lam 1 ∧ D lam 1 < D lam 2) ∧
        ∀ j, D lam 2 ≤ D lam (j + 2) := by
  filter_upwards [h.lt_succ 0, h.lt_succ 1] with lam h1 h2
  exact ⟨⟨h.nonneg lam 0, h1, h2⟩, fun j => h.mono lam (by omega)⟩

/-- The depth-`k` structural hypothesis of the exact ladder theorems: monotonicity supplies the
ordered head and the floor outright. -/
theorem FuchsEnvelope.depth_struct (h : FuchsEnvelope D e) (k : ℕ) :
    ∀ᶠ lam in atTop,
      ((∀ j, j ≤ k → 0 ≤ D lam j ∧ D lam j ≤ D lam k) ∧
        D lam k < D lam (k + 1) ∧ D lam (k + 1) < D lam (k + 2)) ∧
        ∀ j, D lam (k + 2) ≤ D lam (j + (k + 2)) := by
  filter_upwards [h.lt_succ k, h.lt_succ (k + 1)] with lam h1 h2
  exact ⟨⟨fun j hj => ⟨h.nonneg lam j, h.mono lam hj⟩, h1, h2⟩,
    fun j => h.mono lam (by omega)⟩

/-! ## Every constrained law, for any Fuchs-enveloped leakage -/

variable {ℓ : ℝ → ℕ → ℝ}

/-- The exact constrained ground ratio for a Fuchs-enveloped leakage family. -/
theorem FuchsEnvelope.ground_ratio_tendsto (h : FuchsEnvelope D e)
    {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1) atTop
      (nhds (a0 ^ 2 / (a0 ^ 2 + a1 ^ 2))) :=
  infiniteSecularRoot_ratio_tendsto ha0 ha1 h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- The complementary exact constrained gap ratio. -/
theorem FuchsEnvelope.gap_ratio_tendsto (h : FuchsEnvelope D e)
    {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam => (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1) atTop
      (nhds (a1 ^ 2 / (a0 ^ 2 + a1 ^ 2))) :=
  infiniteSecularRoot_gap_ratio_tendsto ha0 ha1 h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- **The CCM `8/11` law for a Fuchs-enveloped leakage.** -/
theorem FuchsEnvelope.ccm_ground_ratio_tendsto (h : FuchsEnvelope D e)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1) atTop
      (nhds (8 / 11)) :=
  ccm_infiniteSecularRoot_ratio_tendsto h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- **The CCM `3/11` gap law for a Fuchs-enveloped leakage.** -/
theorem FuchsEnvelope.ccm_gap_ratio_tendsto (h : FuchsEnvelope D e)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1) atTop
      (nhds (3 / 11)) :=
  ccm_infiniteSecularRoot_gap_ratio_tendsto h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1

/-- **The quantified CCM constrained spectral gap for a Fuchs-enveloped leakage.** -/
theorem FuchsEnvelope.ccm_spectralGap_eventually (h : FuchsEnvelope D e)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))))
    {cst : ℝ} (hc : cst < 3 / 11) :
    ∀ᶠ lam in atTop, ∀ μ' : ℝ, infiniteSecular (D lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (D lam) (ℓ lam) →
      cst * D lam 1 ≤ μ' - infiniteSecularRoot (D lam) (ℓ lam) :=
  ccm_infiniteSecularRoot_spectralGap_eventually h.first_struct hsum hbessel
    (h.ratio_tendsto_zero 0) (h.tail_tendsto_zero 0) hl0 hl1 hc

/-- **The negative-sector `8/13` law for a Fuchs-enveloped leakage.** -/
theorem FuchsEnvelope.ccm_negativeSector_ratio_tendsto (h : FuchsEnvelope D e)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam => infiniteSecularRoot (D lam) (ℓ lam) / D lam 1) atTop
      (nhds (8 / 13)) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have hr := h.ground_ratio_tendsto ha0 ha1 hsum hbessel hl0 hl1
  rwa [ccm_negativeSector_hermite_weight_eq] at hr

/-- **The negative-sector `5/13` gap law for a Fuchs-enveloped leakage.** -/
theorem FuchsEnvelope.ccm_negativeSector_gap_ratio_tendsto (h : FuchsEnvelope D e)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam => (D lam 1 - infiniteSecularRoot (D lam) (ℓ lam)) / D lam 1) atTop
      (nhds (5 / 13)) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have hr := h.gap_ratio_tendsto ha0 ha1 hsum hbessel hl0 hl1
  rwa [ccm_negativeSector_hermite_weight_complement_eq] at hr

/-- **The exact all-depth CCM ladder for a Fuchs-enveloped leakage.**  At every fixed depth the
exact constrained root obeys `μ_k(λ)/D_{k+1}(λ) → θ_k = Q_k/Q_{k+1}`. -/
theorem FuchsEnvelope.ccm_depth_ratio_tendsto (h : FuchsEnvelope D e) (k : ℕ)
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam => depthSecularRoot (D lam) (ℓ lam) k / D lam (k + 1)) atTop
      (nhds (constrainedProlateHermiteTheta k)) :=
  ccm_depthSecularRoot_ratio_tendsto (h.depth_struct k) hsum hbessel
    (h.ratio_tendsto_zero k) (h.tail_tendsto_zero k) hl

/-! ## The concrete Fuchs family is enveloped -/

/-- The radial Fuchs family is its own envelope: the model of the previous transfer modules is
the special case of a Fuchs-enveloped leakage with `c_j = C_j = A_j`. -/
theorem fuchsEnvelope_fuchsRate {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {ν : ℕ → ℕ}
    (hstep : ∀ j, ν (j + 1) = ν j + 4)
    (hmono : ∀ lam : ℝ, 0 < lam → ∀ {i j : ℕ}, i ≤ j →
      fuchsRate (A i) (ν i) lam ≤ fuchsRate (A j) (ν j) lam) :
    FuchsEnvelope (fun lam j => if 0 < lam then fuchsRate (A j) (ν j) lam else 0) ν where
  step := hstep
  nonneg := by
    intro lam j
    by_cases hlam : 0 < lam
    · simp only [if_pos hlam]
      exact (fuchsRate_pos (hA j) _ hlam).le
    · simp [if_neg hlam]
  mono := by
    intro lam i j hij
    by_cases hlam : 0 < lam
    · simp only [if_pos hlam]
      exact hmono lam hlam hij
    · simp [if_neg hlam]
  lower := by
    intro j
    refine ⟨A j, hA j, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    simp only [if_pos hlam]
    exact le_refl _
  upper := by
    intro j
    refine ⟨A j, hA j, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    simp only [if_pos hlam]
    exact le_refl _

end RHTower
