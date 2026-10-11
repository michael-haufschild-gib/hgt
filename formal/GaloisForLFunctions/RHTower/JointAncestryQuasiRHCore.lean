import GaloisForLFunctions.RHTower.JointAncestryQuasiRHAmplification

/-!
# The amplification contradiction, with explicit numerical hypotheses

This file assembles the per-point estimates into a negative value of the log-weight Bernoulli sum.

**Left representatives.**  Every point `s` is paired with `ŝ = s` if `Re s ≤ ½` and `ŝ = 1 − s̄`
otherwise (`jasLeftRep`).  The value, its real part and the weight are the same at `s` and `ŝ`, and
`Re ŝ = ½ − |Re s − ½|`.  Hence every estimate only needs points left of the critical line.

**The bulk prime-sum bound** (`norm_jasLogWeightSum_le_of_far`).  For `|Im z| ≥ 1` and
`Re z ≤ ε`, the window sum is at most `99`, provided the main term `((B+½)^z − (A+½)^z)/z` is at most
`2`, the Perron error is at most `1`, and `(A+1)^{−1/8} M ≤ 99` (for `Re z ≤ −1/8`).
-/

open Complex
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## Left representatives -/

/-- The representative of `s` left of the critical line. -/
def jasLeftRep (s : ℂ) : ℂ := if s.re ≤ 1 / 2 then s else 1 - conj s

theorem jasLeftRep_im (s : ℂ) : (jasLeftRep s).im = s.im := by
  unfold jasLeftRep; split_ifs <;> simp

theorem jasLeftRep_re (s : ℂ) : (jasLeftRep s).re = 1 / 2 - |s.re - 1 / 2| := by
  unfold jasLeftRep
  split_ifs with h
  · rw [abs_of_nonpos (by linarith)]; ring
  · rw [abs_of_pos (by linarith)]; simp; ring

theorem re_jasLogWeightValue_jasLeftRep (ξ : ℂ) (A B : ℕ) (τ φ : ℝ) (s : ℂ) :
    (jasLogWeightValue ξ A B τ φ (jasLeftRep s)).re = (jasLogWeightValue ξ A B τ φ s).re := by
  unfold jasLeftRep; split_ifs
  · rfl
  · exact re_jasLogWeightValue_one_sub_conj ξ A B τ φ s

theorem norm_jasLogWeightValue_jasLeftRep (ξ : ℂ) (A B : ℕ) (τ φ : ℝ) (s : ℂ) :
    ‖jasLogWeightValue ξ A B τ φ (jasLeftRep s)‖ = ‖jasLogWeightValue ξ A B τ φ s‖ := by
  unfold jasLeftRep; split_ifs
  · rfl
  · rw [jasLogWeightValue_one_sub_conj, Complex.norm_conj]

theorem norm_weight_jasLeftRep (s : ℂ) :
    ‖1 / (jasLeftRep s * (1 - jasLeftRep s))‖ = ‖1 / (s * (1 - s))‖ := by
  unfold jasLeftRep; split_ifs
  · rfl
  · have : (1 - conj s) * (1 - (1 - conj s)) = conj (s * (1 - s)) := by
      rw [map_mul, map_sub, map_one]; ring
    rw [this, ← map_one (starRingEnd ℂ), ← map_div₀, Complex.norm_conj, map_one]

/-- Under the strip bound the shifts of the left representative are `≤ ε` and `≤ −δ`. -/
theorem jasLeftRep_shifts {ξ s : ℂ} {δ ε : ℝ} (hδ : ξ.re = 1 / 2 - δ)
    (hs : |s.re - 1 / 2| ≤ δ + ε) :
    (ξ - jasLeftRep s).re ≤ ε ∧ (jasLeftRep s + conj ξ - 1).re ≤ -δ := by
  have hre := jasLeftRep_re s
  constructor
  · rw [Complex.sub_re, hre, hδ]; linarith
  · rw [Complex.sub_re, Complex.add_re, Complex.conj_re, hre, hδ, Complex.one_re]
    linarith [abs_nonneg (s.re - 1 / 2)]

/-! ## The bulk prime-sum bound -/

/-- `‖((x^z − y^z)/z)‖ ≤ (x^{Re z} + y^{Re z})/|Im z|` for positive reals `x, y`. -/
theorem norm_cpow_sub_cpow_div_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) {z : ℂ} (hz : z.im ≠ 0) :
    ‖((x : ℂ) ^ z - (y : ℂ) ^ z) / z‖ ≤ (x ^ z.re + y ^ z.re) / |z.im| := by
  rw [norm_div]
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  have hzn : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hnum : ‖(x : ℂ) ^ z - (y : ℂ) ^ z‖ ≤ x ^ z.re + y ^ z.re := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  calc ‖(x : ℂ) ^ z - (y : ℂ) ^ z‖ / ‖z‖ ≤ (x ^ z.re + y ^ z.re) / ‖z‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (x ^ z.re + y ^ z.re) / |z.im| :=
        div_le_div_of_nonneg_left (by positivity) hzpos hzn

/-- **The bulk bound.**  Away from the target height the window sum is at most `99`. -/
theorem norm_jasLogWeightSum_le_of_far {A B : ℕ} {z : ℂ} {K σ₁ η ε : ℝ}
    (hPer : z ≠ 0 → -1 / 8 < z.re → z.re ≤ 1 - σ₁ - η → z.re ≤ 1 / 8 →
      ‖jasLogWeightSum A B z -
          (((((B : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z - (((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z) / z)‖
        ≤ K * (((A : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
              (1 + Real.log ((A : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2 +
            ((B : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
              (1 + Real.log ((B : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2) + 96)
    (hz1 : 1 ≤ |z.im|) (hzε : z.re ≤ ε) (hεσ : ε ≤ 1 - σ₁ - η) (hε8 : ε ≤ 1 / 8)
    (hmain : (((B : ℝ) + 1 / 2) ^ z.re + ((A : ℝ) + 1 / 2) ^ z.re) / |z.im| ≤ 2)
    (herr : K * (((A : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
              (1 + Real.log ((A : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2 +
            ((B : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
              (1 + Real.log ((B : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2) ≤ 1)
    (htriv : Real.exp (-(1 / 8) * Real.log (A + 1)) * jasLogMass A B ≤ 99) :
    ‖jasLogWeightSum A B z‖ ≤ 99 := by
  rcases le_or_gt z.re (-1 / 8) with hlow | hhigh
  · refine (norm_jasLogWeightSum_le_of_re_nonpos (by linarith)).trans ?_
    refine le_trans ?_ htriv
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (jasLogMass_nonneg A B)
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by linarith [(A.cast_nonneg : (0:ℝ) ≤ A)]))
  · have hz0 : z ≠ 0 := by
      intro h; rw [h, Complex.zero_im, abs_zero] at hz1; linarith
    have hP := hPer hz0 hhigh (by linarith) (by linarith)
    have hm := norm_cpow_sub_cpow_div_le (x := (B : ℝ) + 1 / 2) (y := (A : ℝ) + 1 / 2)
      (by positivity) (by positivity) (z := z) (by intro h; rw [h, abs_zero] at hz1; linarith)
    calc ‖jasLogWeightSum A B z‖
        ≤ ‖jasLogWeightSum A B z -
            (((((B : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z - (((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z) / z)‖ +
          ‖(((((B : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z - (((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z) / z)‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ (1 + 96) + 2 := add_le_add (hP.trans (by linarith)) (hm.trans hmain)
      _ = 99 := by norm_num

/-! ## Class estimates -/

/-- The `B`-part is uniformly small: `‖S(ŝ + ξ̄ − 1)‖ ≤ (A+1)^{−δ} M`. -/
theorem norm_jasLogWeightSum_mirror_le {ξ s : ℂ} {A B : ℕ} {δ : ℝ}
    (h : (jasLeftRep s + conj ξ - 1).re ≤ -δ) (hδ : 0 ≤ δ) :
    ‖jasLogWeightSum A B (jasLeftRep s + conj ξ - 1)‖ ≤
      Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B := by
  refine (norm_jasLogWeightSum_le_of_re_nonpos (by linarith)).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (jasLogMass_nonneg A B)
  exact mul_le_mul_of_nonneg_right h (Real.log_nonneg (by linarith [(A.cast_nonneg : (0:ℝ) ≤ A)]))

/-- **Bulk points.** -/
theorem norm_jasLogWeightValue_le_bulk {ξ s : ℂ} {A B : ℕ} (hA : 1 ≤ A) {τ ε δ Sg φ : ℝ}
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδ : ξ.re = 1 / 2 - δ)
    (hs : |s.re - 1 / 2| ≤ δ + ε)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2)
    (hSg : ‖jasLogWeightSum A B (ξ - jasLeftRep s)‖ ≤ Sg) :
    ‖jasLogWeightValue ξ A B τ φ s‖ ≤ ‖1 / (s * (1 - s))‖ *
      Real.exp (τ * (Sg + Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B) +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A) := by
  obtain ⟨h₁, h₂⟩ := jasLeftRep_shifts hδ hs
  rw [← norm_jasLogWeightValue_jasLeftRep, ← norm_weight_jasLeftRep]
  refine (norm_jasLogWeightValue_le_of_shift hA hτ hε φ h₁ (by linarith) hdev).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hE : (jasLogWeightExponent ξ A B φ (jasLeftRep s)).re ≤
      Sg + Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B := by
    refine (Complex.re_le_norm _).trans ?_
    rw [jasLogWeightExponent]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul,
      one_mul]
    exact add_le_add hSg (norm_jasLogWeightSum_mirror_le h₂ hδ0)
  linarith [mul_le_mul_of_nonneg_left hE hτ]

/-- **Suppressed points near the target height.** -/
theorem norm_jasLogWeightValue_le_suppressed {ξ s : ℂ} {A B : ℕ} (hA : 1 ≤ A) {τ ε δ φ lam0 L₀ : ℝ}
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδ : ξ.re = 1 / 2 - δ)
    (hs : |s.re - 1 / 2| ≤ δ)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2)
    (hM : 0 < jasLogMass A B) (hsin0 : 0 ≤ Real.sin φ) (hcos : 1 / 2 ≤ Real.cos φ)
    (hsinM : τ * jasLogMass A B * Real.sin φ ≤ 13)
    (hlam : lam0 ≤ 1 - (jasLogWeightSum A B (ξ - jasLeftRep s)).re / jasLogMass A B)
    (hL : L₀ ≤ τ * jasLogMass A B * lam0) :
    ‖jasLogWeightValue ξ A B τ φ s‖ ≤ ‖1 / (s * (1 - s))‖ *
      Real.exp (τ * jasLogMass A B * Real.cos φ - L₀ / 2 + 26 +
        τ * (Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B) +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A) := by
  set M := jasLogMass A B with hMdef
  have hs' : |s.re - 1 / 2| ≤ δ + ε := by linarith
  obtain ⟨h₁, h₂⟩ := jasLeftRep_shifts hδ hs'
  have h₁' : (ξ - jasLeftRep s).re ≤ 0 := by
    rw [Complex.sub_re, jasLeftRep_re, hδ]; linarith
  rw [← norm_jasLogWeightValue_jasLeftRep, ← norm_weight_jasLeftRep]
  refine (norm_jasLogWeightValue_le_of_shift hA hτ hε φ h₁ (by linarith) hdev).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  set S₁ := jasLogWeightSum A B (ξ - jasLeftRep s) with hS₁
  have hnS₁ : ‖S₁‖ ≤ M := norm_jasLogWeightSum_le_mass h₁'
  have hreS₁ : -M ≤ S₁.re := by
    have := Complex.abs_re_le_norm S₁; have := abs_le.mp (this.trans hnS₁); linarith [this.1]
  have hlam2 : 1 - S₁.re / M ≤ 2 := by
    have : -1 ≤ S₁.re / M := by rw [le_div_iff₀ hM]; linarith
    linarith
  have hlam0 : 0 ≤ 1 - S₁.re / M := by
    have : S₁.re / M ≤ 1 := (div_le_one hM).mpr ((Complex.re_le_norm _).trans hnS₁)
    linarith
  have him : |S₁.im| ≤ 2 * M := by
    refine (abs_im_le_sqrt_two_mul hM hnS₁).trans ?_
    have : Real.sqrt (2 * (1 - S₁.re / M)) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    nlinarith
  have hE := re_jasLogWeightExponent_le ξ A B hsin0 (jasLeftRep s)
  rw [← hS₁] at hE
  have hS₂ := norm_jasLogWeightSum_mirror_le (A := A) (B := B) h₂ hδ0
  have hreS₁eq : S₁.re = M * (1 - (1 - S₁.re / M)) := by field_simp; ring
  -- `τ Re E ≤ τ M cos φ − τ M λ cos φ + 26 + τ β`
  have key : τ * (jasLogWeightExponent ξ A B φ (jasLeftRep s)).re ≤
      τ * M * Real.cos φ - τ * M * (1 - S₁.re / M) * Real.cos φ + 26 +
        τ * (Real.exp (-δ * Real.log (A + 1)) * M) := by
    have h1 := mul_le_mul_of_nonneg_left hE hτ
    have h2 : τ * (Real.sin φ * |S₁.im|) ≤ 26 := by
      calc τ * (Real.sin φ * |S₁.im|) ≤ τ * (Real.sin φ * (2 * M)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left him hsin0) hτ
        _ = 2 * (τ * M * Real.sin φ) := by ring
        _ ≤ 26 := by linarith
    have h3 : τ * (Real.cos φ * S₁.re) =
        τ * M * Real.cos φ - τ * M * (1 - S₁.re / M) * Real.cos φ := by
      have hM0 : M ≠ 0 := hM.ne'
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left hS₂ hτ]
  have hsupp : L₀ / 2 ≤ τ * M * (1 - S₁.re / M) * Real.cos φ := by
    have hτM : 0 ≤ τ * M := mul_nonneg hτ hM.le
    have : τ * M * lam0 ≤ τ * M * (1 - S₁.re / M) := mul_le_mul_of_nonneg_left hlam hτM
    have h4 := mul_le_mul_of_nonneg_left hcos (mul_nonneg hτM hlam0)
    linarith
  linarith

/-- **Aligned points near the target height.** -/
theorem re_jasLogWeightValue_nonpos_cluster {ξ s : ℂ} {A B : ℕ} (hA : 1 ≤ A) {τ ε δ φ lam0 : ℝ}
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδ : ξ.re = 1 / 2 - δ)
    (hs : |s.re - 1 / 2| ≤ δ)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2)
    (hM : 0 < jasLogMass A B) (hsin0 : 0 ≤ Real.sin φ) (hcos0 : 0 ≤ Real.cos φ)
    (hwξ : 1 / (ξ * (1 - ξ)) ≠ 0)
    (harg : (1 / (ξ * (1 - ξ))).arg + τ * (jasLogMass A B -
      ∑ p ∈ jasPrimeWindow A B, Real.log p / p * Real.exp ((2 * ξ.re - 1) * Real.log p)) *
        Real.sin φ = Real.pi)
    (hlam : 1 - (jasLogWeightSum A B (ξ - jasLeftRep s)).re / jasLogMass A B ≤ lam0)
    {k : ℤ} (halign : |τ * (jasLogWeightSum A B (ξ - jasLeftRep s)).im - 2 * Real.pi * k| ≤
      Real.pi / 4)
    (hc : ‖(1 / (jasLeftRep s * (1 - jasLeftRep s))) / (1 / (ξ * (1 - ξ))) - 1‖ ≤ 1 / 2)
    (hbudget : 2 * ‖(1 / (jasLeftRep s * (1 - jasLeftRep s))) / (1 / (ξ * (1 - ξ))) - 1‖ +
        τ * Real.sin φ ^ 2 * (jasLogMass A B * Real.sqrt (2 * lam0)) +
        τ * Real.sin φ * jasLogMass A B * lam0 +
        2 * (τ * (Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B)) +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A ≤ Real.pi / 4) :
    (jasLogWeightValue ξ A B τ φ s).re ≤ 0 := by
  set M := jasLogMass A B with hMdef
  set SB := ∑ p ∈ jasPrimeWindow A B, Real.log p / p * Real.exp ((2 * ξ.re - 1) * Real.log p)
    with hSBdef
  set β := Real.exp (-δ * Real.log (A + 1)) * M with hβ
  have hs' : |s.re - 1 / 2| ≤ δ + ε := by linarith
  obtain ⟨h₁, h₂⟩ := jasLeftRep_shifts hδ hs'
  have h₁' : (ξ - jasLeftRep s).re ≤ 0 := by
    rw [Complex.sub_re, jasLeftRep_re, hδ]; linarith
  rw [← re_jasLogWeightValue_jasLeftRep]
  set S₁ := jasLogWeightSum A B (ξ - jasLeftRep s) with hS₁
  set S₂ := jasLogWeightSum A B (jasLeftRep s + conj ξ - 1) with hS₂
  have hnS₁ : ‖S₁‖ ≤ M := norm_jasLogWeightSum_le_mass h₁'
  have hnS₂ : ‖S₂‖ ≤ β := norm_jasLogWeightSum_mirror_le h₂ hδ0
  have hlam0 : 0 ≤ 1 - S₁.re / M := by
    have : S₁.re / M ≤ 1 := (div_le_one hM).mpr ((Complex.re_le_norm _).trans hnS₁)
    linarith
  have him : |S₁.im| ≤ M * Real.sqrt (2 * lam0) := by
    refine (abs_im_le_sqrt_two_mul hM hnS₁).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) hM.le
  -- `S_B ≤ β`
  have hSB : SB ≤ β := by
    have hreal : ((2 * ξ.re - 1 : ℝ) : ℂ).re ≤ -δ := by simp; linarith
    have h := norm_jasLogWeightSum_le_of_re_nonpos (A := A) (B := B)
      (z := ((2 * ξ.re - 1 : ℝ) : ℂ)) (by simp; linarith)
    rw [jasLogWeightSum_ofReal, Complex.norm_real, Real.norm_of_nonneg
      (jasLogWeightSum_ofReal_nonneg A B _)] at h
    refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (jasLogMass_nonneg A B))
    simp only [Complex.ofReal_re] at hreal
    exact mul_le_mul_of_nonneg_right hreal
      (Real.log_nonneg (by linarith [(A.cast_nonneg : (0:ℝ) ≤ A)]))
  have hSB0 : 0 ≤ SB := jasLogWeightSum_ofReal_nonneg A B _
  -- the phase deviation
  have hIm := im_jasLogWeightExponent ξ A B φ (jasLeftRep s)
  rw [← hS₁, ← hS₂] at hIm
  have hdecomp : τ * (jasLogWeightExponent ξ A B φ (jasLeftRep s)).im - τ * (M - SB) * Real.sin φ =
      τ * S₁.im + τ * (Real.cos φ - 1) * S₁.im - τ * Real.sin φ * (M - S₁.re) +
        τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im + τ * SB * Real.sin φ := by
    rw [hIm]; ring
  have hcos1 : 1 - Real.cos φ ≤ Real.sin φ ^ 2 := by
    have := Real.cos_sq_add_sin_sq φ
    have hc1 : Real.cos φ ≤ 1 := Real.cos_le_one φ
    nlinarith
  have e1 : |τ * (Real.cos φ - 1) * S₁.im| ≤ τ * Real.sin φ ^ 2 * (M * Real.sqrt (2 * lam0)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hτ, abs_of_nonpos (by linarith [Real.cos_le_one φ])]
    have : 0 ≤ τ * (-(Real.cos φ - 1)) := mul_nonneg hτ (by linarith [Real.cos_le_one φ])
    calc τ * -(Real.cos φ - 1) * |S₁.im| ≤ τ * Real.sin φ ^ 2 * |S₁.im| := by
          gcongr; linarith
      _ ≤ τ * Real.sin φ ^ 2 * (M * Real.sqrt (2 * lam0)) := by gcongr
  have e2 : |τ * Real.sin φ * (M - S₁.re)| ≤ τ * Real.sin φ * M * lam0 := by
    have hMS : M - S₁.re = M * (1 - S₁.re / M) := by field_simp
    rw [hMS, abs_of_nonneg (by positivity)]
    calc τ * Real.sin φ * (M * (1 - S₁.re / M)) ≤ τ * Real.sin φ * (M * lam0) := by gcongr
      _ = τ * Real.sin φ * M * lam0 := by ring
  have e3 : |τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im| ≤ τ * β := by
    rw [abs_mul, abs_of_nonneg hτ]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans
      ((norm_cexp_negTwist_mul φ S₂).le.trans hnS₂)) hτ
  have e4 : |τ * SB * Real.sin φ| ≤ τ * β := by
    rw [abs_of_nonneg (by positivity)]
    have : Real.sin φ ≤ 1 := Real.sin_le_one φ
    calc τ * SB * Real.sin φ ≤ τ * β * 1 := by gcongr
      _ = τ * β := by ring
  have harg' := abs_arg_le_two_mul_norm_sub_one hc
  refine re_jasLogWeightValue_nonpos_of_aligned hA hτ hε h₁ (by linarith) hdev hwξ harg (k := k) ?_
  rw [hdecomp]
  set c := (1 / (jasLeftRep s * (1 - jasLeftRep s))) / (1 / (ξ * (1 - ξ))) with hc'
  calc |c.arg + (τ * S₁.im + τ * (Real.cos φ - 1) * S₁.im - τ * Real.sin φ * (M - S₁.re) +
          τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im + τ * SB * Real.sin φ) - 2 * Real.pi * k| +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A
      ≤ (|τ * S₁.im - 2 * Real.pi * k| + |c.arg| + |τ * (Real.cos φ - 1) * S₁.im| +
          |τ * Real.sin φ * (M - S₁.re)| + |τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im| +
          |τ * SB * Real.sin φ|) + 16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A := by
        gcongr
        have := abs_add_le (τ * S₁.im - 2 * Real.pi * k) c.arg
        have := abs_add_le (τ * S₁.im - 2 * Real.pi * k + c.arg) (τ * (Real.cos φ - 1) * S₁.im)
        have := abs_sub (τ * S₁.im - 2 * Real.pi * k + c.arg + τ * (Real.cos φ - 1) * S₁.im)
          (τ * Real.sin φ * (M - S₁.re))
        have := abs_add_le (τ * S₁.im - 2 * Real.pi * k + c.arg + τ * (Real.cos φ - 1) * S₁.im -
          τ * Real.sin φ * (M - S₁.re)) (τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im)
        have := abs_add_le (τ * S₁.im - 2 * Real.pi * k + c.arg + τ * (Real.cos φ - 1) * S₁.im -
          τ * Real.sin φ * (M - S₁.re) + τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im)
          (τ * SB * Real.sin φ)
        calc |c.arg + (τ * S₁.im + τ * (Real.cos φ - 1) * S₁.im - τ * Real.sin φ * (M - S₁.re) +
              τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im + τ * SB * Real.sin φ) - 2 * Real.pi * k|
            = |τ * S₁.im - 2 * Real.pi * k + c.arg + τ * (Real.cos φ - 1) * S₁.im -
              τ * Real.sin φ * (M - S₁.re) + τ * (cexp (((-φ : ℝ) : ℂ) * I) * S₂).im +
              τ * SB * Real.sin φ| := by ring_nf
          _ ≤ _ := by linarith
    _ ≤ Real.pi / 2 := by linarith

/-! ## Summation -/

/-- A summable family whose distinguished term is `≤ −X/2` and whose other terms are dominated by a
nonnegative summable `g` with `Σ g < X/2` has negative real sum. -/
theorem re_tsum_neg_of_bounds {V : XiZeroCopy → ℂ} (hV : Summable V) (qt : XiZeroCopy) {X : ℝ}
    (g : XiZeroCopy → ℝ) (hg0 : ∀ q, 0 ≤ g q) (hgs : Summable g) (hgX : ∑' q, g q < X / 2)
    (htarget : (V qt).re ≤ -X / 2) (hrest : ∀ q, q ≠ qt → (V q).re ≤ g q) :
    (∑' q, V q).re < 0 := by
  classical
  rw [Complex.re_tsum hV]
  set h : XiZeroCopy → ℝ := fun q => g q - if q = qt then X / 2 + g qt else 0 with hh
  have hsite : Summable (fun q : XiZeroCopy => if q = qt then X / 2 + g qt else 0) :=
    summable_of_ne_finset_zero (s := {qt}) fun q hq => by simp at hq; simp [hq]
  have hhs : Summable h := hgs.sub hsite
  have hle : ∀ q, (V q).re ≤ h q := by
    intro q
    by_cases hq : q = qt
    · subst hq; simp only [hh, if_true]; linarith
    · simp only [hh, if_neg hq, sub_zero]; exact hrest q hq
  have hsum : ∑' q, h q = ∑' q, g q - (X / 2 + g qt) := by
    rw [hh, Summable.tsum_sub hgs hsite, tsum_ite_eq]
  calc ∑' q, (V q).re ≤ ∑' q, h q :=
        Summable.tsum_le_tsum hle ((Complex.reCLM.summable hV)) hhs
    _ < 0 := by rw [hsum]; linarith [hg0 qt]

/-- The window sum against the far shift is at most `B^ε M`. -/
theorem norm_jasLogWeightSum_le_exp_mul {A B : ℕ} (hB : 1 ≤ B) {z : ℂ} {ε : ℝ} (hz : z.re ≤ ε)
    (hε : 0 ≤ ε) :
    ‖jasLogWeightSum A B z‖ ≤ Real.exp (ε * Real.log B) * jasLogMass A B := by
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  rcases le_or_gt 0 z.re with h0 | h0
  · refine (norm_jasLogWeightSum_le_of_re_nonneg h0).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hlogB))
      (jasLogMass_nonneg A B)
  · refine (norm_jasLogWeightSum_le_mass h0.le).trans ?_
    have : 1 ≤ Real.exp (ε * Real.log B) := Real.one_le_exp (mul_nonneg hε hlogB)
    nlinarith [jasLogMass_nonneg A B]

/-! ## The amplification contradiction -/

/-- The case analysis for a single zero: aligned window points are non-positive, suppressed window
points, bulk points and far points are dominated by their class bounds. -/
theorem re_le_indicator_sum {V : ℂ} {w Y₁ Y₂ Y₄ : ℝ} (P₁ Q₁ P₂ P₄ : Prop)
    [Decidable P₁] [Decidable Q₁] [Decidable P₂] [Decidable P₄]
    (hw : 0 ≤ w) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) (hY₄ : 0 ≤ Y₄)
    (hcover : P₁ ∨ P₂ ∨ P₄)
    (hclus : P₁ → ¬ Q₁ → V.re ≤ 0) (hsup : P₁ → Q₁ → ‖V‖ ≤ w * Y₁)
    (hbulk : P₂ → ‖V‖ ≤ w * Y₂) (hfar : ‖V‖ ≤ w * Y₄) :
    V.re ≤ (if P₁ ∧ Q₁ then Y₁ * w else 0) + (if P₂ then Y₂ * w else 0) +
      (if P₄ then Y₄ * w else 0) := by
  have hre := Complex.re_le_norm V
  have e1 : 0 ≤ (if P₁ ∧ Q₁ then Y₁ * w else 0) := by split_ifs <;> positivity
  have e2 : 0 ≤ (if P₂ then Y₂ * w else 0) := by split_ifs <;> positivity
  have e4 : 0 ≤ (if P₄ then Y₄ * w else 0) := by split_ifs <;> positivity
  by_cases h1 : P₁
  · by_cases hq : Q₁
    · rw [if_pos ⟨h1, hq⟩]
      have := hsup h1 hq
      linarith [mul_comm w Y₁]
    · have := hclus h1 hq
      linarith
  · rcases hcover with h | h | h
    · exact absurd h h1
    · rw [if_pos h]
      have := hbulk h
      linarith [mul_comm w Y₂]
    · rw [if_pos h]
      have := hfar
      linarith [mul_comm w Y₄]

/-- **The amplification contradiction.**  Under the listed numerical conditions the log-weight
Bernoulli sum centred at the target has negative real part. -/
theorem re_tsum_jasLogWeightValue_neg {ξ : ℂ} {δ ε γ : ℝ} (hδ : ξ.re = 1 / 2 - δ) (hδ0 : 0 < δ)
    (qt : XiZeroCopy) (hqt : jasLeftRep (qt.1 : ℂ) = ξ)
    (hstrip : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ + ε)
    (hwin : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ 1 → |(q.1 : ℂ).re - 1 / 2| ≤ δ)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) {τ φ lam0 L₀ T₀ : ℝ} (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 4) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ Real.pi / 2) (hcos : 1 / 2 ≤ Real.cos φ)
    (hdev : 2 * τ * Real.log B * Real.exp ((ε - 1) * Real.log (A + 1)) ≤ 1 / 2)
    (hM : 0 < jasLogMass A B)
    (hr : 16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A ≤ 1)
    (hwξ : 1 / (ξ * (1 - ξ)) ≠ 0)
    (harg : (1 / (ξ * (1 - ξ))).arg + τ * (jasLogMass A B -
      ∑ p ∈ jasPrimeWindow A B, Real.log p / p * Real.exp ((2 * ξ.re - 1) * Real.log p)) *
        Real.sin φ = Real.pi)
    (hsinM : τ * jasLogMass A B * Real.sin φ ≤ 13)
    (hL : L₀ ≤ τ * jasLogMass A B * lam0)
    (halign : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ 1 →
      1 - (jasLogWeightSum A B (ξ - jasLeftRep q.1)).re / jasLogMass A B ≤ lam0 →
      ∃ k : ℤ, |τ * (jasLogWeightSum A B (ξ - jasLeftRep q.1)).im - 2 * Real.pi * k| ≤
        Real.pi / 4)
    (hcl : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ 1 →
      ‖(1 / (jasLeftRep q.1 * (1 - jasLeftRep q.1))) / (1 / (ξ * (1 - ξ))) - 1‖ ≤ 1 / 2 ∧
      2 * ‖(1 / (jasLeftRep q.1 * (1 - jasLeftRep q.1))) / (1 / (ξ * (1 - ξ))) - 1‖ +
        τ * Real.sin φ ^ 2 * (jasLogMass A B * Real.sqrt (2 * lam0)) +
        τ * Real.sin φ * jasLogMass A B * lam0 +
        2 * (τ * (Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B)) +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A ≤ Real.pi / 4)
    (hbulk : ∀ q : XiZeroCopy, 1 < |(q.1 : ℂ).im - γ| → |(q.1 : ℂ).im| ≤ T₀ →
      ‖jasLogWeightSum A B (ξ - jasLeftRep q.1)‖ ≤ 99)
    {Y₁ Y₂ Y₄ X : ℝ}
    (hY₁e : Y₁ = Real.exp (τ * jasLogMass A B * Real.cos φ - L₀ / 2 + 26 +
        τ * (Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B) +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A))
    (hY₂e : Y₂ = Real.exp (τ * (99 + Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B) +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A))
    (hY₄e : Y₄ = Real.exp (τ * (Real.exp (ε * Real.log B) * jasLogMass A B +
          Real.exp (-δ * Real.log (A + 1)) * jasLogMass A B) +
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A))
    (hXe : X = ‖1 / (ξ * (1 - ξ))‖ * Real.exp (τ * jasLogMass A B * Real.cos φ -
        16 * τ ^ 2 * Real.log B ^ 2 / Real.sqrt A))
    (hY₁ : Y₁ * (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ≤ X / 8)
    (hY₂ : Y₂ * (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ≤ X / 8)
    (hY₄ : Y₄ * (∑' q : XiZeroCopy, {q : XiZeroCopy | T₀ < |(q.1 : ℂ).im|}.indicator
          (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q) ≤ X / 8) :
    (∑' q : XiZeroCopy, jasLogWeightValue ξ A B τ φ (q.1 : ℂ)).re < 0 := by
  classical
  have hB : 1 ≤ B := le_trans hA hAB
  have hsin0 : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hcos0 : 0 ≤ Real.cos φ := by linarith
  have hws : Summable (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) :=
    summable_inv_mul_one_sub.norm
  have hY₁0 : 0 ≤ Y₁ := by rw [hY₁e]; exact (Real.exp_pos _).le
  have hY₂0 : 0 ≤ Y₂ := by rw [hY₂e]; exact (Real.exp_pos _).le
  have hY₄0 : 0 ≤ Y₄ := by rw [hY₄e]; exact (Real.exp_pos _).le
  have hX0 : 0 < X := by rw [hXe]; exact mul_pos (norm_pos_iff.mpr hwξ) (Real.exp_pos _)
  -- per-zero facts
  have hfar : ∀ q : XiZeroCopy, ‖jasLogWeightValue ξ A B τ φ q.1‖ ≤
      ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * Y₄ := fun q => by
    rw [hY₄e]
    exact norm_jasLogWeightValue_le_bulk hA hτ hε0 hε hδ0.le hδ (hstrip q) hdev
      (norm_jasLogWeightSum_le_exp_mul hB (jasLeftRep_shifts hδ (hstrip q)).1 hε0)
  have hVs : Summable (fun q : XiZeroCopy => jasLogWeightValue ξ A B τ φ q.1) :=
    Summable.of_norm_bounded (hws.mul_right Y₄) hfar
  -- the dominating family
  let g : XiZeroCopy → ℝ := fun q =>
    (if |(q.1 : ℂ).im - γ| ≤ 1 ∧
        lam0 < 1 - (jasLogWeightSum A B (ξ - jasLeftRep q.1)).re / jasLogMass A B
      then Y₁ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) +
    (if 1 < |(q.1 : ℂ).im - γ| ∧ |(q.1 : ℂ).im| ≤ T₀
      then Y₂ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) +
    (if T₀ < |(q.1 : ℂ).im| then Y₄ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0)
  have hite : ∀ (P : Prop) [Decidable P] (Y : ℝ), 0 ≤ Y → ∀ q : XiZeroCopy,
      0 ≤ (if P then Y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) ∧
      (if P then Y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) ≤
        Y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    intro P _ Y hY q
    split_ifs
    · exact ⟨by positivity, le_rfl⟩
    · exact ⟨le_rfl, by positivity⟩
  have hsite : ∀ (P : XiZeroCopy → Prop) [DecidablePred P] (Y : ℝ), 0 ≤ Y →
      Summable (fun q : XiZeroCopy => if P q then Y * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) :=
    fun P _ Y hY => Summable.of_nonneg_of_le (fun q => (hite (P q) Y hY q).1)
      (fun q => (hite (P q) Y hY q).2) (hws.mul_left Y)
  have hs₁ := hsite (fun q : XiZeroCopy => |(q.1 : ℂ).im - γ| ≤ 1 ∧
      lam0 < 1 - (jasLogWeightSum A B (ξ - jasLeftRep q.1)).re / jasLogMass A B) Y₁ hY₁0
  have hs₂ := hsite (fun q : XiZeroCopy => 1 < |(q.1 : ℂ).im - γ| ∧ |(q.1 : ℂ).im| ≤ T₀) Y₂ hY₂0
  have hs₄ := hsite (fun q : XiZeroCopy => T₀ < |(q.1 : ℂ).im|) Y₄ hY₄0
  have hg0 : ∀ q, 0 ≤ g q := fun q =>
    add_nonneg (add_nonneg (hite _ Y₁ hY₁0 q).1 (hite _ Y₂ hY₂0 q).1) (hite _ Y₄ hY₄0 q).1
  have hgs : Summable g := (hs₁.add hs₂).add hs₄
  have hT₁ : ∑' q : XiZeroCopy, (if |(q.1 : ℂ).im - γ| ≤ 1 ∧
        lam0 < 1 - (jasLogWeightSum A B (ξ - jasLeftRep q.1)).re / jasLogMass A B
      then Y₁ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) ≤ X / 8 := by
    refine le_trans (Summable.tsum_le_tsum (fun q => (hite _ Y₁ hY₁0 q).2) hs₁
      (hws.mul_left Y₁)) ?_
    rw [tsum_mul_left]; exact hY₁
  have hT₂ : ∑' q : XiZeroCopy, (if 1 < |(q.1 : ℂ).im - γ| ∧ |(q.1 : ℂ).im| ≤ T₀
      then Y₂ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) ≤ X / 8 := by
    refine le_trans (Summable.tsum_le_tsum (fun q => (hite _ Y₂ hY₂0 q).2) hs₂
      (hws.mul_left Y₂)) ?_
    rw [tsum_mul_left]; exact hY₂
  have hT₄ : ∑' q : XiZeroCopy, (if T₀ < |(q.1 : ℂ).im|
      then Y₄ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) ≤ X / 8 := by
    have he : (fun q : XiZeroCopy => if T₀ < |(q.1 : ℂ).im|
        then Y₄ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) =
        fun q => Y₄ * {q : XiZeroCopy | T₀ < |(q.1 : ℂ).im|}.indicator
          (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q := by
      funext q
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs <;> simp
    rw [he, tsum_mul_left]; exact hY₄
  have hgX : ∑' q, g q < X / 2 := by
    have hsplit : ∑' q, g q = ∑' q : XiZeroCopy, (if |(q.1 : ℂ).im - γ| ≤ 1 ∧
          lam0 < 1 - (jasLogWeightSum A B (ξ - jasLeftRep q.1)).re / jasLogMass A B
        then Y₁ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) +
        ∑' q : XiZeroCopy, (if 1 < |(q.1 : ℂ).im - γ| ∧ |(q.1 : ℂ).im| ≤ T₀
          then Y₂ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) +
        ∑' q : XiZeroCopy, (if T₀ < |(q.1 : ℂ).im|
          then Y₄ * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ else 0) := by
      rw [← Summable.tsum_add hs₁ hs₂, ← Summable.tsum_add (hs₁.add hs₂) hs₄]
    rw [hsplit]
    linarith
  have htarget : (jasLogWeightValue ξ A B τ φ qt.1).re ≤ -X / 2 := by
    rw [← re_jasLogWeightValue_jasLeftRep, hqt]
    have h := re_jasLogWeightValue_target_le hA hτ hε0 hε hφ0 hφ1 (by rw [hδ]; linarith)
      hdev hr hwξ harg
    rw [hXe]; linarith
  refine re_tsum_neg_of_bounds hVs qt g hg0 hgs hgX htarget fun q _ => ?_
  refine re_le_indicator_sum _ _ _ _ (norm_nonneg _) hY₁0 hY₂0 hY₄0 ?_ ?_ ?_ ?_ (hfar q)
  · by_cases h1 : |(q.1 : ℂ).im - γ| ≤ 1
    · exact Or.inl h1
    · by_cases h2 : |(q.1 : ℂ).im| ≤ T₀
      · exact Or.inr (Or.inl ⟨lt_of_not_ge h1, h2⟩)
      · exact Or.inr (Or.inr (lt_of_not_ge h2))
  · intro h1 hq
    obtain ⟨k, hk⟩ := halign q h1 (le_of_not_gt hq)
    obtain ⟨hc, hbud⟩ := hcl q h1
    exact re_jasLogWeightValue_nonpos_cluster hA hτ hε0 hε hδ0.le hδ (hwin q h1) hdev hM hsin0
      hcos0 hwξ harg (le_of_not_gt hq) hk hc hbud
  · intro h1 hq
    rw [hY₁e]
    exact norm_jasLogWeightValue_le_suppressed hA hτ hε0 hε hδ0.le hδ (hwin q h1) hdev hM hsin0
      hcos hsinM hq.le hL
  · intro h2
    rw [hY₂e]
    exact norm_jasLogWeightValue_le_bulk hA hτ hε0 hε hδ0.le hδ (hstrip q) hdev
      (hbulk q h2.1 h2.2)

end

end RHTower
