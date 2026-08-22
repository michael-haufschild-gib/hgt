import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeDecay

/-!
# Burnol's L-Property and the class `𝓛¹`

Definition 10 of arXiv:math/0203120 asks a function analytic with finitely many poles to satisfy
`F(σ+iτ) = O_{a,b,ε}((1+|τ|)^{(1/2-a)^+ + ε})` on every vertical strip `a ≤ σ ≤ b`, and Definition
12 singles out those functions of `L¹` whose Mellin transforms decrease faster than every power of
`|s|` in every vertical strip.  Both are growth conditions on vertical strips; this file records
them and their elementary stability properties, including the mechanism of Lemma 4.10 — the class
of rapidly decreasing functions is stable under multiplication by anything of polynomial vertical
growth, and under the reflection `s ↦ 1-s`.

## Main results

* `HasLProperty`, `HasStripRapidDecrease`
* `HasStripRapidDecrease.hasLProperty`
* `HasStripRapidDecrease.mul_stripPolyGrowth`, `HasStripRapidDecrease.comp_one_sub`
* `hasStripRapidDecrease_chi_mul_reflect` — **Burnol's Lemma 4.10**
-/

namespace RHTower

open Complex

noncomputable section

/-- **Burnol's L-Property (Definition 10).**  The estimate is asked away from the poles, which for
the extended Sonine transforms sit at `s = 0` and `s = 1`; requiring `1 ≤ |Im s|` keeps clear of
them. -/
def HasLProperty (F : ℂ → ℂ) : Prop :=
  ∀ a b ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
    ‖F s‖ ≤ C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε)

/-- **Burnol's `𝓛¹` growth condition (Definition 12):** faster than every power on every vertical
strip. -/
def HasStripRapidDecrease (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
    ‖F s‖ ≤ C * (1 + |s.im|) ^ (-(N : ℝ))

/-- Polynomial vertical growth asked only away from the real axis.  This is the correct hypothesis
for Burnol's Lemma 4.10: the functional-equation factor `χ` has poles at `s = 1, 3, 5, …`, all on
the real axis, so a bound on a full strip is false while a bound for `1 ≤ |Im s|` holds. -/
def HasStripPolyGrowthOffReal (G : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| → ‖G s‖ ≤ C * (1 + |s.im|) ^ N

theorem GaloisForLFunctions.HasStripPolyGrowth.offReal {G : ℂ → ℂ}
    (hG : GaloisForLFunctions.HasStripPolyGrowth G) : HasStripPolyGrowthOffReal G := by
  intro a b
  obtain ⟨N, C, hC, hb⟩ := hG a b
  exact ⟨N, C, hC, fun s h1 h2 _ => hb s h1 h2⟩

theorem one_le_one_add_abs_im (s : ℂ) : (1 : ℝ) ≤ 1 + |s.im| := by
  have := abs_nonneg s.im
  linarith

theorem HasLProperty.add {F G : ℂ → ℂ} (hF : HasLProperty F) (hG : HasLProperty G) :
    HasLProperty (fun s => F s + G s) := by
  intro a b ε hε
  obtain ⟨CF, hCF, hFb⟩ := hF a b ε hε
  obtain ⟨CG, hCG, hGb⟩ := hG a b ε hε
  refine ⟨CF + CG, by linarith, fun s h1 h2 h3 => ?_⟩
  have hpos : (0 : ℝ) ≤ (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) :=
    Real.rpow_nonneg (by linarith [abs_nonneg s.im]) _
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ CF * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε)
        + CG * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) := add_le_add (hFb s h1 h2 h3)
          (hGb s h1 h2 h3)
    _ = (CF + CG) * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) := by ring

theorem HasLProperty.const_mul {F : ℂ → ℂ} (hF : HasLProperty F) (c : ℂ) :
    HasLProperty (fun s => c * F s) := by
  intro a b ε hε
  obtain ⟨C, hC, hFb⟩ := hF a b ε hε
  refine ⟨‖c‖ * C, by positivity, fun s h1 h2 h3 => ?_⟩
  rw [norm_mul]
  have hpos : (0 : ℝ) ≤ (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) :=
    Real.rpow_nonneg (by linarith [abs_nonneg s.im]) _
  calc ‖c‖ * ‖F s‖ ≤ ‖c‖ * (C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε)) :=
        mul_le_mul_of_nonneg_left (hFb s h1 h2 h3) (norm_nonneg c)
    _ = ‖c‖ * C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) := by ring

theorem HasStripRapidDecrease.add {F G : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    (hG : HasStripRapidDecrease G) : HasStripRapidDecrease (fun s => F s + G s) := by
  intro a b N
  obtain ⟨CF, hCF, hFb⟩ := hF a b N
  obtain ⟨CG, hCG, hGb⟩ := hG a b N
  refine ⟨CF + CG, by linarith, fun s h1 h2 h3 => ?_⟩
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ CF * (1 + |s.im|) ^ (-(N : ℝ)) + CG * (1 + |s.im|) ^ (-(N : ℝ)) :=
        add_le_add (hFb s h1 h2 h3) (hGb s h1 h2 h3)
    _ = (CF + CG) * (1 + |s.im|) ^ (-(N : ℝ)) := by ring

/-- Rapid decrease implies the L-Property. -/
theorem HasStripRapidDecrease.hasLProperty {F : ℂ → ℂ} (hF : HasStripRapidDecrease F) :
    HasLProperty F := by
  intro a b ε hε
  obtain ⟨C, hC, hFb⟩ := hF a b 0
  refine ⟨C, hC, fun s h1 h2 h3 => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |s.im| := one_le_one_add_abs_im s
  have hexp : (0 : ℝ) ≤ max (1 / 2 - a) 0 + ε := by
    have := le_max_right (1 / 2 - a) (0 : ℝ)
    linarith
  have h0 : (1 + |s.im|) ^ (-(0 : ℕ) : ℝ) = 1 := by
    norm_num
  have hmono : (1 : ℝ) ≤ (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) :=
    Real.one_le_rpow hbase hexp
  have hb := hFb s h1 h2 h3
  rw [h0, mul_one] at hb
  calc ‖F s‖ ≤ C := hb
    _ = C * 1 := by ring
    _ ≤ C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) := mul_le_mul_of_nonneg_left hmono hC

/-- **Lemma 4.10's mechanism:** rapid vertical decrease survives multiplication by anything of
polynomial vertical growth. -/
theorem HasStripRapidDecrease.mul_stripPolyGrowth {F G : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    (hG : HasStripPolyGrowthOffReal G) :
    HasStripRapidDecrease (fun s => F s * G s) := by
  intro a b N
  obtain ⟨M, CG, hCG, hGb⟩ := hG a b
  obtain ⟨CF, hCF, hFb⟩ := hF a b (N + M)
  refine ⟨CF * CG, by positivity, fun s h1 h2 h3 => ?_⟩
  have hbase : (0 : ℝ) < 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hGpow : (1 + |s.im|) ^ M = (1 + |s.im|) ^ (M : ℝ) := (Real.rpow_natCast _ M).symm
  rw [norm_mul]
  have hprod : (CF * (1 + |s.im|) ^ (-((N + M : ℕ) : ℝ))) * (CG * (1 + |s.im|) ^ (M : ℝ))
      = CF * CG * (1 + |s.im|) ^ (-(N : ℝ)) := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hbase]
    push_cast
    ring_nf
  calc ‖F s‖ * ‖G s‖
      ≤ (CF * (1 + |s.im|) ^ (-((N + M : ℕ) : ℝ))) * (CG * (1 + |s.im|) ^ M) := by
        refine mul_le_mul (hFb s h1 h2 h3) (hGb s h1 h2 h3) (norm_nonneg _) ?_
        positivity
    _ = (CF * (1 + |s.im|) ^ (-((N + M : ℕ) : ℝ))) * (CG * (1 + |s.im|) ^ (M : ℝ)) := by
        rw [hGpow]
    _ = CF * CG * (1 + |s.im|) ^ (-(N : ℝ)) := hprod

/-- Rapid vertical decrease survives the reflection `s ↦ 1 - s`. -/
theorem HasStripRapidDecrease.comp_one_sub {F : ℂ → ℂ} (hF : HasStripRapidDecrease F) :
    HasStripRapidDecrease (fun s => F (1 - s)) := by
  intro a b N
  obtain ⟨C, hC, hFb⟩ := hF (1 - b) (1 - a) N
  refine ⟨C, hC, fun s h1 h2 h3 => ?_⟩
  have hre : (1 - s).re = 1 - s.re := by simp
  have him : |(1 - s).im| = |s.im| := by
    simp
  have hb := hFb (1 - s) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact h3)
  rw [him] at hb
  exact hb

/-- **Burnol's Lemma 4.10.**  The class of rapidly decreasing transforms is stable under
`F ↦ χ · F(1-·)` whenever the multiplier has polynomial vertical growth. -/
theorem hasStripRapidDecrease_chi_mul_reflect {F chi : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    (hchi : HasStripPolyGrowthOffReal chi) :
    HasStripRapidDecrease (fun s => chi s * F (1 - s)) := by
  have h := (hF.comp_one_sub).mul_stripPolyGrowth hchi
  intro a b N
  obtain ⟨C, hC, hb⟩ := h a b N
  refine ⟨C, hC, fun s h1 h2 h3 => ?_⟩
  have hval := hb s h1 h2 h3
  show ‖chi s * F (1 - s)‖ ≤ C * (1 + |s.im|) ^ (-(N : ℝ))
  rw [mul_comm (chi s)]
  exact hval

end

end RHTower
