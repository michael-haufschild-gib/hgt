import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeDecay

/-!
# Burnol's L-Property and the class `𝓛¹`

Definition 10 of arXiv:math/0203120 asks a function analytic with finitely many poles to satisfy
`F(σ+iτ) = O_{a,b,ε}((1+|τ|)^{(1/2-a)^+ + ε})` on every vertical strip `a ≤ σ ≤ b`, and Definition
12 singles out those functions whose Mellin transforms decrease faster than every power of `|τ|` in
every vertical strip.  Both estimates are asked *away from the poles*; since the poles are finitely
many, "away from the poles" is a threshold `T ≤ |τ|`, and that is how both conditions are recorded
here.

## Main results

* `HasLProperty`, `HasStripRapidDecrease`, `HasStripPolyGrowthOffReal`
* `HasStripRapidDecrease.hasLProperty`
* `HasStripRapidDecrease.mul_stripPolyGrowth`, `HasStripRapidDecrease.comp_one_sub`
* `hasStripRapidDecrease_chi_mul_reflect` — **Burnol's Lemma 4.10**
-/

namespace RHTower

open Complex

noncomputable section

/-- **Burnol's L-Property (Definition 10).** -/
def HasLProperty (F : ℂ → ℂ) : Prop :=
  ∀ a b ε : ℝ, 0 < ε → ∃ T C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
    ‖F s‖ ≤ C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε)

/-- **Burnol's `𝓛¹` growth condition (Definition 12):** faster than every power on every vertical
strip. -/
def HasStripRapidDecrease (F : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∀ N : ℕ, ∃ T C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
    ‖F s‖ ≤ C * (1 + |s.im|) ^ (-(N : ℝ))

/-- Polynomial vertical growth asked only away from the real axis.  This is the correct hypothesis
for Burnol's Lemma 4.10: the functional-equation factor `χ` has poles at `s = 1, 3, 5, …`, all on
the real axis, so a bound on a full strip is false while a bound above a height is true. -/
def HasStripPolyGrowthOffReal (G : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ (T : ℝ) (N : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖G s‖ ≤ C * (1 + |s.im|) ^ N

theorem GaloisForLFunctions.HasStripPolyGrowth.offReal {G : ℂ → ℂ}
    (hG : GaloisForLFunctions.HasStripPolyGrowth G) : HasStripPolyGrowthOffReal G := by
  intro a b
  obtain ⟨N, C, hC, hb⟩ := hG a b
  exact ⟨0, N, C, hC, fun s h1 h2 _ => hb s h1 h2⟩

theorem one_le_one_add_abs_im (s : ℂ) : (1 : ℝ) ≤ 1 + |s.im| := by
  have := abs_nonneg s.im
  linarith

theorem HasLProperty.add {F G : ℂ → ℂ} (hF : HasLProperty F) (hG : HasLProperty G) :
    HasLProperty (fun s => F s + G s) := by
  intro a b ε hε
  obtain ⟨TF, CF, hCF, hFb⟩ := hF a b ε hε
  obtain ⟨TG, CG, hCG, hGb⟩ := hG a b ε hε
  refine ⟨max TF TG, CF + CG, by linarith, fun s h1 h2 h3 => ?_⟩
  have hTF : TF ≤ |s.im| := le_trans (le_max_left _ _) h3
  have hTG : TG ≤ |s.im| := le_trans (le_max_right _ _) h3
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ CF * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε)
        + CG * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) :=
          add_le_add (hFb s h1 h2 hTF) (hGb s h1 h2 hTG)
    _ = (CF + CG) * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) := by ring

theorem HasLProperty.const_mul {F : ℂ → ℂ} (hF : HasLProperty F) (c : ℂ) :
    HasLProperty (fun s => c * F s) := by
  intro a b ε hε
  obtain ⟨T, C, hC, hFb⟩ := hF a b ε hε
  refine ⟨T, ‖c‖ * C, by positivity, fun s h1 h2 h3 => ?_⟩
  rw [norm_mul]
  calc ‖c‖ * ‖F s‖ ≤ ‖c‖ * (C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε)) :=
        mul_le_mul_of_nonneg_left (hFb s h1 h2 h3) (norm_nonneg c)
    _ = ‖c‖ * C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) := by ring

theorem HasStripRapidDecrease.add {F G : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    (hG : HasStripRapidDecrease G) : HasStripRapidDecrease (fun s => F s + G s) := by
  intro a b N
  obtain ⟨TF, CF, hCF, hFb⟩ := hF a b N
  obtain ⟨TG, CG, hCG, hGb⟩ := hG a b N
  refine ⟨max TF TG, CF + CG, by linarith, fun s h1 h2 h3 => ?_⟩
  have hTF : TF ≤ |s.im| := le_trans (le_max_left _ _) h3
  have hTG : TG ≤ |s.im| := le_trans (le_max_right _ _) h3
  calc ‖F s + G s‖ ≤ ‖F s‖ + ‖G s‖ := norm_add_le _ _
    _ ≤ CF * (1 + |s.im|) ^ (-(N : ℝ)) + CG * (1 + |s.im|) ^ (-(N : ℝ)) :=
        add_le_add (hFb s h1 h2 hTF) (hGb s h1 h2 hTG)
    _ = (CF + CG) * (1 + |s.im|) ^ (-(N : ℝ)) := by ring

/-- Rapid decrease implies the L-Property. -/
theorem HasStripRapidDecrease.hasLProperty {F : ℂ → ℂ} (hF : HasStripRapidDecrease F) :
    HasLProperty F := by
  intro a b ε hε
  obtain ⟨T, C, hC, hFb⟩ := hF a b 0
  refine ⟨T, C, hC, fun s h1 h2 h3 => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |s.im| := one_le_one_add_abs_im s
  have hexp : (0 : ℝ) ≤ max (1 / 2 - a) 0 + ε := by
    have := le_max_right (1 / 2 - a) (0 : ℝ)
    linarith
  have h0 : (1 + |s.im|) ^ (-(0 : ℕ) : ℝ) = 1 := by norm_num
  have hmono : (1 : ℝ) ≤ (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) :=
    Real.one_le_rpow hbase hexp
  have hb := hFb s h1 h2 h3
  rw [h0, mul_one] at hb
  calc ‖F s‖ ≤ C := hb
    _ = C * 1 := by ring
    _ ≤ C * (1 + |s.im|) ^ (max (1 / 2 - a) 0 + ε) := mul_le_mul_of_nonneg_left hmono hC

/-- **Lemma 4.10's mechanism:** rapid vertical decrease survives multiplication by anything of
polynomial vertical growth away from the real axis. -/
theorem HasStripRapidDecrease.mul_stripPolyGrowth {F G : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    (hG : HasStripPolyGrowthOffReal G) : HasStripRapidDecrease (fun s => F s * G s) := by
  intro a b N
  obtain ⟨TG, M, CG, hCG, hGb⟩ := hG a b
  obtain ⟨TF, CF, hCF, hFb⟩ := hF a b (N + M)
  refine ⟨max TF TG, CF * CG, by positivity, fun s h1 h2 h3 => ?_⟩
  have hTF : TF ≤ |s.im| := le_trans (le_max_left _ _) h3
  have hTG : TG ≤ |s.im| := le_trans (le_max_right _ _) h3
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
        refine mul_le_mul (hFb s h1 h2 hTF) (hGb s h1 h2 hTG) (norm_nonneg _) ?_
        positivity
    _ = (CF * (1 + |s.im|) ^ (-((N + M : ℕ) : ℝ))) * (CG * (1 + |s.im|) ^ (M : ℝ)) := by
        rw [hGpow]
    _ = CF * CG * (1 + |s.im|) ^ (-(N : ℝ)) := hprod

/-- Rapid vertical decrease survives the reflection `s ↦ 1 - s`. -/
theorem HasStripRapidDecrease.comp_one_sub {F : ℂ → ℂ} (hF : HasStripRapidDecrease F) :
    HasStripRapidDecrease (fun s => F (1 - s)) := by
  intro a b N
  obtain ⟨T, C, hC, hFb⟩ := hF (1 - b) (1 - a) N
  refine ⟨T, C, hC, fun s h1 h2 h3 => ?_⟩
  have hre : (1 - s).re = 1 - s.re := by simp
  have him : |(1 - s).im| = |s.im| := by simp
  have hb := hFb (1 - s) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact h3)
  rw [him] at hb
  exact hb

/-- **Burnol's Lemma 4.10.**  The class of rapidly decreasing transforms is stable under
`F ↦ χ · F(1-·)` whenever the multiplier has polynomial vertical growth off the real axis. -/
theorem hasStripRapidDecrease_chi_mul_reflect {F chi : ℂ → ℂ} (hF : HasStripRapidDecrease F)
    (hchi : HasStripPolyGrowthOffReal chi) :
    HasStripRapidDecrease (fun s => chi s * F (1 - s)) := by
  have h := (hF.comp_one_sub).mul_stripPolyGrowth hchi
  intro a b N
  obtain ⟨T, C, hC, hb⟩ := h a b N
  refine ⟨T, C, hC, fun s h1 h2 h3 => ?_⟩
  have hval := hb s h1 h2 h3
  show ‖chi s * F (1 - s)‖ ≤ C * (1 + |s.im|) ^ (-(N : ℝ))
  rw [mul_comm (chi s)]
  exact hval

end

end RHTower
