import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform

/-!
# The Gamma quotient on the closed lower substrip, two-sided and uniform

On the closed substrip `0 ≤ τ ≤ σ₁ < 1` the Gamma quotient of the Suzuki transport,

`‖Γ(1-τ+ix)‖ / ‖Γ(1+τ+ix)‖`,

is bounded above by a constant and below by `c (1+|x|)^{-2σ₁}`, uniformly in the height `τ`.  Above
`|x| = 1` this is the parameter-uniform vertical Gamma-ratio bound with `a = 1-τ`, `δ = 2τ`; inside
the unit box it is continuity and positivity on a compact set.  Conjugation symmetry in the height
transports both halves to the negative ray.

The lower bound is the quantitative statement that the inverse Gamma transport grows at most
polynomially on the cone swept by the segments from the frequency origin.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The Suzuki Gamma quotient as a function of height and frequency. -/
def gammaRatioPair (p : ℝ × ℝ) : ℝ :=
  ‖Complex.Gamma (((1 - p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)‖
    / ‖Complex.Gamma (((1 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)‖

private theorem gamma_line_ne_zero {a x : ℝ} (ha : 0 < a) :
    Complex.Gamma ((a : ℂ) + (x : ℂ) * Complex.I) ≠ 0 := by
  refine Complex.Gamma_ne_zero ?_
  intro n h
  have hre := congrArg Complex.re h
  simp at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem continuousAt_gamma_line {a x : ℝ} (ha : 0 < a) :
    ContinuousAt Complex.Gamma ((a : ℂ) + (x : ℂ) * Complex.I) := by
  refine Complex.continuousAt_Gamma _ ?_
  intro n h
  have hre := congrArg Complex.re h
  simp at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem gammaRatioPair_pos {σ₁ : ℝ} (h1 : σ₁ < 1) {p : ℝ × ℝ} (hp : p.1 ∈ Icc (0 : ℝ) σ₁) :
    0 < gammaRatioPair p := by
  have hnum : 0 < ‖Complex.Gamma (((1 - p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (gamma_line_ne_zero (by linarith [hp.1, hp.2]))
  have hden : 0 < ‖Complex.Gamma (((1 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (gamma_line_ne_zero (by linarith [hp.1]))
  rw [gammaRatioPair]
  positivity

theorem continuousOn_gammaRatioPair {σ₁ : ℝ} (h1 : σ₁ < 1) :
    ContinuousOn gammaRatioPair (Icc (0 : ℝ) σ₁ ×ˢ (univ : Set ℝ)) := by
  intro p hp
  have hp1 : p.1 ∈ Icc (0 : ℝ) σ₁ := hp.1
  have hnum : ContinuousAt
      (fun q : ℝ × ℝ => ‖Complex.Gamma (((1 - q.1 : ℝ) : ℂ) + (q.2 : ℂ) * Complex.I)‖) p := by
    have hinner : ContinuousAt
        (fun q : ℝ × ℝ => ((1 - q.1 : ℝ) : ℂ) + (q.2 : ℂ) * Complex.I) p := by fun_prop
    have hcomp : ContinuousAt (Complex.Gamma ∘
        (fun q : ℝ × ℝ => ((1 - q.1 : ℝ) : ℂ) + (q.2 : ℂ) * Complex.I)) p :=
      ContinuousAt.comp
        (continuousAt_gamma_line (a := 1 - p.1) (x := p.2) (by linarith [hp1.1, hp1.2])) hinner
    exact hcomp.norm
  have hden : ContinuousAt
      (fun q : ℝ × ℝ => ‖Complex.Gamma (((1 + q.1 : ℝ) : ℂ) + (q.2 : ℂ) * Complex.I)‖) p := by
    have hinner : ContinuousAt
        (fun q : ℝ × ℝ => ((1 + q.1 : ℝ) : ℂ) + (q.2 : ℂ) * Complex.I) p := by fun_prop
    have hcomp : ContinuousAt (Complex.Gamma ∘
        (fun q : ℝ × ℝ => ((1 + q.1 : ℝ) : ℂ) + (q.2 : ℂ) * Complex.I)) p :=
      ContinuousAt.comp
        (continuousAt_gamma_line (a := 1 + p.1) (x := p.2) (by linarith [hp1.1])) hinner
    exact hcomp.norm
  have hdenne : ‖Complex.Gamma (((1 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gamma_line_ne_zero (by linarith [hp1.1]))
  exact ((hnum.div hden hdenne)).continuousWithinAt

/-- The Gamma quotient is even in the height. -/
theorem gammaRatioPair_neg (τ x : ℝ) : gammaRatioPair (τ, -x) = gammaRatioPair (τ, x) := by
  have hconj : ∀ a : ℝ, ‖Complex.Gamma ((a : ℂ) + ((-x : ℝ) : ℂ) * Complex.I)‖
      = ‖Complex.Gamma ((a : ℂ) + (x : ℂ) * Complex.I)‖ := by
    intro a
    have h : (starRingEnd ℂ) ((a : ℂ) + (x : ℂ) * Complex.I)
        = (a : ℂ) + ((-x : ℝ) : ℂ) * Complex.I := by
      simp
    rw [← h, _root_.RHTower.norm_Gamma_conj]
  simp only [gammaRatioPair]
  rw [hconj (1 - τ), hconj (1 + τ)]

/-- **The two-sided uniform Gamma quotient bound on the closed lower substrip.** -/
theorem exists_twoSided_gammaRatioPair {σ₁ : ℝ} (h0 : 0 ≤ σ₁) (h1 : σ₁ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ τ : ℝ, τ ∈ Icc (0 : ℝ) σ₁ → ∀ x : ℝ,
      c * (1 + |x|) ^ (-(2 * σ₁)) ≤ gammaRatioPair (τ, x) ∧ gammaRatioPair (τ, x) ≤ C := by
  -- the far field, from the parameter-uniform vertical law
  obtain ⟨c₀, C₀, hc₀, hC₀, hfar⟩ :=
    exists_twoSided_gamma_vertical_ratio (a₁ := 1) (δ₁ := 2 * σ₁) zero_le_one (by linarith)
  -- the unit box, by compactness
  have hbox : IsCompact (Icc (0 : ℝ) σ₁ ×ˢ Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hboxne : (Icc (0 : ℝ) σ₁ ×ˢ Icc (-1 : ℝ) 1).Nonempty :=
    ⟨(0, 0), ⟨⟨le_rfl, h0⟩, ⟨by norm_num, by norm_num⟩⟩⟩
  have hsub : Icc (0 : ℝ) σ₁ ×ˢ Icc (-1 : ℝ) 1 ⊆ Icc (0 : ℝ) σ₁ ×ˢ (univ : Set ℝ) :=
    fun q hq => ⟨hq.1, mem_univ _⟩
  obtain ⟨q₀, hq₀mem, hq₀min⟩ := hbox.exists_isMinOn hboxne
    ((continuousOn_gammaRatioPair h1).mono hsub)
  obtain ⟨q₁, hq₁mem, hq₁max⟩ := hbox.exists_isMaxOn hboxne
    ((continuousOn_gammaRatioPair h1).mono hsub)
  have hm : 0 < gammaRatioPair q₀ := gammaRatioPair_pos h1 hq₀mem.1
  have hMx : 0 < gammaRatioPair q₁ := gammaRatioPair_pos h1 hq₁mem.1
  refine ⟨min c₀ (gammaRatioPair q₀), max C₀ (gammaRatioPair q₁), lt_min hc₀ hm,
    lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  -- reduce to a nonnegative height
  have hkey : ∀ τ : ℝ, τ ∈ Icc (0 : ℝ) σ₁ → ∀ y : ℝ, 0 ≤ y →
      min c₀ (gammaRatioPair q₀) * (1 + |y|) ^ (-(2 * σ₁)) ≤ gammaRatioPair (τ, y) ∧
        gammaRatioPair (τ, y) ≤ max C₀ (gammaRatioPair q₁) := by
    intro τ hτ y hy
    have hy1 : (0 : ℝ) < 1 + |y| := by positivity
    have hg : 0 < (1 + |y|) ^ (-(2 * σ₁)) := Real.rpow_pos_of_pos hy1 _
    rcases le_or_gt y 1 with hle | hgt
    · have hmem : (τ, y) ∈ Icc (0 : ℝ) σ₁ ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨hτ, ⟨by linarith, hle⟩⟩
      have hle1 : (1 + |y|) ^ (-(2 * σ₁)) ≤ 1 := by
        calc (1 + |y|) ^ (-(2 * σ₁)) ≤ (1 : ℝ) ^ (-(2 * σ₁)) :=
              Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith [abs_nonneg y])
                (by linarith)
          _ = 1 := Real.one_rpow _
      refine ⟨?_, le_trans (hq₁max hmem) (le_max_right _ _)⟩
      calc min c₀ (gammaRatioPair q₀) * (1 + |y|) ^ (-(2 * σ₁))
          ≤ gammaRatioPair q₀ * (1 + |y|) ^ (-(2 * σ₁)) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hg.le
        _ ≤ gammaRatioPair q₀ * 1 := mul_le_mul_of_nonneg_left hle1 hm.le
        _ = gammaRatioPair q₀ := mul_one _
        _ ≤ gammaRatioPair (τ, y) := hq₀min hmem
    · have hy0 : (1 : ℝ) ≤ y := hgt.le
      have habs : |y| = y := abs_of_nonneg hy
      have harg : (1 - τ) + 2 * τ = 1 + τ := by ring
      have hbounds := hfar (1 - τ) (2 * τ) y (by linarith [hτ.2]) (by linarith [hτ.1])
        (by linarith [hτ.1]) (by linarith [hτ.2]) hy0
      rw [harg] at hbounds
      have hratio : gammaRatioPair (τ, y)
          = ‖Complex.Gamma (((1 - τ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
            / ‖Complex.Gamma (((1 + τ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ := rfl
      have hylow : (1 + |y|) ^ (-(2 * σ₁)) ≤ y ^ (-(2 * τ)) := by
        rw [habs]
        calc (1 + y) ^ (-(2 * σ₁)) ≤ y ^ (-(2 * σ₁)) :=
              Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith [hτ.1, h0])
          _ ≤ y ^ (-(2 * τ)) :=
              Real.rpow_le_rpow_of_exponent_le hy0 (by linarith [hτ.2])
      have hyup : y ^ (-(2 * τ)) ≤ 1 := by
        calc y ^ (-(2 * τ)) ≤ y ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hy0 (by linarith [hτ.1])
          _ = 1 := Real.rpow_zero y
      constructor
      · rw [hratio]
        calc min c₀ (gammaRatioPair q₀) * (1 + |y|) ^ (-(2 * σ₁))
            ≤ c₀ * (1 + |y|) ^ (-(2 * σ₁)) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hg.le
          _ ≤ c₀ * y ^ (-(2 * τ)) := mul_le_mul_of_nonneg_left hylow hc₀.le
          _ ≤ _ := hbounds.1
      · rw [hratio]
        calc ‖Complex.Gamma (((1 - τ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
              / ‖Complex.Gamma (((1 + τ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
            ≤ C₀ * y ^ (-(2 * τ)) := hbounds.2
          _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left hyup hC₀.le
          _ = C₀ := mul_one _
          _ ≤ max C₀ (gammaRatioPair q₁) := le_max_left _ _
  intro τ hτ x
  rcases le_or_gt 0 x with hx | hx
  · exact hkey τ hτ x hx
  · have hneg : gammaRatioPair (τ, x) = gammaRatioPair (τ, -x) := (gammaRatioPair_neg τ x).symm
    have habs : |x| = |-x| := (abs_neg x).symm
    rw [hneg, habs]
    exact hkey τ hτ (-x) (by linarith)

end GaloisForLFunctions.RHTower
