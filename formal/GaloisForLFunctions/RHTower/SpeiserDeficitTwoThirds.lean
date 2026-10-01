import GaloisForLFunctions.RHTower.SpeiserExactCount
import GaloisForLFunctions.RHTower.LamzouriMontgomeryTaylorXiDensity
import GaloisForLFunctions.RHTower.Zeta23HorizontalSingletonDensity
import GaloisForLFunctions.RHTower.ZetaZeroOrderReflection
import GaloisForLFunctions.RHTower.XiDerivRightCountLe
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount

/-!
# Speiser's deficit is at most a sixth of the zeros

Speiser's theorem says RH is equivalent to `ζ' ≠ 0` on `0 < Re s < 1/2`. Between unshadowed heights
`101 ≤ T₁ < T₂`, the zeros of `ζ'` in `0 < Re s < 1/2`, `T₁ < Im s < T₂` number exactly as many as
the zeros of `ζ` there, with multiplicity (`exists_speiser_count_eq`).

**Theorem** (`eventually_speiser_deficit_le`). For every `ε > 0` and all large `T₂`, for every
unshadowed `101 ≤ T₁ < T₂` with `T₂` unshadowed, the number of zeros of `ζ'` with multiplicity in
`0 < Re s < 1/2`, `T₁ < Im s < T₂` is at most `((1 − HD 1)/2 + ε)·N(T₂)`. Here `HD 1 = 0.6725…` is
the Montgomery–Taylor constant and `N(T₂)` the number of zeros of `ξ` with ordinate in `(0, T₂]`.

**Proof.**
- The left zeros of `ξ` up to height `T` carry exactly half of the off-line multiplicity: the map
  `z ↦ 1 − z̄` swaps the two sides and preserves orders (`two_mul_xiLeftZeroCount_eq`).
- The off-line multiplicity is at most `N(T) − N₀ˢ(T)`.
- The Montgomery–Taylor bound gives `N₀ˢ(T) ≥ (HD 1 − 2ε)N(T)`.

The same bound holds for the right zeros of `ξ'` (`eventually_xiDeriv_right_le`, via
`sum_order_deriv_xi_right_le`) and for the right zeros of Levinson's detector `ζ + λζ'` in its exact
range (`eventually_levinsonG_right_le`, via `exists_levinsonG_count_right`).
-/

open Complex Set Filter

namespace RHTower

noncomputable section

/-- The left zeros of `ξ` with ordinate in `(0, T]`, with multiplicity. -/
def xiLeftZeroCount (T : ℝ) : ℕ :=
  ∑ z ∈ (stripFinsetPos T).filter (fun z => z.re < 1 / 2), (analyticOrderAt xi z).toNat

/-- The right zeros of `ξ` with ordinate in `(0, T]`, with multiplicity. -/
def xiRightZeroCount (T : ℝ) : ℕ :=
  ∑ z ∈ (stripFinsetPos T).filter (fun z => 1 / 2 < z.re), (analyticOrderAt xi z).toNat

/-- The reflection `z ↦ 1 − z̄` across the critical line. -/
private def lineFlip (z : ℂ) : ℂ := 1 - (starRingEnd ℂ) z

private theorem lineFlip_re (z : ℂ) : (lineFlip z).re = 1 - z.re := by
  simp [lineFlip]

private theorem lineFlip_im (z : ℂ) : (lineFlip z).im = z.im := by
  simp [lineFlip]

private theorem lineFlip_lineFlip (z : ℂ) : lineFlip (lineFlip z) = z := by
  simp [lineFlip]

private theorem orderAt_lineFlip (z : ℂ) :
    analyticOrderAt xi (lineFlip z) = analyticOrderAt xi z := by
  rw [lineFlip, xi_orderAt_one_sub, xi_orderAt_conj]

private theorem xi_lineFlip_eq_zero {z : ℂ} (hz : xi z = 0) : xi (lineFlip z) = 0 := by
  rw [lineFlip, xi_one_sub, xi_conj, hz, map_zero]

private theorem mem_stripFinsetPos_lineFlip {T : ℝ} {z : ℂ} (hz : z ∈ stripFinsetPos T) :
    lineFlip z ∈ stripFinsetPos T := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := mem_stripFinsetPos.mp hz
  refine mem_stripFinsetPos.mpr ⟨?_, ?_, ?_, ?_, xi_lineFlip_eq_zero h4⟩
  · rw [lineFlip_re]; linarith
  · rw [lineFlip_re]; linarith
  · rw [lineFlip_im]; exact h2
  · rw [lineFlip_im]; exact h3

/-- The two off-line sides carry the same multiplicity. -/
theorem xiLeftZeroCount_eq_xiRightZeroCount (T : ℝ) :
    xiLeftZeroCount T = xiRightZeroCount T := by
  classical
  unfold xiLeftZeroCount xiRightZeroCount
  refine Finset.sum_nbij' lineFlip lineFlip ?_ ?_ (fun z _ => lineFlip_lineFlip z)
    (fun z _ => lineFlip_lineFlip z) (fun z _ => by rw [orderAt_lineFlip])
  · intro z hz
    obtain ⟨hzS, hre⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_stripFinsetPos_lineFlip hzS, ?_⟩)
    rw [lineFlip_re]; linarith
  · intro z hz
    obtain ⟨hzS, hre⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_stripFinsetPos_lineFlip hzS, ?_⟩)
    rw [lineFlip_re]; linarith

/-- The left side carries exactly half of the off-line multiplicity. -/
theorem two_mul_xiLeftZeroCount_eq (T : ℝ) : 2 * xiLeftZeroCount T = xiOffLineZeroCount T := by
  classical
  have hsplit : xiOffLineZeroCount T = xiLeftZeroCount T + xiRightZeroCount T := by
    unfold xiOffLineZeroCount xiLeftZeroCount xiRightZeroCount
    rw [← Finset.sum_union]
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext z
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hz, hne⟩
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
      · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
        · exact ⟨hz, ne_of_lt h⟩
        · exact ⟨hz, ne_of_gt h⟩
    · rw [Finset.disjoint_filter]
      intro z _ h1 h2
      linarith
  rw [hsplit, xiLeftZeroCount_eq_xiRightZeroCount]
  ring

/-- **The left multiplicity is at most `(1 − HD 1)/2` of the zeros.** -/
theorem eventually_xiLeftZeroCount_le :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (xiLeftZeroCount T : ℝ) ≤ ((1 - Zeta23.ThmD.HD 1) / 2 + ε) * (xiPosZeroCount T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon (2 * ε) (by positivity)
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 := hT₀ T hT
  have h2 : (2 * xiLeftZeroCount T : ℝ) = (xiOffLineZeroCount T : ℝ) := by
    exact_mod_cast two_mul_xiLeftZeroCount_eq T
  have h3 : (xiPosCriticalZeroCount T : ℝ) + xiOffLineZeroCount T = xiPosZeroCount T := by
    exact_mod_cast xiPosCriticalZeroCount_add_xiOffLineZeroCount T
  have h4 : (xiSimpleCriticalZeroCount T : ℝ) ≤ xiPosCriticalZeroCount T := by
    exact_mod_cast xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount T
  nlinarith

/-- The `ζ`-zeros of a Speiser window carry at most the left multiplicity of `ξ` up to `T₂`. -/
theorem sum_order_speiserWindow_le_xiLeftZeroCount {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) {Z₀ : Finset ℂ}
    (hZ₀ : ∀ w : ℂ, w ∈ Z₀ ↔ speiserWindow T₁ T₂ w ∧ riemannZeta w = 0) :
    ∑ w ∈ Z₀, (analyticOrderAt riemannZeta w).toNat ≤ xiLeftZeroCount T₂ := by
  classical
  unfold xiLeftZeroCount
  have hsub : Z₀ ⊆ (stripFinsetPos T₂).filter (fun z => z.re < 1 / 2) := by
    intro w hw
    obtain ⟨⟨h0, h1, h2, h3⟩, hζ⟩ := (hZ₀ w).mp hw
    have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; linarith
    have hxi : xi w = 0 := (xi_eq_zero_iff h0 hw1).mpr hζ
    exact Finset.mem_filter.mpr
      ⟨mem_stripFinsetPos.mpr ⟨h0, by linarith, by linarith, h3.le, hxi⟩, h1⟩
  calc ∑ w ∈ Z₀, (analyticOrderAt riemannZeta w).toNat
      = ∑ w ∈ Z₀, (analyticOrderAt xi w).toNat := by
        refine Finset.sum_congr rfl fun w hw => ?_
        obtain ⟨⟨h0, h1, -, -⟩, -⟩ := (hZ₀ w).mp hw
        rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, by linarith⟩]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- **Speiser's deficit is at most `(1 − HD 1)/2 ≈ 16.4%` of the zeros.** -/
theorem eventually_speiser_deficit_le :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ {T₁ T₂ : ℝ}, T₀ ≤ T₂ → 101 ≤ T₁ → T₁ < T₂ →
      SpeiserUnshadowed T₁ → SpeiserUnshadowed T₂ →
      ∃ Z₁ : Finset ℂ, (∀ w : ℂ, w ∈ Z₁ ↔ speiserWindow T₁ T₂ w ∧ deriv riemannZeta w = 0) ∧
        ((∑ w ∈ Z₁, (analyticOrderAt (deriv riemannZeta) w).toNat : ℕ) : ℝ) ≤
          ((1 - Zeta23.ThmD.HD 1) / 2 + ε) * (xiPosZeroCount T₂ : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_xiLeftZeroCount_le ε hε
  refine ⟨T₀, fun {T₁ T₂} hT₂ h101 hT hu₁ hu₂ => ?_⟩
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, heq⟩ := exists_speiser_count_eq h101 hT hu₁ hu₂
  refine ⟨Z₁, hZ₁, ?_⟩
  have hle := sum_order_speiserWindow_le_xiLeftZeroCount (by linarith) hZ₀
  rw [heq]
  calc ((∑ w ∈ Z₀, (analyticOrderAt riemannZeta w).toNat : ℕ) : ℝ)
      ≤ (xiLeftZeroCount T₂ : ℝ) := by exact_mod_cast hle
    _ ≤ _ := hT₀ T₂ hT₂


/-- Zeros of `ξ` in a right half-window carry at most the right multiplicity up to `T₂`. -/
theorem sum_order_rightHalfWindow_le_xiRightZeroCount {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) {Z₀ : Finset ℂ}
    (hZ₀ : ∀ w : ℂ, w ∈ Z₀ ↔ rightHalfWindow T₁ T₂ w ∧ xi w = 0) :
    ∑ w ∈ Z₀, (analyticOrderAt xi w).toNat ≤ xiRightZeroCount T₂ := by
  classical
  unfold xiRightZeroCount
  apply Finset.sum_le_sum_of_subset
  intro w hw
  obtain ⟨⟨h1, -, h3, h4⟩, hxi⟩ := (hZ₀ w).mp hw
  have hlt1 : w.re < 1 := by
    by_contra h; push Not at h; exact xi_ne_zero_of_one_le_re h hxi
  exact Finset.mem_filter.mpr
    ⟨mem_stripFinsetPos.mpr ⟨by linarith, hlt1, by linarith, h4.le, hxi⟩, h1⟩

/-- The right multiplicity is at most `(1 − HD 1)/2` of the zeros. -/
theorem eventually_xiRightZeroCount_le :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (xiRightZeroCount T : ℝ) ≤ ((1 - Zeta23.ThmD.HD 1) / 2 + ε) * (xiPosZeroCount T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_xiLeftZeroCount_le ε hε
  exact ⟨T₀, fun T hT => by rw [← xiLeftZeroCount_eq_xiRightZeroCount]; exact hT₀ T hT⟩

/-- **The right zeros of `ξ'` are at most `(1 − HD 1)/2` of the zeros.** -/
theorem eventually_xiDeriv_right_le :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ {T₁ T₂ : ℝ}, T₀ ≤ T₂ → 0 ≤ T₁ → T₁ < T₂ →
      SpeiserUnshadowed T₁ → SpeiserUnshadowed T₂ →
      ∃ Z₁ : Finset ℂ, (∀ w : ℂ, w ∈ Z₁ ↔ rightHalfWindow T₁ T₂ w ∧ deriv xi w = 0) ∧
        ((∑ w ∈ Z₁, (analyticOrderAt (deriv xi) w).toNat : ℕ) : ℝ) ≤
          ((1 - Zeta23.ThmD.HD 1) / 2 + ε) * (xiPosZeroCount T₂ : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_xiRightZeroCount_le ε hε
  refine ⟨T₀, fun {T₁ T₂} hT₂ h0 hT hu₁ hu₂ => ?_⟩
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, hle⟩ := sum_order_deriv_xi_right_le hT hu₁ hu₂
  refine ⟨Z₁, hZ₁, ?_⟩
  have h2 := sum_order_rightHalfWindow_le_xiRightZeroCount h0 hZ₀
  calc ((∑ w ∈ Z₁, (analyticOrderAt (deriv xi) w).toNat : ℕ) : ℝ)
      ≤ (xiRightZeroCount T₂ : ℝ) := by exact_mod_cast hle.trans h2
    _ ≤ _ := hT₀ T₂ hT₂

/-- **The right zeros of Levinson's detector are at most `(1 − HD 1)/2` of the zeros.** -/
theorem eventually_levinsonG_right_le :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ {lam T₁ T₂ : ℝ}, T₀ ≤ T₂ → 0 < lam →
      lam * (Real.log (T₂ / (2 * Real.pi)) / 2 + 1 / 20) < 1 → 100 ≤ T₁ → T₁ < T₂ →
      SpeiserUnshadowed T₁ → SpeiserUnshadowed T₂ →
      ∃ Z₁ : Finset ℂ, (∀ w : ℂ, w ∈ Z₁ ↔ rightHalfWindow T₁ T₂ w ∧ levinsonG (lam : ℂ) w = 0) ∧
        ((∑ w ∈ Z₁, (analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℕ) : ℝ) ≤
          ((1 - Zeta23.ThmD.HD 1) / 2 + ε) * (xiPosZeroCount T₂ : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_xiRightZeroCount_le ε hε
  refine ⟨T₀, fun {lam T₁ T₂} hT₂ hlam hlamT h100 hT hu₁ hu₂ => ?_⟩
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, heq⟩ := exists_levinsonG_count_right hlam hlamT h100 hT hu₁ hu₂
  refine ⟨Z₁, hZ₁, ?_⟩
  have h2 := sum_order_rightHalfWindow_le_xiRightZeroCount (by linarith) hZ₀
  rw [heq]
  calc ((∑ w ∈ Z₀, (analyticOrderAt xi w).toNat : ℕ) : ℝ)
      ≤ (xiRightZeroCount T₂ : ℝ) := by exact_mod_cast h2
    _ ≤ _ := hT₀ T₂ hT₂

end

end RHTower
