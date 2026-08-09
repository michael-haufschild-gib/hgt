import GaloisForLFunctions.HTGeometry.ActiveChargeRankHypertranscendence

/-!
# Dressing phases of finite and infinite translation rank

Three exact instances of the translation-rank classification.

* `finrank_translationSpan_phiJT` — the gravitational (flat Jackiw–Teitelboim) dressing phase
  `κ·sinh` has translation rank exactly two when `κ ≠ 0`, so it is differentially algebraic and a
  finite bilinear charge dressing is possible for it.
* `finrank_translationSpan_phiSpin_le` — a finite higher-spin dressing `∑_{s∈F} α_s·sinh(s·x)`
  has translation rank at most `2·|F|`.
* `not_finiteDimensional_translationSpan_phiCDD` — the single elementary CDD shell phase
  `4·arctan(sinh x / B)` with `B > 1` has *infinite* translation rank although it is
  differentially algebraic: its derivative is rational in `sinh`, and a rational function with a
  genuine pole cannot be entire.  Infinite active charge rank therefore does not detect
  hypertranscendence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-! ## Exponential characters -/

/-- The exponential character `x ↦ e^{μ x}` on the real line. -/
def realExpChar (μ : ℂ) : ℝ → ℂ := fun x => Complex.exp (μ * (x : ℂ))

theorem polyExp_one (μ : ℂ) : polyExp 1 μ = realExpChar μ := by
  funext x
  simp [polyExp, polyExpC, realExpChar]

theorem expChar_mem_expPolySpace (μ : ℂ) : realExpChar μ ∈ expPolySpace := by
  rw [← polyExp_one]
  exact polyExp_mem_expPolySpace _ _

private theorem csinh_eq (z : ℂ) : Complex.sinh z = (Complex.exp z - Complex.exp (-z)) / 2 :=
  Complex.ext rfl rfl

private theorem ccosh_eq (z : ℂ) : Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 :=
  Complex.ext rfl rfl

private theorem analyticOnNhd_csinh :
    AnalyticOnNhd ℂ Complex.sinh (Set.univ : Set ℂ) := by
  have h : Complex.sinh = fun z : ℂ => (Complex.exp z - Complex.exp (-z)) * (2 : ℂ)⁻¹ := by
    funext z; rw [csinh_eq]; ring
  rw [h]
  exact ((analyticOnNhd_id.cexp).sub ((analyticOnNhd_id.neg).cexp)).mul analyticOnNhd_const

private theorem analyticOnNhd_ccosh :
    AnalyticOnNhd ℂ Complex.cosh (Set.univ : Set ℂ) := by
  have h : Complex.cosh = fun z : ℂ => (Complex.exp z + Complex.exp (-z)) * (2 : ℂ)⁻¹ := by
    funext z; rw [ccosh_eq]; ring
  rw [h]
  exact ((analyticOnNhd_id.cexp).add ((analyticOnNhd_id.neg).cexp)).mul analyticOnNhd_const

/-! ## The flat-JT dressing phase -/

/-- The gravitational dressing phase `κ·sinh` of the flat Jackiw–Teitelboim tangent ray. -/
def phiJT (κ : ℂ) : ℝ → ℂ := fun x => κ * Complex.sinh (x : ℂ)

theorem realTranslate_phiJT (κ : ℂ) (a : ℝ) :
    realTranslate a (phiJT κ)
      = (κ * Complex.exp (-(a : ℂ)) / 2) • realExpChar 1 -
        (κ * Complex.exp ((a : ℂ)) / 2) • realExpChar (-1) := by
  funext x
  have hx : ((x - a : ℝ) : ℂ) = (x : ℂ) - (a : ℂ) := by push_cast; ring
  have e1 : Complex.exp ((x : ℂ) - (a : ℂ))
      = Complex.exp (1 * (x : ℂ)) * Complex.exp (-(a : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-((x : ℂ) - (a : ℂ)))
      = Complex.exp ((-1 : ℂ) * (x : ℂ)) * Complex.exp ((a : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp only [realTranslate, phiJT, realExpChar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx,
    csinh_eq, e1, e2]
  ring

theorem translationSpan_phiJT_le (κ : ℂ) :
    translationSpan (phiJT κ) ≤ Submodule.span ℂ (Set.range ![realExpChar 1, realExpChar (-1)]) := by
  rw [translationSpan, Submodule.span_le]
  rintro u ⟨a, rfl⟩
  show realTranslate a (phiJT κ) ∈ Submodule.span ℂ (Set.range ![realExpChar 1, realExpChar (-1)])
  rw [realTranslate_phiJT]
  refine Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨0, by simp⟩
  · exact Submodule.subset_span ⟨1, by simp⟩

instance finiteDimensional_span_jtChars :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range ![realExpChar 1, realExpChar (-1)])) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range _)

instance finiteDimensional_translationSpan_phiJT (κ : ℂ) :
    FiniteDimensional ℂ (translationSpan (phiJT κ)) :=
  Submodule.finiteDimensional_of_le (translationSpan_phiJT_le κ)

/-- **The flat-JT phase has translation rank exactly two.** -/
theorem finrank_translationSpan_phiJT {κ : ℂ} (hκ : κ ≠ 0) :
    Module.finrank ℂ (translationSpan (phiJT κ)) = 2 := by
  classical
  refine le_antisymm ?_ ?_
  · have hmono := Submodule.finrank_mono (translationSpan_phiJT_le κ)
    refine le_trans hmono ?_
    have hcard := finrank_span_le_card (R := ℂ) (Set.range ![realExpChar 1, realExpChar (-1)])
    refine le_trans hcard ?_
    rw [Set.toFinset_range]
    exact le_trans Finset.card_image_le (by simp)
  · set v₀ : ℝ → ℂ := phiJT κ with hv₀def
    set v₁ : ℝ → ℂ := realTranslate 1 (phiJT κ) with hv₁def
    have hs1 : Complex.sinh ((1 : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sinh, ne_eq, Complex.ofReal_eq_zero]
      exact Real.sinh_eq_zero.not.mpr (by norm_num)
    have hsm1 : Complex.sinh (((0 : ℝ) - 1 : ℝ) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sinh, ne_eq, Complex.ofReal_eq_zero]
      exact Real.sinh_eq_zero.not.mpr (by norm_num)
    have hLI : LinearIndependent ℂ ![v₀, v₁] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrFun hst 1
      have h0 := congrFun hst 0
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hv₀def, hv₁def,
        phiJT, realTranslate] at h0 h1
      have hzero1 : Complex.sinh (((1 : ℝ) - 1 : ℝ) : ℂ) = 0 := by norm_num
      have hzero0 : Complex.sinh ((0 : ℝ) : ℂ) = 0 := by norm_num
      rw [hzero1] at h1
      rw [hzero0] at h0
      have hs : s = 0 := by
        have h1' : s * (κ * Complex.sinh ((1 : ℝ) : ℂ)) = 0 := by simpa using h1
        rcases mul_eq_zero.mp h1' with h | h
        · exact h
        · exact absurd h (mul_ne_zero hκ hs1)
      have ht : t = 0 := by
        have h0' : t * (κ * Complex.sinh (((0 : ℝ) - 1 : ℝ) : ℂ)) = 0 := by simpa using h0
        rcases mul_eq_zero.mp h0' with h | h
        · exact h
        · exact absurd h (mul_ne_zero hκ hsm1)
      exact ⟨hs, ht⟩
    have hmem0 : v₀ ∈ translationSpan (phiJT κ) := self_mem_translationSpan _
    have hmem1 : v₁ ∈ translationSpan (phiJT κ) := realTranslate_mem_translationSpan _ 1
    have hLIsub : LinearIndependent ℂ
        (![⟨v₀, hmem0⟩, ⟨v₁, hmem1⟩] : Fin 2 → translationSpan (phiJT κ)) := by
      apply LinearIndependent.of_comp (translationSpan (phiJT κ)).subtype
      have hcomp : (⇑(translationSpan (phiJT κ)).subtype ∘
          (![⟨v₀, hmem0⟩, ⟨v₁, hmem1⟩] : Fin 2 → translationSpan (phiJT κ))) = ![v₀, v₁] := by
        funext i
        fin_cases i <;> rfl
      rw [hcomp]
      exact hLI
    have hcard := hLIsub.fintype_card_le_finrank
    simpa using hcard

/-! ## Finite higher-spin dressings -/

/-- A finite generalized `T T̄` dressing phase `∑_{s ∈ F} α_s·sinh(s·x)`. -/
def phiSpin (F : Finset ℂ) (α : ℂ → ℂ) : ℝ → ℂ :=
  fun x => ∑ s ∈ F, α s * Complex.sinh (s * (x : ℂ))

/-- The `2·|F|` exponential characters carrying a finite higher-spin dressing. -/
def spinChar (p : ℂ × Bool) : ℝ → ℂ := realExpChar (cond p.2 p.1 (-p.1))

theorem realTranslate_phiSpin (F : Finset ℂ) (α : ℂ → ℂ) (a : ℝ) :
    realTranslate a (phiSpin F α)
      = ∑ s ∈ F, ((α s * Complex.exp (-(s * (a : ℂ))) / 2) • spinChar (s, true)
          - (α s * Complex.exp (s * (a : ℂ)) / 2) • spinChar (s, false)) := by
  funext x
  have hx : ((x - a : ℝ) : ℂ) = (x : ℂ) - (a : ℂ) := by push_cast; ring
  simp only [realTranslate, phiSpin, hx, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hst : spinChar (s, true) x = Complex.exp (s * (x : ℂ)) := rfl
  have hsf : spinChar (s, false) x = Complex.exp ((-s) * (x : ℂ)) := rfl
  have e1 : Complex.exp (s * ((x : ℂ) - (a : ℂ)))
      = Complex.exp (s * (x : ℂ)) * Complex.exp (-(s * (a : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-(s * ((x : ℂ) - (a : ℂ))))
      = Complex.exp ((-s) * (x : ℂ)) * Complex.exp (s * (a : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hst, hsf, csinh_eq, e1, e2]
  ring

theorem translationSpan_phiSpin_le (F : Finset ℂ) (α : ℂ → ℂ) :
    translationSpan (phiSpin F α)
      ≤ Submodule.span ℂ (spinChar '' ((F ×ˢ (Finset.univ : Finset Bool) :
          Finset (ℂ × Bool)) : Set (ℂ × Bool))) := by
  rw [translationSpan, Submodule.span_le]
  rintro u ⟨a, rfl⟩
  show realTranslate a (phiSpin F α) ∈ _
  rw [realTranslate_phiSpin]
  refine Submodule.sum_mem _ fun s hs => Submodule.sub_mem _ ?_ ?_
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(s, true), ?_, rfl⟩)
    simp [hs]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(s, false), ?_, rfl⟩)
    simp [hs]

/-- **A finite higher-spin dressing has translation rank at most `2·|F|`.** -/
theorem finrank_translationSpan_phiSpin_le (F : Finset ℂ) (α : ℂ → ℂ) :
    Module.finrank ℂ (translationSpan (phiSpin F α)) ≤ 2 * F.card := by
  classical
  set T : Finset (ℂ × Bool) := F ×ˢ (Finset.univ : Finset Bool) with hT
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (spinChar '' (T : Set (ℂ × Bool)))) :=
    Module.Finite.span_of_finite ℂ (Set.Finite.image _ (Finset.finite_toSet _))
  have hmono := Submodule.finrank_mono (translationSpan_phiSpin_le F α)
  refine le_trans hmono ?_
  have hcard := finrank_span_le_card (R := ℂ) (spinChar '' (T : Set (ℂ × Bool)))
  refine le_trans hcard ?_
  have himg : (spinChar '' (T : Set (ℂ × Bool))).toFinset ⊆ T.image spinChar := by
    intro u hu
    simp only [Set.mem_toFinset, Set.mem_image, Finset.mem_coe] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    exact Finset.mem_image_of_mem _ hp
  refine le_trans (Finset.card_le_card himg) ?_
  refine le_trans Finset.card_image_le ?_
  rw [hT, Finset.card_product]
  simp [Nat.mul_comm]

/-! ## The elementary CDD shell: infinite rank without hypertranscendence -/

/-- The single elementary CDD shell phase `4·arctan(sinh x / B)`. -/
def phiCDD (B : ℝ) : ℝ → ℂ := fun x => ((4 * Real.arctan (Real.sinh x / B) : ℝ) : ℂ)

theorem hasDerivAt_phiCDD {B : ℝ} (hB : 0 < B) (x : ℝ) :
    HasDerivAt (phiCDD B)
      (((4 * B * Real.cosh x / (B ^ 2 + Real.sinh x ^ 2) : ℝ) : ℂ)) x := by
  have hBne : B ≠ 0 := ne_of_gt hB
  have hden : B ^ 2 + Real.sinh x ^ 2 ≠ 0 := by positivity
  have hinner : HasDerivAt (fun y : ℝ => Real.sinh y / B) (Real.cosh x / B) x := by
    simpa [div_eq_mul_inv] using (Real.hasDerivAt_sinh x).mul_const B⁻¹
  have hcomp0 := (Real.hasDerivAt_arctan (Real.sinh x / B)).comp x hinner
  have hcomp : HasDerivAt (fun y : ℝ => Real.arctan (Real.sinh y / B))
      ((1 / (1 + (Real.sinh x / B) ^ 2)) * (Real.cosh x / B)) x := hcomp0
  have hscaled : HasDerivAt (fun y : ℝ => 4 * Real.arctan (Real.sinh y / B))
      (4 * ((1 / (1 + (Real.sinh x / B) ^ 2)) * (Real.cosh x / B))) x := hcomp.const_mul 4
  have hval : 4 * ((1 / (1 + (Real.sinh x / B) ^ 2)) * (Real.cosh x / B))
      = 4 * B * Real.cosh x / (B ^ 2 + Real.sinh x ^ 2) := by
    field_simp
  rw [hval] at hscaled
  exact hscaled.ofReal_comp

theorem continuous_phiCDD (B : ℝ) : Continuous (phiCDD B) :=
  Complex.continuous_ofReal.comp
    (continuous_const.mul (Real.continuous_arctan.comp (Real.continuous_sinh.div_const B)))

/-- A complex rapidity at which the CDD denominator vanishes. -/
def cddPole (B : ℝ) : ℂ := Complex.log (Complex.I * ((B + Real.sqrt (B ^ 2 - 1) : ℝ) : ℂ))

theorem sinh_cddPole {B : ℝ} (hB : 1 < B) :
    Complex.sinh (cddPole B) = Complex.I * (B : ℂ) := by
  set c : ℝ := B + Real.sqrt (B ^ 2 - 1) with hc
  have hB0 : (0 : ℝ) < B := lt_trans zero_lt_one hB
  have hsq : Real.sqrt (B ^ 2 - 1) ^ 2 = B ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hcpos : 0 < c := by
    have hnn : 0 ≤ Real.sqrt (B ^ 2 - 1) := Real.sqrt_nonneg _
    simp only [hc]
    linarith
  have hcne : (c : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hcpos)
  have hw0 : Complex.I * (c : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hcne
  have hexp : Complex.exp (cddPole B) = Complex.I * (c : ℂ) := Complex.exp_log hw0
  have hquad : (c : ℝ) ^ 2 - 2 * B * c + 1 = 0 := by
    simp only [hc]
    nlinarith [hsq]
  have hquadC : (c : ℂ) ^ 2 - 2 * (B : ℂ) * (c : ℂ) + 1 = 0 := by
    have hcast := congrArg (fun r : ℝ => (r : ℂ)) hquad
    push_cast at hcast
    simpa using hcast
  have hinv : (Complex.I * (c : ℂ))⁻¹ = -Complex.I * (c : ℂ)⁻¹ := by
    rw [mul_inv, Complex.inv_I]
  have hsum : (c : ℂ) + (c : ℂ)⁻¹ = 2 * (B : ℂ) := by
    field_simp
    linear_combination hquadC
  rw [csinh_eq, hexp, Complex.exp_neg, hexp, hinv,
    show Complex.I * (c : ℂ) - -Complex.I * (c : ℂ)⁻¹
      = Complex.I * ((c : ℂ) + (c : ℂ)⁻¹) by ring, hsum]
  ring

theorem cosh_cddPole_ne_zero {B : ℝ} (hB : 1 < B) : Complex.cosh (cddPole B) ≠ 0 := by
  intro hzero
  have hid := Complex.cosh_sq_sub_sinh_sq (cddPole B)
  rw [hzero, sinh_cddPole hB] at hid
  have hBsq : (B : ℂ) ^ 2 = 1 := by
    linear_combination hid + (B : ℂ) ^ 2 * Complex.I_sq
  have hreal : B ^ 2 = 1 := by
    have hcast : ((B ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact hBsq
    exact_mod_cast hcast
  nlinarith

/-- **The elementary CDD shell phase is not an exponential polynomial.** -/
theorem not_mem_expPolySpace_phiCDD {B : ℝ} (hB : 1 < B) : phiCDD B ∉ expPolySpace := by
  intro hmem
  have hB0 : (0 : ℝ) < B := lt_trans zero_lt_one hB
  have hderivmem : deriv (phiCDD B) ∈ expPolySpace := deriv_mem_expPolySpace hmem
  obtain ⟨E, hEmem, hEeq⟩ := exists_entire_extension hderivmem
  have hEan : AnalyticOnNhd ℂ E (Set.univ : Set ℂ) := analyticOnNhd_of_mem_expPolySpaceC hEmem
  set A : ℂ → ℂ := fun z => E z * ((B : ℂ) ^ 2 + Complex.sinh z ^ 2) with hA
  set C : ℂ → ℂ := fun z => 4 * (B : ℂ) * Complex.cosh z with hC
  have hAan : AnalyticOnNhd ℂ A (Set.univ : Set ℂ) :=
    hEan.mul (analyticOnNhd_const.add (analyticOnNhd_csinh.pow 2))
  have hCan : AnalyticOnNhd ℂ C (Set.univ : Set ℂ) :=
    analyticOnNhd_const.mul analyticOnNhd_ccosh
  have hreal : ∀ x : ℝ, A (x : ℂ) = C (x : ℂ) := by
    intro x
    have hd : deriv (phiCDD B) x
        = ((4 * B * Real.cosh x / (B ^ 2 + Real.sinh x ^ 2) : ℝ) : ℂ) :=
      (hasDerivAt_phiCDD hB0 x).deriv
    have hden : B ^ 2 + Real.sinh x ^ 2 ≠ 0 := by positivity
    have hdenC : ((B : ℂ) ^ 2 + Complex.sinh (x : ℂ) ^ 2)
        = ((B ^ 2 + Real.sinh x ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sinh]
      push_cast
      ring
    have hdenCne : ((B ^ 2 + Real.sinh x ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [ne_eq, Complex.ofReal_eq_zero]
      exact hden
    have hdenCne2 : ((B : ℂ) ^ 2 + Complex.sinh (x : ℂ) ^ 2) ≠ 0 := by
      rw [hdenC]; exact hdenCne
    simp only [hA, hC, hEeq x, hd, hdenC]
    rw [← Complex.ofReal_cosh]
    push_cast
    field_simp
  have hAC : A = C := eq_of_eqOn_real hAan hCan hreal
  have hz := congrFun hAC (cddPole B)
  have hdenzero : (B : ℂ) ^ 2 + Complex.sinh (cddPole B) ^ 2 = 0 := by
    rw [sinh_cddPole hB]
    linear_combination (B : ℂ) ^ 2 * Complex.I_sq
  simp only [hA, hC, hdenzero, mul_zero] at hz
  have hBne : (B : ℂ) ≠ 0 := by simpa using ne_of_gt hB0
  refine cosh_cddPole_ne_zero hB ?_
  rcases mul_eq_zero.mp hz.symm with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · norm_num at h'
    · exact absurd h' hBne
  · exact h

/-- **Infinite translation rank does not detect hypertranscendence.**  The elementary CDD shell
phase has infinite translation rank. -/
theorem not_finiteDimensional_translationSpan_phiCDD {B : ℝ} (hB : 1 < B) :
    ¬ FiniteDimensional ℂ (translationSpan (phiCDD B)) := by
  intro hfin
  exact not_mem_expPolySpace_phiCDD hB
    ((mem_expPolySpace_iff_finiteDimensional_translationSpan (continuous_phiCDD B)).2 hfin)

/-! ## The explicit higher-spin annihilator -/

theorem deriv_expChar (μ : ℂ) : deriv (realExpChar μ) = μ • realExpChar μ := by
  rw [← polyExp_one, deriv_polyExp]
  funext x
  simp [polyExp, polyExpC, expShiftPoly]

theorem contDiff_expChar (μ : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (realExpChar μ) :=
  contDiff_of_mem_expPolySpace (expChar_mem_expPolySpace μ)

theorem sinhChar_eq (s : ℂ) :
    (fun x : ℝ => Complex.sinh (s * (x : ℂ)))
      = (2 : ℂ)⁻¹ • realExpChar s - (2 : ℂ)⁻¹ • realExpChar (-s) := by
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, realExpChar, csinh_eq]
  rw [show (-(s * (x : ℂ))) = (-s) * (x : ℂ) by ring]
  ring

theorem sinhChar_mem_expPolySpace (s : ℂ) :
    (fun x : ℝ => Complex.sinh (s * (x : ℂ))) ∈ expPolySpace := by
  rw [sinhChar_eq]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (expChar_mem_expPolySpace s))
    (Submodule.smul_mem _ _ (expChar_mem_expPolySpace (-s)))

theorem phiSpin_mem_expPolySpace (F : Finset ℂ) (α : ℂ → ℂ) : phiSpin F α ∈ expPolySpace := by
  have hsum : phiSpin F α = ∑ s ∈ F, α s • (fun x : ℝ => Complex.sinh (s * (x : ℂ))) := by
    funext x
    simp [phiSpin]
  rw [hsum]
  exact Submodule.sum_mem _ fun s _ =>
    Submodule.smul_mem _ _ (sinhChar_mem_expPolySpace s)

private theorem aeval_X_sub_C_expChar (μ : ℂ) (hm : realExpChar μ ∈ smoothSubmodule) :
    (Polynomial.aeval smoothDerivLM (Polynomial.X - Polynomial.C μ))
      (⟨realExpChar μ, hm⟩ : smoothSubmodule) = 0 := by
  apply Subtype.ext
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  show deriv (realExpChar μ) - μ • realExpChar μ = (0 : ℝ → ℂ)
  rw [deriv_expChar]
  abel

private theorem aeval_XsqSubC_expChar_pos (s : ℂ) (hm : realExpChar s ∈ smoothSubmodule) :
    (Polynomial.aeval smoothDerivLM (Polynomial.X ^ 2 - Polynomial.C (s ^ 2)))
      (⟨realExpChar s, hm⟩ : smoothSubmodule) = 0 := by
  have hfac : (Polynomial.X ^ 2 - Polynomial.C (s ^ 2) : Polynomial ℂ)
      = (Polynomial.X + Polynomial.C s) * (Polynomial.X - Polynomial.C s) := by
    rw [Polynomial.C_pow]
    ring
  rw [hfac, map_mul, Module.End.mul_apply, aeval_X_sub_C_expChar s hm, map_zero]

private theorem aeval_XsqSubC_expChar_neg (s : ℂ) (hm : realExpChar (-s) ∈ smoothSubmodule) :
    (Polynomial.aeval smoothDerivLM (Polynomial.X ^ 2 - Polynomial.C (s ^ 2)))
      (⟨realExpChar (-s), hm⟩ : smoothSubmodule) = 0 := by
  have hfac : (Polynomial.X ^ 2 - Polynomial.C (s ^ 2) : Polynomial ℂ)
      = (Polynomial.X - Polynomial.C s) * (Polynomial.X - Polynomial.C (-s)) := by
    rw [Polynomial.C_pow, Polynomial.C_neg]
    ring
  rw [hfac, map_mul, Module.End.mul_apply, aeval_X_sub_C_expChar (-s) hm, map_zero]

/-- **The explicit higher-spin annihilator is nonzero.** -/
theorem prod_XsqSubC_ne_zero (F : Finset ℂ) :
    (∏ s ∈ F, (Polynomial.X ^ 2 - Polynomial.C (s ^ 2)) : Polynomial ℂ) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun s _ => ?_
  exact (Polynomial.monic_X_pow_sub_C (s ^ 2) (by norm_num)).ne_zero

/-- **A finite higher-spin dressing is annihilated by `∏_{s ∈ F} (X² − s²)`.** -/
theorem realConstCoeffOp_phiSpin_eq_zero (F : Finset ℂ) (α : ℂ → ℂ) :
    realConstCoeffOp (∏ s ∈ F, (Polynomial.X ^ 2 - Polynomial.C (s ^ 2))) (phiSpin F α) = 0 := by
  classical
  set L : Polynomial ℂ := ∏ s ∈ F, (Polynomial.X ^ 2 - Polynomial.C (s ^ 2)) with hL
  have hsm : ∀ μ : ℂ, realExpChar μ ∈ smoothSubmodule := fun μ => contDiff_expChar μ
  have hphism : phiSpin F α ∈ smoothSubmodule :=
    contDiff_of_mem_expPolySpace (phiSpin_mem_expPolySpace F α)
  have hblock : ∀ s ∈ F, (Polynomial.aeval smoothDerivLM L)
      ((2 : ℂ)⁻¹ • (⟨realExpChar s, hsm s⟩ : smoothSubmodule)
        - (2 : ℂ)⁻¹ • (⟨realExpChar (-s), hsm (-s)⟩ : smoothSubmodule)) = 0 := by
    intro s hs
    have hsplit : L = (∏ t ∈ F.erase s, (Polynomial.X ^ 2 - Polynomial.C (t ^ 2)))
        * (Polynomial.X ^ 2 - Polynomial.C (s ^ 2)) := (Finset.prod_erase_mul F _ hs).symm
    rw [map_sub, map_smul, map_smul, hsplit, map_mul]
    rw [Module.End.mul_apply, Module.End.mul_apply,
      aeval_XsqSubC_expChar_pos s (hsm s), aeval_XsqSubC_expChar_neg s (hsm (-s))]
    simp
  have hdecomp : (⟨phiSpin F α, hphism⟩ : smoothSubmodule)
      = ∑ s ∈ F, α s • ((2 : ℂ)⁻¹ • (⟨realExpChar s, hsm s⟩ : smoothSubmodule)
          - (2 : ℂ)⁻¹ • (⟨realExpChar (-s), hsm (-s)⟩ : smoothSubmodule)) := by
    apply Subtype.ext
    push_cast
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, phiSpin, realExpChar]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [csinh_eq, show (-(s * (x : ℂ))) = (-s) * (x : ℂ) by ring]
    ring
  have hzero : (Polynomial.aeval smoothDerivLM L) (⟨phiSpin F α, hphism⟩ : smoothSubmodule) = 0 := by
    rw [hdecomp, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [map_smul, hblock s hs, smul_zero]
  have hcoe := congrArg (fun w : smoothSubmodule => (w : ℝ → ℂ)) hzero
  rw [coe_aeval_smoothDerivLM] at hcoe
  simpa using hcoe

end

end GaloisForLFunctions.HTGeometry
