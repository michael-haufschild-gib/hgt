import GaloisForLFunctions.RHTower.VerticalProgressionClassLimits

/-!
# The mollified second moment along a vertical progression

**Theorem** (`tendsto_secondMoment_div`). Let `ψ` be smooth, supported in `[1, 2]`, `α > 0`,
`β ∈ ℝ`, `0 < θ < ½`, `N = ⌊T^θ⌋` and `M_N` the linear mollifier. Then

`T^{−1} Σ_{ℓ ∈ ℤ} ψ(ℓ/T) |ζ M_N(½ + i(αℓ + β))|² → (∫ψ)(1 + 1/θ)`.

**Proof.** By the quadruple expansion, `S₂ = 2 Σ_c Φ_T(c) + O(T^{½+θ} log T)`, where `c` runs over
the reduced ratios `nk/(mh)`. Split the ratios with `δ = T^{−1+η}`, `η = (½ − θ)/4`:
* `c = 1`: `Φ_T(1) = Σ_ℓ ψ(ℓ/T) F(1,1,t_ℓ) ∼ (½ + 1/(2θ)) T ∫ψ`;
* off-resonant, near-diagonal, small, medium and huge resonant ratios: each `o(T)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

/-! ## The partition of the ratios -/

/-- The resonant ratios `|u(c) − j| < δ` for some `j ≠ 0`. -/
def resonantRatios (α δ : ℝ) : Set (ℕ × ℕ) :=
  {c | ∃ j : ℤ, j ≠ 0 ∧ |ratioPhase α c - j| < δ}

theorem ratioPhase_one_one (α : ℝ) : ratioPhase α (1, 1) = 0 := by
  unfold ratioPhase; simp

/-- **The six classes partition the ratios** (for `δ < ½` and `Y ≤ Z`). -/
theorem indicator_partition {E : Type*} [AddCommGroup E] (f : ℕ × ℕ → E) {α δ Y Z : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (hYZ : Y ≤ Z) (c : ℕ × ℕ) :
    f c = ({(1, 1)} : Set (ℕ × ℕ)).indicator f c + (offResonant α δ).indicator f c +
      (nearDiagonal α δ).indicator f c +
      (resonantRatios α δ ∩ {c | ((c.1 * c.2 : ℕ) : ℝ) < Y}).indicator f c +
      (resonantRatios α δ ∩ {c | Y ≤ ((c.1 * c.2 : ℕ) : ℝ) ∧ ((c.1 * c.2 : ℕ) : ℝ) ≤ Z}).indicator
        f c +
      (resonantRatios α δ ∩ hugeRatio Z).indicator f c := by
  set u := ratioPhase α c
  by_cases h11 : c = (1, 1)
  · subst h11
    have hu : ratioPhase α (1, 1) = 0 := ratioPhase_one_one α
    have hO : (1, 1) ∉ offResonant α δ := fun h => by
      have := h 0; rw [hu] at this; simp at this; linarith
    have hZd : (1, 1) ∉ nearDiagonal α δ := fun h => h.1 rfl
    have hR : (1, 1) ∉ resonantRatios α δ := by
      rintro ⟨j, hj0, hj⟩
      rw [hu, zero_sub, abs_neg] at hj
      have : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
      linarith
    rw [Set.indicator_of_mem (Set.mem_singleton _), Set.indicator_of_notMem hO,
      Set.indicator_of_notMem hZd, Set.indicator_of_notMem (fun h => hR h.1),
      Set.indicator_of_notMem (fun h => hR h.1), Set.indicator_of_notMem (fun h => hR h.1)]
    simp
  rw [Set.indicator_of_notMem (show c ∉ ({(1, 1)} : Set (ℕ × ℕ)) from h11), zero_add]
  by_cases hO : c ∈ offResonant α δ
  · have hZd : c ∉ nearDiagonal α δ := fun h => by
      have := hO 0; simp only [Int.cast_zero, sub_zero] at this; linarith [h.2]
    have hR : c ∉ resonantRatios α δ := by
      rintro ⟨j, -, hj⟩; linarith [hO j]
    rw [Set.indicator_of_mem hO, Set.indicator_of_notMem hZd,
      Set.indicator_of_notMem (fun h => hR h.1), Set.indicator_of_notMem (fun h => hR h.1),
      Set.indicator_of_notMem (fun h => hR h.1)]
    simp
  rw [Set.indicator_of_notMem hO, zero_add]
  have hex : ∃ j : ℤ, |ratioPhase α c - j| < δ := by
    by_contra h; push Not at h; exact hO h
  obtain ⟨j, hj⟩ := hex
  by_cases hj0 : j = 0
  · subst hj0
    simp only [Int.cast_zero, sub_zero] at hj
    have hZd : c ∈ nearDiagonal α δ := ⟨h11, hj⟩
    have hR : c ∉ resonantRatios α δ := by
      rintro ⟨j', hj'0, hj'⟩
      have h1 : (1 : ℝ) ≤ |(j' : ℝ)| := by exact_mod_cast Int.one_le_abs hj'0
      have := abs_sub_abs_le_abs_sub (j' : ℝ) (ratioPhase α c)
      rw [abs_sub_comm] at hj'
      linarith
    rw [Set.indicator_of_mem hZd, Set.indicator_of_notMem (fun h => hR h.1),
      Set.indicator_of_notMem (fun h => hR h.1), Set.indicator_of_notMem (fun h => hR h.1)]
    simp
  have hR : c ∈ resonantRatios α δ := ⟨j, hj0, hj⟩
  have hZd : c ∉ nearDiagonal α δ := by
    rintro ⟨-, h0⟩
    have h1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
    have := abs_sub_abs_le_abs_sub (j : ℝ) (ratioPhase α c)
    rw [abs_sub_comm] at hj
    linarith
  rw [Set.indicator_of_notMem hZd, zero_add]
  have hnot : ∀ {P : Prop} (S : Set (ℕ × ℕ)), (c ∈ S → P) → ¬ P → c ∉ S := fun S h hP hc =>
    hP (h hc)
  set Ra := resonantRatios α δ ∩ {c : ℕ × ℕ | ((c.1 * c.2 : ℕ) : ℝ) < Y}
  set Rb := resonantRatios α δ ∩
    {c : ℕ × ℕ | Y ≤ ((c.1 * c.2 : ℕ) : ℝ) ∧ ((c.1 * c.2 : ℕ) : ℝ) ≤ Z}
  set Rh := resonantRatios α δ ∩ hugeRatio Z
  have hRh : c ∈ Rh ↔ Z < ((c.1 * c.2 : ℕ) : ℝ) := by
    simp only [Rh, Set.mem_inter_iff, hugeRatio, Set.mem_setOf_eq, hR, true_and]
    push_cast; rfl
  by_cases hY : ((c.1 * c.2 : ℕ) : ℝ) < Y
  · have h1 : c ∈ Ra := ⟨hR, hY⟩
    have h2 : c ∉ Rb := fun h => absurd h.2.1 (not_le.mpr hY)
    have h3 : c ∉ Rh := fun h => absurd (hRh.mp h) (by linarith)
    rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem h3]
    simp
  · push Not at hY
    have h1 : c ∉ Ra := fun h => absurd h.2 (not_lt.mpr hY)
    rw [Set.indicator_of_notMem h1]
    by_cases hZ : ((c.1 * c.2 : ℕ) : ℝ) ≤ Z
    · have h2 : c ∈ Rb := ⟨hR, hY, hZ⟩
      have h3 : c ∉ Rh := fun h => absurd (hRh.mp h) (not_lt.mpr hZ)
      rw [Set.indicator_of_mem h2, Set.indicator_of_notMem h3]
      simp
    · push Not at hZ
      have h2 : c ∉ Rb := fun h => absurd h.2.2 (not_le.mpr hZ)
      have h3 : c ∈ Rh := hRh.mpr hZ
      rw [Set.indicator_of_notMem h2, Set.indicator_of_mem h3]
      simp

/-! ## The diagonal ratio -/

theorem hrange_of {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β T : ℝ} (hα : 0 < α)
    (hT : 1 ≤ T) (hβ : 2 * |β| ≤ α * T) (x : ℝ) (hx : ψ (x / T) ≠ 0) :
    α * x + β ∈ Icc (α / 2 * T) (3 * α * T) := by
  have hT0 : 0 < T := by linarith
  obtain ⟨h1, h2⟩ := hsupp hx
  rw [le_div_iff₀ hT0] at h1
  rw [div_le_iff₀ hT0] at h2
  constructor
  · have := neg_abs_le β; nlinarith
  · have := le_abs_self β; nlinarith

theorem latticeSum_const_mul (a : ℂ) (g : ℝ → ℂ) (u : ℝ) :
    latticeSum (fun x => a * g x) u = a * latticeSum g u := by
  unfold latticeSum
  rw [← tsum_mul_left]
  exact tsum_congr fun ℓ => by ring

/-- **The diagonal fibre** `Φ_T(1)/T → (½ + 1/(2θ)) ∫ψ`. -/
theorem tendsto_fiberTerm_one_one_div {ψ : ℝ → ℝ} (hψ : ∀ r : ℕ, ContDiff ℝ r ψ)
    (hsupp : Function.support ψ ⊆ Icc 1 2) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) :
    Tendsto (fun T => fiberTerm ψ α β (molLen θ T) T (1, 1) / T) atTop
      (𝓝 (((1 / 2 + 1 / (2 * θ) : ℝ) : ℂ) * ((∫ x, ψ x : ℝ) : ℂ))) := by
  have hψC : ∀ r : ℕ, ContDiff ℝ r (fun y : ℝ => (ψ y : ℂ)) := fun r =>
    Complex.ofRealCLM.contDiff.comp (hψ r)
  have hsuppC := complex_support_subset hsupp
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_bound_bump hψC hsuppC
  have hΨ0 : 0 ≤ Ψ₀ := (norm_nonneg _).trans (hΨ₀ 0)
  obtain ⟨Φ₁, hΦ₁⟩ := exists_bound_iteratedDeriv hψC hsuppC 1
  have hb := tendsto_bumpSum_div_int (hψC 1) hsuppC (Φ₁ := Φ₁) (by simpa using hΦ₁) 0
  rw [integral_complex_ofReal] at hb
  set c₀ : ℂ := ((1 / 2 + 1 / (2 * θ) : ℝ) : ℂ)
  -- the difference
  have hdiff : Tendsto (fun T => fiberTerm ψ α β (molLen θ T) T (1, 1) / T -
      c₀ * (bumpSum (fun y => (ψ y : ℂ)) T ((0 : ℤ) : ℝ) / T)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set ε' : ℝ := ε / (2 * Ψ₀ + 2)
    have hε' : 0 < ε' := by positivity
    filter_upwards [ratioForm_one_one_uniform hθ0 hθ (c₁ := α / 2) (c₂ := 3 * α) (by positivity)
      (by linarith) hε', eventually_progression (β := β) hα] with T hF hTβ
    obtain ⟨hT, hβ⟩ := hTβ
    have hT0 : 0 < T := by linarith
    have hpos := pos_of_progression hsupp hα hT0 hβ
    rw [dist_zero_right, fiberTerm_eq hsupp _ hT0 hpos (Nat.coprime_one_left 1) one_pos one_pos]
    unfold bumpSum
    simp only [Nat.cast_one, mul_one, Real.sqrt_one, inv_one, Complex.ofReal_one, one_mul,
      Real.log_one, sub_self, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      Int.cast_zero]
    have hg : Function.support (fun x : ℝ => c₀ * (ψ (x / T) : ℂ)) ⊆ Icc T (2 * T) := by
      intro x hx
      apply support_cutoff_subset hsuppC hT0 (fun _ => c₀)
      simpa [mul_comm] using hx
    rw [← mul_div_assoc, ← latticeSum_const_mul, ← sub_div,
      latticeSum_sub (support_cutoff_subset hsuppC hT0 _) hg,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    have hbd := norm_latticeSum_le_of_bound (A := T) (B := 2 * T)
      (h := fun x => (ψ (x / T) : ℂ) * ratioForm (molLen θ T) 1 1 (α * x + β) - c₀ * (ψ (x / T) : ℂ))
      (M := Ψ₀ * ε') (by linarith)
      (by
        intro x hx
        apply support_cutoff_subset hsuppC hT0 (fun x => ratioForm (molLen θ T) 1 1 (α * x + β) - c₀)
        simp only [Function.mem_support] at hx ⊢
        rw [mul_sub]
        rwa [mul_comm (ψ (x / T) : ℂ) c₀])
      (fun x => ?_) 0
    · rw [div_lt_iff₀ hT0]
      calc ‖latticeSum (fun x => (ψ (x / T) : ℂ) * ratioForm (molLen θ T) 1 1 (α * x + β) -
            c₀ * (ψ (x / T) : ℂ)) 0‖ ≤ (2 * T - T + 1) * (Ψ₀ * ε') := hbd
        _ ≤ (2 * T) * (Ψ₀ * ε') := by gcongr; linarith
        _ < ε * T := by
            simp only [ε']
            rw [show 2 * T * (Ψ₀ * (ε / (2 * Ψ₀ + 2))) = T * ε * (2 * Ψ₀ / (2 * Ψ₀ + 2)) by ring]
            have : 2 * Ψ₀ / (2 * Ψ₀ + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
            nlinarith [mul_pos hT0 hε]
    · by_cases hx : ψ (x / T) = 0
      · simp only [hx, Complex.ofReal_zero, zero_mul, mul_zero, sub_zero, norm_zero]; positivity
      rw [show (ψ (x / T) : ℂ) * ratioForm (molLen θ T) 1 1 (α * x + β) - c₀ * (ψ (x / T) : ℂ) =
        (ψ (x / T) : ℂ) * (ratioForm (molLen θ T) 1 1 (α * x + β) - c₀) by ring, norm_mul]
      have ht := hrange_of hsupp hα hT hβ x hx
      exact mul_le_mul (hΨ₀ _) (hF _ ht) (norm_nonneg _) hΨ0
  have := hdiff.add (hb.const_mul c₀)
  rw [zero_add] at this
  refine this.congr fun T => ?_
  simp only [Int.cast_zero]
  ring

/-! ## Assembly -/

theorem tendsto_div_of_norm_div {f : ℝ → ℂ}
    (h : Tendsto (fun T => ‖f T‖ / T) atTop (𝓝 0)) : Tendsto (fun T => f T / T) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]

theorem smallResonant_eq (α θ T : ℝ) : smallResonant α θ T =
    resonantRatios α (T ^ (-1 + resExp θ)) ∩
      {c : ℕ × ℕ | ((c.1 * c.2 : ℕ) : ℝ) < T ^ (1 - 2 * resExp θ)} := rfl

theorem mediumResonant_eq (α θ T : ℝ) : mediumResonant α θ T =
    resonantRatios α (T ^ (-1 + resExp θ)) ∩ {c : ℕ × ℕ | T ^ (1 - 2 * resExp θ) ≤
      ((c.1 * c.2 : ℕ) : ℝ) ∧ ((c.1 * c.2 : ℕ) : ℝ) ≤ hugeCut θ T} := rfl

/-- The expansion error is `o(T)`. -/
theorem tendsto_expansion_error_div {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2)
    {Ψ₀ : ℝ} (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun T => ((secondMoment ψ α β (molLen θ T) T : ℂ) -
      2 * ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 (molLen θ T), ∑ k ∈ Finset.Icc 1 (molLen θ T),
        quadTerm ψ α β (molLen θ T) T P h k) / T) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hexp⟩ := norm_secondMoment_sub_expansion_le
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  set c₁ : ℝ := 1 + |Real.log (3 * α)|
  set K : ℝ := 2 * Ψ₀ * C * c₁ * 4 / Real.sqrt (α / 2)
  have hK : 0 ≤ K := by positivity
  have hlim : Tendsto (fun T : ℝ => K * ((1 + Real.log T) ^ 1 * T ^ (-(1 / 2 - θ)))) atTop (𝓝 0) := by
    have := (one_add_log_pow_mul_rpow_neg_tendsto 1 (show 0 < 1 / 2 - θ by linarith)).const_mul K
    rwa [mul_zero] at this
  apply tendsto_div_of_norm_div
  refine squeeze_zero' (by filter_upwards [eventually_ge_atTop 0] with T hT; positivity) ?_ hlim
  filter_upwards [eventually_progression (β := β) hα, eventually_ge_atTop (32 / α)] with T hTβ hT32
  obtain ⟨hT, hβ⟩ := hTβ
  have hT0 : 0 < T := by linarith
  have hαT : 32 ≤ α * T := by rwa [div_le_iff₀ hα, mul_comm] at hT32
  have h := hexp hsupp hΨ (molLen θ T) hα hβ hαT
  have hN := molLen_cast_le_rpow (θ := θ) hT0.le
  have hlog : 1 + Real.log (3 * α * T) ≤ c₁ * (1 + Real.log T) := by
    have := one_add_max_log_le hα hT
    have : Real.log (3 * α * T) ≤ max 0 (Real.log (3 * α * T)) := le_max_right _ _
    linarith
  have hlog0 : 0 ≤ 1 + Real.log (3 * α * T) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 3 * α * T by linarith); linarith
  have hsq : Real.sqrt (α * T / 2) = Real.sqrt (α / 2) * Real.sqrt T := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  have hsT : Real.sqrt T * T ^ (-(1 / 2 - θ)) = T ^ θ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT0]; ring_nf
  have hsα : 0 < Real.sqrt (α / 2) := Real.sqrt_pos.mpr (by positivity)
  have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  rw [div_le_iff₀ hT0]
  refine h.trans ?_
  calc (T + 1) * (Ψ₀ * (C * (1 + Real.log (3 * α * T)) / Real.sqrt (α * T / 2) *
        (4 * (molLen θ T : ℝ))))
      ≤ (2 * T) * (Ψ₀ * (C * (c₁ * (1 + Real.log T)) / Real.sqrt (α * T / 2) * (4 * T ^ θ))) := by
        have hL0 : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
        have hb0 : 0 ≤ C * (c₁ * (1 + Real.log T)) / Real.sqrt (α * T / 2) :=
          div_nonneg (mul_nonneg hC0 (mul_nonneg (by positivity) hL0)) (Real.sqrt_nonneg _)
        gcongr
        linarith
    _ = K * ((1 + Real.log T) ^ 1 * T ^ (-(1 / 2 - θ))) * T := by
        rw [hsq, ← hsT]
        simp only [K]
        field_simp

/-- **The mollified second moment along a vertical progression.** -/
theorem tendsto_secondMoment_div {ψ : ℝ → ℝ} (hψ : ∀ r : ℕ, ContDiff ℝ r ψ)
    (hsupp : Function.support ψ ⊆ Icc 1 2) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) :
    Tendsto (fun T => secondMoment ψ α β (molLen θ T) T / T) atTop
      (𝓝 ((∫ x, ψ x) * (1 + 1 / θ))) := by
  have hψC : ∀ r : ℕ, ContDiff ℝ r (fun y : ℝ => (ψ y : ℂ)) := fun r =>
    Complex.ofRealCLM.contDiff.comp (hψ r)
  have hsuppC := complex_support_subset hsupp
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_bound_bump hψC hsuppC
  have hΨ : ∀ y, |ψ y| ≤ Ψ₀ := fun y => by
    have := hΨ₀ y; rwa [Complex.norm_real, Real.norm_eq_abs] at this
  set η := resExp θ with hηdef
  have hη : 0 < η := by rw [hηdef]; unfold resExp; linarith
  have hη1 : η < 1 := by rw [hηdef]; unfold resExp; linarith
  set Φ : ℝ → ℕ × ℕ → ℂ := fun T => fiberTerm ψ α β (molLen θ T) T
  set Tot : ℝ → ℂ := fun T => ∑' P : ℕ × ℕ, ∑ h ∈ Finset.Icc 1 (molLen θ T),
    ∑ k ∈ Finset.Icc 1 (molLen θ T), quadTerm ψ α β (molLen θ T) T P h k
  set XO : ℝ → ℂ := fun T => ∑' c, (offResonant α (T ^ (-1 + η))).indicator (Φ T) c
  set XZ : ℝ → ℂ := fun T => ∑' c, (nearDiagonal α (T ^ (-1 + η))).indicator (Φ T) c
  set Xa : ℝ → ℂ := fun T => ∑' c, (smallResonant α θ T).indicator (Φ T) c
  set Xb : ℝ → ℂ := fun T => ∑' c, (mediumResonant α θ T).indicator (Φ T) c
  set Xh : ℝ → ℂ := fun T => ∑' c,
    (resonantRatios α (T ^ (-1 + η)) ∩ hugeRatio (hugeCut θ T)).indicator (Φ T) c
  -- the decomposition
  have hδ : Tendsto (fun T : ℝ => T ^ (-1 + η)) atTop (𝓝 0) := tendsto_rpow_of_neg (by linarith)
  have hdec : ∀ᶠ T : ℝ in atTop, Tot T = Φ T (1, 1) + XO T + XZ T + Xa T + Xb T + Xh T := by
    filter_upwards [eventually_progression (β := β) hα, eventually_molLen_ge_one hθ0,
      hδ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with T hTβ hN1 hδT
    obtain ⟨hT, hβ⟩ := hTβ
    have hT0 : 0 < T := by linarith
    have hpos := pos_of_progression hsupp hα hT0 hβ
    have hS := hasSum_fiberTerm hsupp (molLen θ T) hT0 hpos
    have hYZ : T ^ (1 - 2 * η) ≤ hugeCut θ T := by
      have hN1R : (1 : ℝ) ≤ molLen θ T := by exact_mod_cast hN1
      unfold hugeCut
      calc T ^ (1 - 2 * η) ≤ T ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
        _ ≤ T ^ (1 + η) * ((molLen θ T : ℕ) : ℝ) ^ 2 :=
            le_mul_of_one_le_right (by positivity) (one_le_pow₀ hN1R)
    have hδ0 : 0 < T ^ (-1 + η) := Real.rpow_pos_of_pos hT0 _
    have hpart := fun c => indicator_partition (Φ T) (α := α) hδ0 hδT hYZ c
    have hsm := hS.summable
    have h1 : ∑' c, ({(1, 1)} : Set (ℕ × ℕ)).indicator (Φ T) c = Φ T (1, 1) := by
      rw [tsum_eq_single (1, 1)]
      · exact Set.indicator_of_mem (Set.mem_singleton _) _
      · intro c hc
        exact Set.indicator_of_notMem (show c ∉ ({(1, 1)} : Set (ℕ × ℕ)) from hc) (Φ T)
    simp only [Tot]
    rw [← hS.tsum_eq]
    simp only [Φ] at hpart h1 ⊢
    rw [tsum_congr hpart, Summable.tsum_add (((((hsm.indicator _).add (hsm.indicator _)).add
      (hsm.indicator _)).add (hsm.indicator _)).add (hsm.indicator _)) (hsm.indicator _),
      Summable.tsum_add ((((hsm.indicator _).add (hsm.indicator _)).add
      (hsm.indicator _)).add (hsm.indicator _)) (hsm.indicator _),
      Summable.tsum_add (((hsm.indicator _).add (hsm.indicator _)).add
      (hsm.indicator _)) (hsm.indicator _),
      Summable.tsum_add ((hsm.indicator _).add (hsm.indicator _)) (hsm.indicator _),
      Summable.tsum_add (hsm.indicator _) (hsm.indicator _), h1]
    rfl
  -- the limits of the pieces
  have h11 := tendsto_fiberTerm_one_one_div hψ hsupp (β := β) hα hθ0 hθ
  have hO := tendsto_div_of_norm_div (tendsto_offResonant_div hψ hsupp (β := β) hα hθ0 hθ)
  have hZ := tendsto_div_of_norm_div (tendsto_nearDiagonal_div hsupp hΨ (β := β) hα hθ0 hθ)
  have hb := tendsto_div_of_norm_div (tendsto_mediumResonant_div hsupp hΨ (β := β) hα hθ0 hθ)
  have hh := tendsto_div_of_norm_div (tendsto_huge_div hsupp hΨ (β := β) hα hθ0 hθ
    (fun T => resonantRatios α (T ^ (-1 + η))))
  have ha : Tendsto (fun T => Xa T / T) atTop (𝓝 0) := by
    apply tendsto_div_of_norm_div
    refine squeeze_zero' (by filter_upwards [eventually_ge_atTop 0] with T hT; positivity) ?_
      (tendsto_smallResonant_div hsupp hΨ (β := β) hα hθ0 hθ)
    filter_upwards [eventually_progression (β := β) hα] with T hTβ
    obtain ⟨hT, hβ⟩ := hTβ
    have hT0 : 0 < T := by linarith
    have hsm := (summable_norm_fiberTerm hsupp (molLen θ T) hT0
      (pos_of_progression hsupp hα hT0 hβ)).indicator (smallResonant α θ T)
    rw [div_le_iff₀ hT0]
    refine (norm_tsum_le_tsum_norm (by simpa [norm_indicator_eq_indicator_norm] using hsm)).trans
      (le_of_eq ?_)
    rw [← tsum_mul_right]
    refine tsum_congr fun c => ?_
    rw [norm_indicator_eq_indicator_norm]
    by_cases hc : c ∈ smallResonant α θ T
    · simp only [Set.indicator_of_mem hc, Φ]; field_simp
    · simp only [Set.indicator_of_notMem hc, zero_mul]
  have hE := tendsto_expansion_error_div hsupp hΨ (β := β) hα hθ0 hθ
  -- assembly in `ℂ`
  set c₀ : ℂ := ((1 / 2 + 1 / (2 * θ) : ℝ) : ℂ)
  have hsum := ((((((h11.add hO).add hZ).add ha).add hb).add hh).const_mul 2).add hE
  simp only [add_zero] at hsum
  have hC : Tendsto (fun T => ((secondMoment ψ α β (molLen θ T) T / T : ℝ) : ℂ)) atTop
      (𝓝 (((∫ x, ψ x) * (1 + 1 / θ) : ℝ) : ℂ)) := by
    have hval : 2 * (c₀ * ((∫ x, ψ x : ℝ) : ℂ)) = (((∫ x, ψ x) * (1 + 1 / θ) : ℝ) : ℂ) := by
      simp only [c₀]; push_cast; field_simp
    rw [← hval]
    refine hsum.congr' ?_
    filter_upwards [hdec, eventually_gt_atTop 0] with T hT hT0
    simp only [Tot, XO, XZ, Xa, Xb, Xh, Φ] at hT ⊢
    push_cast
    rw [hT]
    have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    field_simp
    ring
  have := (Complex.continuous_re.tendsto _).comp hC
  rw [Complex.ofReal_re] at this
  exact this.congr fun T => by simp only [Function.comp_apply, Complex.ofReal_re]

end

end RHTower.VerticalAP
