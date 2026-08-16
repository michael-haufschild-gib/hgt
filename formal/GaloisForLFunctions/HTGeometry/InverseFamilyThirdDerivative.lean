import GaloisForLFunctions.HTGeometry.ResolventSymbolTailDecay

/-!
# The amplitude surviving three integrations by parts

The expansion of a phase integral against an invertible generator is driven by the recursion
`D₀ = C⁻¹`, `D_{j+1} = C⁻¹ ∂ D_j`.  Two integrations by parts leave the amplitude `∂D₁`, which decays
like `w²`; a third leaves `∂D₂`, which decays like `w³`.

That extra power is not a refinement.  After transport the remaining integral is weighted by the
inverse propagator's growth `t^p`, so the two-fold remainder integrates `t^{p-2}` — divergent once
`p > 1` — while the three-fold remainder integrates `t^{p-3}`, absolutely convergent for every
`p < 2`.  For `p = 1/2 + σ` with `σ < 1` that is exactly the range in question.

Everything here is the product rule in a noncommutative ring, carried three levels deep, together
with the corresponding norm bounds for a symbol whose `j`-th derivative is `O(w^j)`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- The triple product bound. -/
theorem norm_mul₃_le (a b c : R) : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le a b) (norm_nonneg _))

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- The quintuple product bound. -/
theorem norm_mul₅_le (a b c d e : R) : ‖a * b * c * d * e‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul₃_le a b c) (norm_nonneg _)))
    (norm_nonneg _))

/-- The third derivative of the inverse family. -/
def invFamilyDeriv3 (C C₁ C₂ C₃ : ℝ → R) (s : ℝ) : R :=
  (invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s
      + invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s
      + invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s
      + invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s
      + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s)
    + (invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s
      + invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s
      + invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s
      + invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s
      + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s)
    - (invFamilyDeriv C C₁ s * C₂ s * invFamily C s
      + invFamily C s * C₃ s * invFamily C s
      + invFamily C s * C₂ s * invFamilyDeriv C C₁ s)

/-- The second derivative of the inverse family is differentiable. -/
theorem hasDerivAt_invFamilyDeriv2 {C C₁ C₂ C₃ : ℝ → R} {t : ℝ}
    (hC : HasDerivAt C (C₁ t) t) (hu : IsUnit (C t))
    (hC₁ : HasDerivAt C₁ (C₂ t) t) (hC₂ : HasDerivAt C₂ (C₃ t) t) :
    HasDerivAt (invFamilyDeriv2 C C₁ C₂) (invFamilyDeriv3 C C₁ C₂ C₃ t) t := by
  have hD : HasDerivAt (invFamily C) (invFamilyDeriv C C₁ t) t := hasDerivAt_invFamily hC hu
  have h1 : HasDerivAt
      (fun s => invFamily C s * C₁ s * invFamily C s * C₁ s * invFamily C s) _ t :=
    (((hD.mul hC₁).mul hD).mul hC₁).mul hD
  have h2 : HasDerivAt (fun s => invFamily C s * C₂ s * invFamily C s) _ t :=
    (hD.mul hC₂).mul hD
  have h := (h1.add h1).sub h2
  refine h.congr_deriv ?_
  rw [invFamilyDeriv3]
  simp only [Pi.mul_apply]
  noncomm_ring

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- The triple sum bound. -/
theorem norm_add₃_le (a b c : R) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_add_le a b) le_rfl)

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- The quintuple sum bound. -/
theorem norm_add₅_le (a b c d e : R) : ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ :=
  (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (norm_add₃_le a b c) le_rfl)) le_rfl)

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- **The third derivative of the inverse family is `O(w³)`.** -/
theorem norm_invFamilyDeriv3_le {C C₁ C₂ C₃ : ℝ → R} {Λ c₁ c₂ c₃ w : ℝ} {t : ℝ}
    (hw : 0 < w) (hΛ : ‖invFamily C t‖ ≤ Λ)
    (h₁ : ‖C₁ t‖ ≤ c₁ * w) (h₂ : ‖C₂ t‖ ≤ c₂ * w ^ 2) (h₃ : ‖C₃ t‖ ≤ c₃ * w ^ 3) :
    ‖invFamilyDeriv3 C C₁ C₂ C₃ t‖
      ≤ (6 * Λ ^ 4 * c₁ ^ 3 + 6 * Λ ^ 3 * c₁ * c₂ + Λ ^ 2 * c₃) * w ^ 3 := by
  have hΛ0 : 0 ≤ Λ := le_trans (norm_nonneg _) hΛ
  have hc₁ : 0 ≤ c₁ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (C₁ t)]
  have hc₂ : 0 ≤ c₂ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (C₂ t), pow_pos hw 2]
  have hc₃ : 0 ≤ c₃ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (C₃ t), pow_pos hw 3]
  have hD' : ‖invFamilyDeriv C C₁ t‖ ≤ Λ ^ 2 * (c₁ * w) := by
    refine (norm_invFamilyDeriv_le C C₁ t).trans ?_
    have hsq : ‖invFamily C t‖ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
    exact mul_le_mul hsq h₁ (norm_nonneg _) (by positivity)
  have tA : ‖invFamilyDeriv C C₁ t * C₁ t * invFamily C t * C₁ t * invFamily C t‖
      ≤ Λ ^ 2 * (c₁ * w) * (c₁ * w) * Λ * (c₁ * w) * Λ := by
    refine (norm_mul₅_le _ _ _ _ _).trans ?_
    gcongr
  have tB : ‖invFamily C t * C₂ t * invFamily C t * C₁ t * invFamily C t‖
      ≤ Λ * (c₂ * w ^ 2) * Λ * (c₁ * w) * Λ := by
    refine (norm_mul₅_le _ _ _ _ _).trans ?_
    gcongr
  have tC : ‖invFamily C t * C₁ t * invFamilyDeriv C C₁ t * C₁ t * invFamily C t‖
      ≤ Λ * (c₁ * w) * (Λ ^ 2 * (c₁ * w)) * (c₁ * w) * Λ := by
    refine (norm_mul₅_le _ _ _ _ _).trans ?_
    gcongr
  have tE : ‖invFamily C t * C₁ t * invFamily C t * C₂ t * invFamily C t‖
      ≤ Λ * (c₁ * w) * Λ * (c₂ * w ^ 2) * Λ := by
    refine (norm_mul₅_le _ _ _ _ _).trans ?_
    gcongr
  have tF : ‖invFamily C t * C₁ t * invFamily C t * C₁ t * invFamilyDeriv C C₁ t‖
      ≤ Λ * (c₁ * w) * Λ * (c₁ * w) * (Λ ^ 2 * (c₁ * w)) := by
    refine (norm_mul₅_le _ _ _ _ _).trans ?_
    gcongr
  have tG : ‖invFamilyDeriv C C₁ t * C₂ t * invFamily C t‖
      ≤ Λ ^ 2 * (c₁ * w) * (c₂ * w ^ 2) * Λ := by
    refine (norm_mul₃_le _ _ _).trans ?_
    gcongr
  have tH : ‖invFamily C t * C₃ t * invFamily C t‖ ≤ Λ * (c₃ * w ^ 3) * Λ := by
    refine (norm_mul₃_le _ _ _).trans ?_
    gcongr
  have tI : ‖invFamily C t * C₂ t * invFamilyDeriv C C₁ t‖
      ≤ Λ * (c₂ * w ^ 2) * (Λ ^ 2 * (c₁ * w)) := by
    refine (norm_mul₃_le _ _ _).trans ?_
    gcongr
  rw [invFamilyDeriv3]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_add₅_le _ _ _ _ _) (norm_add₅_le _ _ _ _ _)))
    (norm_add₃_le _ _ _)) ?_
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add tA tB) tC) tE) tF
  have hsum2 := add_le_add (add_le_add tG tH) tI
  nlinarith [hsum, hsum2]

/-- The second derivative of the boundary amplitude. -/
def invFamilyProductDeriv2 (C C₁ C₂ C₃ : ℝ → R) (s : ℝ) : R :=
  invFamilyDeriv2 C C₁ C₂ s * invFamilyDeriv C C₁ s
    + invFamilyDeriv C C₁ s * invFamilyDeriv2 C C₁ C₂ s
    + invFamilyDeriv C C₁ s * invFamilyDeriv2 C C₁ C₂ s
    + invFamily C s * invFamilyDeriv3 C C₁ C₂ C₃ s

/-- The boundary amplitude's derivative is differentiable. -/
theorem hasDerivAt_invFamilyProductDeriv {C C₁ C₂ C₃ : ℝ → R} {t : ℝ}
    (hC : HasDerivAt C (C₁ t) t) (hu : IsUnit (C t))
    (hC₁ : HasDerivAt C₁ (C₂ t) t) (hC₂ : HasDerivAt C₂ (C₃ t) t) :
    HasDerivAt (invFamilyProductDeriv C C₁ C₂) (invFamilyProductDeriv2 C C₁ C₂ C₃ t) t := by
  have hD : HasDerivAt (invFamily C) (invFamilyDeriv C C₁ t) t := hasDerivAt_invFamily hC hu
  have hD' : HasDerivAt (invFamilyDeriv C C₁) (invFamilyDeriv2 C C₁ C₂ t) t :=
    hasDerivAt_invFamilyDeriv hC hu hC₁
  have hD'' : HasDerivAt (invFamilyDeriv2 C C₁ C₂) (invFamilyDeriv3 C C₁ C₂ C₃ t) t :=
    hasDerivAt_invFamilyDeriv2 hC hu hC₁ hC₂
  have h := (hD'.mul hD').add (hD.mul hD'')
  refine h.congr_deriv ?_
  rw [invFamilyProductDeriv2]
  abel

/-- The third amplitude of the expansion, `D₂ = C⁻¹ ∂ D₁`. -/
def invFamilyProduct2 (C C₁ C₂ : ℝ → R) (s : ℝ) : R :=
  invFamily C s * invFamilyProductDeriv C C₁ C₂ s

/-- Its derivative, the amplitude surviving three integrations by parts. -/
def invFamilyProduct2Deriv (C C₁ C₂ C₃ : ℝ → R) (s : ℝ) : R :=
  invFamilyDeriv C C₁ s * invFamilyProductDeriv C C₁ C₂ s
    + invFamily C s * invFamilyProductDeriv2 C C₁ C₂ C₃ s

/-- The third amplitude is differentiable. -/
theorem hasDerivAt_invFamilyProduct2 {C C₁ C₂ C₃ : ℝ → R} {t : ℝ}
    (hC : HasDerivAt C (C₁ t) t) (hu : IsUnit (C t))
    (hC₁ : HasDerivAt C₁ (C₂ t) t) (hC₂ : HasDerivAt C₂ (C₃ t) t) :
    HasDerivAt (invFamilyProduct2 C C₁ C₂) (invFamilyProduct2Deriv C C₁ C₂ C₃ t) t := by
  have hD : HasDerivAt (invFamily C) (invFamilyDeriv C C₁ t) t := hasDerivAt_invFamily hC hu
  have hP : HasDerivAt (invFamilyProduct C C₁) (invFamilyProductDeriv C C₁ C₂ t) t :=
    hasDerivAt_invFamilyProduct hC hu hC₁
  have hP' : HasDerivAt (invFamilyProductDeriv C C₁ C₂) (invFamilyProductDeriv2 C C₁ C₂ C₃ t) t :=
    hasDerivAt_invFamilyProductDeriv hC hu hC₁ hC₂
  have h := hD.mul hP'
  refine h.congr_deriv ?_
  rw [invFamilyProduct2Deriv]

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- **The amplitude surviving three integrations by parts is `O(w³)`.** -/
theorem norm_invFamilyProduct2Deriv_le {C C₁ C₂ C₃ : ℝ → R} {Λ c₁ c₂ c₃ w : ℝ} {t : ℝ}
    (hw : 0 < w) (hΛ : ‖invFamily C t‖ ≤ Λ)
    (h₁ : ‖C₁ t‖ ≤ c₁ * w) (h₂ : ‖C₂ t‖ ≤ c₂ * w ^ 2) (h₃ : ‖C₃ t‖ ≤ c₃ * w ^ 3) :
    ‖invFamilyProduct2Deriv C C₁ C₂ C₃ t‖
      ≤ ((Λ ^ 2 * c₁) * (3 * Λ ^ 4 * c₁ ^ 2 + Λ ^ 3 * c₂)
          + Λ * (3 * (2 * Λ ^ 3 * c₁ ^ 2 + Λ ^ 2 * c₂) * (Λ ^ 2 * c₁)
            + Λ * (6 * Λ ^ 4 * c₁ ^ 3 + 6 * Λ ^ 3 * c₁ * c₂ + Λ ^ 2 * c₃))) * w ^ 3 := by
  have hΛ0 : 0 ≤ Λ := le_trans (norm_nonneg _) hΛ
  have hc₁ : 0 ≤ c₁ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (C₁ t)]
  have hc₂ : 0 ≤ c₂ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (C₂ t), pow_pos hw 2]
  have hc₃ : 0 ≤ c₃ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (C₃ t), pow_pos hw 3]
  have hD1 : ‖invFamilyDeriv C C₁ t‖ ≤ (Λ ^ 2 * c₁) * w := by
    refine (norm_invFamilyDeriv_le C C₁ t).trans ?_
    have hsq : ‖invFamily C t‖ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
    have := mul_le_mul hsq h₁ (norm_nonneg _) (by positivity)
    calc ‖invFamily C t‖ ^ 2 * ‖C₁ t‖ ≤ Λ ^ 2 * (c₁ * w) := this
      _ = (Λ ^ 2 * c₁) * w := by ring
  have hD2 : ‖invFamilyDeriv2 C C₁ C₂ t‖ ≤ (2 * Λ ^ 3 * c₁ ^ 2 + Λ ^ 2 * c₂) * w ^ 2 := by
    refine (norm_invFamilyDeriv2_le C C₁ C₂ t).trans ?_
    have h3 : ‖invFamily C t‖ ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hΛ 3
    have h2 : ‖invFamily C t‖ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
    have hsq1 : ‖C₁ t‖ ^ 2 ≤ (c₁ * w) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    nlinarith [norm_nonneg (C₁ t), norm_nonneg (C₂ t), norm_nonneg (invFamily C t),
      pow_nonneg (norm_nonneg (invFamily C t)) 3, pow_nonneg (norm_nonneg (invFamily C t)) 2,
      pow_nonneg (norm_nonneg (C₁ t)) 2, sq_nonneg w, hw.le]
  have hD3 : ‖invFamilyDeriv3 C C₁ C₂ C₃ t‖
      ≤ (6 * Λ ^ 4 * c₁ ^ 3 + 6 * Λ ^ 3 * c₁ * c₂ + Λ ^ 2 * c₃) * w ^ 3 :=
    norm_invFamilyDeriv3_le hw hΛ h₁ h₂ h₃
  have hP1 : ‖invFamilyProductDeriv C C₁ C₂ t‖ ≤ (3 * Λ ^ 4 * c₁ ^ 2 + Λ ^ 3 * c₂) * w ^ 2 :=
    norm_invFamilyProductDeriv_le_of_symbolDecay_weight hw hΛ h₁ h₂
  have hP2 : ‖invFamilyProductDeriv2 C C₁ C₂ C₃ t‖
      ≤ (3 * (2 * Λ ^ 3 * c₁ ^ 2 + Λ ^ 2 * c₂) * (Λ ^ 2 * c₁)
        + Λ * (6 * Λ ^ 4 * c₁ ^ 3 + 6 * Λ ^ 3 * c₁ * c₂ + Λ ^ 2 * c₃)) * w ^ 3 := by
    rw [invFamilyProductDeriv2]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add₃_le _ _ _) le_rfl) ?_
    have q1 : ‖invFamilyDeriv2 C C₁ C₂ t * invFamilyDeriv C C₁ t‖
        ≤ ((2 * Λ ^ 3 * c₁ ^ 2 + Λ ^ 2 * c₂) * w ^ 2) * ((Λ ^ 2 * c₁) * w) :=
      (norm_mul_le _ _).trans (mul_le_mul hD2 hD1 (norm_nonneg _) (by positivity))
    have q2 : ‖invFamilyDeriv C C₁ t * invFamilyDeriv2 C C₁ C₂ t‖
        ≤ ((Λ ^ 2 * c₁) * w) * ((2 * Λ ^ 3 * c₁ ^ 2 + Λ ^ 2 * c₂) * w ^ 2) :=
      (norm_mul_le _ _).trans (mul_le_mul hD1 hD2 (norm_nonneg _) (by positivity))
    have q3 : ‖invFamily C t * invFamilyDeriv3 C C₁ C₂ C₃ t‖
        ≤ Λ * ((6 * Λ ^ 4 * c₁ ^ 3 + 6 * Λ ^ 3 * c₁ * c₂ + Λ ^ 2 * c₃) * w ^ 3) :=
      (norm_mul_le _ _).trans (mul_le_mul hΛ hD3 (norm_nonneg _) hΛ0)
    nlinarith [q1, q2, q3]
  rw [invFamilyProduct2Deriv]
  refine le_trans (norm_add_le _ _) ?_
  have r1 : ‖invFamilyDeriv C C₁ t * invFamilyProductDeriv C C₁ C₂ t‖
      ≤ ((Λ ^ 2 * c₁) * w) * ((3 * Λ ^ 4 * c₁ ^ 2 + Λ ^ 3 * c₂) * w ^ 2) :=
    (norm_mul_le _ _).trans (mul_le_mul hD1 hP1 (norm_nonneg _) (by positivity))
  have r2 : ‖invFamily C t * invFamilyProductDeriv2 C C₁ C₂ C₃ t‖
      ≤ Λ * ((3 * (2 * Λ ^ 3 * c₁ ^ 2 + Λ ^ 2 * c₂) * (Λ ^ 2 * c₁)
        + Λ * (6 * Λ ^ 4 * c₁ ^ 3 + 6 * Λ ^ 3 * c₁ * c₂ + Λ ^ 2 * c₃)) * w ^ 3) :=
    (norm_mul_le _ _).trans (mul_le_mul hΛ hP2 (norm_nonneg _) hΛ0)
  nlinarith [r1, r2]

/-! ## Continuity of the amplitudes -/

open Set

variable {C C₁ C₂ C₃ : ℝ → R} {S : Set ℝ}

theorem continuousOn_invFamily_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) : ContinuousOn (invFamily C) S :=
  fun t ht => ((hasDerivAt_invFamily (hC t ht) (hu t ht)).continuousAt).continuousWithinAt

theorem continuousOn_invFamilyDeriv_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) (hC₁ : ContinuousOn C₁ S) :
    ContinuousOn (invFamilyDeriv C C₁) S := by
  have hDc := continuousOn_invFamily_of_unit hC hu
  have h : ContinuousOn (fun s => -(invFamily C s * C₁ s * invFamily C s)) S :=
    ((hDc.mul hC₁).mul hDc).neg
  exact h

theorem continuousOn_invFamilyDeriv2_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) :
    ContinuousOn (invFamilyDeriv2 C C₁ C₂) S := by
  have hDc := continuousOn_invFamily_of_unit hC hu
  have h : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamily C s * C₁ s * invFamily C s
        + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamily C s
        - invFamily C s * C₂ s * invFamily C s) S :=
    ((((hDc.mul hC₁).mul hDc).mul hC₁).mul hDc).add
      ((((hDc.mul hC₁).mul hDc).mul hC₁).mul hDc) |>.sub ((hDc.mul hC₂).mul hDc)
  exact h

theorem continuousOn_invFamilyDeriv3_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S)
    (hC₃ : ContinuousOn C₃ S) :
    ContinuousOn (invFamilyDeriv3 C C₁ C₂ C₃) S := by
  have hDc := continuousOn_invFamily_of_unit hC hu
  have hDderivc := continuousOn_invFamilyDeriv_of_unit hC hu hC₁
  have t1 : ContinuousOn (fun s =>
      invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s) S :=
    (((hDderivc.mul hC₁).mul hDc).mul hC₁).mul hDc
  have t2 : ContinuousOn (fun s =>
      invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s) S :=
    (((hDc.mul hC₂).mul hDc).mul hC₁).mul hDc
  have t3 : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s) S :=
    (((hDc.mul hC₁).mul hDderivc).mul hC₁).mul hDc
  have t4 : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s) S :=
    (((hDc.mul hC₁).mul hDc).mul hC₂).mul hDc
  have t5 : ContinuousOn (fun s =>
      invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s) S :=
    (((hDc.mul hC₁).mul hDc).mul hC₁).mul hDderivc
  have t6 : ContinuousOn (fun s => invFamilyDeriv C C₁ s * C₂ s * invFamily C s) S :=
    (hDderivc.mul hC₂).mul hDc
  have t7 : ContinuousOn (fun s => invFamily C s * C₃ s * invFamily C s) S :=
    (hDc.mul hC₃).mul hDc
  have t8 : ContinuousOn (fun s => invFamily C s * C₂ s * invFamilyDeriv C C₁ s) S :=
    (hDc.mul hC₂).mul hDderivc
  have h : ContinuousOn (fun s =>
      (invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s
        + invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s
        + invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s
        + invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s
        + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s)
      + (invFamilyDeriv C C₁ s * C₁ s * invFamily C s * C₁ s * invFamily C s
        + invFamily C s * C₂ s * invFamily C s * C₁ s * invFamily C s
        + invFamily C s * C₁ s * invFamilyDeriv C C₁ s * C₁ s * invFamily C s
        + invFamily C s * C₁ s * invFamily C s * C₂ s * invFamily C s
        + invFamily C s * C₁ s * invFamily C s * C₁ s * invFamilyDeriv C C₁ s)
      - (invFamilyDeriv C C₁ s * C₂ s * invFamily C s
        + invFamily C s * C₃ s * invFamily C s
        + invFamily C s * C₂ s * invFamilyDeriv C C₁ s)) S :=
    ((((((t1.add t2).add t3).add t4).add t5).add
      ((((t1.add t2).add t3).add t4).add t5)).sub ((t6.add t7).add t8))
  exact h

theorem continuousOn_invFamilyProductDeriv_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) :
    ContinuousOn (invFamilyProductDeriv C C₁ C₂) S := by
  have hDc := continuousOn_invFamily_of_unit hC hu
  have hDderivc := continuousOn_invFamilyDeriv_of_unit hC hu hC₁
  have hD2c := continuousOn_invFamilyDeriv2_of_unit hC hu hC₁ hC₂
  have h : ContinuousOn (fun s =>
      invFamilyDeriv C C₁ s * invFamilyDeriv C C₁ s + invFamily C s * invFamilyDeriv2 C C₁ C₂ s)
      S := (hDderivc.mul hDderivc).add (hDc.mul hD2c)
  exact h

theorem continuousOn_invFamilyProductDeriv2_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S)
    (hC₃ : ContinuousOn C₃ S) :
    ContinuousOn (invFamilyProductDeriv2 C C₁ C₂ C₃) S := by
  have hDc := continuousOn_invFamily_of_unit hC hu
  have hDderivc := continuousOn_invFamilyDeriv_of_unit hC hu hC₁
  have hD2c := continuousOn_invFamilyDeriv2_of_unit hC hu hC₁ hC₂
  have hD3c := continuousOn_invFamilyDeriv3_of_unit hC hu hC₁ hC₂ hC₃
  have h : ContinuousOn (fun s =>
      invFamilyDeriv2 C C₁ C₂ s * invFamilyDeriv C C₁ s
        + invFamilyDeriv C C₁ s * invFamilyDeriv2 C C₁ C₂ s
        + invFamilyDeriv C C₁ s * invFamilyDeriv2 C C₁ C₂ s
        + invFamily C s * invFamilyDeriv3 C C₁ C₂ C₃ s) S :=
    (((hD2c.mul hDderivc).add (hDderivc.mul hD2c)).add (hDderivc.mul hD2c)).add (hDc.mul hD3c)
  exact h

theorem continuousOn_invFamilyProduct2_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S) :
    ContinuousOn (invFamilyProduct2 C C₁ C₂) S := by
  have hDc := continuousOn_invFamily_of_unit hC hu
  have hPc := continuousOn_invFamilyProductDeriv_of_unit hC hu hC₁ hC₂
  have h : ContinuousOn (fun s => invFamily C s * invFamilyProductDeriv C C₁ C₂ s) S :=
    hDc.mul hPc
  exact h

/-- **The amplitude surviving three integrations by parts is continuous where the generator is a
unit.** -/
theorem continuousOn_invFamilyProduct2Deriv_of_unit (hC : ∀ t ∈ S, HasDerivAt C (C₁ t) t)
    (hu : ∀ t ∈ S, IsUnit (C t)) (hC₁ : ContinuousOn C₁ S) (hC₂ : ContinuousOn C₂ S)
    (hC₃ : ContinuousOn C₃ S) :
    ContinuousOn (invFamilyProduct2Deriv C C₁ C₂ C₃) S := by
  have hDc := continuousOn_invFamily_of_unit hC hu
  have hDderivc := continuousOn_invFamilyDeriv_of_unit hC hu hC₁
  have hPc := continuousOn_invFamilyProductDeriv_of_unit hC hu hC₁ hC₂
  have hP2c := continuousOn_invFamilyProductDeriv2_of_unit hC hu hC₁ hC₂ hC₃
  have h : ContinuousOn (fun s =>
      invFamilyDeriv C C₁ s * invFamilyProductDeriv C C₁ C₂ s
        + invFamily C s * invFamilyProductDeriv2 C C₁ C₂ C₃ s) S :=
    (hDderivc.mul hPc).add (hDc.mul hP2c)
  exact h

end GaloisForLFunctions.HTGeometry
