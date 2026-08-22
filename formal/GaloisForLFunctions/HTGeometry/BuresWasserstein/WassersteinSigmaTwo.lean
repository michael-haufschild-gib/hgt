import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldHilbertSchmidt
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNearIdentity

/-!
# Wasserstein points of a Hilbert–Schmidt family stay in `Σ₂`

Kim–Mer–Pálfia (arXiv:2607.29142) work in `Σ₂ = ℙ ∩ SL²_ex(ℋ)`, the strictly positive operators
that differ from a scalar by a Hilbert–Schmidt operator.  The regularity statement — that the
Wasserstein point of a family in `Σ₂` again lies in `Σ₂` — follows from the square-root form of
the Wasserstein equation with no analysis at all:

`X - X^{1/2} = ∑ᵢ wᵢ [(X^{1/2} Aᵢ X^{1/2})^{1/2} - X^{1/2}]`,

each summand is Hilbert–Schmidt because `X^{1/2} Aᵢ X^{1/2} - X = X^{1/2}(Aᵢ - 1)X^{1/2}` is and
the square root is Hilbert–Schmidt-stable (a Sylvester equation with coefficients `√b`, `√c`);
hence `X^{1/2} - 1 = X^{-1/2}(X - X^{1/2})` is Hilbert–Schmidt and so is
`X - 1 = (X^{1/2} - 1)(X^{1/2} + 1)`.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- The Sylvester equation for the difference of two square roots. -/
lemma cfcSqrt_sub_sylvester {b c : E →L[ℂ] E} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    CFC.sqrt b * (CFC.sqrt b - CFC.sqrt c) + (CFC.sqrt b - CFC.sqrt c) * CFC.sqrt c
      = b - c := by
  have h1 : CFC.sqrt b * CFC.sqrt b = b := CFC.sqrt_mul_sqrt_self b hb
  have h2 : CFC.sqrt c * CFC.sqrt c = c := CFC.sqrt_mul_sqrt_self c hc
  have hexp : CFC.sqrt b * (CFC.sqrt b - CFC.sqrt c) + (CFC.sqrt b - CFC.sqrt c) * CFC.sqrt c
      = CFC.sqrt b * CFC.sqrt b - CFC.sqrt c * CFC.sqrt c := by noncomm_ring
  rw [hexp, h1, h2]

/-- **The square root is Hilbert–Schmidt stable.** -/
theorem isHilbertSchmidt_cfcSqrt_sub {b c : E →L[ℂ] E} {α : ℝ} (hα : 0 < α)
    (hbα : α • (1 : E →L[ℂ] E) ≤ b) (hcα : α • (1 : E →L[ℂ] E) ≤ c)
    (h : IsHilbertSchmidt (b - c)) : IsHilbertSchmidt (CFC.sqrt b - CFC.sqrt c) := by
  have hbnn : (0 : E →L[ℂ] E) ≤ b := le_trans (smul_nonneg hα.le zero_le_one) hbα
  have hcnn : (0 : E →L[ℂ] E) ≤ c := le_trans (smul_nonneg hα.le zero_le_one) hcα
  have hsqα : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
  have hbl : (Real.sqrt α) • (1 : E →L[ℂ] E) ≤ CFC.sqrt b := by
    have hm := CFC.sqrt_le_sqrt _ _ hbα
    rwa [cfcSqrt_smul hα.le (zero_le_one (α := E →L[ℂ] E)), CFC.sqrt_one] at hm
  have hcl : (Real.sqrt α) • (1 : E →L[ℂ] E) ≤ CFC.sqrt c := by
    have hm := CFC.sqrt_le_sqrt _ _ hcα
    rwa [cfcSqrt_smul hα.le (zero_le_one (α := E →L[ℂ] E)), CFC.sqrt_one] at hm
  exact isHilbertSchmidt_of_sylvester (CFC.sqrt_nonneg b).isSelfAdjoint
    (CFC.sqrt_nonneg c).isSelfAdjoint (Real.sqrt_pos.mpr hα) (Real.sqrt_pos.mpr hα)
    hbl hcl h (cfcSqrt_sub_sylvester hbnn hcnn)

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E} {X : E →L[ℂ] E}

/-- **A Wasserstein point of a family in `1 + SL²` again lies in `1 + SL²`.** -/
theorem isHilbertSchmidt_sub_one_of_isWassersteinPoint {α : ℝ} (hα : 0 < α)
    (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hXα : α • (1 : E →L[ℂ] E) ≤ X)
    (hHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1))
    (hW : IsWassersteinPoint s w Av X) :
    IsHilbertSchmidt (X - 1) := by
  classical
  have hX : IsStrictlyPositive X := hW.1
  have hXhalf : IsStrictlyPositive (X ^ (1/2 : ℝ) : E →L[ℂ] E) := hX.rpow _ _
  have hsqeq := (isWassersteinPoint_iff_sqrt hX hA).mp hW
  -- each summand of `X - X^{1/2}` is Hilbert–Schmidt
  have hbc : ∀ i ∈ s, IsHilbertSchmidt
      ((X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ) - X) := by
    intro i hi
    have hid : (X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ) - X
        = (X ^ (1/2 : ℝ) : E →L[ℂ] E) * (Av i - 1) * X ^ (1/2 : ℝ) := by
      have hxx : (X ^ (1/2 : ℝ) : E →L[ℂ] E) * X ^ (1/2 : ℝ) = X :=
        rpow_half_mul_rpow_half hX
      have hexp : (X ^ (1/2 : ℝ) : E →L[ℂ] E) * (Av i - 1) * X ^ (1/2 : ℝ)
          = (X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ)
            - (X ^ (1/2 : ℝ) : E →L[ℂ] E) * X ^ (1/2 : ℝ) := by noncomm_ring
      rw [hexp, hxx]
    rw [hid]
    exact (((hHS i hi).comp_left _).comp_right _)
  have hXsq : CFC.sqrt X = (X ^ (1/2 : ℝ) : E →L[ℂ] E) := CFC.sqrt_eq_rpow
  have hsummand : ∀ i ∈ s, IsHilbertSchmidt
      (CFC.sqrt ((X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ))
        - (X ^ (1/2 : ℝ) : E →L[ℂ] E)) := by
    intro i hi
    have hlowb : (α * α) • (1 : E →L[ℂ] E)
        ≤ (X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ) := by
      have h1 : (X ^ (1/2 : ℝ) : E →L[ℂ] E) * (α • (1 : E →L[ℂ] E)) * X ^ (1/2 : ℝ)
          ≤ (X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ) :=
        (isSelfAdjoint_rpow X _).conjugate_le_conjugate (hAα i hi)
      have h2 : (X ^ (1/2 : ℝ) : E →L[ℂ] E) * (α • (1 : E →L[ℂ] E)) * X ^ (1/2 : ℝ)
          = α • X := by
        rw [mul_smul_comm, smul_mul_assoc, mul_one, rpow_half_mul_rpow_half hX]
      have h3 : (α * α) • (1 : E →L[ℂ] E) ≤ α • X := by
        rw [mul_smul]
        exact smul_le_smul_of_nonneg_left hXα hα.le
      exact h3.trans (h2 ▸ h1)
    have hmpos : (0 : ℝ) < min (α * α) α := lt_min (by positivity) hα
    have hlowb' : (min (α * α) α) • (1 : E →L[ℂ] E)
        ≤ (X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ) := by
      refine le_trans ?_ hlowb
      exact smul_le_smul_of_nonneg_right (min_le_left _ _) (zero_le_one (α := E →L[ℂ] E))
    have hlowX' : (min (α * α) α) • (1 : E →L[ℂ] E) ≤ X := by
      refine le_trans ?_ hXα
      exact smul_le_smul_of_nonneg_right (min_le_right _ _) (zero_le_one (α := E →L[ℂ] E))
    have hsub := isHilbertSchmidt_cfcSqrt_sub hmpos hlowb' hlowX' (hbc i hi)
    rwa [hXsq] at hsub
  -- `X - X^{1/2}` is Hilbert–Schmidt
  have hK : IsHilbertSchmidt (X - (X ^ (1/2 : ℝ) : E →L[ℂ] E)) := by
    have hid : X - (X ^ (1/2 : ℝ) : E →L[ℂ] E)
        = ∑ i ∈ s, w i • (CFC.sqrt ((X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ))
          - (X ^ (1/2 : ℝ) : E →L[ℂ] E)) := by
      rw [Finset.sum_congr rfl fun i _ => smul_sub (w i)
        (CFC.sqrt ((X ^ (1/2 : ℝ) : E →L[ℂ] E) * Av i * X ^ (1/2 : ℝ)))
        ((X ^ (1/2 : ℝ) : E →L[ℂ] E)),
        Finset.sum_sub_distrib, ← Finset.sum_smul, hwsum, one_smul, hsqeq]
    rw [hid]
    exact IsHilbertSchmidt.sum s fun i hi => IsHilbertSchmidt.real_smul (hsummand i hi) _
  -- transfer to `X^{1/2} - 1` and then to `X - 1`
  have hhalf : IsHilbertSchmidt ((X ^ (1/2 : ℝ) : E →L[ℂ] E) - 1) := by
    have hid : (X ^ (1/2 : ℝ) : E →L[ℂ] E) - 1
        = (X ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (X - X ^ (1/2 : ℝ)) := by
      have hexp : (X ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (X - X ^ (1/2 : ℝ))
          = (X ^ (-(1/2) : ℝ) : E →L[ℂ] E) * (X ^ (1/2 : ℝ) * X ^ (1/2 : ℝ))
            - (X ^ (-(1/2) : ℝ) : E →L[ℂ] E) * X ^ (1/2 : ℝ) := by
        rw [rpow_half_mul_rpow_half hX]; noncomm_ring
      rw [hexp, ← mul_assoc, rpow_neg_half_mul_rpow_half hX, one_mul]
    rw [hid]
    exact hK.comp_left _
  have hid2 : X - 1 = ((X ^ (1/2 : ℝ) : E →L[ℂ] E) - 1) * ((X ^ (1/2 : ℝ) : E →L[ℂ] E) + 1) := by
    have hexp : ((X ^ (1/2 : ℝ) : E →L[ℂ] E) - 1) * ((X ^ (1/2 : ℝ) : E →L[ℂ] E) + 1)
        = (X ^ (1/2 : ℝ) : E →L[ℂ] E) * X ^ (1/2 : ℝ) - 1 := by noncomm_ring
    rw [hexp, rpow_half_mul_rpow_half hX]
  rw [hid2]
  exact hhalf.comp_right _

/-- **A Wasserstein point of a family in `Σ₂` lies in `Σ₂`.**  General scalar part `γ`. -/
theorem isHilbertSchmidt_sub_smul_one_of_isWassersteinPoint {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - γ • (1 : E →L[ℂ] E)))
    (hW : IsWassersteinPoint s w Av X) :
    IsHilbertSchmidt (X - γ • (1 : E →L[ℂ] E)) := by
  have hγinv : (0 : ℝ) < γ⁻¹ := inv_pos.mpr hγ
  have hXpos : IsStrictlyPositive X := hW.1
  have hXi := IsWassersteinPoint.mem_Icc hα hβ hwsum hw hA hAα hAβ hW
  have hB : ∀ i ∈ s, IsStrictlyPositive (γ⁻¹ • Av i) := fun i hi =>
    IsStrictlyPositive.smul hγinv (hA i hi)
  have hBα : ∀ i ∈ s, (γ⁻¹ * α) • (1 : E →L[ℂ] E) ≤ γ⁻¹ • Av i := by
    intro i hi
    rw [mul_smul]
    exact smul_le_smul_of_nonneg_left (hAα i hi) hγinv.le
  have hYα : (γ⁻¹ * α) • (1 : E →L[ℂ] E) ≤ γ⁻¹ • X := by
    rw [mul_smul]
    exact smul_le_smul_of_nonneg_left hXi.1 hγinv.le
  have hBHS : ∀ i ∈ s, IsHilbertSchmidt (γ⁻¹ • Av i - 1) := by
    intro i hi
    have hid : (γ⁻¹ • Av i - 1 : E →L[ℂ] E) = γ⁻¹ • (Av i - γ • (1 : E →L[ℂ] E)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hγ), one_smul]
    rw [hid]
    exact IsHilbertSchmidt.real_smul (hHS i hi) _
  have hYW : IsWassersteinPoint s (w) (fun i => γ⁻¹ • Av i) (γ⁻¹ • X) :=
    (isWassersteinPoint_smul hγinv hXpos hA).mpr hW
  have hY := isHilbertSchmidt_sub_one_of_isWassersteinPoint (by positivity : (0:ℝ) < γ⁻¹ * α)
    hwsum hB hBα hYα hBHS hYW
  have hid : X - γ • (1 : E →L[ℂ] E) = γ • (γ⁻¹ • X - 1) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (ne_of_gt hγ), one_smul]
  rw [hid]
  exact IsHilbertSchmidt.real_smul hY _

/-- **Theorem 3.7 (Kim–Mer–Pálfia).**  The unique Wasserstein point near the identity of a family
in `1 + SL²` again lies in `1 + SL²`. -/
theorem existsUnique_isWassersteinPoint_sigmaTwo_near_one
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAδ : ∀ i ∈ s, ‖Av i - 1‖ ≤ 1/128)
    (hHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1)) :
    ∃! X : E →L[ℂ] E,
      (‖X - 1‖ ≤ 1/32 ∧ IsWassersteinPoint s w Av X) ∧ IsHilbertSchmidt (X - 1) := by
  obtain ⟨X, ⟨hX1, hXW⟩, huniq⟩ :=
    existsUnique_isWassersteinPoint_near_one hw hwsum hA hAδ
  have hXsa : IsSelfAdjoint X := hXW.1.isSelfAdjoint
  have hα : (0 : ℝ) < 1 - 1/32 := by norm_num
  have hAα : ∀ i ∈ s, (1 - 1/32 : ℝ) • (1 : E →L[ℂ] E) ≤ Av i := fun i hi =>
    smul_one_le_of_norm_sub_one_le (hA i hi).isSelfAdjoint
      ((hAδ i hi).trans (by norm_num))
  have hXα : (1 - 1/32 : ℝ) • (1 : E →L[ℂ] E) ≤ X :=
    smul_one_le_of_norm_sub_one_le hXsa hX1
  refine ⟨X, ⟨⟨hX1, hXW⟩,
    isHilbertSchmidt_sub_one_of_isWassersteinPoint hα hwsum hA hAα hXα hHS hXW⟩, ?_⟩
  rintro Z ⟨hZ, -⟩
  exact huniq Z hZ

/-- **Corollary 3.8 (Kim–Mer–Pálfia).**  On a Loewner interval of ratio at most `(1+1/128)²`,
the Wasserstein equation has a unique solution, and it lies in `Σ₂` whenever the data do. -/
theorem existsUnique_isWassersteinPoint_sigmaTwo_of_ratio
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hratio : β ≤ α * ((1 + 1/128) * (1 + 1/128)))
    (hHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - γ • (1 : E →L[ℂ] E))) :
    ∃! X : E →L[ℂ] E,
      IsWassersteinPoint s w Av X ∧ IsHilbertSchmidt (X - γ • (1 : E →L[ℂ] E)) := by
  obtain ⟨X, hXW, huniq⟩ :=
    existsUnique_isWassersteinPoint_of_ratio hw hwsum hα hβ hA hAα hAβ hratio
  refine ⟨X, ⟨hXW, isHilbertSchmidt_sub_smul_one_of_isWassersteinPoint hα hβ hγ hw hwsum
    hA hAα hAβ hHS hXW⟩, ?_⟩
  rintro Z ⟨hZ, -⟩
  exact huniq Z hZ

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
