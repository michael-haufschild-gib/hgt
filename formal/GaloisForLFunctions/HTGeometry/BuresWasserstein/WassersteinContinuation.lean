import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinExistenceStep
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinHomotopy

/-!
# Homotopy continuation for the Wasserstein equation

Along the affine homotopy `Aᵢ(τ) = (1-τ)·1 + τ·Aᵢ` the Loewner interval is fixed, so all the
constants of the gradient step are uniform in `τ`.  Starting from the solution `X = 1` at `τ = 0`
and stepping by a fixed amount, finitely many applications of
`exists_isWassersteinPoint_of_small_defect` reach `τ = 1`.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- The clipped homotopy parameter moves by at most the step size. -/
lemma abs_min_one_sub_min_one_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    |min 1 (((n : ℝ) + 1) * δ) - min 1 ((n : ℝ) * δ)| ≤ δ := by
  have hmono : (n : ℝ) * δ ≤ ((n : ℝ) + 1) * δ := by nlinarith
  have hle : min 1 ((n : ℝ) * δ) ≤ min 1 (((n : ℝ) + 1) * δ) := by
    exact min_le_min (le_refl 1) hmono
  rw [abs_of_nonneg (by linarith)]
  rcases le_total (((n : ℝ) + 1) * δ) 1 with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total ((n : ℝ) * δ) 1 with h2 | h2
    · rw [min_eq_right h2]; nlinarith
    · rw [min_eq_left h2]; nlinarith
  · rw [min_eq_left h1]
    rcases le_total ((n : ℝ) * δ) 1 with h2 | h2
    · rw [min_eq_right h2]; nlinarith
    · rw [min_eq_left h2]; nlinarith

/-- The Wasserstein field vanishes exactly at Wasserstein points. -/
lemma wassField_eq_zero_of_isWassersteinPoint {Bv : ι → E →L[ℂ] E} {X : E →L[ℂ] E}
    (hwsum : ∑ i ∈ s, w i = 1) (hW : IsWassersteinPoint s w Bv X) :
    wassField s w Bv X = 0 :=
  (wassField_eq_zero_iff hwsum hW.1).mpr hW

/-- Loewner bounds for the homotopy on `[0,1]`. -/
lemma homotopy_Icc {a₀ b₀ τ : ℝ} (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ 1) (hb₁ : 1 ≤ b₀)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (_hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ b₀ • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1)) :
    (∀ i ∈ s, IsStrictlyPositive (homotopyFamily Av τ i))
      ∧ (∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ homotopyFamily Av τ i)
      ∧ (∀ i ∈ s, homotopyFamily Av τ i ≤ b₀ • (1 : E →L[ℂ] E))
      ∧ (∀ i ∈ s, IsHilbertSchmidt (homotopyFamily Av τ i - 1)) := by
  refine ⟨fun i hi => isStrictlyPositive_homotopyFamily ha₀ hτ0 hτ1 (hAα i hi), fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · have h := smul_one_le_homotopyFamily (Av := Av) (i := i) hτ0 hτ1 (hAα i hi)
    rwa [min_eq_right ha₁] at h
  · have h := homotopyFamily_le_smul_one (Av := Av) (i := i) hτ0 hτ1 (hAβ i hi)
    rwa [max_eq_right hb₁] at h
  · have hid : homotopyFamily Av τ i - 1 = τ • (Av i - 1) := by
      have h := homotopyFamily_sub Av τ 0 i
      rwa [homotopyFamily_zero, sub_zero] at h
    rw [hid]
    exact IsHilbertSchmidt.real_smul (hAHS i hi) _

/-- **One homotopy step.** -/
theorem exists_isWassersteinPoint_homotopy_succ
    {a₀ b₀ r t θ σ τ : ℝ}
    (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ 1) (hb₁ : 1 ≤ b₀)
    (hr : 0 < r) (hrα : r ≤ a₀ / 2) (_hrβ : r ≤ b₀) (ht : 0 < t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hfac : 1 - 2 * t * ((a₀ / 2) * (a₀ / 2) / (2 * ((2 * b₀) * ((2 * b₀) * (2 * b₀))))
        - secondOrderConst (a₀ / 2) (2 * b₀) * (2 * r))
      + t ^ 2 * (wassLipConst (a₀ / 2) (2 * b₀)) ^ 2 ≤ θ ^ 2)
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ b₀ • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1))
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {X₀ : E →L[ℂ] E} (hX₀HS : IsHilbertSchmidt (X₀ - 1))
    (hX₀W : IsWassersteinPoint s w (homotopyFamily Av σ) X₀)
    (hdefect : t * hsNorm (wassField s w (homotopyFamily Av τ) X₀) ≤ (1 - θ) * r) :
    ∃ X : E →L[ℂ] E, IsHilbertSchmidt (X - 1)
      ∧ IsWassersteinPoint s w (homotopyFamily Av τ) X := by
  have hb₀ : (0 : ℝ) < b₀ := by linarith
  obtain ⟨hAσ, hAσα, hAσβ, hAσHS⟩ := homotopy_Icc (τ := σ) ha₀ ha₁ hb₁ hσ0 hσ1 hA hAα hAβ hAHS
  obtain ⟨hAτ, hAτα, hAτβ, hAτHS⟩ := homotopy_Icc (τ := τ) ha₀ ha₁ hb₁ hτ0 hτ1 hA hAα hAβ hAHS
  have hIcc := IsWassersteinPoint.mem_Icc ha₀ hb₀ hwsum hw hAσ hAσα hAσβ hX₀W
  have hαpos : (0 : ℝ) < a₀ / 2 := by linarith
  have hβpos : (0 : ℝ) < 2 * b₀ := by linarith
  have hX₀α : (a₀ / 2 + r) • (1 : E →L[ℂ] E) ≤ X₀ := by
    refine le_trans (smul_le_smul_of_nonneg_right ?_ (zero_le_one (α := E →L[ℂ] E))) hIcc.1
    linarith
  have hX₀β : X₀ ≤ (2 * b₀ - r) • (1 : E →L[ℂ] E) := by
    refine hIcc.2.trans (smul_le_smul_of_nonneg_right ?_ (zero_le_one (α := E →L[ℂ] E)))
    linarith
  have hAτα' : ∀ i ∈ s, (a₀ / 2) • (1 : E →L[ℂ] E) ≤ homotopyFamily Av τ i := by
    intro i hi
    refine le_trans (smul_le_smul_of_nonneg_right ?_ (zero_le_one (α := E →L[ℂ] E)))
      (hAτα i hi)
    linarith
  have hAτβ' : ∀ i ∈ s, homotopyFamily Av τ i ≤ (2 * b₀) • (1 : E →L[ℂ] E) := by
    intro i hi
    refine (hAτβ i hi).trans (smul_le_smul_of_nonneg_right ?_ (zero_le_one (α := E →L[ℂ] E)))
    linarith
  obtain ⟨X, hXsa, hXHS, hXb, hXW⟩ :=
    exists_isWassersteinPoint_of_small_defect hαpos hβpos hr ht hθ0 hθ1
      (fun i hi => (hw i hi).le) hwsum hAτ hAτα' hAτβ' hAτHS
      hX₀W.1.isSelfAdjoint hX₀α hX₀β hX₀HS hfac hdefect
  refine ⟨X, ?_, hXW⟩
  have hid : (X : E →L[ℂ] E) - 1 = (X - X₀) + (X₀ - 1) := by abel
  rw [hid]
  exact hXHS.add hX₀HS

/-- **The defect after a homotopy step is linear in the step.** -/
theorem hsNorm_wassField_homotopy_defect {a₀ b₀ Λ σ τ : ℝ}
    (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ 1) (hb₁ : 1 ≤ b₀)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ b₀ • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1))
    (hΛ : ∀ i ∈ s, hsNorm (Av i - 1) ≤ Λ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    {X₀ : E →L[ℂ] E} (hX₀ : IsStrictlyPositive X₀)
    (hX₀α : a₀ • (1 : E →L[ℂ] E) ≤ X₀) (hX₀β : X₀ ≤ b₀ • (1 : E →L[ℂ] E))
    (hX₀W : IsWassersteinPoint s w (homotopyFamily Av σ) X₀) :
    (2 * (Real.sqrt (b₀⁻¹ * a₀) * a₀))
        * hsNorm (wassField s w (homotopyFamily Av τ) X₀)
      ≤ (a₀⁻¹ * b₀) * (|σ - τ| * Λ) := by
  have hb₀ : (0 : ℝ) < b₀ := by linarith
  have hainv : (0 : ℝ) < a₀⁻¹ := inv_pos.mpr ha₀
  have hbinv : (0 : ℝ) < b₀⁻¹ := inv_pos.mpr hb₀
  have hγ : (0 : ℝ) < Real.sqrt (b₀⁻¹ * a₀) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨hAσ, hAσα, hAσβ, hAσHS⟩ := homotopy_Icc (τ := σ) ha₀ ha₁ hb₁ hσ0 hσ1 hA hAα hAβ hAHS
  obtain ⟨hAτ, hAτα, hAτβ, hAτHS⟩ := homotopy_Icc (τ := τ) ha₀ ha₁ hb₁ hτ0 hτ1 hA hAα hAβ hAHS
  have hXlow : b₀⁻¹ • (1 : E →L[ℂ] E) ≤ X₀⁻¹ʳ :=
    smul_one_le_ringInverse_of_le_smul_one hX₀ hb₀ hX₀β
  have hXhigh : (X₀⁻¹ʳ : E →L[ℂ] E) ≤ a₀⁻¹ • (1 : E →L[ℂ] E) :=
    ringInverse_le_of_smul_one_le ha₀ hX₀α
  have hgσ : ∀ i ∈ s, (Real.sqrt (b₀⁻¹ * a₀)) • (1 : E →L[ℂ] E)
      ≤ gm X₀⁻¹ʳ (homotopyFamily Av σ i) := fun i hi =>
    smul_one_le_gm hX₀.ringInverse (hAσ i hi) hbinv ha₀ hXlow (hAσα i hi)
  have hgτ : ∀ i ∈ s, (Real.sqrt (b₀⁻¹ * a₀)) • (1 : E →L[ℂ] E)
      ≤ gm X₀⁻¹ʳ (homotopyFamily Av τ i) := fun i hi =>
    smul_one_le_gm hX₀.ringInverse (hAτ i hi) hbinv ha₀ hXlow (hAτα i hi)
  have hzero : wassField s w (homotopyFamily Av σ) X₀ = 0 :=
    wassField_eq_zero_of_isWassersteinPoint hwsum hX₀W
  have hmain := hsNorm_wassField_homotopy_sub_le (α := b₀⁻¹) (M := a₀⁻¹)
    (γ := Real.sqrt (b₀⁻¹ * a₀)) (Λ := Λ) (σ := σ) (τ := τ) hbinv hainv hγ hw hwsum hX₀
    hXlow hXhigh hAσ hAτ hgσ hgτ hAHS hΛ
  rw [hzero, zero_sub] at hmain
  have hneg : hsNorm (-wassField s w (homotopyFamily Av τ) X₀)
      = hsNorm (wassField s w (homotopyFamily Av τ) X₀) := by
    show Real.sqrt (hsNormSq _) = Real.sqrt (hsNormSq _)
    rw [hsNormSq_neg_eq_self]
  rw [hneg] at hmain
  rwa [inv_inv, inv_inv] at hmain

/-- The constant family `1` has Wasserstein point `1`. -/
lemma isWassersteinPoint_one (hwsum : ∑ i ∈ s, w i = 1) :
    IsWassersteinPoint s w (fun _ : ι => (1 : E →L[ℂ] E)) 1 := by
  refine ⟨isStrictlyPositive_one, ?_⟩
  have hterm : ∀ i ∈ s, w i • gm (1 : E →L[ℂ] E) (1 : E →L[ℂ] E)⁻¹ʳ
      = w i • (1 : E →L[ℂ] E) := by
    intro i _
    rw [Ring.inverse_one, gm_one_left, CFC.sqrt_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, hwsum, one_smul]

set_option maxHeartbeats 1000000 in
/-- The homotopy continuation, iterated. -/
theorem exists_isWassersteinPoint_homotopy_iter {a₀ b₀ r t θ Λ D δ : ℝ}
    (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ 1) (hb₁ : 1 ≤ b₀)
    (hr : 0 < r) (hrα : r ≤ a₀ / 2) (hrβ : r ≤ b₀) (ht : 0 < t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hδ0 : 0 < δ) (hΛ0 : 0 ≤ Λ)
    (hfac : 1 - 2 * t * ((a₀ / 2) * (a₀ / 2) / (2 * ((2 * b₀) * ((2 * b₀) * (2 * b₀))))
        - secondOrderConst (a₀ / 2) (2 * b₀) * (2 * r))
      + t ^ 2 * (wassLipConst (a₀ / 2) (2 * b₀)) ^ 2 ≤ θ ^ 2)
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ b₀ • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1))
    (hΛ : ∀ i ∈ s, hsNorm (Av i - 1) ≤ Λ)
    (hDprop : (a₀⁻¹ * b₀) * (δ * Λ)
      ≤ (2 * (Real.sqrt (b₀⁻¹ * a₀) * a₀)) * (D * δ))
    (htDδ : t * (D * δ) ≤ (1 - θ) * r) :
    ∀ n : ℕ, ∃ X : E →L[ℂ] E, IsHilbertSchmidt (X - 1)
      ∧ IsWassersteinPoint s w (homotopyFamily Av (min 1 ((n : ℝ) * δ))) X := by
  have hb₀ : (0 : ℝ) < b₀ := by linarith
  have hainv : (0 : ℝ) < a₀⁻¹ := inv_pos.mpr ha₀
  have hbinv : (0 : ℝ) < b₀⁻¹ := inv_pos.mpr hb₀
  have hγ : (0 : ℝ) < Real.sqrt (b₀⁻¹ * a₀) := Real.sqrt_pos.mpr (by positivity)
  have hpos : (0 : ℝ) < 2 * (Real.sqrt (b₀⁻¹ * a₀) * a₀) := by positivity
  intro n
  induction n with
  | zero =>
    refine ⟨1, by rw [sub_self]; exact isHilbertSchmidt_zero, ?_⟩
    have h0 : min 1 (((0 : ℕ) : ℝ) * δ) = 0 := by norm_num [hδ0.le]
    rw [h0, show homotopyFamily Av 0 = fun _ : ι => (1 : E →L[ℂ] E) from
      funext fun i => homotopyFamily_zero Av i]
    exact isWassersteinPoint_one hwsum
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
    obtain ⟨X₀, hX₀HS, hX₀W⟩ := ih
    have hσ0 : (0 : ℝ) ≤ min 1 ((n : ℝ) * δ) := le_min zero_le_one (by positivity)
    have hσ1 : min 1 ((n : ℝ) * δ) ≤ 1 := min_le_left _ _
    have hτ0 : (0 : ℝ) ≤ min 1 (((n : ℝ) + 1) * δ) := le_min zero_le_one (by positivity)
    have hτ1 : min 1 (((n : ℝ) + 1) * δ) ≤ 1 := min_le_left _ _
    obtain ⟨hAσ, hAσα, hAσβ, hAσHS⟩ :=
      homotopy_Icc (τ := min 1 ((n : ℝ) * δ)) ha₀ ha₁ hb₁ hσ0 hσ1 hA hAα hAβ hAHS
    have hIcc := IsWassersteinPoint.mem_Icc ha₀ hb₀ hwsum hw hAσ hAσα hAσβ hX₀W
    have hdef := hsNorm_wassField_homotopy_defect (a₀ := a₀) (b₀ := b₀) (Λ := Λ)
      (σ := min 1 ((n : ℝ) * δ)) (τ := min 1 (((n : ℝ) + 1) * δ))
      ha₀ ha₁ hb₁ (fun i hi => (hw i hi).le) hwsum hA hAα hAβ hAHS hΛ hσ0 hσ1 hτ0 hτ1
      hX₀W.1 hIcc.1 hIcc.2 hX₀W
    have hstepsize : |min 1 ((n : ℝ) * δ) - min 1 (((n : ℝ) + 1) * δ)| ≤ δ := by
      rw [abs_sub_comm]
      exact abs_min_one_sub_min_one_le hδ0.le n
    have hup : (a₀⁻¹ * b₀) * (|min 1 ((n : ℝ) * δ) - min 1 (((n : ℝ) + 1) * δ)| * Λ)
        ≤ (a₀⁻¹ * b₀) * (δ * Λ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstepsize hΛ0) (by positivity)
    have hNbound : hsNorm (wassField s w
        (homotopyFamily Av (min 1 (((n : ℝ) + 1) * δ))) X₀) ≤ D * δ :=
      le_of_mul_le_mul_left ((hdef.trans hup).trans hDprop) hpos
    have hdefect : t * hsNorm (wassField s w
        (homotopyFamily Av (min 1 (((n : ℝ) + 1) * δ))) X₀) ≤ (1 - θ) * r :=
      (mul_le_mul_of_nonneg_left hNbound ht.le).trans htDδ
    exact exists_isWassersteinPoint_homotopy_succ ha₀ ha₁ hb₁ hr hrα hrβ ht hθ0 hθ1
      hfac hw hwsum hA hAα hAβ hAHS hσ0 hσ1 hτ0 hτ1 hX₀HS hX₀W hdefect

set_option maxHeartbeats 400000 in
/-- **Theorem 3.16 (Kim–Mer–Pálfia).**  For a family in `1 + SL²` lying in any Loewner interval
`[a₀·1, b₀·1]` with `a₀ ≤ 1 ≤ b₀`, the Wasserstein equation has a solution, and the solution again
lies in `1 + SL²`. -/
theorem exists_isWassersteinPoint_of_Icc {a₀ b₀ : ℝ}
    (ha₀ : 0 < a₀) (ha₁ : a₀ ≤ 1) (hb₁ : 1 ≤ b₀)
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, a₀ • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ b₀ • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1)) :
    ∃ X : E →L[ℂ] E, IsHilbertSchmidt (X - 1) ∧ IsWassersteinPoint s w Av X := by
  classical
  have hb₀ : (0 : ℝ) < b₀ := by linarith
  have hαpos : (0 : ℝ) < a₀ / 2 := by linarith
  have hβpos : (0 : ℝ) < 2 * b₀ := by linarith
  have hr₀ : (0 : ℝ) < min (a₀ / 2) b₀ := lt_min hαpos hb₀
  obtain ⟨r, t, θ, hr, hrr₀, ht, hθ0, hθ1, hfac⟩ := exists_step_constants hαpos hβpos hr₀
  have hrα : r ≤ a₀ / 2 := hrr₀.trans (min_le_left _ _)
  have hrβ : r ≤ b₀ := hrr₀.trans (min_le_right _ _)
  have hΛ : ∀ i ∈ s, hsNorm (Av i - 1) ≤ ∑ j ∈ s, hsNorm (Av j - 1) :=
    fun i hi => Finset.single_le_sum (f := fun j => hsNorm (Av j - 1))
      (fun j _ => hsNorm_nonneg _) hi
  have hΛ0 : (0 : ℝ) ≤ ∑ j ∈ s, hsNorm (Av j - 1) :=
    Finset.sum_nonneg fun i _ => hsNorm_nonneg _
  set Λ : ℝ := ∑ j ∈ s, hsNorm (Av j - 1) with hΛdef
  have hainv : (0 : ℝ) < a₀⁻¹ := inv_pos.mpr ha₀
  have hbinv : (0 : ℝ) < b₀⁻¹ := inv_pos.mpr hb₀
  have hγ : (0 : ℝ) < Real.sqrt (b₀⁻¹ * a₀) := Real.sqrt_pos.mpr (by positivity)
  have hne : (2 : ℝ) * (Real.sqrt (b₀⁻¹ * a₀) * a₀) ≠ 0 := by positivity
  set D : ℝ := (a₀⁻¹ * b₀) * Λ / (2 * (Real.sqrt (b₀⁻¹ * a₀) * a₀)) with hDdef
  have hD0 : (0 : ℝ) ≤ D := by rw [hDdef]; positivity
  have htne : t ≠ 0 := ne_of_gt ht
  have hD1ne : D + 1 ≠ 0 := by positivity
  have hθlt : (0 : ℝ) < 1 - θ := by linarith
  set δ : ℝ := (1 - θ) * r / (t * (D + 1)) with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hDprop : (a₀⁻¹ * b₀) * (δ * Λ)
      ≤ (2 * (Real.sqrt (b₀⁻¹ * a₀) * a₀)) * (D * δ) := by
    refine le_of_eq ?_
    rw [hDdef]
    field_simp
  have htDδ : t * (D * δ) ≤ (1 - θ) * r := by
    have hid : t * (D * δ) = (D / (D + 1)) * ((1 - θ) * r) := by
      rw [hδdef]
      field_simp
    rw [hid]
    have hfrac : D / (D + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith [hfrac, mul_nonneg hθlt.le hr.le]
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / δ)
  obtain ⟨X, hXHS, hXW⟩ := exists_isWassersteinPoint_homotopy_iter ha₀ ha₁ hb₁ hr hrα hrβ ht
    hθ0 hθ1 hδ0 hΛ0 hfac hw hwsum hA hAα hAβ hAHS hΛ hDprop htDδ n
  have hone : min 1 ((n : ℝ) * δ) = 1 := by
    refine min_eq_left ?_
    rw [div_le_iff₀ hδ0] at hn
    linarith
  rw [hone, show homotopyFamily Av 1 = Av from funext fun i => homotopyFamily_one Av i] at hXW
  exact ⟨X, hXHS, hXW⟩


end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
