import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinMeasureExistence
import GaloisForLFunctions.HTGeometry.BuresWasserstein.RobbinsMonroCesaro

/-!
# Perturbed gradient descent for the Wasserstein barycentre of a measure

The stochastic approximation of Theorem 5.3 replaces the exact field `Φ_μ` by a perturbed one at
each step and takes the vanishing step size `λ/(n+1)`.  On a Loewner interval the exact step is a
`√(1 - λκ/2)`-contraction towards the barycentre, so the perturbed iterates obey

`d(n+1) ≤ (1 - λκ/(4(n+1))) d(n) + (n+1)⁻¹ λ ‖perturbation‖`,

and Robbins–Monro with a Cesàro-null perturbation gives `d(n) → 0`.  Only the Cesàro means of the
perturbation are required to vanish, not the perturbation itself; that is exactly the strength
Etemadi's weighted strong law provides in the stochastic setting.
-/

open scoped NNReal Ring BigOperators InnerProductSpace
open Filter Topology MeasureTheory ContinuousLinearMap

attribute [local instance] InnerProductSpace.complexToReal

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Perturbed gradient descent converges to the Wasserstein barycentre.**  The perturbation of
the field only has to be Cesàro-null. -/
theorem tendsto_hsNorm_sub_of_perturbed_descent [IsProbabilityMeasure μ]
    {Av : Ω → E →L[ℂ] E} {α β lam : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hint : ∀ Z : E →L[ℂ] E, IsSelfAdjoint Z → α • (1 : E →L[ℂ] E) ≤ Z →
      Z ≤ β • (1 : E →L[ℂ] E) → (∀ w, IsHilbertSchmidt (Z - Av w)) →
      Integrable (fun w => wassSL (Av w) Z) μ)
    {Y : E →L[ℂ] E}
    (hYsa : IsSelfAdjoint Y) (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hYHS : ∀ w, IsHilbertSchmidt (Y - Av w))
    (hYzero : wassFieldMeasure μ Av Y = 0)
    {X G : ℕ → E →L[ℂ] E}
    (hXsa : ∀ n, IsSelfAdjoint (X n)) (hXα : ∀ n, α • (1 : E →L[ℂ] E) ≤ X n)
    (hXβ : ∀ n, X n ≤ β • (1 : E →L[ℂ] E))
    (hXHS : ∀ n w, IsHilbertSchmidt (X n - Av w))
    (hGHS : ∀ n, IsHilbertSchmidt (G n - wassFieldMeasure μ Av (X n)))
    (hstep : ∀ n : ℕ, X (n + 1) = X n - (lam / ((n : ℝ) + 1)) • G n)
    (hlam : 0 < lam)
    (hlam2 : lam ≤ (α * α / (2 * (β * (β * β)))) / (2 * (wassLipConst α β) ^ 2))
    (hlam3 : lam * (α * α / (2 * (β * (β * β)))) ≤ 2)
    (hces : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
        hsNorm (G i - wassFieldMeasure μ Av (X i))) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => hsNorm (X n - Y)) atTop (𝓝 0) := by
  classical
  set κ : ℝ := α * α / (2 * (β * (β * β))) with hκdef
  set L : ℝ := wassLipConst α β with hLdef
  set Csec : ℝ := secondOrderConst α β with hCdef
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  have hLpos : 0 < L := by
    rw [hLdef]
    unfold wassLipConst
    have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
    have hai : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
    positivity
  have hCpos : 0 < Csec := by rw [hCdef]; exact secondOrderConst_pos hα hβ
  -- the subdivision that makes the second-order defect harmless
  obtain ⟨N, hNge⟩ := exists_nat_ge (Csec * (2 * β) / (κ / 2) + 1)
  have hCM : (0 : ℝ) ≤ Csec * (2 * β) / (κ / 2) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; norm_num at hN1
    · exact h
  have hNR : (0 : ℝ) < (N : ℝ) := by linarith
  -- structural facts
  have hYpos : IsStrictlyPositive Y := isStrictlyPositive_of_smul_one_le hα hYα
  have hXpos : ∀ n, IsStrictlyPositive (X n) := fun n =>
    isStrictlyPositive_of_smul_one_le hα (hXα n)
  have hopX : ∀ n w, (wassSL (Av w) (X n)).op = (1 : E →L[ℂ] E) - gm (Av w) (X n)⁻¹ʳ :=
    fun n w => wassSL_op hα hβ (hA w) (hXpos n) (hAα w) (hAβ w) (hXβ n) (hXHS n w)
  have hopY : ∀ w, (wassSL (Av w) Y).op = (1 : E →L[ℂ] E) - gm (Av w) Y⁻¹ʳ :=
    fun w => wassSL_op hα hβ (hA w) hYpos (hAα w) (hAβ w) hYβ (hYHS w)
  have hintX : ∀ n, Integrable (fun w => wassSL (Av w) (X n)) μ := fun n =>
    hint (X n) (hXsa n) (hXα n) (hXβ n) (hXHS n)
  have hintY : Integrable (fun w => wassSL (Av w) Y) μ := hint Y hYsa hYα hYβ hYHS
  have hdiffHS : ∀ n, IsHilbertSchmidt (X n - Y) := by
    intro n
    obtain ⟨w⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure (μ := μ)
    have h := (hXHS n w).sub (hYHS w)
    rwa [show (X n - Av w) - (Y - Av w) = X n - Y by abel] at h
  have hnormle : ∀ n, ‖X n - Y‖ ≤ 2 * β := by
    intro n
    have hx := norm_le_of_Icc hα hβ (hXα n) (hXβ n)
    have hy := norm_le_of_Icc hα hβ hYα hYβ
    calc ‖X n - Y‖ ≤ ‖X n‖ + ‖Y‖ := norm_sub_le _ _
      _ ≤ 2 * β := by linarith
  -- the one-step contraction
  have hcontr : ∀ n : ℕ, hsNorm ((X n - (lam / ((n : ℝ) + 1)) • wassFieldMeasure μ Av (X n)) - Y)
      ≤ (1 - (lam / ((n : ℝ) + 1)) * κ / 4) * hsNorm (X n - Y) := by
    intro n
    set t : ℝ := lam / ((n : ℝ) + 1) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have htle : t ≤ lam := by
      rw [htdef, div_le_iff₀ (by positivity : (0:ℝ) < (n : ℝ) + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, hlam.le]
    have hstep' := hsNormSq_gradientStepMeasure_sub_le (α := α) (β := β) (t := t)
      hα hβ htpos.le hA (hXpos n) hYpos hAα hAβ (hXα n) (hXβ n) hYα hYβ
      (hdiffHS n) (hintX n) hintY (hopX n) hopY hNpos
    rw [hYzero, smul_zero, sub_zero] at hstep'
    -- the factor
    have hdefect : Csec * (‖X n - Y‖ / (N : ℝ)) ≤ κ / 2 := by
      have h1 : ‖X n - Y‖ / (N : ℝ) ≤ (2 * β) / (N : ℝ) := by gcongr; exact hnormle n
      have h2 : Csec * (‖X n - Y‖ / (N : ℝ)) ≤ Csec * ((2 * β) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hCpos.le
      refine h2.trans ?_
      rw [mul_div_assoc', div_le_iff₀ hNR]
      have h3 : Csec * (2 * β) / (κ / 2) ≤ (N : ℝ) - 1 := by linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < κ / 2)] at h3
      nlinarith [hκpos, hNR]
    have hquad : t ^ 2 * L ^ 2 ≤ t * κ / 2 := by
      have hLs : (0 : ℝ) < 2 * L ^ 2 := by positivity
      have h' : lam * (2 * L ^ 2) ≤ κ := (le_div_iff₀ hLs).mp hlam2
      have h1 : t * L ^ 2 ≤ lam * L ^ 2 := mul_le_mul_of_nonneg_right htle (sq_nonneg L)
      have h2 : lam * L ^ 2 ≤ κ / 2 := by linarith
      have h3 : t * L ^ 2 ≤ κ / 2 := le_trans h1 h2
      have h4 := mul_le_mul_of_nonneg_left h3 htpos.le
      nlinarith [h4]
    have hfac : 1 - 2 * t * (κ - Csec * (‖X n - Y‖ / (N : ℝ))) + t ^ 2 * L ^ 2
        ≤ 1 - t * κ / 2 := by
      nlinarith [htpos.le, hdefect, hquad]
    have hlam3' : lam * κ ≤ 2 := hlam3
    have htκ : t * κ / 2 ≤ 1 := by
      have hle : t * κ ≤ lam * κ := mul_le_mul_of_nonneg_right htle hκpos.le
      linarith [hlam3', hle]
    have h14 : (0 : ℝ) ≤ 1 - t * κ / 4 := by linarith
    have hsq : hsNormSq ((X n - t • wassFieldMeasure μ Av (X n)) - Y)
        ≤ ((1 - t * κ / 4) * hsNorm (X n - Y)) ^ 2 := by
      refine hstep'.trans ?_
      have hb : (1 - t * κ / 2) ≤ (1 - t * κ / 4) ^ 2 := by
        nlinarith [sq_nonneg (t * κ)]
      calc (1 - 2 * t * (κ - Csec * (‖X n - Y‖ / (N : ℝ))) + t ^ 2 * L ^ 2) * hsNormSq (X n - Y)
          ≤ (1 - t * κ / 2) * hsNormSq (X n - Y) :=
            mul_le_mul_of_nonneg_right hfac (hsNormSq_nonneg _)
        _ ≤ (1 - t * κ / 4) ^ 2 * hsNormSq (X n - Y) :=
            mul_le_mul_of_nonneg_right hb (hsNormSq_nonneg _)
        _ = ((1 - t * κ / 4) * hsNorm (X n - Y)) ^ 2 := by rw [mul_pow, sq_hsNorm]
    rw [← sq_hsNorm] at hsq
    exact le_of_pow_le_pow_left₀ two_ne_zero
      (mul_nonneg h14 (hsNorm_nonneg _)) hsq
  -- the perturbed recursion
  have hrec : ∀ n : ℕ, hsNorm (X (n + 1) - Y)
      ≤ (1 - (lam * κ / 4) / ((n : ℝ) + 1)) * hsNorm (X n - Y)
        + (1 / ((n : ℝ) + 1)) * (lam * hsNorm (G n - wassFieldMeasure μ Av (X n)))
        + 0 * (1 / ((n : ℝ) + 1)) ^ 2 := by
    intro n
    set t : ℝ := lam / ((n : ℝ) + 1) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have hsplit : X (n + 1) - Y
        = ((X n - t • wassFieldMeasure μ Av (X n)) - Y)
          - t • (G n - wassFieldMeasure μ Av (X n)) := by
      rw [hstep n, ← htdef, smul_sub]
      abel
    have hHS1 : IsHilbertSchmidt ((X n - t • wassFieldMeasure μ Av (X n)) - Y) := by
      have h1 : IsHilbertSchmidt (wassFieldMeasure μ Av (X n)) :=
        isHilbertSchmidt_wassFieldMeasure (hintX n) (hopX n)
      have h2 : (X n - t • wassFieldMeasure μ Av (X n)) - Y
          = (X n - Y) - t • wassFieldMeasure μ Av (X n) := by abel
      rw [h2]
      exact (hdiffHS n).sub (h1.real_smul t)
    have hHS2 : IsHilbertSchmidt (t • (G n - wassFieldMeasure μ Av (X n))) :=
      (hGHS n).real_smul t
    have htri : hsNorm (X (n + 1) - Y)
        ≤ hsNorm ((X n - t • wassFieldMeasure μ Av (X n)) - Y)
          + hsNorm (t • (G n - wassFieldMeasure μ Av (X n))) := by
      rw [hsplit]
      exact hsNorm_sub_le hHS1 hHS2
    have hsm : hsNorm (t • (G n - wassFieldMeasure μ Av (X n)))
        = (1 / ((n : ℝ) + 1)) * (lam * hsNorm (G n - wassFieldMeasure μ Av (X n))) := by
      rw [hsNorm_real_smul, abs_of_pos htpos, htdef]
      ring
    have hc := hcontr n
    rw [← htdef] at hc
    have hid1 : (1 - t * κ / 4) = 1 - (lam * κ / 4) / ((n : ℝ) + 1) := by
      rw [htdef]; field_simp
    rw [hid1] at hc
    rw [hsm] at htri
    linarith
  -- Robbins–Monro with a Cesàro-null perturbation
  have hacond : 0 < lam * κ / 4 := by positivity
  have hacond1 : lam * κ / 4 < 1 := by linarith
  have hcesL : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
      lam * hsNorm (G i - wassFieldMeasure μ Av (X i))) / (n : ℝ)) atTop (𝓝 0) := by
    have h := hces.const_mul lam
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  exact tendsto_zero_of_robbins_cesaro hacond hacond1
    (fun n => hsNorm_nonneg _) hrec hcesL

/-- **The empirical resolvent iteration converges to the barycentre.**  Each step uses the field
of its own probability measure `ν(n+1)` supported in the same Loewner interval, so the interval is
preserved automatically; only the Cesàro means of the field discrepancies have to vanish.  This is
the deterministic content of the strong law of large numbers for the Wasserstein barycentre. -/
theorem tendsto_hsNorm_sub_of_empirical_descent [IsProbabilityMeasure μ]
    {ν : ℕ → Measure Ω} (hν : ∀ n, IsProbabilityMeasure (ν n))
    {Av : Ω → E →L[ℂ] E} {α β lam : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β)
    (hA : ∀ w, IsStrictlyPositive (Av w))
    (hAα : ∀ w, α • (1 : E →L[ℂ] E) ≤ Av w) (hAβ : ∀ w, Av w ≤ β • (1 : E →L[ℂ] E))
    (hint : ∀ Z : E →L[ℂ] E, IsSelfAdjoint Z → α • (1 : E →L[ℂ] E) ≤ Z →
      Z ≤ β • (1 : E →L[ℂ] E) → (∀ w, IsHilbertSchmidt (Z - Av w)) →
      Integrable (fun w => wassSL (Av w) Z) μ)
    (hintν : ∀ n : ℕ, ∀ Z : E →L[ℂ] E, IsSelfAdjoint Z → α • (1 : E →L[ℂ] E) ≤ Z →
      Z ≤ β • (1 : E →L[ℂ] E) → (∀ w, IsHilbertSchmidt (Z - Av w)) →
      Integrable (fun w => wassSL (Av w) Z) (ν n))
    {Y : E →L[ℂ] E}
    (hYsa : IsSelfAdjoint Y) (hYα : α • (1 : E →L[ℂ] E) ≤ Y) (hYβ : Y ≤ β • (1 : E →L[ℂ] E))
    (hYHS : ∀ w, IsHilbertSchmidt (Y - Av w))
    (hYzero : wassFieldMeasure μ Av Y = 0)
    {X : ℕ → E →L[ℂ] E}
    (hX0sa : IsSelfAdjoint (X 0)) (hX0α : α • (1 : E →L[ℂ] E) ≤ X 0)
    (hX0β : X 0 ≤ β • (1 : E →L[ℂ] E)) (hX0HS : ∀ w, IsHilbertSchmidt (X 0 - Av w))
    (hstep : ∀ n : ℕ, X (n + 1)
      = X n - (lam / ((n : ℝ) + 1)) • wassFieldMeasure (ν (n + 1)) Av (X n))
    (hlam : 0 < lam) (hlamα : lam ≤ 2 * α)
    (hlam2 : lam ≤ (α * α / (2 * (β * (β * β)))) / (2 * (wassLipConst α β) ^ 2))
    (hlam3 : lam * (α * α / (2 * (β * (β * β)))) ≤ 2)
    (hces : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,
        hsNorm (wassFieldMeasure (ν (i + 1)) Av (X i) - wassFieldMeasure μ Av (X i)))
          / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => hsNorm (X n - Y)) atTop (𝓝 0) := by
  have hβ : 0 < β := lt_of_lt_of_le hα hαβ
  have htbound : ∀ n : ℕ, lam / ((n : ℝ) + 1) ≤ 2 * α := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_iff₀ h1]
    nlinarith [Nat.cast_nonneg (α := ℝ) n, hα.le, hlam.le]
  -- the iteration stays in the Loewner interval
  have hclass : ∀ n, IsSelfAdjoint (X n) ∧ α • (1 : E →L[ℂ] E) ≤ X n
      ∧ X n ≤ β • (1 : E →L[ℂ] E) ∧ ∀ w, IsHilbertSchmidt (X n - Av w) := by
    intro n
    induction n with
    | zero => exact ⟨hX0sa, hX0α, hX0β, hX0HS⟩
    | succ n ih =>
      obtain ⟨hsa, hlo, hhi, hHS⟩ := ih
      haveI := hν (n + 1)
      have hXpos : IsStrictlyPositive (X n) := isStrictlyPositive_of_smul_one_le hα hlo
      have hop : ∀ w, (wassSL (Av w) (X n)).op = (1 : E →L[ℂ] E) - gm (Av w) (X n)⁻¹ʳ :=
        fun w => wassSL_op hα hβ (hA w) hXpos (hAα w) (hAβ w) hhi (hHS w)
      have hF := hintν (n + 1) (X n) hsa hlo hhi hHS
      have hopint : Integrable (fun w => (1 : E →L[ℂ] E) - gm (Av w) (X n)⁻¹ʳ) (ν (n + 1)) :=
        integrable_one_sub_gm hF hop
      have htpos : (0 : ℝ) < lam / ((n : ℝ) + 1) := by positivity
      obtain ⟨hlo', hhi'⟩ := sub_smul_wassFieldMeasure_mem_Icc' hα hαβ htpos (htbound n)
        hXpos hA hAα hAβ hlo hhi hopint
      have hFHS : IsHilbertSchmidt (wassFieldMeasure (ν (n + 1)) Av (X n)) :=
        isHilbertSchmidt_wassFieldMeasure hF hop
      have hFsa : IsSelfAdjoint (wassFieldMeasure (ν (n + 1)) Av (X n)) :=
        isSelfAdjoint_wassFieldMeasure hF hop
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hstep n]
        exact hsa.sub (IsSelfAdjoint.smul (star_trivial _) hFsa)
      · rw [hstep n]; exact hlo'
      · rw [hstep n]; exact hhi'
      · intro w
        have hid : X (n + 1) - Av w
            = (X n - Av w) - (lam / ((n : ℝ) + 1)) • wassFieldMeasure (ν (n + 1)) Av (X n) := by
          rw [hstep n]
          exact sub_right_comm _ _ _
        rw [hid]
        exact (hHS w).sub (hFHS.real_smul _)
  -- the field discrepancies are Hilbert–Schmidt
  have hGHS : ∀ n, IsHilbertSchmidt
      (wassFieldMeasure (ν (n + 1)) Av (X n) - wassFieldMeasure μ Av (X n)) := by
    intro n
    obtain ⟨hsa, hlo, hhi, hHS⟩ := hclass n
    haveI := hν (n + 1)
    have hXpos : IsStrictlyPositive (X n) := isStrictlyPositive_of_smul_one_le hα hlo
    have hop : ∀ w, (wassSL (Av w) (X n)).op = (1 : E →L[ℂ] E) - gm (Av w) (X n)⁻¹ʳ :=
      fun w => wassSL_op hα hβ (hA w) hXpos (hAα w) (hAβ w) hhi (hHS w)
    exact (isHilbertSchmidt_wassFieldMeasure (hintν (n + 1) (X n) hsa hlo hhi hHS) hop).sub
      (isHilbertSchmidt_wassFieldMeasure (hint (X n) hsa hlo hhi hHS) hop)
  exact tendsto_hsNorm_sub_of_perturbed_descent hα hβ hA hAα hAβ hint hYsa hYα hYβ hYHS hYzero
    (fun n => (hclass n).1) (fun n => (hclass n).2.1) (fun n => (hclass n).2.2.1)
    (fun n w => (hclass n).2.2.2 w) hGHS hstep hlam hlam2 hlam3 hces

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
