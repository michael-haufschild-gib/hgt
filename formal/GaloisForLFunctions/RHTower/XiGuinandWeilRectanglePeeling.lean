import GaloisForLFunctions.RHTower.FinitePeeling
import GaloisForLFunctions.RHTower.XiGuinandWeilContourSynthesis

/-!
# Exact Xi zero peeling on an admissible rectangle

The Xi zeros in a closed rectangle form a finite set.  Peeling precisely that packet from `XiC`
gives an entire cofactor which is nonzero throughout the rectangle, while retaining every exterior
zero.  Its nonzero locus supplies the open neighbourhood required by the weighted argument
principle.

Consequently, on every positively oriented rectangle whose boundary is pointwise admissible for the
continued Guinand--Weil formula, the contour integral of an arbitrary entire weight against the
full continued prime--archimedean source is exactly the analytic-multiplicity-weighted sum of that
weight over the enclosed centered Xi zeros.  No infinite divisor sum is interchanged with the
contour integral.
-/

open Complex Filter intervalIntegral Set

namespace RHTower

noncomputable section

/-- The centered Xi zeros in any closed coordinate rectangle form a finite set. -/
theorem xiC_zeros_closedRectangle_finite (z₁ z₂ : ℂ) :
    {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) | XiC z = 0}.Finite := by
  have hcod : (XiC ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    XiC_analytic.preimage_zero_mem_codiscreteWithin
      (x := 0) XiC_zero_ne (Set.mem_univ 0) isConnected_univ
  have hcodK : (XiC ⁻¹' {0}ᶜ) ∈ codiscreteWithin
      (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_uIcc.reProdIm isCompact_uIcc).finite_diff_of_mem_codiscreteWithin
    hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- The finite set of distinct centered Xi zeros in the closed rectangle. -/
def xiCClosedRectangleZeros (z₁ z₂ : ℂ) : Finset ℂ :=
  (xiC_zeros_closedRectangle_finite z₁ z₂).toFinset

@[simp] theorem mem_xiCClosedRectangleZeros {z₁ z₂ z : ℂ} :
    z ∈ xiCClosedRectangleZeros z₁ z₂ ↔
      z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ∧ XiC z = 0 := by
  rw [xiCClosedRectangleZeros, Set.Finite.mem_toFinset, Set.mem_sep_iff]

/-- **Exact closed-rectangle Xi factorization.**  Peeling the distinct zeros in the rectangle
produces their exact analytic multiplicities and an entire cofactor nonvanishing on the whole
closed rectangle. -/
theorem exists_xiC_closedRectangle_factorization (z₁ z₂ : ℂ) :
    ∃ (m : ℂ → ℕ) (h : ℂ → ℂ), AnalyticOnNhd ℂ h Set.univ ∧
      (∀ w ∈ xiCClosedRectangleZeros z₁ z₂,
        m w = (analyticOrderAt XiC w).toNat) ∧
      (∀ z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im), h z ≠ 0) ∧
      ∀ z : ℂ, XiC z =
        (∏ w ∈ xiCClosedRectangleZeros z₁ z₂, (z - w) ^ m w) * h z := by
  obtain ⟨m, h, hhan, hm, hh0, hfact⟩ := exists_finite_peel isOpen_univ
    XiC_analytic (xiCClosedRectangleZeros z₁ z₂) (by simp)
      (fun w _ => XiC_order_ne_top w)
  refine ⟨m, h, hhan, hm, ?_, fun z => hfact z (Set.mem_univ z)⟩
  intro z hzK hhzero
  have hXi0 : XiC z = 0 := by
    rw [hfact z (Set.mem_univ z), hhzero, mul_zero]
  exact hh0 z (mem_xiCClosedRectangleZeros.mpr ⟨hzK, hXi0⟩) hhzero

/-- **Admissible-rectangle Guinand--Weil extraction.**  For an entire weight `g`, a positively
oriented rectangle with pointwise Xi-explicit-formula admissible boundary converts the full
continued prime--archimedean source trace into the exact analytic-multiplicity-weighted sum of `g`
over all centered Xi zeros in the closed rectangle.  Boundary admissibility ensures that every
listed zero is actually strict interior. -/
theorem rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * g w := by
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_xiC_closedRectangle_factorization z₁ z₂
  let U : Set ℂ := {z : ℂ | h z ≠ 0}
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hUopen : IsOpen U := by
    change IsOpen (h ⁻¹' {0}ᶜ)
    exact isOpen_compl_singleton.preimage hhcont
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U :=
    fun z hz => hhK z hz
  have hin : ∀ w ∈ xiCClosedRectangleZeros z₁ z₂,
      z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_xiCClosedRectangleZeros.mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    have hwreU := hwre
    have hwimU := hwim
    rw [uIcc_of_le hre.le] at hwre
    rw [uIcc_of_le him.le] at hwim
    have hrel : z₁.re < w.re := by
      have hne : z₁.re ≠ w.re := by
        intro heq
        have hedge : (z₁.re : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (hleft w.im hwimU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.1 hne
    have hrer : w.re < z₂.re := by
      have hne : w.re ≠ z₂.re := by
        intro heq
        have hedge : (z₂.re : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (hright w.im hwimU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.2 hne
    have himl : z₁.im < w.im := by
      have hne : z₁.im ≠ w.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₁.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (hbot w.re hwreU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.1 hne
    have himr : w.im < z₂.im := by
      have hne : w.im ≠ z₂.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₂.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (htop w.re hwreU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.2 hne
    exact ⟨hrel, hrer, himl, himr⟩
  have hres := rectIntegral_continuedPrimeArchSourceRelativeTrace_of_factorization
    (xiCClosedRectangleZeros z₁ z₂) (fun w => w) m hg hUopen hin hsub
      (fun z _ => hhan z (Set.mem_univ z)) (fun _ hz => hz)
      (fun z _ => hfact z) hbot htop hright hleft
  calc
    rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
        2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
          (m w : ℂ) * g w := by
      simpa only using hres
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * g w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      rw [hm w hw]

end

end RHTower
