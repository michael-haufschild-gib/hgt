import GaloisForLFunctions.RHTower.Sieve.RamareAnnulusPartitioned

/-!
# The affine majorant of the Ramaré bilinear mean square, against a frequency partition

`Sieve/RamareLadderAffine.integral_normSq_ramareBilinear_affine_le` repackages the cut-window bound
as `slope·W + const`, which is the shape the fibre capstone
`Sieve/FibreRamareLadderFinal` consumes.  The partitioned bound of
`Sieve/RamareAnnulusPartitioned` is affine in the window in exactly the same way — the exceptional
part contributes only to the constant, because its prime mean square `J j` is taken over the
largest window once and reused.

The slope and constant are written out rather than imported from `Sieve/RamareLadderAffine`, and
the ladder defect is again a hypothesis, so that this module stays off the Route-T stack.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- The slope of the partitioned affine majorant. -/
def ramarePartSlope (M L : ℕ) (Q η : ℝ) (V : ℕ → ℝ) (Dslope : ℝ) : ℝ :=
  2 * (L : ℝ) * ∑ j ∈ Finset.range L,
      V j ^ (2 : ℕ) * (5 * Real.pi / 2 * ((geomCofactorBlock M Q η j).card : ℝ))
    + 2 * Dslope

/-- The constant of the partitioned affine majorant. -/
def ramarePartConst (M L : ℕ) (Q η w₀ : ℝ) (V U Vlow Us J : ℕ → ℝ) (Dconst : ℝ) : ℝ :=
  2 * (L : ℝ) * ∑ j ∈ Finset.range L,
      (V j ^ (2 : ℕ) * (5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
            * ((geomCofactorBlock M Q η j).card : ℝ))
        + Us j ^ (2 : ℕ) * J j
        + Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀))
    + 2 * Dconst

/-- **The partitioned affine majorant.**  Uniform over every window below `T₀`. -/
theorem integral_normSq_ramareBilinear_affine_partitioned_le {P : Finset ℕ} (M : ℕ)
    {Q η w₀ T₀ Dslope Dconst : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hw₀ : 0 ≤ w₀) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    (hDfct : ∀ W : ℝ, 1 ≤ W → W ≤ T₀ →
      (∫ w in Set.Icc (-W) W, ‖ramareLadderError P M Q η L w‖ ^ (2 : ℕ)) ≤ Dslope * W + Dconst)
    {S : Set ℝ} (hSm : MeasurableSet S)
    (V U Vlow Us J : ℕ → ℝ) (hV : ∀ j, 0 ≤ V j) (hU : ∀ j, 0 ≤ U j) (hVlow : ∀ j, 0 ≤ Vlow j)
    (hann : ∀ j ∈ Finset.range L, ∀ w ∈ S \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hcof : ∀ j ∈ Finset.range L, ∀ w ∈ (Set.Icc (-T₀) T₀ \ S) \ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ≤ Us j)
    (hJ : ∀ j ∈ Finset.range L,
      (∫ w in (Set.Icc (-T₀) T₀ \ S) \ Set.Icc (-w₀) w₀,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ (2 : ℕ)) ≤ J j)
    (hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ Vlow j)
    (hlowC : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ≤ U j) :
    ∀ W : ℝ, 1 ≤ W → w₀ ≤ W → W ≤ T₀ →
      (∫ w in Set.Icc (-W) W, ‖ramareBilinear P M w‖ ^ (2 : ℕ))
        ≤ ramarePartSlope M L Q η V Dslope * W
          + ramarePartConst M L Q η w₀ V U Vlow Us J Dconst := by
  classical
  intro W hW hwW hWT
  have hIccsub : Set.Icc (-W) W ⊆ Set.Icc (-T₀) T₀ := by
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  set SW : Set ℝ := S ∩ Set.Icc (-W) W with hSW
  have hSWm : MeasurableSet SW := hSm.inter measurableSet_Icc
  have hSWs : SW ⊆ Set.Icc (-W) W := Set.inter_subset_right
  have hcompl : Set.Icc (-W) W \ SW = Set.Icc (-W) W \ S := by
    rw [hSW]
    ext u
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hannW : ∀ j ∈ Finset.range L, ∀ w ∈ SW \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j := by
    intro j hj w hw
    exact hann j hj w ⟨hw.1.1, hw.2⟩
  have hsubU : (Set.Icc (-W) W \ SW) \ Set.Icc (-w₀) w₀
      ⊆ (Set.Icc (-T₀) T₀ \ S) \ Set.Icc (-w₀) w₀ := by
    rw [hcompl]
    intro u hu
    exact ⟨⟨hIccsub hu.1.1, hu.1.2⟩, hu.2⟩
  have hcofW : ∀ j ∈ Finset.range L, ∀ w ∈ (Set.Icc (-W) W \ SW) \ Set.Icc (-w₀) w₀,
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ≤ Us j :=
    fun j hj w hw => hcof j hj w (hsubU hw)
  have hJW : ∀ j ∈ Finset.range L,
      (∫ w in (Set.Icc (-W) W \ SW) \ Set.Icc (-w₀) w₀,
        ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ (2 : ℕ)) ≤ J j := by
    intro j hj
    have hcont : Continuous fun w : ℝ => ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ (2 : ℕ) :=
      ((continuous_primeBlockPoly _).norm).pow 2
    have hint : IntegrableOn (fun w : ℝ => ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ (2 : ℕ))
        ((Set.Icc (-T₀) T₀ \ S) \ Set.Icc (-w₀) w₀) volume :=
      (hcont.integrableOn_Icc (a := -T₀) (b := T₀)).mono_set
        (fun u hu => hu.1.1)
    have hmono := MeasureTheory.setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun w => by positivity)
      (Filter.Eventually.of_forall hsubU)
    exact hmono.trans (hJ j hj)
  have hbase := integral_normSq_ramareBilinear_annulus_partitioned_le (P := P) M hQ hη hW hw₀ hwW
    hL hP (hDfct W hW hWT) hSWm hSWs V U Vlow Us J hV hU hVlow hannW hcofW hJW hlowP hlowC
  refine hbase.trans (le_of_eq ?_)
  rw [ramarePartSlope, ramarePartConst]
  have hterm : ∀ j ∈ Finset.range L,
      (V j ^ (2 : ℕ) * ((5 * Real.pi / 2 * W
            + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
          * ((geomCofactorBlock M Q η j).card : ℝ))
        + Us j ^ (2 : ℕ) * J j
        + Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀))
      = V j ^ (2 : ℕ) * (5 * Real.pi / 2 * ((geomCofactorBlock M Q η j).card : ℝ)) * W
        + (V j ^ (2 : ℕ) * (5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
              * ((geomCofactorBlock M Q η j).card : ℝ))
            + Us j ^ (2 : ℕ) * J j
            + Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀)) := by
    intro j _
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

end

end RHTower.Sieve

namespace RHTower.Sieve

noncomputable section

open Finset

theorem ramarePartSlope_nonneg (M L : ℕ) (Q η : ℝ) {Dslope : ℝ}
    (V : ℕ → ℝ) (hDs : 0 ≤ Dslope) : 0 ≤ ramarePartSlope M L Q η V Dslope := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_))
    (by linarith)
  positivity

theorem ramarePartConst_nonneg (M L : ℕ) (Q η : ℝ) {w₀ Dconst : ℝ}
    (hw₀ : 0 ≤ w₀) (V U Vlow Us J : ℕ → ℝ) (hJ0 : ∀ j, 0 ≤ J j) (hDc : 0 ≤ Dconst) :
    0 ≤ ramarePartConst M L Q η w₀ V U Vlow Us J Dconst := by
  refine add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => ?_))
    (by linarith)
  have h1 : (0 : ℝ) ≤ V j ^ (2 : ℕ) * (5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
      * ((geomCofactorBlock M Q η j).card : ℝ)) := by positivity
  have h2 : (0 : ℝ) ≤ Us j ^ (2 : ℕ) * J j := mul_nonneg (sq_nonneg _) (hJ0 j)
  have h3 : (0 : ℝ) ≤ Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀) := by positivity
  linarith

end

end RHTower.Sieve
