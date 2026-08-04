import GaloisForLFunctions.RHTower.CCMRationalPeriodicWeightedStrongLogDecay
import GaloisForLFunctions.RHTower.DeningerMeyerStrongLogTarget

/-!
# Strong decay for periodic residue-Schwartz families

A finite sum of periodic traces with a common period is naturally encoded by
a Schwartz function at each residue.  Strong decay requires only global
physical and dual cancellations.  A finite-rank correction reduces global
dual cancellation to the already-proved one-function weighted theorem.
-/

noncomputable section

open Complex
open scoped FourierTransform SchwartzMap BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-- Kronecker residue weight. -/
def ccmRationalPeriodicDeltaWeight
    (M : ℕ) [NeZero M] (r : Fin M) : Fin M → ℂ :=
  fun s => if s = r then 1 else 0

@[simp]
theorem ccmRationalPeriodicDeltaWeight_self
    (M : ℕ) [NeZero M] (r : Fin M) :
    ccmRationalPeriodicDeltaWeight M r r = 1 := by
  simp [ccmRationalPeriodicDeltaWeight]

theorem sum_ccmRationalPeriodicDeltaWeight
    (M : ℕ) [NeZero M] (r : Fin M) :
    ∑ s, ccmRationalPeriodicDeltaWeight M r s = 1 := by
  simp [ccmRationalPeriodicDeltaWeight]

/-- Periodic log trace is linear in residue weight. -/
theorem ccmRationalPeriodicWeightedLogTrace_weight_add
    (M : ℕ) [NeZero M] (w v : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicWeightedLogTrace M (w + v) f =
      ccmRationalPeriodicWeightedLogTrace M w f +
        ccmRationalPeriodicWeightedLogTrace M v f := by
  funext t
  have hw := ccmRationalPeriodicWeightedTrace_summable
    M w f (Real.exp_ne_zero t)
  have hv := ccmRationalPeriodicWeightedTrace_summable
    M v f (Real.exp_ne_zero t)
  change (∑' n : ℤ,
      (w + v) (ccmRationalPeriodicResidue M n) *
        f (Real.exp t * (n : ℝ))) =
    (∑' n : ℤ, w (ccmRationalPeriodicResidue M n) *
        f (Real.exp t * (n : ℝ))) +
      ∑' n : ℤ, v (ccmRationalPeriodicResidue M n) *
        f (Real.exp t * (n : ℝ))
  rw [← hw.tsum_add hv]
  apply tsum_congr
  intro n
  simp only [Pi.add_apply]
  ring

theorem ccmRationalPeriodicWeightedLogTrace_weight_smul
    (M : ℕ) [NeZero M] (c : ℂ) (w : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicWeightedLogTrace M (c • w) f =
      c • ccmRationalPeriodicWeightedLogTrace M w f := by
  funext t
  have hw := ccmRationalPeriodicWeightedTrace_summable
    M w f (Real.exp_ne_zero t)
  change (∑' n : ℤ,
      (c • w) (ccmRationalPeriodicResidue M n) *
        f (Real.exp t * (n : ℝ))) =
    c • (∑' n : ℤ, w (ccmRationalPeriodicResidue M n) *
      f (Real.exp t * (n : ℝ)))
  rw [← hw.tsum_const_smul c]
  apply tsum_congr
  intro n
  simp [Pi.smul_apply]
  ring

/-- Periodic log trace is linear in its Schwartz function. -/
theorem ccmRationalPeriodicWeightedLogTrace_function_add
    (M : ℕ) [NeZero M] (w : Fin M → ℂ)
    (f g : CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicWeightedLogTrace M w (f + g) =
      ccmRationalPeriodicWeightedLogTrace M w f +
        ccmRationalPeriodicWeightedLogTrace M w g := by
  funext t
  have hf := ccmRationalPeriodicWeightedTrace_summable
    M w f (Real.exp_ne_zero t)
  have hg := ccmRationalPeriodicWeightedTrace_summable
    M w g (Real.exp_ne_zero t)
  change (∑' n : ℤ,
      w (ccmRationalPeriodicResidue M n) *
        (f + g) (Real.exp t * (n : ℝ))) =
    (∑' n : ℤ, w (ccmRationalPeriodicResidue M n) *
        f (Real.exp t * (n : ℝ))) +
      ∑' n : ℤ, w (ccmRationalPeriodicResidue M n) *
        g (Real.exp t * (n : ℝ))
  rw [← hf.tsum_add hg]
  apply tsum_congr
  intro n
  simp only [add_apply]
  ring

theorem ccmRationalPeriodicWeightedLogTrace_function_smul
    (M : ℕ) [NeZero M] (w : Fin M → ℂ) (c : ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicWeightedLogTrace M w (c • f) =
      c • ccmRationalPeriodicWeightedLogTrace M w f := by
  funext t
  have hf := ccmRationalPeriodicWeightedTrace_summable
    M w f (Real.exp_ne_zero t)
  change (∑' n : ℤ,
      w (ccmRationalPeriodicResidue M n) *
        (c • f) (Real.exp t * (n : ℝ))) =
    c • (∑' n : ℤ, w (ccmRationalPeriodicResidue M n) *
      f (Real.exp t * (n : ℝ)))
  rw [← hf.tsum_const_smul c]
  apply tsum_congr
  intro n
  simp only [smul_apply]
  ring

/-- Trace associated to a Schwartz family indexed by residue classes. -/
def ccmRationalPeriodicResidueSchwartzLogTrace
    (M : ℕ) [NeZero M]
    (g : Fin M → CCMRationalArchimedeanSchwartz) : ℝ → ℂ :=
  ∑ r, ccmRationalPeriodicWeightedLogTrace M
    (ccmRationalPeriodicDeltaWeight M r) (g r)

/-- Weight-to-trace linear map for fixed Schwartz source. -/
def ccmRationalPeriodicWeightLogTraceLM
    (M : ℕ) [NeZero M]
    (f : CCMRationalArchimedeanSchwartz) :
    (Fin M → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun w := ccmRationalPeriodicWeightedLogTrace M w f
  map_add' := fun w v =>
    ccmRationalPeriodicWeightedLogTrace_weight_add M w v f
  map_smul' := fun c w => by
    simpa using ccmRationalPeriodicWeightedLogTrace_weight_smul M c w f

/-- A rank-one residue-Schwartz family is its ordinary weighted trace. -/
theorem ccmRationalPeriodicResidueSchwartzLogTrace_rankOne
    (M : ℕ) [NeZero M] (c : Fin M → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicResidueSchwartzLogTrace M (fun r => c r • f) =
      ccmRationalPeriodicWeightedLogTrace M c f := by
  rw [ccmRationalPeriodicResidueSchwartzLogTrace]
  simp_rw [ccmRationalPeriodicWeightedLogTrace_function_smul]
  change (∑ r, c r • ccmRationalPeriodicWeightLogTraceLM M f
      (ccmRationalPeriodicDeltaWeight M r)) =
    ccmRationalPeriodicWeightLogTraceLM M f c
  have hweight :
      ∑ r, c r • ccmRationalPeriodicDeltaWeight M r = c := by
    funext s
    simp [ccmRationalPeriodicDeltaWeight]
  calc
    (∑ r, c r • ccmRationalPeriodicWeightLogTraceLM M f
        (ccmRationalPeriodicDeltaWeight M r)) =
        ∑ r, ccmRationalPeriodicWeightLogTraceLM M f
          (c r • ccmRationalPeriodicDeltaWeight M r) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact ((ccmRationalPeriodicWeightLogTraceLM M f).map_smul
        (c r) (ccmRationalPeriodicDeltaWeight M r)).symm
    _ = ccmRationalPeriodicWeightLogTraceLM M f
        (∑ r, c r • ccmRationalPeriodicDeltaWeight M r) := by
      rw [map_sum]
    _ = ccmRationalPeriodicWeightLogTraceLM M f c := by rw [hweight]

theorem ccmRationalPeriodicResidueSchwartzLogTrace_add
    (M : ℕ) [NeZero M]
    (g h : Fin M → CCMRationalArchimedeanSchwartz) :
    ccmRationalPeriodicResidueSchwartzLogTrace M (g + h) =
      ccmRationalPeriodicResidueSchwartzLogTrace M g +
        ccmRationalPeriodicResidueSchwartzLogTrace M h := by
  rw [ccmRationalPeriodicResidueSchwartzLogTrace,
    ccmRationalPeriodicResidueSchwartzLogTrace,
    ccmRationalPeriodicResidueSchwartzLogTrace]
  simp_rw [Pi.add_apply,
    ccmRationalPeriodicWeightedLogTrace_function_add]
  exact Finset.sum_add_distrib

/-- Pointwise Fourier-zero vanishing implies residue-family strong decay. -/
theorem ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay_of_pointwise
    (M : ℕ) [NeZero M]
    (g : Fin M → CCMRationalArchimedeanSchwartz)
    (hphysical : g 0 0 = 0)
    (hdual : ∀ r, (𝓕 (g r)) 0 = 0) :
    RHTower.DeningerMeyerStrongLogDecay
      (ccmRationalPeriodicResidueSchwartzLogTrace M g) := by
  rw [show ccmRationalPeriodicResidueSchwartzLogTrace M g =
      ∑ r, ccmRationalPeriodicWeightedLogTrace M
        (ccmRationalPeriodicDeltaWeight M r) (g r) by rfl]
  apply (RHTower.mem_deningerMeyerStrongLogTarget_iff _).mp
  apply RHTower.DeningerMeyerStrongLogTarget.sum_mem
  intro r hr
  apply (RHTower.mem_deningerMeyerStrongLogTarget_iff _).mpr
  apply ccmRationalPeriodicWeightedLogTrace_strongLogDecay
  · by_cases h : r = 0
    · subst r
      simp [ccmRationalPeriodicDeltaWeight, hphysical]
    · simp [ccmRationalPeriodicDeltaWeight, Ne.symm h]
  · rw [sum_ccmRationalPeriodicDeltaWeight, one_mul, hdual r]

/-- One nonzero Fourier mode gives a finite-rank correction reducing global
dual cancellation to pointwise dual cancellation. -/
theorem ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay_of_base
    (M : ℕ) [NeZero M]
    (g : Fin M → CCMRationalArchimedeanSchwartz)
    (hphysical : g 0 0 = 0)
    (hglobal : ∑ r, (𝓕 (g r)) 0 = 0)
    (r0 : Fin M) (hr0 : (𝓕 (g r0)) 0 ≠ 0)
    (hsafe : r0 = 0 ∨ (𝓕 (g 0)) 0 = 0) :
    RHTower.DeningerMeyerStrongLogDecay
      (ccmRationalPeriodicResidueSchwartzLogTrace M g) := by
  let I : Fin M → ℂ := fun r => (𝓕 (g r)) 0
  let c : Fin M → ℂ := fun r => I r / I r0
  let base : CCMRationalArchimedeanSchwartz := g r0
  let h : Fin M → CCMRationalArchimedeanSchwartz :=
    fun r => g r - c r • base
  have hc0physical : c 0 * base 0 = 0 := by
    rcases hsafe with hbase | hI0
    · subst r0
      dsimp [base]
      rw [hphysical, mul_zero]
    · have hc0 : c 0 = 0 := by simp [c, I, hI0]
      rw [hc0, zero_mul]
  have hhphysical : h 0 0 = 0 := by
    simp only [h, sub_apply, smul_apply]
    change g 0 0 - c 0 * base 0 = 0
    rw [hc0physical, hphysical, sub_zero]
  have hhdual : ∀ r, (𝓕 (h r)) 0 = 0 := by
    intro r
    change ((FourierTransform.fourierCLE ℂ
      CCMRationalArchimedeanSchwartz) (g r - c r • base)) 0 = 0
    rw [map_sub, map_smul]
    change I r - c r * I r0 = 0
    dsimp [c]
    rw [div_mul_cancel₀ (I r) hr0, sub_self]
  have hcsum : ∑ r, c r = 0 := by
    change (∑ r, I r / I r0) = 0
    rw [← Finset.sum_div]
    change (∑ r, (𝓕 (g r)) 0) / I r0 = 0
    rw [hglobal, zero_div]
  have hcorrection :
      RHTower.DeningerMeyerStrongLogDecay
        (ccmRationalPeriodicWeightedLogTrace M c base) := by
    apply ccmRationalPeriodicWeightedLogTrace_strongLogDecay
    · exact hc0physical
    · rw [hcsum, zero_mul]
  have hhstrong :=
    ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay_of_pointwise
      M h hhphysical hhdual
  have hdecomp : g = h + fun r => c r • base := by
    funext r
    simp [h]
  have htrace : ccmRationalPeriodicResidueSchwartzLogTrace M g =
      ccmRationalPeriodicResidueSchwartzLogTrace M h +
        ccmRationalPeriodicWeightedLogTrace M c base := by
    calc
      ccmRationalPeriodicResidueSchwartzLogTrace M g =
          ccmRationalPeriodicResidueSchwartzLogTrace M
            (h + fun r => c r • base) := by rw [hdecomp]
      _ = ccmRationalPeriodicResidueSchwartzLogTrace M h +
          ccmRationalPeriodicResidueSchwartzLogTrace M
            (fun r => c r • base) :=
        ccmRationalPeriodicResidueSchwartzLogTrace_add M h _
      _ = _ := by
        rw [ccmRationalPeriodicResidueSchwartzLogTrace_rankOne]
  rw [htrace]
  exact hhstrong.add hcorrection

/-- **Global residue-Schwartz strong-log theorem.** Only sum of Fourier zero
modes must vanish; individual residue Fourier integrals may cancel. -/
theorem ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay
    (M : ℕ) [NeZero M]
    (g : Fin M → CCMRationalArchimedeanSchwartz)
    (hphysical : g 0 0 = 0)
    (hglobal : ∑ r, (𝓕 (g r)) 0 = 0) :
    RHTower.DeningerMeyerStrongLogDecay
      (ccmRationalPeriodicResidueSchwartzLogTrace M g) := by
  by_cases hI0 : (𝓕 (g 0)) 0 = 0
  · by_cases hall : ∀ r, (𝓕 (g r)) 0 = 0
    · exact
        ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay_of_pointwise
          M g hphysical hall
    · push Not at hall
      obtain ⟨r0, hr0⟩ := hall
      exact ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay_of_base
        M g hphysical hglobal r0 hr0 (Or.inr hI0)
  · exact ccmRationalPeriodicResidueSchwartzLogTrace_strongLogDecay_of_base
      M g hphysical hglobal 0 hI0 (Or.inl rfl)

end RHTower
end GaloisForLFunctions
