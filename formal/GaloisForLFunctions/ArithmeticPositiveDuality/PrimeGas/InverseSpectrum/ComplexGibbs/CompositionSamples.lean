import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.GermRecovery

/-! # Critical-line sampling determines the surviving spectrum

A reciprocal sequence of clock displacements stays on the isometric line.
Agreement on any infinite subsequence recovers every squared singular value.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Clock samples displaced from height t by the successive critical occupation weights. -/
def compositionSample (t : ℝ) (n : ℕ) : ℂ := ⟨1/2,t + occupationWeight n⟩

theorem compositionSample_isometry (t : ℝ) (n : ℕ) :
    ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split (compositionSample t n) f x :=
  (split_isometric_iff _).mpr rfl

/-- Isometric clock samples accumulate at height t without meeting it. -/
theorem tendsto_samples (t : ℝ) :
    Tendsto (compositionSample t) atTop (𝓝[≠] (⟨1/2,t⟩ : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have he : compositionSample t = fun n => (⟨1/2,t⟩ : ℂ) + (occupationWeight n : ℂ)*Complex.I := by
      funext n
      apply Complex.ext <;> simp [compositionSample]
    have hv : Tendsto (fun n => (occupationWeight n : ℂ)) atTop (𝓝 (0:ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp occupationWeight_tendsto
    rw [he]
    simpa only [zero_mul,add_zero] using (tendsto_const_nhds (x := (⟨1/2,t⟩ : ℂ))).add (hv.mul_const Complex.I)
  · apply Eventually.of_forall
    intro n h
    have he : t + occupationWeight n = t := congrArg Complex.im h
    linarith only [he,occupationWeight_pos n]

/-- No ordering assumptions are needed on the propagators: their approximation numbers are already decreasing. -/
theorem composition_samples_iff_physical_levels (t : ℝ) (P Q : Projection) {r q : ℕ}
    (hP : MissingDimension P r) (cP : Conserving (projected P))
    (hQ : MissingDimension Q q) (cQ : Conserving (projected Q)) :
    (∃ᶠ n in atTop, relativePartition (physicalSpectrum P hP cP) (compositionSample t n) =
      relativePartition (physicalSpectrum Q hQ cQ) (compositionSample t n)) ↔
    ∀ n, _root_.RHTower.approxNumber ((projected P)^2) n = _root_.RHTower.approxNumber ((projected Q)^2) n := by
  let b := physicalSpectrum P hP cP
  let c := physicalSpectrum Q hQ cQ
  constructor
  · intro h
    apply levels_of_accumulating_agreement b c (_root_.RHTower.approxNumber_antitone _)
      (_root_.RHTower.approxNumber_antitone _) (z := (⟨1/2,t⟩ : ℂ)) (by change (0:ℝ) < 1/2; norm_num)
    exact fun hne => h ((tendsto_samples t).eventually hne)
  · intro h
    have he : relativePartition b = relativePartition c := relativePartition_eq_of_levels (b := b) (c := c) h
    exact (Eventually.of_forall (fun n => congrFun he (compositionSample t n))).frequently

#print axioms compositionSample_isometry
#print axioms composition_samples_iff_physical_levels

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
