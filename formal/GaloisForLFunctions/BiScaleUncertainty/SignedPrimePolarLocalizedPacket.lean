import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarPacket

/-! Support-localized packet identities and Cauchy bounds. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

theorem signedSource_zero_of_right_support (f : C_c(ℝ, ℝ)) (K : ℕ) {L u : ℝ}
    (hf : ∀ x, L ≤ x → f x = 0) (hu : L ≤ u) : signedSource f K u = 0 := by
  have ha : atomicSource f K u = 0 := by
    change (∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*f (u+Real.log m)) = 0
    apply Finset.sum_eq_zero
    intro m hm
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
    rw [hf _ (by linarith), mul_zero]
  have hp : polarSource f K u = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    rw [hf _ (by linarith [ht.1]), mul_zero]
  change atomicSource f K u-polarSource f K u = 0
  rw [ha, hp, sub_self]

/-- A right support bound stabilizes packets at each physical location it covers. -/
theorem signedSource_stable_of_right_support (f : C_c(ℝ, ℝ)) {A K : ℕ} {L u : ℝ}
    (hf : ∀ x, L ≤ x → f x = 0) (hAK : A ≤ K) (hcut : L ≤ u+cutoff A) :
    signedSource f K u = signedSource f A u := by
  have hlog : cutoff A ≤ cutoff K := by
    unfold cutoff
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show A+2 ≤ K+2 by omega)
  have ha : atomicSource f K u = atomicSource f A u := by
    symm
    change (∑ m ∈ Finset.Icc 1 (A+2), primeWeight m*f (u+Real.log m)) =
      ∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*f (u+Real.log m)
    apply Finset.sum_subset (fun m hm => Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hm).1, by have := (Finset.mem_Icc.mp hm).2; omega⟩)
    intro m hm hnot
    have hAm : A+2 ≤ m := by
      simp only [Finset.mem_Icc] at hm hnot
      omega
    have hlogm : cutoff A ≤ Real.log (m : ℝ) := by
      unfold cutoff
      exact Real.log_le_log (by positivity) (by exact_mod_cast hAm)
    rw [hf _ (by linarith), mul_zero]
  have hp : polarSource f K u = polarSource f A u := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      (fun t ht => ⟨ht.1, ht.2.trans hlog⟩)
    intro t ht
    have htA : cutoff A ≤ t := by
      by_contra! h
      exact ht.2 ⟨ht.1.1, h.le⟩
    rw [hf _ (by linarith), mul_zero]
  change atomicSource f K u-polarSource f K u = atomicSource f A u-polarSource f A u
  rw [ha, hp]

/-- Only the packet region where the source pairing is supported enters the bound. -/
theorem pairing_sq_le_local_packet (q f : C_c(ℝ, ℝ)) (K : ℕ) (a b : ℝ)
    (houtside : ∀ u, u ∉ Icc a b → q u*signedSource f K u = 0) :
    pairing K (fun t => ∫ u, q u*f (u+t)) ^ 2 ≤
      (∫ u, q u^2)*(∫ u in Icc a b, signedSource f K u^2) := by
  have hq : IntegrableOn (fun u => q u^2) (Icc a b) := (q.continuous.pow 2).integrableOn_Icc
  have hf : IntegrableOn (fun u => signedSource f K u^2) (Icc a b) :=
    ((signedSource f K).continuous.pow 2).integrableOn_Icc
  have hs := HTGeometry.sq_integral_mul_le (μ := volume.restrict (Icc a b))
    (f := (q : ℝ → ℝ)) (g := (signedSource f K : ℝ → ℝ))
    q.continuous.aestronglyMeasurable (signedSource f K).continuous.aestronglyMeasurable hq hf
  have he : (∫ u in Icc a b, q u*signedSource f K u) =
      pairing K (fun t => ∫ u, q u*f (u+t)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero houtside, integral_mul_signedSource]
  rw [he] at hs
  have hqle : (∫ u in Icc a b, q u^2) ≤ ∫ u, q u^2 :=
    setIntegral_le_integral (integrable_sq q.continuous q.hasCompactSupport)
      (Filter.Eventually.of_forall fun u => sq_nonneg (q u))
  exact hs.trans (mul_le_mul_of_nonneg_right hqle
    (setIntegral_nonneg measurableSet_Icc fun u _ => sq_nonneg _))

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
