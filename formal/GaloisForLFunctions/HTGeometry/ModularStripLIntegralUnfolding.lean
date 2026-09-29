import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-!
# Unfolding the modular strip for nonnegative functions

For every `T`-periodic `g : ℍ → [0, ∞]`,
`Σ_{(c,d) coprime} ∫_𝒟 g(M_{c,d} z) = 2 ∫_{0 ≤ Re w < 1} g(w)` (`tsum_lintegral_fd_eq_two_mul_lintegral_strip`),
with no integrability hypothesis: the strip and `⋃_{(c,d)} M_{c,d}𝒟` (over one of each pair `±(c,d)`) are
fundamental domains for the translations, the translates of `𝒟` are almost disjoint, and `±(c,d)` give
the same term.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries
open scoped MatrixGroups ENNReal Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem setLIntegral_smul_fd (g : SL(2, ℤ)) (φ : ℍ → ℝ≥0∞) :
    ∫⁻ z in g • fd, φ z = ∫⁻ z in fd, φ (g • z) := by
  rw [← Set.image_smul]
  exact ((measurePreserving_smul g volume).setLIntegral_comp_emb (measurableEmbedding_const_smul g)
    φ fd).symm

/-- **Unfolding for nonnegative functions.** -/
theorem tsum_lintegral_fd_eq_two_mul_lintegral_strip {g : ℍ → ℝ≥0∞}
    (hg : ∀ (n : ℤ) (z : ℍ), g (ModularGroup.T ^ n • z) = g z) :
    ∑' p : gammaSet 1 1 0, ∫⁻ z in fd, g (gammaSetMatrix p • z) =
      2 * ∫⁻ w in modularStrip, g w := by
  have hinv : ∀ (h : translationSubgroup) (z : ℍ), g (h • z) = g z := fun h z => by
    obtain ⟨n, hn⟩ := translationSubgroup_smul_eq h z
    rw [hn, hg]
  have hstrip : ∫⁻ w in modularStrip, g w = ∫⁻ w in ⋃ v : gammaSetHalf, halfRep v • fd, g w :=
    isFundamentalDomain_modularStrip.setLIntegral_eq isFundamentalDomain_iUnion_halfRep_smul_fd g hinv
  have hunion : ∫⁻ w in ⋃ v : gammaSetHalf, halfRep v • fd, g w =
      ∑' v : gammaSetHalf, ∫⁻ z in fd, g (gammaSetMatrix v.1 • z) := by
    rw [lintegral_iUnion₀ (fun v => isFundamentalDomain_fd.nullMeasurableSet_smul (halfRep v))
      (fun v w hvw => isFundamentalDomain_fd.aedisjoint fun heq =>
        hvw (translation_mul_halfRep_injective 1 1 v w (by simpa using heq)).2) g]
    refine tsum_congr fun v => ?_
    rw [halfRep_smul_fd, setLIntegral_smul_fd]
  have hneg : ∀ p : gammaSet 1 1 0, ∫⁻ z in fd, g (gammaSetMatrix (gammaSetNeg p) • z) =
      ∫⁻ z in fd, g (gammaSetMatrix p • z) := fun p => by
    congr 1
    funext z
    obtain ⟨n, hn⟩ := gammaSetMatrix_gammaSetNeg_smul p z
    rw [hn, hg]
  have hcompl : ∑' x : (gammaSetHalfᶜ : Set (gammaSet 1 1 0)), ∫⁻ z in fd, g (gammaSetMatrix x.1 • z) =
      ∑' v : gammaSetHalf, ∫⁻ z in fd, g (gammaSetMatrix v.1 • z) := by
    set F : gammaSet 1 1 0 → ℝ≥0∞ := fun p => ∫⁻ z in fd, g (gammaSetMatrix p • z)
    calc ∑' x : (gammaSetHalfᶜ : Set (gammaSet 1 1 0)), F x.1
        = ∑' v : gammaSetHalf, F (gammaSetHalfNegEquiv v).1 :=
          (gammaSetHalfNegEquiv.tsum_eq (fun x => F x.1)).symm
      _ = ∑' v : gammaSetHalf, F v.1 := tsum_congr fun v => hneg v.1
  have hsplit : (∑' x : gammaSetHalf, ∫⁻ z in fd, g (gammaSetMatrix x.1 • z)) +
      ∑' x : (gammaSetHalfᶜ : Set (gammaSet 1 1 0)), ∫⁻ z in fd, g (gammaSetMatrix x.1 • z) =
      ∑' p : gammaSet 1 1 0, ∫⁻ z in fd, g (gammaSetMatrix p • z) :=
    Summable.tsum_add_tsum_compl (s := gammaSetHalf)
      (f := fun p : gammaSet 1 1 0 => ∫⁻ z in fd, g (gammaSetMatrix p • z)) ENNReal.summable
      ENNReal.summable
  rw [hstrip, hunion, ← hsplit, hcompl, two_mul]

end

end GaloisForLFunctions.HTGeometry
