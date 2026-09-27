import GaloisForLFunctions.RHTower.XiCriticalGaussianWeightedFloor

/-!
# One actual critical family reserves all weighted polynomial samples

The same paired family works for every real polynomial and every positive
heat time. This supplies nodal energy directly, before coefficient norms
or scalar interpolation floors are introduced.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

theorem exists_xiCriticalGaussian_paired_sampling_reserve (N : ℕ) :
    ∃ (γ : Fin N → ℝ) (q : Fin N → XiZeroCopy),
      Function.Injective (fun i => γ i ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}),
        2 * (∑ i, Q.eval (γ i ^ 2) ^ 2 * Real.exp (-((t : ℝ) * γ i ^ 2))) ≤
          xiGaussianRealChannelEnergy Q t := by
  classical
  obtain ⟨γ, q, hinj, hq, _⟩ := exists_xiCriticalGaussian_nodes N
  have hrinj : Function.Injective (fun i => γ i ^ 2) := by
    intro i j hij
    apply hinj
    change (γ i : ℂ) ^ 2 = (γ j : ℂ) ^ 2
    simpa only [Complex.ofReal_pow] using congrArg Complex.ofReal hij
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hinj
    change (γ i : ℂ) ^ 2 = (γ j : ℂ) ^ 2
    rw [← (hq i).2, ← (hq j).2, hij]
  let S := Finset.univ.image q
  let T := Finset.univ.image (fun i => xiZeroCopyConjEquiv (q i))
  have hCinj : Function.Injective (fun i => xiZeroCopyConjEquiv (q i)) :=
    xiZeroCopyConjEquiv.injective.comp hqinj
  have hdisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hpS hpT
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hpS
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpT
    have he : q i = xiZeroCopyConjEquiv (q j) := hi.trans hj.symm
    have hre := congrArg (fun r : XiZeroCopy => (xiSpectralPoint r).re) he
    rw [(hq i).2, xiSpectralPoint_copyConj, (hq j).2,
      Complex.neg_re, Complex.conj_re, Complex.ofReal_re, Complex.ofReal_re] at hre
    linarith only [hre, (hq i).1, (hq j).1]
  refine ⟨γ, q, hrinj, hq, ?_⟩
  intro Q t
  let f : XiZeroCopy → ℝ := fun p =>
    (‖xiPolynomialGaussianHeatTerm Q t p‖ + (xiPolynomialGaussianHeatTerm Q t p).re) / 2
  have hpair (i : Fin N) : f (xiZeroCopyConjEquiv (q i)) = f (q i) := by
    have hpartner : xiSpectralPoint (xiZeroCopyConjEquiv (q i)) = ((-γ i : ℝ) : ℂ) := by
      rw [xiSpectralPoint_copyConj, (hq i).2, Complex.conj_ofReal, Complex.ofReal_neg]
    dsimp only [f]
    rw [xiGaussianRealChannel_atom_at_real Q t (-γ i) ⟨_, hpartner⟩,
      xiGaussianRealChannel_atom_at_real Q t (γ i) ⟨q i, (hq i).2⟩, neg_sq]
  have h := (summable_xiGaussianRealChannel_atom Q t).sum_le_tsum (S ∪ T)
    (fun p _ => xiGaussianRealChannel_atom_nonneg Q t p)
  change (∑ p ∈ S ∪ T, f p) ≤ xiGaussianRealChannelEnergy Q t at h
  rw [Finset.sum_union hdisj] at h
  dsimp only [S, T] at h
  rw [Finset.sum_image (fun i _ j _ hij => hqinj hij),
    Finset.sum_image (fun i _ j _ hij => hCinj hij)] at h
  simp only [hpair, f, xiGaussianRealChannel_atom_at_real Q t (γ _) ⟨q _, (hq _).2⟩] at h
  linarith only [h]

end RHTower
