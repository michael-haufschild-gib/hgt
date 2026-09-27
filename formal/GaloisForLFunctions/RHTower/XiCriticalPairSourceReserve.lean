import GaloisForLFunctions.RHTower.XiGaussianResidualSourcePhase
import GaloisForLFunctions.RHTower.XiCriticalGaussianMaxNodeFloor

/-!
# The same actual critical nodes fund the energy floor and reduce the source debt

Each selected positive critical node and its distinct Schwarz partner are
charged once. Their exact fourth-trace reserve is twice the sum of inverse
fourth powers. The node family also supplies the independent all-time
coefficient floor, so both estimates use the same actual spectral data.
-/

open scoped Real BigOperators
open Complex
noncomputable section

namespace RHTower

theorem xiFourthTraceCriticalAtom_conj (q : XiZeroCopy) :
    xiFourthTraceCriticalAtom (xiZeroCopyConjEquiv q) = xiFourthTraceCriticalAtom q := by
  simp only [xiFourthTraceCriticalAtom, xiSpectralPoint_copyConj, Complex.neg_im,
    Complex.conj_im, neg_neg, xiFourthReciprocalTraceAtom_conj]

theorem xiFourthTraceCriticalAtom_at_real (x : ℝ)
    (q : {q : XiZeroCopy // xiSpectralPoint q = (x : ℂ)}) :
    xiFourthTraceCriticalAtom q.1 = 1 / x ^ 4 := by
  rw [xiFourthTraceCriticalAtom, q.property]
  simp only [Complex.ofReal_im, ite_true]
  rw [xiZeroCopyReciprocalSquare, q.property]
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re,
    ← pow_mul, inv_pow, one_div]

/-- Every finite positive order admits one actual critical family which simultaneously
supplies the independent energy floor and an exact paired subtraction from the source. -/
theorem exists_xiCriticalPair_floor_and_source_reserve (n : ℕ) :
    ∃ (γ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → XiZeroCopy)
      (iMax : Fin (n + 1)) (c : ℝ) (F : Finset XiZeroCopy),
      0 < c ∧ Function.Injective (fun i => (γ i : ℂ) ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ i, γ i ^ 2 ≤ γ iMax ^ 2) ∧
      xiCriticalFourthTraceReserve F = 2 * ∑ i : Fin (n + 1), 1 / γ i ^ 4 ∧
      xiCriticalFourthTraceResidual F =
        normalizedPrimeArchMoment 1 - 2 * ∑ i : Fin (n + 1), 1 / γ i ^ 4 ∧
      (∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        c * Real.exp (-(γ iMax ^ 2 * (t : ℝ))) *
          (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤
            xiGaussianRealChannelEnergy
              (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t) ∧
      ∀ (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
        (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}),
        (∑' r : XiZeroCopy, xiGaussianImaginaryChannelAtom
          (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t.1 r) ≤
            xiGaussianResidualPhaseBudget F (n + 1) s t.1 *
              (∑ j ∈ Finset.range (n + 1), a j ^ 2) := by
  classical
  obtain ⟨γ, q, iMax, c, hc, hinj, hq, hmax, _, hfloor⟩ :=
    exists_xiGaussianRealChannel_maxNode_floor n
  let S := Finset.univ.image q
  let T := Finset.univ.image (fun i => xiZeroCopyConjEquiv (q i))
  let F := S ∪ T
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hinj
    change (γ i : ℂ) ^ 2 = (γ j : ℂ) ^ 2
    rw [← (hq i).2, ← (hq j).2, hij]
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
  have hreserve : xiCriticalFourthTraceReserve F =
      2 * ∑ i : Fin (n + 1), 1 / γ i ^ 4 := by
    unfold xiCriticalFourthTraceReserve
    change (∑ r ∈ S ∪ T, xiFourthTraceCriticalAtom r) = _
    rw [Finset.sum_union hdisj]
    dsimp only [S, T]
    rw [Finset.sum_image (fun i _ j _ hij => hqinj hij),
      Finset.sum_image (fun i _ j _ hij => hCinj hij)]
    simp only [xiFourthTraceCriticalAtom_conj,
      xiFourthTraceCriticalAtom_at_real (γ _) ⟨q _, (hq _).2⟩]
    ring
  refine ⟨γ, q, iMax, c, F, hc, hinj, hq, hmax, hreserve, ?_, hfloor, ?_⟩
  · rw [xiCriticalFourthTraceResidual, hreserve]
  · intro a s t
    exact xiGaussianImaginaryChannel_le_residual_source F (n + 1) a s t

end RHTower
