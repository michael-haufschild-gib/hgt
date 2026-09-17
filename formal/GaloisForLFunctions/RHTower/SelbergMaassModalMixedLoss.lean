import GaloisForLFunctions.RHTower.SelbergMaassKernelWronskian

/-!
# Same-residue modal form of the unresolved Maass phase stress

The mixed source loss which occurs in the Selberg quarter boundary term has an exact
finite modal form.  A horizontal mode contributes its literal imaginary frequency,
a height mode contributes its literal coefficient derivative, and the finite
arithmetic transfer annihilates all pairs in distinct upper-residue channels.

This leaves only the signed same-residue coefficient interaction.  No positivity,
spectral estimate, or boundary sign is introduced here.
-/

open Complex Set UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassModalMixedLoss
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionGram
open SelbergMaassUnipotentFourier SelbergMaassCharacterGradient SelbergMaassFourier
open SelbergMaassPhaseStress SelbergMaassMixedLoss SelbergMaassSliceRigidity
open SelbergMaassKernelWronskian
open GaloisForLFunctions.HTGeometry
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

variable (N : ℕ) (r s : ZMod (N + 1))

/-- Sesquilinearity of the actual complex loss for two independent finite source sums. -/
private theorem complexLoss_bisum {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ)
    (v : ι → EuclideanSpace ℂ (Deck N))
    (w : κ → EuclideanSpace ℂ (Deck N)) :
    complexLoss N r s (∑ i ∈ I, a i • v i) (∑ j ∈ J, b j • w j) =
      ∑ i ∈ I, ∑ j ∈ J,
        (starRingEnd ℂ) (a i) * b j * complexLoss N r s (v i) (w j) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [complexLoss, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum, mul_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Mixed loss between one literal source coefficient and one literal height coefficient. -/
def coefficientMixedLoss (n m : ℤ) (y : ℝ) : ℂ :=
  complexLoss N r s (coefficientVector N f n y) (coefficientHeightVector N f m y)

/-- A height coefficient lies in exactly its original upper residue channel. -/
theorem upperProjection_coefficientHeightVector (t : ZMod (N + 1)) (m : ℤ)
    {y : ℝ} (hy : 0 < y) :
    characterProjection N (upperBlock N) t (coefficientHeightVector N f m y) =
      if (m : ZMod (N + 1)) = t then coefficientHeightVector N f m y else 0 := by
  calc
    characterProjection N (upperBlock N) t (coefficientHeightVector N f m y) =
        characterProjection N (upperBlock N) t
          (characterProjection N (upperBlock N) (m : ZMod (N + 1))
            (coefficientHeightVector N f m y)) := by
          rw [coefficientHeight_upperProjection N f m hy]
    _ = if t = (m : ZMod (N + 1)) then
          characterProjection N (upperBlock N) (m : ZMod (N + 1))
            (coefficientHeightVector N f m y) else 0 :=
      characterProjection_pair N (upperBlock N) t (m : ZMod (N + 1)) _
    _ = _ := by
      rw [coefficientHeight_upperProjection N f m hy]
      by_cases h : t = (m : ZMod (N + 1))
      · simp [h]
      · simp [h, Ne.symm h]

/-- Mixed source loss vanishes across distinct literal upper-residue channels. -/
theorem coefficientMixedLoss_eq_zero_of_residue_ne (n m : ℤ)
    (hnm : (n : ZMod (N + 1)) ≠ (m : ZMod (N + 1)))
    {y : ℝ} (hy : 0 < y) :
    coefficientMixedLoss N r s f n m y = 0 := by
  have hfix (k : ℤ) :
      characterProjection N (upperBlock N) (k : ZMod (N + 1))
        (coefficientVector N f k y) = coefficientVector N f k y := by
    rw [upperProjection_coefficientVector N f (k : ZMod (N + 1)) k hy, if_pos rfl]
  have hfixHeight (k : ℤ) :
      characterProjection N (upperBlock N) (k : ZMod (N + 1))
        (coefficientHeightVector N f k y) = coefficientHeightVector N f k y := by
    rw [upperProjection_coefficientHeightVector N f (k : ZMod (N + 1)) k hy, if_pos rfl]
  have hi := characterProjection_inner_eq_zero N (upperBlock N)
    (n : ZMod (N + 1)) (m : ZMod (N + 1)) hnm
    (coefficientVector N f n y) (coefficientHeightVector N f m y)
  rw [hfix n, hfixHeight m] at hi
  unfold coefficientMixedLoss complexLoss inversionTransfer
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hi,
    upperProjection_coefficientVector N f s n hy,
    upperProjection_coefficientHeightVector N f s m hy]
  by_cases hn : (n : ZMod (N + 1)) = s
  · have hm : (m : ZMod (N + 1)) ≠ s := fun h => hnm (hn.trans h.symm)
    simp only [if_neg hm, map_zero, inner_zero_right, sub_zero]
  · simp only [if_neg hn, map_zero, inner_zero_left, sub_zero]

private theorem complexLoss_hasDerivAt {u v : ℝ → EuclideanSpace ℂ (Deck N)}
    {u' v' : EuclideanSpace ℂ (Deck N)} {y : ℝ}
    (hu : HasDerivAt u u' y) (hv : HasDerivAt v v' y) :
    HasDerivAt (fun t => complexLoss N r s (u t) (v t))
      (complexLoss N r s (u y) v' + complexLoss N r s u' (v y)) y := by
  let T := (inversionTransfer N r s).toContinuousLinearMap.restrictScalars ℝ
  have h := (hu.inner ℂ hv).sub
    ((T.hasFDerivAt.comp_hasDerivAt y hu).inner ℂ
      (T.hasFDerivAt.comp_hasDerivAt y hv))
  convert h using 1 <;> try rfl
  simp only [complexLoss]
  dsimp [T]
  ring

/-- The height derivative of the Hermitian coefficient loss is the sum of its two mixed slots. -/
theorem coefficientLoss_hasDerivAt_mixed (n m : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (coefficientLoss N r s f n m)
      ((starRingEnd ℂ) (coefficientMixedLoss N r s f m n y) +
        coefficientMixedLoss N r s f n m y) y := by
  have hn := coefficientVector_hasDerivAt N f n hy
  have hm := coefficientVector_hasDerivAt N f m hy
  have h := complexLoss_hasDerivAt N r s hn hm
  have hexchange :
      (starRingEnd ℂ) (coefficientMixedLoss N r s f m n y) =
        complexLoss N r s (coefficientHeightVector N f n y)
          (coefficientVector N f m y) := by
    unfold coefficientMixedLoss
    exact complexLoss_conj N r s _ _
  change HasDerivAt
    (fun t => complexLoss N r s (coefficientVector N f n t) (coefficientVector N f m t)) _ y
  rw [hexchange]
  simpa only [coefficientMixedLoss, add_comm] using h

/-- Each signed mixed coefficient is exactly the symmetric loss derivative minus its Wronskian
current.  This separates the unclosed symmetric term from the already-controlled tail current. -/
theorem two_coefficientMixedLoss_eq_deriv_sub_wronskian (n m : ℤ) {y : ℝ} (hy : 0 < y) :
    2 * coefficientMixedLoss N r s f n m y =
      deriv (coefficientLoss N r s f n m) y - coefficientWronskian N r s f n m y := by
  rw [(coefficientLoss_hasDerivAt_mixed N r s f n m hy).deriv]
  unfold coefficientMixedLoss coefficientWronskian
  rw [← complexLoss_conj N r s (coefficientVector N f m y)
    (coefficientHeightVector N f n y)]
  ring

/-- Pairing the two index orders isolates the two possible signed sources in the real horizontal
modal loss: the imaginary loss derivative and the imaginary Wronskian current. -/
theorem real_weighted_pair_decomposition (n m : ℤ) {y : ℝ} (hy : 0 < y) :
    ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
        coefficientMixedLoss N r s f n m y +
      (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) m : ℝ) : ℂ) * Complex.I) *
        coefficientMixedLoss N r s f m n y).re =
      (1 / 2 : ℝ) *
        (((signedFrequency (N + 1 : ℕ) n : ℝ) - (signedFrequency (N + 1 : ℕ) m : ℝ)) *
            (deriv (coefficientLoss N r s f n m) y).im -
          ((signedFrequency (N + 1 : ℕ) n : ℝ) + (signedFrequency (N + 1 : ℕ) m : ℝ)) *
            (coefficientWronskian N r s f n m y).im) := by
  have hderiv := (coefficientLoss_hasDerivAt_mixed N r s f n m hy).deriv
  have hcurrent :
      coefficientWronskian N r s f n m y =
        (starRingEnd ℂ) (coefficientMixedLoss N r s f m n y) -
          coefficientMixedLoss N r s f n m y := by
    unfold coefficientWronskian coefficientMixedLoss
    rw [← complexLoss_conj N r s (coefficientVector N f m y)
      (coefficientHeightVector N f n y)]
  rw [hderiv, hcurrent]
  simp [Complex.mul_re, Complex.add_re]
  ring

/-- In the exceptional cusp range, every diagonal modal contribution to the real horizontal loss
vanishes.  The remaining signed modal problem is therefore strictly off-diagonal. -/
theorem real_weighted_diagonal_mixed_eq_zero
    (e : Ioo (0 : ℝ) (1 / 4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (e : ℝ))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
      coefficientMixedLoss N r s g n n y).re = 0 := by
  have hpair := real_weighted_pair_decomposition N r s g n n hy
  rw [coefficientWronskian_self_eq_zero N r s e g n hy] at hpair
  simp only [Complex.add_re, Complex.zero_im, mul_zero, sub_self, zero_mul] at hpair
  linarith

/-- Finite literal horizontal source derivative reconstructed from modal coefficients. -/
def finiteModalHorizontal (I : Finset ℤ) (y : ℝ) : EuclideanSpace ℂ (Deck N) :=
  ∑ n ∈ I, (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) •
    coefficientVector N f n y

/-- Finite literal vertical source derivative reconstructed from modal coefficients. -/
def finiteModalVertical (I : Finset ℤ) (y : ℝ) : EuclideanSpace ℂ (Deck N) :=
  ∑ n ∈ I, coefficientHeightVector N f n y

/-- The finite mixed modal loss retains exactly the same-residue coefficient interactions. -/
theorem finiteModal_mixedLoss_sameResidue (I J : Finset ℤ) (y : ℝ) (hy : 0 < y) :
    complexLoss N r s (finiteModalHorizontal N f I y) (finiteModalVertical N f J y) =
      ∑ n ∈ I, ∑ m ∈ J,
        if (n : ZMod (N + 1)) = (m : ZMod (N + 1)) then
          (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
            coefficientMixedLoss N r s f n m y
        else 0 := by
  calc
    _ = ∑ n ∈ I, ∑ m ∈ J,
        (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
          coefficientMixedLoss N r s f n m y := by
      simpa only [finiteModalHorizontal, finiteModalVertical, one_smul, one_mul, mul_one,
        coefficientMixedLoss] using
        (complexLoss_bisum (N := N) (r := r) (s := s) I J
          (fun n => (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I))
          (fun _ => (1 : ℂ))
          (fun n => coefficientVector N f n y)
          (fun m => coefficientHeightVector N f m y))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      by_cases hnm : (n : ZMod (N + 1)) = (m : ZMod (N + 1))
      · simp only [if_pos hnm]
      · rw [coefficientMixedLoss_eq_zero_of_residue_ne N r s f n m hnm hy]
        simp only [if_neg hnm, mul_zero]

/-- Twice the finite mixed modal loss splits into the unresolved Hermitian-loss derivative and the
known Wronskian current, with no cross-residue contribution. -/
theorem two_finiteModal_mixedLoss_deriv_sub_wronskian (I J : Finset ℤ)
    (y : ℝ) (hy : 0 < y) :
    2 * complexLoss N r s (finiteModalHorizontal N f I y) (finiteModalVertical N f J y) =
      ∑ n ∈ I, ∑ m ∈ J,
        if (n : ZMod (N + 1)) = (m : ZMod (N + 1)) then
          (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
            (deriv (coefficientLoss N r s f n m) y - coefficientWronskian N r s f n m y)
        else 0 := by
  rw [finiteModal_mixedLoss_sameResidue N r s f I J y hy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hnm : (n : ZMod (N + 1)) = (m : ZMod (N + 1))
  · simp only [if_pos hnm]
    calc
      2 * ((starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
          coefficientMixedLoss N r s f n m y) =
          (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
            (2 * coefficientMixedLoss N r s f n m y) := by ring
      _ = _ := by rw [two_coefficientMixedLoss_eq_deriv_sub_wronskian N r s f n m hy]
  · simp [hnm]

/-- The real mixed source loss of finite modal derivatives is the explicit signed same-residue sum. -/
theorem finiteModal_lossPair_sameResidue (I J : Finset ℤ) (y : ℝ) (hy : 0 < y) :
    lossPair N r s (finiteModalHorizontal N f I y) (finiteModalVertical N f J y) =
      (∑ n ∈ I, ∑ m ∈ J,
        if (n : ZMod (N + 1)) = (m : ZMod (N + 1)) then
          (starRingEnd ℂ) (((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) * Complex.I) *
            coefficientMixedLoss N r s f n m y
        else 0).re := by
  rw [← complexLoss_re, finiteModal_mixedLoss_sameResidue N r s f I J y hy]

end
end GaloisForLFunctions.RHTower.SelbergMaassModalMixedLoss
