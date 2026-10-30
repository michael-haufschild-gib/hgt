import GaloisForLFunctions.CompletedArithmeticForms.GammaSuccessorReserve
import GaloisForLFunctions.CompletedArithmeticForms.SignedParityTransfer
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllRankNativeTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomScaleSevenProfiles
import GaloisForLFunctions.HTGeometry.SampledSmallComplex
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay

/-!
# The first theta atom has a strict rank boundary at every center

The entire reflected first atom becomes periodic on the imaginary axis. Nonnegative
signed jets would force this periodic profile to be nondecreasing, contradicting its
explicit values at a half period and a full period. Every fixed shifted Hankel head
nevertheless becomes positive on its own cofinal ray. The complete theta remainder
cannot be discarded in a claim uniform over all orders at one source center.
-/

noncomputable section

open Finset Filter Topology Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Entire continuation of the literal reflected first theta atom. -/
def firstAtomComplexPair (x : ℝ) (z : ℂ) : ℂ :=
  let q := thetaCuspSingleAtomReflectionScale 1 x
  ((4 * q ^ 2 * Real.exp (x - 2 * q) : ℝ) : ℂ) *
    Complex.exp (-2 * (q : ℂ) * (Complex.cosh (2 * z) - 1)) *
      (((2 * q - 3) ^ 2 : ℝ) - 12 * (q : ℂ) * (Complex.cosh (2 * z) - 1))

theorem firstAtomComplexPair_entire (x : ℝ) :
    Differentiable ℂ (firstAtomComplexPair x) := by
  unfold firstAtomComplexPair
  fun_prop

theorem firstAtomComplexPair_ofReal (x t : ℝ) :
    firstAtomComplexPair x (t : ℂ) =
      ((thetaCuspSourceTerm (x + t) 1 * thetaCuspSourceTerm (x - t) 1 : ℝ) : ℂ) := by
  rw [ThetaCuspOddFour.firstAtomPair_eq_affine]
  simp only [firstAtomComplexPair, ThetaCuspOddFour.affine, ThetaCuspOddFour.gaussian,
    ThetaCuspOddFour.factor, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow,
    Complex.ofReal_exp, Complex.ofReal_cosh, Complex.ofReal_ofNat, Complex.ofReal_neg,
    Complex.ofReal_one]
  ring

theorem firstAtomComplexPair_jet (x : ℝ) (n : ℕ) :
    iteratedDeriv n (firstAtomComplexPair x) 0 = (thetaCuspFirstAtomReflectionJet n x : ℂ) := by
  have h := congrFun (_root_.HTGeometry.iteratedDeriv_comp_ofReal n
    (firstAtomComplexPair_entire x)) 0
  have he : (fun t : ℝ => firstAtomComplexPair x (t : ℂ)) =
      fun t : ℝ => ((thetaCuspSourceTerm (x + t) 1 * thetaCuspSourceTerm (x - t) 1 : ℝ) : ℂ) :=
    funext (firstAtomComplexPair_ofReal x)
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => thetaCuspSourceTerm (x + t) 1 * thetaCuspSourceTerm (x - t) 1) := by
    have hf := funext (ThetaCuspOddFour.firstAtomPair_eq_affine x)
    rw [hf]
    dsimp [ThetaCuspOddFour.affine, ThetaCuspOddFour.gaussian, ThetaCuspOddFour.factor]
    fun_prop
  rw [he, GaloisForLFunctions.iteratedDeriv_ofReal_comp hs n] at h
  exact h.symm

/-- Imaginary-axis rotation whose even Taylor jets are the signed source moments. -/
def firstAtomRotatedPair (x : ℝ) (z : ℂ) : ℂ :=
  firstAtomComplexPair x (Complex.I * z)

theorem firstAtomRotatedPair_entire (x : ℝ) :
    Differentiable ℂ (firstAtomRotatedPair x) :=
  (firstAtomComplexPair_entire x).comp ((differentiable_const Complex.I).mul differentiable_id)

theorem firstAtomRotatedPair_jet (x : ℝ) (n : ℕ) :
    iteratedDeriv n (firstAtomRotatedPair x) 0 =
      Complex.I ^ n * (thetaCuspFirstAtomReflectionJet n x : ℂ) := by
  have hc : ContDiff ℂ n (firstAtomComplexPair x) := (firstAtomComplexPair_entire x).contDiff
  change iteratedDeriv n (fun z : ℂ => firstAtomComplexPair x (Complex.I * z)) 0 = _
  rw [iteratedDeriv_comp_const_mul hc Complex.I]
  simp only [mul_zero, firstAtomComplexPair_jet]

theorem firstAtomRotatedPair_ofReal (x y : ℝ) :
    firstAtomRotatedPair x (y : ℂ) =
      let q := thetaCuspSingleAtomReflectionScale 1 x
      ((4 * q ^ 2 * Real.exp (x - 2 * q) *
        Real.exp (-2 * q * (Real.cos (2 * y) - 1)) *
          ((2 * q - 3) ^ 2 - 12 * q * (Real.cos (2 * y) - 1)) : ℝ) : ℂ) := by
  have hcos : Complex.cosh (2 * (Complex.I * (y : ℂ))) = (Real.cos (2 * y) : ℂ) := by
    rw [show (2 : ℂ) * (Complex.I * (y : ℂ)) = ((2 * y : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.cosh_mul_I, Complex.ofReal_cos]
  simp only [firstAtomRotatedPair, firstAtomComplexPair, hcos,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_exp,
    Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_one]

private theorem entire_re_monotone_of_nonneg_jets {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hn : ∀ n : ℕ, 0 ≤ (iteratedDeriv n g 0).re)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : (g u).re ≤ (g v).re := by
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_of_entire hg 0 (u : ℂ))
  have ht := Complex.hasSum_re (Complex.hasSum_taylorSeries_of_entire hg 0 (v : ℂ))
  refine hasSum_le (fun n => ?_) hs ht
  have he (y : ℝ) :
      ((n.factorial : ℂ)⁻¹ • ((y : ℂ) - 0) ^ n • iteratedDeriv n g 0).re =
        (n.factorial : ℝ)⁻¹ * y ^ n * (iteratedDeriv n g 0).re := by
    simp only [smul_eq_mul, sub_zero, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  rw [he, he]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv n) (by positivity)) (hn n)

/-- At every center, an actual first-atom signed reflection moment is strictly negative. -/
theorem exists_firstAtom_signed_moment_neg (x : ℝ) :
    ∃ k : ℕ, (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x < 0 := by
  by_contra h
  have hm (k : ℕ) : 0 ≤ (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x :=
    le_of_not_gt (fun hk => h ⟨k, hk⟩)
  have hn (n : ℕ) : 0 ≤ (iteratedDeriv n (firstAtomRotatedPair x) 0).re := by
    rw [firstAtomRotatedPair_jet]
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨k, hk⟩ := he
      have hI : Complex.I ^ (2 * k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
        rw [pow_mul, Complex.I_sq]
        norm_cast
      rw [show n = 2 * k by omega, hI, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact hm k
    · rw [thetaCuspFirstAtomReflectionJet_odd_zero ho, Complex.ofReal_zero, mul_zero,
        Complex.zero_re]
  have hg := firstAtomRotatedPair_entire x
  have hmono := entire_re_monotone_of_nonneg_jets hg hn
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    (show Real.pi / 2 ≤ Real.pi by linarith only [Real.pi_pos])
  rw [firstAtomRotatedPair_ofReal, firstAtomRotatedPair_ofReal] at hmono
  simp only [show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi, Real.cos_two_pi,
    Complex.ofReal_re] at hmono
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let C := 4 * q ^ 2 * Real.exp (x - 2 * q)
  have hq : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hexp : 1 ≤ Real.exp (4 * q) := Real.one_le_exp (by positivity)
  have hB : 0 ≤ (2 * q - 3) ^ 2 := sq_nonneg _
  have hgt : (2 * q - 3) ^ 2 < Real.exp (4 * q) * ((2 * q - 3) ^ 2 + 24 * q) := by
    calc
      _ < (2 * q - 3) ^ 2 + 24 * q := by linarith only [hq]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hexp
  have he : -2 * q * (-1 - 1) = 4 * q := by ring
  change C * Real.exp (-2 * q * (-1 - 1)) *
      ((2 * q - 3) ^ 2 - 12 * q * (-1 - 1)) ≤
    C * Real.exp (-2 * q * (1 - 1)) * ((2 * q - 3) ^ 2 - 12 * q * (1 - 1)) at hmono
  rw [he] at hmono
  norm_num only [sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero] at hmono
  have hstrict := mul_lt_mul_of_pos_left hgt hC
  nlinarith only [hmono, hstrict]

/-- There is no common source ray on which all first-atom signed moments are nonnegative. -/
theorem not_firstAtom_all_order_positive_ray :
    ¬ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ k : ℕ,
      0 ≤ (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x := by
  rintro ⟨X, hX⟩
  obtain ⟨k, hk⟩ := exists_firstAtom_signed_moment_neg X
  exact not_lt_of_ge (hX X le_rfl k) hk

/-- Fourier-signed jets of the literal reflected first atom, with its exact odd zeros. -/
def firstAtomSignedSequence (x : ℝ) (n : ℕ) : ℝ :=
  if Even n then (-1 : ℝ) ^ (n / 2) * thetaCuspFirstAtomReflectionJet n x else 0

/-- Every first-atom center has a finite signed Hankel section with a negative diagonal. -/
theorem exists_firstAtom_signed_head_not_posSemidef (x : ℝ) :
    ∃ N : ℕ, ¬ (finiteHankelMatrix (firstAtomSignedSequence x) N).PosSemidef := by
  obtain ⟨k, hk⟩ := exists_firstAtom_signed_moment_neg x
  refine ⟨k + 1, ?_⟩
  intro hA
  have hd := hA.diag_nonneg (i := (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)))
  change 0 ≤ firstAtomSignedSequence x (k + k) at hd
  have he : Even (k + k) := ⟨k, rfl⟩
  rw [firstAtomSignedSequence, if_pos he, show (k + k) / 2 = k by omega,
    show k + k = 2 * k by omega] at hd
  exact not_lt_of_ge hd hk

/-- First-atom signed moments in the actual Gaussian source coordinates. -/
def firstAtomBalancedMoment (s : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  thetaCuspFirstAtomScaledEvenJet (k + s) x

private theorem firstAtom_model_shift (s k : ℕ) :
    gaussianMoment (k + s) =
      scaledGammaMoment (gaussianMoment s) 16 ((s : ℝ) + 1 / 2) k := by
  rw [Nat.add_comm k s]
  simp only [gaussianMoment, scaledGammaMoment, pow_add, gammaShapeMoment_add]
  rw [add_comm (1 / 2 : ℝ) (s : ℝ)]
  ring

/-- Every fixed shifted head of the first atom is strictly positive on a rank-dependent ray. -/
theorem firstAtomBalancedHead_posDef_eventually (N s : ℕ) :
    ∀ᶠ x : ℝ in atTop, (finiteHankelMatrix (firstAtomBalancedMoment s x) N).PosDef := by
  have hg : 0 < gaussianMoment s :=
    mul_pos (pow_pos (by positivity) s) (gammaShapeMoment_pos (by positivity) s)
  have hh (x : ℝ) : (finiteHankelMatrix (firstAtomBalancedMoment s x) N).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [finiteHankelMatrix, add_comm]
  apply posDef_eventually_of_tendsto
    (scaledGammaHankel_posDef hg (show (0 : ℝ) < 16 by positivity)
      (show (0 : ℝ) < (s : ℝ) + 1 / 2 by positivity) N)
    (Filter.Eventually.of_forall hh)
  intro i j
  simpa only [firstAtomBalancedMoment, finiteHankelMatrix, thetaCuspFirstAtomScaledEvenJet,
    profile_signed_even_jet, firstAtom_model_shift] using
    firstAtom_scaled_jet_tendsto (i.val + j.val + s)

/-- Each fixed raw signed moment is eventually strictly positive in the literal source mass. -/
theorem firstAtom_signed_moment_eventually_pos (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 < (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x := by
  have hg : 0 < gaussianMoment k :=
    mul_pos (pow_pos (by positivity) k) (gammaShapeMoment_pos (by positivity) k)
  have hlim : Tendsto (thetaCuspFirstAtomScaledEvenJet k) atTop (𝓝 (gaussianMoment k)) := by
    change Tendsto (fun x : ℝ => thetaCuspFirstAtomScaledEvenJet k x)
      atTop (𝓝 (gaussianMoment k))
    simpa only [thetaCuspFirstAtomScaledEvenJet, profile_signed_even_jet] using
      firstAtom_scaled_jet_tendsto k
  filter_upwards [hlim.eventually (lt_mem_nhds hg), eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (show 0 < (1 : ℕ) by omega)
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hd : 0 < thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ k :=
    mul_pos (pow_pos hf 2) (pow_pos hq k)
  change 0 < (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x /
    (thetaCuspSourceTerm x 1 ^ 2 * thetaCuspSingleAtomReflectionScale 1 x ^ k) at hx
  have h := mul_pos hx hd
  rwa [div_mul_cancel₀ _ hd.ne'] at h

/-- Least order of a negative signed first-atom moment at the specified source center. -/
def firstAtomNegativeOrder (x : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_firstAtom_signed_moment_neg x)

theorem firstAtomNegativeOrder_spec (x : ℝ) :
    (-1 : ℝ) ^ firstAtomNegativeOrder x *
      thetaCuspFirstAtomReflectionJet (2 * firstAtomNegativeOrder x) x < 0 := by
  classical
  exact Nat.find_spec (exists_firstAtom_signed_moment_neg x)

theorem firstAtom_signed_moment_nonneg_before_negativeOrder (x : ℝ) {k : ℕ}
    (hk : k < firstAtomNegativeOrder x) :
    0 ≤ (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x := by
  classical
  exact le_of_not_gt (Nat.find_min (exists_firstAtom_signed_moment_neg x) hk)

/-- Every fixed finite order lies below the first negative signed moment on a cofinal ray. -/
theorem firstAtomNegativeOrder_eventually_gt (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, K < firstAtomNegativeOrder x := by
  have hsmall : ∀ᶠ x : ℝ in atTop, ∀ i : Fin (K + 1),
      0 < (-1 : ℝ) ^ i.val * thetaCuspFirstAtomReflectionJet (2 * i.val) x := by
    rw [Filter.eventually_all]
    intro i
    exact firstAtom_signed_moment_eventually_pos i.val
  filter_upwards [hsmall] with x hx
  by_contra h
  have hle : firstAtomNegativeOrder x ≤ K := le_of_not_gt h
  have hp := hx (⟨firstAtomNegativeOrder x, by omega⟩ : Fin (K + 1))
  exact not_lt_of_ge hp.le (firstAtomNegativeOrder_spec x)

/-- The obstruction rank is finite at every center and escapes to infinity along the source tail. -/
theorem firstAtomNegativeOrder_tendsto : Tendsto firstAtomNegativeOrder atTop atTop := by
  refine tendsto_atTop.mpr fun K => ?_
  filter_upwards [firstAtomNegativeOrder_eventually_gt K] with x hx
  exact hx.le

/-- The balanced shifted first-atom form transfers to the exact unnormalized source by congruence. -/
theorem firstAtomShiftedHead_posDef_eventually (N s : ℕ) :
    ∀ᶠ x : ℝ in atTop, (finiteHankelMatrix
      (fun k => (-1 : ℝ) ^ (k + s) * thetaCuspFirstAtomReflectionJet (2 * (k + s)) x)
      N).PosDef := by
  filter_upwards [firstAtomBalancedHead_posDef_eventually N s,
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let D : Matrix (Fin N) (Fin N) ℝ := diagonal (fun i => f * q ^ i.val)
  have hqp : 0 < q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have hq := hqp.ne'
  have hf : f ≠ 0 :=
    (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)).ne'
  have hD : Function.Injective D.mulVec := by
    intro v w h
    funext i
    have hi := congrFun h i
    simp only [D, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (mul_ne_zero hf (pow_ne_zero _ hq)) hi
  have he : finiteHankelMatrix
      (fun k => (-1 : ℝ) ^ (k + s) * thetaCuspFirstAtomReflectionJet (2 * (k + s)) x) N =
      q ^ s • (Dᴴ * finiteHankelMatrix (firstAtomBalancedMoment s x) N * D) := by
    ext i j
    simp only [D, diagonal_conjTranspose, star_trivial, diagonal_mul, mul_diagonal,
      Matrix.smul_apply, smul_eq_mul, finiteHankelMatrix, firstAtomBalancedMoment,
      thetaCuspFirstAtomScaledEvenJet]
    change _ = q ^ s * (f * q ^ i.val *
      (_ / (f ^ (2 : ℕ) * q ^ (i.val + j.val + s))) * (f * q ^ j.val))
    rw [pow_add, pow_add]
    field_simp [hf, hq]
    ring
  rw [he]
  exact (hx.conjTranspose_mul_mul_same hD).smul (pow_pos hqp s)

theorem firstAtomSignedSequence_eq_evenMomentSequence (x : ℝ) :
    firstAtomSignedSequence x = evenMomentSequence
      (fun k => (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x) := by
  funext n
  by_cases hn : Even n
  · simp only [firstAtomSignedSequence, evenMomentSequence, if_pos hn]
    rw [show 2 * (n / 2) = n by obtain ⟨k, hk⟩ := hn; omega]
  · simp only [firstAtomSignedSequence, evenMomentSequence, if_neg hn]

/-- Every fixed full signed first-atom head is strictly positive on its own cofinal ray. -/
theorem firstAtomSignedHead_posDef_eventually (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, (finiteHankelMatrix (firstAtomSignedSequence x) N).PosDef := by
  filter_upwards [firstAtomShiftedHead_posDef_eventually ((N + 1) / 2) 0,
    firstAtomShiftedHead_posDef_eventually (N / 2) 1] with x he ho
  rw [firstAtomSignedSequence_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨he, ho⟩

/-- Least full signed Hankel dimension at which the literal first atom loses semidefiniteness. -/
def firstAtomFailureRank (x : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_firstAtom_signed_head_not_posSemidef x)

theorem firstAtomFailureRank_spec (x : ℝ) :
    ¬ (finiteHankelMatrix (firstAtomSignedSequence x) (firstAtomFailureRank x)).PosSemidef := by
  classical
  exact Nat.find_spec (exists_firstAtom_signed_head_not_posSemidef x)

/-- Every smaller full head remains in the closed positive cone at that same center. -/
theorem firstAtomSignedHead_posSemidef_below_failureRank (x : ℝ) {N : ℕ}
    (hN : N < firstAtomFailureRank x) :
    (finiteHankelMatrix (firstAtomSignedSequence x) N).PosSemidef := by
  classical
  exact not_not.mp (Nat.find_min (exists_firstAtom_signed_head_not_posSemidef x) hN)

/-- The negative diagonal bounds the first mixed-form failure from above. -/
theorem firstAtomFailureRank_le_negativeOrder_succ (x : ℝ) :
    firstAtomFailureRank x ≤ firstAtomNegativeOrder x + 1 := by
  classical
  apply Nat.find_min' (exists_firstAtom_signed_head_not_posSemidef x)
  intro hA
  have hd := hA.diag_nonneg
    (i := (⟨firstAtomNegativeOrder x, Nat.lt_succ_self _⟩ : Fin (firstAtomNegativeOrder x + 1)))
  change 0 ≤ firstAtomSignedSequence x (firstAtomNegativeOrder x + firstAtomNegativeOrder x) at hd
  rw [firstAtomSignedSequence_eq_evenMomentSequence,
    show firstAtomNegativeOrder x + firstAtomNegativeOrder x = 2 * firstAtomNegativeOrder x by omega,
    evenMomentSequence_even] at hd
  exact not_lt_of_ge hd (firstAtomNegativeOrder_spec x)

/-- No bounded rank detects the first-atom failure throughout a cofinal source ray. -/
theorem firstAtomFailureRank_eventually_gt (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, K < firstAtomFailureRank x := by
  have hsmall : ∀ᶠ x : ℝ in atTop, ∀ i : Fin (K + 1),
      (finiteHankelMatrix (firstAtomSignedSequence x) i.val).PosDef := by
    rw [Filter.eventually_all]
    intro i
    exact firstAtomSignedHead_posDef_eventually i.val
  filter_upwards [hsmall] with x hx
  by_contra h
  have hle : firstAtomFailureRank x ≤ K := le_of_not_gt h
  have hp := hx (⟨firstAtomFailureRank x, by omega⟩ : Fin (K + 1))
  exact firstAtomFailureRank_spec x hp.posSemidef

/-- The least failing full mixed head is finite everywhere and tends to infinity along the tail. -/
theorem firstAtomFailureRank_tendsto : Tendsto firstAtomFailureRank atTop atTop := by
  refine tendsto_atTop.mpr fun K => ?_
  filter_upwards [firstAtomFailureRank_eventually_gt K] with x hx
  exact hx.le

#print axioms exists_firstAtom_signed_moment_neg
#print axioms not_firstAtom_all_order_positive_ray
#print axioms exists_firstAtom_signed_head_not_posSemidef
#print axioms firstAtomBalancedHead_posDef_eventually
#print axioms firstAtomNegativeOrder_spec
#print axioms firstAtomSignedHead_posDef_eventually
#print axioms firstAtomSignedHead_posSemidef_below_failureRank
#print axioms firstAtomFailureRank_le_negativeOrder_succ
#print axioms firstAtomFailureRank_tendsto
#print axioms firstAtomNegativeOrder_tendsto

end GaloisForLFunctions.CompletedArithmeticForms
