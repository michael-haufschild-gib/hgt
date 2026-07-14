import GaloisForLFunctions.HTGeometry.UniversalOrientedHerglotz

/-!
# The atomic Herglotz residue cone

The sign cube is only the set of vertices of a more intrinsic object.  For a finite real Cauchy
divisor attached to the universal positive background, the resulting function has nonnegative
imaginary part on the upper half-plane exactly when every residue coefficient is nonnegative.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The universal positive background with arbitrary real residues on a finite pole set. -/
def universalResidueConeHerglotz (S : Finset ℕ) (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  primeLogHerglotz (fun q => universalFacetOrbitGauge q) z +
    ∑ n ∈ S, (a n : ℂ) * ((orientationPole n : ℂ) - z)⁻¹

theorem residueAtom_im_nonneg {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (((r : ℂ) * ((orientationPole n : ℂ) - z)⁻¹)).im := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  exact mul_nonneg hr (div_nonneg hz.le (Complex.normSq_nonneg _))

theorem universalResidueConeHerglotz_im_nonneg
    (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ n ∈ S, 0 ≤ a n)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (universalResidueConeHerglotz S a z).im := by
  have hbase := universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz
  rw [universalResidueConeHerglotz, Complex.add_im]
  change 0 ≤ _ + Complex.imLm (∑ n ∈ S, _)
  rw [map_sum Complex.imLm]
  exact add_nonneg hbase (Finset.sum_nonneg fun n hn => residueAtom_im_nonneg (ha n hn) hz)

/-- Remove one residue atom to expose a background continuous at its pole. -/
def universalResidueConeRegular
    (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  primeLogHerglotz (fun q => universalFacetOrbitGauge q) z +
    ∑ q ∈ S.erase n, (a q : ℂ) * ((orientationPole q : ℂ) - z)⁻¹

theorem continuousAt_universalResidueConeRegular
    (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) :
    ContinuousAt (universalResidueConeRegular S a n) (orientationPole n : ℂ) := by
  apply ContinuousAt.add (continuousAt_universalPrimeLog_orientationPole n)
  let T := S.erase n
  change ContinuousAt (fun z : ℂ => ∑ q ∈ T,
    (a q : ℂ) * ((orientationPole q : ℂ) - z)⁻¹) _
  have hnT : n ∉ T := by simp [T]
  revert hnT
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty] using
        (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) _)
  | @insert q T hq ih =>
      intro hnInsert
      have hqn : q ≠ n := by
        intro h
        subst q
        exact hnInsert (by simp)
      have hnT : n ∉ T := by
        intro hn
        exact hnInsert (by simp [hn])
      have hterm : ContinuousAt (fun z : ℂ =>
          (a q : ℂ) * ((orientationPole q : ℂ) - z)⁻¹)
          (orientationPole n : ℂ) := by
        apply ContinuousAt.const_mul
        apply ContinuousAt.inv₀ (continuousAt_const.sub continuousAt_id)
        intro heq
        have hpole : orientationPole q = orientationPole n := by
          exact Complex.ofReal_injective (sub_eq_zero.mp heq)
        exact hqn (orientationPole_injective hpole)
      simpa [Finset.sum_insert hq] using hterm.add (ih hnT)

theorem universalResidueConeHerglotz_eq_regular_add_atom
    {S : Finset ℕ} {a : ℕ → ℝ} {n : ℕ} (hnS : n ∈ S) (z : ℂ) :
    universalResidueConeHerglotz S a z =
      universalResidueConeRegular S a n z +
        (a n : ℂ) * ((orientationPole n : ℂ) - z)⁻¹ := by
  rw [universalResidueConeHerglotz, universalResidueConeRegular]
  have hsplit := Finset.sum_erase_add (s := S) (f := fun q =>
    (a q : ℂ) * ((orientationPole q : ℂ) - z)⁻¹) hnS
  rw [← hsplit]
  ring

/-- A strictly negative real residue dominates every continuous background at its real pole. -/
theorem exists_upper_im_neg_of_continuous_add_negativeCoefficientAtom
    (pole r : ℝ) (hr : r < 0) (g : ℂ → ℂ) (hg : ContinuousAt g (pole : ℂ)) :
    ∃ z : ℂ, 0 < z.im ∧
      (g z + (r : ℂ) * ((pole : ℂ) - z)⁻¹).im < 0 := by
  let c : ℝ := -r
  have hc : 0 < c := neg_pos.mpr hr
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  let h : ℂ → ℂ := fun z => (c : ℂ)⁻¹ * g z
  have hh : ContinuousAt h (pole : ℂ) :=
    (continuousAt_const.mul hg)
  obtain ⟨z, hz, hneg⟩ :=
    exists_upper_im_neg_of_continuous_add_negativeAtom pole h hh
  refine ⟨z, hz, ?_⟩
  have hshape :
      g z + (r : ℂ) * ((pole : ℂ) - z)⁻¹ =
        (c : ℂ) * (h z - ((pole : ℂ) - z)⁻¹) := by
    simp only [h]
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    dsimp only [c]
    push_cast
    ring
  rw [hshape, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  exact mul_neg_of_pos_of_neg hc hneg

theorem universalResidueConeHerglotz_not_nonneg_of_negative
    (S : Finset ℕ) (a : ℕ → ℝ) {n : ℕ} (hnS : n ∈ S) (han : a n < 0) :
    ¬ ∀ z : ℂ, 0 < z.im → 0 ≤ (universalResidueConeHerglotz S a z).im := by
  obtain ⟨z, hz, hneg⟩ :=
    exists_upper_im_neg_of_continuous_add_negativeCoefficientAtom
      (orientationPole n) (a n) han (universalResidueConeRegular S a n)
      (continuousAt_universalResidueConeRegular S a n)
  intro hnonneg
  have h := hnonneg z hz
  rw [universalResidueConeHerglotz_eq_regular_add_atom hnS z] at h
  exact (not_lt_of_ge h) hneg

/-- **Exact finite atomic Herglotz cone.**  The residue vector points into the Herglotz cone if
and only if every active residue is nonnegative. -/
theorem universalResidueConeHerglotz_nonneg_iff
    (S : Finset ℕ) (a : ℕ → ℝ) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalResidueConeHerglotz S a z).im) ↔
      ∀ n ∈ S, 0 ≤ a n := by
  constructor
  · intro h n hn
    by_contra hnonneg
    exact universalResidueConeHerglotz_not_nonneg_of_negative S a hn
      (lt_of_not_ge hnonneg) h
  · intro ha z hz
    exact universalResidueConeHerglotz_im_nonneg S a ha hz

end

end GaloisForLFunctions.HTGeometry
