import GaloisForLFunctions.HTGeometry.MovingCanonicalSurgeryFieldInvariance
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalProduct

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology Filter Matrix
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped ComplexConjugate ComplexOrder BigOperators

noncomputable section

/-- Even complement carrier after deleting the selected positive and
negative real-zero pairs. -/
def movingEvenCanonicalComplementCarrier
    (θ : BoundedRealSequence) (S : Finset ℕ)
    (z : ℂ) : ℂ :=
  movingCanonicalComplementCarrier θ S z -
    movingCanonicalComplementCarrier θ S (-z)

theorem movingCanonicalComplementCarrier_conj
    (θ : BoundedRealSequence) (S : Finset ℕ)
    (z : ℂ) :
    movingCanonicalComplementCarrier θ S (star z) =
      star (movingCanonicalComplementCarrier θ S z) := by
  let f : {n // n ∉ S} → ℂ := fun n =>
    movingCanonicalRegularizedAtom θ n.1 z
  let g : {n // n ∉ S} → ℂ := fun n =>
    movingCanonicalRegularizedAtom θ n.1 (star z)
  have hgf : g = fun n => star (f n) := by
    funext n
    simp [f, g, movingCanonicalRegularizedAtom]
  rw [movingCanonicalComplementCarrier,
    movingCanonicalComplementCarrier]
  change ∑' n, g n = star (∑' n, f n)
  rw [hgf]
  exact (Complex.conjCLE.map_tsum).symm

theorem carrierPickMatrix_neg_comp_neg_eq_transpose
    (f : ℂ → ℂ)
    (hreal : ∀ z, f (star z) = star (f z))
    {N : ℕ} (z : Fin N → ℂ) :
    carrierPickMatrix (fun w => -f (-w)) z =
      (carrierPickMatrix f
        (fun j => -star (z j)))ᵀ := by
  ext i j
  rw [carrierPickMatrix, carrierPickMatrix]
  simp only [Matrix.of_apply, transpose_apply,
    star_neg]
  have hj :
      f (-star (z j)) = star (f (-z j)) := by
    simpa only [star_neg] using hreal (-z j)
  have hi :
      f (-star (z i)) = star (f (-z i)) := by
    simpa only [star_neg] using hreal (-z i)
  rw [hj, hi]
  simp only [star_star]
  ring

theorem movingEvenCanonicalComplementCarrier_pick_posSemidef
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {N : ℕ} (z : Fin N → ℂ)
    (hz : ∀ j, 0 < (z j).im) :
    (carrierPickMatrix
      (movingEvenCanonicalComplementCarrier θ S) z).PosSemidef := by
  let u : Fin N → ℂ := fun j => -star (z j)
  have hu : ∀ j, 0 < (u j).im := by
    intro j
    simp [u]
    exact hz j
  have hpos :=
    movingCanonicalComplementCarrier_pick_posSemidef
      θ S z hz
  have hrefPos :
      (carrierPickMatrix
        (fun w =>
          -movingCanonicalComplementCarrier θ S (-w))
        z).PosSemidef := by
    rw [carrierPickMatrix_neg_comp_neg_eq_transpose
      (movingCanonicalComplementCarrier θ S)
      (movingCanonicalComplementCarrier_conj θ S)]
    exact
      (movingCanonicalComplementCarrier_pick_posSemidef
        θ S u hu).transpose
  rw [show movingEvenCanonicalComplementCarrier θ S =
      fun w =>
        movingCanonicalComplementCarrier θ S w +
          -movingCanonicalComplementCarrier θ S (-w) by
    funext w
    simp [movingEvenCanonicalComplementCarrier,
      sub_eq_add_neg]]
  rw [carrierPickMatrix_add]
  exact hpos.add hrefPos

theorem continuousAt_movingEvenCanonicalComplementCarrier
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {t : ℂ} (ht : 0 < t.im) :
    ContinuousAt
      (movingEvenCanonicalComplementCarrier θ S) t := by
  have hpos :=
    continuousAt_movingCanonicalComplementCarrier θ S ht
  let u : ℂ := -star t
  have hu : 0 < u.im := by
    simp [u]
    exact ht
  have href :=
    continuousAt_movingCanonicalComplementCarrier θ S hu
  have harg :
      ContinuousAt (fun z : ℂ => -star z) t := by
    fun_prop
  have hcomp :
      ContinuousAt
        (fun z =>
          star (movingCanonicalComplementCarrier
            θ S (-star z))) t := by
    change ContinuousAt
      ((starRingEnd ℂ) ∘
        movingCanonicalComplementCarrier θ S ∘
          fun z => -star z) t
    exact Complex.continuous_conj.continuousAt.comp
      (href.comp_of_eq harg rfl)
  have heq :
      (fun z =>
        star (movingCanonicalComplementCarrier
          θ S (-star z))) =
        fun z =>
          movingCanonicalComplementCarrier θ S (-z) := by
    funext z
    have h :=
      movingCanonicalComplementCarrier_conj
        θ S (-star z)
    simpa only [star_neg, star_star] using h.symm
  rw [heq] at hcomp
  exact hpos.sub hcomp

/-- Two upper-half-plane poles per inserted quartet, indexed as one
`Fin (2k)` packet. -/
def movingEvenCanonicalSurgeryPoleFamily
    {k : ℕ} (t : Fin k → ℂ) :
    Fin (k + k) → ℂ :=
  fun j =>
    Sum.elim t (fun i => -star (t i))
      (finSumFinEquiv.symm j)

@[simp] theorem movingEvenCanonicalSurgeryPoleFamily_inl
    {k : ℕ} (t : Fin k → ℂ) (i : Fin k) :
    movingEvenCanonicalSurgeryPoleFamily t
        (finSumFinEquiv (Sum.inl i)) =
      t i := by
  change
    Sum.elim t (fun i => -star (t i))
        (finSumFinEquiv.symm
          (finSumFinEquiv (Sum.inl i))) =
      t i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem movingEvenCanonicalSurgeryPoleFamily_inr
    {k : ℕ} (t : Fin k → ℂ) (i : Fin k) :
    movingEvenCanonicalSurgeryPoleFamily t
        (finSumFinEquiv (Sum.inr i)) =
      -star (t i) := by
  change
    Sum.elim t (fun i => -star (t i))
        (finSumFinEquiv.symm
          (finSumFinEquiv (Sum.inr i))) =
      -star (t i)
  rw [Equiv.symm_apply_apply]
  rfl

/-- Required separation of all sign-conjugation orbits. -/
def EvenSurgeryPoleSeparated
    {k : ℕ} (t : Fin k → ℂ) : Prop :=
  Function.Injective
    (movingEvenCanonicalSurgeryPoleFamily t)

theorem movingEvenCanonicalSurgeryPoleFamily_im_pos
    {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) :
    ∀ j, 0 <
      (movingEvenCanonicalSurgeryPoleFamily t j).im := by
  intro j
  unfold movingEvenCanonicalSurgeryPoleFamily
  obtain i | i := finSumFinEquiv.symm j
  · exact ht i
  · simpa using ht i

theorem multiPairCarrier_movingEvenCanonicalSurgeryPoleFamily
    {k : ℕ} (t : Fin k → ℂ) (z : ℂ) :
    multiPairCarrier
        (movingEvenCanonicalSurgeryPoleFamily t) z =
      multiPairCarrier t z -
        multiPairCarrier t (-z) := by
  rw [multiPairCarrier, multiPairCarrier,
    multiPairCarrier]
  rw [← Equiv.sum_comp finSumFinEquiv]
  rw [Fintype.sum_sum_type]
  simp only [movingEvenCanonicalSurgeryPoleFamily,
    Equiv.symm_apply_apply,
    Sum.elim_inl, Sum.elim_inr]
  rw [show
      (∑ i : Fin k,
        ((-star (t i) - z)⁻¹ +
          (star (-star (t i)) - z)⁻¹)) =
        -(∑ i : Fin k,
          ((t i - -z)⁻¹ +
            (star (t i) - -z)⁻¹)) by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [star_neg, star_star]
    rw [show -star (t i) - z =
          -(star (t i) + z) by ring,
      show -t i - z = -(t i + z) by ring,
      inv_neg, inv_neg]
    ring]
  ring

/-- Even canonical surgery carrier: delete selected real sign-pairs
and insert the off-real quartets. -/
def movingEvenCanonicalSurgeryCarrier
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) : ℂ :=
  movingEvenCanonicalComplementCarrier θ
      (movingCanonicalSurgerySelectedIndices aIdx bIdx) z +
    multiPairCarrier
      (movingEvenCanonicalSurgeryPoleFamily t) z

/-- Exact `2k` negative-square theorem for even Schwarz-real
canonical surgery. -/
theorem movingEvenCanonicalSurgeryCarrier_exact_negativeSquares
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (hsep : EvenSurgeryPoleSeparated t) :
    (∀ {N : ℕ} (z : Fin N → ℂ),
      (∀ j, 0 < (z j).im) →
      (∀ i j,
        z j ≠ movingEvenCanonicalSurgeryPoleFamily t i) →
      ∀ W : Submodule ℂ (Fin N → ℂ),
        (∀ x ∈ W, x ≠ 0 →
          (star x ⬝ᵥ
            (carrierPickMatrix
              (movingEvenCanonicalSurgeryCarrier
                θ aIdx bIdx t) z).mulVec x).re < 0) →
        Module.finrank ℂ W ≤ k + k) ∧
      ∃ z : Fin (k + k) → ℂ,
        (∀ j, 0 < (z j).im) ∧
        (∀ i j,
          z j ≠
            movingEvenCanonicalSurgeryPoleFamily t i) ∧
        Function.Injective z ∧
        ∀ x : Fin (k + k) → ℂ, x ≠ 0 →
          (star x ⬝ᵥ
            (carrierPickMatrix
              (movingEvenCanonicalSurgeryCarrier
                θ aIdx bIdx t) z).mulVec x).re < 0 := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let p :=
    movingEvenCanonicalSurgeryPoleFamily t
  exact add_multiPairCarrier_exact_negativeSquares
    (movingEvenCanonicalComplementCarrier θ S)
    p
    (movingEvenCanonicalSurgeryPoleFamily_im_pos t ht)
    hsep
    (fun i =>
      continuousAt_movingEvenCanonicalComplementCarrier
        θ S
        (movingEvenCanonicalSurgeryPoleFamily_im_pos
          t ht i))
    (fun {_} z hz =>
      movingEvenCanonicalComplementCarrier_pick_posSemidef
        θ S z hz)

/-- A moving canonical zero cannot meet a nonreal point. -/
theorem movingCanonicalZero_ne_of_im_ne_zero
    (θ : BoundedRealSequence) (n : ℕ) {z : ℂ}
    (hz : z.im ≠ 0) :
    z ≠ (movingCanonicalZero θ n : ℂ) := by
  intro h
  apply hz
  have him := congrArg Complex.im h
  simpa using him

/-- Complement carrier summability in either open half-plane. -/
theorem summable_movingCanonicalComplementCarrier_of_im_ne_zero
    (θ : BoundedRealSequence) (S : Finset ℕ) {z : ℂ}
    (hz : z.im ≠ 0) :
    Summable (fun n : {n // n ∉ S} =>
      movingCanonicalRegularizedAtom θ n z) := by
  have hfull :=
    summable_movingCanonicalLogDerivative θ
      (fun n =>
        movingCanonicalZero_ne_of_im_ne_zero
          θ n hz)
  exact hfull.comp_injective Subtype.val_injective

/-- Negative logarithmic derivative of the complement product,
valid off the real axis. -/
theorem neg_logDeriv_movingCanonicalComplementProduct_eq_of_im_ne_zero
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {z : ℂ} (hz : z.im ≠ 0) :
    -logDeriv (movingCanonicalComplementProduct θ S) z =
      movingCanonicalComplementCarrier θ S z := by
  let a : {n // n ∉ S} → ℂ :=
    fun n => (movingCanonicalZero θ n.1 : ℂ)
  have ha : ∀ n, a n ≠ 0 :=
    fun n => Complex.ofReal_ne_zero.mpr
      (ne_of_gt (movingCanonicalZero_pos θ n.1))
  have hsum : Summable
      (fun n : {n // n ∉ S} =>
        1 / ‖a n‖ ^ 2) :=
    RHTower.canonicalProductE1IndexedComplement_inv_sq_summable
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => n ∈ S)
      (summable_movingCanonicalZero_inv_sq θ)
  have hpole : ∀ n, z ≠ a n :=
    fun n =>
      movingCanonicalZero_ne_of_im_ne_zero
        θ n.1 hz
  have hcarrier :
      Summable (fun n : {n // n ∉ S} =>
        (a n - z)⁻¹ - (a n)⁻¹) := by
    simpa [a, movingCanonicalRegularizedAtom] using
      summable_movingCanonicalComplementCarrier_of_im_ne_zero
        θ S hz
  simpa [movingCanonicalComplementProduct,
    RHTower.canonicalProductE1IndexedComplement,
    movingCanonicalComplementCarrier,
    movingCanonicalRegularizedAtom, a] using
      neg_logDeriv_canonicalProductE1Indexed_eq
        a ha hsum hpole hcarrier

/-- Negative logarithmic derivative of ordinary finite surgery at
every nonreal point away from its inserted conjugate poles. -/
theorem neg_logDeriv_movingCanonicalSurgeryProduct_eq_of_im_ne_zero
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    {z : ℂ} (hz : z.im ≠ 0)
    (hzt : ∀ i, z ≠ t i)
    (hzstar : ∀ i, z ≠ star (t i)) :
    -logDeriv
        (movingCanonicalSurgeryProduct
          θ aIdx bIdx t) z =
      movingCanonicalSurgeryCarrier
        θ aIdx bIdx t z := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let P : ℂ → ℂ := fun w =>
    ∏ i, movingCanonicalSurgeryPairFactor
      (movingCanonicalZero θ (aIdx i))
      (movingCanonicalZero θ (bIdx i))
      (t i) w
  have hcompNe :
      movingCanonicalComplementProduct θ S z ≠ 0 := by
    apply
      RHTower.canonicalProductE1IndexedComplement_ne_zero
        (fun n =>
          (movingCanonicalZero θ n : ℂ))
        (fun n => n ∈ S)
        (fun n => Complex.ofReal_ne_zero.mpr
          (ne_of_gt
            (movingCanonicalZero_pos θ n)))
        (summable_movingCanonicalZero_inv_sq θ)
    intro n
    exact
      movingCanonicalZero_ne_of_im_ne_zero
        θ n.1 hz
  have hpairNe : ∀ i,
      movingCanonicalSurgeryPairFactor
        (movingCanonicalZero θ (aIdx i))
        (movingCanonicalZero θ (bIdx i))
        (t i) z ≠ 0 := by
    intro i
    simp only [movingCanonicalSurgeryPairFactor]
    exact mul_ne_zero
      (mul_ne_zero
        (div_ne_zero (Complex.exp_ne_zero _)
          (mul_ne_zero
            (Complex.ofReal_ne_zero.mpr
              (ne_of_gt
                (movingCanonicalZero_pos θ
                  (aIdx i))))
            (Complex.ofReal_ne_zero.mpr
              (ne_of_gt
                (movingCanonicalZero_pos θ
                  (bIdx i))))))
        (sub_ne_zero.mpr (hzt i)))
      (sub_ne_zero.mpr (hzstar i))
  have hPNe : P z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hpairNe i
  have hcompDiff : DifferentiableAt ℂ
      (movingCanonicalComplementProduct θ S) z :=
    (movingCanonicalComplementProduct_analytic θ S
      z (Set.mem_univ z)).differentiableAt
  have hPDiff : DifferentiableAt ℂ P z := by
    dsimp only [P]
    apply DifferentiableAt.fun_finsetProd
    intro i hi
    exact
      (movingCanonicalSurgeryPairFactor_analytic
        _ _ _ z (Set.mem_univ z)).differentiableAt
  change -logDeriv
      (fun w =>
        movingCanonicalComplementProduct θ S w *
          P w) z = _
  rw [logDeriv_mul z hcompNe hPNe
    hcompDiff hPDiff]
  have hcomp :=
    neg_logDeriv_movingCanonicalComplementProduct_eq_of_im_ne_zero
      θ S hz
  have hprod :
      logDeriv P z =
        ∑ i, logDeriv
          (movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i)) z := by
    dsimp only [P]
    exact logDeriv_prod
      (fun i _ => hpairNe i)
      (fun i _ =>
        (movingCanonicalSurgeryPairFactor_analytic
          _ _ _ z
          (Set.mem_univ z)).differentiableAt)
  rw [hprod]
  have hpair : ∀ i,
      -logDeriv
          (movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i)) z =
        (t i - z)⁻¹ + (star (t i) - z)⁻¹ -
          (((movingCanonicalZero θ (aIdx i) : ℂ)⁻¹) +
            ((movingCanonicalZero θ (bIdx i) : ℂ)⁻¹)) :=
    fun i =>
      neg_logDeriv_movingCanonicalSurgeryPairFactor
        _ _ _ _
        (ne_of_gt
          (movingCanonicalZero_pos θ (aIdx i)))
        (ne_of_gt
          (movingCanonicalZero_pos θ (bIdx i)))
        (hzt i) (hzstar i)
  have hpairsum :
      -(∑ i, logDeriv
          (movingCanonicalSurgeryPairFactor
            (movingCanonicalZero θ (aIdx i))
            (movingCanonicalZero θ (bIdx i))
            (t i)) z) =
        multiPairCarrier t z -
          (movingCanonicalSurgeryConstant
            θ aIdx bIdx : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    simp_rw [hpair]
    rw [multiPairCarrier,
      movingCanonicalSurgeryConstant]
    push_cast
    rw [Finset.sum_sub_distrib]
  rw [movingCanonicalSurgeryCarrier]
  linear_combination hcomp + hpairsum

/-- Even surgery carrier is the odd reflection of ordinary surgery;
the ordinary normalization constant cancels exactly. -/
theorem movingEvenCanonicalSurgeryCarrier_eq_sub
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) :
    movingEvenCanonicalSurgeryCarrier
        θ aIdx bIdx t z =
      movingCanonicalSurgeryCarrier
          θ aIdx bIdx t z -
        movingCanonicalSurgeryCarrier
          θ aIdx bIdx t (-z) := by
  rw [movingEvenCanonicalSurgeryCarrier,
    movingEvenCanonicalComplementCarrier,
    movingCanonicalSurgeryCarrier,
    movingCanonicalSurgeryCarrier,
    multiPairCarrier_movingEvenCanonicalSurgeryPoleFamily]
  ring

/-- Entire product realizing formula (13), defined by multiplying
ordinary surgery with its sign reflection. -/
def movingEvenCanonicalSurgeryProduct
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) : ℂ :=
  movingCanonicalSurgeryProduct θ aIdx bIdx t z *
    movingCanonicalSurgeryProduct θ aIdx bIdx t (-z)

theorem movingEvenCanonicalSurgeryProduct_analytic
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    AnalyticOnNhd ℂ
      (movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t) Set.univ := by
  have hS :=
    movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t
  have hneg :
      AnalyticOnNhd ℂ (fun z : ℂ => -z) Set.univ := by
    intro z hz
    fun_prop
  exact hS.mul (hS.comp hneg (by simp))

theorem movingEvenCanonicalSurgeryProduct_even
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) :
    movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t (-z) =
      movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t z := by
  simp [movingEvenCanonicalSurgeryProduct, mul_comm]

theorem movingCanonicalSurgeryProduct_ne_zero_of_nonreal
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    {z : ℂ} (hz : z.im ≠ 0)
    (hzt : ∀ i, z ≠ t i)
    (hzstar : ∀ i, z ≠ star (t i)) :
    movingCanonicalSurgeryProduct
        θ aIdx bIdx t z ≠ 0 := by
  rw [Ne,
    movingCanonicalSurgeryProduct_eq_zero_iff]
  push Not
  exact
    ⟨fun n hn =>
        movingCanonicalZero_ne_of_im_ne_zero
          θ n hz,
      fun i => ⟨hzt i, hzstar i⟩⟩

theorem logDeriv_comp_neg'
    (f : ℂ → ℂ) (z : ℂ) :
    logDeriv (fun w => f (-w)) z =
      -logDeriv f (-z) := by
  rw [logDeriv_apply, deriv_comp_neg, logDeriv_apply]
  ring_nf

/-- Literal negative logarithmic derivative identity for even
surgery on the upper half-plane away from inserted poles. -/
theorem neg_logDeriv_movingEvenCanonicalSurgeryProduct_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    {z : ℂ} (hz : 0 < z.im)
    (ht : ∀ i, 0 < (t i).im)
    (havoid : ∀ i,
      z ≠ movingEvenCanonicalSurgeryPoleFamily t i) :
    -logDeriv
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t) z =
      movingEvenCanonicalSurgeryCarrier
        θ aIdx bIdx t z := by
  have hzt : ∀ i, z ≠ t i := by
    intro i h
    apply havoid (finSumFinEquiv (Sum.inl i))
    rw [movingEvenCanonicalSurgeryPoleFamily_inl]
    exact h
  have hzstar : ∀ i, z ≠ star (t i) := by
    intro i h
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith [hz, ht i]
  have hnzt : ∀ i, -z ≠ t i := by
    intro i h
    have him := congrArg Complex.im h
    simp only [Complex.neg_im] at him
    linarith [hz, ht i]
  have hnzstar : ∀ i, -z ≠ star (t i) := by
    intro i h
    apply havoid (finSumFinEquiv (Sum.inr i))
    have h' := congrArg Neg.neg h
    rw [movingEvenCanonicalSurgeryPoleFamily_inr]
    simpa only [neg_neg] using h'
  have hSz :
      movingCanonicalSurgeryProduct
        θ aIdx bIdx t z ≠ 0 :=
    movingCanonicalSurgeryProduct_ne_zero_of_nonreal
      θ aIdx bIdx t (ne_of_gt hz) hzt hzstar
  have hSnz :
      movingCanonicalSurgeryProduct
        θ aIdx bIdx t (-z) ≠ 0 :=
    movingCanonicalSurgeryProduct_ne_zero_of_nonreal
      θ aIdx bIdx t
      (by simp; exact ne_of_gt hz)
      hnzt hnzstar
  have hSdiff :
      DifferentiableAt ℂ
        (movingCanonicalSurgeryProduct
          θ aIdx bIdx t) z :=
    (movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t z
      (Set.mem_univ z)).differentiableAt
  have hSnegdiff :
      DifferentiableAt ℂ
        (fun w =>
          movingCanonicalSurgeryProduct
            θ aIdx bIdx t (-w)) z :=
    (movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t (-z)
      (Set.mem_univ (-z))).differentiableAt.comp
        z (by fun_prop)
  change -logDeriv
      (fun w =>
        movingCanonicalSurgeryProduct
            θ aIdx bIdx t w *
          movingCanonicalSurgeryProduct
            θ aIdx bIdx t (-w)) z = _
  rw [logDeriv_mul z hSz hSnz hSdiff hSnegdiff,
    logDeriv_comp_neg']
  have hpos :=
    neg_logDeriv_movingCanonicalSurgeryProduct_eq_of_im_ne_zero
      θ aIdx bIdx t (ne_of_gt hz) hzt hzstar
  have hneg :=
    neg_logDeriv_movingCanonicalSurgeryProduct_eq_of_im_ne_zero
      θ aIdx bIdx t
      (z := -z)
      (by simp; exact ne_of_gt hz)
      hnzt hnzstar
  rw [movingEvenCanonicalSurgeryCarrier_eq_sub]
  linear_combination hpos - hneg

/-- Even finite surgery remains of order at most one. -/
theorem movingEvenCanonicalSurgeryProduct_orderOneEnvelope
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    OrderOneEnvelope
      (movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t) := by
  obtain ⟨C, hC, hbound⟩ :=
    movingCanonicalSurgeryProduct_orderOneEnvelope
      θ aIdx bIdx t
  refine ⟨2 * C, by positivity, fun z => ?_⟩
  rw [movingEvenCanonicalSurgeryProduct, norm_mul]
  calc
    ‖movingCanonicalSurgeryProduct
          θ aIdx bIdx t z‖ *
        ‖movingCanonicalSurgeryProduct
          θ aIdx bIdx t (-z)‖ ≤
      Real.exp (orderOneWeight C z) *
        Real.exp (orderOneWeight C (-z)) :=
      mul_le_mul (hbound z) (hbound (-z))
        (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp
        (orderOneWeight C z +
          orderOneWeight C (-z)) := by
      rw [← Real.exp_add]
    _ = Real.exp
        (orderOneWeight (2 * C) z) := by
      congr 1
      simp only [orderOneWeight, norm_neg]
      ring_nf

/-- Exact formula (13) away from its removable denominator zeros.
The entire left side is the canonical continuation through them. -/
theorem movingEvenCanonicalSurgeryProduct_eq_paperQuotient
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (hidx : Function.Injective
      (movingCanonicalSurgeryIndexFamily aIdx bIdx))
    {z : ℂ}
    (hza : ∀ i,
      z ≠ (movingCanonicalZero θ (aIdx i) : ℂ))
    (hzb : ∀ i,
      z ≠ (movingCanonicalZero θ (bIdx i) : ℂ))
    (hnza : ∀ i,
      z ≠ -(movingCanonicalZero θ (aIdx i) : ℂ))
    (hnzb : ∀ i,
      z ≠ -(movingCanonicalZero θ (bIdx i) : ℂ)) :
    movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t z =
      movingEvenCanonicalProduct θ z *
        ∏ i,
          (((z ^ 2 - (t i) ^ 2) *
              (z ^ 2 - (star (t i)) ^ 2)) /
            ((z ^ 2 -
                (movingCanonicalZero
                  θ (aIdx i) : ℂ) ^ 2) *
              (z ^ 2 -
                (movingCanonicalZero
                  θ (bIdx i) : ℂ) ^ 2))) := by
  have hnza' : ∀ i,
      -z ≠
        (movingCanonicalZero θ (aIdx i) : ℂ) := by
    intro i h
    apply hnza i
    have h' := congrArg Neg.neg h
    simpa only [neg_neg] using h'
  have hnzb' : ∀ i,
      -z ≠
        (movingCanonicalZero θ (bIdx i) : ℂ) := by
    intro i h
    apply hnzb i
    have h' := congrArg Neg.neg h
    simpa only [neg_neg] using h'
  have hzq :=
    movingCanonicalSurgeryProduct_eq_paperQuotient
      θ aIdx bIdx t hidx hza hzb
  have hnzq :=
    movingCanonicalSurgeryProduct_eq_paperQuotient
      θ aIdx bIdx t hidx
      (z := -z) hnza' hnzb'
  let Rpos : Fin k → ℂ := fun i =>
    (((z - t i) * (z - star (t i))) /
      ((z -
          (movingCanonicalZero θ (aIdx i) : ℂ)) *
        (z -
          (movingCanonicalZero θ (bIdx i) : ℂ))))
  let Rneg : Fin k → ℂ := fun i =>
    (((-z - t i) * (-z - star (t i))) /
      ((-z -
          (movingCanonicalZero θ (aIdx i) : ℂ)) *
        (-z -
          (movingCanonicalZero θ (bIdx i) : ℂ))))
  let Q : Fin k → ℂ := fun i =>
    (((z ^ 2 - (t i) ^ 2) *
        (z ^ 2 - (star (t i)) ^ 2)) /
      ((z ^ 2 -
          (movingCanonicalZero θ (aIdx i) : ℂ) ^ 2) *
        (z ^ 2 -
          (movingCanonicalZero θ (bIdx i) : ℂ) ^ 2)))
  have hpair : ∀ i, Rpos i * Rneg i = Q i := by
    intro i
    let a : ℂ :=
      (movingCanonicalZero θ (aIdx i) : ℂ)
    let b : ℂ :=
      (movingCanonicalZero θ (bIdx i) : ℂ)
    have hpa : z - a ≠ 0 :=
      sub_ne_zero.mpr (hza i)
    have hpb : z - b ≠ 0 :=
      sub_ne_zero.mpr (hzb i)
    have hna : -z - a ≠ 0 :=
      sub_ne_zero.mpr (hnza' i)
    have hnb : -z - b ≠ 0 :=
      sub_ne_zero.mpr (hnzb' i)
    have hzaPlus : z + a ≠ 0 := by
      intro h
      apply hnza i
      linear_combination h
    have hzbPlus : z + b ≠ 0 := by
      intro h
      apply hnzb i
      linear_combination h
    have hsqA : z ^ 2 - a ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hzaPlus hpa
    have hsqB : z ^ 2 - b ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero hzbPlus hpb
    dsimp only [Rpos, Rneg, Q, a, b]
    field_simp [hpa, hpb, hna, hnb, hsqA, hsqB]
    ring
  have hprod :
      (∏ i, Rpos i) * (∏ i, Rneg i) =
        ∏ i, Q i := by
    rw [← Finset.prod_mul_distrib]
    apply Fintype.prod_congr
    exact hpair
  rw [movingEvenCanonicalSurgeryProduct,
    hzq, hnzq, movingEvenCanonicalProduct]
  change
    (movingCanonicalProduct θ z * ∏ i, Rpos i) *
        (movingCanonicalProduct θ (-z) * ∏ i, Rneg i) =
      movingCanonicalProduct θ z *
        movingCanonicalProduct θ (-z) * ∏ i, Q i
  calc
    (movingCanonicalProduct θ z * ∏ i, Rpos i) *
        (movingCanonicalProduct θ (-z) * ∏ i, Rneg i) =
      movingCanonicalProduct θ z *
        movingCanonicalProduct θ (-z) *
          ((∏ i, Rpos i) * ∏ i, Rneg i) := by ring
    _ = movingCanonicalProduct θ z *
        movingCanonicalProduct θ (-z) * ∏ i, Q i := by
      rw [hprod]

/-- Orbit separation implies ordinary injectivity of inserted upper
poles. -/
theorem EvenSurgeryPoleSeparated.t_injective
    {k : ℕ} {t : Fin k → ℂ}
    (hsep : EvenSurgeryPoleSeparated t) :
    Function.Injective t := by
  intro i j hij
  change Function.Injective
    (movingEvenCanonicalSurgeryPoleFamily t) at hsep
  have heq :
      movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inl i)) =
        movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inl j)) := by
    calc
      movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inl i)) =
          t i :=
        movingEvenCanonicalSurgeryPoleFamily_inl t i
      _ = t j := hij
      _ = movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inl j)) :=
        (movingEvenCanonicalSurgeryPoleFamily_inl t j).symm
  have hpacket := hsep heq
  have hsum := finSumFinEquiv.injective hpacket
  exact Sum.inl.inj hsum

/-- No inserted upper pole lies in another sign-conjugate orbit. -/
theorem EvenSurgeryPoleSeparated.t_ne_neg_star
    {k : ℕ} {t : Fin k → ℂ}
    (hsep : EvenSurgeryPoleSeparated t)
    (i j : Fin k) :
    t i ≠ -star (t j) := by
  intro hij
  change Function.Injective
    (movingEvenCanonicalSurgeryPoleFamily t) at hsep
  have heq :
      movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inl i)) =
        movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inr j)) := by
    calc
      movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inl i)) =
          t i :=
        movingEvenCanonicalSurgeryPoleFamily_inl t i
      _ = -star (t j) := hij
      _ = movingEvenCanonicalSurgeryPoleFamily t
          ((@finSumFinEquiv k k) (Sum.inr j)) :=
        (movingEvenCanonicalSurgeryPoleFamily_inr t j).symm
  have hpacket := hsep heq
  have hsum := finSumFinEquiv.injective hpacket
  exact Sum.inl_ne_inr hsum

/-- Exact divisor of the even surgery product, including all four
members of every inserted quartet. -/
theorem movingEvenCanonicalSurgeryProduct_eq_zero_iff
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) :
    movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t z = 0 ↔
      (∃ n : ℕ,
        n ∉ movingCanonicalSurgerySelectedIndices
            aIdx bIdx ∧
          (z = (movingCanonicalZero θ n : ℂ) ∨
            z = -(movingCanonicalZero θ n : ℂ))) ∨
        ∃ i : Fin k,
          z = t i ∨ z = star (t i) ∨
            z = -t i ∨ z = -star (t i) := by
  rw [movingEvenCanonicalSurgeryProduct, mul_eq_zero,
    movingCanonicalSurgeryProduct_eq_zero_iff,
    movingCanonicalSurgeryProduct_eq_zero_iff]
  constructor
  · rintro
      ((⟨n, hn, hz⟩ | ⟨i, hz⟩) |
        (⟨n, hn, hz⟩ | ⟨i, hz⟩))
    · exact Or.inl ⟨n, hn, Or.inl hz⟩
    · exact Or.inr ⟨i, hz.elim Or.inl
        (fun h => Or.inr (Or.inl h))⟩
    · left
      refine ⟨n, hn, Or.inr ?_⟩
      have h := congrArg Neg.neg hz
      simpa only [neg_neg] using h
    · right
      refine ⟨i, ?_⟩
      rcases hz with hz | hz
      · right
        right
        left
        have h := congrArg Neg.neg hz
        simpa only [neg_neg] using h
      · right
        right
        right
        have h := congrArg Neg.neg hz
        simpa only [neg_neg] using h
  · rintro (⟨n, hn, hz | hz⟩ |
      ⟨i, hz | hz | hz | hz⟩)
    · exact Or.inl (Or.inl ⟨n, hn, hz⟩)
    · right
      left
      refine ⟨n, hn, ?_⟩
      have h := congrArg Neg.neg hz
      simpa only [neg_neg] using h
    · exact Or.inl (Or.inr ⟨i, Or.inl hz⟩)
    · exact Or.inl (Or.inr ⟨i, Or.inr hz⟩)
    · right
      right
      refine ⟨i, Or.inl ?_⟩
      have h := congrArg Neg.neg hz
      simpa only [neg_neg] using h
    · right
      right
      refine ⟨i, Or.inr ?_⟩
      have h := congrArg Neg.neg hz
      simpa only [neg_neg] using h

theorem analyticOrderAt_mul_comp_neg_eq_one_of_left
    (f : ℂ → ℂ) (w : ℂ)
    (hf : AnalyticAt ℂ f w)
    (hfneg : AnalyticAt ℂ f (-w))
    (horder : analyticOrderAt f w = 1)
    (hne : f (-w) ≠ 0) :
    analyticOrderAt (fun z => f z * f (-z)) w = 1 := by
  have hneg :
      AnalyticAt ℂ (fun z : ℂ => -z) w := by
    fun_prop
  have hcomp :
      AnalyticAt ℂ (fun z => f (-z)) w :=
    hfneg.comp hneg
  rw [show (fun z => f z * f (-z)) =
      f * (fun z => f (-z)) by rfl,
    analyticOrderAt_mul hf hcomp,
    hcomp.analyticOrderAt_eq_zero.mpr hne,
    horder]
  rfl

theorem analyticOrderAt_mul_comp_neg_eq_one_of_right
    (f : ℂ → ℂ) (w : ℂ)
    (hf : AnalyticAt ℂ f w)
    (hfneg : AnalyticAt ℂ f (-w))
    (hne : f w ≠ 0)
    (horder : analyticOrderAt f (-w) = 1) :
    analyticOrderAt (fun z => f z * f (-z)) w = 1 := by
  let g : ℂ → ℂ := fun z => -z
  have hg : AnalyticAt ℂ g w := by
    fun_prop
  have hgd : deriv g w ≠ 0 := by
    simp [g]
  have hcomp : AnalyticAt ℂ (f ∘ g) w :=
    hfneg.comp hg
  have hcompOrder :=
    analyticOrderAt_comp_of_deriv_ne_zero
      (f := f) hg hgd
  rw [show (fun z => f z * f (-z)) =
      f * (f ∘ g) by rfl,
    analyticOrderAt_mul hf hcomp,
    hf.analyticOrderAt_eq_zero.mpr hne]
  have hone :
      analyticOrderAt (f ∘ g) w = 1 := by
    rw [hcompOrder]
    simpa [g] using horder
  rw [hone]
  rfl

/-- Ordinary surgery has no zeros at reflected negative real
canonical locations. -/
theorem movingCanonicalSurgeryProduct_neg_real_ne_zero
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) (n : ℕ) :
    movingCanonicalSurgeryProduct θ aIdx bIdx t
        (-(movingCanonicalZero θ n : ℂ)) ≠ 0 := by
  rw [Ne,
    movingCanonicalSurgeryProduct_eq_zero_iff]
  push Not
  constructor
  · intro m hm h
    have hre := congrArg Complex.re h
    change -movingCanonicalZero θ n =
      movingCanonicalZero θ m at hre
    linarith [movingCanonicalZero_pos θ n,
      movingCanonicalZero_pos θ m]
  · intro i
    constructor
    · intro h
      have him := congrArg Complex.im h
      rw [Complex.neg_im, Complex.ofReal_im,
        neg_zero] at him
      linarith [ht i]
    · intro h
      have him := congrArg Complex.im h
      rw [Complex.neg_im, Complex.ofReal_im,
        neg_zero, Complex.star_def,
        Complex.conj_im] at him
      linarith [ht i]

/-- Ordinary surgery is nonzero at the negative of every inserted
upper pole when symmetry orbits are separated. -/
theorem movingCanonicalSurgeryProduct_neg_inserted_ne_zero
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (hsep : EvenSurgeryPoleSeparated t) (i : Fin k) :
    movingCanonicalSurgeryProduct θ aIdx bIdx t
        (-t i) ≠ 0 := by
  apply movingCanonicalSurgeryProduct_ne_zero_of_nonreal
  · simp only [Complex.neg_im]
    exact neg_ne_zero.mpr (ne_of_gt (ht i))
  · intro j h
    have him := congrArg Complex.im h
    simp only [Complex.neg_im] at him
    linarith [ht i, ht j]
  · intro j h
    apply hsep.t_ne_neg_star i j
    have h' := congrArg Neg.neg h
    simpa only [neg_neg] using h'

/-- Ordinary surgery is nonzero at the sign-conjugate upper member
of every inserted quartet. -/
theorem movingCanonicalSurgeryProduct_neg_star_inserted_ne_zero
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (hsep : EvenSurgeryPoleSeparated t) (i : Fin k) :
    movingCanonicalSurgeryProduct θ aIdx bIdx t
        (-star (t i)) ≠ 0 := by
  apply movingCanonicalSurgeryProduct_ne_zero_of_nonreal
  · rw [Complex.neg_im, Complex.star_def,
      Complex.conj_im, neg_neg]
    exact ne_of_gt (ht i)
  · intro j h
    exact hsep.t_ne_neg_star j i h.symm
  · intro j h
    have him := congrArg Complex.im h
    have hsti :
        (star (t i)).im = -(t i).im := by simp
    have hstj :
        (star (t j)).im = -(t j).im := by simp
    rw [Complex.neg_im, hsti, hstj,
      neg_neg] at him
    linarith [ht i, ht j]

theorem movingEvenCanonicalSurgeryProduct_pos_real_zero_analyticOrderAt
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (n : ℕ)
    (hn : n ∉ movingCanonicalSurgerySelectedIndices
      aIdx bIdx) :
    analyticOrderAt
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t)
        (movingCanonicalZero θ n : ℂ) = 1 := by
  let S : ℂ → ℂ :=
    movingCanonicalSurgeryProduct θ aIdx bIdx t
  have hf : AnalyticAt ℂ S
      (movingCanonicalZero θ n : ℂ) :=
    movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t _ (Set.mem_univ _)
  have hfneg : AnalyticAt ℂ S
      (-(movingCanonicalZero θ n : ℂ)) :=
    movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t _ (Set.mem_univ _)
  change analyticOrderAt
      (fun z => S z * S (-z))
      (movingCanonicalZero θ n : ℂ) = 1
  exact analyticOrderAt_mul_comp_neg_eq_one_of_left
      S (movingCanonicalZero θ n : ℂ)
      hf hfneg
      (movingCanonicalSurgeryProduct_real_zero_analyticOrderAt
        θ aIdx bIdx t ht n hn)
      (movingCanonicalSurgeryProduct_neg_real_ne_zero
        θ aIdx bIdx t ht n)

theorem movingEvenCanonicalSurgeryProduct_neg_real_zero_analyticOrderAt
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (n : ℕ)
    (hn : n ∉ movingCanonicalSurgerySelectedIndices
      aIdx bIdx) :
    analyticOrderAt
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t)
        (-(movingCanonicalZero θ n : ℂ)) = 1 := by
  let S : ℂ → ℂ :=
    movingCanonicalSurgeryProduct θ aIdx bIdx t
  have hf : AnalyticAt ℂ S
      (-(movingCanonicalZero θ n : ℂ)) :=
    movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t _ (Set.mem_univ _)
  have hfneg : AnalyticAt ℂ S
      (-(-(movingCanonicalZero θ n : ℂ))) :=
    movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t _ (Set.mem_univ _)
  apply analyticOrderAt_mul_comp_neg_eq_one_of_right
    S (-(movingCanonicalZero θ n : ℂ))
    hf hfneg
    (movingCanonicalSurgeryProduct_neg_real_ne_zero
      θ aIdx bIdx t ht n)
  simpa only [neg_neg] using
    movingCanonicalSurgeryProduct_real_zero_analyticOrderAt
      θ aIdx bIdx t ht n hn

theorem movingEvenCanonicalSurgeryProduct_inserted_zero_analyticOrderAt
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (hsep : EvenSurgeryPoleSeparated t) (i : Fin k) :
    analyticOrderAt
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t) (t i) = 1 ∧
      analyticOrderAt
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t) (star (t i)) = 1 ∧
      analyticOrderAt
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t) (-t i) = 1 ∧
      analyticOrderAt
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t) (-star (t i)) = 1 := by
  let S : ℂ → ℂ :=
    movingCanonicalSurgeryProduct θ aIdx bIdx t
  have horders :=
    movingCanonicalSurgeryProduct_inserted_zero_analyticOrderAt
      θ aIdx bIdx t ht hsep.t_injective i
  have han (w : ℂ) : AnalyticAt ℂ S w :=
    movingCanonicalSurgeryProduct_analytic
      θ aIdx bIdx t w (Set.mem_univ w)
  have hneT :=
    movingCanonicalSurgeryProduct_neg_inserted_ne_zero
      θ aIdx bIdx t ht hsep i
  have hneStar :=
    movingCanonicalSurgeryProduct_neg_star_inserted_ne_zero
      θ aIdx bIdx t ht hsep i
  refine ⟨?_, ?_, ?_, ?_⟩
  · change analyticOrderAt
      (fun z => S z * S (-z)) (t i) = 1
    exact analyticOrderAt_mul_comp_neg_eq_one_of_left
        S (t i) (han (t i)) (han (-t i))
        horders.1 hneT
  · change analyticOrderAt
      (fun z => S z * S (-z)) (star (t i)) = 1
    exact analyticOrderAt_mul_comp_neg_eq_one_of_left
        S (star (t i)) (han (star (t i)))
        (han (-star (t i))) horders.2 hneStar
  · apply analyticOrderAt_mul_comp_neg_eq_one_of_right
      S (-t i) (han (-t i)) (han (-(-t i))) hneT
    simpa only [neg_neg] using horders.1
  · apply analyticOrderAt_mul_comp_neg_eq_one_of_right
      S (-star (t i)) (han (-star (t i)))
      (han (-(-star (t i)))) hneStar
    simpa only [neg_neg] using horders.2

/-- Complementary canonical product is Schwarz-real. -/
theorem movingCanonicalComplementProduct_conj
    (θ : BoundedRealSequence) (S : Finset ℕ)
    (z : ℂ) :
    movingCanonicalComplementProduct θ S (conj z) =
      conj (movingCanonicalComplementProduct θ S z) := by
  have hm :
      Multipliable (fun n : {n // n ∉ S} =>
        RHTower.weierstrassE1
          (z / (movingCanonicalZero θ n.1 : ℂ))) :=
    RHTower.canonicalProductE1IndexedComplement_multipliable
      (fun n => (movingCanonicalZero θ n : ℂ))
      (fun n => n ∈ S)
      (fun n => Complex.ofReal_ne_zero.mpr
        (ne_of_gt (movingCanonicalZero_pos θ n)))
      (summable_movingCanonicalZero_inv_sq θ) z
  change
    (∏' n : {n // n ∉ S},
      RHTower.weierstrassE1
        (conj z /
          (movingCanonicalZero θ n.1 : ℂ))) =
      conj
        (∏' n : {n // n ∉ S},
          RHTower.weierstrassE1
            (z /
              (movingCanonicalZero θ n.1 : ℂ)))
  calc
    (∏' n : {n // n ∉ S},
        RHTower.weierstrassE1
          (conj z /
            (movingCanonicalZero θ n.1 : ℂ))) =
      ∏' n : {n // n ∉ S},
        Complex.conjAe.toMonoidHom
          (RHTower.weierstrassE1
            (z /
              (movingCanonicalZero θ n.1 : ℂ))) := by
        apply tprod_congr
        intro n
        change
          RHTower.weierstrassE1
              (conj z /
                (movingCanonicalZero θ n.1 : ℂ)) =
            conj
              (RHTower.weierstrassE1
                (z /
                  (movingCanonicalZero θ n.1 : ℂ)))
        simp only [RHTower.weierstrassE1,
          map_mul, map_sub, map_one, map_div₀,
          Complex.conj_ofReal]
        rw [← Complex.exp_conj]
        rw [map_div₀, Complex.conj_ofReal]
    _ = Complex.conjAe.toMonoidHom
        (∏' n : {n // n ∉ S},
          RHTower.weierstrassE1
            (z /
              (movingCanonicalZero θ n.1 : ℂ))) :=
      (hm.map_tprod Complex.conjAe.toMonoidHom
        Complex.continuous_conj).symm
    _ = _ := rfl

theorem movingCanonicalSurgeryPairFactor_conj
    (a b : ℝ) (t z : ℂ) :
    movingCanonicalSurgeryPairFactor
        a b t (conj z) =
      conj (movingCanonicalSurgeryPairFactor
        a b t z) := by
  rw [movingCanonicalSurgeryPairFactor,
    movingCanonicalSurgeryPairFactor]
  simp only [map_mul, map_div₀, map_sub,
    Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  simp only [map_add, map_div₀,
    Complex.conj_ofReal]
  rw [show conj (star t) = t by simp]
  rw [show star t = conj t by rfl]
  ring

theorem movingCanonicalSurgeryProduct_conj
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) :
    movingCanonicalSurgeryProduct
        θ aIdx bIdx t (conj z) =
      conj (movingCanonicalSurgeryProduct
        θ aIdx bIdx t z) := by
  rw [movingCanonicalSurgeryProduct,
    movingCanonicalSurgeryProduct,
    movingCanonicalComplementProduct_conj,
    map_mul, map_prod]
  apply congrArg
  apply Fintype.prod_congr
  intro i
  exact movingCanonicalSurgeryPairFactor_conj
    _ _ _ _

/-- Formula (13) is Schwarz-real as an entire function. -/
theorem movingEvenCanonicalSurgeryProduct_conj
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (z : ℂ) :
    movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t (conj z) =
      conj (movingEvenCanonicalSurgeryProduct
        θ aIdx bIdx t z) := by
  change
    movingCanonicalSurgeryProduct θ aIdx bIdx t
          (conj z) *
        movingCanonicalSurgeryProduct θ aIdx bIdx t
          (-conj z) =
      conj
        (movingCanonicalSurgeryProduct θ aIdx bIdx t z *
          movingCanonicalSurgeryProduct θ aIdx bIdx t (-z))
  rw [movingCanonicalSurgeryProduct_conj]
  have harg : -conj z = conj (-z) := by simp
  rw [harg, movingCanonicalSurgeryProduct_conj,
    map_mul]

/-- Finite-deletion decomposition of the complement carrier at any
nonreal point. -/
theorem movingCanonicalComplementCarrier_eq_sub_sum_of_im_ne_zero
    (θ : BoundedRealSequence) (S : Finset ℕ)
    {z : ℂ} (hz : z.im ≠ 0) :
    movingCanonicalComplementCarrier θ S z =
      movingCanonicalLogDerivative θ z -
        ∑ n ∈ S,
          movingCanonicalRegularizedAtom θ n z := by
  have hfull :=
    summable_movingCanonicalLogDerivative θ
      (fun n =>
        movingCanonicalZero_ne_of_im_ne_zero
          θ n hz)
  have hsplit :=
    hfull.sum_add_tsum_subtype_compl S
  change
    (∑ n ∈ S,
        movingCanonicalRegularizedAtom θ n z) +
        movingCanonicalComplementCarrier θ S z =
      movingCanonicalLogDerivative θ z at hsplit
  rw [add_comm] at hsplit
  exact eq_sub_of_add_eq hsplit

/-- Rational correction from the even surgery carrier to its
unsurgered even canonical carrier. -/
def movingEvenCanonicalSurgeryGaugeRatFunc
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    RatFunc ℂ :=
  -(∑ n ∈ movingCanonicalSurgerySelectedIndices aIdx bIdx,
      (complexPoleTermRatFunc
          (movingCanonicalZero θ n : ℂ) 1 +
        complexPoleTermRatFunc
          (-(movingCanonicalZero θ n : ℂ)) 1)) +
    ∑ j : Fin (k + k),
      (complexPoleTermRatFunc
          (movingEvenCanonicalSurgeryPoleFamily t j) 1 +
        complexPoleTermRatFunc
          (star
            (movingEvenCanonicalSurgeryPoleFamily t j)) 1)

def movingEvenCanonicalSurgeryGaugeUpperEndAnalytic
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    upperEndAnalyticSubring :=
  -(∑ n ∈ movingCanonicalSurgerySelectedIndices aIdx bIdx,
      (complexPoleTermUpperEndAnalytic
          (movingCanonicalZero θ n : ℂ) 1 +
        complexPoleTermUpperEndAnalytic
          (-(movingCanonicalZero θ n : ℂ)) 1)) +
    ∑ j : Fin (k + k),
      (complexPoleTermUpperEndAnalytic
          (movingEvenCanonicalSurgeryPoleFamily t j) 1 +
        complexPoleTermUpperEndAnalytic
          (star
            (movingEvenCanonicalSurgeryPoleFamily t j)) 1)

theorem upperEndRatfuncToMero_movingEvenCanonicalSurgeryGauge
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero
        (movingEvenCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (movingEvenCanonicalSurgeryGaugeUpperEndAnalytic
          θ aIdx bIdx t) := by
  letI := isDomain_upperEndAnalyticSubring
  simp only [movingEvenCanonicalSurgeryGaugeRatFunc,
    movingEvenCanonicalSurgeryGaugeUpperEndAnalytic,
    map_add, map_neg, map_sum,
    upperEndRatfuncToMero_complexPoleTerm]

theorem movingEvenCanonicalSurgeryGaugeUpperEndAnalytic_coe
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    ((movingEvenCanonicalSurgeryGaugeUpperEndAnalytic
        θ aIdx bIdx t : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      ((fun z =>
        -(∑ n ∈
            movingCanonicalSurgerySelectedIndices aIdx bIdx,
            (((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
              (-(movingCanonicalZero θ n : ℂ) - z)⁻¹)) +
          multiPairCarrier
            (movingEvenCanonicalSurgeryPoleFamily t) z) :
        Germ upperEndFilter ℂ) := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let p :=
    movingEvenCanonicalSurgeryPoleFamily t
  have hpole (a : ℂ) :
      Subring.subtype upperEndAnalyticSubring
          (complexPoleTermUpperEndAnalytic a 1) =
        ((fun z : ℂ => (a - z)⁻¹) :
          Germ upperEndFilter ℂ) := by
    change
      (((fun z : ℂ => 1 / (a - z)) : ℂ → ℂ) :
          Germ upperEndFilter ℂ) =
        ((fun z : ℂ => (a - z)⁻¹) :
          Germ upperEndFilter ℂ)
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by
      simp [one_div]
  have hselectedAtom (n : ℕ) :
      Subring.subtype upperEndAnalyticSubring
          (complexPoleTermUpperEndAnalytic
              (movingCanonicalZero θ n : ℂ) 1 +
            complexPoleTermUpperEndAnalytic
              (-(movingCanonicalZero θ n : ℂ)) 1) =
        ((fun z =>
          ((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
            (-(movingCanonicalZero θ n : ℂ) - z)⁻¹) :
          Germ upperEndFilter ℂ) := by
    rw [map_add, hpole, hpole,
      ← Filter.Germ.coe_add]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => rfl
  have hselected :
      Subring.subtype upperEndAnalyticSubring
          (∑ n ∈ S,
            (complexPoleTermUpperEndAnalytic
                (movingCanonicalZero θ n : ℂ) 1 +
              complexPoleTermUpperEndAnalytic
                (-(movingCanonicalZero θ n : ℂ)) 1)) =
        ((fun z =>
          ∑ n ∈ S,
            (((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
              (-(movingCanonicalZero θ n : ℂ) - z)⁻¹)) :
          Germ upperEndFilter ℂ) := by
    rw [map_sum]
    simp_rw [hselectedAtom]
    change
      (∑ n ∈ S,
        (Filter.Germ.coeRingHom upperEndFilter)
          (fun z =>
            ((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
              (-(movingCanonicalZero θ n : ℂ) - z)⁻¹)) = _
    rw [← map_sum
      (Filter.Germ.coeRingHom upperEndFilter)]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by simp
  have hpair (j : Fin (k + k)) :
      Subring.subtype upperEndAnalyticSubring
          (complexPoleTermUpperEndAnalytic (p j) 1 +
            complexPoleTermUpperEndAnalytic
              (star (p j)) 1) =
        ((fun z =>
          (p j - z)⁻¹ +
            (star (p j) - z)⁻¹) :
          Germ upperEndFilter ℂ) := by
    rw [map_add, hpole, hpole,
      ← Filter.Germ.coe_add]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => rfl
  have hpairs :
      Subring.subtype upperEndAnalyticSubring
          (∑ j : Fin (k + k),
            (complexPoleTermUpperEndAnalytic (p j) 1 +
              complexPoleTermUpperEndAnalytic
                (star (p j)) 1)) =
        ((fun z =>
          ∑ j : Fin (k + k),
            ((p j - z)⁻¹ +
              (star (p j) - z)⁻¹)) :
          Germ upperEndFilter ℂ) := by
    rw [map_sum]
    simp_rw [hpair]
    change
      (∑ j : Fin (k + k),
        (Filter.Germ.coeRingHom upperEndFilter)
          (fun z =>
            (p j - z)⁻¹ +
              (star (p j) - z)⁻¹)) = _
    rw [← map_sum
      (Filter.Germ.coeRingHom upperEndFilter)]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by simp
  change
    Subring.subtype upperEndAnalyticSubring
        (movingEvenCanonicalSurgeryGaugeUpperEndAnalytic
          θ aIdx bIdx t) = _
  rw [movingEvenCanonicalSurgeryGaugeUpperEndAnalytic,
    map_add, map_neg, hselected, hpairs,
    ← Filter.Germ.coe_neg,
    ← Filter.Germ.coe_add]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    simp [S, p, multiPairCarrier]

/-- Exact even surgery carrier as one upper-end analytic germ. -/
def movingEvenCanonicalSurgeryCarrierUpperEndAnalytic
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    upperEndAnalyticSubring :=
  analyticUpperEndElement
      (movingEvenCanonicalCarrier θ) 0
      (by
        simpa using
          analyticOnNhd_movingEvenCanonicalCarrier_translate_upperTail
            θ 0) +
    movingEvenCanonicalSurgeryGaugeUpperEndAnalytic
      θ aIdx bIdx t

theorem movingEvenCanonicalSurgeryCarrierUpperEndAnalytic_coe
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    ((movingEvenCanonicalSurgeryCarrierUpperEndAnalytic
        θ aIdx bIdx t : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (movingEvenCanonicalSurgeryCarrier
        θ aIdx bIdx t : Germ upperEndFilter ℂ) := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  let p :=
    movingEvenCanonicalSurgeryPoleFamily t
  change
    Subring.subtype upperEndAnalyticSubring
        (movingEvenCanonicalSurgeryCarrierUpperEndAnalytic
          θ aIdx bIdx t) = _
  rw [movingEvenCanonicalSurgeryCarrierUpperEndAnalytic,
    map_add]
  rw [show
      Subring.subtype upperEndAnalyticSubring
          (movingEvenCanonicalSurgeryGaugeUpperEndAnalytic
            θ aIdx bIdx t) =
        ((fun z =>
          -(∑ n ∈
              movingCanonicalSurgerySelectedIndices aIdx bIdx,
              (((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
                (-(movingCanonicalZero θ n : ℂ) - z)⁻¹)) +
            multiPairCarrier
              (movingEvenCanonicalSurgeryPoleFamily t) z) :
          Germ upperEndFilter ℂ) from
    movingEvenCanonicalSurgeryGaugeUpperEndAnalytic_coe
      θ aIdx bIdx t]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards
    [upperEndFilter_basis.mem_iff.mpr
      ⟨0, trivial, Set.Subset.rfl⟩] with z hz
  have hz0 : z.im ≠ 0 := ne_of_gt hz
  have hnz0 : (-z).im ≠ 0 := by
    simp only [Complex.neg_im]
    exact neg_ne_zero.mpr hz0
  have hpos :=
    movingCanonicalComplementCarrier_eq_sub_sum_of_im_ne_zero
      θ S hz0
  have hneg :=
    movingCanonicalComplementCarrier_eq_sub_sum_of_im_ne_zero
      θ S hnz0
  have hterm (n : ℕ) :
      -((((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
          (-(movingCanonicalZero θ n : ℂ) - z)⁻¹)) =
        -movingCanonicalRegularizedAtom θ n z +
          movingCanonicalRegularizedAtom θ n (-z) := by
    rw [movingCanonicalRegularizedAtom,
      movingCanonicalRegularizedAtom]
    rw [show
        -(movingCanonicalZero θ n : ℂ) - z =
          -((movingCanonicalZero θ n : ℂ) + z) by ring,
      inv_neg]
    ring
  have hselected :
      -(∑ n ∈ S,
          (((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
            (-(movingCanonicalZero θ n : ℂ) - z)⁻¹)) =
        -(∑ n ∈ S,
            movingCanonicalRegularizedAtom θ n z) +
          ∑ n ∈ S,
            movingCanonicalRegularizedAtom θ n (-z) := by
    rw [← Finset.sum_neg_distrib]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,
      Finset.sum_neg_distrib]
  rw [movingEvenCanonicalSurgeryCarrier,
    movingEvenCanonicalComplementCarrier,
    movingEvenCanonicalCarrier]
  change
    (movingCanonicalLogDerivative θ z -
        movingCanonicalLogDerivative θ (-z)) +
      (-(∑ n ∈ S,
          (((movingCanonicalZero θ n : ℂ) - z)⁻¹ +
            (-(movingCanonicalZero θ n : ℂ) - z)⁻¹)) +
        multiPairCarrier p z) =
      movingCanonicalComplementCarrier θ S z -
        movingCanonicalComplementCarrier θ S (-z) +
        multiPairCarrier p z
  linear_combination -hpos + hneg + hselected

/-- Upper-end meromorphic realization of literal even surgery
carrier. -/
def movingEvenCanonicalSurgeryUpperEndMero
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (movingEvenCanonicalSurgeryCarrierUpperEndAnalytic
      θ aIdx bIdx t)

theorem movingEvenCanonicalTranslatedUpperEndMero_zero
    (θ : BoundedRealSequence) :
    letI := isDomain_upperEndAnalyticSubring
    movingEvenCanonicalTranslatedUpperEndMero θ 0 =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (analyticUpperEndElement
          (movingEvenCanonicalCarrier θ) 0
          (by
            simpa using
              analyticOnNhd_movingEvenCanonicalCarrier_translate_upperTail
                θ 0)) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingEvenCanonicalTranslatedUpperEndMero,
    analyticUpperEndMero]
  congr 1
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by simp

theorem movingEvenCanonicalSurgeryUpperEndMero_eq_add_rational
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    movingEvenCanonicalSurgeryUpperEndMero
        θ aIdx bIdx t =
      movingEvenCanonicalTranslatedUpperEndMero θ 0 +
        upperEndRatfuncToMero
          (movingEvenCanonicalSurgeryGaugeRatFunc
            θ aIdx bIdx t) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingEvenCanonicalSurgeryUpperEndMero,
    movingEvenCanonicalSurgeryCarrierUpperEndAnalytic,
    map_add,
    upperEndRatfuncToMero_movingEvenCanonicalSurgeryGauge]
  rw [movingEvenCanonicalTranslatedUpperEndMero_zero]

theorem movingEvenCanonicalTranslatedUpperEndMero_eq_translation
    (θ : BoundedRealSequence) (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    movingEvenCanonicalTranslatedUpperEndMero θ h =
      upperEndTranslationMeroEquiv h
        (movingEvenCanonicalTranslatedUpperEndMero θ 0) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingEvenCanonicalTranslatedUpperEndMero_zero,
    upperEndTranslationMeroEquiv_algebraMap]
  rw [movingEvenCanonicalTranslatedUpperEndMero,
    analyticUpperEndMero]
  congr 1

/-- Full complex translation orbit of exact even surgery carrier. -/
def movingEvenCanonicalSurgeryTranslateFamily
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (h : ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndTranslationMeroEquiv h
    (movingEvenCanonicalSurgeryUpperEndMero
      θ aIdx bIdx t)

theorem movingEvenCanonicalSurgeryTranslateFamily_eq_add_rational
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    movingEvenCanonicalSurgeryTranslateFamily
        θ aIdx bIdx t h =
      movingEvenCanonicalTranslatedUpperEndMero θ h +
        upperEndRatfuncToMero
          (ratFuncTranslationEquiv h
            (movingEvenCanonicalSurgeryGaugeRatFunc
              θ aIdx bIdx t)) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingEvenCanonicalSurgeryTranslateFamily,
    movingEvenCanonicalSurgeryUpperEndMero_eq_add_rational,
    map_add,
    upperEndTranslationMeroEquiv_ratfuncToMero]
  rw [←
    movingEvenCanonicalTranslatedUpperEndMero_eq_translation
      θ h]

theorem
    movingEvenCanonicalSurgeryTranslateFamily_differentialIndependent_iff
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
        (movingEvenCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t) ↔
      DifferentialIndependent (RatFunc ℂ)
        (movingEvenCanonicalTranslatedUpperEndMero θ) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  rw [show
      movingEvenCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t =
        fun h =>
          movingEvenCanonicalTranslatedUpperEndMero θ h +
            upperEndRatfuncToMero
              (ratFuncTranslationEquiv h
                (movingEvenCanonicalSurgeryGaugeRatFunc
                  θ aIdx bIdx t)) by
    funext h
    exact
      movingEvenCanonicalSurgeryTranslateFamily_eq_add_rational
        θ aIdx bIdx t h]
  exact differentialIndependent_addUpperEndRatfunc_iff
    (movingEvenCanonicalTranslatedUpperEndMero θ)
    (fun h =>
      ratFuncTranslationEquiv h
        (movingEvenCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t))

theorem movingEvenCanonicalSurgeryTranslateFamily_differentialAdjoin_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra
        (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    differentialAdjoin (RatFunc ℂ)
        (Set.range
          (movingEvenCanonicalSurgeryTranslateFamily
            θ aIdx bIdx t)) =
      differentialAdjoin (RatFunc ℂ)
        (Set.range
          (movingEvenCanonicalTranslatedUpperEndMero θ)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) :=
    ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra
      (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  rw [show
      movingEvenCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t =
        fun h =>
          movingEvenCanonicalTranslatedUpperEndMero θ h +
            algebraMap (RatFunc ℂ) upperEndMeroField
              (ratFuncTranslationEquiv h
                (movingEvenCanonicalSurgeryGaugeRatFunc
                  θ aIdx bIdx t)) by
    funext h
    exact
      movingEvenCanonicalSurgeryTranslateFamily_eq_add_rational
        θ aIdx bIdx t h]
  simpa using differentialAdjoin_range_affineBase_eq
    (movingEvenCanonicalTranslatedUpperEndMero θ)
    (fun _ : ℂ => 1)
    (fun h =>
      ratFuncTranslationEquiv h
        (movingEvenCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t))
    (fun _ => one_ne_zero)

theorem
    movingEvenCanonicalSurgeryTranslateFamily_differentialFamilyMatroid_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra
        (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    letI : CharZero upperEndMeroField :=
      charZero_of_injective_ringHom
        upperEndRatfuncToMero.injective
    differentialFamilyMatroid (F := RatFunc ℂ)
        (movingEvenCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t) =
      differentialFamilyMatroid (F := RatFunc ℂ)
        (movingEvenCanonicalTranslatedUpperEndMero θ) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) :=
    ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra
      (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  letI : CharZero upperEndMeroField :=
    charZero_of_injective_ringHom
      upperEndRatfuncToMero.injective
  rw [show
      movingEvenCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t =
        fun h =>
          movingEvenCanonicalTranslatedUpperEndMero θ h +
            algebraMap (RatFunc ℂ) upperEndMeroField
              (ratFuncTranslationEquiv h
                (movingEvenCanonicalSurgeryGaugeRatFunc
                  θ aIdx bIdx t)) by
    funext h
    exact
      movingEvenCanonicalSurgeryTranslateFamily_eq_add_rational
        θ aIdx bIdx t h]
  exact differentialFamilyMatroid_addBase_eq
    (movingEvenCanonicalTranslatedUpperEndMero θ)
    (fun h =>
      ratFuncTranslationEquiv h
        (movingEvenCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t))

theorem
    movingEvenCanonicalSurgeryTranslateFamily_differentialIndependent
    {k : ℕ} (θ : BoundedRealSequence)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift :
        InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p ×
          Fin (p.coefficientDegree + 1) → ℂ),
      movingEvenCanonicalExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (movingEvenCanonicalSurgeryTranslateFamily
        θ aIdx bIdx t) := by
  exact
    (movingEvenCanonicalSurgeryTranslateFamily_differentialIndependent_iff
      θ aIdx bIdx t).2
      (movingEvenCanonicalTranslation_upperEnd_differentialIndependent
        θ hfree)

theorem
    movingEvenCanonicalSurgery_fullTranslationUpperEndDifferentialIndependence_denseResidual
    {k : ℕ} (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    let universalPhase : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift :
          InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p ×
            Fin (p.coefficientDegree + 1) → ℂ),
        movingEvenCanonicalExpandedPatternRelationHolds
          (row := CarrierPatternRow p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧
      universalPhase ∈ residual BoundedRealSequence ∧
      ∀ θ ∈ universalPhase,
        letI := isDomain_upperEndAnalyticSubring
        letI : Algebra (RatFunc ℂ) upperEndMeroField :=
          upperEndRatfuncToMero.toAlgebra
        letI := upperEndMeroFieldDifferential
        DifferentialIndependent (RatFunc ℂ)
          (movingEvenCanonicalSurgeryTranslateFamily
            θ aIdx bIdx t) := by
  dsimp only
  have hphase :=
    movingEvenCanonical_fullTranslationFreeness_denseResidual
  dsimp only at hphase
  refine ⟨hphase.1, hphase.2.1, ?_⟩
  intro θ hθ
  exact
    movingEvenCanonicalSurgeryTranslateFamily_differentialIndependent
      θ hθ aIdx bIdx t

/-- Unpointed generated differential field cannot recover exact even
surgery index `2k`. -/
theorem no_movingEvenCanonicalSurgeryIndex_selector_of_differentialAdjoin
    (θ : BoundedRealSequence) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra
        (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    ¬ ∃ S :
        IntermediateField (RatFunc ℂ)
          upperEndMeroField → ℕ,
      ∀ (k : ℕ) (aIdx bIdx : Fin k → ℕ)
        (t : Fin k → ℂ),
        S (differentialAdjoin (RatFunc ℂ)
          (Set.range
            (movingEvenCanonicalSurgeryTranslateFamily
              θ aIdx bIdx t))) = k + k := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) :=
    ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra
      (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  rintro ⟨S, hS⟩
  let a0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let b0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let t0 : Fin 0 → ℂ := fun i => Fin.elim0 i
  let a1 : Fin 1 → ℕ := fun _ => 0
  let b1 : Fin 1 → ℕ := fun _ => 1
  let t1 : Fin 1 → ℂ := fun _ => 1 + Complex.I
  have h0 := hS 0 a0 b0 t0
  have h1 := hS 1 a1 b1 t1
  rw [
    movingEvenCanonicalSurgeryTranslateFamily_differentialAdjoin_eq
      θ a0 b0 t0] at h0
  rw [
    movingEvenCanonicalSurgeryTranslateFamily_differentialAdjoin_eq
      θ a1 b1 t1] at h1
  omega

/-- Complete entire/even/Schwarz-real/order/divisor package for
formula (13). -/
theorem movingEvenCanonicalSurgeryProduct_exactOrderOneDivisor
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im)
    (hsep : EvenSurgeryPoleSeparated t) :
    AnalyticOnNhd ℂ
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t) Set.univ ∧
      (∀ z,
        movingEvenCanonicalSurgeryProduct
            θ aIdx bIdx t (-z) =
          movingEvenCanonicalSurgeryProduct
            θ aIdx bIdx t z) ∧
      (∀ z,
        movingEvenCanonicalSurgeryProduct
            θ aIdx bIdx t (conj z) =
          conj (movingEvenCanonicalSurgeryProduct
            θ aIdx bIdx t z)) ∧
      OrderOneEnvelope
        (movingEvenCanonicalSurgeryProduct
          θ aIdx bIdx t) ∧
      HasExponentOfConvergenceOneIndexed
        (fun n :
            {n // n ∉
              movingCanonicalSurgerySelectedIndices
                aIdx bIdx} =>
          (movingCanonicalZero θ n.1 : ℂ)) ∧
      (∀ z,
        movingEvenCanonicalSurgeryProduct
            θ aIdx bIdx t z = 0 ↔
          (∃ n : ℕ,
            n ∉ movingCanonicalSurgerySelectedIndices
                aIdx bIdx ∧
              (z = (movingCanonicalZero θ n : ℂ) ∨
                z = -(movingCanonicalZero θ n : ℂ))) ∨
            ∃ i : Fin k,
              z = t i ∨ z = star (t i) ∨
                z = -t i ∨ z = -star (t i)) ∧
      (∀ n,
        n ∉ movingCanonicalSurgerySelectedIndices
            aIdx bIdx →
          analyticOrderAt
              (movingEvenCanonicalSurgeryProduct
                θ aIdx bIdx t)
              (movingCanonicalZero θ n : ℂ) = 1 ∧
            analyticOrderAt
              (movingEvenCanonicalSurgeryProduct
                θ aIdx bIdx t)
              (-(movingCanonicalZero θ n : ℂ)) = 1) ∧
      ∀ i,
        analyticOrderAt
            (movingEvenCanonicalSurgeryProduct
              θ aIdx bIdx t) (t i) = 1 ∧
          analyticOrderAt
            (movingEvenCanonicalSurgeryProduct
              θ aIdx bIdx t) (star (t i)) = 1 ∧
          analyticOrderAt
            (movingEvenCanonicalSurgeryProduct
              θ aIdx bIdx t) (-t i) = 1 ∧
          analyticOrderAt
            (movingEvenCanonicalSurgeryProduct
              θ aIdx bIdx t) (-star (t i)) = 1 := by
  exact
    ⟨movingEvenCanonicalSurgeryProduct_analytic
        θ aIdx bIdx t,
      movingEvenCanonicalSurgeryProduct_even
        θ aIdx bIdx t,
      movingEvenCanonicalSurgeryProduct_conj
        θ aIdx bIdx t,
      movingEvenCanonicalSurgeryProduct_orderOneEnvelope
        θ aIdx bIdx t,
      movingCanonicalComplementZero_hasExponentOfConvergenceOne
        θ
          (movingCanonicalSurgerySelectedIndices
            aIdx bIdx),
      movingEvenCanonicalSurgeryProduct_eq_zero_iff
        θ aIdx bIdx t,
      fun n hn =>
        ⟨movingEvenCanonicalSurgeryProduct_pos_real_zero_analyticOrderAt
            θ aIdx bIdx t ht n hn,
          movingEvenCanonicalSurgeryProduct_neg_real_zero_analyticOrderAt
            θ aIdx bIdx t ht n hn⟩,
      movingEvenCanonicalSurgeryProduct_inserted_zero_analyticOrderAt
        θ aIdx bIdx t ht hsep⟩

end

end GaloisForLFunctions.HTGeometry
