import GaloisForLFunctions.ArithmeticIndexDescent.ThePrimeTwoMixedTailIsGammaSmall

/-!
# The mixed cell pairing is the original prime correlation

The actual half-line coarse and detail vectors have the complete real cell
profiles as representatives. Their two shifted pairings therefore give the
two original source integrals, with the literal prime coefficient. Gamma
payment transfers to these integrals without changing either profile.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

private theorem cellAtom_real_representative (a : ℕ) :
    (cellAtom a : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (rawCell a x : ℂ) := by
  refine (cellAtom_coeFn a).trans (Eventually.of_forall ?_)
  intro x
  simp only [rawCell, indicator_apply]
  split_ifs <;> rfl

/-- A coarse Hilbert atom retains both original adjacent cells. -/
theorem coarseAtom_coeFn (a : ℕ) :
    (coarseAtom a : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (coarseProfile a x : ℂ) := by
  unfold coarseAtom
  filter_upwards [Lp.coeFn_add (cellAtom (2 * a)) (cellAtom (2 * a + 1)),
    cellAtom_real_representative (2 * a), cellAtom_real_representative (2 * a + 1)]
      with x hadd hl hr
  rw [hadd]
  simp only [Pi.add_apply, hl, hr, coarseProfile, Complex.ofReal_add]

theorem coarseSection_coeFn (q : ℕ → ℝ) (X : ℕ) :
    (coarseSection q X : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (averageSectionProfile q X x : ℂ) := by
  have hs := coeFn_finset_sum_smul (Finset.Icc 1 X) (fun a => (q a : ℂ)) coarseAtom
  have ha : ∀ᵐ x ∂halfLineMeasure, ∀ a : ℕ,
      (coarseAtom a : ℝ → ℂ) x = (coarseProfile a x : ℂ) := ae_all_iff.mpr coarseAtom_coeFn
  unfold coarseSection
  filter_upwards [hs, ha] with x hx ha
  rw [hx, averageSectionProfile, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [ha a, Complex.ofReal_mul]

theorem averageSectionProfile_zero_neg (q : ℕ → ℝ) (X : ℕ) {x : ℝ} (hx : x < 0) :
    averageSectionProfile q X x = 0 := by
  have hraw {a : ℕ} (ha : 1 ≤ a) : rawCell a x = 0 := by
    apply indicator_of_notMem
    intro hm
    have hlo : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha)
    exact (not_lt_of_ge (hlo.trans hm.1)) hx
  unfold averageSectionProfile
  apply Finset.sum_eq_zero
  intro a ha
  have ha1 := (Finset.mem_Icc.mp ha).1
  simp only [coarseProfile, hraw (by omega : 1 ≤ 2 * a),
    hraw (by omega : 1 ≤ 2 * a + 1), add_zero, mul_zero]

theorem halfLineExtend_averageSectionProfile (q : ℕ → ℝ) (X : ℕ) :
    (halfLineExtend (coarseSection q X) : ℝ → ℂ) =ᵐ[volume]
      fun x => (averageSectionProfile q X x : ℂ) := by
  refine (halfLineExtend_coeFn _).trans
    ((indicator_ae_eq_of_halfLine (coarseSection_coeFn q X)).trans ?_)
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hx _
  · simp only [indicator_of_notMem hx,
      averageSectionProfile_zero_neg q X (lt_of_not_ge hx), Complex.ofReal_zero]

private theorem inner_shift_real_representatives (u v : L²₊) (f g : ℝ → ℝ)
    (hv : (v : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (g x : ℂ))
    (he : (halfLineExtend u : ℝ → ℂ) =ᵐ[volume] fun x => (f x : ℂ))
    (hg : ∀ x < 0, g x = 0) (t : ℝ) :
    (inner ℂ (halfLineRightShift t u) v).re = ∫ x, f x * g (x + t) := by
  have ht : ∀ᵐ x ∂halfLineMeasure,
      (halfLineExtend u : ℝ → ℂ) (x - t) = (f (x - t) : ℂ) :=
    ae_restrict_of_ae ((measurePreserving_sub_right volume t).quasiMeasurePreserving.ae he)
  have hinner : Integrable (fun x =>
      inner ℂ ((halfLineRightShift t u : ℝ → ℂ) x) (v x)) halfLineMeasure :=
    L2.integrable_inner (halfLineRightShift t u) v
  have hre := integral_re hinner
  simp only [RCLike.re_to_complex] at hre
  rw [L2.inner_def, ← hre]
  have hi : (∫ x, (inner ℂ ((halfLineRightShift t u : ℝ → ℂ) x) (v x)).re ∂halfLineMeasure) =
      ∫ x, f (x - t) * g x ∂halfLineMeasure := by
    apply integral_congr_ae
    filter_upwards [halfLineRightShift_coeFn t u, hv, ht] with x hshift hx hxt
    rw [hshift, hx, hxt, RCLike.inner_apply]
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  rw [hi]
  have hall : (∫ x, f (x - t) * g x ∂halfLineMeasure) = ∫ x, f (x - t) * g x := by
    rw [halfLineMeasure, ← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ici (0 : ℝ)
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx, hg x (lt_of_not_ge hx), mul_zero]
  rw [hall]
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x => f x * g (x + t)) t
  simpa only [sub_add_cancel] using h

/-- Every translated detail-to-average pairing is the physical mixed correlation. -/
theorem inner_shift_haar_coarse_profiles (d q : ℕ → ℝ) (Y X : ℕ) (t : ℝ) :
    (inner ℂ (halfLineRightShift t (haarSection d Y)) (coarseSection q X)).re =
      ∫ x, haarSectionProfile d Y x * averageSectionProfile q X (x + t) :=
  inner_shift_real_representatives _ _ _ _ (coarseSection_coeFn q X)
    (halfLineExtend_haarSectionProfile d Y)
    (fun _ hx => averageSectionProfile_zero_neg q X hx) t

/-- The opposite orientation has the opposite ordered source integral. -/
theorem inner_shift_coarse_haar_profiles (d q : ℕ → ℝ) (Y X : ℕ) (t : ℝ) :
    (inner ℂ (halfLineRightShift t (coarseSection q X)) (haarSection d Y)).re =
      ∫ x, averageSectionProfile q X x * haarSectionProfile d Y (x + t) :=
  inner_shift_real_representatives _ _ _ _ (haarSection_coeFn d Y)
    (halfLineExtend_averageSectionProfile q X)
    (fun _ hx => haarSectionProfile_zero_neg d Y hx) t

theorem inner_shift_coarse_profile (q : ℕ → ℝ) (X : ℕ) (t : ℝ) :
    (inner ℂ (halfLineRightShift t (coarseSection q X)) (coarseSection q X)).re =
      ∫ x, averageSectionProfile q X x * averageSectionProfile q X (x + t) :=
  inner_shift_real_representatives _ _ _ _ (coarseSection_coeFn q X)
    (halfLineExtend_averageSectionProfile q X)
    (fun _ hx => averageSectionProfile_zero_neg q X hx) t

/-- The sum of both actual Hilbert sections realizes the entire complete-cell profile. -/
theorem inner_shift_completePairProfile (q d : ℕ → ℝ) (X : ℕ) (t : ℝ) :
    (inner ℂ (halfLineRightShift t (coarseSection q X + haarSection d X))
      (coarseSection q X + haarSection d X)).re =
        ∫ x, completePairProfile q d X x * completePairProfile q d X (x + t) := by
  have hrep : ((coarseSection q X + haarSection d X : L²₊) : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (completePairProfile q d X x : ℂ) := by
    filter_upwards [Lp.coeFn_add (coarseSection q X) (haarSection d X),
      coarseSection_coeFn q X, haarSection_coeFn d X] with x hadd hc hd
    rw [hadd]
    simp only [Pi.add_apply, hc, hd, completePairProfile, Complex.ofReal_add]
  have hz (x : ℝ) (hx : x < 0) : completePairProfile q d X x = 0 := by
    rw [completePairProfile, averageSectionProfile_zero_neg q X hx,
      haarSectionProfile_zero_neg d X hx, add_zero]
  have he : (halfLineExtend (coarseSection q X + haarSection d X) : ℝ → ℂ) =ᵐ[volume]
      fun x => (completePairProfile q d X x : ℂ) := by
    refine (halfLineExtend_coeFn _).trans
      ((indicator_ae_eq_of_halfLine hrep).trans (Eventually.of_forall ?_))
    intro x
    by_cases hx : x ∈ Ici (0 : ℝ)
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx, hz x (lt_of_not_ge hx), Complex.ofReal_zero]
  exact inner_shift_real_representatives _ _ _ _ hrep he hz t

/-- The mixed coefficient is exactly the sum of both original prime-two correlations. -/
theorem primeTwoMixedSource_eq_integrals (d q : ℕ → ℝ) (Y X : ℕ) :
    primeTwoMixedSource d q Y X =
      (2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        ((∫ x, haarSectionProfile d Y x * averageSectionProfile q X (x + Real.log 2)) +
          ∫ x, averageSectionProfile q X x * haarSectionProfile d Y (x + Real.log 2)) := by
  rw [primeTwoMixedSource, inner_shift_haar_coarse_profiles, inner_shift_coarse_haar_profiles]

/-- Subtracting the two diagonal prime-two terms leaves exactly the actual mixed block. -/
theorem primeTwoMixedSource_eq_polarized_integral (d q : ℕ → ℝ) (X : ℕ) :
    (2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        (∫ x, completePairProfile q d X x * completePairProfile q d X (x + Real.log 2)) -
      (2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        (∫ x, averageSectionProfile q X x * averageSectionProfile q X (x + Real.log 2)) -
      (2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        (∫ x, haarSectionProfile d X x * haarSectionProfile d X (x + Real.log 2)) =
      primeTwoMixedSource d q X X := by
  rw [← inner_shift_completePairProfile, ← inner_shift_coarse_profile,
    ← inner_shift_haarSectionProfile, primeTwoMixedSource, map_add,
    inner_add_left, inner_add_right, inner_add_right]
  simp only [Complex.add_re]
  ring

/-- Original Gamma energy pays the literal mixed prime-two integrals above a fixed detail index. -/
theorem exists_high_detail_gamma_pays_original_primeTwo :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (Y : ℕ),
      let c := fun a => if A ≤ a then d a else 0
      let X := 2 * Y + 1
      |(2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        ((∫ x, haarSectionProfile c X x * averageSectionProfile q X (x + Real.log 2)) +
          ∫ x, averageSectionProfile q X x * haarSectionProfile c X (x + Real.log 2))| ≤
        levyEnergy (completePairProfile q c X) := by
  obtain ⟨A, hA, hpay⟩ := exists_high_detail_gamma_pays_primeTwo
  refine ⟨A, hA, ?_⟩
  intro d q Y
  dsimp only
  rw [← primeTwoMixedSource_eq_integrals]
  exact hpay d q Y

/-- The original mixed prime-two tail is small relative to the untruncated Gamma source. -/
theorem exists_original_primeTwo_gamma_small_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (Y : ℕ),
      let c := fun a => if A ≤ a then d a else 0
      let X := 2 * Y + 1
      |(2 * ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
        ((∫ x, haarSectionProfile c X x * averageSectionProfile q X (x + Real.log 2)) +
          ∫ x, averageSectionProfile q X x * haarSectionProfile c X (x + Real.log 2))| ≤
        δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA, hpay⟩ := exists_primeTwo_gamma_small_tail hδ
  refine ⟨A, hA, ?_⟩
  intro d q Y
  dsimp only
  rw [← primeTwoMixedSource_eq_integrals]
  exact hpay d q Y

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.primeTwoMixedSource_eq_integrals
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.primeTwoMixedSource_eq_polarized_integral
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_high_detail_gamma_pays_original_primeTwo
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_original_primeTwo_gamma_small_tail
