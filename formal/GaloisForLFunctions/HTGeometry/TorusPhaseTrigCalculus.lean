import GaloisForLFunctions.HTGeometry.TorusTranslateDifference

/-!
# Coordinate calculus of torus characters on the vector model

A character of the unit torus lifts to the vector model as the exponential of a continuous linear
phase, so every coordinate partial derivative of the lift multiplies it by the corresponding
frequency.  Iterating along a list of coordinates multiplies it by the product of the frequencies
along that list.

Characters integrate to one or to zero over the fundamental box according to whether their
frequency vanishes, because the box integral factors into one-dimensional exponential integrals.
Consequently the box integral of the squared modulus of a finite character combination is the sum
of the products of coefficients over pairs of equal frequencies, which is the Parseval identity in
the form that tolerates repeated frequencies.
-/

open MeasureTheory Complex UnitAddTorus Set

open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section CharacterLift

/-- The phase of a torus character, as a continuous real-linear functional on the vector model. -/
def charPhase (n : d → ℤ) : (d → ℝ) →L[ℝ] ℂ :=
  ∑ i : d, (2 * Real.pi * I * (n i : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) i))

theorem charPhase_apply (n : d → ℤ) (x : d → ℝ) :
    charPhase n x = ∑ i : d, (2 * Real.pi * I * (n i : ℂ)) * (x i : ℂ) := by
  simp [charPhase]

theorem charPhase_single (n : d → ℤ) (i : d) :
    charPhase n (Pi.single i (1 : ℝ)) = 2 * Real.pi * I * (n i : ℂ) := by
  rw [charPhase_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
    simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The lift of a torus character to the vector model. -/
def charLift (n : d → ℤ) (x : d → ℝ) : ℂ := Complex.exp (charPhase n x)

theorem charLift_apply_zero (n : d → ℤ) : charLift n (0 : d → ℝ) = 1 := by
  simp [charLift, charPhase_apply]

theorem charLift_zero_index (x : d → ℝ) : charLift (0 : d → ℤ) x = 1 := by
  simp [charLift, charPhase_apply]

theorem charLift_add_index (n m : d → ℤ) (x : d → ℝ) :
    charLift (n + m) x = charLift n x * charLift m x := by
  rw [charLift, charLift, charLift, ← Complex.exp_add]
  congr 1
  rw [charPhase_apply, charPhase_apply, charPhase_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add]
  ring

theorem charLift_neg_index (n : d → ℤ) (x : d → ℝ) :
    charLift (-n) x = (starRingEnd ℂ) (charLift n x) := by
  rw [charLift, charLift, ← Complex.exp_conj]
  congr 1
  rw [charPhase_apply, charPhase_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.neg_apply, Int.cast_neg, map_mul, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat, map_intCast]
  ring

theorem norm_charLift (n : d → ℤ) (x : d → ℝ) : ‖charLift n x‖ = 1 := by
  rw [charLift, Complex.norm_exp, charPhase_apply]
  have hre : (∑ i : d, (2 * (Real.pi : ℂ) * I * (n i : ℂ)) * (x i : ℂ)).re = 0 := by
    rw [Complex.re_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

theorem charLift_sub_right (n : d → ℤ) (x a : d → ℝ) :
    charLift n (x - a) = charLift n x * charLift n (-a) := by
  rw [charLift, charLift, charLift, ← Complex.exp_add]
  congr 1
  rw [charPhase_apply, charPhase_apply, charPhase_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.neg_apply, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem charLift_eq_mFourier (n : d → ℤ) (x : d → ℝ) :
    charLift n x = mFourier n (torusProj x) := by
  have hrhs : mFourier n (torusProj x) =
      ∏ i : d, Complex.exp (2 * Real.pi * I * ((n i : ℤ) : ℂ) * ((x i : ℝ) : ℂ)) := by
    simp only [mFourier, ContinuousMap.coe_mk, torusProj]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [hrhs, charLift, charPhase_apply, Complex.exp_sum]


theorem charLift_pow (n : d → ℤ) (x : d → ℝ) (m : ℕ) :
    charLift n x ^ m = charLift ((m : ℤ) • n) x := by
  induction m with
  | zero => simp [charLift_zero_index]
  | succ m ih =>
      rw [pow_succ, ih, ← charLift_add_index]
      congr 1
      push_cast
      module

theorem charLift_prod_index {ι : Type*} (s : Finset ι) (n : ι → (d → ℤ)) (x : d → ℝ) :
    (∏ i ∈ s, charLift (n i) x) = charLift (∑ i ∈ s, n i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [charLift_zero_index]
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← charLift_add_index]

end CharacterLift

section PartialDerivative

/-- The coordinate partial derivative of a function on the vector model. -/
def pderiv (i : d) (G : (d → ℝ) → ℂ) : (d → ℝ) → ℂ :=
  fun x => fderiv ℝ G x (Pi.single i (1 : ℝ))

/-- Iterated coordinate partial derivatives along a list of coordinates. -/
def pderivList : List d → ((d → ℝ) → ℂ) → ((d → ℝ) → ℂ)
  | [], G => G
  | i :: l, G => pderiv i (pderivList l G)

@[simp]
theorem pderivList_nil (G : (d → ℝ) → ℂ) : pderivList [] G = G := rfl

@[simp]
theorem pderivList_cons (i : d) (l : List d) (G : (d → ℝ) → ℂ) :
    pderivList (i :: l) G = pderiv i (pderivList l G) := rfl

/-- A finite combination of character lifts. -/
def trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) (x : d → ℝ) : ℂ :=
  ∑ p ∈ P, a p * charLift (ν p) x

theorem hasFDerivAt_charLift (n : d → ℤ) (x : d → ℝ) :
    HasFDerivAt (charLift n) (charLift n x • charPhase n) x :=
  ((charPhase n).hasFDerivAt (x := x)).cexp

theorem hasFDerivAt_trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ)
    (x : d → ℝ) :
    HasFDerivAt (trigLift P ν a)
      (∑ p ∈ P, (a p * charLift (ν p) x) • charPhase (ν p)) x := by
  have hterm : ∀ p ∈ P, HasFDerivAt (fun y => a p * charLift (ν p) y)
      ((a p * charLift (ν p) x) • charPhase (ν p)) x := by
    intro p _
    have hp := (hasFDerivAt_charLift (ν p) x).const_mul (a p)
    rwa [smul_smul] at hp
  have hfun : (∑ p ∈ P, fun y : d → ℝ => a p * charLift (ν p) y) = trigLift P ν a := by
    funext y
    rw [trigLift, Finset.sum_apply]
  rw [← hfun]
  exact HasFDerivAt.sum hterm

theorem pderiv_trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) (i : d) :
    pderiv i (trigLift P ν a) =
      trigLift P ν (fun p => (2 * Real.pi * I * ((ν p) i : ℂ)) * a p) := by
  funext x
  rw [pderiv, (hasFDerivAt_trigLift P ν a x).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, charPhase_single]
  rw [trigLift]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem pderivList_trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) :
    ∀ l : List d, pderivList l (trigLift P ν a) =
      trigLift P ν (fun p => (l.map fun i => (2 * Real.pi * I * ((ν p) i : ℂ))).prod * a p)
  | [] => by
      rw [pderivList_nil]
      exact congrArg (trigLift P ν) (funext fun p => by simp)
  | i :: l => by
      rw [pderivList_cons, pderivList_trigLift P ν a l, pderiv_trigLift]
      exact congrArg (trigLift P ν) (funext fun p => by rw [List.map_cons, List.prod_cons]; ring)

end PartialDerivative

section BoxIntegral

theorem integral_Ioc_exp (m : ℤ) :
    (∫ t in Ioc (0 : ℝ) 1, Complex.exp (2 * Real.pi * I * (m : ℂ) * (t : ℂ))) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [if_neg hm]
    have hc : (2 * (Real.pi : ℂ) * I * (m : ℂ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, not_or]
      refine ⟨⟨⟨two_ne_zero, ?_⟩, Complex.I_ne_zero⟩, ?_⟩
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hm
    have hint := intervalIntegral.integral_of_le (a := (0 : ℝ)) (b := 1) zero_le_one
      (f := fun t : ℝ => Complex.exp (2 * Real.pi * I * (m : ℂ) * (t : ℂ)))
      (μ := volume)
    rw [← hint, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 : ℂ) * (Real.pi : ℂ) * I * (m : ℂ) * ((1 : ℝ) : ℂ)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    have h0 : Complex.exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    rw [h1, h0, sub_self, zero_div]

theorem integral_box_charLift (n : d → ℤ) :
    (∫ x in torusBox d, charLift n x) = if n = 0 then 1 else 0 := by
  have hprod : ∀ x : d → ℝ, charLift n x =
      ∏ i : d, Complex.exp (2 * Real.pi * I * ((n i : ℤ) : ℂ) * ((x i : ℝ) : ℂ)) := by
    intro x
    rw [charLift, charPhase_apply, Complex.exp_sum]
  simp_rw [hprod]
  rw [torusBox_eq_pi, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (𝕜 := ℂ)
      (f := fun (i : d) (t : ℝ) => Complex.exp (2 * Real.pi * I * ((n i : ℤ) : ℂ) * (t : ℂ)))]
  simp_rw [integral_Ioc_exp]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg hn]
    obtain ⟨i, hi⟩ : ∃ i : d, n i ≠ 0 := by
      by_contra hcon
      exact hn (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem integral_box_charLift_mul_conj (n m : d → ℤ) :
    (∫ x in torusBox d, charLift n x * (starRingEnd ℂ) (charLift m x)) =
      if n = m then 1 else 0 := by
  have hpt : ∀ x : d → ℝ,
      charLift n x * (starRingEnd ℂ) (charLift m x) = charLift (n - m) x := by
    intro x
    rw [← charLift_neg_index, ← charLift_add_index, ← sub_eq_add_neg]
  simp_rw [hpt]
  rw [integral_box_charLift]
  by_cases h : n = m
  · subst h; simp
  · have hne : n - m ≠ 0 := fun hcon => h (sub_eq_zero.mp hcon)
    rw [if_neg hne, if_neg h]

end BoxIntegral


section Parseval

theorem continuous_charLift (n : d → ℤ) : Continuous (charLift (d := d) n) :=
  Complex.continuous_exp.comp (charPhase n).continuous

theorem continuous_trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) :
    Continuous (trigLift P ν a) :=
  continuous_finsetSum P fun p _ => continuous_const.mul (continuous_charLift (ν p))

theorem integrableOn_box_of_bounded {G : (d → ℝ) → ℂ} (hG : Continuous G) {C : ℝ}
    (hC : ∀ x, ‖G x‖ ≤ C) : IntegrableOn G (torusBox d) volume := by
  haveI := isFiniteMeasure_restrict_torusBox (d := d)
  exact Integrable.of_bound hG.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem integrableOn_box_charLift_mul_conj (n m : d → ℤ) :
    IntegrableOn (fun x => charLift (d := d) n x * (starRingEnd ℂ) (charLift m x))
      (torusBox d) volume := by
  refine integrableOn_box_of_bounded
    ((continuous_charLift n).mul (Complex.continuous_conj.comp (continuous_charLift m)))
    (C := 1) fun x => ?_
  rw [norm_mul, RCLike.norm_conj, norm_charLift, norm_charLift, mul_one]

theorem integrableOn_box_charLift (n : d → ℤ) :
    IntegrableOn (charLift (d := d) n) (torusBox d) volume :=
  integrableOn_box_of_bounded (continuous_charLift n) (C := 1) fun x => le_of_eq (norm_charLift n x)

/-- **Mean of a character combination.**  Only the zero frequencies survive. -/
theorem integral_box_trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) :
    (∫ x in torusBox d, trigLift P ν a x) = ∑ p ∈ P with ν p = 0, a p := by
  classical
  simp only [trigLift]
  rw [integral_finsetSum P fun p _ => (integrableOn_box_charLift (ν p)).const_mul (a p)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul, integral_box_charLift]
  by_cases h : ν p = 0
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **Parseval with repeated frequencies.**  The mean square of a finite character combination is
the sum of the coefficient products over pairs of equal frequencies. -/
theorem ofReal_integral_box_normSq_trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ))
    (a : ι → ℂ) :
    ((∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then a p * (starRingEnd ℂ) (a q) else 0 := by
  classical
  have hmulconj : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.sq_norm z
  have hpt : ∀ x : d → ℝ, ((‖trigLift P ν a x‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ q ∈ P,
        (a p * (starRingEnd ℂ) (a q)) *
          (charLift (ν p) x * (starRingEnd ℂ) (charLift (ν q) x)) := by
    intro x
    rw [hmulconj, trigLift, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul]
    ring
  have hbdd : ∀ x : d → ℝ, ‖trigLift P ν a x‖ ≤ ∑ p ∈ P, ‖a p‖ := by
    intro x
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, norm_charLift, mul_one]
  have hint : IntegrableOn (fun x => ‖trigLift P ν a x‖ ^ 2) (torusBox d) volume := by
    haveI := isFiniteMeasure_restrict_torusBox (d := d)
    refine Integrable.of_bound ?_ ((∑ p ∈ P, ‖a p‖) ^ 2) ?_
    · exact (((continuous_trigLift P ν a).norm).pow 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbdd x) 2
  rw [show ((∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2 : ℝ) : ℂ)
      = Complex.ofRealCLM (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2) from rfl,
    ← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint]
  simp only [Complex.ofRealCLM_apply]
  simp_rw [hpt]
  rw [integral_finsetSum P fun p _ => ?_]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum P fun q _ => ?_]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_const_mul, integral_box_charLift_mul_conj]
      by_cases h : ν p = ν q
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    · exact (integrableOn_box_charLift_mul_conj (ν p) (ν q)).const_mul _
  · exact integrable_finsetSum P fun q _ =>
      (integrableOn_box_charLift_mul_conj (ν p) (ν q)).const_mul _

/-- **Crude Parseval bound.**  The mean square is at most the squared coefficient ceiling times the
number of pairs of equal frequencies. -/
theorem integral_box_normSq_trigLift_le {ι : Type*} [DecidableEq ι] (P : Finset ι)
    (ν : ι → (d → ℤ)) (a : ι → ℂ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p ∈ P, ‖a p‖ ≤ M) :
    (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2) ≤
      M ^ 2 * (((P ×ˢ P).filter fun pq => ν pq.1 = ν pq.2).card : ℝ) := by
  classical
  have hnn : 0 ≤ ∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have heq := ofReal_integral_box_normSq_trigLift P ν a
  have hnorm : (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2) =
      ‖∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then a p * (starRingEnd ℂ) (a q) else 0‖ := by
    rw [← heq, Complex.norm_real, Real.norm_of_nonneg hnn]
  rw [hnorm, ← Finset.sum_product']
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ pq ∈ P ×ˢ P, ‖if ν pq.1 = ν pq.2 then a pq.1 * (starRingEnd ℂ) (a pq.2) else 0‖
      ≤ ∑ pq ∈ P ×ˢ P, if ν pq.1 = ν pq.2 then M ^ 2 else 0 := by
        refine Finset.sum_le_sum fun pq hpq => ?_
        by_cases h : ν pq.1 = ν pq.2
        · rw [if_pos h, if_pos h, norm_mul, RCLike.norm_conj, sq]
          exact mul_le_mul (hM _ (Finset.mem_product.mp hpq).1)
            (hM _ (Finset.mem_product.mp hpq).2) (norm_nonneg _) hM0
        · rw [if_neg h, if_neg h, norm_zero]
    _ = M ^ 2 * (((P ×ˢ P).filter fun pq => ν pq.1 = ν pq.2).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]


/-- **Parseval at distinct frequencies.**  When the frequencies are pairwise distinct the mean
square of a character combination is the sum of the squared coefficient moduli. -/
theorem integral_box_normSq_trigLift_of_injOn {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ))
    (a : ι → ℂ) (hinj : ∀ p ∈ P, ∀ q ∈ P, ν p = ν q → p = q) :
    (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2) = ∑ p ∈ P, ‖a p‖ ^ 2 := by
  classical
  have hcomplex := ofReal_integral_box_normSq_trigLift P ν a
  have hdiag : (∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then a p * (starRingEnd ℂ) (a q) else 0) =
      ∑ p ∈ P, ((‖a p‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_eq_single p]
    · rw [if_pos rfl, Complex.mul_conj]
      norm_cast
      exact (Complex.sq_norm (a p)).symm
    · intro q hq hqp
      rw [if_neg]
      intro hcon
      exact hqp (hinj q hq p hp hcon.symm)
    · intro hcon
      exact absurd hp hcon
  rw [hdiag, ← Complex.ofReal_sum] at hcomplex
  exact_mod_cast hcomplex

end Parseval

end GaloisForLFunctions.HTGeometry
