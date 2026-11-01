import GaloisForLFunctions.RHTower.SelbergScatteringPolynomialXiObstruction
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rational reality on the native scattering parabola

A reduced rational function is real at infinitely many regular points of
`3/16 + t²/4 + it/4` only when it is a real constant. Coprimeness transfers
Schwarz reflection to the denominator; polynomial reality rigidity then
forces both denominator and numerator to be constant. Otherwise the number of
regular real matches is at most twice the sum of the reduced degrees; a linear
fractional transform attains four. Arbitrarily high genuine critical scattering
poles lie outside the finite real-match and denominator-zero sets.
-/

open Complex Polynomial Set
open RHTower.SelbergScatteringPolynomialReality

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ScatteringRationalReality

private theorem leadingCoeff_casimir : casimirPolynomial.leadingCoeff = (1 / 4 : ℂ) := by
  change casimirPolynomial.coeff casimirPolynomial.natDegree = _
  rw [natDegree_casimirPolynomial]
  norm_num [casimirPolynomial]

/-- A reduced monic-denominator fraction real on infinitely many native critical Casimirs
has denominator one and a real constant numerator. -/
theorem constant_pair_of_infinite_real_locus (P Q : ℂ[X]) (hcop : IsCoprime P Q)
    (hmonic : Q.Monic)
    (hinf : Set.Infinite {t : ℝ | Q.eval (criticalCasimir t) ≠ 0 ∧
      (P.eval (criticalCasimir t) / Q.eval (criticalCasimir t)).im = 0}) :
    ∃ c : ℝ, P = C (c : ℂ) ∧ Q = 1 := by
  let A := P.comp casimirPolynomial
  let B := Q.comp casimirPolynomial
  have heA (z : ℂ) : A.eval z = P.eval (criticalCasimir z) := by simp [A]
  have heB (z : ℂ) : B.eval z = Q.eval (criticalCasimir z) := by simp [B]
  have hAB : IsCoprime A B :=
    hcop.map (Polynomial.eval₂RingHom Polynomial.C casimirPolynomial)
  have hlead : B.leadingCoeff = (1 / 4 : ℂ) ^ Q.natDegree := by
    change (Q.comp casimirPolynomial).leadingCoeff = _
    rw [Polynomial.leadingCoeff_comp (by rw [natDegree_casimirPolynomial]; norm_num),
      hmonic.leadingCoeff, leadingCoeff_casimir, one_mul]
  have hreal : star B.leadingCoeff = B.leadingCoeff := by rw [hlead]; simp
  have hB : B ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (by
    rw [hlead]
    exact pow_ne_zero _ (by norm_num))
  have hBmap : B.map (starRingEnd ℂ) = B := by
    have hcross : A.map (starRingEnd ℂ) * B = A * B.map (starRingEnd ℂ) := by
      apply Polynomial.eq_of_infinite_eval_eq
      apply (hinf.image Complex.ofReal_injective.injOn).mono
      rintro _ ⟨t, ⟨ht, hr⟩, rfl⟩
      change (A.map (starRingEnd ℂ) * B).eval (t : ℂ) =
        (A * B.map (starRingEnd ℂ)).eval (t : ℂ)
      have hmA := Polynomial.eval_map_apply (p := A) (starRingEnd ℂ) (t : ℂ)
      have hmB := Polynomial.eval_map_apply (p := B) (starRingEnd ℂ) (t : ℂ)
      simp only [Complex.conj_ofReal] at hmA hmB
      rw [Polynomial.eval_mul, Polynomial.eval_mul, hmA, hmB]
      have hval : star (A.eval (t : ℂ) / B.eval (t : ℂ)) =
          A.eval (t : ℂ) / B.eval (t : ℂ) := by
        simpa only [heA, heB, Complex.star_def] using Complex.conj_eq_iff_im.mpr hr
      rw [star_div₀] at hval
      have htB : B.eval (t : ℂ) ≠ 0 := by simpa only [heB] using ht
      exact (div_eq_div_iff (by simpa using htB) htB).mp hval
    have hdvd : B ∣ B.map (starRingEnd ℂ) := by
      apply hAB.symm.dvd_of_dvd_mul_right
      refine ⟨A.map (starRingEnd ℂ), ?_⟩
      simpa only [mul_comm] using hcross.symm
    obtain ⟨D, hD⟩ := hdvd
    have hBm : B.map (starRingEnd ℂ) ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (by
      rw [Polynomial.leadingCoeff_map]
      change star B.leadingCoeff ≠ 0
      rw [hreal]
      exact Polynomial.leadingCoeff_ne_zero.mpr hB)
    have hD0 : D ≠ 0 := by
      intro h0
      apply hBm
      rw [hD, h0, mul_zero]
    have hdegD : D.natDegree = 0 := by
      have h := Polynomial.natDegree_map (p := B) (starRingEnd ℂ)
      rw [hD, Polynomial.natDegree_mul hB hD0] at h
      omega
    obtain ⟨d, hd⟩ := Polynomial.natDegree_eq_zero.mp hdegD
    have hl := congrArg Polynomial.leadingCoeff hD
    rw [Polynomial.leadingCoeff_map, Polynomial.leadingCoeff_mul, ← hd,
      Polynomial.leadingCoeff_C] at hl
    change star B.leadingCoeff = B.leadingCoeff * d at hl
    rw [hreal] at hl
    have hd1 : d = 1 := mul_left_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hB)
      (hl.symm.trans (mul_one B.leadingCoeff).symm)
    simpa only [← hd, hd1, Polynomial.C_1, mul_one] using hD
  have hQreal (t : ℝ) : (Q.eval (criticalCasimir t)).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    have h := Polynomial.eval_map_apply (p := B) (starRingEnd ℂ) (t : ℂ)
    simpa only [hBmap, Complex.conj_ofReal, heB] using h.symm
  obtain ⟨q, hq⟩ := constant_of_infinite_real_locus Q
    (Set.infinite_univ.mono (fun t _ => hQreal t))
  have hqone : (q : ℂ) = 1 := by
    simpa only [hq, Polynomial.leadingCoeff_C] using hmonic.leadingCoeff
  have hQone : Q = 1 := by rw [hq, hqone, Polynomial.C_1]
  have hPinf : Set.Infinite {t : ℝ | (P.eval (criticalCasimir t)).im = 0} := by
    simpa [hQone] using hinf
  obtain ⟨c, hc⟩ := constant_of_infinite_real_locus P hPinf
  exact ⟨c, hc, hQone⟩

/-- Regular critical-line parameters where a rational scattering transport is real. -/
def realLocus (r : RatFunc ℂ) : Set ℝ :=
  {t | r.denom.eval (criticalCasimir t) ≠ 0 ∧
    (r.num.eval (criticalCasimir t) / r.denom.eval (criticalCasimir t)).im = 0}

/-- Infinite exact reality forces a real constant rational transport. -/
theorem constant_of_infinite_realLocus (r : RatFunc ℂ) (h : (realLocus r).Infinite) :
    ∃ c : ℝ, r = algebraMap ℂ (RatFunc ℂ) (c : ℂ) := by
  obtain ⟨c, hp, hq⟩ := constant_pair_of_infinite_real_locus r.num r.denom
    r.isCoprime_num_denom r.monic_denom h
  refine ⟨c, ?_⟩
  rw [← RatFunc.num_div_denom r, hp, hq, map_one, div_one]
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- Every rational transport other than a real constant has finitely many regular real values. -/
theorem finite_realLocus (r : RatFunc ℂ)
    (h : ¬ ∃ c : ℝ, r = algebraMap ℂ (RatFunc ℂ) (c : ℂ)) : (realLocus r).Finite := by
  rw [← Set.not_infinite]
  exact fun hi => h (constant_of_infinite_realLocus r hi)


/-- Real constants are the complete rational reality locus classification. -/
theorem infinite_realLocus_iff (r : RatFunc ℂ) :
    (realLocus r).Infinite ↔ ∃ c : ℝ, r = algebraMap ℂ (RatFunc ℂ) (c : ℂ) := by
  constructor
  · exact constant_of_infinite_realLocus r
  · rintro ⟨c, rfl⟩
    have h : algebraMap ℂ (RatFunc ℂ) (c : ℂ) =
        algebraMap ℂ[X] (RatFunc ℂ) (C (c : ℂ)) := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rw [h]
    simpa [realLocus, RatFunc.num_algebraMap, RatFunc.denom_algebraMap] using
      (Set.infinite_univ : (Set.univ : Set ℝ).Infinite)

/-- The polynomial measuring failure of Schwarz reflection after the Casimir substitution. -/
def realityPolynomial (r : RatFunc ℂ) : ℂ[X] :=
  let A := r.num.comp casimirPolynomial
  let B := r.denom.comp casimirPolynomial
  A.map (starRingEnd ℂ) * B - A * B.map (starRingEnd ℂ)

private theorem eval_conj_real (P : ℂ[X]) (t : ℝ) :
    (P.map (starRingEnd ℂ)).eval (t : ℂ) = star (P.eval (t : ℂ)) := by
  simpa only [Complex.conj_ofReal, Complex.star_def] using
    Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (t : ℂ)

private theorem eval_cross_zero_iff (A B : ℂ[X]) (t : ℝ) (hB : B.eval (t : ℂ) ≠ 0) :
    (A.map (starRingEnd ℂ) * B - A * B.map (starRingEnd ℂ)).eval (t : ℂ) = 0 ↔
      (A.eval (t : ℂ) / B.eval (t : ℂ)).im = 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_conj_real, eval_conj_real, sub_eq_zero, ← Complex.conj_eq_iff_im]
  change star (A.eval (t : ℂ)) * B.eval (t : ℂ) =
      A.eval (t : ℂ) * star (B.eval (t : ℂ)) ↔
    star (A.eval (t : ℂ) / B.eval (t : ℂ)) = A.eval (t : ℂ) / B.eval (t : ℂ)
  rw [star_div₀, div_eq_div_iff (by simpa using hB) hB]

private theorem comp_casimir_ne_zero (P : ℂ[X]) (hP : P ≠ 0) :
    P.comp casimirPolynomial ≠ 0 := by
  intro h
  rcases Polynomial.comp_eq_zero_iff.mp h with h0 | ⟨_, hc⟩
  · exact hP h0
  · have hd := natDegree_casimirPolynomial
    rw [hc] at hd
    norm_num at hd

/-- A rational transport other than a real constant has a nonzero reality polynomial. -/
theorem realityPolynomial_ne_zero (r : RatFunc ℂ)
    (h : ¬ ∃ c : ℝ, r = algebraMap ℂ (RatFunc ℂ) (c : ℂ)) : realityPolynomial r ≠ 0 := by
  intro hzero
  let A := r.num.comp casimirPolynomial
  let B := r.denom.comp casimirPolynomial
  have hB : B ≠ 0 := comp_casimir_ne_zero r.denom r.denom_ne_zero
  have hf : {t : ℝ | B.eval (t : ℂ) = 0}.Finite :=
    Set.Finite.preimage Complex.ofReal_injective.injOn (Polynomial.finite_setOf_isRoot hB)
  apply h
  apply constant_of_infinite_realLocus r
  apply (Set.infinite_univ.sdiff hf).mono
  intro t ht
  have htB : B.eval (t : ℂ) ≠ 0 := ht.2
  have he : (A.map (starRingEnd ℂ) * B - A * B.map (starRingEnd ℂ)).eval (t : ℂ) = 0 := by
    change (realityPolynomial r).eval (t : ℂ) = 0
    rw [hzero, Polynomial.eval_zero]
  have hr := (eval_cross_zero_iff A B t htB).mp he
  exact ⟨by simpa only [B, Polynomial.eval_comp, eval_casimirPolynomial] using htB,
    by simpa only [A, B, Polynomial.eval_comp, eval_casimirPolynomial] using hr⟩

/-- Degree of the real-interpolation obstruction. -/
theorem natDegree_realityPolynomial_le (r : RatFunc ℂ) :
    (realityPolynomial r).natDegree ≤ 2 * (r.num.natDegree + r.denom.natDegree) := by
  let A := r.num.comp casimirPolynomial
  let B := r.denom.comp casimirPolynomial
  have ha : A.natDegree = r.num.natDegree * 2 := by
    change (r.num.comp casimirPolynomial).natDegree = _
    rw [Polynomial.natDegree_comp, natDegree_casimirPolynomial]
  have hb : B.natDegree = r.denom.natDegree * 2 := by
    change (r.denom.comp casimirPolynomial).natDegree = _
    rw [Polynomial.natDegree_comp, natDegree_casimirPolynomial]
  have h₁ : (A.map (starRingEnd ℂ) * B).natDegree ≤
      2 * (r.num.natDegree + r.denom.natDegree) := by
    calc
      _ ≤ (A.map (starRingEnd ℂ)).natDegree + B.natDegree := Polynomial.natDegree_mul_le
      _ = _ := by rw [Polynomial.natDegree_map, ha, hb]; omega
  have h₂ : (A * B.map (starRingEnd ℂ)).natDegree ≤
      2 * (r.num.natDegree + r.denom.natDegree) := by
    calc
      _ ≤ A.natDegree + (B.map (starRingEnd ℂ)).natDegree := Polynomial.natDegree_mul_le
      _ = _ := by rw [Polynomial.natDegree_map, ha, hb]; omega
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le h₁ h₂)

/-- A rational transform can be exactly real at no more than twice the sum of its reduced degrees. -/
theorem ncard_realLocus_le (r : RatFunc ℂ)
    (h : ¬ ∃ c : ℝ, r = algebraMap ℂ (RatFunc ℂ) (c : ℂ)) :
    (realLocus r).ncard ≤ 2 * (r.num.natDegree + r.denom.natDegree) := by
  classical
  have hD := realityPolynomial_ne_zero r h
  have hs : Complex.ofReal '' realLocus r ⊆ ((realityPolynomial r).roots.toFinset : Set ℂ) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hD]
    apply (eval_cross_zero_iff (r.num.comp casimirPolynomial)
      (r.denom.comp casimirPolynomial) t
      (by simpa only [Polynomial.eval_comp, eval_casimirPolynomial] using ht.1)).mpr
    simpa only [Polynomial.eval_comp, eval_casimirPolynomial] using ht.2
  rw [← Set.ncard_image_of_injective (realLocus r) Complex.ofReal_injective]
  calc
    _ ≤ (((realityPolynomial r).roots.toFinset : Set ℂ)).ncard := Set.ncard_le_ncard hs
    _ = (realityPolynomial r).roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ (realityPolynomial r).roots.card := Multiset.toFinset_card_le _
    _ ≤ (realityPolynomial r).natDegree := Polynomial.card_roots' _
    _ ≤ _ := natDegree_realityPolynomial_le r


/-- A degree-one rational transform attaining four real critical Casimirs. -/
def sharpMobius (z : ℂ) : ℂ := I * (z - 3 / 2) / (z - 1 / 2)

private theorem criticalCasimir_ne_half (t : ℝ) : criticalCasimir t - 1 / 2 ≠ 0 := by
  have hi : (criticalCasimir t - 1 / 2).im = t / 4 := by
    norm_num [criticalCasimir, pow_two]
  intro h
  rw [h, Complex.zero_im] at hi
  have ht : t = 0 := by linarith only [hi]
  subst t
  norm_num [criticalCasimir] at h

/-- The four matching parameters are exactly the roots of two positive quadratic levels. -/
theorem sharpMobius_real_iff (t : ℝ) :
    (sharpMobius (criticalCasimir t)).im = 0 ↔ t ^ 2 = 7 / 4 ∨ t ^ 2 = 15 / 4 := by
  have hn : normSq (criticalCasimir t - 1 / 2) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (criticalCasimir_ne_half t)).ne'
  have hnum : (I * (criticalCasimir t - 3 / 2)).im * (criticalCasimir t - 1 / 2).re -
      (I * (criticalCasimir t - 3 / 2)).re * (criticalCasimir t - 1 / 2).im =
        (4 * t ^ 2 - 7) * (4 * t ^ 2 - 15) / 256 := by
    norm_num [criticalCasimir, pow_two]
    ring
  rw [sharpMobius, Complex.div_im, ← sub_div, hnum,
    div_eq_zero_iff, div_eq_zero_iff]
  simp only [hn, or_false, show (256 : ℝ) ≠ 0 by norm_num, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linarith only [h]
    · right; linarith only [h]
  · rintro (h | h)
    · left; linarith only [h]
    · right; linarith only [h]

/-- Four regular exact-real matches occur already for a linear fractional transform. -/
theorem sharpMobius_realLocus_ncard :
    {t : ℝ | (sharpMobius (criticalCasimir t)).im = 0}.ncard = 4 := by
  classical
  let a : ℝ := Real.sqrt (7 / 4)
  let b : ℝ := Real.sqrt (15 / 4)
  have ha : 0 < a := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0 < b := Real.sqrt_pos.mpr (by norm_num)
  have ha2 : a ^ 2 = 7 / 4 := Real.sq_sqrt (by norm_num)
  have hb2 : b ^ 2 = 15 / 4 := Real.sq_sqrt (by norm_num)
  have hab : a < b := by
    by_contra h
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt h)) (add_nonneg ha.le hb.le)
    nlinarith only [ha2, hb2, hp]
  have h₁ : a ≠ -a := by linarith only [ha]
  have h₂ : a ≠ b := hab.ne
  have h₃ : a ≠ -b := by linarith only [ha, hb]
  have h₄ : -a ≠ b := by linarith only [ha, hb]
  have h₅ : -a ≠ -b := by linarith only [hab]
  have h₆ : b ≠ -b := by linarith only [hb]
  let S : Finset ℝ := {a, -a, b, -b}
  have hc : S.card = 4 := by simp [S, h₁, h₂, h₃, h₄, h₅, h₆]
  have he : {t : ℝ | (sharpMobius (criticalCasimir t)).im = 0} = (S : Set ℝ) := by
    ext t
    rw [Set.mem_setOf_eq, sharpMobius_real_iff]
    change (t ^ 2 = 7 / 4 ∨ t ^ 2 = 15 / 4) ↔ t ∈ S
    rw [← ha2, ← hb2]
    simp only [S, Finset.mem_insert, Finset.mem_singleton, sq_eq_sq_iff_eq_or_eq_neg, or_assoc]
  rw [he, Set.ncard_coe_finset, hc]


open _root_.RHTower

private theorem finite_denominator_zero_locus (r : RatFunc ℂ) :
    {t : ℝ | r.denom.eval (criticalCasimir t) = 0}.Finite := by
  have h := Set.Finite.preimage Complex.ofReal_injective.injOn
    (Polynomial.finite_setOf_isRoot (comp_casimir_ne_zero r.denom r.denom_ne_zero))
  change {t : ℝ | (r.denom.comp casimirPolynomial).eval (t : ℂ) = 0}.Finite at h
  simpa only [Polynomial.IsRoot, Polynomial.eval_comp, eval_casimirPolynomial] using h

/-- A fixed non-real-constant rational transport is regular and nonreal at all sufficiently
high critical parameters. No uniform lower bound on the imaginary part is asserted. -/
theorem eventually_regular_nonreal (r : RatFunc ℂ)
    (h : ¬ ∃ c : ℝ, r = algebraMap ℂ (RatFunc ℂ) (c : ℂ)) :
    ∃ B : ℝ, ∀ t : ℝ, B < t → r.denom.eval (criticalCasimir t) ≠ 0 ∧
      (r.num.eval (criticalCasimir t) / r.denom.eval (criticalCasimir t)).im ≠ 0 := by
  obtain ⟨B, hB⟩ := ((finite_realLocus r h).union (finite_denominator_zero_locus r)).bddAbove
  refine ⟨B, fun t ht => ?_⟩
  have hreg : r.denom.eval (criticalCasimir t) ≠ 0 :=
    fun he => not_le_of_gt ht (hB (Or.inr he))
  exact ⟨hreg, fun hr => not_le_of_gt ht (hB (Or.inl ⟨hreg, hr⟩))⟩

/-- Arbitrarily high genuine critical-line scattering poles defeat every fixed rational
transport other than a real constant, at points where that transport is defined. -/
theorem exists_critical_pole_regular_nonreal_above (r : RatFunc ℂ)
    (h : ¬ ∃ c : ℝ, r = algebraMap ℂ (RatFunc ℂ) (c : ℂ)) (H : ℝ) :
    ∃ t : ℝ, H < t ∧ riemannZeta (linePt t) = 0 ∧
      meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering (t : ℂ) < 0 ∧
      r.denom.eval (criticalCasimir t) ≠ 0 ∧
      (r.num.eval (criticalCasimir t) / r.denom.eval (criticalCasimir t)).im ≠ 0 := by
  obtain ⟨B, hB⟩ := eventually_regular_nonreal r h
  obtain ⟨T0, _, hHardy⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨t, ht, hz⟩ := hHardy (max T0 (max B H + 1)) (le_max_left _ _)
  have hlarge : max B H + 1 ≤ t := (le_max_right _ _).trans ht.1
  have htB : B < t := by linarith only [hlarge, le_max_left B H]
  have htH : H < t := by linarith only [hlarge, le_max_right B H]
  obtain ⟨q, hq⟩ := exists_copy_of_line_zero hz
  refine ⟨t, htH, hz, ?_, hB t htB⟩
  simpa only [hq] using thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q

end GaloisForLFunctions.RenormalizedIntersectionTheory.ScatteringRationalReality

