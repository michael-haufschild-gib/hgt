import GaloisForLFunctions.RHTower.XiGaussianHeatArchPrimeHankel
import GaloisForLFunctions.HTGeometry.LeadingMinorSylvesterCriterion

/-!
# RH as positivity of explicit Hankel determinants

The heat moments `M_n(a) = Σ_q w_q^n e^{-a w_q}` are real (the zero set is symmetric under
`w ↦ w̄`).  Their Hankel determinants

`Δ_N(a) = det (M_{i+j}(a))_{i,j<N}`

decide RH: **RH holds iff `Δ_N(a) > 0` for every `N`**, for any one `a > 0`
(`riemannHypothesis_iff_heatMomentDet_pos`).  By `archPrimeMoment_eq` the entries are explicit
archimedean and prime data,

`M_n(a) = (−1)^n (Arch − Prime)^{(n)}(a)/π + 2 (−¼)^n e^{a/4}`,

so RH is the positivity of one explicit sequence of determinants built from the Gamma factor and the
von Mangoldt chirp (`riemannHypothesis_iff_archPrimeDet_pos`).

Under RH the Hankel form `Σ_q e^{-aλ_q}|P(λ_q)|²` is positive on nonzero polynomials, because there
are infinitely many distinct frequencies.  Conversely, positive leading minors give positive definite
leading blocks (Sylvester's criterion), hence a nonnegative Hankel form, hence RH by
`riemannHypothesis_iff_heatHankel_nonneg`.
-/

open Complex Filter Topology Set Polynomial Matrix
open GaloisForLFunctions.HTGeometry (leadingMatrix forall_posDef_leadingMatrix_iff)

namespace RHTower

noncomputable section

theorem infinite_xiZeroCopy : Infinite XiZeroCopy := by
  have hbase : Infinite XiDivisorSupport := Set.infinite_coe_iff.mpr xiDivisorSupport_infinite
  refine Infinite.of_injective (fun ρ : XiDivisorSupport => (⟨ρ, ⟨0, ?_⟩⟩ : XiZeroCopy)) ?_
  · have hpos := xi_divisor_pos_on_support ρ
    omega
  · intro a b h
    exact congrArg Sigma.fst h

/-- There are infinitely many distinct squared spectral points. -/
theorem infinite_range_xiHeatFrequency : (Set.range xiHeatFrequency).Infinite := by
  intro hfin
  obtain ⟨C, hC⟩ := (hfin.image Complex.re).bddAbove
  have hall : ∀ q, xiHeatTilt 0 q ≤ C := fun q => by
    have h := hC ⟨xiHeatFrequency q, ⟨q, rfl⟩, rfl⟩
    simpa [xiHeatTilt] using h
  have hfinU : (Set.univ : Set XiZeroCopy).Finite :=
    (finite_xiHeatTilt_le (C := C) (β := 0) le_rfl).subset fun q _ => hall q
  haveI := infinite_xiZeroCopy
  exact Set.infinite_univ hfinU

theorem conj_xiHeatMoment (n : ℕ) (a : ℝ) :
    (starRingEnd ℂ) (xiHeatMoment n a) = xiHeatMoment n a := by
  rw [xiHeatMoment, Complex.conj_tsum]
  conv_rhs => rw [← xiZeroCopyLineConjEquiv.tsum_eq]
  refine tsum_congr fun q => ?_
  rw [xiHeatFrequency_lineConj, map_mul, map_pow, ← Complex.exp_conj, map_mul, map_neg,
    Complex.conj_ofReal]

theorem im_xiHeatMoment (n : ℕ) (a : ℝ) : (xiHeatMoment n a).im = 0 :=
  Complex.conj_eq_iff_im.1 (conj_xiHeatMoment n a)

/-- The real heat-moment array `(i, j) ↦ M_{i+j}(a)`. -/
def heatMomentArray (a : ℝ) (i j : ℕ) : ℝ := (xiHeatMoment (i + j) a).re

theorem heatMomentArray_symm (a : ℝ) (i j : ℕ) : heatMomentArray a i j = heatMomentArray a j i := by
  rw [heatMomentArray, heatMomentArray, add_comm]

/-- The real part of the Hankel form is the sum of two real quadratic forms of the moment array. -/
theorem re_heatHankel_eq_quadratic {a : ℝ} (ha : 0 < a) (P : ℂ[X]) {N : ℕ}
    (hN : P.natDegree < N) :
    (heatHankel a P P).re =
      (∑ i : Fin N, ∑ j : Fin N, (P.coeff i).re * (P.coeff j).re * heatMomentArray a i j) +
      (∑ i : Fin N, ∑ j : Fin N, (P.coeff i).im * (P.coeff j).im * heatMomentArray a i j) := by
  rw [heatHankel_eq_moments ha,
    Polynomial.sum_over_range' _ (fun _ => by simp [Polynomial.sum_def]) N hN]
  rw [Finset.sum_congr rfl fun k _ => Polynomial.sum_over_range' P (fun _ => by simp) N hN]
  rw [Finset.sum_range, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have him := im_xiHeatMoment ((i : ℕ) + j) a
  simp only [mul_re, conj_re, conj_im, mul_im, him, heatMomentArray]
  ring

theorem coeff_sum_C_mul_X_pow {N : ℕ} (u : Fin N → ℝ) (k : ℕ) :
    (∑ i : Fin N, C ((u i : ℝ) : ℂ) * X ^ (i : ℕ)).coeff k =
      if h : k < N then ((u ⟨k, h⟩ : ℝ) : ℂ) else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hk
      exact hb (Fin.ext hk.symm)
    · intro hk; exact absurd (Finset.mem_univ _) hk
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hk
    exact h (hk ▸ i.2)

/-- **RH as positivity of the heat Hankel determinants.** -/
theorem riemannHypothesis_iff_heatMomentDet_pos {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ N, 0 < (leadingMatrix (heatMomentArray a) N).det := by
  rw [← forall_posDef_leadingMatrix_iff (heatMomentArray_symm a)]
  constructor
  · intro hRH N
    refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun u hu => ?_⟩
    · ext i j
      simp [leadingMatrix, conjTranspose_apply, heatMomentArray_symm]
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h
        exact absurd (Subsingleton.elim u 0) hu
      · exact h
    set P : ℂ[X] := ∑ i : Fin N, C ((u i : ℝ) : ℂ) * X ^ (i : ℕ) with hP
    have hcoeff := coeff_sum_C_mul_X_pow u
    have hdeg : P.natDegree < N := by
      by_cases hP0 : P = 0
      · rw [hP0, natDegree_zero]; exact hN
      · rw [natDegree_lt_iff_degree_lt hP0, degree_lt_iff_coeff_zero]
        intro m hm
        rw [hP, hcoeff, dif_neg (by omega)]
    have hquad : star u ⬝ᵥ (leadingMatrix (heatMomentArray a) N *ᵥ u) = (heatHankel a P P).re := by
      rw [re_heatHankel_eq_quadratic ha P hdeg]
      simp only [hP, hcoeff, Fin.is_lt, dif_pos, Fin.eta, ofReal_re, ofReal_im, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
      simp only [dotProduct, mulVec, leadingMatrix, of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hquad]
    have hnn : ∀ q : XiZeroCopy, 0 ≤ (heatHankelTermAt a P P (xiHeatFrequency q)).re := fun q => by
      have h0 : (xiSpectralPoint q).im = 0 :=
        (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH q
      have him : (xiHeatFrequency q).im = 0 := by rw [xiHeatFrequency_im, h0, mul_zero]
      rw [re_heatHankelTermAt_of_im_eq_zero a P him]
      positivity
    have hs := (summable_heatHankelTermAt ha P P).mapL Complex.reCLM
    rw [heatHankel, Complex.re_tsum (summable_heatHankelTermAt ha P P)]
    refine lt_of_le_of_ne (tsum_nonneg hnn) fun h0 => hu ?_
    have hzero := (hasSum_zero_iff_of_nonneg hnn).1 (h0 ▸ hs.hasSum)
    have hroot : ∀ q : XiZeroCopy, P.IsRoot (xiHeatFrequency q) := by
      intro q
      have h0q := congrFun hzero q
      have h0' : (xiSpectralPoint q).im = 0 :=
        (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero).1 hRH q
      have him : (xiHeatFrequency q).im = 0 := by rw [xiHeatFrequency_im, h0', mul_zero]
      simp only [Pi.zero_apply] at h0q
      rw [re_heatHankelTermAt_of_im_eq_zero a P him] at h0q
      have hexp := Real.exp_pos (-(a * (xiHeatFrequency q).re))
      have : ‖P.eval (xiHeatFrequency q)‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h0q with h | h
        · exact absurd h hexp.ne'
        · exact h
      exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    have hP0 : P = 0 := P.eq_zero_of_infinite_isRoot
      (infinite_range_xiHeatFrequency.mono fun w hw => by
        obtain ⟨q, rfl⟩ := hw
        exact hroot q)
    funext i
    have := congrArg (fun R : ℂ[X] => R.coeff i) hP0
    simp only [coeff_zero] at this
    rw [hcoeff, dif_pos i.2] at this
    simp only [Fin.eta, ofReal_eq_zero] at this
    simpa using this
  · intro h
    rw [riemannHypothesis_iff_heatHankel_nonneg ha]
    intro P
    have hN : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self _
    rw [re_heatHankel_eq_quadratic ha P hN]
    have hpsd := (posSemidef_iff_dotProduct_mulVec.1 (h (P.natDegree + 1)).posSemidef).2
    have h1 := hpsd fun i : Fin (P.natDegree + 1) => (P.coeff i).re
    have h2 := hpsd fun i : Fin (P.natDegree + 1) => (P.coeff i).im
    simp only [dotProduct, mulVec, leadingMatrix, of_apply, star_trivial, Finset.mul_sum] at h1 h2
    have e1 : (∑ i : Fin (P.natDegree + 1), ∑ j : Fin (P.natDegree + 1),
        (P.coeff i).re * (P.coeff j).re * heatMomentArray a i j) =
        ∑ i : Fin (P.natDegree + 1), ∑ j : Fin (P.natDegree + 1),
          (P.coeff i).re * (heatMomentArray a i j * (P.coeff j).re) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have e2 : (∑ i : Fin (P.natDegree + 1), ∑ j : Fin (P.natDegree + 1),
        (P.coeff i).im * (P.coeff j).im * heatMomentArray a i j) =
        ∑ i : Fin (P.natDegree + 1), ∑ j : Fin (P.natDegree + 1),
          (P.coeff i).im * (heatMomentArray a i j * (P.coeff j).im) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    linarith

theorem heatMomentArray_eq_archPrime {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    heatMomentArray a i j =
      (archPrimeMoment (i + j) a).re + 2 * (-1 / 4 : ℝ) ^ (i + j) * Real.exp (a / 4) := by
  rw [heatMomentArray, archPrimeMoment_eq ha]
  have h : (2 * (-1 / 4 : ℂ) ^ (i + j) * Complex.exp ((a : ℂ) / 4)) =
      ((2 * (-1 / 4 : ℝ) ^ (i + j) * Real.exp (a / 4) : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [sub_re, h, ofReal_re]
  ring

/-- **RH as positivity of explicit arch−prime determinants.**  For any `a > 0`, RH holds iff for every
`N` the Hankel determinant of `(−1)^n Re (Arch − Prime)^{(n)}(a)/π + 2(−¼)^n e^{a/4}` is positive. -/
theorem riemannHypothesis_iff_archPrimeDet_pos {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ N, 0 < (leadingMatrix (fun i j =>
      (archPrimeMoment (i + j) a).re + 2 * (-1 / 4 : ℝ) ^ (i + j) * Real.exp (a / 4)) N).det := by
  have h : (fun i j : ℕ =>
      (archPrimeMoment (i + j) a).re + 2 * (-1 / 4 : ℝ) ^ (i + j) * Real.exp (a / 4)) =
      heatMomentArray a := funext fun i => funext fun j => (heatMomentArray_eq_archPrime ha i j).symm
  rw [h]
  exact riemannHypothesis_iff_heatMomentDet_pos ha

end

end RHTower
