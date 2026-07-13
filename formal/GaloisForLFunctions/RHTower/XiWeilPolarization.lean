import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.Bottcher.ArgumentPrinciple

/-!
# Multiplicity-exact Weil polarization on the Xi divisor

This module constructs the zero-side polarized Weil form on the actual centered Xi divisor, with
every zero repeated according to its analytic multiplicity.  Functional-equation reflection and
Schwarz conjugation give the exact reindexing that makes the form Hermitian.  The completed theta
kernel `XiC` lies in both radicals, multiplication by the centered spectral coordinate is formally
symmetric, and RH makes every square-summable diagonal value nonnegative.

No positivity or RH hypothesis is used in the construction, Hermitian identity, radical theorem,
or multiplier symmetry.  This is the algebraic divisor side of the Hedenmalm--Weil card; the
prime-plus-Gamma explicit-formula realization and Hilbert completion remain separate analytic work.
-/

open Complex

namespace RHTower

noncomputable section

/-- Conjugation lifted to the exact multiplicity-copy index of the Xi divisor. -/
def xiZeroCopyConjEquiv : XiZeroCopy ≃ XiZeroCopy :=
  Equiv.sigmaCongr xiZeroConjEquiv (fun ρ => Equiv.cast (by
    change Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =
      Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ)
        ((starRingEnd ℂ) (ρ : ℂ))))
    rw [xi_divisor_conj]))

/-- Conjugating a Xi zero sends its centered spectral coordinate to minus its conjugate. -/
theorem xiSpectralPoint_copyConj (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyConjEquiv q) =
      -(starRingEnd ℂ) (xiSpectralPoint q) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.conj_ofReal]
  rw [xiSpectralPoint, xiSpectralPoint]
  change (((starRingEnd ℂ) (q.1 : ℂ)) - 1 / 2) * (-I) =
    -(starRingEnd ℂ) (((q.1 : ℂ) - 1 / 2) * (-I))
  simp only [map_mul, map_sub, map_neg, conj_I, hhalf]
  ring

/-- Critical-line reflection `rho ↦ 1-conj(rho)` on multiplicity copies. -/
def xiZeroCopyLineConjEquiv : XiZeroCopy ≃ XiZeroCopy :=
  xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv

/-- Critical-line reflection is ordinary conjugation in centered spectral coordinates. -/
theorem xiSpectralPoint_lineConj (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ) (xiSpectralPoint q) := by
  rw [xiZeroCopyLineConjEquiv, Equiv.trans_apply, xiSpectralPoint_reflect,
    xiSpectralPoint_copyConj]
  ring

/-- The involution `F#(z) = conj(F(conj z))` on Weil test functions. -/
def xiWeilSharp (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (F ((starRingEnd ℂ) z))

/-- Absolute convergence condition for a polarized pair on the multiplicity-exact Xi divisor. -/
def XiWeilPairSummable (F G : ℂ → ℂ) : Prop :=
  Summable (fun q : XiZeroCopy =>
    F (xiSpectralPoint q) * xiWeilSharp G (xiSpectralPoint q))

/-- Square-summability of a test function on the multiplicity-exact centered Xi divisor. -/
def XiWeilSquareSummable (F : ℂ → ℂ) : Prop :=
  Summable (fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖ ^ 2)

/-- The multiplicity-exact zero-side Weil polarization. -/
def xiWeilPolarization (F G : ℂ → ℂ) : ℂ :=
  ∑' q : XiZeroCopy,
    F (xiSpectralPoint q) * xiWeilSharp G (xiSpectralPoint q)

/-- The actual Xi-divisor polarization is Hermitian, unconditionally. -/
theorem xiWeilPolarization_conj_symm (F G : ℂ → ℂ) :
    xiWeilPolarization G F = (starRingEnd ℂ) (xiWeilPolarization F G) := by
  unfold xiWeilPolarization
  let term : XiZeroCopy → ℂ := fun q =>
    G (xiSpectralPoint q) * xiWeilSharp F (xiSpectralPoint q)
  calc
    (∑' q : XiZeroCopy,
        G (xiSpectralPoint q) * xiWeilSharp F (xiSpectralPoint q)) =
        ∑' q : XiZeroCopy, term (xiZeroCopyLineConjEquiv q) := by
          symm
          exact xiZeroCopyLineConjEquiv.tsum_eq term
    _ = ∑' q : XiZeroCopy,
        (starRingEnd ℂ)
          (F (xiSpectralPoint q) * xiWeilSharp G (xiSpectralPoint q)) := by
      apply tsum_congr
      intro q
      dsimp only [term]
      rw [xiSpectralPoint_lineConj]
      simp [xiWeilSharp]
      ring
    _ = (starRingEnd ℂ) (∑' q : XiZeroCopy,
        F (xiSpectralPoint q) * xiWeilSharp G (xiSpectralPoint q)) := by
      exact (Complex.conj_tsum _).symm

/-- Multiplication by `-z`, the Fourier image of the card's centered differential operator, is
formally symmetric for the Weil polarization. -/
theorem xiWeilPolarization_spectralMultiply (F G : ℂ → ℂ) :
    xiWeilPolarization (fun z => -z * F z) G =
      xiWeilPolarization F (fun z => -z * G z) := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  simp [xiWeilSharp]
  ring

/-- The completed theta transform is in the left radical because every divisor copy is a zero. -/
theorem xiWeilPolarization_XiC_left (G : ℂ → ℂ) :
    xiWeilPolarization XiC G = 0 := by
  unfold xiWeilPolarization
  simp [XiC_xiSpectralPoint_eq_zero]

/-- Hermitian symmetry puts the completed theta transform in the right radical as well. -/
theorem xiWeilPolarization_XiC_right (F : ℂ → ℂ) :
    xiWeilPolarization F XiC = 0 := by
  rw [xiWeilPolarization_conj_symm, xiWeilPolarization_XiC_left]
  simp

/-- Adding a multiple of the completed theta transform to a left preimage does not change the
polarization.  This is the exact left-preimage independence needed for descent through the theta
constraint. -/
theorem xiWeilPolarization_add_XiC_left (F G : ℂ → ℂ) (c : ℂ) :
    xiWeilPolarization (fun z => F z + c * XiC z) G = xiWeilPolarization F G := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  change (F (xiSpectralPoint q) + c * XiC (xiSpectralPoint q)) *
    xiWeilSharp G (xiSpectralPoint q) = _
  rw [XiC_xiSpectralPoint_eq_zero]
  ring

/-- Adding a multiple of the completed theta transform to a right preimage also leaves the
polarization unchanged. -/
theorem xiWeilPolarization_add_XiC_right (F G : ℂ → ℂ) (c : ℂ) :
    xiWeilPolarization F (fun z => G z + c * XiC z) = xiWeilPolarization F G := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  have hzero : XiC ((starRingEnd ℂ) (xiSpectralPoint q)) = 0 := by
    rw [← xiSpectralPoint_lineConj]
    exact XiC_xiSpectralPoint_eq_zero _
  change F (xiSpectralPoint q) *
      (starRingEnd ℂ)
        (G ((starRingEnd ℂ) (xiSpectralPoint q)) +
          c * XiC ((starRingEnd ℂ) (xiSpectralPoint q))) = _
  rw [hzero]
  simp only [mul_zero, add_zero]
  rfl

/-- Under RH the diagonal polarization is exactly the positive atomic Gram sum. -/
theorem xiWeilPolarization_diagonal_of_riemannHypothesis
    (hRH : RiemannHypothesis) (F : ℂ → ℂ) :
    xiWeilPolarization F F =
      ∑' q : XiZeroCopy, ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) := by
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [ht]
  have htconj : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [xiWeilSharp, htconj]
  simpa [Complex.sq_norm] using Complex.mul_conj (F (t : ℂ))

/-- Every square-summable diagonal Weil value is nonnegative under RH. -/
theorem xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis
    (hRH : RiemannHypothesis) (F : ℂ → ℂ)
    (hsum : XiWeilSquareSummable F) :
    0 ≤ (xiWeilPolarization F F).re := by
  rw [xiWeilPolarization_diagonal_of_riemannHypothesis hRH]
  have hsumC : Summable (fun q : XiZeroCopy =>
      ((‖F (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ)) :=
    by
      simpa only [Function.comp_apply] using
        hsum.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  rw [Complex.re_tsum hsumC]
  apply tsum_nonneg
  intro q
  simp only [Complex.ofReal_re]
  positivity

/-! ## The removable Hedenmalm eigenfunction quotient -/

/-- The entire removable quotient in the Hedenmalm eigenfunction formula:
`i * dslope XiC alpha`, equal away from `alpha` to `-i XiC(z)/(alpha-z)`. -/
def xiThetaEigenFourier (alpha z : ℂ) : ℂ :=
  I * dslope XiC alpha z

/-- The removable quotient is entire for every parameter. -/
theorem xiThetaEigenFourier_analytic (alpha : ℂ) :
    AnalyticOnNhd ℂ (xiThetaEigenFourier alpha) Set.univ := by
  have hdiff : DifferentiableOn ℂ XiC Set.univ := fun z hz =>
    (XiC_analytic z hz).differentiableAt.differentiableWithinAt
  have hdslope : DifferentiableOn ℂ (dslope XiC alpha) Set.univ :=
    (differentiableOn_dslope (isOpen_univ.mem_nhds (Set.mem_univ alpha))).mpr hdiff
  intro z _hz
  simpa only [xiThetaEigenFourier] using
    (analyticAt_const.mul
      (hdslope.analyticAt (isOpen_univ.mem_nhds (Set.mem_univ z))))

/-- Away from its removed point, the entire definition is the card's literal quotient. -/
theorem xiThetaEigenFourier_eq_div {alpha z : ℂ}
    (halpha : XiC alpha = 0) (hz : z ≠ alpha) :
    xiThetaEigenFourier alpha z = -I * XiC z / (alpha - z) := by
  have hfactor : XiC z = (z - alpha) * dslope XiC alpha z := by
    have hs := sub_smul_dslope XiC alpha z
    rw [halpha, sub_zero, smul_eq_mul] at hs
    exact hs.symm
  rw [xiThetaEigenFourier, hfactor]
  have hden : alpha - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  field_simp [hden]
  ring

/-- At the removed zero, the quotient has the exact derivative value `i XiC'(alpha)`. -/
theorem xiThetaEigenFourier_self (alpha : ℂ) :
    xiThetaEigenFourier alpha alpha = I * deriv XiC alpha := by
  rw [xiThetaEigenFourier, dslope_same]

/-- The eigenfunction quotient based at one Xi zero vanishes at every distinct Xi zero. -/
theorem xiThetaEigenFourier_eq_zero_of_XiC_eq_zero
    {alpha beta : ℂ} (halpha : XiC alpha = 0) (hbeta : XiC beta = 0)
    (hne : beta ≠ alpha) :
    xiThetaEigenFourier alpha beta = 0 := by
  rw [xiThetaEigenFourier_eq_div halpha hne, hbeta]
  ring

/-- Multiplicity-exact divisor-copy version of the off-diagonal vanishing law. -/
theorem xiThetaEigenFourier_spectralPoint_eq_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) (q : XiZeroCopy)
    (hne : xiSpectralPoint q ≠ alpha) :
    xiThetaEigenFourier alpha (xiSpectralPoint q) = 0 :=
  xiThetaEigenFourier_eq_zero_of_XiC_eq_zero halpha
    (XiC_xiSpectralPoint_eq_zero q) hne

/-- Evaluation on the actual divisor is supported exactly on the multiplicity copies at the base
zero, where its value is `i XiC'(alpha)`. -/
theorem xiThetaEigenFourier_spectralPoint
    {alpha : ℂ} (halpha : XiC alpha = 0) (q : XiZeroCopy) :
    xiThetaEigenFourier alpha (xiSpectralPoint q) =
      if xiSpectralPoint q = alpha then I * deriv XiC alpha else 0 := by
  split_ifs with h
  · rw [h, xiThetaEigenFourier_self]
  · exact xiThetaEigenFourier_spectralPoint_eq_zero halpha q h

/-- Only finitely many multiplicity copies can occupy one centered spectral point. -/
theorem finite_xiSpectralPoint_fiber (alpha : ℂ) :
    {q : XiZeroCopy | xiSpectralPoint q = alpha}.Finite := by
  by_cases h : ∃ q : XiZeroCopy, xiSpectralPoint q = alpha
  · obtain ⟨q0, hq0⟩ := h
    have hbase : {q : XiZeroCopy | q.1 = q0.1}.Finite := by
      letI : Fintype {q : XiZeroCopy | q.1 = q0.1} :=
        Fintype.ofEquiv
          (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q0.1 : ℂ))))
          (xiZeroCopyFiberEquiv q0.1)
      exact Set.finite_def.mpr ⟨inferInstance⟩
    apply hbase.subset
    intro q hq
    change q.1 = q0.1
    apply xiSpectralPointSupport_injective
    simpa only [xiSpectralPoint_eq_support] using hq.trans hq0.symm
  · simp only [not_exists] at h
    have hempty : {q : XiZeroCopy | xiSpectralPoint q = alpha} = ∅ := by
      ext q
      simp [h q]
    rw [hempty]
    exact Set.finite_empty

/-- The number of divisor-multiplicity copies at one centered spectral point. -/
def xiSpectralMultiplicity (alpha : ℂ) : ℕ :=
  (finite_xiSpectralPoint_fiber alpha).toFinset.card

/-- At every actual centered Xi zero, the number of divisor copies in the spectral carrier is
exactly the analytic vanishing order of `XiC`. -/
theorem xiSpectralMultiplicity_eq_analyticOrderAt_toNat
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiSpectralMultiplicity alpha = (analyticOrderAt XiC alpha).toNat := by
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
  let S : Set XiZeroCopy := {r | xiSpectralPoint r = alpha}
  let B : Set XiZeroCopy := {r | r.1 = q.1}
  have hSB : S = B := by
    ext r
    simp only [S, B, Set.mem_setOf_eq]
    constructor
    · intro hr
      apply xiSpectralPointSupport_injective
      simpa only [xiSpectralPoint_eq_support] using hr.trans hq.symm
    · intro hr
      rw [← hq]
      simp only [xiSpectralPoint_eq_support, hr]
  letI : Fintype {r : XiZeroCopy // r ∈ B} :=
    Fintype.ofEquiv
      (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ))))
      (by simpa only [B, Set.mem_setOf_eq] using xiZeroCopyFiberEquiv q.1)
  calc
    xiSpectralMultiplicity alpha = S.ncard := by
      rw [xiSpectralMultiplicity]
      exact (Set.ncard_eq_toFinset_card S (finite_xiSpectralPoint_fiber alpha)).symm
    _ = B.ncard := congrArg Set.ncard hSB
    _ = B.toFinset.card := Set.ncard_eq_toFinset_card' B
    _ = Fintype.card {r : XiZeroCopy // r ∈ B} := Set.toFinset_card B
    _ = Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ)) := by
      rw [Fintype.card_congr
        (by simpa only [B, Set.mem_setOf_eq] using (xiZeroCopyFiberEquiv q.1).symm)]
      exact Fintype.card_fin _
    _ = (analyticOrderAt XiC alpha).toNat := by
      rw [← hq, xiSpectralPoint_eq_support, XiC_analyticOrderAt_support]
      simp

/-- Every actual Xi zero has at least one multiplicity copy. -/
theorem xiSpectralMultiplicity_pos_of_XiC_eq_zero
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    0 < xiSpectralMultiplicity alpha := by
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
  rw [xiSpectralMultiplicity, Finset.card_pos]
  refine ⟨q, ?_⟩
  simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq

/-- Every Hedenmalm eigenfunction quotient is square-summable on the actual centered divisor: its
evaluation sequence has finite support, namely the multiplicity fiber at its base zero. -/
theorem xiThetaEigenFourier_squareSummable {alpha : ℂ} (halpha : XiC alpha = 0) :
    XiWeilSquareSummable (xiThetaEigenFourier alpha) := by
  unfold XiWeilSquareSummable
  apply summable_of_hasFiniteSupport
  apply (finite_xiSpectralPoint_fiber alpha).subset
  intro q hq
  simp only [Function.mem_support] at hq
  by_contra hne
  apply hq
  rw [xiThetaEigenFourier_spectralPoint_eq_zero halpha q hne, norm_zero]
  norm_num

/-- Under RH, the Hedenmalm eigenfunction norm is its analytic multiplicity times the squared
derivative of `XiC`, exactly as in the polarized Weil law. -/
theorem xiWeilPolarization_thetaEigen_diagonal_of_riemannHypothesis
    (hRH : RiemannHypothesis) {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier alpha) =
      (((xiSpectralMultiplicity alpha : ℝ) * ‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ) := by
  rw [xiWeilPolarization_diagonal_of_riemannHypothesis hRH]
  let S : Set XiZeroCopy := {q | xiSpectralPoint q = alpha}
  let T : Finset XiZeroCopy := (finite_xiSpectralPoint_fiber alpha).toFinset
  let c : ℂ := ((‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ)
  let g : XiZeroCopy → ℂ := fun q => if q ∈ S then c else 0
  have heq (q : XiZeroCopy) :
      ((‖xiThetaEigenFourier alpha (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) = g q := by
    by_cases hq : xiSpectralPoint q = alpha
    · rw [xiThetaEigenFourier_spectralPoint halpha, if_pos hq]
      simp only [g, S, Set.mem_setOf_eq, hq, if_pos, norm_mul, norm_I, one_mul, c]
    · rw [xiThetaEigenFourier_spectralPoint halpha, if_neg hq]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Complex.ofReal_zero, g, S, Set.mem_setOf_eq, hq, if_false]
  calc
    (∑' q : XiZeroCopy,
        ((‖xiThetaEigenFourier alpha (xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ)) =
        ∑' q : XiZeroCopy, g q := tsum_congr heq
    _ = ∑ q ∈ T, g q := by
      apply tsum_eq_sum
      intro q hqT
      have hqS : q ∉ S := by
        intro hqS
        apply hqT
        simpa only [T, Set.Finite.mem_toFinset, S] using hqS
      simp [g, hqS]
    _ = (T.card : ℂ) * c := by
      have hmem : ∀ q ∈ T, q ∈ S := by
        intro q hq
        simpa only [T, Set.Finite.mem_toFinset, S] using hq
      calc
        ∑ q ∈ T, g q = ∑ _q ∈ T, c := by
          apply Finset.sum_congr rfl
          intro q hq
          change (if q ∈ S then c else 0) = c
          rw [if_pos (hmem q hq)]
        _ = (T.card : ℂ) * c := by simp
    _ = (((xiSpectralMultiplicity alpha : ℝ) * ‖deriv XiC alpha‖ ^ 2 : ℝ) : ℂ) := by
      have hcard : T.card = xiSpectralMultiplicity alpha := by
        rfl
      rw [hcard]
      simp only [c]
      norm_cast

/-- Distinct Hedenmalm eigenfunction quotients are orthogonal under RH. -/
theorem xiWeilPolarization_thetaEigen_orthogonal_of_riemannHypothesis
    (hRH : RiemannHypothesis) {alpha beta : ℂ}
    (halpha : XiC alpha = 0) (hbeta : XiC beta = 0) (hne : alpha ≠ beta) :
    xiWeilPolarization (xiThetaEigenFourier alpha) (xiThetaEigenFourier beta) = 0 := by
  unfold xiWeilPolarization
  have hterm : (fun q : XiZeroCopy =>
      xiThetaEigenFourier alpha (xiSpectralPoint q) *
        xiWeilSharp (xiThetaEigenFourier beta) (xiSpectralPoint q)) = 0 := by
    funext q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q := by
      rw [ht]
      exact Complex.conj_ofReal t
    rw [xiWeilSharp, hreal]
    by_cases hqa : xiSpectralPoint q = alpha
    · have hqb : xiSpectralPoint q ≠ beta := by
        intro h
        apply hne
        exact hqa.symm.trans h
      rw [xiThetaEigenFourier_spectralPoint_eq_zero hbeta q hqb]
      simp
    · rw [xiThetaEigenFourier_spectralPoint_eq_zero halpha q hqa]
      simp
  rw [hterm]
  exact tsum_zero

/-- On a genuine Xi zero and under RH, the Hedenmalm eigenfunction is null exactly when the zero
is multiple, i.e. exactly when `XiC'(alpha)=0`. -/
theorem xiWeilPolarization_thetaEigen_re_eq_zero_iff_deriv_eq_zero
    (hRH : RiemannHypothesis) {alpha : ℂ} (halpha : XiC alpha = 0) :
    (xiWeilPolarization (xiThetaEigenFourier alpha)
      (xiThetaEigenFourier alpha)).re = 0 ↔ deriv XiC alpha = 0 := by
  rw [xiWeilPolarization_thetaEigen_diagonal_of_riemannHypothesis hRH halpha]
  simp only [Complex.ofReal_re, mul_eq_zero]
  have hm : (xiSpectralMultiplicity alpha : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (xiSpectralMultiplicity_pos_of_XiC_eq_zero halpha))
  simp [hm, norm_eq_zero]

end

end RHTower
