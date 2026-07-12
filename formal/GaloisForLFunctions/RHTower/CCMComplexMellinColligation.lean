import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import GaloisForLFunctions.RHTower.CCMFiniteFockPassivity

/-!
# Complex CCM polar--prime Mellin colligation

The real-ray polar--prime identity extends to the complete right half-plane.  The continuous
polar density has the two elementary Laplace coordinates `1 / s` and `1 / (s + 1)`, while the
resolved von Mangoldt channel is the Euler-region logarithmic derivative of zeta.  Their signed
defect therefore gives an exact complex Cauchy colligation, entrywise on every finite packet of
right-half-plane nodes.

No zero-location hypothesis or positivity assumption enters this module.
-/

open scoped BigOperators ComplexConjugate ComplexOrder
open Finset MeasureTheory ArithmeticFunction Complex Matrix Set Filter

noncomputable section

namespace RHTower

/-- The continuous polar half-line channel on the complex right half-plane. -/
def continuousPolarLaplaceChannelComplex (s : ℂ) : ℂ :=
  ∫ h : ℝ in Ioi 0,
    Complex.exp (-(s + 1 / 2) * (h : ℂ)) *
      (2 * Real.cosh (h / 2) : ℝ)

/-- The complex polar channel splits exactly into its two elementary Cauchy coordinates. -/
theorem continuousPolarLaplaceChannelComplex_eq {s : ℂ} (hs : 0 < s.re) :
    continuousPolarLaplaceChannelComplex s = 1 / s + 1 / (s + 1) := by
  rw [continuousPolarLaplaceChannelComplex]
  have hs0 : (-s).re < 0 := by simp; linarith
  have hs1 : (-(s + 1)).re < 0 := by simp; linarith
  have hfun : (fun h : ℝ =>
      Complex.exp (-(s + 1 / 2) * (h : ℂ)) *
        (2 * Real.cosh (h / 2) : ℝ)) =
      fun h : ℝ => Complex.exp ((-s) * h) + Complex.exp (-(s + 1) * h) := by
    funext h
    rw [Real.cosh_eq]
    push_cast
    ring_nf
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1 <;> ring
  rw [hfun, integral_add]
  · rw [integral_exp_mul_complex_Ioi hs0 0,
      integral_exp_mul_complex_Ioi hs1 0]
    norm_num
    rw [show (-1 : ℂ) + -s = -(s + 1) by ring, div_neg]
    ring
  · exact integrableOn_exp_mul_complex_Ioi hs0 0
  · exact integrableOn_exp_mul_complex_Ioi hs1 0

/-- The resolved von Mangoldt prime-power channel at a complex right-half-plane coordinate. -/
def vonMangoldtPrimeLaplaceChannelComplex (s : ℂ) : ℂ :=
  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + 1)

/-- The complex signed critical Mellin-defect channel. -/
def criticalMellinDefectLaplaceChannelComplex (s : ℂ) : ℂ :=
  continuousPolarLaplaceChannelComplex s - vonMangoldtPrimeLaplaceChannelComplex s

/-- The complex prime channel is the Euler-region negative logarithmic derivative of zeta. -/
theorem vonMangoldtPrimeLaplaceChannelComplex_eq_logDeriv
    {s : ℂ} (hs : 0 < s.re) :
    vonMangoldtPrimeLaplaceChannelComplex s =
      -deriv riemannZeta (s + 1) / riemannZeta (s + 1) := by
  rw [vonMangoldtPrimeLaplaceChannelComplex]
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
    simpa using hs)

/-- **Complex polar--prime critical Mellin colligation.**  On the whole right half-plane, the
universal Cauchy coordinate is the resolved prime channel minus the shifted polar coordinate plus
the signed critical Mellin defect. -/
theorem cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect_complex
    {s : ℂ} (hs : 0 < s.re) :
    1 / s = vonMangoldtPrimeLaplaceChannelComplex s - 1 / (s + 1) +
      criticalMellinDefectLaplaceChannelComplex s := by
  rw [criticalMellinDefectLaplaceChannelComplex,
    continuousPolarLaplaceChannelComplex_eq hs]
  ring

/-- The universal Cauchy Gram on a finite packet of complex right-half-plane nodes. -/
def cauchyRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => 1 / (w i + star (w j))

/-- The resolved von Mangoldt Gram on the same complex packet. -/
def vonMangoldtPrimeRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => vonMangoldtPrimeLaplaceChannelComplex (w i + star (w j))

private abbrev vonMangoldtComplexCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

private def vonMangoldtRightHalfPlaneWeight (n : ℕ) : ℂ :=
  LSeries.term vonMangoldtComplexCoefficient 1 n

private def primePowerRightHalfPlaneFeature (w : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ w)⁻¹

private lemma star_natCast_cpow (n : ℕ) (w : ℂ) (hn : n ≠ 0) :
    star (((n : ℂ) ^ w)) = (n : ℂ) ^ star w := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have harg : ((n : ℂ).arg ≠ Real.pi) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg hnpos.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (n : ℂ) w harg
  simpa using h.symm

private lemma star_primePowerRightHalfPlaneFeature
    (w : ℂ) (n : ℕ) (hn : n ≠ 0) :
    star (primePowerRightHalfPlaneFeature w n) =
      primePowerRightHalfPlaneFeature (star w) n := by
  rw [primePowerRightHalfPlaneFeature, primePowerRightHalfPlaneFeature,
    star_inv₀, star_natCast_cpow n w hn]

private lemma vonMangoldtComplexTerm_eq_weight_mul_features
    {w v : ℂ} (n : ℕ) :
    LSeries.term vonMangoldtComplexCoefficient (w + star v + 1) n =
      vonMangoldtRightHalfPlaneWeight n * primePowerRightHalfPlaneFeature w n *
        star (primePowerRightHalfPlaneFeature v n) := by
  by_cases hn : n = 0
  · subst n
    simp [vonMangoldtRightHalfPlaneWeight, primePowerRightHalfPlaneFeature, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn]
    rw [vonMangoldtRightHalfPlaneWeight, LSeries.term_of_ne_zero hn]
    rw [star_primePowerRightHalfPlaneFeature v n hn]
    rw [primePowerRightHalfPlaneFeature, primePowerRightHalfPlaneFeature]
    rw [Complex.cpow_add (w + star v) 1 (Nat.cast_ne_zero.mpr hn),
      Complex.cpow_add w (star v) (Nat.cast_ne_zero.mpr hn)]
    simp only [div_eq_mul_inv]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    ring

private lemma complex_vonMangoldtCoefficient_nonneg (n : ℕ) :
    0 ≤ vonMangoldtComplexCoefficient n := by
  apply Complex.nonneg_iff.mpr
  exact ⟨by simp [vonMangoldtComplexCoefficient, ArithmeticFunction.vonMangoldt_nonneg],
    by simp [vonMangoldtComplexCoefficient]⟩

private lemma vonMangoldtRightHalfPlaneWeight_nonneg (n : ℕ) :
    0 ≤ vonMangoldtRightHalfPlaneWeight n :=
  LSeries.term_nonneg (complex_vonMangoldtCoefficient_nonneg n) 1

private lemma star_vonMangoldtRightHalfPlaneWeight (n : ℕ) :
    star (vonMangoldtRightHalfPlaneWeight n) = vonMangoldtRightHalfPlaneWeight n := by
  have h := vonMangoldtRightHalfPlaneWeight_nonneg n
  rcases Complex.nonneg_iff.mp h with ⟨_, him⟩
  exact RCLike.conj_eq_iff_im.mpr him.symm

private lemma summable_vonMangoldtRightHalfPlaneWeight_mul_features
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    Summable (fun n => vonMangoldtRightHalfPlaneWeight n *
      primePowerRightHalfPlaneFeature w n * star (primePowerRightHalfPlaneFeature v n)) := by
  have hs : 1 < (w + star v + 1).re := by
    change 1 < w.re + v.re + 1
    linarith
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr
    (fun n => vonMangoldtComplexTerm_eq_weight_mul_features n)

private def resolvedVonMangoldtPrimeRightHalfPlaneGram
    {N : ℕ} (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∑' n, vonMangoldtRightHalfPlaneWeight n *
    primePowerRightHalfPlaneFeature (w i) n * star (primePowerRightHalfPlaneFeature (w j) n)

private lemma resolvedVonMangoldtPrimeRightHalfPlaneGram_eq
    {N : ℕ} (w : Fin N → ℂ) :
    resolvedVonMangoldtPrimeRightHalfPlaneGram w = vonMangoldtPrimeRightHalfPlaneGram w := by
  ext i j
  rw [resolvedVonMangoldtPrimeRightHalfPlaneGram, vonMangoldtPrimeRightHalfPlaneGram,
    vonMangoldtPrimeLaplaceChannelComplex, LSeries]
  apply tsum_congr
  intro n
  exact (vonMangoldtComplexTerm_eq_weight_mul_features n).symm

/-- **Complex resolved Euler Gram positivity.**  Every finite packet of actual von Mangoldt
right-half-plane channels is positive semidefinite.  Its quadratic form retains the unsquared
arithmetic weights and is the convergent prime-power sum
`sum_n (Lambda(n)/n) * |sum_i c_i n^(-conj(w_i))|^2`. -/
theorem vonMangoldtPrimeRightHalfPlaneGram_posSemidef
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    (vonMangoldtPrimeRightHalfPlaneGram w).PosSemidef := by
  rw [← resolvedVonMangoldtPrimeRightHalfPlaneGram_eq w]
  have hherm : (resolvedVonMangoldtPrimeRightHalfPlaneGram w).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply]
    rw [resolvedVonMangoldtPrimeRightHalfPlaneGram,
      resolvedVonMangoldtPrimeRightHalfPlaneGram, tsum_star]
    apply tsum_congr
    intro n
    simp only [star_mul', star_star, star_vonMangoldtRightHalfPlaneWeight]
    ring
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun c => ?_)
  let P : ℕ → ℂ := fun n =>
    ∑ k, c k * star (primePowerRightHalfPlaneFeature (w k) n)
  have hpairs : ∀ i j : Fin N,
      Summable (fun n => star (c i) * (c j *
        (vonMangoldtRightHalfPlaneWeight n * primePowerRightHalfPlaneFeature (w i) n *
          star (primePowerRightHalfPlaneFeature (w j) n)))) := by
    intro i j
    exact (((summable_vonMangoldtRightHalfPlaneWeight_mul_features
      (hw i) (hw j)).mul_left (c j)).mul_left (star (c i))).congr (fun n => by ring)
  have key : star c ⬝ᵥ (resolvedVonMangoldtPrimeRightHalfPlaneGram w).mulVec c =
      ∑' n, star (P n) * (vonMangoldtRightHalfPlaneWeight n * P n) := by
    simp only [dotProduct, Pi.star_apply]
    have hswap : ∀ i,
        star (c i) * (resolvedVonMangoldtPrimeRightHalfPlaneGram w).mulVec c i =
          ∑' n, ∑ j, star (c i) * (c j *
            (vonMangoldtRightHalfPlaneWeight n * primePowerRightHalfPlaneFeature (w i) n *
              star (primePowerRightHalfPlaneFeature (w j) n))) := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum, Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [resolvedVonMangoldtPrimeRightHalfPlaneGram]
        rw [← (summable_vonMangoldtRightHalfPlaneWeight_mul_features
          (hw i) (hw j)).tsum_mul_right (c j)]
        rw [← ((summable_vonMangoldtRightHalfPlaneWeight_mul_features
          (hw i) (hw j)).mul_right (c j)).tsum_mul_left (star (c i))]
        apply tsum_congr
        intro n
        ring
      · intro j hj
        exact hpairs i j
    calc
      (∑ i, star (c i) * (resolvedVonMangoldtPrimeRightHalfPlaneGram w).mulVec c i) =
          ∑ i, ∑' n, ∑ j, star (c i) * (c j *
            (vonMangoldtRightHalfPlaneWeight n * primePowerRightHalfPlaneFeature (w i) n *
              star (primePowerRightHalfPlaneFeature (w j) n))) :=
        Finset.sum_congr rfl (fun i _ => hswap i)
      _ = ∑' n, star (P n) * (vonMangoldtRightHalfPlaneWeight n * P n) := by
        rw [← Summable.tsum_finsetSum]
        · apply tsum_congr
          intro n
          change (∑ i, ∑ j, star (c i) * (c j *
              (vonMangoldtRightHalfPlaneWeight n * primePowerRightHalfPlaneFeature (w i) n *
                star (primePowerRightHalfPlaneFeature (w j) n)))) =
            (starRingEnd ℂ)
                (∑ k, c k * star (primePowerRightHalfPlaneFeature (w k) n)) *
              (vonMangoldtRightHalfPlaneWeight n *
                ∑ k, c k * star (primePowerRightHalfPlaneFeature (w k) n))
          rw [map_sum]
          have hstar (k : Fin N) :
              (starRingEnd ℂ)
                  (c k * star (primePowerRightHalfPlaneFeature (w k) n)) =
                star (c k) * primePowerRightHalfPlaneFeature (w k) n := by
            rw [map_mul]
            change star (c k) *
              star (star (primePowerRightHalfPlaneFeature (w k) n)) = _
            rw [star_star]
          simp_rw [hstar]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        · intro i hi
          exact summable_sum (fun j hj => hpairs i j)
  rw [key]
  apply tsum_nonneg
  intro n
  have hweight := vonMangoldtRightHalfPlaneWeight_nonneg n
  have hsq : 0 ≤ star (P n) * P n := by
    change 0 ≤ (starRingEnd ℂ) (P n) * P n
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.nonneg_iff.mpr ⟨Complex.normSq_nonneg _, rfl⟩
  have hprod := mul_nonneg hweight hsq
  rw [show star (P n) * (vonMangoldtRightHalfPlaneWeight n * P n) =
    vonMangoldtRightHalfPlaneWeight n * (star (P n) * P n) by ring]
  exact hprod

/-- The shifted elementary polar Gram on the same complex packet. -/
def shiftedPolarRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => 1 / (w i + star (w j) + 1)

/-- The critical Mellin-defect matrix on the same complex packet. -/
def criticalMellinDefectRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => criticalMellinDefectLaplaceChannelComplex (w i + star (w j))

/-- **Finite complex source incidence.**  Every finite right-half-plane Cauchy Gram is exactly the
resolved prime Gram minus the shifted polar Gram plus the critical Mellin-defect matrix. -/
theorem cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    cauchyRightHalfPlaneGram w = vonMangoldtPrimeRightHalfPlaneGram w -
      shiftedPolarRightHalfPlaneGram w + criticalMellinDefectRightHalfPlaneGram w := by
  ext i j
  exact cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect_complex (by
    change 0 < (w i + conj (w j)).re
    rw [Complex.add_re, Complex.conj_re]
    linarith [hw i, hw j])

/-- **Concrete complex finite-Fock reduction.**  For the actual complex polar--prime Mellin
incidence, diagonal-Fock passivity is exactly the source-resolved inequality.  The theorem removes
the abstract incidence hypothesis from the finite CCM algebra. -/
theorem ccmComplexMellinFiniteFockPassivity_iff_sourceResolved
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    CCMFiniteFockPassivity A (cauchyRightHalfPlaneGram w) ↔
      CCMSourceResolvedPassivity A (vonMangoldtPrimeRightHalfPlaneGram w)
        (shiftedPolarRightHalfPlaneGram w) (criticalMellinDefectRightHalfPlaneGram w) := by
  exact ccmFiniteFockPassivity_iff_sourceResolved
    A (cauchyRightHalfPlaneGram w) (vonMangoldtPrimeRightHalfPlaneGram w)
      (shiftedPolarRightHalfPlaneGram w) (criticalMellinDefectRightHalfPlaneGram w)
      (cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect w hw)

/-- The same concrete complex reduction in the equivalent Krein-defect form. -/
theorem ccmComplexMellinDiagonalDefect_nonneg_iff_sourceResolved
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    KreinNonneg (ccmDiagonalDefectGram A (cauchyRightHalfPlaneGram w)) ↔
      CCMSourceResolvedPassivity A (vonMangoldtPrimeRightHalfPlaneGram w)
        (shiftedPolarRightHalfPlaneGram w) (criticalMellinDefectRightHalfPlaneGram w) := by
  exact ccmDiagonalDefect_kreinNonneg_iff_sourceResolved
    A (cauchyRightHalfPlaneGram w) (vonMangoldtPrimeRightHalfPlaneGram w)
      (shiftedPolarRightHalfPlaneGram w) (criticalMellinDefectRightHalfPlaneGram w)
      (cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect w hw)

end RHTower
