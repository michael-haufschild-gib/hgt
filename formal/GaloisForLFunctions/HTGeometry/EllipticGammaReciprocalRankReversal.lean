import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFacewiseRankThreeMinor

/-!
# Reciprocal-period phase reversal

Take a transcendental `ω` in the upper half plane, distinct integers `n_j`, and the two period
families

`α_j = (ω + n_j)/m`,   `β_j = -m/(ω + n_j)`.

The first family lies on a rational affine line: any two of its members differ by a rational number,
so no triple `1, α_q, α_r` is rationally independent and the augmented period rank is two.  The
second family is rationally independent in pairs: a relation among `1`, `1/(ω+n_q)`, `1/(ω+n_r)`
clears denominators into a polynomial vanishing at `ω`, hence identically, and evaluating at `-n_q`
and `-n_r` kills the coefficients.

Componentwise reciprocalization therefore reverses the phase of the multiple elliptic Gamma
function: the direct family is differentially algebraic and every reciprocal pair is
hypertranscendental.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

variable {N : ℕ}

/-- The direct period family `(ω + n j)/m`. -/
def directPeriod (omega : ℂ) (n : Fin N → ℤ) (m : ℕ) (j : Fin N) : ℂ :=
  (omega + (n j : ℂ)) / (m : ℂ)

/-- The componentwise reciprocal period family `-m/(ω + n j)`. -/
def inversePeriod (omega : ℂ) (n : Fin N → ℤ) (m : ℕ) (j : Fin N) : ℂ :=
  -(m : ℂ) / (omega + (n j : ℂ))

/-- A transcendental number is not the negative of an integer. -/
theorem add_intCast_ne_zero_of_transcendental {omega : ℂ} (homega : Transcendental ℚ omega)
    (k : ℤ) : omega + (k : ℂ) ≠ 0 := by
  intro h0
  refine homega ⟨Polynomial.X + Polynomial.C (k : ℚ), Polynomial.X_add_C_ne_zero _, ?_⟩
  have hmap : (algebraMap ℚ ℂ) ((k : ℤ) : ℚ) = (k : ℂ) := by simp
  rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C, hmap]
  exact h0

/-- **Partial-fraction independence.**  Over a transcendental `ω` a rational combination of `1` and
the two reciprocals `1/(ω + a)`, `1/(ω + b)` with distinct integers `a ≠ b` vanishes only
trivially. -/
theorem partialFraction_independent {omega : ℂ} (homega : Transcendental ℚ omega)
    {a b : ℤ} (hab : a ≠ b) {u v w : ℚ}
    (h : (u : ℂ) + (v : ℂ) / (omega + (a : ℂ)) + (w : ℂ) / (omega + (b : ℂ)) = 0) :
    u = 0 ∧ v = 0 ∧ w = 0 := by
  have hane : omega + (a : ℂ) ≠ 0 := add_intCast_ne_zero_of_transcendental homega a
  have hbne : omega + (b : ℂ) ≠ 0 := add_intCast_ne_zero_of_transcendental homega b
  set P : Polynomial ℚ :=
    Polynomial.C u * ((Polynomial.X + Polynomial.C (a : ℚ)) * (Polynomial.X + Polynomial.C (b : ℚ)))
      + Polynomial.C v * (Polynomial.X + Polynomial.C (b : ℚ))
      + Polynomial.C w * (Polynomial.X + Polynomial.C (a : ℚ)) with hPdef
  have haeval : Polynomial.aeval omega P = 0 := by
    rw [hPdef]
    have hu : (algebraMap ℚ ℂ) u = (u : ℂ) := by simp
    have hv' : (algebraMap ℚ ℂ) v = (v : ℂ) := by simp
    have hw' : (algebraMap ℚ ℂ) w = (w : ℂ) := by simp
    have ha : (algebraMap ℚ ℂ) ((a : ℤ) : ℚ) = (a : ℂ) := by simp
    have hb : (algebraMap ℚ ℂ) ((b : ℤ) : ℚ) = (b : ℂ) := by simp
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hu, hv', hw', ha, hb]
    field_simp at h
    linear_combination h
  have hP0 : P = 0 := by
    by_contra hne
    exact homega ⟨P, hne, haeval⟩
  have hvalA : Polynomial.eval (-(a : ℚ)) P = 0 := by rw [hP0, Polynomial.eval_zero]
  have hvalB : Polynomial.eval (-(b : ℚ)) P = 0 := by rw [hP0, Polynomial.eval_zero]
  have habQ : (a : ℚ) ≠ (b : ℚ) := by exact_mod_cast hab
  have hv : v = 0 := by
    rw [hPdef] at hvalA
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      neg_add_cancel, mul_zero, zero_add, zero_mul, add_zero] at hvalA
    rcases mul_eq_zero.mp hvalA with h1 | h2
    · exact h1
    · exact absurd (by linarith [h2] : (a : ℚ) = (b : ℚ)) habQ
  have hw : w = 0 := by
    rw [hPdef] at hvalB
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      neg_add_cancel, mul_zero, zero_add, add_zero] at hvalB
    rcases mul_eq_zero.mp hvalB with h1 | h2
    · exact h1
    · exact absurd (by linarith [h2] : (a : ℚ) = (b : ℚ)) habQ
  refine ⟨?_, hv, hw⟩
  have hfinal : Polynomial.C u
      * ((Polynomial.X + Polynomial.C (a : ℚ)) * (Polynomial.X + Polynomial.C (b : ℚ))) = 0 := by
    have h' := hP0
    rw [hPdef, hv, hw] at h'
    simpa using h'
  have hfac : (Polynomial.X + Polynomial.C (a : ℚ)) * (Polynomial.X + Polynomial.C (b : ℚ)) ≠ 0 :=
    mul_ne_zero (Polynomial.X_add_C_ne_zero _) (Polynomial.X_add_C_ne_zero _)
  rcases mul_eq_zero.mp hfinal with h1 | h2
  · exact Polynomial.C_eq_zero.mp h1
  · exact absurd h2 hfac

/-- **The reciprocal periods are rationally independent in pairs.** -/
theorem linearIndependent_inversePeriods {omega : ℂ} (homega : Transcendental ℚ omega)
    {n : Fin N → ℤ} (hn : Function.Injective n) {m : ℕ} (hm : 0 < m) {q r : Fin N} (hqr : q ≠ r) :
    LinearIndependent ℚ (ellipticGammaSourcePeriods (inversePeriod omega n m q)
      (inversePeriod omega n m r)) := by
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hnqr : n q ≠ n r := fun h => hqr (hn h)
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  rw [Fin.sum_univ_three] at hg
  simp only [ellipticGammaSourcePeriods, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def, inversePeriod] at hg
  have hrel : ((g 0 : ℚ) : ℂ) + ((-(g 1 * m) : ℚ) : ℂ) / (omega + ((n q : ℤ) : ℂ))
      + ((-(g 2 * m) : ℚ) : ℂ) / (omega + ((n r : ℤ) : ℂ)) = 0 := by
    push_cast
    rw [← hg]
    ring
  obtain ⟨h0, h1, h2⟩ := partialFraction_independent homega hnqr hrel
  fin_cases i
  · exact h0
  · have : g 1 * m = 0 := by linarith [neg_eq_zero.mp h1]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hmQ
  · have : g 2 * m = 0 := by linarith [neg_eq_zero.mp h2]
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hmQ

/-- **The direct periods carry no rank-three minor.**  Any two of them differ by a rational
number. -/
theorem not_rankThreeMinor_directPeriods {omega : ℂ} (n : Fin N → ℤ) {m : ℕ} (hm : 0 < m) :
    ¬ MultipleEllipticGammaHasRankThreeMinor (directPeriod omega n m) := by
  rintro ⟨q, r, hqr, hlin⟩
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  set g : Fin 3 → ℚ := ![-(((n q : ℤ) : ℚ) - ((n r : ℤ) : ℚ)) / (m : ℚ), 1, -1] with hg
  have hsum : ∑ i : Fin 3, g i •
      ellipticGammaSourcePeriods (directPeriod omega n m q) (directPeriod omega n m r) i = 0 := by
    rw [Fin.sum_univ_three]
    simp only [ellipticGammaSourcePeriods, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def, directPeriod, hg]
    push_cast
    field_simp
    ring
  have hone := Fintype.linearIndependent_iff.mp hlin g hsum 1
  rw [hg] at hone
  simp only [Matrix.cons_val_one] at hone
  exact one_ne_zero hone

/-- The direct periods lie in the upper half plane. -/
theorem directPeriod_im_pos {omega : ℂ} (himω : 0 < omega.im) (n : Fin N → ℤ) {m : ℕ} (hm : 0 < m)
    (j : Fin N) : 0 < (directPeriod omega n m j).im := by
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [directPeriod, Complex.div_im]
  simp only [Complex.add_im, Complex.intCast_im, add_zero, Complex.natCast_re,
    Complex.natCast_im, Complex.normSq_natCast, mul_zero, zero_div, sub_zero]
  positivity

/-- The reciprocal periods lie in the upper half plane. -/
theorem inversePeriod_im_pos {omega : ℂ} (homega : Transcendental ℚ omega) (himω : 0 < omega.im)
    (n : Fin N → ℤ) {m : ℕ} (hm : 0 < m) (j : Fin N) : 0 < (inversePeriod omega n m j).im := by
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hne : omega + ((n j : ℤ) : ℂ) ≠ 0 := add_intCast_ne_zero_of_transcendental homega (n j)
  have hnormpos : 0 < Complex.normSq (omega + ((n j : ℤ) : ℂ)) := by
    rw [Complex.normSq_pos]
    exact hne
  rw [inversePeriod, Complex.div_im]
  have hre : (-(m : ℂ)).re = -(m : ℝ) := by simp
  have him : (-(m : ℂ)).im = 0 := by simp
  have hwim : (omega + ((n j : ℤ) : ℂ)).im = omega.im := by simp
  rw [hre, him, hwim, zero_mul, zero_div, zero_sub, neg_mul, neg_div, neg_neg]
  exact div_pos (mul_pos hmpos himω) hnormpos

/-- No rank-three minor survives on a face of a family that has none. -/
theorem not_rankThreeMinor_face {ι : Type} [Fintype ι] [DecidableEq ι] (tau : ι → ℂ)
    (J : Finset ι) (h : ¬ MultipleEllipticGammaHasRankThreeMinor tau) :
    ¬ MultipleEllipticGammaHasRankThreeMinor (multipleEllipticGammaFaceParameters tau J) := by
  rintro ⟨q, r, hqr, hlin⟩
  exact h ⟨q.1, r.1, fun h' => hqr (Subtype.ext h'), hlin⟩

/-- **The direct family is differentially algebraic at augmented rank two.** -/
theorem directPeriod_differentialAlgebraic {omega : ℂ} (himω : 0 < omega.im) (n : Fin N → ℤ)
    {m : ℕ} (hm : 0 < m) (hN : 0 < N) :
    multipleEllipticGammaAugmentedPeriodRank (directPeriod omega n m) = 2 ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaMero (directPeriod omega n m)
          (directPeriod_im_pos himω n hm)) ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero (directPeriod omega n m)
          (directPeriod_im_pos himω n hm)) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hminor := not_rankThreeMinor_directPeriods (omega := omega) n hm
  have hrank : multipleEllipticGammaAugmentedPeriodRank (directPeriod omega n m) = 2 :=
    (augmentedPeriodRank_eq_two_iff_not_rankThreeMinor (directPeriod omega n m)
      (directPeriod_im_pos himω n hm)).2 hminor
  rcases (multipleEllipticGamma_exactPeriodRankDichotomy (directPeriod omega n m)
    (directPeriod_im_pos himω n hm)).1 with ⟨-, hDA, hDA'⟩ | ⟨h3, -, -⟩
  · exact ⟨hrank, hDA, hDA'⟩
  · omega

/-- **The reciprocal family is hypertranscendental at augmented rank at least three.** -/
theorem inversePeriod_hypertranscendental {omega : ℂ} (homega : Transcendental ℚ omega)
    (himω : 0 < omega.im) {n : Fin N → ℤ} (hn : Function.Injective n) {m : ℕ} (hm : 0 < m)
    (hN : 2 ≤ N) :
    3 ≤ multipleEllipticGammaAugmentedPeriodRank (inversePeriod omega n m) ∧
      HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaMero (inversePeriod omega n m)
          (inversePeriod_im_pos homega himω n hm)) ∧
      HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivMero (inversePeriod omega n m)
          (inversePeriod_im_pos homega himω n hm)) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hqr : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hminor : MultipleEllipticGammaHasRankThreeMinor (inversePeriod omega n m) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, hqr, linearIndependent_inversePeriods homega hn hm hqr⟩
  have hrank : 3 ≤ multipleEllipticGammaAugmentedPeriodRank (inversePeriod omega n m) :=
    rankThreeMinor_implies_three_le_augmentedPeriodRank (inversePeriod omega n m) hminor
  rcases (multipleEllipticGamma_exactPeriodRankDichotomy (inversePeriod omega n m)
    (inversePeriod_im_pos homega himω n hm)).1 with ⟨h2, -, -⟩ | ⟨-, hHT, hHT'⟩
  · omega
  · exact ⟨hrank, hHT, hHT'⟩

/-- **Every face of the direct family stays differentially algebraic.** -/
theorem directPeriodFace_differentialAlgebraic {omega : ℂ} (himω : 0 < omega.im) (n : Fin N → ℤ)
    {m : ℕ} (hm : 0 < m) (J : Finset (Fin N)) (hJ : Jᶜ.Nonempty) :
    multipleEllipticGammaAugmentedPeriodRank
        (multipleEllipticGammaFaceParameters (directPeriod omega n m) J) = 2 ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaFaceMero (directPeriod omega n m)
          (directPeriod_im_pos himω n hm) J) ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero (directPeriod omega n m)
          (directPeriod_im_pos himω n hm) J) := by
  haveI : Nonempty (MultipleEllipticGammaFaceIndex J) := by
    obtain ⟨i, hi⟩ := hJ
    exact ⟨⟨i, by simpa using hi⟩⟩
  have hminor := not_rankThreeMinor_face (directPeriod omega n m) J
    (not_rankThreeMinor_directPeriods (omega := omega) n hm)
  have hrank : multipleEllipticGammaAugmentedPeriodRank
      (multipleEllipticGammaFaceParameters (directPeriod omega n m) J) = 2 :=
    (augmentedPeriodRank_eq_two_iff_not_rankThreeMinor
      (multipleEllipticGammaFaceParameters (directPeriod omega n m) J)
      (fun i => directPeriod_im_pos himω n hm i.1)).2 hminor
  obtain ⟨h1, h2, -, -⟩ := multipleEllipticGammaFace_exactPeriodRankLaw
    (directPeriod omega n m) (directPeriod_im_pos himω n hm) J hJ
  exact ⟨hrank, h1.2 hrank, h2.2 hrank⟩

/-- **Every face of the reciprocal family with two surviving labels is hypertranscendental.** -/
theorem inversePeriodFace_hypertranscendental {omega : ℂ} (homega : Transcendental ℚ omega)
    (himω : 0 < omega.im) {n : Fin N → ℤ} (hn : Function.Injective n) {m : ℕ} (hm : 0 < m)
    (J : Finset (Fin N)) {q r : MultipleEllipticGammaFaceIndex J} (hqr : q ≠ r) :
    3 ≤ multipleEllipticGammaAugmentedPeriodRank
        (multipleEllipticGammaFaceParameters (inversePeriod omega n m) J) ∧
      HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaFaceMero (inversePeriod omega n m)
          (inversePeriod_im_pos homega himω n hm) J) ∧
      HypertranscendentalOver (RatFunc ℂ)
        (multipleEllipticGammaLogDerivFaceMero (inversePeriod omega n m)
          (inversePeriod_im_pos homega himω n hm) J) := by
  have hJ : Jᶜ.Nonempty := ⟨q.1, by simpa using q.2⟩
  have hqr' : q.1 ≠ r.1 := fun h => hqr (Subtype.ext h)
  have hminor : MultipleEllipticGammaHasRankThreeMinor
      (multipleEllipticGammaFaceParameters (inversePeriod omega n m) J) :=
    ⟨q, r, hqr, linearIndependent_inversePeriods homega hn hm hqr'⟩
  have hrank := rankThreeMinor_implies_three_le_augmentedPeriodRank
    (multipleEllipticGammaFaceParameters (inversePeriod omega n m) J) hminor
  obtain ⟨-, -, h3, h4⟩ := multipleEllipticGammaFace_exactPeriodRankLaw
    (inversePeriod omega n m) (inversePeriod_im_pos homega himω n hm) J hJ
  exact ⟨hrank, h3.2 hrank, h4.2 hrank⟩

/-- **Partial-fraction independence of the whole reciprocal packet.**  A rational combination of
`1` and all the reciprocals `1/(ω + n_j)` with distinct integers `n_j` vanishes only trivially. -/
theorem partialFraction_independent_family {omega : ℂ} (homega : Transcendental ℚ omega)
    {n : Fin N → ℤ} (hn : Function.Injective n) {c0 : ℚ} {c : Fin N → ℚ}
    (h : (c0 : ℂ) + ∑ j : Fin N, (c j : ℂ) / (omega + ((n j : ℤ) : ℂ)) = 0) :
    c0 = 0 ∧ ∀ j, c j = 0 := by
  classical
  have hQ : ∀ x : ℚ, (algebraMap ℚ ℂ) x = (x : ℂ) := fun x => by simp
  have hZ : ∀ k : ℤ, ((k : ℚ) : ℂ) = (k : ℂ) := fun k => by push_cast; ring
  have hne : ∀ k : Fin N, omega + ((n k : ℤ) : ℂ) ≠ 0 :=
    fun k => add_intCast_ne_zero_of_transcendental homega (n k)
  set P : Polynomial ℚ :=
    Polynomial.C c0 * ∏ k : Fin N, (Polynomial.X + Polynomial.C ((n k : ℤ) : ℚ))
      + ∑ j : Fin N, Polynomial.C (c j)
        * ∏ k ∈ Finset.univ.erase j, (Polynomial.X + Polynomial.C ((n k : ℤ) : ℚ)) with hPdef
  have haevalEq : Polynomial.aeval omega P
      = (c0 : ℂ) * ∏ k : Fin N, (omega + ((n k : ℤ) : ℂ))
        + ∑ j : Fin N, (c j : ℂ) * ∏ k ∈ Finset.univ.erase j, (omega + ((n k : ℤ) : ℂ)) := by
    rw [hPdef]
    simp only [map_add, map_mul, map_sum, map_prod, Polynomial.aeval_X, Polynomial.aeval_C, hQ, hZ]
  have haeval : Polynomial.aeval omega P = 0 := by
    rw [haevalEq]
    have hsplit : ∀ j : Fin N, (c j : ℂ) * ∏ k ∈ Finset.univ.erase j,
        (omega + ((n k : ℤ) : ℂ))
        = ((c j : ℂ) / (omega + ((n j : ℤ) : ℂ)))
          * ∏ k : Fin N, (omega + ((n k : ℤ) : ℂ)) := by
      intro j
      rw [← Finset.mul_prod_erase Finset.univ (fun k => omega + ((n k : ℤ) : ℂ))
        (Finset.mem_univ j)]
      field_simp
      rw [mul_div_assoc, div_self (hne j), mul_one]
    rw [Finset.sum_congr rfl (fun j _ => hsplit j), ← Finset.sum_mul,
      ← add_mul, h, zero_mul]
  have hP0 : P = 0 := by
    by_contra hPne
    exact homega ⟨P, hPne, haeval⟩
  have hprodne : ∀ i : Fin N,
      ∏ k ∈ Finset.univ.erase i, (-((n i : ℤ) : ℚ) + ((n k : ℤ) : ℚ)) ≠ 0 := by
    intro i
    refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    intro h0
    have hcast : ((n k : ℤ) : ℚ) = ((n i : ℤ) : ℚ) := by linarith
    exact hki (hn (by exact_mod_cast hcast))
  have hc : ∀ i : Fin N, c i = 0 := by
    intro i
    have hv : Polynomial.eval (-((n i : ℤ) : ℚ)) P = 0 := by rw [hP0, Polynomial.eval_zero]
    rw [hPdef] at hv
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_X] at hv
    have hzero1 : ∏ k : Fin N, (-((n i : ℤ) : ℚ) + ((n k : ℤ) : ℚ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
    have hzero2 : ∀ j ∈ (Finset.univ : Finset (Fin N)), j ≠ i →
        c j * ∏ k ∈ Finset.univ.erase j, (-((n i : ℤ) : ℚ) + ((n k : ℤ) : ℚ)) = 0 := by
      intro j _ hji
      have hmem : i ∈ Finset.univ.erase j :=
        Finset.mem_erase.mpr ⟨fun h => hji h.symm, Finset.mem_univ i⟩
      rw [Finset.prod_eq_zero hmem (by ring), mul_zero]
    rw [hzero1, mul_zero, zero_add, Finset.sum_eq_single i hzero2 (by simp)] at hv
    rcases mul_eq_zero.mp hv with h1 | h2
    · exact h1
    · exact absurd h2 (hprodne i)
  refine ⟨?_, hc⟩
  have hfinal : Polynomial.C c0 * ∏ k : Fin N,
      (Polynomial.X + Polynomial.C ((n k : ℤ) : ℚ)) = 0 := by
    have h' := hP0
    rw [hPdef] at h'
    have hzero : ∑ j : Fin N, Polynomial.C (c j)
        * ∏ k ∈ Finset.univ.erase j, (Polynomial.X + Polynomial.C ((n k : ℤ) : ℚ)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hc j, map_zero, zero_mul]
    rw [hzero, add_zero] at h'
    exact h'
  have hprodpoly : (∏ k : Fin N, (Polynomial.X + Polynomial.C ((n k : ℤ) : ℚ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => Polynomial.X_add_C_ne_zero _
  rcases mul_eq_zero.mp hfinal with h1 | h2
  · exact Polynomial.C_eq_zero.mp h1
  · exact absurd h2 hprodpoly

/-- **The reciprocal packet together with the unit period is rationally independent.** -/
theorem linearIndependent_inversePeriod_cons {omega : ℂ} (homega : Transcendental ℚ omega)
    {n : Fin N → ℤ} (hn : Function.Injective n) {m : ℕ} (hm : 0 < m) :
    LinearIndependent ℚ (Fin.cons 1 (inversePeriod omega n m) : Fin (N + 1) → ℂ) := by
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ, Rat.smul_def, inversePeriod, mul_one] at hg
  have hrel : ((g 0 : ℚ) : ℂ)
      + ∑ j : Fin N, ((-(g j.succ * m) : ℚ) : ℂ) / (omega + ((n j : ℤ) : ℂ)) = 0 := by
    push_cast
    rw [← hg]
    refine congrArg (fun x => ((g 0 : ℚ) : ℂ) + x) ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨h0, hj⟩ := partialFraction_independent_family homega hn hrel
  refine Fin.cases ?_ ?_ i
  · exact h0
  · intro j
    have hjj := hj j
    have hmul : g j.succ * m = 0 := by linarith [neg_eq_zero.mp hjj]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h hmQ

/-- **The reciprocal augmented period rank is exactly `N+1`.**  This is the rank reversal in its
sharp form: the direct family has rank two whatever `N` is. -/
theorem inversePeriod_augmentedPeriodRank {omega : ℂ} (homega : Transcendental ℚ omega)
    {n : Fin N → ℤ} (hn : Function.Injective n) {m : ℕ} (hm : 0 < m) :
    multipleEllipticGammaAugmentedPeriodRank (inversePeriod omega n m) = N + 1 := by
  rw [multipleEllipticGammaAugmentedPeriodRank, ← Fin.range_cons,
    finrank_span_eq_card (linearIndependent_inversePeriod_cons homega hn hm), Fintype.card_fin]

/-- **Reciprocal-period phase reversal.**  Componentwise reciprocalization of a rank-two period
family produces a family of augmented rank at least three: the multiple elliptic Gamma function and
its logarithmic derivative pass from the differentially algebraic phase to the hypertranscendental
one. -/
theorem reciprocalPeriod_phase_reversal {omega : ℂ} (homega : Transcendental ℚ omega)
    (himω : 0 < omega.im) {n : Fin N → ℤ} (hn : Function.Injective n) {m : ℕ} (hm : 0 < m)
    (hN : 2 ≤ N) :
    (multipleEllipticGammaAugmentedPeriodRank (directPeriod omega n m) = 2 ∧
        DifferentialAlgebraicOver (RatFunc ℂ)
          (multipleEllipticGammaMero (directPeriod omega n m)
            (directPeriod_im_pos himω n hm)) ∧
        DifferentialAlgebraicOver (RatFunc ℂ)
          (multipleEllipticGammaLogDerivMero (directPeriod omega n m)
            (directPeriod_im_pos himω n hm))) ∧
      (3 ≤ multipleEllipticGammaAugmentedPeriodRank (inversePeriod omega n m) ∧
        HypertranscendentalOver (RatFunc ℂ)
          (multipleEllipticGammaMero (inversePeriod omega n m)
            (inversePeriod_im_pos homega himω n hm)) ∧
        HypertranscendentalOver (RatFunc ℂ)
          (multipleEllipticGammaLogDerivMero (inversePeriod omega n m)
            (inversePeriod_im_pos homega himω n hm))) :=
  ⟨directPeriod_differentialAlgebraic himω n hm (by omega),
    inversePeriod_hypertranscendental homega himω hn hm hN⟩

end

end GaloisForLFunctions.HTGeometry
