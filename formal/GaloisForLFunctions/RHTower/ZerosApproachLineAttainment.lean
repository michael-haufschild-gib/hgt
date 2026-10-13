import GaloisForLFunctions.RHTower.XiLogDerivEventualPositivityAbscissa
import GaloisForLFunctions.RHTower.LagRatioLawAttained
import GaloisForLFunctions.RHTower.ConstrainedWeilApertureWindowMean

/-!
# Zeros approaching the line give attainment, and close the attainment dichotomies

Several one-sided receivers only yield a dichotomy: either RH holds, or the supremum `Θ` of the real
parts of the zeros is not attained (it is approached by zeros of growing height).

* bounded lags along one geometric progression `b^m`
  (`riemannHypothesis_or_not_attained_of_forall_le`);
* bounded lags on a logarithmically dense set
  (`riemannHypothesis_or_not_attained_of_logDense_bddAbove`);
* nonnegative twisted plateau Weil energies (`not_attainedTopExcess_of_twistedPlateau_nonneg`).

**Theorem** (`exists_attainedTop_of_zerosApproachLine`, `attainedTopExcess_of_zerosApproachLine`).
If the zeros approach the critical line and RH fails, the maximal real part `β₀ > ½` and the maximal
excess `|β − ½|` are attained.  Only finitely many zeros lie right of `½ + h` for
`h = (β₁ − ½)/2`, where `β₁ > ½` is the real part of any off-line zero right of the line, and a
finite nonempty set attains its maximum.

**Corollaries.**  For every base `b ≥ 2`,
`RH ⟺ (zeros approach the line) ∧ (the lag values Φ(m log b) are bounded above)`
(`riemannHypothesis_iff_zerosApproachLine_and_pow_integerLag_bddAbove`), and the same with any
logarithmically dense set of integers in place of the powers of `b`.  By the large-height ladder,
"zeros approach the line" may be replaced by eventual Hadamard positivity
(`riemannHypothesis_iff_eventualHadamardPositivity_and_pow_integerLag_bddAbove`).  So the attainment
gap of these arithmetic routes is exactly a large-height statement: RH splits into an asymptotic
condition that only sees the limit superior `Θ∞` of `Re ρ − ½`, and a one-sided bound on the lag
function sampled along a single geometric progression.
-/

open Complex Set

namespace RHTower

noncomputable section

open BacklundConverse LindelofSparse

/-- If RH fails, some zero lies strictly right of the critical line. -/
theorem exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re := by
  by_contra h
  push Not at h
  apply hRH
  refine riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase fun q => ?_
  have h1 := h q
  have h2 := h (xiZeroCopyReflectEquiv.symm q)
  have hr := spectral_im_eq (xiZeroCopyReflectEquiv.symm q)
  rw [xiSpectralPoint_reflect_symm, Complex.neg_im, spectral_im_eq] at hr
  linarith

/-- Under RH the zeros approach the line. -/
theorem zerosApproachLine_of_riemannHypothesis (hRH : RiemannHypothesis) : ZerosApproachLine := by
  intro h hh
  refine Set.finite_empty.subset fun q hq => ?_
  have hq' : h < (xiSpectralPoint q).im := hq
  rw [spectral_im_eq, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q] at hq'
  simp only [sub_self] at hq'
  exact absurd hq' (not_lt.mpr hh.le)

/-- **Zeros approaching the line attain the maximal real part.** -/
theorem exists_attainedTop_of_zerosApproachLine (hZ : ZerosApproachLine)
    (hRH : ¬ RiemannHypothesis) : ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
  set h : ℝ := ((q₁.1 : ℂ).re - 1 / 2) / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  set F : Set XiZeroCopy := {q | 1 / 2 + h < (q.1 : ℂ).re} with hF
  have hFfin : F.Finite := by
    refine (finite_abs_im_gt_of_zerosApproachLine hZ hh0).subset fun q hq => ?_
    simp only [hF, mem_setOf_eq] at hq ⊢
    rw [spectral_im_eq]
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  have hq₁F : q₁ ∈ F := by
    simp only [hF, mem_setOf_eq]; rw [hh]; linarith
  obtain ⟨q₀, hq₀F, hmax⟩ := hFfin.exists_maximalFor (fun q => (q.1 : ℂ).re) F ⟨q₁, hq₁F⟩
  have hq₀ : 1 / 2 + h < (q₀.1 : ℂ).re := hq₀F
  refine ⟨(q₀.1 : ℂ).re, by linarith, ⟨q₀, rfl⟩, fun q => ?_⟩
  by_cases hq : q ∈ F
  · by_contra hlt
    push Not at hlt
    exact absurd (hmax hq hlt.le) (not_le.mpr hlt)
  · simp only [hF, mem_setOf_eq, not_lt] at hq
    linarith

/-- **Zeros approaching the line attain the maximal excess `|β − ½|`.** -/
theorem attainedTopExcess_of_zerosApproachLine (hZ : ZerosApproachLine)
    (hRH : ¬ RiemannHypothesis) : AttainedTopExcess := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
  have hq₁im : |(xiSpectralPoint q₁).im| = (q₁.1 : ℂ).re - 1 / 2 := by
    rw [spectral_im_eq, abs_sub_comm, abs_of_pos (by linarith)]
  set h : ℝ := ((q₁.1 : ℂ).re - 1 / 2) / 2 with hh
  have hh0 : 0 < h := by rw [hh]; linarith
  set E : Set XiZeroCopy := {q | h < |(xiSpectralPoint q).im|} with hE
  have hEfin : E.Finite := finite_abs_im_gt_of_zerosApproachLine hZ hh0
  have hq₁E : q₁ ∈ E := by
    simp only [hE, mem_setOf_eq]; rw [hq₁im, hh]; linarith
  obtain ⟨q₀, hq₀E, hmax⟩ :=
    hEfin.exists_maximalFor (fun q => |(xiSpectralPoint q).im|) E ⟨q₁, hq₁E⟩
  have hq₀ : h < |(xiSpectralPoint q₀).im| := hq₀E
  refine ⟨|(xiSpectralPoint q₀).im|, by linarith, q₀, rfl, fun q => ?_⟩
  by_cases hq : q ∈ E
  · by_contra hlt
    push Not at hlt
    exact absurd (hmax hq hlt.le) (not_le.mpr hlt)
  · simp only [hE, mem_setOf_eq, not_lt] at hq
    linarith

/-- **RH splits into zeros approaching the line and bounded lags along one geometric
progression.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_pow_integerLag_bddAbove {b : ℕ}
    (hb : 2 ≤ b) :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ M : ℝ, ∀ m : ℕ, integerLag (b ^ m) ≤ M := by
  constructor
  · intro hRH
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_weilLagFunctionReal_bddAbove.mp hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH, M, fun m => hM _⟩
  · rintro ⟨hZ, M, hM⟩
    by_contra hRH
    obtain ⟨β₀, hβ, htop⟩ := exists_attainedTop_of_zerosApproachLine hZ hRH
    obtain ⟨m, -, hm⟩ := exists_pow_integerLag_gt_of_attainedTop hβ htop hb M
    linarith [hM m]

/-- **The same split on any logarithmically dense set of integers.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_logDense_integerLag_bddAbove {N : Set ℕ}
    (hN : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ L : ℝ, X ≤ L → ∃ n ∈ N, |Real.log n - L| ≤ δ) :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ M : ℝ, ∀ n ∈ N, integerLag n ≤ M := by
  constructor
  · intro hRH
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_weilLagFunctionReal_bddAbove.mp hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH, M, fun n _ => hM _⟩
  · rintro ⟨hZ, M, hM⟩
    by_contra hRH
    obtain ⟨β₀, hβ, htop⟩ := exists_attainedTop_of_zerosApproachLine hZ hRH
    obtain ⟨n, hn, hlt⟩ := exists_lag_gt_of_attainedTop_of_logDense hβ htop hN M
    linarith [hM n hn]

/-- **Eventual Hadamard positivity and bounded lags along one geometric progression give RH.** -/
theorem riemannHypothesis_iff_eventualHadamardPositivity_and_pow_integerLag_bddAbove {b : ℕ}
    (hb : 2 ≤ b) :
    RiemannHypothesis ↔
      EventualHadamardPositivity ∧ ∃ M : ℝ, ∀ m : ℕ, integerLag (b ^ m) ≤ M := by
  rw [eventualHadamardPositivity_iff_zerosApproachLine]
  exact riemannHypothesis_iff_zerosApproachLine_and_pow_integerLag_bddAbove hb

/-- **Zeros approaching the line and nonnegative twisted plateau energies give RH.** -/
theorem riemannHypothesis_of_zerosApproachLine_of_twistedPlateau_nonneg (hZ : ZerosApproachLine)
    (h : ∀ γ : ℝ, ∀ a : ℝ, ∀ ha0 : 0 ≤ a, 1 / 2 ≤ a →
      0 ≤ (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
            (twistedOddTest (plateauProfile a ha0) γ)).re) :
    RiemannHypothesis := by
  by_contra hRH
  exact not_attainedTopExcess_of_twistedPlateau_nonneg h
    (attainedTopExcess_of_zerosApproachLine hZ hRH)

end

end RHTower
