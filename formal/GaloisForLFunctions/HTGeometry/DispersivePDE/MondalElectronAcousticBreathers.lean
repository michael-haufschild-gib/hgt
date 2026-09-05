import GaloisForLFunctions.HTGeometry.DispersivePDE.MondalElectronAcousticKP

/-!
# Electron-acoustic KP breather interaction audit (arXiv:2609.03539)

Closed conjugate-pair consequences of equations (30), (31), (42), and (43).  The printed
breather coefficients are identified exactly as projective evaluations of the time-reversed
Hirota symbols found in the soliton audit.  A total positive interaction parameterization also
gives a premise-free family on which the real breather tau function never vanishes.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

def mondalComplexPair (re im : ℝ) : ℂ := (re : ℂ) + (im : ℂ) * Complex.I

theorem mondalComplexPair_conj (re im : ℝ) :
    starRingEnd ℂ (mondalComplexPair re im) = mondalComplexPair re (-im) := by
  simp [mondalComplexPair]

theorem mondalComplexPair_add_conj (re im : ℝ) :
    mondalComplexPair re im + mondalComplexPair re (-im) = (2 * re : ℝ) := by
  unfold mondalComplexPair
  push_cast
  ring

theorem mondalComplexPair_sub_conj (re im : ℝ) :
    mondalComplexPair re im - mondalComplexPair re (-im) =
      (2 * im : ℝ) * Complex.I := by
  unfold mondalComplexPair
  push_cast
  ring

noncomputable def mondalComplexTimeReversedHirotaSymbol
    (δ ρ : ℝ) (omega k l : ℂ) : ℂ :=
  omega * k + (δ : ℂ) * k ^ 4 + (ρ : ℂ) * l ^ 2

theorem mondalComplexTimeReversedHirotaSymbol_conj
    (δ ρ : ℝ) (omega k l : ℂ) :
    starRingEnd ℂ (mondalComplexTimeReversedHirotaSymbol δ ρ omega k l) =
      mondalComplexTimeReversedHirotaSymbol δ ρ
        (starRingEnd ℂ omega) (starRingEnd ℂ k) (starRingEnd ℂ l) := by
  simp [mondalComplexTimeReversedHirotaSymbol, map_add, map_mul, map_pow]

theorem mondalComplexTimeReversedHirotaSymbol_pureImaginary
    (δ ρ omegaIm kIm lIm : ℝ) :
    mondalComplexTimeReversedHirotaSymbol δ ρ
        ((2 * omegaIm : ℝ) * Complex.I)
        ((2 * kIm : ℝ) * Complex.I)
        ((2 * lIm : ℝ) * Complex.I) =
      ((-4 * omegaIm * kIm + 16 * δ * kIm ^ 4 - 4 * ρ * lIm ^ 2 : ℝ) : ℂ) := by
  unfold mondalComplexTimeReversedHirotaSymbol
  push_cast
  ring_nf
  simp
  ring

theorem mondalComplexTimeReversedHirotaSymbol_real
    (δ ρ omegaRe kRe lRe : ℝ) :
    mondalComplexTimeReversedHirotaSymbol δ ρ
        (2 * omegaRe : ℝ) (2 * kRe : ℝ) (2 * lRe : ℝ) =
      ((4 * omegaRe * kRe + 16 * δ * kRe ^ 4 + 4 * ρ * lRe ^ 2 : ℝ) : ℂ) := by
  unfold mondalComplexTimeReversedHirotaSymbol
  push_cast
  ring

/-! ## Right-moving breather coefficient (31) -/

def mondalPrintedRightBreatherNumerator (β γ n omegaIm q : ℝ) : ℝ :=
  4 * n * omegaIm + 16 * β * n ^ 4 + 4 * γ * q ^ 2

def mondalPrintedRightBreatherDenominator (β γ m omegaRe p : ℝ) : ℝ :=
  4 * m * omegaRe - 16 * β * m ^ 4 + 4 * γ * p ^ 2

theorem mondalPrintedRightBreatherNumerator_eq_symbol
    (β γ n omegaIm q : ℝ) :
    (mondalPrintedRightBreatherNumerator β γ n omegaIm q : ℂ) =
      -mondalComplexTimeReversedHirotaSymbol (-β) γ
        (mondalComplexPair 0 omegaIm - mondalComplexPair 0 (-omegaIm))
        (mondalComplexPair 0 n - mondalComplexPair 0 (-n))
        (mondalComplexPair 0 q - mondalComplexPair 0 (-q)) := by
  rw [mondalComplexPair_sub_conj, mondalComplexPair_sub_conj,
    mondalComplexPair_sub_conj,
    mondalComplexTimeReversedHirotaSymbol_pureImaginary]
  simp [mondalPrintedRightBreatherNumerator]
  ring

theorem mondalPrintedRightBreatherDenominator_eq_symbol
    (β γ m omegaRe p : ℝ) :
    (mondalPrintedRightBreatherDenominator β γ m omegaRe p : ℂ) =
      mondalComplexTimeReversedHirotaSymbol (-β) γ
        (mondalComplexPair omegaRe 0 + mondalComplexPair omegaRe 0)
        (mondalComplexPair m 0 + mondalComplexPair m 0)
        (mondalComplexPair p 0 + mondalComplexPair p 0) := by
  simp [mondalPrintedRightBreatherDenominator, mondalComplexPair,
    mondalComplexTimeReversedHirotaSymbol]
  ring

/-! ## Left-moving breather coefficient (43) -/

def mondalPrintedLeftBreatherNumerator (β γ n omegaIm q : ℝ) : ℝ :=
  4 * n * omegaIm - 16 * β * n ^ 4 - 4 * γ * q ^ 2

def mondalPrintedLeftBreatherDenominator (β γ m omegaRe p : ℝ) : ℝ :=
  4 * m * omegaRe + 16 * β * m ^ 4 - 4 * γ * p ^ 2

theorem mondalPrintedLeftBreatherNumerator_eq_symbol
    (β γ n omegaIm q : ℝ) :
    (mondalPrintedLeftBreatherNumerator β γ n omegaIm q : ℂ) =
      -mondalComplexTimeReversedHirotaSymbol β (-γ)
        (mondalComplexPair 0 omegaIm - mondalComplexPair 0 (-omegaIm))
        (mondalComplexPair 0 n - mondalComplexPair 0 (-n))
        (mondalComplexPair 0 q - mondalComplexPair 0 (-q)) := by
  rw [mondalComplexPair_sub_conj, mondalComplexPair_sub_conj,
    mondalComplexPair_sub_conj,
    mondalComplexTimeReversedHirotaSymbol_pureImaginary]
  simp [mondalPrintedLeftBreatherNumerator]
  ring

theorem mondalPrintedLeftBreatherDenominator_eq_symbol
    (β γ m omegaRe p : ℝ) :
    (mondalPrintedLeftBreatherDenominator β γ m omegaRe p : ℂ) =
      mondalComplexTimeReversedHirotaSymbol β (-γ)
        (mondalComplexPair omegaRe 0 + mondalComplexPair omegaRe 0)
        (mondalComplexPair m 0 + mondalComplexPair m 0)
        (mondalComplexPair p 0 + mondalComplexPair p 0) := by
  simp [mondalPrintedLeftBreatherDenominator, mondalComplexPair,
    mondalComplexTimeReversedHirotaSymbol]
  ring

/-! ## Premise-free nonsingular real breather tau family -/

noncomputable def mondalPositiveBreatherInteraction (a : ℝ) : ℝ := 1 + Real.exp a

theorem mondalPositiveBreatherInteraction_gt_one (a : ℝ) :
    1 < mondalPositiveBreatherInteraction a := by
  unfold mondalPositiveBreatherInteraction
  exact lt_add_of_pos_right 1 (Real.exp_pos a)

theorem mondalPositiveBreatherTau_pos (a : ℝ) (z : ℂ) :
    0 < mondalRealBreatherTau (mondalPositiveBreatherInteraction a) z := by
  have hexp : 0 < Real.exp z.re := Real.exp_pos z.re
  have hcos : 0 ≤ 1 + Real.cos z.im := by
    linarith [Real.neg_one_le_cos z.im]
  have hsquare : 0 ≤ (1 - Real.exp z.re) ^ 2 := sq_nonneg _
  have hmiddle : 0 ≤ 2 * Real.exp z.re * (1 + Real.cos z.im) := by positivity
  have hlast : 0 < Real.exp a * Real.exp z.re ^ 2 := by positivity
  rw [show mondalRealBreatherTau (mondalPositiveBreatherInteraction a) z =
      (1 - Real.exp z.re) ^ 2
        + 2 * Real.exp z.re * (1 + Real.cos z.im)
        + Real.exp a * Real.exp z.re ^ 2 by
    unfold mondalRealBreatherTau mondalPositiveBreatherInteraction
    rw [show (2 : ℝ) * z.re = z.re + z.re by ring, Real.exp_add]
    ring]
  positivity

theorem mondalPositiveBreatherTau_ne_zero (a : ℝ) (z : ℂ) :
    mondalRealBreatherTau (mondalPositiveBreatherInteraction a) z ≠ 0 :=
  ne_of_gt (mondalPositiveBreatherTau_pos a z)

end GaloisForLFunctions.HTGeometry.DispersivePDE
