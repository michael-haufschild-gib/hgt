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
  omega * k + (δ : ℂ) * k ^ (4 : ℕ) + (ρ : ℂ) * l ^ (2 : ℕ)

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
      ((-4 * omegaIm * kIm + 16 * δ * kIm ^ (4 : ℕ) - 4 * ρ * lIm ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold mondalComplexTimeReversedHirotaSymbol
  push_cast
  ring_nf
  simp
  ring

theorem mondalComplexTimeReversedHirotaSymbol_real
    (δ ρ omegaRe kRe lRe : ℝ) :
    mondalComplexTimeReversedHirotaSymbol δ ρ
        (2 * omegaRe : ℝ) (2 * kRe : ℝ) (2 * lRe : ℝ) =
      ((4 * omegaRe * kRe + 16 * δ * kRe ^ (4 : ℕ) + 4 * ρ * lRe ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold mondalComplexTimeReversedHirotaSymbol
  push_cast
  ring

/-! ## Right-moving breather coefficient (31) -/

def mondalPrintedRightBreatherNumerator (β γ n omegaIm q : ℝ) : ℝ :=
  4 * n * omegaIm + 16 * β * n ^ (4 : ℕ) + 4 * γ * q ^ (2 : ℕ)

def mondalPrintedRightBreatherDenominator (β γ m omegaRe p : ℝ) : ℝ :=
  4 * m * omegaRe - 16 * β * m ^ (4 : ℕ) + 4 * γ * p ^ (2 : ℕ)

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
  4 * n * omegaIm - 16 * β * n ^ (4 : ℕ) - 4 * γ * q ^ (2 : ℕ)

def mondalPrintedLeftBreatherDenominator (β γ m omegaRe p : ℝ) : ℝ :=
  4 * m * omegaRe + 16 * β * m ^ (4 : ℕ) - 4 * γ * p ^ (2 : ℕ)

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

/-! ## On-shell factorization and the physical breather obstruction -/

def mondalBreatherTransverseRe (m n slopeRe slopeIm : ℝ) : ℝ :=
  m * slopeRe - n * slopeIm

def mondalBreatherTransverseIm (m n slopeRe slopeIm : ℝ) : ℝ :=
  m * slopeIm + n * slopeRe

def mondalPrintedRightBreatherOmegaRe
    (β γ m n slopeRe slopeIm : ℝ) : ℝ :=
  β * (m ^ (3 : ℕ) - 3 * m * n ^ (2 : ℕ))
    - γ * (m * (slopeRe ^ (2 : ℕ) - slopeIm ^ (2 : ℕ)) - 2 * n * slopeRe * slopeIm)

def mondalPrintedRightBreatherOmegaIm
    (β γ m n slopeRe slopeIm : ℝ) : ℝ :=
  β * (3 * m ^ (2 : ℕ) * n - n ^ (3 : ℕ))
    - γ * (2 * m * slopeRe * slopeIm + n * (slopeRe ^ (2 : ℕ) - slopeIm ^ (2 : ℕ)))

theorem mondalPrintedRightBreatherNumerator_onShell_factor
    (β γ m n slopeRe slopeIm : ℝ) :
    mondalPrintedRightBreatherNumerator β γ n
        (mondalPrintedRightBreatherOmegaIm β γ m n slopeRe slopeIm)
        (mondalBreatherTransverseIm m n slopeRe slopeIm) =
      4 * (m ^ (2 : ℕ) + n ^ (2 : ℕ)) * (3 * β * n ^ (2 : ℕ) + γ * slopeIm ^ (2 : ℕ)) := by
  unfold mondalPrintedRightBreatherNumerator mondalPrintedRightBreatherOmegaIm
    mondalBreatherTransverseIm
  ring

theorem mondalPrintedRightBreatherDenominator_onShell_factor
    (β γ m n slopeRe slopeIm : ℝ) :
    mondalPrintedRightBreatherDenominator β γ m
        (mondalPrintedRightBreatherOmegaRe β γ m n slopeRe slopeIm)
        (mondalBreatherTransverseRe m n slopeRe slopeIm) =
      4 * (m ^ (2 : ℕ) + n ^ (2 : ℕ)) * (γ * slopeIm ^ (2 : ℕ) - 3 * β * m ^ (2 : ℕ)) := by
  unfold mondalPrintedRightBreatherDenominator mondalPrintedRightBreatherOmegaRe
    mondalBreatherTransverseRe
  ring

def mondalPrintedLeftBreatherOmegaRe
    (β γ m n slopeRe slopeIm : ℝ) : ℝ :=
  -mondalPrintedRightBreatherOmegaRe β γ m n slopeRe slopeIm

def mondalPrintedLeftBreatherOmegaIm
    (β γ m n slopeRe slopeIm : ℝ) : ℝ :=
  -mondalPrintedRightBreatherOmegaIm β γ m n slopeRe slopeIm

theorem mondalPrintedLeftBreatherNumerator_onShell_factor
    (β γ m n slopeRe slopeIm : ℝ) :
    mondalPrintedLeftBreatherNumerator β γ n
        (mondalPrintedLeftBreatherOmegaIm β γ m n slopeRe slopeIm)
        (mondalBreatherTransverseIm m n slopeRe slopeIm) =
      -4 * (m ^ (2 : ℕ) + n ^ (2 : ℕ)) * (3 * β * n ^ (2 : ℕ) + γ * slopeIm ^ (2 : ℕ)) := by
  unfold mondalPrintedLeftBreatherNumerator mondalPrintedLeftBreatherOmegaIm
    mondalPrintedRightBreatherOmegaIm mondalBreatherTransverseIm
  ring

theorem mondalPrintedLeftBreatherDenominator_onShell_factor
    (β γ m n slopeRe slopeIm : ℝ) :
    mondalPrintedLeftBreatherDenominator β γ m
        (mondalPrintedLeftBreatherOmegaRe β γ m n slopeRe slopeIm)
        (mondalBreatherTransverseRe m n slopeRe slopeIm) =
      -4 * (m ^ (2 : ℕ) + n ^ (2 : ℕ)) * (γ * slopeIm ^ (2 : ℕ) - 3 * β * m ^ (2 : ℕ)) := by
  unfold mondalPrintedLeftBreatherDenominator mondalPrintedLeftBreatherOmegaRe
    mondalPrintedRightBreatherOmegaRe mondalBreatherTransverseRe
  ring

noncomputable def mondalPhysicalBreatherNumerator
    (betaLog gammaLog n slopeIm : ℝ) : ℝ :=
  Real.exp gammaLog * slopeIm ^ (2 : ℕ) - 3 * Real.exp betaLog * n ^ (2 : ℕ)

noncomputable def mondalPhysicalBreatherDenominator
    (betaLog gammaLog mLog slopeIm : ℝ) : ℝ :=
  Real.exp gammaLog * slopeIm ^ (2 : ℕ) + 3 * Real.exp betaLog * Real.exp mLog ^ (2 : ℕ)

noncomputable def mondalPhysicalBreatherInteraction
    (betaLog gammaLog mLog n slopeIm : ℝ) : ℝ :=
  mondalPhysicalBreatherNumerator betaLog gammaLog n slopeIm /
    mondalPhysicalBreatherDenominator betaLog gammaLog mLog slopeIm

theorem mondalPhysicalBreatherDenominator_pos
    (betaLog gammaLog mLog slopeIm : ℝ) :
    0 < mondalPhysicalBreatherDenominator betaLog gammaLog mLog slopeIm := by
  unfold mondalPhysicalBreatherDenominator
  have hterm : 0 < 3 * Real.exp betaLog * Real.exp mLog ^ (2 : ℕ) := by positivity
  nlinarith [mul_nonneg (le_of_lt (Real.exp_pos gammaLog)) (sq_nonneg slopeIm)]

theorem mondalPhysicalBreatherInteraction_lt_one
    (betaLog gammaLog mLog n slopeIm : ℝ) :
    mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm < 1 := by
  rw [show mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm =
      mondalPhysicalBreatherNumerator betaLog gammaLog n slopeIm /
        mondalPhysicalBreatherDenominator betaLog gammaLog mLog slopeIm by rfl,
    div_lt_one (mondalPhysicalBreatherDenominator_pos betaLog gammaLog mLog slopeIm)]
  unfold mondalPhysicalBreatherNumerator mondalPhysicalBreatherDenominator
  have hbeta : 0 < Real.exp betaLog := Real.exp_pos betaLog
  have hm : 0 < Real.exp mLog := Real.exp_pos mLog
  have hsum : 0 < Real.exp mLog ^ (2 : ℕ) + n ^ (2 : ℕ) := by positivity
  have hgap : 0 < 3 * Real.exp betaLog * (Real.exp mLog ^ (2 : ℕ) + n ^ (2 : ℕ)) := by positivity
  nlinarith

theorem mondalPrintedRightBreatherInteraction_eq_physical
    (betaLog gammaLog mLog n slopeRe slopeIm : ℝ) :
    mondalPrintedRightBreatherNumerator (-Real.exp betaLog) (Real.exp gammaLog) n
          (mondalPrintedRightBreatherOmegaIm (-Real.exp betaLog) (Real.exp gammaLog)
            (Real.exp mLog) n slopeRe slopeIm)
          (mondalBreatherTransverseIm (Real.exp mLog) n slopeRe slopeIm) /
        mondalPrintedRightBreatherDenominator (-Real.exp betaLog) (Real.exp gammaLog)
          (Real.exp mLog)
          (mondalPrintedRightBreatherOmegaRe (-Real.exp betaLog) (Real.exp gammaLog)
            (Real.exp mLog) n slopeRe slopeIm)
          (mondalBreatherTransverseRe (Real.exp mLog) n slopeRe slopeIm) =
      mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm := by
  rw [mondalPrintedRightBreatherNumerator_onShell_factor,
    mondalPrintedRightBreatherDenominator_onShell_factor]
  have hnorm : Real.exp mLog ^ (2 : ℕ) + n ^ (2 : ℕ) ≠ 0 := by
    positivity
  have hcommon : 4 * (Real.exp mLog ^ (2 : ℕ) + n ^ (2 : ℕ)) ≠ 0 :=
    mul_ne_zero (by norm_num) hnorm
  rw [mul_div_mul_left _ _ hcommon]
  unfold mondalPhysicalBreatherInteraction mondalPhysicalBreatherNumerator
    mondalPhysicalBreatherDenominator
  congr 1 <;> ring

theorem mondalPrintedLeftBreatherInteraction_eq_physical
    (betaLog gammaLog mLog n slopeRe slopeIm : ℝ) :
    mondalPrintedLeftBreatherNumerator (-Real.exp betaLog) (Real.exp gammaLog) n
          (mondalPrintedLeftBreatherOmegaIm (-Real.exp betaLog) (Real.exp gammaLog)
            (Real.exp mLog) n slopeRe slopeIm)
          (mondalBreatherTransverseIm (Real.exp mLog) n slopeRe slopeIm) /
        mondalPrintedLeftBreatherDenominator (-Real.exp betaLog) (Real.exp gammaLog)
          (Real.exp mLog)
          (mondalPrintedLeftBreatherOmegaRe (-Real.exp betaLog) (Real.exp gammaLog)
            (Real.exp mLog) n slopeRe slopeIm)
          (mondalBreatherTransverseRe (Real.exp mLog) n slopeRe slopeIm) =
      mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm := by
  rw [mondalPrintedLeftBreatherNumerator_onShell_factor,
    mondalPrintedLeftBreatherDenominator_onShell_factor]
  have hnorm : Real.exp mLog ^ (2 : ℕ) + n ^ (2 : ℕ) ≠ 0 := by
    positivity
  have hcommon : -4 * (Real.exp mLog ^ (2 : ℕ) + n ^ (2 : ℕ)) ≠ 0 :=
    mul_ne_zero (by norm_num) hnorm
  rw [mul_div_mul_left _ _ hcommon]
  unfold mondalPhysicalBreatherInteraction mondalPhysicalBreatherNumerator
    mondalPhysicalBreatherDenominator
  congr 1 <;> ring

noncomputable def mondalBreatherTauNegativePoint : ℂ := mondalComplexPair 0 Real.pi

theorem mondalPhysicalBreatherTau_negative
    (betaLog gammaLog mLog n slopeIm : ℝ) :
    mondalRealBreatherTau
        (mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm)
        mondalBreatherTauNegativePoint < 0 := by
  have hinteraction :=
    mondalPhysicalBreatherInteraction_lt_one betaLog gammaLog mLog n slopeIm
  rw [show mondalRealBreatherTau
      (mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm)
      mondalBreatherTauNegativePoint =
        mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm - 1 by
    simp [mondalRealBreatherTau, mondalBreatherTauNegativePoint, mondalComplexPair]
    ring]
  exact sub_neg.mpr hinteraction

noncomputable def mondalBreatherRadialTau (interaction radialExp : ℝ) : ℝ :=
  1 - 2 * radialExp + interaction * radialExp ^ (2 : ℕ)

theorem mondalBreatherRadialTau_small_pos (interaction : ℝ) :
    0 < mondalBreatherRadialTau interaction (1 / (3 + |interaction|)) := by
  have hden : 0 < 3 + |interaction| := by positivity
  have hden_ne : 3 + |interaction| ≠ 0 := ne_of_gt hden
  rw [show mondalBreatherRadialTau interaction (1 / (3 + |interaction|)) =
      (3 + 4 * |interaction| + |interaction| ^ (2 : ℕ) + interaction) /
        (3 + |interaction|) ^ (2 : ℕ) by
    unfold mondalBreatherRadialTau
    field_simp [hden_ne]
    ring]
  apply div_pos
  · nlinarith [neg_abs_le interaction, abs_nonneg interaction,
      sq_nonneg |interaction|]
  · exact sq_pos_of_pos hden

theorem mondalPhysicalBreatherTau_has_zero
    (betaLog gammaLog mLog n slopeIm : ℝ) :
    ∃ z : ℂ,
      mondalRealBreatherTau
        (mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm) z = 0 := by
  let interaction := mondalPhysicalBreatherInteraction betaLog gammaLog mLog n slopeIm
  let radialSmall := 1 / (3 + |interaction|)
  have hinteraction : interaction < 1 :=
    mondalPhysicalBreatherInteraction_lt_one betaLog gammaLog mLog n slopeIm
  have hsmallPos : 0 < mondalBreatherRadialTau interaction radialSmall := by
    exact mondalBreatherRadialTau_small_pos interaction
  have honeNeg : mondalBreatherRadialTau interaction 1 < 0 := by
    unfold mondalBreatherRadialTau
    linarith
  have hradialSmallPos : 0 < radialSmall := by
    unfold radialSmall
    positivity
  have hradialSmallLe : radialSmall ≤ 1 := by
    unfold radialSmall
    have hden : (0 : ℝ) < 3 + |interaction| := by positivity
    rw [div_le_one hden]
    linarith [abs_nonneg interaction]
  have hcont : ContinuousOn (mondalBreatherRadialTau interaction)
      (Set.Icc radialSmall 1) := by
    apply Continuous.continuousOn
    unfold mondalBreatherRadialTau
    fun_prop
  have hzeroMem : (0 : ℝ) ∈ Set.Icc
      (mondalBreatherRadialTau interaction 1)
      (mondalBreatherRadialTau interaction radialSmall) :=
    ⟨le_of_lt honeNeg, le_of_lt hsmallPos⟩
  obtain ⟨radialExp, hradialExp, hzero⟩ :=
    intermediate_value_Icc' hradialSmallLe hcont hzeroMem
  have hradialExpPos : 0 < radialExp := lt_of_lt_of_le hradialSmallPos hradialExp.1
  have hexpTwo : Real.exp (2 * Real.log radialExp) = radialExp ^ (2 : ℕ) := by
    rw [show (2 : ℝ) * Real.log radialExp =
      Real.log radialExp + Real.log radialExp by ring, Real.exp_add,
      Real.exp_log hradialExpPos]
    ring
  refine ⟨mondalComplexPair (Real.log radialExp) Real.pi, ?_⟩
  rw [show mondalRealBreatherTau interaction
      (mondalComplexPair (Real.log radialExp) Real.pi) =
        mondalBreatherRadialTau interaction radialExp by
    unfold mondalRealBreatherTau mondalComplexPair mondalBreatherRadialTau
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.ofReal_im,
      zero_add, add_zero, mul_one, Real.cos_pi, Real.exp_log hradialExpPos]
    rw [hexpTwo]
    ring]
  exact hzero

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
  have hsquare : 0 ≤ (1 - Real.exp z.re) ^ (2 : ℕ) := sq_nonneg _
  have hmiddle : 0 ≤ 2 * Real.exp z.re * (1 + Real.cos z.im) := by positivity
  have hlast : 0 < Real.exp a * Real.exp z.re ^ (2 : ℕ) := by positivity
  rw [show mondalRealBreatherTau (mondalPositiveBreatherInteraction a) z =
      (1 - Real.exp z.re) ^ (2 : ℕ)
        + 2 * Real.exp z.re * (1 + Real.cos z.im)
        + Real.exp a * Real.exp z.re ^ (2 : ℕ) by
    unfold mondalRealBreatherTau mondalPositiveBreatherInteraction
    rw [show (2 : ℝ) * z.re = z.re + z.re by ring, Real.exp_add]
    ring]
  positivity

theorem mondalPositiveBreatherTau_ne_zero (a : ℝ) (z : ℂ) :
    mondalRealBreatherTau (mondalPositiveBreatherInteraction a) z ≠ 0 :=
  ne_of_gt (mondalPositiveBreatherTau_pos a z)

end GaloisForLFunctions.HTGeometry.DispersivePDE
