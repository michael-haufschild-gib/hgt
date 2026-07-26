import GaloisForLFunctions.HTGeometry.DimensionalQEDGammaGaugePartitionUniversalityLaw
import GaloisForLFunctions.HTGeometry.GammaIntegerOrbitOpenClosedSpinUniversalityLaw
import GaloisForLFunctions.RHTower.ThermalBetaQEDZetaThreeGammaOrbitSuperselectionLaw
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Integer-string/QED/thermal/zeta six-gauge-class universality

Five physical Gamma sectors are encoded by distinct charge vectors on the
three translation orbits represented by `1/4`, `1/2`, and `1`.  Quotients of
distinct vectors retain a nonzero separated charge and are therefore
hypertranscendental.  The differentially algebraic integer-string sector is a
sixth gauge class.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace RHTower

open GaloisForLFunctions Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

private theorem gaugeEquivalent_of_nonzero_of_differentialAlgebraic
    {x y : meroField Set.univ} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x)
    (hy : DifferentialAlgebraicOver (RatFunc ℂ) y) :
    GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
      (F := RatFunc ℂ) x y := by
  exact ⟨x / y, div_ne_zero hx0 hy0,
    GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_div hx hy,
    (div_mul_cancel₀ x hy0).symm⟩

private theorem not_gaugeEquivalent_of_differentialAlgebraic_of_hypertranscendental
    {x y : meroField Set.univ}
    (hx : DifferentialAlgebraicOver (RatFunc ℂ) x)
    (hy : HypertranscendentalOver (RatFunc ℂ) y) :
    ¬ GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
      (F := RatFunc ℂ) x y := by
  rintro ⟨g, hg0, hg, hxy⟩
  apply hy
  have hDA : DifferentialAlgebraicOver (RatFunc ℂ) (g⁻¹ * x) :=
    GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_mul
      (GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_inv hg) hx
  rw [hxy] at hDA
  simpa [hg0, mul_assoc] using hDA

/-- Quarter-, half-, and integral-translation Gamma-orbit representatives. -/
def qedThermalZetaGammaOrbitShifts : Fin 3 → ℂ :=
  ![(1 / 4 : ℂ), (1 / 2 : ℂ), 1]

/-- Charge vectors for scalar QED, spinor QED, their ratio, thermal/de Sitter,
and centered-zeta positive reconstruction. -/
def qedThermalZetaGammaOrbitCharges : Fin 5 → Fin 3 → ℤ :=
  ![![0, 1, 0], ![0, 0, 1], ![0, -1, 1], ![0, 0, 2], ![4, 0, 0]]

/-- The five exact finite Gamma-product representatives. -/
def qedThermalZetaGammaOrbitCarrier (i : Fin 5) : meroField Set.univ :=
  gammaOrbitProductMero qedThermalZetaGammaOrbitShifts
    (qedThermalZetaGammaOrbitCharges i)

theorem qedThermalZetaGammaOrbitCharges_injective :
    Function.Injective qedThermalZetaGammaOrbitCharges := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [qedThermalZetaGammaOrbitCharges]

private theorem quarter_multiple_ne_integer (a : ℤ) (ha : ¬ 4 ∣ a)
    (n : ℤ) : ((a : ℂ) / 4) ≠ (n : ℂ) := by
  intro h
  have hfour : (a : ℂ) = 4 * (n : ℂ) := by
    calc
      (a : ℂ) = 4 * ((a : ℂ) / 4) := by ring
      _ = 4 * (n : ℂ) := by rw [h]
  have hz : a = 4 * n := by
    exact_mod_cast hfour
  exact ha ⟨n, by omega⟩

/-- The three chosen shifts lie in distinct integer-translation orbits. -/
theorem qedThermalZetaGammaOrbitShifts_separated
    (c c₀ : Fin 3) (hc : c ≠ c₀) (n : ℤ) :
    qedThermalZetaGammaOrbitShifts c -
        qedThermalZetaGammaOrbitShifts c₀ ≠ (n : ℂ) := by
  fin_cases c <;> fin_cases c₀
  all_goals simp_all [qedThermalZetaGammaOrbitShifts]
  · have h := quarter_multiple_ne_integer (-1) (by norm_num) n
    norm_num at h ⊢
    exact h
  · have h := quarter_multiple_ne_integer (-3) (by norm_num) n
    norm_num at h ⊢
    exact h
  · have h := quarter_multiple_ne_integer 1 (by norm_num) n
    norm_num at h ⊢
    exact h
  · have h := quarter_multiple_ne_integer (-2) (by norm_num) n
    norm_num at h ⊢
    exact h
  · have h := quarter_multiple_ne_integer 3 (by norm_num) n
    norm_num at h ⊢
    exact h
  · have h := quarter_multiple_ne_integer 2 (by norm_num) n
    norm_num at h ⊢
    exact h

/-- Quotients in the atlas subtract their Gamma-orbit charge vectors. -/
theorem qedThermalZetaGammaOrbitCarrier_div
    (i j : Fin 5) :
    qedThermalZetaGammaOrbitCarrier i /
        qedThermalZetaGammaOrbitCarrier j =
      gammaOrbitProductMero qedThermalZetaGammaOrbitShifts
        (fun c => qedThermalZetaGammaOrbitCharges i c -
          qedThermalZetaGammaOrbitCharges j c) := by
  classical
  simp only [qedThermalZetaGammaOrbitCarrier, gammaOrbitProductMero]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro c _
  exact (zpow_sub₀ (gammaShiftMero_ne_zero _) _ _).symm

/-- Every nonzero atlas charge vector gives an HT Gamma carrier. -/
theorem hypertranscendentalOver_qedThermalZetaGammaOrbitCarrier
    (i : Fin 5) :
    HypertranscendentalOver (RatFunc ℂ)
      (qedThermalZetaGammaOrbitCarrier i) := by
  fin_cases i
  · apply hypertranscendentalOver_gammaOrbitProductMero
      qedThermalZetaGammaOrbitShifts
        (qedThermalZetaGammaOrbitCharges 0) 1
    · change (1 : ℤ) ≠ 0
      norm_num
    · exact fun c hc n =>
        qedThermalZetaGammaOrbitShifts_separated c 1 hc n
  · apply hypertranscendentalOver_gammaOrbitProductMero
      qedThermalZetaGammaOrbitShifts
        (qedThermalZetaGammaOrbitCharges 1) 2
    · change (1 : ℤ) ≠ 0
      norm_num
    · exact fun c hc n =>
        qedThermalZetaGammaOrbitShifts_separated c 2 hc n
  · apply hypertranscendentalOver_gammaOrbitProductMero
      qedThermalZetaGammaOrbitShifts
        (qedThermalZetaGammaOrbitCharges 2) 1
    · change (-1 : ℤ) ≠ 0
      norm_num
    · exact fun c hc n =>
        qedThermalZetaGammaOrbitShifts_separated c 1 hc n
  · apply hypertranscendentalOver_gammaOrbitProductMero
      qedThermalZetaGammaOrbitShifts
        (qedThermalZetaGammaOrbitCharges 3) 2
    · change (2 : ℤ) ≠ 0
      norm_num
    · exact fun c hc n =>
        qedThermalZetaGammaOrbitShifts_separated c 2 hc n
  · apply hypertranscendentalOver_gammaOrbitProductMero
      qedThermalZetaGammaOrbitShifts
        (qedThermalZetaGammaOrbitCharges 4) 0
    · change (4 : ℤ) ≠ 0
      norm_num
    · exact fun c hc n =>
        qedThermalZetaGammaOrbitShifts_separated c 0 hc n

/-- Distinct atlas labels have an HT quotient. -/
theorem hypertranscendentalOver_qedThermalZetaGammaOrbitCarrier_div
    {i j : Fin 5} (hij : i ≠ j) :
    HypertranscendentalOver (RatFunc ℂ)
      (qedThermalZetaGammaOrbitCarrier i /
        qedThermalZetaGammaOrbitCarrier j) := by
  rw [qedThermalZetaGammaOrbitCarrier_div]
  have hcharges :
      qedThermalZetaGammaOrbitCharges i ≠
        qedThermalZetaGammaOrbitCharges j := by
    intro h
    exact hij (qedThermalZetaGammaOrbitCharges_injective h)
  obtain ⟨c₀, hc₀⟩ :
      ∃ c₀, qedThermalZetaGammaOrbitCharges i c₀ ≠
        qedThermalZetaGammaOrbitCharges j c₀ := by
    by_contra h
    apply hcharges
    funext c
    exact not_ne_iff.mp (not_exists.mp h c)
  apply hypertranscendentalOver_gammaOrbitProductMero
    qedThermalZetaGammaOrbitShifts
      (fun c => qedThermalZetaGammaOrbitCharges i c -
        qedThermalZetaGammaOrbitCharges j c) c₀
  · exact sub_ne_zero.mpr hc₀
  · exact fun c hc n =>
      qedThermalZetaGammaOrbitShifts_separated c c₀ hc n

/-- The five nonzero Gamma-charge sectors are pairwise distinct modulo
nonzero differential-algebraic multiplication. -/
theorem qedThermalZetaGammaOrbitCarrier_pairwiseGaugeSeparated :
    Set.Pairwise (Set.univ : Set (Fin 5))
      (fun i j =>
        ¬ GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
          (F := RatFunc ℂ) (qedThermalZetaGammaOrbitCarrier i)
            (qedThermalZetaGammaOrbitCarrier j)) := by
  intro i _ j _ hij
  exact not_differentialAlgebraicGaugeEquivalent_of_div_hypertranscendental
    (gammaOrbitProductMero_ne_zero qedThermalZetaGammaOrbitShifts
      (qedThermalZetaGammaOrbitCharges j))
    (hypertranscendentalOver_qedThermalZetaGammaOrbitCarrier_div hij)

theorem constantMagneticScalarQEDGammaCarrierMero_eq_gammaOrbitCarrier :
    constantMagneticScalarQEDGammaCarrierMero =
      qedThermalZetaGammaOrbitCarrier 0 := by
  simp [constantMagneticScalarQEDGammaCarrierMero,
    qedThermalZetaGammaOrbitCarrier, gammaOrbitProductMero,
    qedThermalZetaGammaOrbitShifts, qedThermalZetaGammaOrbitCharges,
    Fin.prod_univ_three]

theorem constantMagneticSpinorQEDGammaCarrierMero_eq_gammaOrbitCarrier :
    constantMagneticSpinorQEDGammaCarrierMero =
      qedThermalZetaGammaOrbitCarrier 1 := by
  simp [constantMagneticSpinorQEDGammaCarrierMero,
    qedThermalZetaGammaOrbitCarrier, gammaOrbitProductMero,
    qedThermalZetaGammaOrbitShifts, qedThermalZetaGammaOrbitCharges,
    Fin.prod_univ_three]

theorem constantMagneticQEDSpinStatisticsRatioMero_eq_gammaOrbitCarrier :
    constantMagneticQEDSpinStatisticsRatioMero =
      qedThermalZetaGammaOrbitCarrier 2 := by
  simp [constantMagneticQEDSpinStatisticsRatioMero,
    constantMagneticSpinorQEDGammaCarrierMero,
    constantMagneticScalarQEDGammaCarrierMero,
    qedThermalZetaGammaOrbitCarrier, gammaOrbitProductMero,
    qedThermalZetaGammaOrbitShifts, qedThermalZetaGammaOrbitCharges,
    Fin.prod_univ_three, div_eq_mul_inv]
  ring

theorem centeredZetaPositiveReconstructionMero_eq_gammaOrbitCarrier :
    centeredZetaPositiveReconstructionMero =
      qedThermalZetaGammaOrbitCarrier 4 := by
  rw [centeredZetaPositiveReconstructionMero,
    centeredZetaGammaIntensity_sq_div_phase_eq_positiveFourth]
  simp [qedThermalZetaGammaOrbitCarrier, gammaOrbitProductMero,
    qedThermalZetaGammaOrbitShifts, qedThermalZetaGammaOrbitCharges,
    Fin.prod_univ_three]
  rfl

private theorem thermalGammaOrbitCarrier_eq_spinor_sq :
    qedThermalZetaGammaOrbitCarrier 3 =
      constantMagneticSpinorQEDGammaCarrierMero ^ 2 := by
  simp [constantMagneticSpinorQEDGammaCarrierMero,
    qedThermalZetaGammaOrbitCarrier, gammaOrbitProductMero,
    qedThermalZetaGammaOrbitShifts, qedThermalZetaGammaOrbitCharges,
    Fin.prod_univ_three]
  rfl

/-- Thermal/de Sitter positive reconstruction is the charge-two integral
atlas sector up to its explicit recurrence/exponential DA gauge. -/
theorem thermalDeSitterPositiveReconstructionMero_gammaOrbitGaugeEquivalent
    (ell : ℕ) (lambda : ℂ) :
    GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
      (F := RatFunc ℂ) (thermalDeSitterPositiveReconstructionMero ell lambda)
        (qedThermalZetaGammaOrbitCarrier 3) := by
  have hcross :=
    thermalDeSitterQEDSpinCrossRatioMero_eq_gauge_mul_combinedQED ell lambda
  have hratio0 : constantMagneticQEDSpinStatisticsRatioMero ≠ 0 :=
    constantMagneticQEDSpinStatisticsRatioMero_ne_zero
  have hthermal :
      thermalDeSitterPositiveReconstructionMero ell lambda =
        thermalDeSitterQEDSpinCrossGaugeMero ell lambda *
          constantMagneticSpinorQEDGammaCarrierMero ^ 2 := by
    calc
      thermalDeSitterPositiveReconstructionMero ell lambda =
          thermalDeSitterQEDSpinCrossRatioMero ell lambda *
            constantMagneticQEDSpinStatisticsRatioMero := by
              rw [thermalDeSitterQEDSpinCrossRatioMero]
              exact (div_mul_cancel₀ _ hratio0).symm
      _ = (thermalDeSitterQEDSpinCrossGaugeMero ell lambda *
            constantMagneticQEDCombinedGammaCarrierMero) *
          constantMagneticQEDSpinStatisticsRatioMero := by rw [hcross]
      _ = thermalDeSitterQEDSpinCrossGaugeMero ell lambda *
          constantMagneticSpinorQEDGammaCarrierMero ^ 2 := by
            rw [constantMagneticQEDCombinedGammaCarrierMero,
              constantMagneticQEDSpinStatisticsRatioMero]
            field_simp [constantMagneticScalarQEDGammaCarrierMero,
              gammaShiftMero_ne_zero]
  refine ⟨thermalDeSitterQEDSpinCrossGaugeMero ell lambda,
    thermalDeSitterQEDSpinCrossGaugeMero_ne_zero ell lambda,
    differentialAlgebraicOver_thermalDeSitterQEDSpinCrossGaugeMero ell lambda,
    ?_⟩
  rw [thermalGammaOrbitCarrier_eq_spinor_sq]
  exact hthermal

/-- Six-class certificate: one DA integer-string class and five pairwise
separated nonzero Gamma-charge classes, with exact physical identifications. -/
structure IntegerStringQEDThermalZetaSixGaugeClassCertificate
    (a N : ℂ) (ell : ℕ) (lambda : ℂ) : Prop where
  integerStringCollapse :
    DifferentialAlgebraicOver (RatFunc ℂ) (generalizedSpinTowerChannelMero N) ∧
      DifferentialAlgebraicOver (RatFunc ℂ) (reducedVenezianoAmplitudeMero a N) ∧
      DifferentialAlgebraicOver (RatFunc ℂ)
        (reducedVirasoroShapiroAmplitudeMero a N)
  integerStringNonzero :
    generalizedSpinTowerChannelMero N ≠ 0 ∧
      reducedVenezianoAmplitudeMero a N ≠ 0 ∧
      reducedVirasoroShapiroAmplitudeMero a N ≠ 0
  spinOpen :
    GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
      (F := RatFunc ℂ) (generalizedSpinTowerChannelMero N)
        (reducedVenezianoAmplitudeMero a N)
  spinClosed :
    GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
      (F := RatFunc ℂ) (generalizedSpinTowerChannelMero N)
        (reducedVirasoroShapiroAmplitudeMero a N)
  gammaCarriersNonzero :
    ∀ i, qedThermalZetaGammaOrbitCarrier i ≠ 0
  gammaCarriersHypertranscendental :
    ∀ i, HypertranscendentalOver (RatFunc ℂ)
      (qedThermalZetaGammaOrbitCarrier i)
  gammaCarriersPairwiseSeparated :
    Set.Pairwise (Set.univ : Set (Fin 5))
      (fun i j =>
        ¬ GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
          (F := RatFunc ℂ) (qedThermalZetaGammaOrbitCarrier i)
            (qedThermalZetaGammaOrbitCarrier j))
  integerStringSeparated :
    ∀ i,
      ¬ GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
        (F := RatFunc ℂ) (generalizedSpinTowerChannelMero N)
          (qedThermalZetaGammaOrbitCarrier i)
  scalarQED : constantMagneticScalarQEDGammaCarrierMero =
    qedThermalZetaGammaOrbitCarrier 0
  spinorQED : constantMagneticSpinorQEDGammaCarrierMero =
    qedThermalZetaGammaOrbitCarrier 1
  spinStatistics : constantMagneticQEDSpinStatisticsRatioMero =
    qedThermalZetaGammaOrbitCarrier 2
  thermal :
    GaloisForLFunctions.HTGeometry.DifferentialAlgebraicGaugeEquivalent
      (F := RatFunc ℂ) (thermalDeSitterPositiveReconstructionMero ell lambda)
        (qedThermalZetaGammaOrbitCarrier 3)
  centeredZeta : centeredZetaPositiveReconstructionMero =
    qedThermalZetaGammaOrbitCarrier 4

/-- **Integer-string/QED/thermal/zeta six-gauge-class law.** At every
integer string channel, the string class and the five physical Gamma-charge
sectors form six pairwise distinct nonzero DA multiplicative gauge classes. -/
theorem integerStringQEDThermalZeta_sixGaugeClassUniversality
    (a N : ℂ) (hN : ∃ k : ℤ, N = (k : ℂ))
    (ell : ℕ) (lambda : ℂ) :
    IntegerStringQEDThermalZetaSixGaugeClassCertificate
      a N ell lambda := by
  have hcollapse :=
    (gammaIntegerOrbit_openClosedSpin_simultaneousCollapse a N).1 hN
  have hnegative (b : ℂ) : gammaNegativeShiftMero b ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero b)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - b)))
  have hspin0 : generalizedSpinTowerChannelMero N ≠ 0 := by
    rw [generalizedSpinTowerChannelMero]
    exact div_ne_zero
      (mul_ne_zero (hnegative 1) (gammaShiftMero_ne_zero (1 + N)))
      (mul_ne_zero (gammaShiftMero_ne_zero 1) (hnegative (1 + N)))
  have hopen0 : reducedVenezianoAmplitudeMero a N ≠ 0 := by
    rw [reducedVenezianoAmplitudeMero]
    exact div_ne_zero (gammaShiftMero_ne_zero a)
      (gammaShiftMero_ne_zero (a + N))
  have hclosed0 : reducedVirasoroShapiroAmplitudeMero a N ≠ 0 := by
    rw [reducedVirasoroShapiroAmplitudeMero]
    exact div_ne_zero
      (mul_ne_zero (gammaShiftMero_ne_zero a) (hnegative (1 - a - N)))
      (mul_ne_zero (hnegative (1 - a)) (gammaShiftMero_ne_zero (a + N)))
  refine {
    integerStringCollapse := hcollapse
    integerStringNonzero := ⟨hspin0, hopen0, hclosed0⟩
    spinOpen := gaugeEquivalent_of_nonzero_of_differentialAlgebraic
      hspin0 hopen0 hcollapse.1 hcollapse.2.1
    spinClosed := gaugeEquivalent_of_nonzero_of_differentialAlgebraic
      hspin0 hclosed0 hcollapse.1 hcollapse.2.2
    gammaCarriersNonzero := fun i =>
      gammaOrbitProductMero_ne_zero qedThermalZetaGammaOrbitShifts
        (qedThermalZetaGammaOrbitCharges i)
    gammaCarriersHypertranscendental :=
      hypertranscendentalOver_qedThermalZetaGammaOrbitCarrier
    gammaCarriersPairwiseSeparated :=
      qedThermalZetaGammaOrbitCarrier_pairwiseGaugeSeparated
    integerStringSeparated := ?_
    scalarQED :=
      constantMagneticScalarQEDGammaCarrierMero_eq_gammaOrbitCarrier
    spinorQED :=
      constantMagneticSpinorQEDGammaCarrierMero_eq_gammaOrbitCarrier
    spinStatistics :=
      constantMagneticQEDSpinStatisticsRatioMero_eq_gammaOrbitCarrier
    thermal :=
      thermalDeSitterPositiveReconstructionMero_gammaOrbitGaugeEquivalent
        ell lambda
    centeredZeta :=
      centeredZetaPositiveReconstructionMero_eq_gammaOrbitCarrier }
  intro i
  exact not_gaugeEquivalent_of_differentialAlgebraic_of_hypertranscendental
    hcollapse.1
    (hypertranscendentalOver_qedThermalZetaGammaOrbitCarrier i)

end

end RHTower
