import GaloisForLFunctions.ArithmeticDefectRigidity.CompleteWienerSourceRowsRespectDilation
import GaloisForLFunctions.ArithmeticDefectRigidity.TheAdmittedCofactorKernelIsUnique
import GaloisForLFunctions.ArithmeticDefectRigidity.WienerUnitsTransportCofactorGrams
import GaloisForLFunctions.ArithmeticDefectRigidity.PaidCorrectionsPreserveNormalizedCofactorGrams
import GaloisForLFunctions.ArithmeticOrientationTheory.UnitsOfTheWienerMonoidPreservePayment

/-!
# Real Wiener convolution transports actual cofactor Grams

Exact source convolution differs from the complete Wiener dilation by a paid
mean correction. Its escaping Gram limit is the cyclic orbit Gram of the
Wiener action. Units preserve a positive energy ratio and give unitary transport.
-/

section
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The normalized Gram table of the complete source row acted on by a Wiener unit. -/
def wienerUnitSourceGram (ε : SubcriticalDamping)
    (u : (WienerAlgebraAt (1 / 2))ˣ) (T : ℕ) (j k : ℕ+) : ℂ :=
  wienerSourcePairing ε T ((u : WienerAlgebraAt (1 / 2)) * pointMass j)
      ((u : WienerAlgebraAt (1 / 2)) * pointMass k) /
    wienerSourcePairing ε T u u

namespace ActualCofactorLimit

theorem wienerRepresentation_unit_mul_pointMass_vector {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (u : (WienerAlgebraAt (1 / 2))ˣ) (j : ℕ+) :
    wienerRepresentation L ((u : WienerAlgebraAt (1 / 2)) * pointMass j) (vector L 1) =
      unitVector L u j := by
  rw [map_mul, wienerRepresentation_pointMass, mul_apply_eq_comp, dilation_vector, mul_one]
  rfl

/-- A unit acts on the full source energy with a positive limiting energy ratio. -/
theorem unit_source_energy_ratio_tendsto {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (u : (WienerAlgebraAt (1 / 2))ˣ) :
    Tendsto (fun m => complexWienerEnergy ε u (L.subsequence m) /
      dampedMobiusEnergy ε (L.subsequence m + 1)) atTop
      (𝓝 (‖unitVector L u 1‖ ^ 2)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (wienerSourcePairing_tendsto L u u)
  change Tendsto (fun m => (wienerSourcePairing ε (L.subsequence m) u u).re)
    atTop (𝓝 (inner ℂ (unitVector L u 1) (unitVector L u 1)).re) at h
  rw [inner_self_eq_norm_sq_to_K] at h
  simpa only [wienerSourcePairing_self_re, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

/-- Every actual common subsequence transports through every Wiener unit without another extraction. -/
theorem wienerUnitSourceGram_tendsto {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (u : (WienerAlgebraAt (1 / 2))ˣ) (j k : ℕ+) :
    Tendsto (fun m => wienerUnitSourceGram ε u (L.subsequence m) j k) atTop
      (𝓝 (unitGram L (normalizedUnit L u) j k)) := by
  have hnum := wienerSourcePairing_tendsto L
    ((u : WienerAlgebraAt (1 / 2)) * pointMass j)
    ((u : WienerAlgebraAt (1 / 2)) * pointMass k)
  simp only [wienerRepresentation_unit_mul_pointMass_vector] at hnum
  have hden := wienerSourcePairing_tendsto L (u : WienerAlgebraAt (1 / 2)) u
  change Tendsto (fun m => wienerSourcePairing ε (L.subsequence m) u u) atTop
    (𝓝 ⟪unitVector L u 1, unitVector L u 1⟫_ℂ) at hden
  have hnorm : ⟪unitVector L u 1, unitVector L u 1⟫_ℂ =
      ((‖unitVector L u 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hnorm] at hden
  have hne : ((‖unitVector L u 1‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (unitVector_one_ne_zero L u))
  rw [unitGram_normalizedUnit]
  exact (hnum.div hden hne).congr (fun m => rfl)

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.wienerUnitSourceGram_tendsto
end
end


section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open scoped ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A real Wiener kernel acts on the complex source by complexifying its real floor dilation. -/
theorem complexWienerRow_toWiener (ε : SubcriticalDamping) (g : ℕ → ℝ)
    (hg : TransHorizonIncidenceMechanics.CriticalWiener g) (n : ℕ) :
    complexWienerRow ε (toWiener g hg) n =
      (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε) n : ℂ) := by
  unfold complexWienerRow prefixDilation
  push_cast
  apply sum_congr rfl
  intro j hj
  change realFn g j * _ = _
  rw [realFn_apply (by have := (mem_Icc.mp hj).1; omega)]

/-- The finite complete pairing of two real dilates is their ordinary signed pronic pairing. -/
theorem wienerSourcePairing_toWiener_pointMass (ε : SubcriticalDamping) (g : ℕ → ℝ)
    (hg : TransHorizonIncidenceMechanics.CriticalWiener g) (T : ℕ) (j k : ℕ+) :
    wienerSourcePairing ε T (toWiener g hg * pointMass j) (toWiener g hg * pointMass k) =
      ((pronicPairing (T + 1)
        (rowDilate j (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)))
        (rowDilate k (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε))) /
          dampedMobiusEnergy ε (T + 1) : ℝ) : ℂ) := by
  unfold wienerSourcePairing pronicPairing rowDilate
  simp only [complexWienerRow_mul_pointMass, complexWienerRow_toWiener,
    Complex.conj_ofReal]
  push_cast
  congr 1
  exact sum_congr rfl fun n _ => by ring

/-- The source correction in exact real Wiener convolution. -/
def wienerMeanCorrection (ε : SubcriticalDamping) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  TransHorizonIncidenceMechanics.dampedDensity ε *
    TransHorizonIncidenceMechanics.weightCenteredPrefix g (∑' d : ℕ, g d / d) n

/-- The actual centered receiver after a real Wiener convolution. -/
def wienerConvolvedReceiver (ε : SubcriticalDamping) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  TransHorizonIncidenceMechanics.weightCenteredPrefix
    (dirichletConv g (pmPowerDampedRealWeight ε))
    ((∑' d : ℕ, g d / d) * TransHorizonIncidenceMechanics.dampedDensity ε) n

/-- Exact convolution separates the complete source action from its mean correction. -/
theorem wienerConvolvedReceiver_eq (ε : SubcriticalDamping) (g : ℕ → ℝ) :
    wienerConvolvedReceiver ε g = fun n =>
      prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε) n + wienerMeanCorrection ε g n := by
  funext n
  unfold wienerConvolvedReceiver wienerMeanCorrection
  rw [TransHorizonIncidenceMechanics.weightCenteredPrefix_dirichletConv]
  congr 1
  apply sum_congr rfl
  intro j _
  congr 1
  rw [TransHorizonIncidenceMechanics.weightCenteredPrefix,
    pmPowerDampedCenteredDivisorPrefix_eq]
  rfl

theorem wienerMeanCorrection_zero (ε : SubcriticalDamping) (g : ℕ → ℝ) :
    wienerMeanCorrection ε g 0 = 0 := by
  rw [wienerMeanCorrection, TransHorizonIncidenceMechanics.weightCenteredPrefix_zero, mul_zero]

theorem prefixDilation_receiver_zero (ε : SubcriticalDamping) (g : ℕ → ℝ) :
    prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε) 0 = 0 := by
  simp [prefixDilation]

/-- The correction is globally paid, uniformly over all positive cofactor indices. -/
theorem exists_uniform_wienerMeanCorrection_bound (ε : SubcriticalDamping) (g : ℕ → ℝ)
    (hg : TransHorizonIncidenceMechanics.CriticalWiener g) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ+, ∀ T : ℕ,
      pronicNorm T (rowDilate j (wienerMeanCorrection ε g)) ≤ D := by
  let D := |TransHorizonIncidenceMechanics.dampedDensity ε| *
    ((Real.sqrt 2 + 1) * ∑' n : ℕ, |g n| * (n : ℝ) ^ (-(1 / 2 : ℝ)))
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity)
      (tsum_nonneg fun n => by positivity))
  have hbase (T : ℕ) : pronicNorm T (wienerMeanCorrection ε g) ≤ D := by
    change TransHorizonIncidenceMechanics.pronicNorm
      (fun n => TransHorizonIncidenceMechanics.dampedDensity ε *
        TransHorizonIncidenceMechanics.weightCenteredPrefix g (∑' d : ℕ, g d / d) n) T ≤ D
    rw [TransHorizonIncidenceMechanics.pronicNorm_smul]
    exact mul_le_mul_of_nonneg_left
      (TransHorizonIncidenceMechanics.pronicNorm_weightCenteredPrefix_le_critical hg T)
      (abs_nonneg _)
  refine ⟨D, hD, fun j T => ?_⟩
  exact (pronicNorm_rowDilate_le_sharp j.property T _ (wienerMeanCorrection_zero ε g)).trans
    ((mul_le_mul_of_nonneg_left (hbase T) (by positivity)).trans
      (mul_le_of_le_one_left hD (inv_sqrt_pnat_le_one j)))

/-- The complete real Wiener action and all its positive cofactors obey one receiver norm budget. -/
theorem exists_uniform_wienerDilation_bound (ε : SubcriticalDamping) (g : ℕ → ℝ)
    (hg : TransHorizonIncidenceMechanics.CriticalWiener g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ+, ∀ T : ℕ,
      pronicNorm T (rowDilate j (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε))) ≤
        C * Real.sqrt (dampedMobiusEnergy ε T) := by
  let C := ∑' n : ℕ, |g n| * (n : ℝ) ^ (-(1 / 2 : ℝ))
  have hC : 0 ≤ C := tsum_nonneg fun n => by positivity
  have hbase (T : ℕ) : pronicNorm T (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)) ≤
      C * Real.sqrt (dampedMobiusEnergy ε T) := by
    have h := pronicNorm_prefixDilation_le hg (pmPowerDampedCenteredDivisorPrefix ε)
      (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero ε) T
    change pronicNorm T (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)) ≤
      C * pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) at h
    rwa [pronicNorm_centeredPrefix] at h
  refine ⟨C, hC, fun j T => ?_⟩
  exact (pronicNorm_rowDilate_le_sharp j.property T _ (prefixDilation_receiver_zero ε g)).trans
    ((mul_le_mul_of_nonneg_left (hbase T) (by positivity)).trans
      (mul_le_of_le_one_left (mul_nonneg hC (Real.sqrt_nonneg _))
        (inv_sqrt_pnat_le_one j)))

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.wienerConvolvedReceiver_eq
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.exists_uniform_wienerMeanCorrection_bound
end
end


section
noncomputable section
set_option autoImplicit false
open Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- On actual escape, exact Wiener convolution and its full dilation have the same normalized Gram table. -/
theorem admits_or_wienerConvolution_gram_error_vanishes (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (g : ℕ → ℝ), TransHorizonIncidenceMechanics.CriticalWiener g →
        ∀ j k : ℕ+,
          Tendsto (fun T =>
            (pronicPairing (T + 1)
                (rowDilate j (wienerConvolvedReceiver ε g))
                (rowDilate k (wienerConvolvedReceiver ε g)) -
              pronicPairing (T + 1)
                (rowDilate j (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)))
                (rowDilate k (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)))) /
              dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | hE
  · exact Or.inl h
  · refine Or.inr fun g hg j k => ?_
    obtain ⟨C, hC, hmain⟩ := exists_uniform_wienerDilation_bound ε g hg
    obtain ⟨D, hD, hpaid⟩ := exists_uniform_wienerMeanCorrection_bound ε g hg
    have h := normalized_pronicPairing_perturbation_tendsto_zero_of_nonneg
      (dampedMobiusEnergy ε) (dampedMobiusEnergy_nonneg ε) hE
      (rowDilate j (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)))
      (rowDilate k (prefixDilation g (pmPowerDampedCenteredDivisorPrefix ε)))
      (rowDilate j (wienerMeanCorrection ε g)) (rowDilate k (wienerMeanCorrection ε g))
      hC hD (hmain j) (hmain k) (hpaid j) (hpaid k)
    apply (h.comp (tendsto_add_atTop_nat 1)).congr
    intro T
    simp only [wienerConvolvedReceiver_eq]
    rfl

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_wienerConvolution_gram_error_vanishes
end
end


section
noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open scoped InnerProductSpace
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.ArithmeticCompensationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The cofactor Gram table of a real zero-origin row at its own pronic energy scale. -/
def normalizedSourceGram (f : ℕ → ℝ) (T : ℕ) (j k : ℕ+) : ℝ :=
  pronicPairing (T + 1) (rowDilate j f) (rowDilate k f) / pronicNorm (T + 1) f ^ 2

theorem pronicPairing_one_one (f : ℕ → ℝ) (T : ℕ) :
    pronicPairing T (rowDilate 1 f) (rowDilate 1 f) = pronicNorm T f ^ 2 := by
  change pronicPairing T (fun n => f (n / 1)) (fun n => f (n / 1)) = _
  rw [pronicNorm_sq]
  simp only [pronicPairing, Nat.div_one, pow_two]

namespace ActualCofactorLimit

/-- Every real Wiener convolution retains all complete limiting pairings after its paid correction. -/
theorem admits_or_real_convolution_pairings_tendsto {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (g : ℕ → ℝ) (hg : TransHorizonIncidenceMechanics.CriticalWiener g) (j k : ℕ+),
        Tendsto (fun m => ((pronicPairing (L.subsequence m + 1)
          (rowDilate j (wienerConvolvedReceiver ε g))
          (rowDilate k (wienerConvolvedReceiver ε g)) /
            dampedMobiusEnergy ε (L.subsequence m + 1) : ℝ) : ℂ)) atTop
          (𝓝 ⟪wienerRepresentation L (toWiener g hg * pointMass k) (vector L 1),
            wienerRepresentation L (toWiener g hg * pointMass j) (vector L 1)⟫_ℂ) := by
  rcases admits_or_wienerConvolution_gram_error_vanishes ε with hpaid | herror
  · exact Or.inl hpaid
  · refine Or.inr fun g hg j k => ?_
    have hbase := wienerSourcePairing_tendsto L
      (toWiener g hg * pointMass j) (toWiener g hg * pointMass k)
    simp only [wienerSourcePairing_toWiener_pointMass] at hbase
    have herr := Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((herror g hg j k).comp L.strictMono.tendsto_atTop)
    change Tendsto (fun m => (((_ - _) /
      dampedMobiusEnergy ε (L.subsequence m + 1) : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) at herr
    have hsum := hbase.add herr
    rw [add_zero] at hsum
    convert hsum using 1
    funext m
    push_cast
    ring

/-- A real Wiener unit preserves a positive proportion of the actual escaping receiver energy. -/
theorem admits_or_real_unit_convolution_energy_ratio_tendsto {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (g : ℕ → ℝ) (hg : TransHorizonIncidenceMechanics.CriticalWiener g)
        (u : (WienerAlgebraAt (1 / 2))ˣ),
        (u : WienerAlgebraAt (1 / 2)) = toWiener g hg →
        0 < ‖unitVector L u 1‖ ^ 2 ∧
          Tendsto (fun m => pronicNorm (L.subsequence m + 1) (wienerConvolvedReceiver ε g) ^ 2 /
            dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (‖unitVector L u 1‖ ^ 2)) := by
  rcases admits_or_real_convolution_pairings_tendsto L with hpaid | hpairs
  · exact Or.inl hpaid
  · refine Or.inr fun g hg u hu => ⟨sq_pos_of_ne_zero
      (norm_ne_zero_iff.mpr (unitVector_one_ne_zero L u)), ?_⟩
    have h := hpairs g hg 1 1
    rw [← hu] at h
    simp only [wienerRepresentation_unit_mul_pointMass_vector] at h
    change Tendsto (fun m => ((pronicPairing (L.subsequence m + 1)
      (rowDilate 1 (wienerConvolvedReceiver ε g))
      (rowDilate 1 (wienerConvolvedReceiver ε g)) /
        dampedMobiusEnergy ε (L.subsequence m + 1) : ℝ) : ℂ)) atTop
      (𝓝 ⟪unitVector L u 1, unitVector L u 1⟫_ℂ) at h
    simp only [pronicPairing_one_one] at h
    have hre := Complex.continuous_re.continuousAt.tendsto.comp h
    change Tendsto (fun m => pronicNorm (L.subsequence m + 1)
      (wienerConvolvedReceiver ε g) ^ 2 / dampedMobiusEnergy ε (L.subsequence m + 1))
      atTop (𝓝 (inner ℂ (unitVector L u 1) (unitVector L u 1)).re) at hre
    rw [inner_self_eq_norm_sq_to_K] at hre
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      Complex.ofReal_re] using hre

/-- Real Wiener units preserve actual source escape, not only the normalized limiting table. -/
theorem admits_or_real_unit_convolution_escapes {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (g : ℕ → ℝ) (hg : TransHorizonIncidenceMechanics.CriticalWiener g)
        (u : (WienerAlgebraAt (1 / 2))ˣ),
        (u : WienerAlgebraAt (1 / 2)) = toWiener g hg →
          Tendsto (fun T => pronicNorm T (wienerConvolvedReceiver ε g) ^ 2) atTop atTop := by
  by_cases hpaid : Admits dampedMobiusEnergy ε
  · exact Or.inl hpaid
  · refine Or.inr fun g hg u hu => ?_
    have hE := (admits_or_tendsto_atTop (ε : ℝ)).resolve_left hpaid
    have hratio := ((admits_or_real_unit_convolution_energy_ratio_tendsto L).resolve_left
      hpaid) g hg u hu
    have hsmall := hratio.2.eventually (eventually_gt_nhds (half_lt_self hratio.1))
    have hE' : Tendsto (fun m => dampedMobiusEnergy ε (L.subsequence m + 1)) atTop atTop :=
      hE.comp ((tendsto_add_atTop_nat 1).comp L.strictMono.tendsto_atTop)
    have hseq : Tendsto (fun m => pronicNorm (L.subsequence m + 1)
        (wienerConvolvedReceiver ε g) ^ 2) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_
        (Filter.Tendsto.const_mul_atTop (half_pos hratio.1) hE')
      filter_upwards [hsmall] with m hm
      exact (le_div_iff₀ (receiverEnergy_succ_pos ε (L.subsequence m))).mp hm.le
    apply tendsto_atTop.mpr
    intro R
    obtain ⟨m, hm⟩ := (hseq.eventually_ge_atTop R).exists
    filter_upwards [eventually_ge_atTop (L.subsequence m + 1)] with T hT
    exact hm.trans (pronicNorm_sq_monotone (wienerConvolvedReceiver ε g) hT)

/-- Real unit convolution changes the actual source Gram only by the normalized choice of cyclic vector. -/
theorem admits_or_real_unit_convolution_gram_tendsto {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (g : ℕ → ℝ) (hg : TransHorizonIncidenceMechanics.CriticalWiener g)
        (u : (WienerAlgebraAt (1 / 2))ˣ),
        (u : WienerAlgebraAt (1 / 2)) = toWiener g hg → ∀ j k : ℕ+,
          Tendsto (fun m =>
            (normalizedSourceGram (wienerConvolvedReceiver ε g) (L.subsequence m) j k : ℂ))
            atTop (𝓝 (unitGram L (normalizedUnit L u) j k)) := by
  rcases admits_or_real_convolution_pairings_tendsto L with hpaid | hpairs
  · exact Or.inl hpaid
  · refine Or.inr fun g hg u hu => ?_
    have hpair (j k : ℕ+) :
        Tendsto (fun m => ((pronicPairing (L.subsequence m + 1)
          (rowDilate j (wienerConvolvedReceiver ε g))
          (rowDilate k (wienerConvolvedReceiver ε g)) /
            dampedMobiusEnergy ε (L.subsequence m + 1) : ℝ) : ℂ)) atTop
          (𝓝 (unitGram L u j k)) := by
      have h := hpairs g hg j k
      rw [← hu] at h
      simpa only [wienerRepresentation_unit_mul_pointMass_vector, unitGram] using h
    have hden := hpair 1 1
    have hnorm : unitGram L u 1 1 = ((‖unitVector L u 1‖ ^ 2 : ℝ) : ℂ) := by
      unfold unitGram
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    change Tendsto (fun m => ((pronicPairing (L.subsequence m + 1)
      (rowDilate 1 (wienerConvolvedReceiver ε g))
      (rowDilate 1 (wienerConvolvedReceiver ε g)) /
        dampedMobiusEnergy ε (L.subsequence m + 1) : ℝ) : ℂ)) atTop
      (𝓝 (unitGram L u 1 1)) at hden
    simp only [pronicPairing_one_one, hnorm] at hden
    have hne : ((‖unitVector L u 1‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (unitVector_one_ne_zero L u))
    intro j k
    have hquot := (hpair j k).div hden hne
    rw [← unitGram_normalizedUnit] at hquot
    apply hquot.congr
    intro m
    simp only [Pi.div_apply]
    unfold normalizedSourceGram
    have hE := (receiverEnergy_succ_pos ε (L.subsequence m)).ne'
    push_cast
    have hEC : (dampedMobiusEnergy ε (L.subsequence m + 1) : ℂ) ≠ 0 := by exact_mod_cast hE
    by_cases hN : (pronicNorm (L.subsequence m + 1) (wienerConvolvedReceiver ε g) : ℂ) = 0
    · simp only [hN, zero_pow two_ne_zero, zero_div, div_zero]
    · field_simp [hEC, hN]

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.admits_or_real_unit_convolution_gram_tendsto
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.admits_or_real_unit_convolution_energy_ratio_tendsto
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.admits_or_real_unit_convolution_escapes
end
end
