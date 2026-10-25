import GaloisForLFunctions.ArithmeticOrientationTheory.WienerCoefficientEvaluation
import GaloisForLFunctions.ArithmeticDefectRigidity.TheClosedCofactorAnnihilatorHasNoCountableIndex
import GaloisForLFunctions.ArithmeticDefectRigidity.CompleteWienerPairingsFollowTheCommonCofactorLimit

/-!
# Admitted cofactor modules are faithful

On admission, a null Wiener orbit vector forces its unnormalized source
energy to vanish. Every finite cell then vanishes, and triangular coefficient
recovery at the nonzero first source cell proves faithfulness. The admitted
module has the full Bohr hull and continuum quotient index. Every finite-dimensional
actual cofactor module therefore lies on the escaping branch.
-/

noncomputable section
set_option autoImplicit false

open Finset Filter Topology RHTower
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The unnormalized complex energy of a complete Wiener source action. -/
def complexWienerEnergy (ε : SubcriticalDamping) (a : WienerAlgebraAt (1 / 2)) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 (T + 1), ‖complexWienerRow ε a n‖ ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

theorem complexWienerEnergy_nonneg (ε : SubcriticalDamping)
    (a : WienerAlgebraAt (1 / 2)) (T : ℕ) : 0 ≤ complexWienerEnergy ε a T :=
  sum_nonneg fun _ _ => by positivity

/-- Self-pairing records exactly the positive source energy. -/
theorem wienerSourcePairing_self (ε : SubcriticalDamping) (T : ℕ)
    (a : WienerAlgebraAt (1 / 2)) :
    wienerSourcePairing ε T a a =
      ((complexWienerEnergy ε a T / dampedMobiusEnergy ε (T + 1) : ℝ) : ℂ) := by
  unfold wienerSourcePairing complexWienerEnergy
  push_cast
  simp only [Complex.conj_mul']

theorem wienerSourcePairing_self_re (ε : SubcriticalDamping) (T : ℕ)
    (a : WienerAlgebraAt (1 / 2)) :
    (wienerSourcePairing ε T a a).re =
      complexWienerEnergy ε a T / dampedMobiusEnergy ε (T + 1) := by
  rw [wienerSourcePairing_self, Complex.ofReal_re]

/-- Vanishing energy along cofinal horizons forces every source cell to vanish. -/
theorem complexWienerRow_eq_zero_of_energy_tendsto_zero (ε : SubcriticalDamping)
    (a : WienerAlgebraAt (1 / 2)) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (hE : Tendsto (fun m => complexWienerEnergy ε a (ns m)) atTop (𝓝 0)) :
    ∀ n : ℕ, complexWienerRow ε a n = 0 := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [complexWienerRow, Icc_eq_empty (by omega : ¬ (1 : ℕ) ≤ 0), sum_empty]
  · have hcell : ‖complexWienerRow ε a n‖ ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤ 0 := by
      apply ge_of_tendsto hE
      filter_upwards [hns.eventually_ge_atTop n] with m hm
      unfold complexWienerEnergy
      exact single_le_sum (fun j _ =>
        div_nonneg (sq_nonneg ‖complexWienerRow ε a j‖)
          (by positivity : 0 ≤ (j : ℝ) * ((j : ℝ) + 1)))
        (mem_Icc.mpr ⟨hn, hm.trans (Nat.le_succ _)⟩)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq := (div_le_iff₀ (by positivity : 0 < (n : ℝ) * ((n : ℝ) + 1))).mp hcell
    apply norm_eq_zero.mp
    nlinarith only [hsq, norm_nonneg (complexWienerRow ε a n)]

/-- The first nonzero Wiener coefficient is visible at its own source cell. -/
theorem eq_zero_of_complexWienerRow_eq_zero (ε : SubcriticalDamping)
    (a : WienerAlgebraAt (1 / 2)) (ha : ∀ n, complexWienerRow ε a n = 0) : a = 0 := by
  have hfirst : pmPowerDampedCenteredDivisorPrefix ε 1 ≠ 0 := by
    intro hz
    have h := receiverEnergy_succ_pos ε 0
    simp [dampedMobiusEnergy, pmPowerDampedDivisorDiscreteEnergy, hz] at h
  have hfirstC : (pmPowerDampedCenteredDivisorPrefix ε 1 : ℂ) ≠ 0 := by
    exact_mod_cast hfirst
  have hcoeff : ∀ n : ℕ, a.toFn n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hrow : complexWienerRow ε a n =
            a.toFn n * (pmPowerDampedCenteredDivisorPrefix ε 1 : ℂ) := by
          unfold complexWienerRow
          rw [sum_eq_single n]
          · rw [Nat.div_self hn]
          · intro j hj hjn
            rw [ih j (by have := (mem_Icc.mp hj).2; omega), zero_mul]
          · intro hnot
            exact (hnot (mem_Icc.mpr ⟨hn, le_rfl⟩)).elim
        exact (mul_eq_zero.mp (hrow.symm.trans (ha n))).resolve_right hfirstC
  apply toFn_injective
  ext n
  simpa only [toFn_zero, ArithmeticFunction.zero_apply] using hcoeff n

namespace ActualCofactorLimit

/-- On the admitted branch, a null limiting Wiener vector has zero source energy. -/
theorem complexWienerEnergy_tendsto_zero_of_admits_of_null {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hpaid : Admits dampedMobiusEnergy ε)
    (a : WienerAlgebraAt (1 / 2)) (ha : wienerRepresentation L a (vector L 1) = 0) :
    Tendsto (fun m => complexWienerEnergy ε a (L.subsequence m)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hpaid
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp
    (wienerSourcePairing_tendsto L a a)
  simp only [ha, inner_zero_left, Complex.zero_re] at hlim
  change Tendsto (fun m => (wienerSourcePairing ε (L.subsequence m) a a).re)
    atTop (𝓝 0) at hlim
  simp only [wienerSourcePairing_self_re] at hlim
  have hmajor := hlim.const_mul C
  rw [mul_zero] at hmajor
  apply squeeze_zero (fun m => complexWienerEnergy_nonneg ε a (L.subsequence m)) _ hmajor
  intro m
  have hE := receiverEnergy_succ_pos ε (L.subsequence m)
  calc
    _ = (complexWienerEnergy ε a (L.subsequence m) /
        dampedMobiusEnergy ε (L.subsequence m + 1)) *
          dampedMobiusEnergy ε (L.subsequence m + 1) := by field_simp [hE.ne']
    _ ≤ (complexWienerEnergy ε a (L.subsequence m) /
        dampedMobiusEnergy ε (L.subsequence m + 1)) * C :=
      mul_le_mul_of_nonneg_left (hC _) (div_nonneg
        (complexWienerEnergy_nonneg ε a (L.subsequence m)) hE.le)
    _ = _ := mul_comm _ _

/-- Admission makes the complete actual Wiener action faithful. -/
theorem annihilator_eq_bot_of_admits {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hpaid : Admits dampedMobiusEnergy ε) :
    annihilator L = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  change a = 0
  apply eq_zero_of_complexWienerRow_eq_zero ε a
  exact complexWienerRow_eq_zero_of_energy_tendsto_zero ε a L.subsequence
    L.strictMono.tendsto_atTop (complexWienerEnergy_tendsto_zero_of_admits_of_null L hpaid a
      ((mem_annihilator_iff L a).mp ha))

/-- Every admitted actual cofactor limit has the full Bohr hull. -/
theorem moduleHull_eq_univ_of_admits {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hpaid : Admits dampedMobiusEnergy ε) :
    moduleHull L = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω a ha
  rw [annihilator_eq_bot_of_admits L hpaid] at ha
  have ha0 : a = 0 := ha
  subst a
  rw [← bohrCharacter_apply, map_zero]

/-- A nonfaithful actual module can occur only on an escaping receiver branch. -/
theorem faithful_or_receiver_escapes {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    annihilator L = ⊥ ∨ Tendsto (dampedMobiusEnergy ε) atTop atTop := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with h | h
  · exact Or.inl (annihilator_eq_bot_of_admits L h)
  · exact Or.inr h

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity


section
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

open ArithmeticOrientationTheory ArithmeticContinuationAndCriticalEnergy ArithmeticCompensationTheory

/-- An admitted actual module has infinitely many independent Wiener orbit vectors. -/
theorem hilbert_not_finiteDimensional_of_admits {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hpaid : Admits dampedMobiusEnergy ε) :
    ¬ FiniteDimensional ℂ (Hilbert L) := by
  intro hH
  letI := hH
  have hker : (cyclicLinear L).ker = ⊥ := by
    rw [cyclicLinear_ker, annihilator_eq_bot_of_admits L hpaid]
    rfl
  have hinj := LinearMap.ker_eq_bot.mp hker
  exact WienerAlgebraAt.not_finiteDimensional (1 / 2)
    (FiniteDimensional.of_injective (cyclicLinear L).toLinearMap hinj)

/-- Admission realizes the continuum branch of the algebraic index dichotomy. -/
theorem annihilator_quotient_rank_eq_continuum_of_admits {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hpaid : Admits dampedMobiusEnergy ε) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L) = Cardinal.continuum :=
  annihilator_quotient_rank_eq_continuum_of_infinite L
    (hilbert_not_finiteDimensional_of_admits L hpaid)

/-- Every finite-dimensional actual cofactor module necessarily lies on the escaping branch. -/
theorem receiver_escapes_of_finiteDimensional {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)] :
    Filter.Tendsto (dampedMobiusEnergy ε) Filter.atTop Filter.atTop := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with hpaid | hescape
  · exact (hilbert_not_finiteDimensional_of_admits L hpaid inferInstance).elim
  · exact hescape

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.annihilator_quotient_rank_eq_continuum_of_admits
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.receiver_escapes_of_finiteDimensional
end
end
