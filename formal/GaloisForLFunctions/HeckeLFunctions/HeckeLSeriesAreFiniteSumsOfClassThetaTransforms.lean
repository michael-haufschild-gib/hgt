import GaloisForLFunctions.HeckeLFunctions.HeckeUnitAveragedMellinIsTheIdealClassSeries
import GaloisForLFunctions.HeckeLFunctions.UnramifiedHeckeCharactersDescendToIdealClasses
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Hecke L-series as a finite sum of actual class theta transforms

Choose an integral ideal prime to the modulus in each inverse ordinary ideal class.
Absolute ideal-series convergence permits partitioning by class. The exact unit-theta
Mellin formula then identifies the normalized finite theta sum with the Gamma-completed
Hecke L-series. Its inverse Gamma product gives an entire continuation whenever the
finite residue weight or real parity is nontrivial.
-/

noncomputable section
open NumberField MeasureTheory
open scoped Classical nonZeroDivisors
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Each ordinary class admits an inverse-class integral representative prime to the modulus. -/
theorem exists_heckeClassBaseIdeal (c : ClassGroup (𝓞 K)) :
    ∃ b : (Ideal (𝓞 K))⁰, (b : Ideal (𝓞 K)) ⊔ 𝔪.fin = ⊤ ∧ ClassGroup.mk0 b = c⁻¹ := by
  obtain ⟨b, hb0, hb, hc⟩ := exists_integral_rep 𝔪 c⁻¹
  refine ⟨⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩, hb, ?_⟩
  rw [← ClassGroup.mk_mk0 K]
  exact hc

/-- A chosen actual nonzero integral representative of the inverse class, prime to the modulus. -/
def heckeClassBaseIdeal (c : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  (exists_heckeClassBaseIdeal 𝔪 c).choose

theorem heckeClassBaseIdeal_coprime (c : ClassGroup (𝓞 K)) :
    (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) ⊔ 𝔪.fin = ⊤ :=
  (exists_heckeClassBaseIdeal 𝔪 c).choose_spec.1

theorem heckeClassBaseIdeal_class (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk0 (heckeClassBaseIdeal 𝔪 c) = c⁻¹ :=
  (exists_heckeClassBaseIdeal 𝔪 c).choose_spec.2

theorem heckeClassBaseIdeal_heckeValue_ne_zero (ψ : HeckeCharacter 𝔪) (c : ClassGroup (𝓞 K)) :
    heckeValue 𝔪 ψ (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) ≠ 0 := by
  rw [heckeValue_of_mem 𝔪 ψ (nonZeroDivisors.coe_ne_zero _)
    ((idealUnit_mem_idealGroup_iff 𝔪 _).mpr (heckeClassBaseIdeal_coprime 𝔪 c))]
  exact Units.ne_zero _

local instance : Fintype (ClassGroup (𝓞 K)) := Fintype.ofFinite _

/-- The absolutely convergent actual ideal series partitions into all ordinary class fibers. -/
theorem heckeL_eq_sum_inverseClassL (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeL 𝔪 ψ s = ∑ c : ClassGroup (𝓞 K), heckeInverseClassL 𝔪 ψ (heckeClassBaseIdeal 𝔪 c) s := by
  have h := (summable_norm_heckeIdealTerm 𝔪 ψ hs).of_norm.hasSum.tsum_fiberwise
    (ClassGroup.mk0 : (Ideal (𝓞 K))⁰ → ClassGroup (𝓞 K))
  rw [heckeL_eq_tsum_ideals 𝔪 ψ hs, ← h.tsum_eq, tsum_fintype]
  apply Finset.sum_congr rfl
  intro c _
  change (∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c}, heckeIdealTerm 𝔪 ψ s I.1) =
    ∑' I : inverseClassIntegralIdeals (heckeClassBaseIdeal 𝔪 c), heckeIdealTerm 𝔪 ψ s I.1
  let e : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c} ≃
      inverseClassIntegralIdeals (heckeClassBaseIdeal 𝔪 c) :=
    Equiv.subtypeEquivRight (fun I => by rw [heckeClassBaseIdeal_class, inv_inv])
  exact e.tsum_eq (fun I : inverseClassIntegralIdeals (heckeClassBaseIdeal 𝔪 c) =>
    heckeIdealTerm 𝔪 ψ s I.1)

/-- The entire inverse of the chosen base-ideal summand. -/
def heckeClassWeight (ψ : HeckeCharacter 𝔪) (c : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  (heckeValue 𝔪 ψ (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)))⁻¹ *
    (Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : ℂ) ^ s

theorem differentiable_heckeClassWeight (ψ : HeckeCharacter 𝔪) (c : ClassGroup (𝓞 K)) :
    Differentiable ℂ (heckeClassWeight 𝔪 ψ c) := by
  have hn : (Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
  exact (differentiable_id.const_cpow (Or.inl hn)).const_mul _

theorem heckeClassWeight_mul_idealTerm (ψ : HeckeCharacter 𝔪)
    (c : ClassGroup (𝓞 K)) (s : ℂ) :
    heckeClassWeight 𝔪 ψ c s * heckeIdealTerm 𝔪 ψ s (heckeClassBaseIdeal 𝔪 c) = 1 := by
  have hc := heckeClassBaseIdeal_heckeValue_ne_zero 𝔪 ψ c
  have hn : (Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
  change ((heckeValue 𝔪 ψ (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)))⁻¹ *
    (Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : ℂ) ^ s) *
    (heckeValue 𝔪 ψ (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) *
      (Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : ℂ) ^ (-s)) = 1
  rw [Complex.cpow_neg]
  have hp : (Ideal.absNorm (heckeClassBaseIdeal 𝔪 c : Ideal (𝓞 K)) : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn]
    exact Complex.exp_ne_zero _
  field_simp [hc, hp]

/-- The inverse torsion/Jacobian scalar in the actual Mellin unfolding. -/
def heckeMellinNormalization : ℂ :=
  ((Module.finrank ℚ K : ℂ) * 2 ^ Units.rank K) / (Units.torsionOrder K : ℂ)

/-- The normalized finite sum of actual unit-theta continuations. -/
def heckeCompletedThetaContinuation (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeMellinNormalization (K := K) * ∑ c : ClassGroup (𝓞 K),
    heckeClassWeight 𝔪 ψ c s *
      heckeUnitThetaMellinContinuation 𝔪 (heckeClassBaseIdeal_coprime 𝔪 c)
        (nonZeroDivisors.coe_ne_zero _) ψ (heckeThetaMellinArgument 𝔪 ψ s)

/-- The ordinary Hecke continuation obtained from the actual completed theta sum. -/
def heckeThetaLContinuation (ψ : HeckeCharacter 𝔪) (s : ℂ) : ℂ :=
  heckeCompletedThetaContinuation 𝔪 ψ s * (heckeGammaFactor 𝔪 ψ s)⁻¹

/-- The normalized actual theta sum agrees with the Gamma-completed Hecke L-series. -/
theorem heckeCompletedThetaContinuation_eq (ψ : HeckeCharacter 𝔪)
    {s : ℂ} (hs : 1 < s.re) :
    heckeCompletedThetaContinuation 𝔪 ψ s = heckeGammaFactor 𝔪 ψ s * heckeL 𝔪 ψ s := by
  have hn : (Module.finrank ℚ K : ℂ) ≠ 0 := by
    have hp : 0 < (Module.finrank ℚ K : ℝ) := by
      rw [← numberFieldInfinitePlaceWeight_eq_finrank]
      exact numberFieldInfinitePlaceWeight_pos
    exact_mod_cast hp.ne'
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Units.torsionOrder_pos (K := K)).ne'
  rw [heckeCompletedThetaContinuation, heckeL_eq_sum_inverseClassL 𝔪 ψ hs,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [heckeUnitThetaMellinContinuation_eq_inverseClassL 𝔪 ψ _
    (heckeClassBaseIdeal_coprime 𝔪 c) hs]
  have hc := heckeClassWeight_mul_idealTerm 𝔪 ψ c s
  rw [heckeMellinNormalization]
  calc
    _ = (heckeClassWeight 𝔪 ψ c s * heckeIdealTerm 𝔪 ψ s (heckeClassBaseIdeal 𝔪 c)) *
        (heckeGammaFactor 𝔪 ψ s * heckeInverseClassL 𝔪 ψ (heckeClassBaseIdeal 𝔪 c) s) := by
      field_simp
    _ = _ := by rw [hc, one_mul]

/-- The actual normalized theta expression extends the original Hecke L-series on `Re s > 1`. -/
theorem heckeThetaLContinuation_eq (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    heckeThetaLContinuation 𝔪 ψ s = heckeL 𝔪 ψ s := by
  rw [heckeThetaLContinuation, heckeCompletedThetaContinuation_eq 𝔪 ψ hs,
    mul_right_comm, mul_inv_cancel₀ (heckeGammaFactor_ne_zero 𝔪 ψ (zero_lt_one.trans hs)), one_mul]

/-- The Hecke-variable change is entire. -/
theorem differentiable_heckeThetaMellinArgument (ψ : HeckeCharacter 𝔪) :
    Differentiable ℂ (heckeThetaMellinArgument 𝔪 ψ) :=
  ((differentiable_id.const_mul _).add_const _).div_const _

/-- Nonzero real parity makes the actual globally recombined completed theta entire. -/
theorem differentiable_heckeCompletedThetaContinuation_of_parity_ne_zero
    (ψ : HeckeCharacter 𝔪) (hp : parityDegree (heckeCoordinateParity 𝔪 ψ) ≠ 0) :
    Differentiable ℂ (heckeCompletedThetaContinuation 𝔪 ψ) := by
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro c _
  exact (differentiable_heckeClassWeight 𝔪 ψ c).mul
    ((differentiable_heckeUnitThetaMellinContinuation_of_parity_ne_zero 𝔪
      (heckeClassBaseIdeal_coprime 𝔪 c) (nonZeroDivisors.coe_ne_zero _) ψ hp).comp
        (differentiable_heckeThetaMellinArgument 𝔪 ψ))

/-- Nontrivial finite residue weight makes the actual globally recombined completed theta entire. -/
theorem differentiable_heckeCompletedThetaContinuation_of_finiteWeight_ne_one
    (ψ : HeckeCharacter 𝔪) (hf : finiteHeckeWeight 𝔪 ψ ≠ 1) :
    Differentiable ℂ (heckeCompletedThetaContinuation 𝔪 ψ) := by
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro c _
  exact (differentiable_heckeClassWeight 𝔪 ψ c).mul
    ((differentiable_heckeUnitThetaMellinContinuation_of_finiteWeight_ne_one 𝔪
      (heckeClassBaseIdeal_coprime 𝔪 c) (nonZeroDivisors.coe_ne_zero _) ψ hf).comp
        (differentiable_heckeThetaMellinArgument 𝔪 ψ))

/-- Every character with nontrivial finite or infinite component has an entire actual L-continuation. -/
theorem differentiable_heckeThetaLContinuation_of_ramified (ψ : HeckeCharacter 𝔪)
    (h : finiteHeckeWeight 𝔪 ψ ≠ 1 ∨ parityDegree (heckeCoordinateParity 𝔪 ψ) ≠ 0) :
    Differentiable ℂ (heckeThetaLContinuation 𝔪 ψ) := by
  have hc : Differentiable ℂ (heckeCompletedThetaContinuation 𝔪 ψ) := by
    rcases h with hf | hp
    · exact differentiable_heckeCompletedThetaContinuation_of_finiteWeight_ne_one 𝔪 ψ hf
    · exact differentiable_heckeCompletedThetaContinuation_of_parity_ne_zero 𝔪 ψ hp
  exact hc.mul (differentiable_heckeGammaFactor_inv 𝔪 ψ)

end GaloisForLFunctions.HeckeLFunctions
