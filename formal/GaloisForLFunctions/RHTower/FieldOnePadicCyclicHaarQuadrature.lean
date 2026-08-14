import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicHaarQuadrature
import GaloisForLFunctions.RHTower.FieldOnePadicHaarScaling
import Mathlib.Topology.Instances.ZMod

/-!
# Exact cyclic Haar quadrature on `ℤ_p`

The normalized additive Haar measure on `ℤ_p` has mass one.  Reduction modulo
`p^n` therefore turns every integrable residue-class function into an exact
finite sum with factor `p^n`.  This is the local Haar half of the finite
Fourier Parseval argument required by Connes--Marcolli Lemma 2.33.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- The whole compact group `ℤ_p`, packaged as the normalization set for its
additive Haar probability measure. -/
def fieldOnePadicIntPositiveCompacts : PositiveCompacts ℤ_[p] := ⊤

/-- Additive Haar probability measure on `ℤ_p`. -/
def fieldOnePadicIntNormalizedHaar : Measure ℤ_[p] :=
  Measure.addHaarMeasure (fieldOnePadicIntPositiveCompacts p)

instance fieldOnePadicIntNormalizedHaar_isAddHaar :
    (fieldOnePadicIntNormalizedHaar p).IsAddHaarMeasure := by
  unfold fieldOnePadicIntNormalizedHaar
  infer_instance

@[simp]
theorem fieldOnePadicIntNormalizedHaar_univ :
    fieldOnePadicIntNormalizedHaar p Set.univ = 1 := by
  change Measure.addHaarMeasure (fieldOnePadicIntPositiveCompacts p)
      (fieldOnePadicIntPositiveCompacts p) = 1
  exact Measure.addHaarMeasure_self

/-- Canonical least-nonnegative residue representative in `ℤ_p`. -/
def fieldOnePadicIntResidueRep (n : ℕ) : ZMod (p ^ n) → ℤ_[p] :=
  fun r => (r.val : ℤ_[p])

theorem fieldOnePadicIntResidueRep_spec
    (n : ℕ) (r : ZMod (p ^ n)) :
    PadicInt.toZModPow n (fieldOnePadicIntResidueRep p n r) = r := by
  change PadicInt.toZModPow n (r.val : ℤ_[p]) = r
  rw [map_natCast]
  exact ZMod.natCast_zmod_val r

/-- Exact cyclic quadrature for an integrable function on `ℤ_p` which is
constant modulo `p^n`. -/
theorem fieldOnePadicInt_cyclicSampleSum_eq_nsmul_integral
    (n : ℕ) (f : ℤ_[p] → ℂ)
    (hf : Integrable f (fieldOnePadicIntNormalizedHaar p))
    (hclass : ∀ {x y : ℤ_[p]},
      PadicInt.toZModPow n x = PadicInt.toZModPow n y → f x = f y) :
    ∑ r : ZMod (p ^ n), f (fieldOnePadicIntResidueRep p n r) =
      (p ^ n) • (∫ x, f x ∂fieldOnePadicIntNormalizedHaar p) := by
  letI : NeZero (p ^ n) :=
    ⟨pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero⟩
  exact fieldOneFiniteCyclicQuotient_sampleSum_eq_nsmul_integral
    (fieldOnePadicIntNormalizedHaar p)
    (fieldOnePadicIntNormalizedHaar_univ p)
    (p ^ n) (PadicInt.toZModPow n).toAddMonoidHom
    (ZMod.ringHom_surjective (PadicInt.toZModPow n))
    (fieldOnePadicIntResidueRep p n)
    (fieldOnePadicIntResidueRep_spec p n) f hf hclass

/-- Translation invariance under `p^n ℤ_p` is exactly the fiber-constancy
condition for reduction modulo `p^n`. -/
theorem fieldOnePadicInt_classInvariant_of_primePowerInvariant
    (n : ℕ) (f : ℤ_[p] → ℂ)
    (hperiod : ∀ x z : ℤ_[p],
      f (x + (p : ℤ_[p]) ^ n * z) = f x) :
    ∀ {x y : ℤ_[p]},
      PadicInt.toZModPow n x = PadicInt.toZModPow n y → f x = f y := by
  intro x y hxy
  have hker : x - y ∈ RingHom.ker (PadicInt.toZModPow n) := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact hxy
  rw [PadicInt.ker_toZModPow] at hker
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hker
  calc
    f x = f (y + (p : ℤ_[p]) ^ n * z) := by
      congr 1
      rw [← hz]
      abel
    _ = f y := hperiod y z

/-- Prime-power-periodic form of exact cyclic Haar quadrature. -/
theorem fieldOnePadicInt_cyclicSampleSum_eq_nsmul_integral_of_primePowerInvariant
    (n : ℕ) (f : ℤ_[p] → ℂ)
    (hf : Integrable f (fieldOnePadicIntNormalizedHaar p))
    (hperiod : ∀ x z : ℤ_[p],
      f (x + (p : ℤ_[p]) ^ n * z) = f x) :
    ∑ r : ZMod (p ^ n), f (fieldOnePadicIntResidueRep p n r) =
      (p ^ n) • (∫ x, f x ∂fieldOnePadicIntNormalizedHaar p) :=
  fieldOnePadicInt_cyclicSampleSum_eq_nsmul_integral p n f hf
    (fieldOnePadicInt_classInvariant_of_primePowerInvariant p n f hperiod)

/-- Probability-normalized cyclic Fourier transform of a function on
`ℤ_p / p^nℤ_p`. -/
def fieldOnePadicIntCyclicFourier
    (n : ℕ) (f : ℤ_[p] → ℂ) : ZMod (p ^ n) → ℂ :=
  fun k => ((p ^ n : ℕ) : ℂ)⁻¹ *
    ZMod.dft (fun r => f (fieldOnePadicIntResidueRep p n r)) k

/-- Exact finite-level Plancherel theorem on `ℤ_p`.  This is proved by
combining literal residue-class Haar quadrature with cyclic Parseval. -/
theorem fieldOnePadicIntCyclicFourier_plancherel
    (n : ℕ) (f : ℤ_[p] → ℂ)
    (hf2 : Integrable (fun x => (Complex.normSq (f x) : ℂ))
      (fieldOnePadicIntNormalizedHaar p))
    (hperiod : ∀ x z : ℤ_[p],
      f (x + (p : ℤ_[p]) ^ n * z) = f x) :
    ∑ k : ZMod (p ^ n),
        Complex.normSq (fieldOnePadicIntCyclicFourier p n f k) =
      ∫ x, Complex.normSq (f x) ∂fieldOnePadicIntNormalizedHaar p := by
  letI : NeZero (p ^ n) :=
    ⟨pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero⟩
  have hperiod2 : ∀ x z : ℤ_[p],
      (Complex.normSq (f (x + (p : ℤ_[p]) ^ n * z)) : ℂ) =
        (Complex.normSq (f x) : ℂ) := by
    intro x z
    rw [hperiod]
  have hquad :=
    fieldOnePadicInt_cyclicSampleSum_eq_nsmul_integral_of_primePowerInvariant
      p n (fun x => (Complex.normSq (f x) : ℂ)) hf2 hperiod2
  rw [integral_complex_ofReal] at hquad
  have hquadR :
      ∑ r : ZMod (p ^ n),
          Complex.normSq (f (fieldOnePadicIntResidueRep p n r)) =
        (p ^ n : ℝ) *
          ∫ x, Complex.normSq (f x) ∂fieldOnePadicIntNormalizedHaar p := by
    apply Complex.ofReal_injective
    push_cast
    simpa [nsmul_eq_mul] using hquad
  change ∑ k : ZMod (p ^ n),
      Complex.normSq (((p ^ n : ℕ) : ℂ)⁻¹ *
        ZMod.dft (fun r => f (fieldOnePadicIntResidueRep p n r)) k) = _
  rw [fieldOneFiniteCyclicFourier_normalized_parseval]
  rw [hquadR]
  have hM : (p ^ n : ℝ) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero
  rw [Nat.cast_pow, ← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- Reduction modulo `p^n` is locally constant, hence continuous, on
`ℤ_p`. -/
theorem fieldOnePadicInt_toZModPow_continuous (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := p) n) := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.ball_mem_nhds x
    (show 0 < (p : ℝ) ^ (-(n : ℤ)) by
      exact zpow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _)] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  apply sub_eq_zero.mp
  rw [← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    ← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact hy.le

/-- Literal Haar-integral Fourier coefficient of a residue-class function
on `ℤ_p`. -/
def fieldOnePadicIntCyclicFourierIntegral
    (n : ℕ) (f : ℤ_[p] → ℂ) (k : ZMod (p ^ n)) : ℂ :=
  ∫ x, ZMod.stdAddChar (-(PadicInt.toZModPow n x * k)) * f x
    ∂fieldOnePadicIntNormalizedHaar p

/-- Exact identification of the literal Haar-integral coefficient with the
probability-normalized discrete Fourier transform. -/
theorem fieldOnePadicIntCyclicFourierIntegral_eq
    (n : ℕ) (f : ℤ_[p] → ℂ)
    (hf : Integrable f (fieldOnePadicIntNormalizedHaar p))
    (hperiod : ∀ x z : ℤ_[p],
      f (x + (p : ℤ_[p]) ^ n * z) = f x)
    (k : ZMod (p ^ n)) :
    fieldOnePadicIntCyclicFourierIntegral p n f k =
      fieldOnePadicIntCyclicFourier p n f k := by
  letI : NeZero (p ^ n) :=
    ⟨pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero⟩
  let g : ℤ_[p] → ℂ := fun x =>
    ZMod.stdAddChar (-(PadicInt.toZModPow n x * k)) * f x
  have hchar : Continuous (fun x : ℤ_[p] =>
      ZMod.stdAddChar (-(PadicInt.toZModPow n x * k))) := by
    exact (continuous_of_discreteTopology : Continuous
      (fun r : ZMod (p ^ n) => ZMod.stdAddChar (-(r * k)))).comp
        (fieldOnePadicInt_toZModPow_continuous p n)
  have hg : Integrable g (fieldOnePadicIntNormalizedHaar p) := by
    exact hf.bdd_mul (c := 1) hchar.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  have hfclass : ∀ {x y : ℤ_[p]},
      PadicInt.toZModPow n x = PadicInt.toZModPow n y → f x = f y :=
    fieldOnePadicInt_classInvariant_of_primePowerInvariant p n f hperiod
  have hgclass : ∀ {x y : ℤ_[p]},
      PadicInt.toZModPow n x = PadicInt.toZModPow n y → g x = g y := by
    intro x y hxy
    simp only [g]
    rw [hxy, hfclass hxy]
  have hquad := fieldOnePadicInt_cyclicSampleSum_eq_nsmul_integral
    p n g hg hgclass
  have hsum :
      ∑ r : ZMod (p ^ n), g (fieldOnePadicIntResidueRep p n r) =
        ZMod.dft (fun r => f (fieldOnePadicIntResidueRep p n r)) k := by
    rw [ZMod.dft_apply]
    apply Finset.sum_congr rfl
    intro r _
    simp only [g, fieldOnePadicIntResidueRep_spec]
    rfl
  rw [hsum] at hquad
  change (∫ x, g x ∂fieldOnePadicIntNormalizedHaar p) =
    ((p ^ n : ℕ) : ℂ)⁻¹ *
      ZMod.dft (fun r => f (fieldOnePadicIntResidueRep p n r)) k
  rw [hquad]
  have hM : ((p : ℂ) ^ n) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (Fact.out : Nat.Prime p).ne_zero
  simp only [nsmul_eq_mul, Nat.cast_pow]
  rw [← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- Exact Haar-integral Plancherel identity on every finite quotient
`ℤ_p / p^nℤ_p`. -/
theorem fieldOnePadicIntCyclicFourierIntegral_plancherel
    (n : ℕ) (f : ℤ_[p] → ℂ)
    (hf : Integrable f (fieldOnePadicIntNormalizedHaar p))
    (hf2 : Integrable (fun x => (Complex.normSq (f x) : ℂ))
      (fieldOnePadicIntNormalizedHaar p))
    (hperiod : ∀ x z : ℤ_[p],
      f (x + (p : ℤ_[p]) ^ n * z) = f x) :
    ∑ k : ZMod (p ^ n),
        Complex.normSq (fieldOnePadicIntCyclicFourierIntegral p n f k) =
      ∫ x, Complex.normSq (f x) ∂fieldOnePadicIntNormalizedHaar p := by
  simp_rw [fieldOnePadicIntCyclicFourierIntegral_eq p n f hf hperiod]
  exact fieldOnePadicIntCyclicFourier_plancherel p n f hf2 hperiod

end

end GaloisForLFunctions.RHTower
