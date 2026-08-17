import GaloisForLFunctions.HTGeometry.QuasiLocalInfiniteLBitEvolutionLaw
import GaloisForLFunctions.HTGeometry.LBitObserverTimeDimensionLaw
import GaloisForLFunctions.HTGeometry.LBitSupportTemporalScaleLaw
import GaloisForLFunctions.HTGeometry.QuantitativeMonomialWallCrossingLaw

/-!
# Thermodynamic diameter-scaled l-bit cascade

The corpus's single absolutely summable, rationally independent l-bit field is assigned the
geometric Rees scale `g ^ diameter(S)`.  On `0 ≤ g ≤ 1` this only decreases every coefficient, so
the infinite energy and its uniform finite-window approximation survive.  On every finite window,
the scaled spectrum is exactly the existing diameter-birth spectral jet, and rational independence
of the global field supplies every layerwise independence premise.

The endpoint pair `{0,b}` realizes birth order `b` for every natural number `b`.  Thus one
quasi-local thermodynamic interaction field contains a nonterminating temporal wall-crossing
cascade; it is not merely a countable abstract spectrum.
-/

open Set Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance thermodynamicDiameterFintypeForallBool
    {I : Type*} [Fintype I] : Fintype (I → Bool) :=
  lbitSupportScaleFintypeForallBool

/-- Scale each interaction by the power of `g` equal to its lattice diameter. -/
def diameterScaledQuasiLocalInfiniteLBitCoefficient
    (g : ℝ) (S : Finset ℕ) : ℝ :=
  g ^ finiteLBitSupportDiameter S *
    quasiLocalInfiniteLBitCoefficient S

/-- On the physical coupling interval, diameter scaling cannot enlarge any coefficient. -/
theorem abs_diameterScaledQuasiLocalInfiniteLBitCoefficient_le
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (S : Finset ℕ) :
    |diameterScaledQuasiLocalInfiniteLBitCoefficient g S| ≤
      |quasiLocalInfiniteLBitCoefficient S| := by
  rw [diameterScaledQuasiLocalInfiniteLBitCoefficient,
    abs_mul, abs_pow, abs_of_nonneg hg0]
  exact mul_le_of_le_one_left (abs_nonneg _)
    (pow_le_one₀ hg0 hg1)

/-- The complete diameter-scaled interaction field remains absolutely summable. -/
theorem summable_abs_diameterScaledQuasiLocalInfiniteLBitCoefficient
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    Summable
      (fun S : Finset ℕ =>
        |diameterScaledQuasiLocalInfiniteLBitCoefficient g S|) :=
  Summable.of_nonneg_of_le
    (fun _ => abs_nonneg _)
    (abs_diameterScaledQuasiLocalInfiniteLBitCoefficient_le hg0 hg1)
    summable_abs_quasiLocalInfiniteLBitCoefficient

/-- One summand of the diameter-scaled thermodynamic energy. -/
def diameterScaledQuasiLocalInfiniteLBitEnergyTerm
    (g : ℝ) (S : Finset ℕ) (σ : InfiniteLBitConfiguration) : ℝ :=
  diameterScaledQuasiLocalInfiniteLBitCoefficient g S *
    infiniteLBitCharacter S σ

@[simp]
theorem abs_diameterScaledQuasiLocalInfiniteLBitEnergyTerm
    (g : ℝ) (S : Finset ℕ) (σ : InfiniteLBitConfiguration) :
    |diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ| =
      |diameterScaledQuasiLocalInfiniteLBitCoefficient g S| := by
  simp [diameterScaledQuasiLocalInfiniteLBitEnergyTerm, abs_mul]

theorem summable_diameterScaledQuasiLocalInfiniteLBitEnergyTerm
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (σ : InfiniteLBitConfiguration) :
    Summable
      (fun S : Finset ℕ =>
        diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ) := by
  apply Summable.of_norm
  simpa [Real.norm_eq_abs] using
    summable_abs_diameterScaledQuasiLocalInfiniteLBitCoefficient hg0 hg1

/-- Genuine infinite-volume diameter-scaled energy. -/
def diameterScaledQuasiLocalInfiniteLBitEnergy
    (g : ℝ) (σ : InfiniteLBitConfiguration) : ℝ :=
  ∑' S : Finset ℕ,
    diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ

/-- The original total interaction mass uniformly bounds every scaled infinite energy. -/
theorem abs_diameterScaledQuasiLocalInfiniteLBitEnergy_le_mass
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (σ : InfiniteLBitConfiguration) :
    |diameterScaledQuasiLocalInfiniteLBitEnergy g σ| ≤
      quasiLocalInfiniteLBitMass := by
  calc
    |diameterScaledQuasiLocalInfiniteLBitEnergy g σ|
        ≤ ∑' S : Finset ℕ,
            |diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ| := by
          simpa [diameterScaledQuasiLocalInfiniteLBitEnergy,
            Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm
              (show Summable
                (fun S : Finset ℕ =>
                  ‖diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ‖) by
                simpa [Real.norm_eq_abs] using
                  summable_abs_diameterScaledQuasiLocalInfiniteLBitCoefficient
                    hg0 hg1)
    _ = ∑' S : Finset ℕ,
          |diameterScaledQuasiLocalInfiniteLBitCoefficient g S| := by
            apply tsum_congr
            intro S
            simp
    _ ≤ ∑' S : Finset ℕ,
          |quasiLocalInfiniteLBitCoefficient S| := by
            exact Summable.tsum_le_tsum
              (fun S => abs_diameterScaledQuasiLocalInfiniteLBitCoefficient_le
                hg0 hg1 S)
              (summable_abs_diameterScaledQuasiLocalInfiniteLBitCoefficient
                hg0 hg1)
              summable_abs_quasiLocalInfiniteLBitCoefficient
    _ = quasiLocalInfiniteLBitMass := rfl

/-- First-`n`-site restriction of the scaled infinite energy. -/
def diameterScaledQuasiLocalInfiniteLBitWindowEnergy
    (g : ℝ) (n : ℕ) (σ : InfiniteLBitConfiguration) : ℝ :=
  ∑ S ∈ quasiLocalInfiniteLBitWindowSupports n,
    diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ

/-- The scaled first-site windows converge uniformly to the scaled infinite energy. -/
theorem tendstoUniformly_diameterScaledQuasiLocalInfiniteLBitWindowEnergy
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    TendstoUniformly
      (diameterScaledQuasiLocalInfiniteLBitWindowEnergy g)
      (diameterScaledQuasiLocalInfiniteLBitEnergy g) atTop := by
  have hgeneral :
      TendstoUniformly
        (fun F : Finset (Finset ℕ) =>
          fun σ : InfiniteLBitConfiguration =>
            ∑ S ∈ F,
              diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ)
        (diameterScaledQuasiLocalInfiniteLBitEnergy g) atTop := by
    change TendstoUniformly
      (fun F : Finset (Finset ℕ) =>
        fun σ : InfiniteLBitConfiguration =>
          ∑ S ∈ F,
            diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ)
      (fun σ =>
        ∑' S : Finset ℕ,
          diameterScaledQuasiLocalInfiniteLBitEnergyTerm g S σ) atTop
    apply tendstoUniformly_tsum
      (summable_abs_diameterScaledQuasiLocalInfiniteLBitCoefficient hg0 hg1)
    intro S σ
    simp [Real.norm_eq_abs]
  rw [Metric.tendstoUniformly_iff] at hgeneral ⊢
  intro ε hε
  have heventually :=
    tendsto_quasiLocalInfiniteLBitWindowSupports_atTop.eventually
      (hgeneral ε hε)
  simpa [diameterScaledQuasiLocalInfiniteLBitWindowEnergy] using
    heventually

/-- The scaled infinite energy remains continuous in the product topology. -/
theorem continuous_diameterScaledQuasiLocalInfiniteLBitEnergy
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    Continuous (diameterScaledQuasiLocalInfiniteLBitEnergy g) := by
  apply continuous_tsum
    (fun S =>
      continuous_const.mul
        (continuous_infiniteLBitCharacter S))
    (summable_abs_diameterScaledQuasiLocalInfiniteLBitCoefficient hg0 hg1)
  intro S σ
  simp

/-- Canonical inclusion of a finite first-site window preserves support diameter. -/
theorem finiteLBitSupportDiameter_map_finValEmbedding
    {n : ℕ} (S : Finset (Fin n)) :
    finiteLBitSupportDiameter (S.map Fin.valEmbedding) =
      lbitSupportDiameterBirthOrder S := by
  simp [finiteLBitSupportDiameter, lbitSupportDiameterBirthOrder]
  rfl

/-- Coefficients of the physical first-`n`-site restriction. -/
def diameterScaledQuasiLocalFiniteCoefficient
    (n : ℕ) (g : ℝ) (S : Finset (Fin n)) : ℝ :=
  diameterScaledQuasiLocalInfiniteLBitCoefficient g
    (S.map Fin.valEmbedding)

/-- The physical restriction is exactly the finite diameter-scaled l-bit coefficient family. -/
theorem diameterScaledQuasiLocalFiniteCoefficient_eq
    (n : ℕ) (g : ℝ) (S : Finset (Fin n)) :
    diameterScaledQuasiLocalFiniteCoefficient n g S =
      scaledLBitCoefficient lbitSupportDiameterBirthOrder
        (quasiLocalInfiniteLBitRestriction (Fin n) Fin.valEmbedding)
        g S := by
  rw [diameterScaledQuasiLocalFiniteCoefficient,
    diameterScaledQuasiLocalInfiniteLBitCoefficient,
    finiteLBitSupportDiameter_map_finValEmbedding]
  rfl

/-- Every exact diameter layer in every finite window is rationally independent. -/
theorem quasiLocalInfiniteLBitRestriction_birthLayer_linearIndependent
    (n order : ℕ) :
    LinearIndependent ℚ
      (lbitBirthLayerCoefficient lbitSupportDiameterBirthOrder
        (quasiLocalInfiniteLBitRestriction (Fin n) Fin.valEmbedding)
        order) := by
  let includeLayer :
      LBitBirthLayerSupport (Fin n) lbitSupportDiameterBirthOrder order →
        {S : Finset (Fin n) // S.Nonempty} :=
    fun S => ⟨S.1, S.2.1⟩
  have hinjective : Function.Injective includeLayer := by
    intro S T hST
    apply Subtype.ext
    exact congrArg
      (fun U : {S : Finset (Fin n) // S.Nonempty} => U.1) hST
  have hreal :=
    (quasiLocalInfiniteLBitRestriction_linearIndependent
      (Fin n) Fin.valEmbedding).comp includeLayer hinjective
  let ofRealQ : ℝ →ₗ[ℚ] ℂ :=
    Complex.ofRealCLM.toLinearMap.restrictScalars ℚ
  have hofRealKer : ofRealQ.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Complex.ofReal_injective hxy
  have hcomplex := hreal.map' ofRealQ hofRealKer
  change LinearIndependent ℚ
    (fun S : LBitBirthLayerSupport (Fin n)
      lbitSupportDiameterBirthOrder order =>
        (quasiLocalInfiniteLBitRestriction (Fin n) Fin.valEmbedding S.1 : ℂ))
  exact hcomplex

set_option maxHeartbeats 600000 in
/-- Exact resolved temporal dimension of every finite thermodynamic window. -/
theorem temporalDimension_quasiLocalDiameterScaledLBitSpectralJet_eq
    (n r : ℕ) :
    temporalDimension
        (scaledLBitSpectralJet lbitSupportDiameterBirthOrder
          (quasiLocalInfiniteLBitRestriction (Fin n) Fin.valEmbedding)) r =
      (lbitSupportsBornBefore
        (Fin n) lbitSupportDiameterBirthOrder r).card := by
  exact temporalDimension_scaledLBitSpectralJet_eq_card_bornBefore
    lbitSupportDiameterBirthOrder
    (quasiLocalInfiniteLBitRestriction (Fin n) Fin.valEmbedding) r
    (fun order =>
      quasiLocalInfiniteLBitRestriction_birthLayer_linearIndependent
        n order)

/-- The endpoint pair in the first `b+1` sites. -/
def lbitDiameterPairSupport (b : ℕ) : Finset (Fin (b + 1)) :=
  {⟨0, Nat.zero_lt_succ b⟩, ⟨b, Nat.lt_succ_self b⟩}

theorem lbitDiameterPairSupport_nonempty (b : ℕ) :
    (lbitDiameterPairSupport b).Nonempty := by
  simp [lbitDiameterPairSupport]

/-- Every natural birth order occurs as the exact diameter of an endpoint pair. -/
theorem lbitSupportDiameterBirthOrder_pair (b : ℕ) :
    lbitSupportDiameterBirthOrder (lbitDiameterPairSupport b) = b := by
  simp [lbitSupportDiameterBirthOrder, lbitDiameterPairSupport,
    Nat.dist_zero_left, Nat.dist_zero_right]

/-- The endpoint-pair coefficient is nonzero in every layer. -/
theorem quasiLocalInfiniteLBitRestriction_pair_ne_zero (b : ℕ) :
    quasiLocalInfiniteLBitRestriction (Fin (b + 1)) Fin.valEmbedding
      (lbitDiameterPairSupport b) ≠ 0 := by
  have h :=
    (quasiLocalInfiniteLBitRestriction_linearIndependent
      (Fin (b + 1)) Fin.valEmbedding).ne_zero
      ⟨lbitDiameterPairSupport b,
        lbitDiameterPairSupport_nonempty b⟩
  exact h

/-- At every order, the corresponding finite-volume endpoint reporter has the exact critical sinc
profile, independent of the nonzero coupling. -/
theorem diameterPair_finitePhaseResponse_birth_exact
    (b : ℕ) (g τ : ℝ) (hg : g ≠ 0) :
    (∫ x,
      UnitAddTorus.mFourier
        (lbitSupportIntegerCharacter (lbitDiameterPairSupport b) :
          ((Fin (b + 1) → Bool) → ℤ)) x
      ∂(finiteTorusPhaseProbabilityMeasure
        (lbitEnergy
          (diameterScaledQuasiLocalFiniteCoefficient (b + 1) g))
        (τ / g ^ b) :
        Measure (UnitAddTorus (Fin (b + 1) → Bool)))) =
      Real.sinc
        (τ * (((2 : ℚ) ^ (b + 1)) •
          quasiLocalInfiniteLBitRestriction (Fin (b + 1))
            Fin.valEmbedding (lbitDiameterPairSupport b))) := by
  have hcoeff :
      diameterScaledQuasiLocalFiniteCoefficient (b + 1) g =
        scaledLBitCoefficient lbitSupportDiameterBirthOrder
          (quasiLocalInfiniteLBitRestriction (Fin (b + 1)) Fin.valEmbedding)
          g := by
    funext S
    exact diameterScaledQuasiLocalFiniteCoefficient_eq (b + 1) g S
  rw [hcoeff]
  simpa [lbitSupportDiameterBirthOrder_pair] using
    lbitSupport_scaled_finitePhaseResponse_birth_exact
      lbitSupportDiameterBirthOrder
      (quasiLocalInfiniteLBitRestriction (Fin (b + 1)) Fin.valEmbedding)
      (lbitDiameterPairSupport b) g τ hg

/-- **Thermodynamic diameter-cascade capstone.**  One quasi-local infinite interaction field has a
uniform finite-window thermodynamic limit, exact finite-volume dimension at every resolution, and
one nonzero critical reporter at every birth order. -/
theorem thermodynamicDiameterLBitCascadeLaw
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    Summable
        (fun S : Finset ℕ =>
          |diameterScaledQuasiLocalInfiniteLBitCoefficient g S|) ∧
    TendstoUniformly
      (diameterScaledQuasiLocalInfiniteLBitWindowEnergy g)
      (diameterScaledQuasiLocalInfiniteLBitEnergy g) atTop ∧
    (∀ n r,
      temporalDimension
          (scaledLBitSpectralJet lbitSupportDiameterBirthOrder
            (quasiLocalInfiniteLBitRestriction (Fin n) Fin.valEmbedding)) r =
        (lbitSupportsBornBefore
          (Fin n) lbitSupportDiameterBirthOrder r).card) ∧
    (∀ b g τ, g ≠ 0 →
      (∫ x,
        UnitAddTorus.mFourier
          (lbitSupportIntegerCharacter (lbitDiameterPairSupport b) :
            ((Fin (b + 1) → Bool) → ℤ)) x
        ∂(finiteTorusPhaseProbabilityMeasure
          (lbitEnergy
            (diameterScaledQuasiLocalFiniteCoefficient (b + 1) g))
          (τ / g ^ b) :
          Measure (UnitAddTorus (Fin (b + 1) → Bool)))) =
        Real.sinc
          (τ * (((2 : ℚ) ^ (b + 1)) •
            quasiLocalInfiniteLBitRestriction (Fin (b + 1))
              Fin.valEmbedding (lbitDiameterPairSupport b)))) := by
  exact ⟨
    summable_abs_diameterScaledQuasiLocalInfiniteLBitCoefficient hg0 hg1,
    tendstoUniformly_diameterScaledQuasiLocalInfiniteLBitWindowEnergy hg0 hg1,
    temporalDimension_quasiLocalDiameterScaledLBitSpectralJet_eq,
    fun b g τ hg => diameterPair_finitePhaseResponse_birth_exact b g τ hg⟩

end

end GaloisForLFunctions.HTGeometry
