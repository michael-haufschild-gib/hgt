import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteBruhatPeriodicWeights

/-!
# Exact periodic trace packets for rational adelic pure tensors

This file identifies the full rational orbit sum of an adelic Bruhat pure
tensor with a periodic weighted integer-lattice trace.  A positive common
denominator is extracted from finite-adele compact support, the rational sum
is reindexed without dropping zero terms, and finite-adic local constancy
factors the remaining coefficients through a finite residue weight.

The result is an exact bridge from the genuine adelic source to the weighted
Poisson theorem; it is not a model or a replacement trace.
-/

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct algebraMap Topology

namespace GaloisForLFunctions
namespace RHTower

/-- Reindex a `tsum` along an injection when every nonzero summand lies in its
range. -/
theorem ccmRational_tsum_reindex_of_support_subset_range
    {A B : Type*} (g : A → B) (hg : Function.Injective g)
    (F : B → ℂ) (hs : Function.support F ⊆ Set.range g) :
    (∑' b : B, F b) = ∑' a : A, F (g a) := by
  let e : A ≃ Set.range g := Equiv.ofInjective g hg
  calc
    (∑' b : B, F b) = ∑' b : Set.range g, F b :=
      (tsum_subtype_eq_of_support_subset hs).symm
    _ = ∑' a : A, F (e a) := (e.tsum_eq fun b => F b).symm
    _ = ∑' a : A, F (g a) := by rfl

/-- Compact support supplies a strictly positive natural common denominator
for every nonzero finite-adele orbit value. -/
theorem ccmRationalFiniteBruhatMulRight_exists_positiveNatDenominator
    (f : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℚ,
      f.1 (algebraMap ℚ CCMRationalFiniteAdele q * b) ≠ 0 →
        algebraMap ℕ ℚ D * q ∈ (algebraMap ℤ ℚ).range := by
  obtain ⟨d, hd, hden⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_integerDenominator f b
  let D : ℕ := d.natAbs
  have hD : 0 < D := Int.natAbs_pos.mpr hd
  refine ⟨D, hD, fun q hq => ?_⟩
  obtain ⟨n, hn⟩ := hden q hq
  by_cases hsign : 0 ≤ d
  · refine ⟨n, ?_⟩
    have hsignQ : 0 ≤ (d : ℚ) := by exact_mod_cast hsign
    have hDcast : (D : ℚ) = (d : ℚ) := by
      simp [D, abs_of_nonneg hsignQ]
    simpa [hDcast] using hn
  · refine ⟨-n, ?_⟩
    have hneg : d < 0 := lt_of_not_ge hsign
    have hnegQ : (d : ℚ) < 0 := by exact_mod_cast hneg
    have hDcast : (D : ℚ) = -(d : ℚ) := by
      simp [D, abs_of_neg hnegQ]
    simpa [hDcast] using congrArg Neg.neg hn

/-- Exact rational-to-integer reindexing for a fixed valid positive
denominator. -/
theorem ccmRationalAdelicBruhatPureTensorOrbitSum_eq_integerSum
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (bInf : ℝ) (b : CCMRationalFiniteAdeleˣ)
    (D : ℕ) (hD : 0 < D)
    (hden : ∀ q : ℚ,
      phi.1 (algebraMap ℚ CCMRationalFiniteAdele q * b) ≠ 0 →
        algebraMap ℕ ℚ D * q ∈ (algebraMap ℤ ℚ).range) :
    (∑' q : ℚ,
        ccmRationalAdelicBruhatPureTensorOrbit f phi bInf b q) =
      ∑' n : ℤ,
        f ((bInf / (D : ℝ)) * (n : ℝ)) *
          phi.1 (algebraMap ℚ CCMRationalFiniteAdele
            ((n : ℚ) / (D : ℚ)) * b) := by
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  let g : ℤ → ℚ := fun n => (n : ℚ) / (D : ℚ)
  let F : ℚ → ℂ := fun q =>
    ccmRationalAdelicBruhatPureTensorOrbit f phi bInf b q
  have hg : Function.Injective g := by
    intro n m hnm
    change (n : ℚ) / (D : ℚ) = (m : ℚ) / (D : ℚ) at hnm
    have hcast : (n : ℚ) = (m : ℚ) :=
      (div_left_inj' hDQ).mp hnm
    exact Int.cast_injective hcast
  have hs : Function.support F ⊆ Set.range g := by
    intro q hq
    have hphi :
        phi.1 (algebraMap ℚ CCMRationalFiniteAdele q * b) ≠ 0 := by
      intro hz
      apply hq
      simp [F, ccmRationalAdelicBruhatPureTensorOrbit, hz]
    obtain ⟨n, hn⟩ := hden q hphi
    refine ⟨n, ?_⟩
    dsimp [g]
    apply (div_eq_iff hDQ).2
    calc
      (n : ℚ) = (D : ℚ) * q := hn
      _ = q * (D : ℚ) := mul_comm _ _
  rw [ccmRational_tsum_reindex_of_support_subset_range g hg F hs]
  apply tsum_congr
  intro n
  dsimp [F, g, ccmRationalAdelicBruhatPureTensorOrbit]
  congr 2
  push_cast
  ring

/-- Positive-denominator pullback of the archimedean Schwartz factor. -/
def ccmRationalPositiveDenominatorDilation
    (f : CCMRationalArchimedeanSchwartz)
    (D : ℕ) (hD : 0 < D) : CCMRationalArchimedeanSchwartz :=
  ccmRationalArchimedeanDilation f ((D : ℝ)⁻¹)
    (inv_ne_zero (by exact_mod_cast (ne_of_gt hD)))

@[simp]
theorem ccmRationalPositiveDenominatorDilation_apply
    (f : CCMRationalArchimedeanSchwartz)
    (D : ℕ) (hD : 0 < D) (x : ℝ) :
    ccmRationalPositiveDenominatorDilation f D hD x =
      f ((D : ℝ)⁻¹ * x) :=
  rfl

/-- Exact data reducing one genuine adelic pure-tensor rational trace to a
finite periodic weight. -/
structure CCMRationalAdelicPureTensorPeriodicTracePacket
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  period : ℕ
  period_neZero : NeZero period
  weight : Fin period → ℂ
  finiteCoefficient : ∀ n : ℤ,
    phi.1 (algebraMap ℚ CCMRationalFiniteAdele
      ((n : ℚ) / (denominator : ℚ)) * b) =
      weight (@ccmRationalPeriodicResidue period period_neZero n)
  trace_eq : ∀ bInf : ℝ,
    (∑' q : ℚ,
      ccmRationalAdelicBruhatPureTensorOrbit f phi bInf b q) =
      @ccmRationalPeriodicWeightedTrace period period_neZero weight
        (ccmRationalPositiveDenominatorDilation
          f denominator denominator_pos) bInf

/-- Every genuine adelic Bruhat pure tensor admits an exact periodic trace
packet. -/
theorem ccmRationalAdelicPureTensor_exists_periodicTracePacket
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalFiniteAdeleˣ) :
    Nonempty (CCMRationalAdelicPureTensorPeriodicTracePacket
      f phi b) := by
  obtain ⟨D, hD, hden⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_positiveNatDenominator phi b
  obtain ⟨M, hM0, w, hM, hw⟩ :=
    ccmRationalFiniteBruhat_denominatorOrbit_exists_residueWeight
      phi b (D : ℤ) (by exact_mod_cast (ne_of_gt hD))
  refine ⟨⟨D, hD, M, hM0, w, hw, fun bInf => ?_⟩⟩
  rw [ccmRationalAdelicBruhatPureTensorOrbitSum_eq_integerSum
    f phi bInf b D hD hden]
  rw [ccmRationalPeriodicWeightedTrace]
  apply tsum_congr
  intro n
  rw [← hw n]
  rw [ccmRationalPositiveDenominatorDilation_apply]
  rw [mul_comm]
  congr 1
  ring

end RHTower
end GaloisForLFunctions
