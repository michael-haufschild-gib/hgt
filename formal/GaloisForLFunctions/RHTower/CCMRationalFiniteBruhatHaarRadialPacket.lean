import GaloisForLFunctions.RHTower.CCMRationalProfiniteHaarUnitRadialization
import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatCyclicHaarPacket

/-!
# Haar-radial packets for genuine finite Bruhat factors

Every rational finite Bruhat function admits one denominator and one finite
cyclic quotient which work uniformly over the whole profinite-unit factor.
The resulting residue coefficients are actual Haar integrals, are invariant
under `(ZMod N)ˣ`, and retain the exact finite additive Haar endpoint.

This strengthens pointwise cyclic packets: the period is chosen before the
profinite average, so no non-uniform choice of packet occurs under an
integral.
-/

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped RestrictedProduct algebraMap Classical BigOperators

namespace GaloisForLFunctions.RHTower

private abbrev U := CCMRationalProfiniteUnit
private abbrev IntegralFiniteAdeles :=
  ccmRationalIntegralFiniteAdelesAddSubgroup

/-- Uniform finite-place packet before and after profinite Haar
radialization. -/
structure CCMRationalFiniteBruhatHaarRadialPacket
    (phi : CCMRationalFiniteBruhatSchwartz) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  period : ℕ
  period_neZero : NeZero period
  restricted : IntegralFiniteAdeles → ℂ
  restricted_continuous : Continuous restricted
  restricted_congruenceInvariant :
    CCMRationalIntegralFiniteAdeleCongruenceInvariant period restricted
  rationalDenominator : ∀ (q : ℚ) (u : U),
    phi.1 (algebraMap ℚ CCMRationalFiniteAdele q * u.1) ≠ 0 →
      algebraMap ℕ ℚ denominator * q ∈ (algebraMap ℤ ℚ).range
  finiteCoefficient : ∀ (n : ℤ) (u : U),
    phi.1 (algebraMap ℚ CCMRationalFiniteAdele
        ((n : ℚ) / (denominator : ℚ)) * u.1) =
      ccmRationalProfiniteHaarResidueSample period restricted
        (n : ZMod period) u
  restrictedIntegral_eq :
    (∫ x : IntegralFiniteAdeles, restricted x
      ∂ccmRationalIntegralFiniteAdelesHaar) =
      (denominator : ℝ)⁻¹ • ccmRationalFiniteBruhatIntegral phi

namespace CCMRationalFiniteBruhatHaarRadialPacket

/-- Haar-radial residue coefficient. -/
def averageWeight
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    ZMod P.period → ℂ :=
  ccmRationalProfiniteHaarResidueAverage P.period P.restricted

/-- Haar-radial residue coefficients are unit invariant. -/
theorem averageWeight_unitInvariant
    {phi : CCMRationalFiniteBruhatSchwartz}
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    CCMRationalZModUnitInvariant P.period P.averageWeight := by
  exact ccmRationalProfiniteHaarResidueAverage_unitInvariant
    P.period P.period_neZero.out P.restricted
      P.restricted_congruenceInvariant

end CCMRationalFiniteBruhatHaarRadialPacket

/-- Every genuine rational finite Bruhat function has a uniform
Haar-radial packet. -/
theorem ccmRationalFiniteBruhat_exists_haarRadialPacket
    (phi : CCMRationalFiniteBruhatSchwartz) :
    Nonempty (CCMRationalFiniteBruhatHaarRadialPacket phi) := by
  obtain ⟨D, hD, hsupport, hrational⟩ :=
    ccmRationalFiniteBruhatMulRight_exists_positiveNatFullDenominator
      phi (1 : CCMRationalFiniteAdeleˣ)
  let h := ccmRationalFiniteBruhatDenominatorPullback
    phi (1 : CCMRationalFiniteAdeleˣ) D hD
  letI : NonarchimedeanAddGroup CCMRationalFiniteAdele :=
    ccmRationalFiniteAdele_nonarchimedeanAddGroup
  obtain ⟨V, hV⟩ :=
    ccmRationalFiniteBruhat_exists_openAddSubgroup_stabilizer h
  let W : OpenAddSubgroup IntegralFiniteAdeles :=
    V.comap ccmRationalIntegralFiniteAdelesAddSubgroup.subtype
      continuous_subtype_val
  let N := Nat.card (IntegralFiniteAdeles ⧸ W.toAddSubgroup)
  have hN : N ≠ 0 :=
    ccmRationalIntegralFiniteAdele_openQuotient_card_ne_zero W
  letI hNZ : NeZero N := ⟨hN⟩
  let ψ : IntegralFiniteAdeles → ℂ := fun x => h.1 x.1
  have hψ : Continuous ψ :=
    h.1.continuous.comp continuous_subtype_val
  have hperiod : ∀ x z : IntegralFiniteAdeles,
      ψ (x + N • z) = ψ x := by
    intro x z
    have hzW : N • z ∈ W :=
      ccmRationalIntegralFiniteAdele_openQuotient_nsmulRange_le W ⟨z, rfl⟩
    simpa [ψ] using hV x.1 ⟨(N • z).1, hzW⟩
  have hclass : CCMRationalIntegralFiniteAdeleCongruenceInvariant N ψ := by
    intro x y hxy
    obtain ⟨z, hz⟩ := hxy
    have hx : x = y + N • z := by
      rw [← hz]
      abel
    rw [hx]
    exact hperiod y z
  have hcoeff (n : ℤ) (u : U) :
      phi.1 (algebraMap ℚ CCMRationalFiniteAdele
          ((n : ℚ) / (D : ℚ)) * u.1) =
        ccmRationalProfiniteHaarResidueSample N ψ (n : ZMod N) u := by
    let r : ZMod N := n
    have hcast : ((r.val : ℤ) : ZMod N) = (n : ZMod N) := by
      simpa [r] using ZMod.natCast_zmod_val r
    have hdiag :=
      ccmRationalIntegralFiniteAdeleDiagonal_congruent_of_intCast_eq
        (N := N) (m := (r.val : ℤ)) (n := n) hcast
    have hdiagU := hdiag.mul_right
      (ccmRationalProfiniteUnitIntegralVal u)
    have hsample :
        ccmRationalProfiniteHaarResidueSample N ψ r u =
          ψ (ccmRationalIntegralFiniteAdeleMul
            (ccmRationalIntegralFiniteAdeleDiagonal n)
            (ccmRationalProfiniteUnitIntegralVal u)) := by
      exact hclass hdiagU
    rw [hsample]
    change phi.1 (algebraMap ℚ CCMRationalFiniteAdele
      ((n : ℚ) / (D : ℚ)) * u.1) =
      h.1 (algebraMap ℤ CCMRationalFiniteAdele n * u.1)
    rw [ccmRationalFiniteBruhatDenominatorPullback_apply]
    simp only [Units.val_one, mul_one]
    rw [← mul_assoc]
    congr 1
    rw [show algebraMap ℤ CCMRationalFiniteAdele n =
        algebraMap ℚ CCMRationalFiniteAdele (n : ℚ) by simp,
      ← map_mul]
    congr 1
    field_simp
  have hintegral :
      (∫ x : IntegralFiniteAdeles, ψ x
        ∂ccmRationalIntegralFiniteAdelesHaar) =
        (D : ℝ)⁻¹ • ccmRationalFiniteBruhatIntegral phi := by
    simpa [ψ, h] using
      ccmRationalFiniteBruhatDenominatorPullback_restrictedIntegral_eq
        phi (1 : U) D hD (by
          intro x hx
          simpa using hsupport x (by simpa using hx))
  refine ⟨⟨D, hD, N, hNZ, ψ, hψ, hclass, ?_, hcoeff, hintegral⟩⟩
  intro q u hq
  have hDu := hsupport
    (algebraMap ℚ CCMRationalFiniteAdele q * u.1) (by simpa using hq)
  have hfinite :
      algebraMap ℕ CCMRationalFiniteAdele D *
          algebraMap ℚ CCMRationalFiniteAdele q ∈
        ccmRationalIntegralFiniteAdelesAddSubgroup := by
    intro v
    have hv := mul_mem (hDu v) (u.2.2 v)
    change ((algebraMap ℕ CCMRationalFiniteAdele D *
        (algebraMap ℚ CCMRationalFiniteAdele q * u.1)) *
          ((u.1⁻¹ : CCMRationalFiniteAdeleˣ) :
            CCMRationalFiniteAdele)) v ∈ CCMRationalLocalIntegers v at hv
    have hcancel :
        (u.1 : CCMRationalFiniteAdele) *
            ((u.1⁻¹ : CCMRationalFiniteAdeleˣ) :
              CCMRationalFiniteAdele) = 1 := by
      change ↑(u.1 * u.1⁻¹) = (1 : CCMRationalFiniteAdele)
      simp
    rw [mul_assoc,
      mul_assoc (algebraMap ℚ CCMRationalFiniteAdele q),
      hcancel, mul_one] at hv
    exact hv
  have hmap : algebraMap ℕ CCMRationalFiniteAdele D =
      algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) := by simp
  rw [hmap] at hfinite
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
  intro v
  have hv := hfinite v
  change ((algebraMap ℚ CCMRationalFiniteAdele (D : ℚ) *
    algebraMap ℚ CCMRationalFiniteAdele q) v) ∈
      v.adicCompletionIntegers ℚ at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  change Valued.v
      (algebraMap ℚ (v.adicCompletion ℚ) (D : ℚ) *
        algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 at hv
  rw [← map_mul,
    HeightOneSpectrum.algebraMap_adicCompletion ℤ ℚ v,
    Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  exact hv

end GaloisForLFunctions.RHTower
