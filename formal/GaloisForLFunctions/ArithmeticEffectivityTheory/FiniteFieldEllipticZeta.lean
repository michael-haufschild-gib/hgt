import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity

/-!
# The point-count zeta function of the elliptic curve over `𝔽₃`

The projective points of `Y²Z=X³−XZ²` over every finite extension give the ghost
coefficients of this zeta series. The hyperelliptic theorem supplies two Frobenius
eigenvalues of modulus `√3`; their reciprocal factors form a degree-two numerator.
The rationality identity is proved in formal power series, and its numerator is
nonzero at both denominator roots. Thus the two zeta zeros, counted with multiplicity,
are genuine and become uncancelled denominator zeros of the reciprocal function.
-/

open Polynomial Finset
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open ArithmeticCastelnuovoSeveri RHTower.Hyperelliptic
attribute [local instance] Classical.propDecidable
noncomputable section

lemma characteristic_ne_two : ringChar Constants ≠ 2 := by
  rw [ringChar.eq Constants 3]
  norm_num

abbrev FrobeniusIndex := Fin (lRoots cubic).toList.length

def datum : CurveDatum FrobeniusIndex :=
  hyperellipticDatum characteristic_ne_two cubic_squarefree cubic_odd

lemma card_frobeniusIndex : Fintype.card FrobeniusIndex = 2 := by
  rw [card_hyperellipticDatum cubic_odd, cubic_natDegree]

lemma datum_q : datum.q = 3 := by
  change (Fintype.card (ZMod 3) : ℝ) = 3
  rw [ZMod.card]
  norm_num

lemma datum_alpha (i : FrobeniusIndex) : datum.alpha i = rootEnum (lRoots cubic) i := by
  change (Real.sqrt (Fintype.card Constants) : ℂ) *
    (rootEnum (lRoots cubic) i / (Real.sqrt (Fintype.card Constants) : ℂ)) = _
  exact mul_div_cancel₀ _ sqrt_card_ne_zero

lemma norm_alpha (i : FrobeniusIndex) : ‖datum.alpha i‖ = Real.sqrt 3 := by
  rw [datum_alpha]
  simpa [Constants, ZMod.card] using
    norm_rootEnum_eq characteristic_ne_two cubic_squarefree cubic_odd i

lemma alpha_ne_zero (i : FrobeniusIndex) : datum.alpha i ≠ 0 := by
  intro h
  have hn := norm_alpha i
  rw [h, norm_zero] at hn
  exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne' hn.symm

lemma datum_pointCount (E : Type*) [Field E] [Fintype E] [Algebra Constants E] :
    datum.pointCount (Module.finrank Constants E) = (Nat.card (Points E) : ℝ) := by
  rw [card_points]
  push_cast
  exact hyperellipticDatum_pointCount characteristic_ne_two cubic_squarefree cubic_odd E

/-- The actual projective point count on the extension of degree n; degree zero is a ghost convention. -/

def extensionPointCount (n : ℕ) : ℕ :=
  if hn : n = 0 then 0 else
    letI : NeZero n := ⟨hn⟩
    Nat.card (Points (FiniteField.Extension Constants 3 n))

lemma extensionPointCount_zero : extensionPointCount 0 = 0 := by
  simp [extensionPointCount]

lemma extensionPointCount_eq (n : ℕ) [NeZero n] :
    (extensionPointCount n : ℝ) = datum.pointCount n := by
  letI := Fintype.ofFinite (FiniteField.Extension Constants 3 n)
  rw [extensionPointCount, dif_neg (NeZero.ne n),
    ← datum_pointCount]
  congr 1
  convert! FiniteField.finrank_extension Constants 3 n using 1
  congr 1
  exact Subsingleton.elim _ _

def pointCountGhost : PowerSeries ℂ := PowerSeries.mk fun n => (extensionPointCount n : ℂ)

lemma pointCountGhost_eq : pointCountGhost = datum.ghostSeries := by
  ext n
  simp only [pointCountGhost, CurveDatum.ghostSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn, extensionPointCount_zero]
  · letI : NeZero n := ⟨hn⟩
    rw [if_neg hn, ← extensionPointCount_eq]
    simp only [Complex.ofReal_natCast]

def numerator : ℂ[X] := ∏ i : FrobeniusIndex, (1 - C (datum.alpha i) * X)

lemma numerator_constantCoeff : numerator.coeff 0 = 1 := by
  simp [numerator, coeff_zero_eq_eval_zero, eval_prod]

lemma numerator_factor_degree (i : FrobeniusIndex) :
    (1 - C (datum.alpha i) * X).natDegree = 1 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt, natDegree_C_mul_X _ (alpha_ne_zero i)]
  rw [natDegree_one, natDegree_C_mul_X _ (alpha_ne_zero i)]
  exact Nat.zero_lt_one

lemma numerator_factor_ne_zero (i : FrobeniusIndex) :
    (1 - C (datum.alpha i) * X : ℂ[X]) ≠ 0 := by
  intro h
  have hd := numerator_factor_degree i
  rw [h, natDegree_zero] at hd
  exact Nat.zero_ne_one hd

lemma numerator_degree : numerator.natDegree = 2 := by
  rw [numerator, natDegree_prod _ _ (fun i _ => numerator_factor_ne_zero i)]
  simp only [numerator_factor_degree, sum_const, card_univ, smul_eq_mul, mul_one,
    card_frobeniusIndex]

lemma numeratorSeries_eq : (numerator : PowerSeries ℂ) = datum.hOnePoly := by
  change Polynomial.coeToPowerSeries.ringHom (∏ i : FrobeniusIndex, (1 - C (datum.alpha i) * X)) = _
  rw [map_prod]
  simp only [map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X, CurveDatum.hOnePoly]

/-- The rational numerator has precisely two complex roots, counted with multiplicity. -/

lemma numerator_root_count : numerator.roots.card = 2 := by
  rw [IsAlgClosed.card_roots_eq_natDegree, numerator_degree]

lemma numerator_ne_zero : numerator ≠ 0 := by
  intro h
  have hc := numerator_constantCoeff
  rw [h, coeff_zero] at hc
  exact zero_ne_one hc

lemma numerator_eval (z : ℂ) : numerator.eval z = ∏ i, (1 - datum.alpha i * z) := by
  simp only [numerator, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]

lemma numerator_eval_eq_zero_iff (z : ℂ) :
    numerator.eval z = 0 ↔ ∃ i : FrobeniusIndex, z = (datum.alpha i)⁻¹ := by
  rw [numerator_eval, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, _, hi⟩
    refine ⟨i, (mul_left_cancel₀ (alpha_ne_zero i)) ?_⟩
    rw [mul_inv_cancel₀ (alpha_ne_zero i)]
    exact (sub_eq_zero.mp hi).symm
  · rintro ⟨i, rfl⟩
    exact ⟨i, mem_univ i, by rw [mul_inv_cancel₀ (alpha_ne_zero i), sub_self]⟩

/-- The zeros of the numerator lie on the circle of radius `1/√3`. -/

lemma numerator_zero_norm (z : ℂ) (hz : numerator.eval z = 0) :
    ‖z‖ = (Real.sqrt 3)⁻¹ := by
  obtain ⟨i, rfl⟩ := (numerator_eval_eq_zero_iff z).mp hz
  rw [norm_inv, norm_alpha]

lemma numerator_zero_norm_sq (z : ℂ) (hz : numerator.eval z = 0) :
    ‖z‖ ^ 2 = (1 / 3 : ℝ) := by
  rw [numerator_zero_norm z hz, inv_pow, Real.sq_sqrt (by norm_num)]
  simp only [one_div]

lemma numerator_at_one_ne_zero : numerator.eval 1 ≠ 0 := by
  intro h
  have hn := numerator_zero_norm_sq 1 h
  norm_num at hn

lemma numerator_at_third_ne_zero : numerator.eval (1 / 3) ≠ 0 := by
  intro h
  have hn := numerator_zero_norm_sq (1 / 3) h
  norm_num [norm_div] at hn

/-- The zeta series of the actual curve, characterized below by all its point counts. -/

def zeta : PowerSeries ℂ := datum.zetaSeries

lemma zeta_constantCoeff : PowerSeries.constantCoeff zeta = 1 :=
  datum.constantCoeff_zetaSeries

/-- The logarithmic derivative has the actual extension point counts as coefficients. -/

lemma zeta_hasGhost : HasGhost zeta pointCountGhost := by
  rw [pointCountGhost_eq]
  exact datum.zetaSeries_hasGhost

/-- Constant term one and all projective point counts determine this zeta series uniquely. -/

lemma zeta_unique (Z : PowerSeries ℂ) (h₀ : PowerSeries.constantCoeff Z = 1)
    (hZ : HasGhost Z pointCountGhost) : Z = zeta := by
  apply eq_of_hasGhost hZ zeta_hasGhost
  · exact h₀.trans zeta_constantCoeff.symm
  · simp [pointCountGhost, extensionPointCount_zero]

/-- The finite-field rationality identity, with no cancellation at either pole. -/

lemma zeta_rational :
    ((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) * zeta =
      (numerator : PowerSeries ℂ) := by
  rw [numeratorSeries_eq]
  change ((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) *
    (geom 1 * geom (datum.q : ℂ) * datum.hOnePoly) = _
  rw [datum_q]
  have h₁ : (1 - PowerSeries.X) * geom 1 = 1 := by
    simpa only [map_one, one_mul] using one_sub_mul_geom (1 : ℂ)
  have h₃ : (1 - PowerSeries.C 3 * PowerSeries.X) * geom 3 = 1 := one_sub_mul_geom 3
  calc
    _ = ((1 - PowerSeries.X) * geom 1) *
        ((1 - PowerSeries.C 3 * PowerSeries.X) * geom 3) * datum.hOnePoly := by
          norm_num only [Complex.ofReal_ofNat]
          ring
    _ = datum.hOnePoly := by rw [h₁, h₃, one_mul, one_mul]

/-- The numerator zeros remain denominator zeros of the reciprocal zeta function. -/

lemma reciprocal_numerator_nonzero (z : ℂ) (hz : numerator.eval z = 0) :
    (1 - z) * (1 - 3 * z) ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have : z = 1 := (sub_eq_zero.mp h).symm
    exact numerator_at_one_ne_zero (this ▸ hz)
  · intro h
    have : z = 1 / 3 := by linear_combination -(1 / 3 : ℂ) * h
    exact numerator_at_third_ne_zero (this ▸ hz)

/-- The rational zeta function, evaluated away from `T=1` and `T=1/3`. -/

def zetaFunction (T : ℂ) : ℂ := numerator.eval T / ((1 - T) * (1 - 3 * T))

/-- Every numerator root is a genuine zero in the domain of the rational zeta function. -/

lemma numerator_root_is_zeta_zero (T : ℂ) (hT : numerator.eval T = 0) :
    zetaFunction T = 0 ∧ (1 - T) * (1 - 3 * T) ≠ 0 :=
  ⟨by simp only [zetaFunction, hT, zero_div], reciprocal_numerator_nonzero T hT⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
