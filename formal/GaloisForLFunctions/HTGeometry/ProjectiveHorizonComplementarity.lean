import GaloisForLFunctions.HTGeometry.ProjectiveJetHorizon
import GaloisForLFunctions.HTGeometry.SchwarzianProjectiveInvariant
import Mathlib.Tactic

/-!
# Projective-horizon complementarity for a hypertranscendental scalar

The positive jets of `x` and of the incompatible projective coordinate `x⁻¹` jointly recover
`x` from second-order data.  Each horizon also contains the same Schwarzian curvature.

This is static differential-field reconstruction.  No evolution or carrier is introduced.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The first derivative of projective inversion. -/
theorem deriv_inv_eq_neg_inv_sq_mul_deriv
    {K : Type*} [Field K] [Differential K] (x : K) :
    (x⁻¹)′ = -x⁻¹ ^ 2 * x′ := by
  simpa [smul_eq_mul] using Differential.deriv.leibniz_inv x

/-- The second derivative of projective inversion. -/
theorem secondDeriv_inv_eq
    {K : Type*} [Field K] [Differential K] (x : K) :
    (x⁻¹)′′ = 2 * x⁻¹ ^ 3 * x′ ^ 2 - x⁻¹ ^ 2 * x′′ := by
  rw [deriv_inv_eq_neg_inv_sq_mul_deriv]
  simp only [map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_inv, smul_eq_mul]
  ring

/-- Every differential jet of a hypertranscendental scalar is nonzero. -/
theorem hypertranscendentalOver_differentialJet_ne_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (n : ℕ) :
    differentialJet n x ≠ 0 := by
  intro hzero
  apply hypertranscendentalOver_jet_transcendental hx n
  simpa [hzero] using (isAlgebraic_zero : IsAlgebraic F (0 : E))

/-- Opposite projective derivative horizons recover the original coordinate from two jets. -/
theorem projectiveInversion_twoJet_reconstruction
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x ≠ 0) (hdx : x′ ≠ 0) :
    x = 2 * x′ / (x′′ / x′ - (x⁻¹)′′ / (x⁻¹)′) := by
  have hdinv : (x⁻¹)′ ≠ 0 := by
    rw [deriv_inv_eq_neg_inv_sq_mul_deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero hx))) hdx
  rw [secondDeriv_inv_eq, deriv_inv_eq_neg_inv_sq_mul_deriv]
  field_simp [hx, hdx, hdinv]
  ring

/-- The Schwarzian uses only positive-order jets, hence belongs to the first jet horizon. -/
theorem schwarzian_mem_jetTailField_one
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] (x : E) :
    schwarzian x ∈ jetTailField F x 1 := by
  have h1 : x′ ∈ jetTailField F x 1 := by
    simpa [differentialJet_succ] using
      (differentialJet_mem_jetTailField F x (n := 1) (m := 1) le_rfl)
  have h2 : x′′ ∈ jetTailField F x 1 := by
    simpa [differentialJet_succ] using
      (differentialJet_mem_jetTailField F x (n := 1) (m := 2) (by omega))
  have h3 : x′′′ ∈ jetTailField F x 1 := by
    simpa [differentialJet_succ] using
      (differentialJet_mem_jetTailField F x (n := 1) (m := 3) (by omega))
  unfold schwarzian
  exact sub_mem (div_mem h3 h1)
    (mul_mem (div_mem (natCast_mem _ 3) (natCast_mem _ 2))
      (pow_mem (div_mem h2 h1) 2))

/-- The two opposite first jet horizons contain the source coordinate itself. -/
theorem hypertranscendentalOver_mem_sup_firstJetTail_inv
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x) :
    x ∈ jetTailField F x 1 ⊔ jetTailField F x⁻¹ 1 := by
  let J : IntermediateField F E := jetTailField F x 1 ⊔ jetTailField F x⁻¹ 1
  have hx0 : x ≠ 0 := by
    simpa only [differentialJet_zero] using
      hypertranscendentalOver_differentialJet_ne_zero hx 0
  have hdx : x′ ≠ 0 := by
    simpa only [differentialJet_succ] using!
      hypertranscendentalOver_differentialJet_ne_zero hx 1
  have hdinv : (x⁻¹)′ ≠ 0 := by
    rw [deriv_inv_eq_neg_inv_sq_mul_deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (inv_ne_zero hx0))) hdx
  have hx1 : x′ ∈ J := by
    exact (show jetTailField F x 1 ≤ J from le_sup_left) (by
      simpa [differentialJet_succ] using
        (differentialJet_mem_jetTailField F x (n := 1) (m := 1) le_rfl))
  have hx2 : x′′ ∈ J := by
    exact (show jetTailField F x 1 ≤ J from le_sup_left) (by
      simpa [differentialJet_succ] using
        (differentialJet_mem_jetTailField F x (n := 1) (m := 2) (by omega)))
  have hi1 : (x⁻¹)′ ∈ J := by
    exact (show jetTailField F x⁻¹ 1 ≤ J from le_sup_right) (by
      simpa [differentialJet_succ] using
        (differentialJet_mem_jetTailField F x⁻¹ (n := 1) (m := 1) le_rfl))
  have hi2 : (x⁻¹)′′ ∈ J := by
    exact (show jetTailField F x⁻¹ 1 ≤ J from le_sup_right) (by
      simpa [differentialJet_succ] using
        (differentialJet_mem_jetTailField F x⁻¹ (n := 1) (m := 2) (by omega)))
  have hden : x′′ / x′ - (x⁻¹)′′ / (x⁻¹)′ ∈ J :=
    sub_mem (div_mem hx2 hx1) (div_mem hi2 hi1)
  let r : E := 2 * x′ / (x′′ / x′ - (x⁻¹)′′ / (x⁻¹)′)
  have hr : r ∈ J := div_mem (mul_mem (natCast_mem J 2) hx1) hden
  have hrec : x = r := projectiveInversion_twoJet_reconstruction x hx0 hdx
  exact Eq.mp (congrArg (fun z : E => z ∈ J) hrec.symm) hr

/-- Opposite first horizons reconstruct every jet generated by the HT source. -/
theorem hypertranscendentalOver_zeroJetTail_le_sup_firstJetTail_inv
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x) :
    jetTailField F x 0 ≤ jetTailField F x 1 ⊔ jetTailField F x⁻¹ 1 := by
  rw [jetTailField, IntermediateField.adjoin_le_iff]
  rintro _ ⟨m, -, rfl⟩
  cases m with
  | zero =>
      exact hypertranscendentalOver_mem_sup_firstJetTail_inv x hx
  | succ m =>
      exact (le_sup_left : jetTailField F x 1 ≤
        jetTailField F x 1 ⊔ jetTailField F x⁻¹ 1)
          (differentialJet_mem_jetTailField F x
            (Nat.succ_le_succ (Nat.zero_le m)))

/-- In the differential field generated by `x`, two opposite horizons have full join. -/
theorem hypertranscendentalOver_sup_firstJetTail_inv_eq_top
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x)
    (hgen : jetTailField F x 0 = ⊤) :
    jetTailField F x 1 ⊔ jetTailField F x⁻¹ 1 = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact hypertranscendentalOver_zeroJetTail_le_sup_firstJetTail_inv x hx

/-- The Schwarzian curvature is common to the two opposite projective horizons. -/
theorem hypertranscendentalOver_schwarzian_mem_inf_firstJetTail_inv
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x) :
    schwarzian x ∈ jetTailField F x 1 ⊓ jetTailField F x⁻¹ 1 := by
  have hx0 : x ≠ 0 := by
    simpa only [differentialJet_zero] using
      hypertranscendentalOver_differentialJet_ne_zero hx 0
  have hdx : x′ ≠ 0 := by
    simpa only [differentialJet_succ] using!
      hypertranscendentalOver_differentialJet_ne_zero hx 1
  rw [IntermediateField.mem_inf]
  refine ⟨schwarzian_mem_jetTailField_one F x, ?_⟩
  rw [← schwarzian_inv x hx0 hdx]
  exact schwarzian_mem_jetTailField_one F x⁻¹

/-- **Power ambiguity collapse.**  In a derivation-closed field, once a power of `x` whose
exponent remains nonzero in the field and one nonzero jet of `x` are visible, `x` itself is
visible. -/
theorem mem_of_pow_mem_and_nonzero_differentialJet_mem_of_cast_ne_zero
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x : K) (k n : ℕ) (hkK : (k : K) ≠ 0) (hx : x ≠ 0)
    (hpow : x ^ k ∈ L)
    (hjet : differentialJet n x ∈ L)
    (hjet0 : differentialJet n x ≠ 0) :
    x ∈ L := by
  have hk : k ≠ 0 := by
    intro hk
    apply hkK
    simp [hk]
  have hpder : (x ^ k)′ ∈ L := hL hpow
  have hlambdaEq : x′ / x = (x ^ k)′ / ((k : K) * x ^ k) := by
    have hpowder : (x ^ k)′ = (k : K) * x ^ (k - 1) * x′ := by
      rw [Derivation.leibniz_pow]
      simp
      ring
    have hpowSplit : x ^ k = x ^ (k - 1) * x := by
      calc
        x ^ k = x ^ ((k - 1) + 1) := by congr 1; omega
        _ = x ^ (k - 1) * x := pow_succ x (k - 1)
    apply (div_eq_iff hx).2
    rw [hpowder, hpowSplit]
    field_simp [hx, hkK]
  have hlambda : x′ / x ∈ L := by
    rw [hlambdaEq]
    exact div_mem hpder (mul_mem (natCast_mem L k) hpow)
  have hratio : ∀ k : ℕ, differentialJet k x / x ∈ L := by
    intro k
    induction k with
    | zero =>
        simpa only [differentialJet_zero, div_self hx] using L.one_mem
    | succ k ih =>
        have hd : (differentialJet k x / x)′ ∈ L := hL ih
        have hrec : differentialJet (k + 1) x / x =
            (differentialJet k x / x)′ +
              (x′ / x) * (differentialJet k x / x) := by
          rw [(Differential.deriv : Derivation ℤ K K).leibniz_div]
          simp only [smul_eq_mul, differentialJet_succ]
          field_simp [hx]
          ring
        rw [hrec]
        exact add_mem hd (mul_mem hlambda ih)
  have hratioN : differentialJet n x / x ∈ L := hratio n
  have hratioN0 : differentialJet n x / x ≠ 0 := div_ne_zero hjet0 hx
  let r : K := differentialJet n x / (differentialJet n x / x)
  have hr : r ∈ L := div_mem hjet hratioN
  have hrec : x = r := by
    dsimp [r]
    field_simp [hx, hjet0, hratioN0]
  exact Eq.mp (congrArg (fun z : K => z ∈ L) hrec.symm) hr

/-- Characteristic-zero specialization of power ambiguity collapse. -/
theorem mem_of_pow_mem_and_nonzero_differentialJet_mem
    {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x : K) (k n : ℕ) (hk : k ≠ 0) (hx : x ≠ 0)
    (hpow : x ^ k ∈ L)
    (hjet : differentialJet n x ∈ L)
    (hjet0 : differentialJet n x ≠ 0) :
    x ∈ L :=
  mem_of_pow_mem_and_nonzero_differentialJet_mem_of_cast_ne_zero
    L hL x k n (Nat.cast_ne_zero.mpr hk) hx hpow hjet hjet0

/-- Quadratic specialization used by projective inversion. -/
theorem mem_of_sq_mem_and_nonzero_differentialJet_mem
    {F K : Type*} [Field F] [Field K] [CharZero K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L)
    (x : K) (n : ℕ) (hx : x ≠ 0)
    (hsq : x ^ 2 ∈ L)
    (hjet : differentialJet n x ∈ L)
    (hjet0 : differentialJet n x ≠ 0) :
    x ∈ L :=
  mem_of_pow_mem_and_nonzero_differentialJet_mem
    L hL x 2 n (by norm_num) hx hsq hjet hjet0

end

end GaloisForLFunctions
