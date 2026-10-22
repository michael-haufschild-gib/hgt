import GaloisForLFunctions.HTGeometry.LogarithmicDifferentialAlgebraicity
import GaloisForLFunctions.RHTower.ExpAlgebraicTranscendental

/-!
# Integral independence of numerical exponential defects

For a rationally independent complex tuple `x`, the logarithmic Kähler defects

`d(exp xᵢ) / exp xᵢ - dxᵢ`

are integrally independent.  An integral relation packages into `dw = w ds`, where
`s = ∑ mᵢxᵢ` and `w = ∏ exp(xᵢ)^mᵢ = exp s`.  Logarithmic-differential algebraicity makes both
`s` and `w` algebraic, while rational independence makes `s` nonzero; Hermite–Lindemann then gives
the contradiction.
-/

open Polynomial

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Logarithmic derivative of a Laurent power for a derivation into a module. -/
theorem derivation_log_zpow
    {R K M : Type*} [CommRing R] [Field K] [AddCommGroup M]
    [Algebra R K] [Module K M] [Module R M] [IsScalarTower R K M]
    (D : Derivation R K M) (u : K) (m : ℤ) (hu : u ≠ 0) :
    (u ^ m)⁻¹ • D (u ^ m) = (m : K) • (u⁻¹ • D u) := by
  have hcoeff :
      (u ^ m)⁻¹ * ((m : K) * u ^ (m - 1)) = (m : K) * u⁻¹ := by
    calc
      (u ^ m)⁻¹ * ((m : K) * u ^ (m - 1)) =
          (m : K) * (u ^ (m - 1) * (u ^ m)⁻¹) := by ring
      _ = (m : K) * (u ^ (m - 1) * u ^ (-m)) := by rw [zpow_neg]
      _ = (m : K) * u ^ ((m - 1) + (-m)) := by rw [zpow_add₀ hu]
      _ = (m : K) * u⁻¹ := by congr 1; rw [show (m - 1) + (-m) = -1 by omega, zpow_neg_one]
  rw [D.leibniz_zpow, ← Int.cast_smul_eq_zsmul K]
  simp only [smul_smul, hcoeff]

/-- Logarithmic derivative turns multiplication of nonzero field elements into addition, for a
derivation into an arbitrary module. -/
theorem derivation_log_mul
    {R K M : Type*} [CommRing R] [Field K] [AddCommGroup M]
    [Algebra R K] [Module K M] [Module R M] [IsScalarTower R K M]
    (D : Derivation R K M) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v)⁻¹ • D (u * v) = u⁻¹ • D u + v⁻¹ • D v := by
  rw [D.leibniz]
  simp only [smul_add, smul_smul]
  have huv : u * v ≠ 0 := mul_ne_zero hu hv
  rw [add_comm]
  congr 1
  · field_simp
  · field_simp

/-- Logarithmic derivative of a finite Laurent monomial is its integral exponent sum. -/
theorem derivation_log_finprod_zpow
    {ι R K M : Type*} [CommRing R] [Field K] [AddCommGroup M]
    [Algebra R K] [Module K M] [Module R M] [IsScalarTower R K M]
    (D : Derivation R K M) (t : Finset ι) (u : ι → K) (m : ι → ℤ)
    (hu : ∀ i ∈ t, u i ≠ 0) :
    (∏ i ∈ t, u i ^ m i)⁻¹ • D (∏ i ∈ t, u i ^ m i) =
      ∑ i ∈ t, (m i : K) • (u i)⁻¹ • D (u i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      have hui : u i ≠ 0 := hu i (Finset.mem_insert_self i t)
      have hut : ∀ j ∈ t, u j ≠ 0 := fun j hj => hu j (Finset.mem_insert_of_mem hj)
      have hprod : ∏ j ∈ t, u j ^ m j ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j hj => zpow_ne_zero _ (hut j hj)
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        derivation_log_mul D _ _ (zpow_ne_zero _ hui) hprod,
        derivation_log_zpow D _ _ hui, ih hut]

/-- Numerical logarithmic Kähler defect of one exponential pair, relative to the algebraic
numbers. -/
def schanuelDefect (z : ℂ) :
    KaehlerDifferential (algebraicClosure ℚ ℂ) ℂ :=
  (Complex.exp z)⁻¹ •
      KaehlerDifferential.D (algebraicClosure ℚ ℂ) ℂ (Complex.exp z) -
    KaehlerDifferential.D (algebraicClosure ℚ ℂ) ℂ z

/-- **Integral exponential-defect independence.** For a rationally linearly independent complex
tuple, the numerical logarithmic Kähler defects are integrally independent. -/
theorem schanuelDefect_integer_relation
    {n : ℕ} (x : Fin n → ℂ) (hx : LinearIndependent ℚ x)
    (m : Fin n → ℤ)
    (hdefect : ∑ i, (m i : ℂ) • schanuelDefect (x i) = 0) :
    m = 0 := by
  classical
  let A := algebraicClosure ℚ ℂ
  let D := KaehlerDifferential.D A ℂ
  let s : ℂ := ∑ i, m i • x i
  let w : ℂ := ∏ i, Complex.exp (x i) ^ m i
  letI : Algebra.IsAlgebraic ℚ A := by
    exact algebraicClosure.isAlgebraic ℚ ℂ
  by_cases hm : m = 0
  · exact hm
  have hexp0 : ∀ i, Complex.exp (x i) ≠ 0 := fun i => Complex.exp_ne_zero _
  have hw : w ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hexp0 i)
  have hsum :
      ∑ i, (m i : ℂ) • ((Complex.exp (x i))⁻¹ • D (Complex.exp (x i))) =
        ∑ i, (m i : ℂ) • D (x i) := by
    apply sub_eq_zero.mp
    simpa only [schanuelDefect, smul_sub, Finset.sum_sub_distrib] using hdefect
  have hDs : D s = ∑ i, (m i : ℂ) • D (x i) := by
    simp only [s, map_sum, map_zsmul]
    simp_rw [← Int.cast_smul_eq_zsmul ℂ]
  have hlogw : w⁻¹ • D w =
      ∑ i, (m i : ℂ) • ((Complex.exp (x i))⁻¹ • D (Complex.exp (x i))) := by
    simpa only [w] using derivation_log_finprod_zpow D Finset.univ
      (fun i => Complex.exp (x i)) m (fun i _ => hexp0 i)
  have hlog : D w = w • D s := by
    have hnormalized : w⁻¹ • D w = D s := by rw [hlogw, hsum, ← hDs]
    have hscaled := congrArg (fun q => w • q) hnormalized
    simpa only [smul_smul, mul_inv_cancel₀ hw, one_smul] using hscaled
  obtain ⟨hsA, hwA⟩ := algebraic_of_kaehlerD_eq_smul hw hlog
  have hsQ : IsAlgebraic ℚ s := hsA.restrictScalars ℚ
  have hwQ : IsAlgebraic ℚ w := hwA.restrictScalars ℚ
  have hs0 : s ≠ 0 := by
    intro hs
    have hcomb : Fintype.linearCombination ℚ x (fun i => (m i : ℚ)) = 0 := by
      rw [Fintype.linearCombination_apply]
      calc
        ∑ i, (m i : ℚ) • x i = ∑ i, m i • x i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Algebra.smul_def, zsmul_eq_mul]
          norm_cast
        _ = 0 := hs
    have hc : (fun i => (m i : ℚ)) = 0 :=
      hx.fintypeLinearCombination_injective (by simpa using hcomb)
    have hm0 : m = 0 := by
      funext i
      have hi : (m i : ℚ) = 0 := by simpa using congrFun hc i
      exact_mod_cast hi
    exact hm hm0
  have hwexp : w = Complex.exp s := by
    dsimp only [w, s]
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [zsmul_eq_mul, Complex.exp_int_mul]
  have hsZ : IsAlgebraic ℤ s :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hsQ
  have htrans : Transcendental ℚ (Complex.exp s) :=
    exp_algebraic_transcendental hsZ hs0
  exfalso
  apply htrans
  rw [← hwexp]
  exact hwQ

end

end GaloisForLFunctions.RHTower
