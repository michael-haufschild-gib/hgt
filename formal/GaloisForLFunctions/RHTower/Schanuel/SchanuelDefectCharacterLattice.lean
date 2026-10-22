import GaloisForLFunctions.RHTower.Schanuel.SchanuelDefectLattice

/-!
# Character lattice of value-field exponential defects

An integral combination of logarithmic exponential defects is itself a logarithmic derivative
exactly when the matching additive combination is algebraic over the constant field.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Logarithmic exponential defect of a pair in an arbitrary characteristic-zero field
extension. -/
def valueDefect
    {C L : Type*} [Field C] [Field L] [Algebra C L]
    (x y : L) : KaehlerDifferential C L :=
  y⁻¹ • KaehlerDifferential.D C L y - KaehlerDifferential.D C L x

/-- Logarithmic derivative turns division of nonzero field elements into subtraction. -/
theorem derivation_log_div
    {R K M : Type*} [CommRing R] [Field K] [AddCommGroup M]
    [Algebra R K] [Module K M] [Module R M] [IsScalarTower R K M]
    (D : Derivation R K M) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) :
    (u / v)⁻¹ • D (u / v) =
      u⁻¹ • D u - v⁻¹ • D v := by
  rw [div_eq_mul_inv, derivation_log_mul D u v⁻¹ hu (inv_ne_zero hv),
    D.leibniz_inv]
  simp only [smul_smul]
  have hcoeff : (v⁻¹)⁻¹ * (-(v⁻¹ ^ 2)) = -v⁻¹ := by
    field_simp
  rw [hcoeff, neg_smul]
  simp only [sub_eq_add_neg]

/-- An integral defect sum is the logarithmic derivative of the torus monomial minus the
differential of the matching additive linear form. -/
theorem sum_valueDefect_eq_log_monomial_sub
    {ι C L : Type*} [Fintype ι] [Field C] [Field L] [Algebra C L]
    (x y : ι → L) (hy : ∀ i, y i ≠ 0) (m : ι → ℤ) :
    ∑ i, (m i : L) • valueDefect (C := C) (x i) (y i) =
      (∏ i, y i ^ m i)⁻¹ •
          KaehlerDifferential.D C L (∏ i, y i ^ m i) -
        KaehlerDifferential.D C L (∑ i, m i • x i) := by
  classical
  rw [derivation_log_finprod_zpow
    (KaehlerDifferential.D C L) Finset.univ y m]
  · simp [valueDefect, smul_sub, Finset.sum_sub_distrib, map_sum,
      ← Int.cast_smul_eq_zsmul L]
  · exact fun i _ => hy i

/-- **Exact defect character lattice.** Integral combinations of value-field defects are
logarithmic derivatives exactly when the matching additive combination is algebraic over the
constant field. -/
theorem defect_integer_combination_is_logarithmic_iff
    {ι C L : Type*} [Fintype ι] [Field C] [Field L] [Algebra C L] [CharZero C]
    (x y : ι → L) (hy : ∀ i, y i ≠ 0) (m : ι → ℤ) :
    (∃ f : L, f ≠ 0 ∧
      ∑ i, (m i : L) • valueDefect (C := C) (x i) (y i) =
        f⁻¹ • KaehlerDifferential.D C L f) ↔
      IsAlgebraic C (∑ i, m i • x i) := by
  classical
  let D := KaehlerDifferential.D C L
  let s : L := ∑ i, m i • x i
  let u : L := ∏ i, y i ^ m i
  have hu : u ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hy i)
  have hsum :
      ∑ i, (m i : L) • valueDefect (C := C) (x i) (y i) =
        u⁻¹ • D u - D s := by
    simpa only [D, s, u] using sum_valueDefect_eq_log_monomial_sub x y hy m
  constructor
  · rintro ⟨f, hf, hrel⟩
    let w : L := u / f
    have hw : w ≠ 0 := div_ne_zero hu hf
    have hwlog : w⁻¹ • D w = D s := by
      change (u / f)⁻¹ • D (u / f) = D s
      rw [derivation_log_div D u f hu hf]
      rw [hsum] at hrel
      apply (sub_eq_iff_eq_add).mpr
      have h := (sub_eq_iff_eq_add).mp hrel
      simpa only [add_comm] using h
    have hlog : D w = w • D s := by
      have h := congrArg (fun z => w • z) hwlog
      simpa only [smul_smul, mul_inv_cancel₀ hw, one_smul] using h
    exact isAlgebraic_left_of_kaehlerD_eq_smul hw hlog
  · intro hs
    refine ⟨u, hu, ?_⟩
    rw [hsum]
    have hds : D s = 0 :=
      GaloisForLFunctions.kaehlerD_eq_zero_of_isAlgebraic hs
    rw [hds, sub_zero]

end


end GaloisForLFunctions.RHTower
