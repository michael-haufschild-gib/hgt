import GaloisForLFunctions.HTGeometry.PoincareSeriesPeterssonIntegrand
import Mathlib.Data.ZMod.Units

/-!
# Coprime rows with positive first entry, indexed by `(c, d mod c, ⌊d/c⌋)`

A coprime row `(c, d)` with `c ≥ 1` is determined by `c`, the unit `d mod c`, and the quotient
`⌊d/c⌋`; conversely `(c, u.val + l c)` is coprime for every unit `u` mod `c` and every `l ∈ ℤ`.
This is the bijection `{(c, d) : c > 0} ≃ Σ_{c ≥ 1} (ℤ/c)ˣ × ℤ` used to unfold the Poincaré
series along the translations `l ↦ z + l`.  Along it the Poincaré summand of `(c, u.val + lc)` at
`z` is `(c(z+l) + u.val)^{-k} e(m M_{c,u}(z + l))`, and negating a row multiplies the summand by
`(-1)^k`.
-/

open UpperHalfPlane hiding I
open EisensteinSeries ModularGroup Complex
open scoped MatrixGroups Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Shifted unit rows -/

/-- The coprime row `(c, u.val + l c)`. -/
def shiftedRow (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) : gammaSet 1 1 0 :=
  ⟨![(c : ℤ), (((u : ZMod c).val : ℤ) + l * c)], by
    rw [gammaSet_one_mem_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Int.isCoprime_iff_gcd_eq_one]
    refine IsCoprime.add_mul_right_right ?_ l
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (ZMod.val_coe_unit_coprime u).symm⟩

@[simp] theorem shiftedRow_val_zero (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) :
    (shiftedRow c u l).1 0 = c := rfl

@[simp] theorem shiftedRow_val_one (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) :
    (shiftedRow c u l).1 1 = ((u : ZMod c).val : ℤ) + l * c := rfl

/-- The second entry of a coprime row `(c, d)`, `c ≥ 1`, is a unit mod `c`. -/
theorem isUnit_row_snd (c : ℕ+) (v : gammaSet 1 1 0) (hv : v.1 0 = c) :
    IsUnit ((v.1 1 : ℤ) : ZMod c) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  have h := (gammaSet_one_mem_iff 1 v.1).mp v.2
  rw [hv] at h
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.gcd_comm] using h

/-- The unit `d mod c` of a row `(c, d)`. -/
def rowUnit (c : ℕ+) (v : {v : gammaSet 1 1 0 // v.1 0 = c}) : (ZMod c)ˣ :=
  (isUnit_row_snd c v.1 v.2).unit

theorem rowUnit_coe (c : ℕ+) (v : {v : gammaSet 1 1 0 // v.1 0 = c}) :
    ((rowUnit c v : (ZMod c)ˣ) : ZMod c) = ((v.1.1 1 : ℤ) : ZMod c) :=
  IsUnit.unit_spec _

/-- Rows with first entry `c` correspond to `(d mod c, ⌊d/c⌋)`. -/
def rowFiberEquiv (c : ℕ+) : {v : gammaSet 1 1 0 // v.1 0 = c} ≃ (ZMod c)ˣ × ℤ where
  toFun v := (rowUnit c v, v.1.1 1 / c)
  invFun p := ⟨shiftedRow c p.1 p.2, rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    · exact v.2.symm
    · show (((rowUnit c v : ZMod c).val : ℤ) + (v.1.1 1 / c) * c) = v.1.1 1
      rw [rowUnit_coe, ZMod.val_intCast, Int.emod_def]
      ring
  right_inv p := by
    obtain ⟨u, l⟩ := p
    refine Prod.ext ?_ ?_
    · apply Units.ext
      rw [rowUnit_coe]
      show ((((u : ZMod c).val : ℤ) + l * c : ℤ) : ZMod c) = u
      push_cast
      rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val]
    · show ((((u : ZMod c).val : ℤ) + l * c) / c) = l
      rw [Int.add_mul_ediv_right _ _ (by exact_mod_cast c.ne_zero),
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast ZMod.val_lt _), zero_add]

/-! ## All rows with positive first entry -/

/-- The row attached to `(c, u, l)`. -/
def positiveRowOfSigma (p : Σ c : ℕ+, (ZMod c)ˣ × ℤ) : {v : gammaSet 1 1 0 // 0 < v.1 0} :=
  ⟨shiftedRow p.1 p.2.1 p.2.2, by
    rw [shiftedRow_val_zero]
    exact_mod_cast p.1.pos⟩

theorem positiveRowOfSigma_injective : Function.Injective positiveRowOfSigma := by
  rintro ⟨c, u, l⟩ ⟨c', u', l'⟩ h
  have h0 := congrArg (fun v : {v : gammaSet 1 1 0 // 0 < v.1 0} => v.1.1 0) h
  simp only [positiveRowOfSigma, shiftedRow_val_zero] at h0
  have hc : c = c' := PNat.coe_inj.mp (by exact_mod_cast h0)
  subst hc
  have hval : shiftedRow c u l = shiftedRow c u' l' := congrArg Subtype.val h
  have h1 : (rowFiberEquiv c).symm (u, l) = (rowFiberEquiv c).symm (u', l') := Subtype.ext hval
  have := (rowFiberEquiv c).symm.injective h1
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2]

theorem positiveRowOfSigma_surjective : Function.Surjective positiveRowOfSigma := by
  intro v
  have hpos : 0 < (v.1.1 0).toNat := by
    have := v.2
    omega
  set c : ℕ+ := ⟨(v.1.1 0).toNat, hpos⟩ with hc
  have hvc : v.1.1 0 = c := by
    rw [hc]
    exact (Int.toNat_of_nonneg v.2.le).symm
  refine ⟨⟨c, rowFiberEquiv c ⟨v.1, hvc⟩⟩, Subtype.ext ?_⟩
  have hs := (rowFiberEquiv c).symm_apply_apply ⟨v.1, hvc⟩
  have hval : shiftedRow c (rowFiberEquiv c ⟨v.1, hvc⟩).1 (rowFiberEquiv c ⟨v.1, hvc⟩).2 = v.1 :=
    congrArg Subtype.val hs
  exact hval

/-- **The rows with positive first entry are indexed by `(c, u, l)`.** -/
def positiveRowEquiv : (Σ c : ℕ+, (ZMod c)ˣ × ℤ) ≃ {v : gammaSet 1 1 0 // 0 < v.1 0} :=
  Equiv.ofBijective positiveRowOfSigma ⟨positiveRowOfSigma_injective, positiveRowOfSigma_surjective⟩

theorem positiveRowEquiv_apply (p : Σ c : ℕ+, (ZMod c)ˣ × ℤ) :
    (positiveRowEquiv p).1 = shiftedRow p.1 p.2.1 p.2.2 := rfl

/-! ## The Poincaré summand along a shifted row -/

theorem eisSummand_shiftedRow (k : ℤ) (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) (z : ℍ) :
    eisSummand k (shiftedRow c u l) z
      = ((c : ℂ) * ((z : ℂ) + l) + ((u : ZMod c).val : ℂ)) ^ (-k) := by
  rw [eisSummand]
  congr 1
  simp only [shiftedRow_val_zero, shiftedRow_val_one]
  push_cast
  ring

/-- The matrix attached to the unit row `(c, u.val)`. -/
def unitRowMatrix (c : ℕ+) (u : (ZMod c)ˣ) : SL(2, ℤ) := gammaSetMatrix (shiftedRow c u 0)

theorem exists_gammaSetMatrix_shiftedRow_smul (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) (z : ℍ) :
    ∃ n : ℤ, gammaSetMatrix (shiftedRow c u l) • z
      = ModularGroup.T ^ n • (unitRowMatrix c u • (ModularGroup.T ^ l • z)) := by
  have h0 : gammaSetMatrix (shiftedRow c u l) 1 0 = (unitRowMatrix c u * ModularGroup.T ^ l) 1 0 := by
    rw [gammaSetMatrix_apply_one_zero, shiftedRow_val_zero, Matrix.SpecialLinearGroup.coe_mul,
      coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two, unitRowMatrix]
  have h1 : gammaSetMatrix (shiftedRow c u l) 1 1 = (unitRowMatrix c u * ModularGroup.T ^ l) 1 1 := by
    rw [gammaSetMatrix_apply_one_one, shiftedRow_val_one, Matrix.SpecialLinearGroup.coe_mul,
      coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two, unitRowMatrix]
    ring
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq (gammaSetMatrix (shiftedRow c u l))
    (unitRowMatrix c u * ModularGroup.T ^ l) h0 h1
  exact ⟨n, by rw [hn, mul_smul, mul_smul]⟩

/-- **The Poincaré summand of a shifted row**:
`(c(z+l) + u.val)^{-k} e(m M_{c,u}(z + l))`. -/
theorem poincareSummand_shiftedRow (k : ℤ) (m : ℕ) (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) (z : ℍ) :
    poincareSummand k m (shiftedRow c u l) z
      = ((c : ℂ) * ((z : ℂ) + l) + ((u : ZMod c).val : ℂ)) ^ (-k) *
          expSeed m (unitRowMatrix c u • (ModularGroup.T ^ l • z)) := by
  obtain ⟨n, hn⟩ := exists_gammaSetMatrix_shiftedRow_smul c u l z
  rw [poincareSummand, eisSummand_shiftedRow, hn]
  congr 1
  exact expSeed_T_zpow_smul m n _

/-! ## Negating a row -/

theorem neg_one_zpow_neg (k : ℤ) : ((-1 : ℂ)) ^ (-k) = (-1) ^ k := by
  rcases Int.even_or_odd k with h | h
  · rw [h.neg_one_zpow, h.neg.neg_one_zpow]
  · rw [h.neg_one_zpow, h.neg.neg_one_zpow]

theorem eisSummand_gammaSetNeg (k : ℤ) (v : gammaSet 1 1 0) (z : ℍ) :
    eisSummand k (gammaSetNeg v) z = (-1) ^ k * eisSummand k v z := by
  simp only [eisSummand, gammaSetNeg_val, Pi.neg_apply, Int.cast_neg]
  rw [show -(v.1 0 : ℂ) * z + -(v.1 1 : ℂ) = (-1) * ((v.1 0 : ℂ) * z + v.1 1) by ring, mul_zpow,
    neg_one_zpow_neg]

/-- Negating a row multiplies the Poincaré summand by `(-1)^k`. -/
theorem poincareSummand_gammaSetNeg (k : ℤ) (m : ℕ) (v : gammaSet 1 1 0) (z : ℍ) :
    poincareSummand k m (gammaSetNeg v) z = (-1) ^ k * poincareSummand k m v z := by
  obtain ⟨n, hn⟩ := gammaSetMatrix_gammaSetNeg_smul v z
  rw [poincareSummand, poincareSummand, eisSummand_gammaSetNeg, hn]
  have : Complex.exp (2 * π * I * m * ((ModularGroup.T ^ n • (gammaSetMatrix v • z) : ℍ) : ℂ))
      = Complex.exp (2 * π * I * m * ((gammaSetMatrix v • z : ℍ) : ℂ)) :=
    expSeed_T_zpow_smul m n _
  rw [this]
  ring

end

end GaloisForLFunctions.HTGeometry
