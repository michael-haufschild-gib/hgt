import GaloisForLFunctions.RHTower.KuznetsovGammaZeroCusp
import GaloisForLFunctions.RHTower.Sieve.KloostermanSum

/-!
# Row sums are Kloosterman sums

The reduced rows `(c, d)` (`c ≠ 0`, `0 ≤ d < |c|`, `(c, d) = 1`) with a fixed first entry `c` are in bijection
with the units modulo `|c|` (`fiberEquivUnits`).  For `M = (a b; c d)` we have `ad ≡ 1 (mod c)`, so

`Σ_{d} e((md + na)/c) = S(m, n; |c|)`

(`sum_fiber_rowExp`), and any absolutely summable function of the rows of the form
`e((md + na)/c) Φ(c)` sums to `Σ_{c ≠ 0} S(m, n; |c|) Φ(c)` (`tsum_rowExp_mul`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry RHTower.Sieve

noncomputable section

/-- The phase `e((md + na)/c)` of the row `(c, d)` of `M = (a b; c d)`. -/
def rowExp (m n : ℤ) (p : gammaSet 1 1 0) : ℂ :=
  cexp (2 * Real.pi * Complex.I * (((m : ℝ) * (p.1 1 : ℂ) + (n : ℝ) * (gammaSetMatrix p 0 0 : ℂ)) /
    (p.1 0 : ℂ)))

/-- The first entry of a reduced row. -/
def rowModulus (r : ReducedRow) : ℤ := r.1.1 0

theorem rowModulus_ne_zero (r : ReducedRow) : rowModulus r ≠ 0 := r.2.1

theorem coprime_row (p : gammaSet 1 1 0) : IsCoprime (p.1 0) (p.1 1) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact (EisensteinSeries.gammaSet_one_mem_iff 1 p.1).1 p.2

theorem gammaSetMatrix_mul_row (p : gammaSet 1 1 0) :
    gammaSetMatrix p 0 0 * p.1 1 - gammaSetMatrix p 0 1 * p.1 0 = 1 := by
  have h := (gammaSetMatrix p).det_coe
  rw [Matrix.det_fin_two, gammaSetMatrix_apply_one_zero, gammaSetMatrix_apply_one_one] at h
  exact h

/-- In `ZMod |c|`, the entry `a` is the inverse of `d`. -/
theorem intCast_a_mul_d (p : gammaSet 1 1 0) :
    ((gammaSetMatrix p 0 0 : ℤ) : ZMod (p.1 0).natAbs) * ((p.1 1 : ℤ) : ZMod (p.1 0).natAbs) = 1 := by
  have h := gammaSetMatrix_mul_row p
  have h0 : ((p.1 0 : ℤ) : ZMod (p.1 0).natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Int.natAbs_dvd.2 dvd_rfl
  have := congrArg (fun x : ℤ => (x : ZMod (p.1 0).natAbs)) h
  push_cast at this
  rw [h0, mul_zero, sub_zero] at this
  exact this

/-! ## The fibres of a fixed modulus -/

/-- The reduced row `(c, d)` with `d` the least nonnegative representative of a unit modulo `|c|`. -/
def mkRow (c : ℤ) (hc : c ≠ 0) (u : (ZMod c.natAbs)ˣ) : ReducedRow :=
  ⟨⟨![c, ((u : ZMod c.natAbs).val : ℤ)], by
    rw [EisensteinSeries.gammaSet_one_mem_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.gcd, Int.natAbs_natCast]
    exact (ZMod.val_coe_unit_coprime u).symm⟩, hc, by simp, by
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
    rw [← Int.natCast_natAbs]
    exact_mod_cast ZMod.val_lt _⟩

theorem rowModulus_mkRow (c : ℤ) (hc : c ≠ 0) (u : (ZMod c.natAbs)ˣ) :
    rowModulus (mkRow c hc u) = c := rfl

theorem row_one_toNat_coprime (r : ReducedRow) :
    (r.1.1 1).toNat.Coprime (rowModulus r).natAbs := by
  have h := (EisensteinSeries.gammaSet_one_mem_iff 1 r.1.1).1 r.1.2
  have hd : (r.1.1 1).toNat = (r.1.1 1).natAbs := by
    have := r.2.2.1; omega
  rw [hd]
  exact Nat.Coprime.symm h

/-- **The rows of modulus `c` are the units modulo `|c|`.** -/
def fiberEquivUnits (c : ℤ) (hc : c ≠ 0) : ↑(rowModulus ⁻¹' {c}) ≃ (ZMod c.natAbs)ˣ where
  toFun r := ZMod.unitOfCoprime (r.1.1.1 1).toNat (by
    have h := row_one_toNat_coprime r.1
    rwa [show rowModulus r.1 = c from r.2] at h)
  invFun u := ⟨mkRow c hc u, rfl⟩
  left_inv r := by
    obtain ⟨⟨⟨v, hv⟩, hc0, h0, h1⟩, hr⟩ := r
    change v 0 = c at hr
    subst hr
    refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
    funext i
    fin_cases i
    · rfl
    · simp only [mkRow, ZMod.coe_unitOfCoprime, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      have hlt : (v 1).toNat < (v 0).natAbs := by
        have h1' : v 1 < |v 0| := h1
        have h0' : 0 ≤ v 1 := h0
        rw [Int.abs_eq_natAbs] at h1'
        omega
      rw [ZMod.val_natCast_of_lt hlt, Int.toNat_of_nonneg h0]
  right_inv u := by
    haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
    refine Units.ext ?_
    rw [ZMod.coe_unitOfCoprime]
    show ((((u : ZMod c.natAbs).val : ℤ).toNat : ℕ) : ZMod c.natAbs) = u
    rw [Int.toNat_natCast, ZMod.natCast_zmod_val]

/-! ## Kloosterman sums of the fibres -/

/-- The classical Kloosterman sum `S(m, n; |c|)` of an integral modulus `c` (zero for `c = 0`). -/
def intKloosterman (m n c : ℤ) : ℂ :=
  if h : c = 0 then 0 else
    haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 h⟩
    kloostermanSum c.natAbs (m : ZMod c.natAbs) (n : ZMod c.natAbs)

theorem sum_units_stdAddChar_neg (N : ℕ) [NeZero N] (m n : ZMod N) :
    ∑ u : (ZMod N)ˣ, ZMod.stdAddChar (-(m * (u : ZMod N) + n * ((u⁻¹ : (ZMod N)ˣ) : ZMod N))) =
      kloostermanSum N m n := by
  unfold kloostermanSum kloostermanPhase
  refine Fintype.sum_equiv (Equiv.neg (ZMod N)ˣ) _ _ fun u => ?_
  simp only [Equiv.neg_apply, Units.val_neg, inv_neg]
  ring_nf

theorem rowExp_mkRow (m n c : ℤ) (hc : c ≠ 0) (u : (ZMod c.natAbs)ˣ) :
    haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
    rowExp m n (mkRow c hc u).1 = ZMod.stdAddChar (((Int.sign c : ℤ) : ZMod c.natAbs) *
      ((m : ZMod c.natAbs) * (u : ZMod c.natAbs) +
        (n : ZMod c.natAbs) * ((u⁻¹ : (ZMod c.natAbs)ˣ) : ZMod c.natAbs))) := by
  haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
  set p := (mkRow c hc u).1
  set d : ℤ := p.1 1
  set a : ℤ := gammaSetMatrix p 0 0
  have hp0 : p.1 0 = c := rfl
  have hd : (d : ZMod c.natAbs) = u := by
    show (((u : ZMod c.natAbs).val : ℤ) : ZMod c.natAbs) = u
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have ha : (a : ZMod c.natAbs) = ((u⁻¹ : (ZMod c.natAbs)ˣ) : ZMod c.natAbs) := by
    have h := intCast_a_mul_d p
    rw [hp0] at h
    rw [show ((p.1 1 : ℤ) : ZMod c.natAbs) = u from hd] at h
    calc (a : ZMod c.natAbs) = (a : ZMod c.natAbs) * (u : ZMod c.natAbs) *
          ((u⁻¹ : (ZMod c.natAbs)ˣ) : ZMod c.natAbs) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h, one_mul]
  have hcast : ((Int.sign c * (m * d + n * a) : ℤ) : ZMod c.natAbs) = ((Int.sign c : ℤ) :
      ZMod c.natAbs) * ((m : ZMod c.natAbs) * (u : ZMod c.natAbs) +
        (n : ZMod c.natAbs) * ((u⁻¹ : (ZMod c.natAbs)ˣ) : ZMod c.natAbs)) := by
    push_cast; rw [hd, ha]
  rw [← hcast, ZMod.stdAddChar_coe, rowExp]
  congr 1
  rw [hp0]
  have hN : (c.natAbs : ℂ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.2 hc
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hab : ((c.natAbs : ℕ) : ℂ) = -(c : ℂ) := by
      rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg.le, Int.cast_neg]
    rw [Int.sign_eq_neg_one_of_neg hneg, hab]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast
    field_simp
    ring
  · have hab : ((c.natAbs : ℕ) : ℂ) = (c : ℂ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le]
    rw [Int.sign_eq_one_of_pos hpos, hab]
    push_cast
    ring

theorem sum_rowExp_fiber (m n c : ℤ) (hc : c ≠ 0) :
    ∑' b : ↑(rowModulus ⁻¹' {c}), rowExp m n b.1.1 = intKloosterman m n c := by
  haveI : NeZero c.natAbs := ⟨Int.natAbs_ne_zero.2 hc⟩
  rw [← (fiberEquivUnits c hc).symm.tsum_eq, tsum_fintype, intKloosterman, dif_neg hc]
  have hpt : ∀ u : (ZMod c.natAbs)ˣ, rowExp m n ((fiberEquivUnits c hc).symm u).1.1 =
      ZMod.stdAddChar (((Int.sign c : ℤ) : ZMod c.natAbs) *
        ((m : ZMod c.natAbs) * (u : ZMod c.natAbs) +
          (n : ZMod c.natAbs) * ((u⁻¹ : (ZMod c.natAbs)ˣ) : ZMod c.natAbs))) :=
    fun u => rowExp_mkRow m n c hc u
  simp_rw [hpt]
  rcases lt_or_gt_of_ne hc with h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
    exact sum_units_stdAddChar_neg _ _ _
  · rw [Int.sign_eq_one_of_pos h]; simp only [Int.cast_one, one_mul]; rfl

/-- **A summable row series of the form `e((md+na)/c) Φ(c)` is a series of Kloosterman sums.** -/
theorem tsum_rowExp_mul (m n : ℤ) (Φ : ℤ → ℂ)
    (hsum : Summable fun r : ReducedRow => rowExp m n r.1 * Φ (rowModulus r)) :
    ∑' r : ReducedRow, rowExp m n r.1 * Φ (rowModulus r) =
      ∑' c : ℤ, intKloosterman m n c * Φ c := by
  rw [← (hsum.hasSum.tsum_fiberwise rowModulus).tsum_eq]
  refine tsum_congr fun c => ?_
  by_cases hc : c = 0
  · subst hc
    haveI : IsEmpty ↑(rowModulus ⁻¹' {0}) := ⟨fun b => rowModulus_ne_zero b.1 b.2⟩
    rw [tsum_empty, intKloosterman, dif_pos rfl, zero_mul]
  · have hpt : ∀ b : ↑(rowModulus ⁻¹' {c}), rowExp m n b.1.1 * Φ (rowModulus b.1) =
        rowExp m n b.1.1 * Φ c := fun b => by rw [show rowModulus b.1 = c from b.2]
    rw [tsum_congr hpt, tsum_mul_right, sum_rowExp_fiber m n c hc]

end

end GaloisForLFunctions.RHTower.DeckPointPair
