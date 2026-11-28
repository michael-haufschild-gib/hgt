import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicRadicalContraction
import GaloisForLFunctions.WindowedLandauTheory.SatakeDualWeyl.AdelicIwasawaHecke.Cartan

/-! The integral Cartan decomposition for p-adic general linear
matrices follows from the valuation-ring Smith normal form. -/

noncomputable section

open Matrix WithZero
open WindowedLandauTheory.UG WindowedLandauTheory.UG.P

namespace GlobalTheory.GLp

variable {p m : ℕ} [Fact p.Prime]

private theorem padic_mulValuation_p : Padic.mulValuation (p := p) (p : ℚ_[p]) = exp (-1 : ℤ) := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  classical
  change (if (p : ℚ_[p]) = 0 then 0 else exp (-(p : ℚ_[p]).valuation)) = _
  rw [if_neg hp, Padic.valuation_p]

private theorem padic_integer_iff (x : ℚ_[p]) :
    x ∈ PadicInt.subring p ↔ Padic.mulValuation x ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  classical
  rw [PadicInt.mem_subring_iff, Padic.norm_le_one_iff_val_nonneg]
  change _ ↔ (if x = 0 then 0 else exp (-x.valuation)) ≤ exp (0 : ℤ)
  rw [if_neg hx, exp_le_exp, neg_nonpos]

private theorem exists_integer_clear_matrix (M : Matrix (Fin m) (Fin m) ℚ_[p]) :
    ∃ c : ℤ_[p], c ≠ 0 ∧ (c : ℚ_[p]) • M ∈
      (RingHom.mapMatrix (m := Fin m) (PadicInt.subring p).subtype).range := by
  let N := Finset.univ.sup (fun ij : Fin m × Fin m => (-(M ij.1 ij.2).valuation).toNat)
  let c : ℤ_[p] := (p : ℤ_[p]) ^ N
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hc : (c : ℚ_[p]) = (p : ℚ_[p]) ^ N := by simp [c]
  have hc0 : (c : ℚ_[p]) ≠ 0 := hc ▸ pow_ne_zero _ hp
  have hInt (i j : Fin m) : (c : ℚ_[p]) * M i j ∈ PadicInt.subring p := by
    rw [PadicInt.mem_subring_iff, Padic.norm_le_one_iff_val_nonneg]
    rcases eq_or_ne (M i j) 0 with hz | hz
    · simp [hz]
    have hN : (-(M i j).valuation).toNat ≤ N :=
      Finset.le_sup (f := fun ij : Fin m × Fin m => (-(M ij.1 ij.2).valuation).toNat)
        (Finset.mem_univ (i, j))
    rw [Padic.valuation_mul hc0 hz, hc, Padic.valuation_pow, Padic.valuation_p, mul_one]
    omega
  exact ⟨c, fun h => hc0 (by rw [h, PadicInt.coe_zero]), ⟨fun i j => ⟨_, hInt i j⟩, Matrix.ext fun _ _ => rfl⟩⟩

theorem exists_integral_cartan (x : GL (Fin m) ℚ_[p]) :
    ∃ (a : Fin m → ℤ) (k l : GL (Fin m) ℤ_[p]), Antitone a ∧
      x = integralInclusion p (Fin m) k * uniformizerTorus (p := p) a * integralInclusion p (Fin m) l := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hr (y : ℚ_[p]) (hy : y ≠ 0) : ∃ j : ℤ,
      Padic.mulValuation y = Padic.mulValuation (p : ℚ_[p]) ^ j := by
    refine ⟨y.valuation, ?_⟩
    rw [padic_mulValuation_p, ← WithZero.exp_zsmul]
    classical
    change (if y = 0 then 0 else exp (-y.valuation)) = _
    rw [if_neg hy]
    simp
  letI : IsPrincipalIdealRing (PadicInt.subring p) := inferInstanceAs (IsPrincipalIdealRing ℤ_[p])
  obtain ⟨c, hc, hcx⟩ := exists_integer_clear_matrix x.val
  obtain ⟨a, ha, k, ⟨k', rfl⟩, l, ⟨l', rfl⟩, he⟩ :=
    cartan_decomp_gen (PadicInt.subring p) (Padic.mulValuation (p := p)) padic_integer_iff
      (p : ℚ_[p]) hp hr x c hc hcx
  exact ⟨a, k', l', ha, Units.ext he⟩

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.exists_integral_cartan
