import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.EqZeroOfNegEq

/-! Cyclotomic automorphisms act on quadratic Gauss roots by the Jacobi character. -/

open NumberField IntermediateField Ideal

noncomputable section

namespace WindowedLandauTheory.HC

open WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition

namespace D7

def sgnN {p N : ℕ} (hp : p.Prime) (h : p ∣ N) : (ZMod N)ˣ →* ℤˣ :=
  haveI := Fact.mk hp
  (quadraticChar (ZMod p)).toUnitHom.comp (ZMod.unitsMap h)

theorem unitsMap_val {M N : ℕ} [NeZero N] (h : M ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M) = (((u : ZMod N).val : ℕ) : ZMod M) := by
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (u : ZMod N) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem unitsMap_neg_one {M N : ℕ} (h : M ∣ N) : ZMod.unitsMap h (-1) = -1 := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map]
  show ZMod.castHom h (ZMod M) (-1) = -1
  rw [map_neg, map_one]

theorem sgnN_val {p N : ℕ} [NeZero N] (hp : p.Prime) (h : p ∣ N) (u : (ZMod N)ˣ) :
    ((sgnN hp h u : ℤˣ) : ℤ) = jacobiSym (((u : ZMod N).val : ℕ) : ℤ) p := by
  have := Fact.mk hp
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ← unitsMap_val h u]
  exact MulChar.coe_toUnitHom _ _

theorem sgnN_neg_one {p N : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) : sgnN hp h (-1) = -1 := by
  have := Fact.mk hp
  apply Units.ext
  have h1 : ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) = -1 := by
    rw [unitsMap_neg_one]; rfl
  have h2 : ((sgnN hp h (-1) : ℤˣ) : ℤ) = quadraticChar (ZMod p) ((ZMod.unitsMap h (-1) : (ZMod p)ˣ) : ZMod p) :=
    MulChar.coe_toUnitHom _ _
  rw [h2, h1, quadraticChar_neg_one (Cond.ringChar_ne_two hp4), ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]
  rfl

theorem gs_act {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime] {x : K} (hx : x ^ p = 1) (σ : K →+* K)
    (v : ℕ) (hσ : σ x = x ^ v) (hv : Nat.Coprime v p) :
    σ (Cond.gs p hx) = ((jacobiSym (v : ℤ) p : ℤ) : K) * Cond.gs p hx := by
  set w : (ZMod p)ˣ := ZMod.unitOfCoprime v hv with hw
  have hwv : (w : ZMod p) = (v : ZMod p) := ZMod.coe_unitOfCoprime v hv
  have hψ : ∀ a : ZMod p, σ (AddChar.zmodChar p hx a) = AddChar.zmodChar p hx ((w : ZMod p) * a) := by
    intro a
    rw [AddChar.zmodChar_apply, map_pow, hσ, ← pow_mul]
    have : (w : ZMod p) * a = (((v * a.val : ℕ)) : ZMod p) := by
      push_cast; rw [hwv, ZMod.natCast_zmod_val]
    rw [this, AddChar.zmodChar_apply']
  have hχ : ∀ a : ZMod p, σ (Cond.chi p K a) = Cond.chi p K a := by
    intro a; simp [Cond.chi, MulChar.ringHomComp_apply]
  have h1 : σ (Cond.gs p hx) = gaussSum (Cond.chi p K) (AddChar.mulShift (AddChar.zmodChar p hx) (w : ZMod p)) := by
    simp only [Cond.gs, gaussSum, map_sum, map_mul, hψ, hχ, AddChar.mulShift_apply]
  have h2 := gaussSum_mulShift (Cond.chi p K) (AddChar.zmodChar p hx) w
  have h3 : Cond.chi p K (w : ZMod p) = ((jacobiSym (v : ℤ) p : ℤ) : K) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, hwv]
    rfl
  have h4 : jacobiSym (v : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (by simpa using hv)
  have h5 : ((jacobiSym (v : ℤ) p : ℤ) : K) ^ 2 = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) h4
  rw [h3, ← h1] at h2
  have h6 : Cond.gs p hx = ((jacobiSym (v : ℤ) p : ℤ) : K) * σ (Cond.gs p hx) := h2.symm
  linear_combination (-σ (Cond.gs p hx)) * h5 - ((jacobiSym (v : ℤ) p : ℤ) : K) * h6

theorem sqrt_act {p N : ℕ} [NeZero N] (hp : p.Prime) (hp4 : p % 4 = 3) (h : p ∣ N) (u : (ZMod N)ˣ)
    (τ : Cond.Cyc N ≃ₐ[ℚ] Cond.Cyc N) (hτ : ∀ w : Cond.Cyc N, w ^ N = 1 → τ w = w ^ (u : ZMod N).val)
    (y : Cond.Cyc N) (hy : y ^ 2 = -(p : Cond.Cyc N)) :
    τ y = (((sgnN hp h u : ℤˣ) : ℤ) : Cond.Cyc N) * y := by
  have := Fact.mk hp
  have hx := Cond.prim_pow (N := N) h
  have hxN : (Cond.z N ^ (N / p)) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, (Cond.z_spec N).pow_eq_one, one_pow]
  have hg := gs_act hx.pow_eq_one (τ : Cond.Cyc N →+* Cond.Cyc N) _ (hτ _ hxN)
    ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h)
  have hg' : τ (Cond.gs p hx.pow_eq_one) = _ := hg
  rw [sgnN_val]
  have hsq : y ^ 2 = Cond.gs p hx.pow_eq_one ^ 2 := by rw [hy, Cond.gs_sq hp4 hx]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · rw [h1, hg']
  · rw [h1, map_neg, hg']; ring

end D7

end WindowedLandauTheory.HC
