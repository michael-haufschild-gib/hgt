import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.StatementT

/-! Raising to the primary part of a torsion exponent kills the
component discarded by the prime-to-part projection. Equal
projections therefore constrain the ratio to a prime-power root. -/

noncomputable section

namespace WindowedLandauTheory.CyclotomicNorms

theorem primeToPart_pow_ordProj {M : Type*} [Monoid M] {l n : ℕ}
    (hl : l.Prime) (hn : n ≠ 0) (x : M) (hx : x ^ n = 1) :
    primeToPart l x ^ (l ^ n.factorization l) = x ^ (l ^ n.factorization l) := by
  let a := l ^ (orderOf x).factorization l
  let b := orderOf x / a
  have ho : orderOf x ≠ 0 := (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hx⟩).orderOf_pos.ne'
  have hab : a * b = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hba : b * a = orderOf x := (mul_comm b a).trans hab
  have hc : a.Coprime b := (Nat.coprime_ordCompl hl ho).pow_left _
  have hmod : a * ((a : ZMod b)⁻¹).val ≡ 1 [MOD b] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
      simpa only [Nat.cast_mul, Nat.cast_one] using ZMod.mul_val_inv hc)
  have he : a * ((a : ZMod b)⁻¹).val * a ≡ a [MOD orderOf x] := by
    simpa only [one_mul, hba] using hmod.mul_right' a
  have hpow : primeToPart l x ^ a = x ^ a := by
    change (x ^ (a * ((a : ZMod b)⁻¹).val)) ^ a = x ^ a
    rw [← pow_mul, ← pow_mod_orderOf x (a * ((a : ZMod b)⁻¹).val * a),
      ← pow_mod_orderOf x a]
    exact congrArg (fun k => x ^ k) he
  obtain ⟨k, hk⟩ := Nat.ordProj_dvd_ordProj_of_dvd hn (orderOf_dvd_of_pow_eq_one hx) l
  change l ^ n.factorization l = a * k at hk
  rw [hk, pow_mul, pow_mul, hpow]

theorem div_pow_ordProj_max_eq_one {M : Type*} [CommGroupWithZero M]
    {l n n' : ℕ} (hl : l.Prime) (hn : n ≠ 0) (hn' : n' ≠ 0) {x y : M}
    (hx : x ^ n = 1) (hy : y ^ n' = 1) (hy0 : y ≠ 0)
    (he : primeToPart l x = primeToPart l y) :
    (x / y) ^ (l ^ max (n.factorization l) (n'.factorization l)) = 1 := by
  let e := max (n.factorization l) (n'.factorization l)
  have hpow {z : M} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) (hle : m.factorization l ≤ e) :
      primeToPart l z ^ (l ^ e) = z ^ (l ^ e) := by
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hle
    rw [hb, pow_add, pow_mul, pow_mul, primeToPart_pow_ordProj hl hm z hz]
  have hc : x ^ (l ^ e) = y ^ (l ^ e) :=
    (hpow hn hx (le_max_left _ _)).symm.trans
      ((congrArg (fun t => t ^ (l ^ e)) he).trans (hpow hn' hy (le_max_right _ _)))
  rw [div_pow, hc, div_self (pow_ne_zero _ hy0)]

end WindowedLandauTheory.CyclotomicNorms

#print axioms WindowedLandauTheory.CyclotomicNorms.div_pow_ordProj_max_eq_one
