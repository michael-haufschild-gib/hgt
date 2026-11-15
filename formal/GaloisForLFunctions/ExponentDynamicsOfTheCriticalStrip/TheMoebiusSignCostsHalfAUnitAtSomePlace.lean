import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheMoebiusSignOfAGaussMonomialIsAHalfIntegralStickelbergerDefect

/-!
# The Möbius sign costs half a unit at some place

The Galois conjugates of a Gauss monomial `∏ g(χ)` over `𝔽_p` are the monomials of the conjugate
lists `χ ↦ χ^t`, `t ∈ (ℤ/(p − 1))^×` (`conjList`).

* **The defects average to zero** (`sum_stickelbergerDefect_conjList_eq_zero`): for `χ = ω^n` the
  exponent of `χ^t` is `tn mod (p − 1)`, and the exponents at `t` and `−t` add to `p − 1`; so the
  `p`-adic content of a monomial of `r` nontrivial characters averages to its weight `r/2`.
* **Conjugation keeps the Möbius sign** (`isMoebiusSignedTuple_conjList`): `t` is odd and
  `(∏ L)² = 1`, so `∏ L^t = ∏ L`.
* **The price of the sign** (`exists_conjList_half_le_stickelbergerDefect`): every conjugate of a
  Möbius-signed monomial has half-integral defect (`isMoebiusSignedTuple_iff_defect`), and the
  defects average to zero; so at some place above `p` the weight exceeds the `p`-content by at
  least `½`.

* **Frames** (`half_lt_stickelbergerPrice_div`): pricing a monomial at the period `k` by `k` times
  its largest conjugate defect gives `c ≥ k/2 > (k − 1)/2`: no such frame is centred.

For one character of order `m` the largest defect over its conjugates is `½ − 1/m` (the extremal
character, `norm_gaussSum_extremalChar_pow`), the price per unit of a completed factor in the Gauss
pairings. For a Möbius-signed monomial taken as a whole the sign alone forces a price of at least
`½` at some place: no Möbius-signed abelian monomial reaches `ζ` through powers of `p` alone.
-/

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger

open GaloisForLFunctions.FamilyContinuationTheory (IsMoebiusSignedTuple)

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] neZero_p

theorem neZero_p_sub_one : NeZero (p - 1) := ⟨by have := hp.out.two_le; omega⟩

attribute [local instance] neZero_p_sub_one

/-- The conjugate list `χ ↦ χ^t`. -/
noncomputable def conjList (t : (ZMod (p - 1))ˣ) (L : List (MulChar (ZMod p) (PadicAlgCl p))) :
    List (MulChar (ZMod p) (PadicAlgCl p)) :=
  L.map fun χ => χ ^ (t : ZMod (p - 1)).val

/-- The Teichmüller exponent is the exponent in `[1, p − 1]`. -/
theorem teichExp_eq {χ : MulChar (ZMod p) (PadicAlgCl p)} {e : ℕ} (he1 : 1 ≤ e) (heN : e ≤ p - 1)
    (h : χ = teichCharK p ^ e) : teichExp p χ = e := by
  obtain ⟨h1, h2, h3⟩ := teichExp_spec p χ
  have h4 : teichCharK p ^ teichExp p χ = teichCharK p ^ e := h3.symm.trans h
  rw [pow_inj_mod, orderOf_teichCharK] at h4
  have key : ∀ a, 1 ≤ a → a ≤ p - 1 → a % (p - 1) = if a = p - 1 then 0 else a := fun a ha1 ha2 => by
    split_ifs with ha
    · rw [ha, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (lt_of_le_of_ne ha2 ha)
  rw [key _ h1 h2, key e he1 heN] at h4
  split_ifs at h4 <;> omega

theorem teichExp_lt_of_ne_one {χ : MulChar (ZMod p) (PadicAlgCl p)} (hχ : χ ≠ 1) :
    teichExp p χ < p - 1 := by
  obtain ⟨h1, h2, h3⟩ := teichExp_spec p χ
  refine lt_of_le_of_ne h2 fun h => hχ ?_
  rw [h3, h, teichCharK_pow_sub_one]

/-- The exponent of `χ^t` is `t·n mod (p − 1)`, a nonzero residue. -/
theorem teichExp_pow_val {χ : MulChar (ZMod p) (PadicAlgCl p)} (hχ : χ ≠ 1) (t : (ZMod (p - 1))ˣ) :
    teichExp p (χ ^ (t : ZMod (p - 1)).val) =
        ((t : ZMod (p - 1)) * (teichExp p χ : ZMod (p - 1))).val ∧
      ((t : ZMod (p - 1)) * (teichExp p χ : ZMod (p - 1))) ≠ 0 := by
  obtain ⟨h1, -, h3⟩ := teichExp_spec p χ
  have hlt := teichExp_lt_of_ne_one p hχ
  have hn0 : (teichExp p χ : ZMod (p - 1)) ≠ 0 := by
    intro h0
    have := congrArg ZMod.val h0
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_zero] at this
    omega
  have hy : (t : ZMod (p - 1)) * (teichExp p χ : ZMod (p - 1)) ≠ 0 :=
    fun h0 => hn0 ((Units.mul_right_eq_zero t).1 h0)
  refine ⟨teichExp_eq p ?_ (ZMod.val_lt _).le ?_, hy⟩
  · rcases Nat.eq_zero_or_pos ((t : ZMod (p - 1)) * (teichExp p χ : ZMod (p - 1))).val with h0 | h0
    · exact absurd ((ZMod.val_eq_zero _).1 h0) hy
    · exact h0
  · have hmod := pow_mod_orderOf (teichCharK p) ((t : ZMod (p - 1)).val * teichExp p χ)
    rw [orderOf_teichCharK] at hmod
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, hmod]
    conv_lhs => rw [h3]
    rw [← pow_mul, mul_comm]

/-- **The Stickelberger distribution.** For `a ≠ 0` in `ℤ/(p − 1)` the residues `t a` over the
units `t` add to half of `(p − 1)` times their number. -/
theorem sum_val_unit_mul {a : ZMod (p - 1)} (ha : a ≠ 0) :
    2 * ∑ t : (ZMod (p - 1))ˣ, ((t : ZMod (p - 1)) * a).val =
      Fintype.card (ZMod (p - 1))ˣ * (p - 1) := by
  have hpair : ∀ t : (ZMod (p - 1))ˣ,
      ((t : ZMod (p - 1)) * a).val + (((-t : (ZMod (p - 1))ˣ) : ZMod (p - 1)) * a).val = p - 1 := by
    intro t
    have hy : (t : ZMod (p - 1)) * a ≠ 0 := fun h0 => ha ((Units.mul_right_eq_zero t).1 h0)
    rw [Units.val_neg, neg_mul, ZMod.neg_val, if_neg hy]
    have := ZMod.val_lt ((t : ZMod (p - 1)) * a)
    omega
  have hsym : ∑ t : (ZMod (p - 1))ˣ, (((-t : (ZMod (p - 1))ˣ) : ZMod (p - 1)) * a).val =
      ∑ t : (ZMod (p - 1))ˣ, ((t : ZMod (p - 1)) * a).val :=
    Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl
  have hsum := Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => hpair t
  rw [Finset.sum_add_distrib, hsym, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

variable {p}

theorem prod_conjList (t : (ZMod (p - 1))ˣ) (L : List (MulChar (ZMod p) (PadicAlgCl p))) :
    (conjList p t L).prod = L.prod ^ (t : ZMod (p - 1)).val := by
  induction L with
  | nil => simp [conjList]
  | cons χ L ih =>
    simp only [conjList, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, mul_pow]

/-- **Conjugation keeps the Möbius sign.** -/
theorem isMoebiusSignedTuple_conjList (hp2 : p ≠ 2) {L : List (MulChar (ZMod p) (PadicAlgCl p))}
    (hM : IsMoebiusSignedTuple L) (t : (ZMod (p - 1))ˣ) : IsMoebiusSignedTuple (conjList p t L) := by
  set m := (t : ZMod (p - 1)).val with hm
  have hcop : m.Coprime (p - 1) := ZMod.val_coe_unit_coprime t
  have hodd : Odd m := by
    rw [Nat.odd_iff]
    by_contra h
    have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    have h2N : 2 ∣ p - 1 := (hp.out.even_sub_one hp2).two_dvd
    have := Nat.dvd_gcd h2m h2N
    rw [hcop.gcd_eq_one] at this
    omega
  have hprod : (conjList p t L).prod = L.prod := by
    obtain ⟨k, hk⟩ := hodd
    rw [prod_conjList, ← hm, hk, pow_succ, pow_mul, hM.prod_sq_eq_one, one_pow, one_mul]
  refine ⟨?_, fun x hx => ?_, ?_, ?_⟩
  · simpa [conjList] using hM.nonempty
  · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 hx
    have hc : (orderOf χ).Coprime m :=
      (Nat.Coprime.coprime_dvd_right (orderOf_dvd_sub_one p χ) hcop).symm
    rw [Nat.Coprime.orderOf_pow hc]
    exact hM.two_le_order χ hχ
  · rw [hprod]
    exact hM.prod_sq_eq_one
  · rw [hprod, conjList, List.length_map]
    exact hM.parity

/-- The defect of a conjugate list, factor by factor. -/
theorem stickelbergerDefect_conjList {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (t : (ZMod (p - 1))ˣ) {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hL : ∀ χ ∈ L, χ ≠ 1) :
    stickelbergerDefect p hζ (conjList p t L) =
      (L.map fun χ => (((t : ZMod (p - 1)) * (teichExp p χ : ZMod (p - 1))).val : ℝ) /
        ((p - 1 : ℕ) : ℝ) - 1 / 2).sum := by
  rw [stickelbergerDefect_eq]
  induction L with
  | nil => simp [conjList]
  | cons χ L ih =>
    have h1 := (teichExp_pow_val p (hL χ List.mem_cons_self) t).1
    have ih' := ih fun ψ hψ => hL ψ (List.mem_cons_of_mem _ hψ)
    simp only [conjList, List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
    rw [h1, ← ih']
    push_cast
    ring

/-- **The defects of the conjugates average to zero.** -/
theorem sum_stickelbergerDefect_conjList_eq_zero {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hL : ∀ χ ∈ L, χ ≠ 1) :
    ∑ t : (ZMod (p - 1))ˣ, stickelbergerDefect p hζ (conjList p t L) = 0 := by
  have hN : ((p - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  simp_rw [stickelbergerDefect_conjList hζ _ hL]
  induction L with
  | nil => simp
  | cons χ L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih fun ψ hψ => hL ψ (List.mem_cons_of_mem _ hψ), add_zero,
      Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 := sum_val_unit_mul p (teichExp_pow_val p (hL χ List.mem_cons_self) 1).2
    simp only [Units.val_one, one_mul] at h2
    have h3 : (2 : ℝ) * ∑ t : (ZMod (p - 1))ˣ,
        (((t : ZMod (p - 1)) * (teichExp p χ : ZMod (p - 1))).val : ℝ) =
        (Fintype.card (ZMod (p - 1))ˣ : ℝ) * ((p - 1 : ℕ) : ℝ) := by
      have := sum_val_unit_mul p (a := (teichExp p χ : ZMod (p - 1))) (by
        have := (teichExp_pow_val p (hL χ List.mem_cons_self) 1).2
        simpa using this)
      exact_mod_cast this
    field_simp
    linarith

/-- **The Möbius sign costs half a unit at some place.** A Möbius-signed monomial has a conjugate of
defect at least `½`. -/
theorem exists_conjList_half_le_stickelbergerDefect {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hM : IsMoebiusSignedTuple L) :
    ∃ t : (ZMod (p - 1))ˣ, 1 / 2 ≤ stickelbergerDefect p hζ (conjList p t L) := by
  have hL : ∀ χ ∈ L, χ ≠ 1 := fun χ hχ h1 => by
    have := hM.two_le_order χ hχ
    rw [h1, orderOf_one] at this
    omega
  have hp2 : p ≠ 2 := by
    intro h2
    obtain ⟨χ, hχ⟩ := List.exists_mem_of_ne_nil L hM.nonempty
    have := teichExp_lt_of_ne_one p (hL χ hχ)
    have := (teichExp_spec p χ).1
    omega
  by_contra hcon
  push Not at hcon
  have hle : ∀ t : (ZMod (p - 1))ˣ, stickelbergerDefect p hζ (conjList p t L) ≤ -(1 / 2) := by
    intro t
    have hMt := isMoebiusSignedTuple_conjList hp2 hM t
    have hLt : ∀ χ ∈ conjList p t L, χ ≠ 1 := fun χ hχ h1 => by
      have := hMt.two_le_order χ hχ
      rw [h1, orderOf_one] at this
      omega
    obtain ⟨j, hj⟩ := (isMoebiusSignedTuple_iff_defect hζ hMt.nonempty hLt hMt.prod_sq_eq_one).1 hMt
    have h1 := hcon t
    rw [hj] at h1 ⊢
    have : j < 0 := by
      have : (j : ℝ) < 0 := by linarith
      exact_mod_cast this
    have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    linarith
  have hsum := sum_stickelbergerDefect_conjList_eq_zero hζ hL
  have hcard : (0 : ℝ) < Fintype.card (ZMod (p - 1))ˣ := by exact_mod_cast Fintype.card_pos
  have := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hle t
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  nlinarith

/-! ### Frames priced by the defect -/

/-- The **Stickelberger price** of a monomial at the period `k`: `k` times the largest defect of its
Galois conjugates, the weight of `G^k` that reaches `ζ` through no power of `p` at the worst place. -/
noncomputable def stickelbergerPrice {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (k : ℝ)
    (L : List (MulChar (ZMod p) (PadicAlgCl p))) : ℝ :=
  k * Finset.univ.sup' Finset.univ_nonempty fun t : (ZMod (p - 1))ˣ =>
    stickelbergerDefect p hζ (conjList p t L)

theorem half_mul_le_stickelbergerPrice {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) {k : ℝ}
    (hk : 0 ≤ k) {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hM : IsMoebiusSignedTuple L) :
    k / 2 ≤ stickelbergerPrice hζ k L := by
  obtain ⟨t, ht⟩ := exists_conjList_half_le_stickelbergerDefect hζ hM
  have hsup : 1 / 2 ≤ Finset.univ.sup' Finset.univ_nonempty fun t : (ZMod (p - 1))ˣ =>
      stickelbergerDefect p hζ (conjList p t L) :=
    ht.trans (Finset.le_sup' (fun t : (ZMod (p - 1))ˣ => stickelbergerDefect p hζ (conjList p t L))
      (Finset.mem_univ t))
  unfold stickelbergerPrice
  nlinarith

/-- **No frame of a Möbius-signed abelian monomial priced by its defect is centred:** the centre
`c/(k − 1)` of the frame `(c, k)` with `c` the Stickelberger price exceeds `½`. -/
theorem half_lt_stickelbergerPrice_div {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) {k : ℝ}
    (hk : 1 < k) {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hM : IsMoebiusSignedTuple L) :
    1 / 2 < stickelbergerPrice hζ k L / (k - 1) := by
  rw [lt_div_iff₀ (by linarith)]
  have := half_mul_le_stickelbergerPrice hζ (by linarith) hM
  linarith

#print axioms sum_stickelbergerDefect_conjList_eq_zero
#print axioms exists_conjList_half_le_stickelbergerDefect
#print axioms half_lt_stickelbergerPrice_div

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger
