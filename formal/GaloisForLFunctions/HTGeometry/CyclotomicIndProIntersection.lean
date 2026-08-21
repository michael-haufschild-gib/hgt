import GaloisForLFunctions.HTGeometry.MonoidAlgebraGroupLike
import GaloisForLFunctions.HTGeometry.ProKummerHolonomyCapacity

/-!
# Cyclotomic ind–pro intersection

Finite root groups carry two opposite depth laws: formation inclusion keeps an element fixed, while
history reduction raises it to the refinement degree.  A pro-history that is realized by one
element born at a finite depth is therefore trivial, and the only group-like landing in a complex
root-group algebra is the unit.  The integral charge histories give the sharp instance: only the
zero charge is ind-formed, while the whole tower reconstructs the charge exactly.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Pro-histories -/

/-- A coherent history of roots of unity: a root of order dividing `n` at each depth `n ≥ 1`,
compatible with the reduction maps `z ↦ z ^ (m / n)`. -/
structure ProHistory where
  /-- The depth-`n` root. -/
  toFun : ℕ → ℂˣ
  /-- Each entry is a root of unity of the corresponding depth. -/
  pow_eq_one : ∀ n : ℕ, 1 ≤ n → toFun n ^ n = 1
  /-- Reduction from a multiple depth recovers the entry. -/
  coherent : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ∣ m → toFun m ^ (m / n) = toFun n

/-- A pro-history is ind-formed when one element born at a finite depth represents it on the
cofinal tail of multiples of that depth. -/
def ProHistory.IsIndFormed (z : ProHistory) : Prop :=
  ∃ d : ℕ, 1 ≤ d ∧ ∃ ξ : ℂˣ, ∀ m : ℕ, 1 ≤ m → d ∣ m → z.toFun m = ξ

/-- An idempotent unit is the identity. -/
theorem eq_one_of_sq_eq_self {ξ : ℂˣ} (h : ξ ^ 2 = ξ) : ξ = 1 := by
  have : ξ * ξ = ξ * 1 := by rw [mul_one, ← sq, h]
  exact mul_left_cancel this

/-- **Theorem 2.1 — trivial ind–pro intersection.**  A pro-history is ind-formed exactly when it is
the identity history; one birth depth and its double already force it. -/
theorem ProHistory.isIndFormed_iff (z : ProHistory) :
    z.IsIndFormed ↔ ∀ n : ℕ, 1 ≤ n → z.toFun n = 1 := by
  constructor
  · rintro ⟨d, hd, ξ, hξ⟩
    have hzd : z.toFun d = ξ := hξ d hd dvd_rfl
    have hz2d : z.toFun (2 * d) = ξ := hξ (2 * d) (by omega) ⟨2, by ring⟩
    have hdiv : (2 * d) / d = 2 := by
      rw [Nat.mul_div_cancel _ (by omega : 0 < d)]
    have hsq : ξ ^ 2 = ξ := by
      have := z.coherent d (2 * d) hd (by omega) ⟨2, by ring⟩
      rw [hdiv, hz2d, hzd] at this
      exact this
    have hξ1 : ξ = 1 := eq_one_of_sq_eq_self hsq
    intro n hn
    set m : ℕ := Nat.lcm n d with hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.lcm_ne_zero (by omega) (by omega))
    have hnm : n ∣ m := Nat.dvd_lcm_left n d
    have hdm : d ∣ m := Nat.dvd_lcm_right n d
    have hzm : z.toFun m = 1 := by rw [hξ (m) hm1 hdm, hξ1]
    have := z.coherent n m hn hm1 hnm
    rw [hzm, one_pow] at this
    exact this.symm
  · intro h
    exact ⟨1, le_rfl, 1, fun m hm _ => h m hm⟩

/-! ## Charge histories -/

/-- The depth-`n` Kummer holonomy of an integral charge as a unit. -/
def chargeUnit (n : ℕ) (q : ℤ) : ℂˣ :=
  Units.mk0 (kummerHolonomy n q) (kummerHolonomy_ne_zero n q)

@[simp] theorem chargeUnit_coe (n : ℕ) (q : ℤ) :
    ((chargeUnit n q : ℂˣ) : ℂ) = kummerHolonomy n q := rfl

theorem chargeUnit_pow (n : ℕ) (q : ℤ) (k : ℕ) :
    (chargeUnit n q) ^ k = chargeUnit n (q * k) := by
  refine Units.ext ?_
  push_cast
  rw [chargeUnit_coe, chargeUnit_coe, ← kummerHolonomy_pow]

theorem chargeUnit_eq_one_iff {n : ℕ} (hn : 1 ≤ n) (q : ℤ) :
    chargeUnit n q = 1 ↔ (n : ℤ) ∣ q := by
  rw [← kummerHolonomy_eq_one_iff (by omega : n ≠ 0) q]
  constructor
  · intro h
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simpa using this
  · intro h
    exact Units.ext (by simpa using h)

/-- The integral charge history (IPT.6). -/
def chargeHistory (q : ℤ) : ProHistory where
  toFun n := chargeUnit n q
  pow_eq_one n hn := by
    rw [chargeUnit_pow]
    refine (chargeUnit_eq_one_iff hn _).2 ?_
    exact ⟨q, by ring⟩
  coherent n m hn hm hnm := by
    obtain ⟨k, rfl⟩ := hnm
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · omega
      · exact hk
    have hdiv : (n * k) / n = k := Nat.mul_div_cancel_left k (by omega)
    rw [hdiv, chargeUnit_pow]
    refine Units.ext ?_
    rw [chargeUnit_coe, chargeUnit_coe, kummerHolonomy, kummerHolonomy]
    have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hk0 : ((k : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    congr 2
    push_cast
    field_simp

@[simp] theorem chargeHistory_toFun (q : ℤ) (n : ℕ) :
    (chargeHistory q).toFun n = chargeUnit n q := rfl

/-- **Corollary 3.1 — integral charge selection.**  Only the zero charge has an ind-formed
history. -/
theorem chargeHistory_isIndFormed_iff (q : ℤ) : (chargeHistory q).IsIndFormed ↔ q = 0 := by
  rw [ProHistory.isIndFormed_iff]
  constructor
  · intro h
    set n : ℕ := q.natAbs + 1 with hn
    have hdvd : (n : ℤ) ∣ q := (chargeUnit_eq_one_iff (by omega) q).1 (by
      simpa using h n (by omega))
    by_contra hq
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hq
    simp only [Int.natAbs_natCast] at hle
    omega
  · rintro rfl
    intro n hn
    exact (chargeUnit_eq_one_iff hn 0).2 (dvd_zero _)

/-- **Theorem 3.2 — reconstruction from the complete pro-history.** -/
theorem eq_of_forall_chargeUnit_eq {q q' : ℤ}
    (h : ∀ n : ℕ, 1 ≤ n → chargeUnit n q = chargeUnit n q') : q = q' := by
  refine eq_of_forall_kummerHolonomy_eq fun n hn => ?_
  have := h n (by omega)
  simpa using congrArg (fun u : ℂˣ => (u : ℂ)) this

/-! ## Group-like landing -/

/-- **Corollary 4.1 — group-like landing no-go.**  If one group-like element of the complex root
group algebra realizes a pro-history on the cofinal tail of multiples of its birth depth, the
history is trivial. -/
theorem eq_one_of_groupLike_landing (z : ProHistory)
    (x : MonoidAlgebra ℂ ℂˣ) (hx : IsGroupLikeElem ℂ x)
    (d : ℕ) (hd : 1 ≤ d)
    (hland : ∀ m : ℕ, 1 ≤ m → d ∣ m → MonoidAlgebra.single (z.toFun m) (1 : ℂ) = x) :
    ∀ n : ℕ, 1 ≤ n → z.toFun n = 1 := by
  obtain ⟨g, rfl⟩ := isGroupLikeElem_iff_exists_single.1 hx
  refine z.isIndFormed_iff.1 ⟨d, hd, g, fun m hm hdm => ?_⟩
  have hsingle := hland m hm hdm
  exact Finsupp.single_left_injective (one_ne_zero) (by
    have := congrArg MonoidAlgebra.coeff hsingle
    rwa [MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single] at this)

/-- **Corollary 4.1 for charges.**  No nonzero integral charge lands as one group-like element of
the finite-stage cyclotomic source compatibly at every depth. -/
theorem eq_zero_of_groupLike_landing {q : ℤ}
    (x : MonoidAlgebra ℂ ℂˣ) (hx : IsGroupLikeElem ℂ x)
    (d : ℕ) (hd : 1 ≤ d)
    (hland : ∀ m : ℕ, 1 ≤ m → d ∣ m → MonoidAlgebra.single (chargeUnit m q) (1 : ℂ) = x) :
    q = 0 :=
  (chargeHistory_isIndFormed_iff q).1
    ((chargeHistory q).isIndFormed_iff.2
      (eq_one_of_groupLike_landing (chargeHistory q) x hx d hd hland))

/-! ## The prime-to-`p` scope -/

/-- **Prime-to-two selection.**  A root of unity of odd order fixed by both the threefold and the
fivefold reduction is trivial. -/
theorem eq_one_of_odd_of_pow_three_of_pow_five {ξ : ℂˣ} {d : ℕ} (hd : Odd d)
    (h1 : ξ ^ d = 1) (h3 : ξ ^ 3 = ξ) (h5 : ξ ^ 5 = ξ) : ξ = 1 := by
  have hsq : ξ ^ 2 = 1 := by
    have h53 : ξ ^ 5 = ξ ^ 3 * ξ ^ 2 := by rw [← pow_add]
    rw [h5, h3] at h53
    have hstep : ξ * 1 = ξ * ξ ^ 2 := by rw [mul_one]; exact h53
    exact (mul_left_cancel hstep).symm
  obtain ⟨k, rfl⟩ := hd
  rw [pow_add, pow_mul, hsq, one_pow, one_mul, pow_one] at h1
  exact h1

end

end GaloisForLFunctions.HTGeometry
