import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.NNReal.Defs

/-!
# The additive defect of a multiplicative map and the subspaces `Y_α`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Propositions 14.6
(`t93`) and 14.12 (`t119`).

For a perfect `F_p`-algebra `A` and a rank one valuation ring `𝒪` with valuation `v`, a pointed
multiplicative map `P : A → 𝒪` has additive defect `D_P (r,s) = P (r+s) - P r - P s`, and

`Y_α = { P | v (D_P (r,s)) ≤ α  for all r, s }` .

The Frobenius operator `F_p P = P ^ p` is precomposition with the Frobenius of `A`, because `P` is
multiplicative; since the Frobenius of a perfect `F_p`-algebra is bijective, `F_p` is a bijection of
the set of pointed multiplicative maps which preserves each `Y_α` in both directions.

In any commutative ring one has

`(a - b - c) ^ p ^ ν ≡ a ^ p ^ ν - b ^ p ^ ν - c ^ p ^ ν  (mod p)` ,

so `v (D_{F_p^ν P}) ≤ max (v (D_P) ^ p ^ ν , v p)`.  For `α < 1` and `v p > 0` the first term
eventually drops below `v p`, and since `F_p^ν` is onto `Y_α` this gives `Y_α = Y_{v p}`, which is
Deninger's `Y_α = Y` for `α ≥ 1 / p`.
-/

namespace RHTower

open scoped NNReal

/-! ## A congruence modulo `p` -/

/-- In any commutative ring, `(-b) ^ p ^ ν ≡ - b ^ p ^ ν` modulo `p`. -/
theorem deningerNeg_pow_prime_pow {O : Type*} [CommRing O] {p : ℕ} (hp : p.Prime) (b : O)
    (ν : ℕ) : ∃ e : O, (-b) ^ p ^ ν = -b ^ p ^ ν + (p : O) * e := by
  rcases hp.eq_two_or_odd' with h2 | hodd
  · subst h2
    rcases Nat.eq_zero_or_pos ν with rfl | hν
    · exact ⟨0, by ring⟩
    · refine ⟨b ^ 2 ^ ν, ?_⟩
      have : Even (2 ^ ν) := (Nat.even_pow' hν.ne').2 even_two
      rw [this.neg_pow]
      push_cast
      ring
  · refine ⟨0, ?_⟩
    have hoddpow : Odd (p ^ ν) := hodd.pow
    rw [hoddpow.neg_pow]
    ring

/-- **The congruence behind Deninger's Proposition 14.6.**  In any commutative ring,
`(a - b - c) ^ p ^ ν ≡ a ^ p ^ ν - b ^ p ^ ν - c ^ p ^ ν` modulo `p`. -/
theorem deningerSubSub_pow_prime_pow {O : Type*} [CommRing O] {p : ℕ} (hp : p.Prime)
    (a b c : O) (ν : ℕ) :
    ∃ e : O, a ^ p ^ ν - b ^ p ^ ν - c ^ p ^ ν = (a - b - c) ^ p ^ ν + (p : O) * e := by
  obtain ⟨r₁, h₁⟩ := (Commute.all a (-b)).exists_add_pow_prime_pow_eq hp ν
  obtain ⟨r₂, h₂⟩ := (Commute.all (a + -b) (-c)).exists_add_pow_prime_pow_eq hp ν
  obtain ⟨e₁, he₁⟩ := deningerNeg_pow_prime_pow hp b ν
  obtain ⟨e₂, he₂⟩ := deningerNeg_pow_prime_pow hp c ν
  refine ⟨-(a * -b * r₁ + (a + -b) * -c * r₂ + e₁ + e₂), ?_⟩
  have hrw : a - b - c = a + -b + -c := by ring
  rw [hrw, h₂, h₁, he₁, he₂]
  ring

/-! ## The defect sets -/

variable {A O : Type*} [CommRing A] [CommRing O] (v : Valuation O ℝ≥0)

/-- The additive defect of a multiplicative map. -/
def deningerDefect (P : A →*₀ O) (r s : A) : O := P (r + s) - P r - P s

/-- **Deninger, Definition 14.5 (`t92`) / 14.11 (`t1512`).**  The set `Y_α` of pointed
multiplicative maps whose additive defect has valuation at most `α`. -/
def DeningerDefectSet (α : ℝ≥0) : Set (A →*₀ O) :=
  {P | ∀ r s : A, v (deningerDefect P r s) ≤ α}

variable {p : ℕ} [Fact p.Prime] [CharP A p] [PerfectRing A p]

/-- **Deninger, §14.**  The Frobenius operator on pointed multiplicative maps: raising the values
to the `p`-th power, equivalently precomposing with the Frobenius of `A`. -/
def deningerDefectFrobenius (P : A →*₀ O) : A →*₀ O :=
  P.comp (frobenius A p).toMonoidWithZeroHom

omit [PerfectRing A p] in
@[simp] theorem deningerDefectFrobenius_apply (P : A →*₀ O) (a : A) :
    deningerDefectFrobenius (p := p) P a = P (a ^ p) := rfl

omit [PerfectRing A p] in
theorem deningerDefectFrobenius_eq_pow (P : A →*₀ O) (a : A) :
    deningerDefectFrobenius (p := p) P a = P a ^ p := by
  rw [deningerDefectFrobenius_apply, map_pow]

omit [PerfectRing A p] in
theorem deningerDefect_frobenius (P : A →*₀ O) (r s : A) :
    deningerDefect (deningerDefectFrobenius (p := p) P) r s
      = deningerDefect P (r ^ p) (s ^ p) := by
  have hadd : (r + s) ^ p = r ^ p + s ^ p := add_pow_char r s p
  simp only [deningerDefect, deningerDefectFrobenius_apply, hadd]

/-- **Deninger, Proposition 14.6 (`t93`), first assertion.**  The Frobenius operator preserves
`Y_α` in both directions. -/
theorem deningerDefectFrobenius_mem_iff (α : ℝ≥0) (P : A →*₀ O) :
    deningerDefectFrobenius (p := p) P ∈ DeningerDefectSet v α ↔ P ∈ DeningerDefectSet v α := by
  constructor
  · intro h r s
    obtain ⟨r', rfl⟩ := (frobeniusEquiv A p).surjective r
    obtain ⟨s', rfl⟩ := (frobeniusEquiv A p).surjective s
    have := h r' s'
    rwa [deningerDefect_frobenius] at this
  · intro h r s
    rw [deningerDefect_frobenius]
    exact h _ _

/-- The Frobenius operator is a bijection of the pointed multiplicative maps. -/
theorem deningerDefectFrobenius_bijective :
    Function.Bijective (deningerDefectFrobenius (A := A) (O := O) (p := p)) := by
  constructor
  · intro P Q h
    ext a
    obtain ⟨b, rfl⟩ := (frobeniusEquiv A p).surjective a
    exact congrArg (fun R : A →*₀ O => R b) h
  · intro Q
    refine ⟨Q.comp ((frobeniusEquiv A p).symm : A →+* A).toMonoidWithZeroHom, ?_⟩
    ext a
    show Q ((frobeniusEquiv A p).symm (a ^ p)) = Q a
    congr 1
    have : (frobeniusEquiv A p) a = a ^ p := rfl
    rw [← this, RingEquiv.symm_apply_apply]

/-- **Deninger, Proposition 14.6 (`t93`).**  The image of `Y_α` under the Frobenius operator is
`Y_α`. -/
theorem deningerDefectFrobenius_image (α : ℝ≥0) :
    deningerDefectFrobenius (A := A) (O := O) (p := p) '' DeningerDefectSet v α
      = DeningerDefectSet v α := by
  ext Q
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact (deningerDefectFrobenius_mem_iff v α P).2 hP
  · intro hQ
    obtain ⟨P, rfl⟩ := deningerDefectFrobenius_bijective.2 Q
    exact ⟨P, (deningerDefectFrobenius_mem_iff v α P).1 hQ, rfl⟩

/-! ## The valuation estimate -/

omit [CharP A p] [PerfectRing A p] in
/-- **Deninger, Proposition 14.6 (`t93`), the estimate.**  The defect of the `ν`-th Frobenius
iterate is bounded by `max (v (defect) ^ p ^ ν, v p)` on a valuation ring. -/
theorem deningerDefect_frobenius_iterate_le (hv : ∀ x : O, v x ≤ 1) (α : ℝ≥0)
    (P : A →*₀ O) (hP : P ∈ DeningerDefectSet v α) (ν : ℕ) (r s : A) :
    v (P (r + s) ^ p ^ ν - P r ^ p ^ ν - P s ^ p ^ ν) ≤ max (α ^ p ^ ν) (v (p : O)) := by
  obtain ⟨e, he⟩ := deningerSubSub_pow_prime_pow (Fact.out : p.Prime)
    (P (r + s)) (P r) (P s) ν
  rw [he]
  refine le_trans (v.map_add _ _) ?_
  refine max_le_max ?_ ?_
  · rw [map_pow]
    have hle : v (P (r + s) - P r - P s) ≤ α := hP r s
    gcongr
  · rw [map_mul]
    calc v (p : O) * v e ≤ v (p : O) * 1 := by gcongr; exact hv e
      _ = v (p : O) := mul_one _

omit [PerfectRing A p] in
/-- Iterating the Frobenius operator raises the values to the `p ^ ν`-th power. -/
theorem deningerDefectFrobenius_iterate_apply (ν : ℕ) (P : A →*₀ O) (a : A) :
    (deningerDefectFrobenius (p := p))^[ν] P a = P a ^ p ^ ν := by
  induction ν generalizing P with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, deningerDefectFrobenius_eq_pow, ← pow_mul,
        ← pow_succ']

theorem deningerDefectFrobenius_iterate_mem_iff (α : ℝ≥0) (ν : ℕ) (P : A →*₀ O) :
    (deningerDefectFrobenius (p := p))^[ν] P ∈ DeningerDefectSet v α
      ↔ P ∈ DeningerDefectSet v α := by
  induction ν generalizing P with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, deningerDefectFrobenius_mem_iff]

/-- **Deninger, Proposition 14.6 (`t93`) and Proposition 14.12 (`t119`).**  For `α < 1` and a
valuation ring in which `p` is nonzero, `Y_α = Y_{v p}`; in Deninger's normalisation this is
`Y_α = Y` for every `0 < α < 1`. -/
theorem deningerDefectSet_eq_of_lt_one (hv : ∀ x : O, v x ≤ 1) {α : ℝ≥0} (hα : α < 1)
    (hp0 : 0 < v (p : O)) (hple : v (p : O) ≤ α) :
    DeningerDefectSet (A := A) v α = DeningerDefectSet (A := A) v (v (p : O)) := by
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one hp0 hα
  have hp1 : 1 < p := ‹Fact p.Prime›.out.one_lt
  have hν : n ≤ p ^ n := (Nat.lt_pow_self hp1).le
  have hpow : α ^ p ^ n ≤ v (p : O) :=
    le_of_lt (lt_of_le_of_lt (pow_le_pow_of_le_one (by simp : (0:ℝ≥0) ≤ α) hα.le hν) hn)
  refine Set.Subset.antisymm ?_ ?_
  · intro Q hQ r s
    obtain ⟨P, rfl⟩ :=
      (deningerDefectFrobenius_bijective (A := A) (O := O) (p := p)).iterate n |>.2 Q
    have hP : P ∈ DeningerDefectSet v α :=
      (deningerDefectFrobenius_iterate_mem_iff v α n P).1 hQ
    have hest := deningerDefect_frobenius_iterate_le (p := p) v hv α P hP n r s
    have hrw : deningerDefect ((deningerDefectFrobenius (p := p))^[n] P) r s
        = P (r + s) ^ p ^ n - P r ^ p ^ n - P s ^ p ^ n := by
      simp only [deningerDefect, deningerDefectFrobenius_iterate_apply]
    rw [hrw]
    exact le_trans hest (max_le hpow le_rfl)
  · intro P hP r s
    exact le_trans (hP r s) hple

end RHTower
