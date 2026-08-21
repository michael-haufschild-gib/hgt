import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.DysonTransform
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Additive energy and a Pollard-type lower bound

`energy A B = ∑_g r_{A,B}(g)²` is the additive energy of a pair of finite subsets of a finite
commutative group.  It is unchanged when the second set is inverted (`energy_inv`), because both
sides count quadruples `(a,b,a',b')` and the involution `(a,b,a',b') ↦ (a,b',a',b)` matches the two
conditions `a·b = a'·b'` and `a·b'⁻¹ = a'·b⁻¹`.

The main results are the lower bounds for `repSum A B t = ∑_{i=1}^t #(A ·_i B)`:

* `le_repSum_of_linear_quadratic` — for any reals `a, b` with `b > 0`, `a − b ≤ 1` and
  `a² ≤ 4bt`, one has `repSum ≥ a·#A·#B − b·energy`.  This comes from the pointwise minorant
  `min(r,t) ≥ a r − b r²`, valid at every natural number `r`.
* `repSum_ge_min` — optimising the two free parameters gives
  `repSum ≥ min( t·M/(t+√(t(t−1))), t·M²/Q )` with `M = #A·#B` and `Q` the energy.
* `energy_le_of_rep_inv_le` — an upper bound for the energy from a pointwise bound on
  representations as `a·b⁻¹`.
* `repSum_ge_min_of_rep_inv_le` — combining the two, Grynkiewicz's Lemma 2.1.

The parameter choices in `repSum_ge_min` are `(a,b) = (2t/μ, t/μ²)` when `μ = Q/M ≥ t + s`, and
`(a,b) = (2(t−s), 2t−1−2s)` otherwise, where `s = √(t(t−1))`; the identity
`(t+s)(2t−1−2s) = t−s` makes the second case exact.  This replaces the continuous
extremal-configuration argument of the source, and yields the same constants.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- The (unreduced) additive energy `∑_g r_{A,B}(g)²`. -/
def energy (A B : Finset G) : ℕ := ∑ g : G, (rep A B g) ^ 2

/-- A linear-quadratic minorant of `min(r, t)` valid at every natural number `r`. -/
theorem le_min_of_linear_quadratic {a b : ℝ} {t r : ℕ} (hb : 0 < b) (hab : a - b ≤ 1)
    (hmax : a ^ 2 ≤ 4 * b * t) :
    a * (r : ℝ) - b * (r : ℝ) ^ 2 ≤ ((min r t : ℕ) : ℝ) := by
  rcases le_total t r with hr | hr
  · have hmin : (min r t : ℕ) = t := min_eq_right hr
    rw [hmin]
    nlinarith [sq_nonneg (2 * b * (r : ℝ) - a), hb]
  · have hmin : (min r t : ℕ) = r := min_eq_left hr
    rw [hmin]
    rcases Nat.eq_zero_or_pos r with h0 | h1
    · simp [h0]
    · have h1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1
      have hbr : b ≤ b * (r : ℝ) := le_mul_of_one_le_right hb.le h1'
      have h2 : (a - 1) * (r : ℝ) ≤ (b * (r : ℝ)) * (r : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith
      nlinarith [h2]

/-- Summing the pointwise minorant: a lower bound for `∑_{i=1}^t #(A ·_i B)` in terms of the
total mass `#A · #B` and the additive energy. -/
theorem le_repSum_of_linear_quadratic {a b : ℝ} (A B : Finset G) (t : ℕ)
    (hb : 0 < b) (hab : a - b ≤ 1) (hmax : a ^ 2 ≤ 4 * b * t) :
    a * ((A.card : ℝ) * B.card) - b * (energy A B : ℝ) ≤ (repSum A B t : ℝ) := by
  classical
  have hsum : (repSum A B t : ℝ) = ∑ g : G, ((min (rep A B g) t : ℕ) : ℝ) := by
    rw [repSum_eq_sum_min]
    push_cast
    rfl
  have hmass : ((A.card : ℝ) * B.card) = ∑ g : G, ((rep A B g : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, sum_rep]
    push_cast
    ring
  have hen : (energy A B : ℝ) = ∑ g : G, ((rep A B g : ℕ) : ℝ) ^ 2 := by
    rw [energy, Nat.cast_sum]
    push_cast
    rfl
  rw [hsum, hmass, hen, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun g _ => ?_)
  exact le_min_of_linear_quadratic hb hab hmax


theorem sum_rep_le_energy (A B : Finset G) : A.card * B.card ≤ energy A B := by
  rw [← sum_rep A B, energy]
  exact Finset.sum_le_sum (fun g _ => Nat.le_self_pow (by norm_num) _)

/-- **Pollard-type lower bound from the additive energy.**  With `M = #A · #B`, `Q` the additive
energy and `s = √(t(t−1))`,
`∑_{i=1}^t #(A ·_i B) ≥ min ( t·M/(t+s), t·M²/Q )`. -/
theorem repSum_ge_min (A B : Finset G) (t : ℕ) (ht : 1 ≤ t) (hA : A.Nonempty) (hB : B.Nonempty) :
    min ((t : ℝ) * ((A.card : ℝ) * B.card)
          / ((t : ℝ) + Real.sqrt ((t : ℝ) * ((t : ℝ) - 1))))
        ((t : ℝ) * ((A.card : ℝ) * B.card) ^ 2 / (energy A B : ℝ))
      ≤ (repSum A B t : ℝ) := by
  set M : ℝ := (A.card : ℝ) * B.card with hMdef
  set Q : ℝ := (energy A B : ℝ) with hQdef
  set s : ℝ := Real.sqrt ((t : ℝ) * ((t : ℝ) - 1)) with hsdef
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hnn : (0 : ℝ) ≤ (t : ℝ) * ((t : ℝ) - 1) := by nlinarith
  have hs2 : s ^ 2 = (t : ℝ) * ((t : ℝ) - 1) := Real.sq_sqrt hnn
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hst : s < (t : ℝ) := by nlinarith [hs2, hs0]
  have hts : (0 : ℝ) < (t : ℝ) + s := by linarith
  have hMpos : (0 : ℝ) < M := by
    rw [hMdef]
    have h1 : 0 < A.card := Finset.card_pos.2 hA
    have h2 : 0 < B.card := Finset.card_pos.2 hB
    positivity
  have hQM : M ≤ Q := by
    rw [hMdef, hQdef]
    exact_mod_cast sum_rep_le_energy A B
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le hMpos hQM
  have hbpos : (0 : ℝ) < 2 * (t : ℝ) - 1 - 2 * s := by nlinarith [hs2, hs0]
  have hkey : ((t : ℝ) + s) * (2 * (t : ℝ) - 1 - 2 * s) = (t : ℝ) - s := by nlinarith [hs2]
  by_cases hcase : Q ≤ ((t : ℝ) + s) * M
  · refine le_trans (min_le_left _ _) ?_
    have hdiv : (t : ℝ) * M / ((t : ℝ) + s) = ((t : ℝ) - s) * M := by
      rw [div_eq_iff (ne_of_gt hts)]
      nlinarith [hs2]
    rw [hdiv]
    have hlq := le_repSum_of_linear_quadratic (a := 2 * ((t : ℝ) - s))
      (b := 2 * (t : ℝ) - 1 - 2 * s) A B t hbpos (by linarith) (by nlinarith [hs2])
    have hbQ : (2 * (t : ℝ) - 1 - 2 * s) * Q ≤ ((t : ℝ) - s) * M := by
      calc (2 * (t : ℝ) - 1 - 2 * s) * Q
          ≤ (2 * (t : ℝ) - 1 - 2 * s) * (((t : ℝ) + s) * M) :=
            mul_le_mul_of_nonneg_left hcase (le_of_lt hbpos)
        _ = ((t : ℝ) - s) * M := by rw [← hkey]; ring
    have : ((t : ℝ) - s) * M ≤ 2 * ((t : ℝ) - s) * M - (2 * (t : ℝ) - 1 - 2 * s) * Q := by
      linarith
    linarith [hlq, this]
  · push Not at hcase
    refine le_trans (min_le_right _ _) ?_
    have hfac : Q ^ 2 - 2 * (t : ℝ) * M * Q + (t : ℝ) * M ^ 2
        = (Q - ((t : ℝ) + s) * M) * (Q - ((t : ℝ) - s) * M) := by nlinarith [hs2]
    have hpos1 : 0 < Q - ((t : ℝ) + s) * M := by linarith
    have hpos2 : 0 < Q - ((t : ℝ) - s) * M := by nlinarith [hs0, hMpos]
    have hnonneg : (0 : ℝ) ≤ Q ^ 2 - 2 * (t : ℝ) * M * Q + (t : ℝ) * M ^ 2 := by
      rw [hfac]
      exact le_of_lt (mul_pos hpos1 hpos2)
    have hmulQ : (0 : ℝ) ≤ Q * (Q ^ 2 - 2 * (t : ℝ) * M * Q + (t : ℝ) * M ^ 2) :=
      mul_nonneg (le_of_lt hQpos) hnonneg
    have hab : 2 * (t : ℝ) * M / Q - (t : ℝ) * M ^ 2 / Q ^ 2 ≤ 1 := by
      rw [div_sub_div _ _ (ne_of_gt hQpos) (by positivity), div_le_one (by positivity)]
      nlinarith [hmulQ]
    have hbpos2 : (0 : ℝ) < (t : ℝ) * M ^ 2 / Q ^ 2 := by positivity
    have hmaxeq : (2 * (t : ℝ) * M / Q) ^ 2 = 4 * ((t : ℝ) * M ^ 2 / Q ^ 2) * (t : ℝ) := by
      field_simp
      ring
    have hmax : (2 * (t : ℝ) * M / Q) ^ 2 ≤ 4 * ((t : ℝ) * M ^ 2 / Q ^ 2) * (t : ℝ) :=
      le_of_eq hmaxeq
    have hlq := le_repSum_of_linear_quadratic (a := 2 * (t : ℝ) * M / Q)
      (b := (t : ℝ) * M ^ 2 / Q ^ 2) A B t hbpos2 hab hmax
    have hval : 2 * (t : ℝ) * M / Q * M - (t : ℝ) * M ^ 2 / Q ^ 2 * Q
        = (t : ℝ) * M ^ 2 / Q := by
      field_simp
      ring
    linarith [hlq, hval.le, hval.ge]


/-! ### The energy is unchanged by inverting the second set -/

/-- The set of quadruples `(a, b, a', b') ∈ A × B × A × B` with `a·b = a'·b'`. -/
def quad (A B : Finset G) : Finset ((G × G) × (G × G)) :=
  ((A ×ˢ B) ×ˢ (A ×ˢ B)).filter (fun q => q.1.1 * q.1.2 = q.2.1 * q.2.2)

theorem energy_eq_card_quad (A B : Finset G) : energy A B = (quad A B).card := by
  classical
  have h : (quad A B).card
      = ∑ g : G, ((quad A B).filter (fun q => q.1.1 * q.1.2 = g)).card :=
    Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_univ _)
  rw [energy, h]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have hset : (quad A B).filter (fun q => q.1.1 * q.1.2 = g)
      = ((A ×ˢ B).filter (fun p => p.1 * p.2 = g))
        ×ˢ ((A ×ˢ B).filter (fun p => p.1 * p.2 = g)) := by
    ext q
    simp only [quad, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, h2, by rw [← h3, h4]⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨⟨h1, h3⟩, by rw [h2, h4]⟩, h2⟩
  rw [hset, Finset.card_product, sq]
  rfl

theorem energy_inv (A B : Finset G) : energy A B⁻¹ = energy A B := by
  classical
  rw [energy_eq_card_quad, energy_eq_card_quad]
  refine Finset.card_nbij' (fun q => ((q.1.1, q.2.2⁻¹), (q.2.1, q.1.2⁻¹)))
    (fun q => ((q.1.1, q.2.2⁻¹), (q.2.1, q.1.2⁻¹))) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, c⟩, ⟨a', c'⟩⟩ hq
    simp only [quad, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_inv'] at hq ⊢
    obtain ⟨⟨⟨ha, hc⟩, ha', hc'⟩, heq⟩ := hq
    refine ⟨⟨⟨ha, ?_⟩, ha', ?_⟩, ?_⟩
    · simpa using hc'
    · simpa using hc
    · rw [mul_inv_eq_iff_eq_mul, mul_assoc, mul_comm c⁻¹ c', ← mul_assoc, ← heq,
        mul_inv_cancel_right]
  · rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ hq
    simp only [quad, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product,
      Finset.mem_inv'] at hq ⊢
    obtain ⟨⟨⟨ha, hb⟩, ha', hb'⟩, heq⟩ := hq
    refine ⟨⟨⟨ha, ?_⟩, ha', ?_⟩, ?_⟩
    · simpa using hb'
    · simpa using hb
    · rw [mul_inv_eq_iff_eq_mul, mul_assoc, mul_comm b⁻¹ b', ← mul_assoc, ← heq,
        mul_inv_cancel_right]
  · rintro ⟨⟨a, c⟩, ⟨a', c'⟩⟩ _
    simp
  · rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ _
    simp


omit [Fintype G] in
theorem rep_le_card_right (A C : Finset G) (x : G) : rep A C x ≤ C.card := by
  rw [rep_eq_card_filter_right]
  exact Finset.card_filter_le _ _

/-- **Energy bound from a pointwise bound on difference representations.**  If every element
outside `T` has at most `k` representations as `a · b⁻¹`, then the additive energy of `(A, B)` is
at most `k·#A·#B + (#B − k)·#T·#B`. -/
theorem energy_le_of_rep_inv_le {A B T : Finset G} {k : ℕ}
    (hkB : k ≤ B.card) (hk : ∀ x : G, x ∉ T → rep A B⁻¹ x ≤ k) :
    energy A B ≤ k * (A.card * B.card) + (B.card - k) * (T.card * B.card) := by
  classical
  have hcardinv : (B⁻¹).card = B.card := Finset.card_inv B
  have hbound : ∀ x : G, rep A B⁻¹ x ≤ B.card := by
    intro x
    have := rep_le_card_right A B⁻¹ x
    omega
  have hsplit : ∑ x ∈ univ \ T, (rep A B⁻¹ x) ^ 2 + ∑ x ∈ T, (rep A B⁻¹ x) ^ 2
      = ∑ x : G, (rep A B⁻¹ x) ^ 2 := Finset.sum_sdiff (Finset.subset_univ T)
  have hout : ∑ x ∈ univ \ T, (rep A B⁻¹ x) ^ 2 ≤ ∑ x ∈ univ \ T, k * rep A B⁻¹ x := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    rw [sq]
    exact Nat.mul_le_mul_right _ (hk x (Finset.mem_sdiff.1 hx).2)
  have hin : ∑ x ∈ T, (rep A B⁻¹ x) ^ 2 ≤ ∑ x ∈ T, B.card * rep A B⁻¹ x := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [sq]
    exact Nat.mul_le_mul_right _ (hbound x)
  have hmassT : ∑ x ∈ T, rep A B⁻¹ x ≤ T.card * B.card := by
    calc ∑ x ∈ T, rep A B⁻¹ x ≤ ∑ _x ∈ T, B.card := Finset.sum_le_sum (fun x _ => hbound x)
      _ = T.card * B.card := by rw [Finset.sum_const, smul_eq_mul]
  have hmassAll : ∑ x : G, rep A B⁻¹ x = A.card * B.card := by
    rw [sum_rep, hcardinv]
  have hmassOut : ∑ x ∈ univ \ T, rep A B⁻¹ x + ∑ x ∈ T, rep A B⁻¹ x = A.card * B.card := by
    rw [Finset.sum_sdiff (Finset.subset_univ T), hmassAll]
  rw [← energy_inv, energy]
  rw [← hsplit]
  rw [← Finset.mul_sum] at hout hin
  have hkey : k * (∑ x ∈ univ \ T, rep A B⁻¹ x) + B.card * (∑ x ∈ T, rep A B⁻¹ x)
      ≤ k * (A.card * B.card) + (B.card - k) * (T.card * B.card) := by
    have h1 : B.card * (∑ x ∈ T, rep A B⁻¹ x)
        = k * (∑ x ∈ T, rep A B⁻¹ x) + (B.card - k) * (∑ x ∈ T, rep A B⁻¹ x) := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have h2 : (B.card - k) * (∑ x ∈ T, rep A B⁻¹ x) ≤ (B.card - k) * (T.card * B.card) :=
      Nat.mul_le_mul_left _ hmassT
    have h3 : k * (∑ x ∈ univ \ T, rep A B⁻¹ x) + k * (∑ x ∈ T, rep A B⁻¹ x)
        = k * (A.card * B.card) := by
      rw [← Nat.mul_add, hmassOut]
    omega
  omega


/-- **Grynkiewicz's Lemma 2.1.**  If every element outside `T` has at most `k` representations as
`a · b⁻¹`, then
`∑_{i=1}^t #(A ·_i B) ≥ min ( t·#A·#B/(t+√(t(t−1))), t·#A²·#B/(k·#A + #T·(#B−k)) )`. -/
theorem repSum_ge_min_of_rep_inv_le {A B T : Finset G} {k t : ℕ}
    (ht : 1 ≤ t) (hA : A.Nonempty) (hB : B.Nonempty) (hk1 : 1 ≤ k) (hkB : k ≤ B.card)
    (hk : ∀ x : G, x ∉ T → rep A B⁻¹ x ≤ k) :
    min ((t : ℝ) * ((A.card : ℝ) * B.card)
          / ((t : ℝ) + Real.sqrt ((t : ℝ) * ((t : ℝ) - 1))))
        ((t : ℝ) * (A.card : ℝ) ^ 2 * (B.card : ℝ)
          / ((k : ℝ) * A.card + (T.card : ℝ) * ((B.card : ℝ) - k)))
      ≤ (repSum A B t : ℝ) := by
  classical
  set D : ℝ := (k : ℝ) * A.card + (T.card : ℝ) * ((B.card : ℝ) - k) with hDdef
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hA
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hkBle : (k : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hkB
  have hTnn : (0 : ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hDpos : (0 : ℝ) < D := by
    rw [hDdef]
    have : (0 : ℝ) ≤ (T.card : ℝ) * ((B.card : ℝ) - k) := by
      apply mul_nonneg hTnn
      linarith
    nlinarith
  have hQpos : (0 : ℝ) < (energy A B : ℝ) := by
    have h1 : A.card * B.card ≤ energy A B := sum_rep_le_energy A B
    have h2 : 0 < A.card * B.card := by
      have := Finset.card_pos.2 hA
      have := Finset.card_pos.2 hB
      positivity
    have : 0 < energy A B := lt_of_lt_of_le h2 h1
    exact_mod_cast this
  have hQle : (energy A B : ℝ) ≤ (B.card : ℝ) * D := by
    have hnat := energy_le_of_rep_inv_le hkB hk
    have hcast : ((k * (A.card * B.card) + (B.card - k) * (T.card * B.card) : ℕ) : ℝ)
        = (B.card : ℝ) * D := by
      rw [hDdef]
      push_cast [Nat.cast_sub hkB]
      ring
    calc (energy A B : ℝ) ≤ ((k * (A.card * B.card) + (B.card - k) * (T.card * B.card) : ℕ) : ℝ) :=
          by exact_mod_cast hnat
      _ = (B.card : ℝ) * D := hcast
  refine le_trans ?_ (repSum_ge_min A B t ht hA hB)
  refine min_le_min (le_refl _) ?_
  rw [div_le_div_iff₀ hDpos hQpos]
  have hMsq : (t : ℝ) * (A.card : ℝ) ^ 2 * (B.card : ℝ) * (energy A B : ℝ)
      ≤ (t : ℝ) * (A.card : ℝ) ^ 2 * (B.card : ℝ) * ((B.card : ℝ) * D) := by
    have hnn : (0 : ℝ) ≤ (t : ℝ) * (A.card : ℝ) ^ 2 * (B.card : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hQle hnn
  have hgoal : (t : ℝ) * (A.card : ℝ) ^ 2 * (B.card : ℝ) * ((B.card : ℝ) * D)
      = (t : ℝ) * ((A.card : ℝ) * B.card) ^ 2 * D := by ring
  linarith [hMsq, hgoal.le, hgoal.ge]

end GaloisForLFunctions.HTGeometry.AddComb
