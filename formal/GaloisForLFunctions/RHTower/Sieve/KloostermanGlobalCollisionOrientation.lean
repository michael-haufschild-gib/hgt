import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime

/-!
# Exact orientation fibres of global Kloosterman collisions

For a pairwise-coprime positive modulus family, each global cross-frequency fibre has at most two
representatives.  This file identifies the second representative exactly: reverse the two stored
moduli and negate both unit endpoints.  Hence every nonempty fibre has exactly two points.

When both the modulus weights and source coefficients are fixed by complex conjugation, the two
representatives carry identical coefficients.  Thus the factor two in the existing coprime global
collision receiver is a literal orientation symmetry, not unaccounted cross-modulus cancellation.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Reversing two stored clocks and negating both unit endpoints preserves their global phase. -/
theorem kloostermanGlobalCrossPhaseFrequency_reverse_neg
    (Q : Finset ℕ) (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) :
    kloostermanGlobalCrossPhaseFrequency Q r q (-y) (-x) =
      kloostermanGlobalCrossPhaseFrequency Q q r x y := by
  apply (kloostermanGlobalCrossPhaseFrequency_eq_iff Q r q q r hr hq hq hr (-y) (-x) x y).mpr
  unfold kloostermanCrossPhaseRatio
  change star (ZMod.stdAddChar (-(y : ZMod (r + 1)))) *
      ZMod.stdAddChar (-(x : ZMod (q + 1))) = _
  rw [AddChar.map_neg_eq_conj, AddChar.map_neg_eq_conj]
  simp only [starRingEnd_apply, star_star]
  change ZMod.stdAddChar (y : ZMod (r + 1)) *
      star (ZMod.stdAddChar (x : ZMod (q + 1))) = _
  ring

/-- At conjugation-fixed sources, negating a unit frequency conjugates its source transform. -/
theorem kloostermanSourceFourier_neg_eq_star_of_star_fixed
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ)
    (hb : ∀ n ∈ B, star (b n) = b n)
    (x : (ZMod q)ˣ) :
    kloostermanSourceFourier q B b (-x) = star (kloostermanSourceFourier q B b x) := by
  unfold kloostermanSourceFourier
  change (∑ n ∈ B, b n * ZMod.stdAddChar
      ((n : ZMod q) * (((-x)⁻¹ : (ZMod q)ˣ) : ZMod q))) =
    (starRingEnd ℂ) (∑ n ∈ B, b n * ZMod.stdAddChar
      ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [map_mul]
  simp only [starRingEnd_apply, hb n hn]
  congr 1
  rw [star_stdAddChar_eq_neg q]
  congr 1
  simp

/-- The forced second representative of a global cross-frequency tuple. -/
def kloostermanGlobalCrossTupleReverseNeg
    {Q : Finset ℕ} (p : KloostermanGlobalCrossTuple Q) :
    KloostermanGlobalCrossTuple Q :=
  ⟨p.2.1, p.1, ⟨⟨-p.2.2.1.2, -p.2.2.1.1⟩, Ne.symm p.2.2.2⟩⟩

/-- The forced orientation mate has exactly the same literal global frequency. -/
theorem kloostermanLiteralCrossTupleFrequency_reverseNeg
    (Q : Finset ℕ) (p : KloostermanGlobalCrossTuple Q) :
    kloostermanLiteralCrossTupleFrequency Q (kloostermanGlobalCrossTupleReverseNeg p) =
      kloostermanLiteralCrossTupleFrequency Q p := by
  rcases p with ⟨q, r, ⟨⟨x, y⟩, hqr⟩⟩
  exact kloostermanGlobalCrossPhaseFrequency_reverse_neg Q q r q.property r.property x y

/-- A cross-frequency tuple and its orientation mate are distinct because the stored moduli differ. -/
theorem kloostermanGlobalCrossTupleReverseNeg_ne
    {Q : Finset ℕ} (p : KloostermanGlobalCrossTuple Q) :
    kloostermanGlobalCrossTupleReverseNeg p ≠ p := by
  intro h
  have hfirst := congrArg (fun u : KloostermanGlobalCrossTuple Q => u.1.1) h
  change p.2.1.1 = p.1.1 at hfirst
  apply p.2.2.2
  exact Subtype.ext hfirst.symm

/-- Conjugation-fixed weights and source coefficients make the orientation pair constructive. -/
theorem kloostermanGlobalCrossTupleCoefficient_reverseNeg_eq_of_star_fixed
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ)
    (hw : ∀ q, star (w q) = w q)
    (hb : ∀ n ∈ B, star (b n) = b n)
    (p : KloostermanGlobalCrossTuple Q) :
    kloostermanGlobalCrossTupleCoefficient Q w B b (kloostermanGlobalCrossTupleReverseNeg p) =
      kloostermanGlobalCrossTupleCoefficient Q w B b p := by
  rcases p with ⟨q, r, ⟨⟨x, y⟩, hqr⟩⟩
  unfold kloostermanGlobalCrossTupleReverseNeg kloostermanGlobalCrossTupleCoefficient
  simp only
  rw [kloostermanSourceFourier_neg_eq_star_of_star_fixed (r + 1) B b hb y,
    kloostermanSourceFourier_neg_eq_star_of_star_fixed (q + 1) B b hb x]
  simp only [star_star, hw]
  ring

/-- Under pairwise-coprime positive clocks, every global collision fibre is exactly its forced
orientation pair. -/
theorem card_filter_kloostermanLiteralCrossTupleFrequency_eq_two
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (p : KloostermanGlobalCrossTuple Q) :
    (Finset.univ.filter fun u : KloostermanGlobalCrossTuple Q =>
      kloostermanLiteralCrossTupleFrequency Q p =
        kloostermanLiteralCrossTupleFrequency Q u).card = 2 := by
  let S := Finset.univ.filter fun u : KloostermanGlobalCrossTuple Q =>
    kloostermanLiteralCrossTupleFrequency Q p =
      kloostermanLiteralCrossTupleFrequency Q u
  have hp : p ∈ S := by simp [S]
  have hrev : kloostermanGlobalCrossTupleReverseNeg p ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (kloostermanLiteralCrossTupleFrequency_reverseNeg Q p).symm
  have hne : p ≠ kloostermanGlobalCrossTupleReverseNeg p :=
    (kloostermanGlobalCrossTupleReverseNeg_ne p).symm
  have hsubset : ({p, kloostermanGlobalCrossTupleReverseNeg p} :
      Finset (KloostermanGlobalCrossTuple Q)) ⊆ S := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hp
    · exact hrev
  have hlower : 2 ≤ S.card := by
    calc
      2 = ({p, kloostermanGlobalCrossTupleReverseNeg p} :
          Finset (KloostermanGlobalCrossTuple Q)).card := (Finset.card_pair hne).symm
      _ ≤ S.card := Finset.card_le_card hsubset
  have hupper : S.card ≤ 2 := by
    exact card_filter_kloostermanLiteralCrossTupleFrequency_le_two Q hpair
      (fun i => hpos i.1 i.2) p
  exact Nat.le_antisymm hupper hlower

end

end RHTower.Sieve
