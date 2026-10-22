import GaloisForLFunctions.RHTower.Deninger.DeningerCommonCyclic
import GaloisForLFunctions.RHTower.Deninger.DeningerNotConjShort
import GaloisForLFunctions.RHTower.Deninger.DeningerBaseCentralizerOne
import GaloisForLFunctions.RHTower.Deninger.DeningerFactorCentralizer

/-!
# The descent in an amalgam with one exceptional factor

In an amalgam whose base group is self centralizing in every factor but one, an element commuting
with a nontrivial base element lies in the exceptional factor, and an element commuting with an
element of a factor either lies in that factor or the factor element conjugates into the base.  In
both cases a long cyclically reduced element would be conjugate to an element of length at most one,
which is impossible, so the two structural hypotheses of the descent hold.

* `deningerCommon_cyclic_amalgam` : commuting elements lie in a common cyclic subgroup.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Commuting elements lie in a common cyclic subgroup**, in an amalgam over a base group which is
self centralizing in every factor but one. -/
theorem deningerCommon_cyclic_amalgam
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (i₀ : ι)
    (hself : ∀ (i : ι) (x : G i) (v : H), i ≠ i₀ → v ≠ 1 → x * φ i v * x⁻¹ = φ i v →
      x ∈ (φ i).range)
    (X : List (Σ i, G i)) (hX2 : 2 ≤ X.length)
    (hXred : ∀ p ∈ X, p.2 ∉ (φ p.1).range)
    (hXalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) X)
    (hXcyc : ∀ p ∈ X.getLast?, ∀ q ∈ X.head?, p.1 ≠ q.1)
    (z : PushoutI φ)
    (hz : z⁻¹ * deningerLetterProd (φ := φ) X * z = deningerLetterProd (φ := φ) X) :
    ∃ (v : PushoutI φ) (n : ℕ), 0 < n ∧ v ^ n = deningerLetterProd (φ := φ) X ∧
      z ∈ Subgroup.zpowers v := by
  classical
  -- an element of a factor has length at most one
  have hlenof : ∀ (i : ι) (x : G i), deningerLen d (PushoutI.of (φ := φ) i x) ≤ 1 := by
    intro i x
    have := deningerLen_of_mul_le (d := d) i x 1
    rw [mul_one, deningerLen_one] at this
    omega
  -- an element commuting with a nontrivial base element lies in the exceptional factor
  have hbasecent : ∀ (k : H) (V : List (Σ i, G i)), 2 ≤ V.length →
      (∀ p ∈ V, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V →
      (∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) →
      ∀ g : PushoutI φ, k ≠ 1 →
      (g⁻¹ * deningerLetterProd (φ := φ) V * g) * PushoutI.base φ k =
        PushoutI.base φ k * (g⁻¹ * deningerLetterProd (φ := φ) V * g) → False := by
    intro k V h2 hred halt hcyc g hk hcomm
    obtain ⟨y, hy⟩ := deningerCentralizer_base_one (d := d) hcent i₀ hself k hk _ hcomm
    refine deningerCycRed_not_conj_short (d := d) V h2 hred halt hcyc g⁻¹
      (PushoutI.of (φ := φ) i₀ y) (hlenof i₀ y) ?_
    rw [← hy]
    group
  refine deningerCommon_cyclic (d := d) ?_ ?_ X hX2 hXred hXalt hXcyc z hz
  · -- a base element commuting with a long cyclically reduced word is trivial
    intro k V h2 hred halt hcyc hcomm
    by_cases hk : k = 1
    · rw [hk, map_one]
    · exact absurd (hbasecent k V h2 hred halt hcyc 1 hk (by
        rw [inv_one, one_mul, mul_one]
        exact hcomm.symm)) (fun h => h)
  · -- no conjugate of an element of a factor commutes with a long cyclically reduced word
    intro V h2 hred halt hcyc i x g hx hcomm
    have hcomm' : (g⁻¹ * deningerLetterProd (φ := φ) V * g) * PushoutI.of (φ := φ) i x =
        PushoutI.of (φ := φ) i x * (g⁻¹ * deningerLetterProd (φ := φ) V * g) := by
      calc (g⁻¹ * deningerLetterProd (φ := φ) V * g) * PushoutI.of (φ := φ) i x
          = g⁻¹ * (deningerLetterProd (φ := φ) V *
              (g * PushoutI.of (φ := φ) i x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * PushoutI.of (φ := φ) i x * g⁻¹) *
              deningerLetterProd (φ := φ) V) * g := by rw [← hcomm]
        _ = PushoutI.of (φ := φ) i x * (g⁻¹ * deningerLetterProd (φ := φ) V * g) := by group
    rcases deningerCentralizer_factor (d := d) i x hx _ hcomm' with ⟨y, hy⟩ | ⟨x', k, hk⟩
    · refine deningerCycRed_not_conj_short (d := d) V h2 hred halt hcyc g⁻¹
        (PushoutI.of (φ := φ) i y) (hlenof i y) ?_
      rw [← hy]
      group
    · have hk1 : k ≠ 1 := by
        intro hc
        rw [hc, map_one] at hk
        exact hx ⟨1, by
          rw [map_one]
          have : x = x' * (x'⁻¹ * x * x') * x'⁻¹ := by group
          rw [this, hk, mul_one, mul_inv_cancel]⟩
      have hxconj : PushoutI.of (φ := φ) i x =
          PushoutI.of (φ := φ) i x' * PushoutI.base φ k * (PushoutI.of (φ := φ) i x')⁻¹ := by
        have h1 : PushoutI.of (φ := φ) i (x'⁻¹ * x * x') = PushoutI.base φ k := by
          rw [hk, PushoutI.of_apply_eq_base]
        rw [map_mul, map_mul, map_inv] at h1
        rw [← h1]
        group
      refine absurd (hbasecent k V h2 hred halt hcyc
        (g * PushoutI.of (φ := φ) i x') hk1 ?_) (fun h => h)
      rw [show (g * PushoutI.of (φ := φ) i x')⁻¹ * deningerLetterProd (φ := φ) V *
            (g * PushoutI.of (φ := φ) i x') =
          (PushoutI.of (φ := φ) i x')⁻¹ * (g⁻¹ * deningerLetterProd (φ := φ) V * g) *
            PushoutI.of (φ := φ) i x' by group]
      calc (PushoutI.of (φ := φ) i x')⁻¹ * (g⁻¹ * deningerLetterProd (φ := φ) V * g) *
            PushoutI.of (φ := φ) i x' * PushoutI.base φ k
          = (PushoutI.of (φ := φ) i x')⁻¹ *
              ((g⁻¹ * deningerLetterProd (φ := φ) V * g) *
                (PushoutI.of (φ := φ) i x' * PushoutI.base φ k *
                  (PushoutI.of (φ := φ) i x')⁻¹)) * PushoutI.of (φ := φ) i x' := by group
        _ = (PushoutI.of (φ := φ) i x')⁻¹ *
              ((g⁻¹ * deningerLetterProd (φ := φ) V * g) * PushoutI.of (φ := φ) i x) *
              PushoutI.of (φ := φ) i x' := by rw [← hxconj]
        _ = (PushoutI.of (φ := φ) i x')⁻¹ *
              (PushoutI.of (φ := φ) i x * (g⁻¹ * deningerLetterProd (φ := φ) V * g)) *
              PushoutI.of (φ := φ) i x' := by rw [hcomm']
        _ = (PushoutI.of (φ := φ) i x')⁻¹ *
              ((PushoutI.of (φ := φ) i x' * PushoutI.base φ k *
                (PushoutI.of (φ := φ) i x')⁻¹) *
                (g⁻¹ * deningerLetterProd (φ := φ) V * g)) * PushoutI.of (φ := φ) i x' := by
            rw [hxconj]
        _ = PushoutI.base φ k * ((PushoutI.of (φ := φ) i x')⁻¹ *
              (g⁻¹ * deningerLetterProd (φ := φ) V * g) * PushoutI.of (φ := φ) i x') := by group

end RHTower
