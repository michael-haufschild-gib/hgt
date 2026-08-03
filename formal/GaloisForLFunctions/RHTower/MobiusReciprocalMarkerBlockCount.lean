import GaloisForLFunctions.RHTower.MobiusReciprocalMarkerPrimeCapacity
import GaloisForLFunctions.RHTower.Sieve.ReciprocalFibre

/-!
# Assembling the reciprocal-marker blocks

The marker construction produces, for each retained prime `p`, a set of cofactors immediately above
`⌊X/p⌋`.  This module packages the three properties of the resulting target set:

* its cardinality is the *sum* of the cofactor counts, because the pair-to-product map is injective
  once every cofactor is smaller than every marker;
* every target lies in the physical window `(X, X+H]`, because `p·L ≤ H`;
* every target carries the reversed Möbius sign.

It also charges the discard: the markers lost to a set `S` of bad starts number at most
`|S| · (X/(A(A+1)) + 1)`, since the reciprocal fibres over `S` are disjoint and each is bounded by
`ReciprocalFibre.lean`.  That is the growing-block compensation — a bad-start proportion `ε` costs
at most `ε · A · (X/A² + 1)` markers, not `ε · A`.

Nothing here uses a distribution theorem; the inputs are the *hypotheses* a distribution theorem
would supply.
-/

noncomputable section

namespace RHTower

open Finset

/-- The target set of a marker family with prescribed cofactor sets. -/
def markerBlockTargets (P : Finset ℕ) (C : ℕ → Finset ℕ) : Finset ℕ :=
  (P.sigma C).image fun x => x.2 * x.1

/-- **Physical cardinality.**  No target is produced twice. -/
theorem card_markerBlockTargets (P : Finset ℕ) (C : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpos : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r) :
    (markerBlockTargets P C).card = ∑ p ∈ P, (C p).card := by
  classical
  have hinj : ∀ x ∈ P.sigma C, ∀ y ∈ P.sigma C, x.2 * x.1 = y.2 * y.1 → x = y := by
    rintro ⟨p, a⟩ hx ⟨q, b⟩ hy hxy
    simp only [Finset.mem_sigma] at hx hy
    obtain ⟨hp, ha⟩ := hx
    obtain ⟨hq, hb⟩ := hy
    have h := largePrimeMarker_product_injective (hprime p hp) (hprime q hq)
      (hpos q hq b hb) (hsmall q hq b hb p hp) (hsmall p hp a ha q hq) hxy
    obtain ⟨hab, hpq⟩ := h
    subst hab
    subst hpq
    rfl
  rw [markerBlockTargets, Finset.card_image_of_injOn hinj, Finset.card_sigma]

/-- **Physical window.**  Every target lies immediately above `X`. -/
theorem markerBlockTargets_mem_window {X H L : ℕ} (P : Finset ℕ) (C : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlow : ∀ p ∈ P, ∀ a ∈ C p, X / p < a)
    (hhigh : ∀ p ∈ P, ∀ a ∈ C p, a ≤ X / p + L)
    (hcost : ∀ p ∈ P, p * L ≤ H) :
    ∀ n ∈ markerBlockTargets P C, X < n ∧ n ≤ X + H := by
  classical
  intro n hn
  rw [markerBlockTargets] at hn
  obtain ⟨⟨p, a⟩, hx, rfl⟩ := Finset.mem_image.1 hn
  simp only [Finset.mem_sigma] at hx
  obtain ⟨hp, ha⟩ := hx
  exact reciprocalMarker_product_mem_window (hprime p hp).pos
    (hlow p hp a ha) (hhigh p hp a ha) (hcost p hp)

/-- **Sign reversal.**  Every target carries the opposite nonzero Möbius sign. -/
theorem markerBlockTargets_sign {σ : ℂ} (P : Finset ℕ) (C : ℕ → Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpos : ∀ p ∈ P, ∀ a ∈ C p, 0 < a)
    (hsmall : ∀ p ∈ P, ∀ a ∈ C p, ∀ r ∈ P, a < r)
    (hsign : ∀ p ∈ P, ∀ a ∈ C p, mobiusComplexCoefficient a = σ) :
    ∀ n ∈ markerBlockTargets P C, mobiusComplexCoefficient n = -σ := by
  classical
  intro n hn
  rw [markerBlockTargets] at hn
  obtain ⟨⟨p, a⟩, hx, rfl⟩ := Finset.mem_image.1 hn
  simp only [Finset.mem_sigma] at hx
  obtain ⟨hp, ha⟩ := hx
  rw [reciprocalMarker_target_sign_flip (hprime p hp) (hpos p hp a ha)
    (hsmall p hp a ha p hp), hsign p hp a ha]

/-- **Discarded markers.**  The reciprocal fibres over a set of bad starts are disjoint, so the
markers lost are at most the number of bad starts times the largest fibre. -/
theorem card_markers_start_mem_le (X A : ℕ) (hA : 1 ≤ A) (S : Finset ℕ) (hS : ∀ t ∈ S, A ≤ t) :
    ((#{p ∈ Finset.Icc 1 X | X / p ∈ S} : ℕ) : ℝ)
      ≤ (S.card : ℝ) * ((X : ℝ) / ((A : ℝ) * ((A : ℝ) + 1)) + 1) := by
  classical
  have hfib : ∀ p ∈ {p ∈ Finset.Icc 1 X | X / p ∈ S}, X / p ∈ S := by
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have hcard : (#{p ∈ Finset.Icc 1 X | X / p ∈ S})
      = ∑ t ∈ S, (#{p ∈ {p ∈ Finset.Icc 1 X | X / p ∈ S} | X / p = t}) :=
    Finset.card_eq_sum_card_fiberwise hfib
  have hstep : ∀ t ∈ S,
      ((#{p ∈ {p ∈ Finset.Icc 1 X | X / p ∈ S} | X / p = t} : ℕ) : ℝ)
        ≤ (X : ℝ) / ((A : ℝ) * ((A : ℝ) + 1)) + 1 := by
    intro t ht
    have htA : A ≤ t := hS t ht
    have ht1 : 1 ≤ t := le_trans hA htA
    have hsub : {p ∈ {p ∈ Finset.Icc 1 X | X / p ∈ S} | X / p = t}
        ⊆ {p ∈ Finset.Icc 1 X | X / p = t} := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hp1).1, hp2⟩
    have hmono : ((#{p ∈ {p ∈ Finset.Icc 1 X | X / p ∈ S} | X / p = t} : ℕ) : ℝ)
        ≤ ((#{p ∈ Finset.Icc 1 X | X / p = t} : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hbase := RHTower.Sieve.card_reciprocalFibre_le X t ht1
    have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have htR : (A : ℝ) ≤ (t : ℝ) := by exact_mod_cast htA
    have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
    have hden : (0 : ℝ) < (A : ℝ) * ((A : ℝ) + 1) := by nlinarith
    have hdiv : (X : ℝ) / ((t : ℝ) * ((t : ℝ) + 1)) ≤ (X : ℝ) / ((A : ℝ) * ((A : ℝ) + 1)) := by
      refine div_le_div_of_nonneg_left hXnn hden ?_
      nlinarith
    linarith
  have hsum : ((#{p ∈ Finset.Icc 1 X | X / p ∈ S} : ℕ) : ℝ)
      = ∑ t ∈ S, ((#{p ∈ {p ∈ Finset.Icc 1 X | X / p ∈ S} | X / p = t} : ℕ) : ℝ) := by
    rw [hcard]
    push_cast
    ring
  rw [hsum]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

end RHTower
