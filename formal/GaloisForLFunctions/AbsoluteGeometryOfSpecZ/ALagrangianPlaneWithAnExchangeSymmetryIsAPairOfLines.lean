import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A Lagrangian plane with an exchange symmetry is a pair of lines

Let `V = ℂ²` and let `L ⊆ V × V` be a plane that is isotropic for
`ω((x, y), (x', y')) = ⟨y, x'⟩ − ⟨x, y'⟩` and invariant under the exchange of the two
coordinates in both factors. A pair `(x, y)` has **parity** `ε = ±1` if `x₁ = ε x₀` and
`y₁ = ε y₀` (`parityPairs`).

* The pairs of `L` of one parity form a space of dimension at most one
  (`finrank_inf_parityPairs_le_one`): two pairs `(s, t)`, `(s', t')` of one parity are isotropic
  iff `t̄ s' = s̄ t'`, and `t̄ s = s̄ t`, so they are proportional.
* `L` is the direct sum of its even part and its odd part, so each is a line
  (`finrank_inf_parityPairs_eq_one`).
-/

open Module
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

local notation "V₂" => EuclideanSpace ℂ (Fin 2)

/-- The pairs of parity `ε`: in both components the second coordinate is `ε` times the first. -/
def parityPairs (ε : ℂ) : Submodule ℂ (V₂ × V₂) where
  carrier := {p | p.1 1 = ε * p.1 0 ∧ p.2 1 = ε * p.2 0}
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · show p.1 1 + q.1 1 = ε * (p.1 0 + q.1 0)
      rw [h1, h1']
      ring
    · show p.2 1 + q.2 1 = ε * (p.2 0 + q.2 0)
      rw [h2, h2']
      ring
  zero_mem' := ⟨(mul_zero ε).symm, (mul_zero ε).symm⟩
  smul_mem' := by
    rintro c p ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show c * p.1 1 = ε * (c * p.1 0)
      rw [h1]
      ring
    · show c * p.2 1 = ε * (c * p.2 0)
      rw [h2]
      ring

theorem mem_parityPairs {ε : ℂ} {p : V₂ × V₂} :
    p ∈ parityPairs ε ↔ p.1 1 = ε * p.1 0 ∧ p.2 1 = ε * p.2 0 :=
  Iff.rfl

/-- A vector of `ℂ²` with both coordinates zero is zero. -/
theorem eq_zero_of_coords {x : V₂} (h0 : x 0 = 0) (h1 : x 1 = 0) : x = 0 := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Two isotropic pairs of one parity are proportional. -/
theorem exists_smul_eq_of_isotropic_parity {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {p q : V₂ × V₂}
    (hp : p ∈ parityPairs ε) (hq : q ∈ parityPairs ε) (hp0 : p ≠ 0)
    (hpp : ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ) (hpq : ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ) :
    ∃ c : ℂ, c • p = q := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  have hεε : (starRingEnd ℂ) ε * ε = 1 := by
    rcases hε with rfl | rfl
    · simp
    · simp
  -- the two isotropy relations in coordinates
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_two] at hpp hpq
  simp only [RCLike.inner_apply, hp1, hp2, hq1, hq2, map_mul] at hpp hpq
  have hpp' : (starRingEnd ℂ) (p.2 0) * p.1 0 = (starRingEnd ℂ) (p.1 0) * p.2 0 := by
    linear_combination (1 / 2 : ℂ) * hpp +
      (1 / 2 : ℂ) * ((starRingEnd ℂ) (p.1 0) * p.2 0 - (starRingEnd ℂ) (p.2 0) * p.1 0) *
        hεε
  have hpq' : (starRingEnd ℂ) (p.2 0) * q.1 0 = (starRingEnd ℂ) (p.1 0) * q.2 0 := by
    linear_combination (1 / 2 : ℂ) * hpq +
      (1 / 2 : ℂ) * ((starRingEnd ℂ) (p.1 0) * q.2 0 - (starRingEnd ℂ) (p.2 0) * q.1 0) *
        hεε
  -- the proportionality of the first coordinates extends to the pair
  have hext : ∀ c : ℂ, c * p.1 0 = q.1 0 → c * p.2 0 = q.2 0 → c • p = q := by
    intro c h1 h2
    refine Prod.ext ?_ ?_
    · ext i
      fin_cases i
      · exact h1
      · show c * p.1 1 = q.1 1
        rw [hp1, hq1, ← h1]
        ring
    · ext i
      fin_cases i
      · exact h2
      · show c * p.2 1 = q.2 1
        rw [hp2, hq2, ← h2]
        ring
  by_cases ht : p.2 0 = 0
  · have hs : p.1 0 ≠ 0 := by
      intro hs
      apply hp0
      refine Prod.ext (eq_zero_of_coords hs ?_) (eq_zero_of_coords ht ?_)
      · show p.1 1 = 0
        rw [hp1, hs, mul_zero]
      · show p.2 1 = 0
        rw [hp2, ht, mul_zero]
    have ht' : q.2 0 = 0 := by
      rw [ht, map_zero, zero_mul] at hpq'
      rcases mul_eq_zero.mp hpq'.symm with h | h
      · exact absurd ((map_eq_zero _).mp h) hs
      · exact h
    refine ⟨q.1 0 / p.1 0, hext _ (div_mul_cancel₀ _ hs) ?_⟩
    rw [ht, ht', mul_zero]
  · have hct : (starRingEnd ℂ) (p.2 0) ≠ 0 := fun h => ht ((map_eq_zero _).mp h)
    have hcross : (starRingEnd ℂ) (p.2 0) * (q.1 0 * p.2 0 - p.1 0 * q.2 0) = 0 := by
      linear_combination p.2 0 * hpq' - q.2 0 * hpp'
    have hcross' : q.1 0 * p.2 0 = p.1 0 * q.2 0 := by
      rcases mul_eq_zero.mp hcross with h | h
      · exact absurd h hct
      · exact sub_eq_zero.mp h
    refine ⟨q.2 0 / p.2 0, hext _ ?_ (div_mul_cancel₀ _ ht)⟩
    field_simp
    linear_combination -hcross'

variable {L : Submodule ℂ (V₂ × V₂)}

/-- **The pairs of one parity in an isotropic space form at most a line.** -/
theorem finrank_inf_parityPairs_le_one
    (hiso : ∀ p ∈ L, ∀ q ∈ L, ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) :
    finrank ℂ ↥(L ⊓ parityPairs ε) ≤ 1 := by
  rw [finrank_le_one_iff]
  by_cases h0 : ∃ p ∈ L ⊓ parityPairs ε, p ≠ 0
  · obtain ⟨p, hp, hp0⟩ := h0
    refine ⟨⟨p, hp⟩, fun w => ?_⟩
    obtain ⟨c, hc⟩ := exists_smul_eq_of_isotropic_parity hε hp.2 w.2.2 hp0
      (hiso p hp.1 p hp.1) (hiso p hp.1 w.1 w.2.1)
    exact ⟨c, Subtype.ext hc⟩
  · push Not at h0
    exact ⟨0, fun w => ⟨0, by rw [zero_smul]; exact Subtype.ext (h0 w.1 w.2).symm⟩⟩

/-- **An isotropic plane with the exchange symmetry is the sum of an even line and an odd
line.** -/
theorem finrank_inf_parityPairs_eq_one
    (hiso : ∀ p ∈ L, ∀ q ∈ L, ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ)
    (hswap : ∀ p ∈ L, ∃ q ∈ L, q.1 0 = p.1 1 ∧ q.1 1 = p.1 0 ∧ q.2 0 = p.2 1 ∧ q.2 1 = p.2 0)
    (hdim : finrank ℂ L = 2) :
    finrank ℂ ↥(L ⊓ parityPairs 1) = 1 ∧ finrank ℂ ↥(L ⊓ parityPairs (-1)) = 1 := by
  have h1 := finrank_inf_parityPairs_le_one hiso (ε := 1) (Or.inl rfl)
  have h2 := finrank_inf_parityPairs_le_one hiso (ε := -1) (Or.inr rfl)
  have hdisj : (L ⊓ parityPairs 1) ⊓ (L ⊓ parityPairs (-1)) = ⊥ := by
    rw [eq_bot_iff]
    rintro p ⟨⟨-, ha1, ha2⟩, ⟨-, hb1, hb2⟩⟩
    rw [Submodule.mem_bot]
    have hs : p.1 0 = 0 := by linear_combination (1 / 2 : ℂ) * hb1 - (1 / 2 : ℂ) * ha1
    have ht : p.2 0 = 0 := by linear_combination (1 / 2 : ℂ) * hb2 - (1 / 2 : ℂ) * ha2
    refine Prod.ext (eq_zero_of_coords hs ?_) (eq_zero_of_coords ht ?_)
    · show p.1 1 = 0
      rw [ha1, hs, mul_zero]
    · show p.2 1 = 0
      rw [ha2, ht, mul_zero]
  have hsup : L ≤ (L ⊓ parityPairs 1) ⊔ (L ⊓ parityPairs (-1)) := by
    intro p hp
    obtain ⟨q, hq, h10, h11, h20, h21⟩ := hswap p hp
    rw [Submodule.mem_sup]
    refine ⟨(2 : ℂ)⁻¹ • (p + q), ⟨L.smul_mem _ (L.add_mem hp hq), ?_, ?_⟩,
      (2 : ℂ)⁻¹ • (p - q), ⟨L.smul_mem _ (L.sub_mem hp hq), ?_, ?_⟩, ?_⟩
    · show (2 : ℂ)⁻¹ * (p.1 1 + q.1 1) = 1 * ((2 : ℂ)⁻¹ * (p.1 0 + q.1 0))
      rw [h10, h11]
      ring
    · show (2 : ℂ)⁻¹ * (p.2 1 + q.2 1) = 1 * ((2 : ℂ)⁻¹ * (p.2 0 + q.2 0))
      rw [h20, h21]
      ring
    · show (2 : ℂ)⁻¹ * (p.1 1 - q.1 1) = -1 * ((2 : ℂ)⁻¹ * (p.1 0 - q.1 0))
      rw [h10, h11]
      ring
    · show (2 : ℂ)⁻¹ * (p.2 1 - q.2 1) = -1 * ((2 : ℂ)⁻¹ * (p.2 0 - q.2 0))
      rw [h20, h21]
      ring
    · rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ p, smul_smul,
        inv_mul_cancel₀ (two_ne_zero), one_smul]
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (L ⊓ parityPairs 1)
    (L ⊓ parityPairs (-1))
  rw [hdisj, finrank_bot, add_zero] at hfin
  have hle := Submodule.finrank_mono hsup
  omega

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
