import GaloisForLFunctions.HTGeometry.RittLevelTwoClassification
import GaloisForLFunctions.HTGeometry.RittLevelTwoReduction

/-!
# The trichotomy forced by a collapse of the jet tower

Combining the monotone descent — which reduces a collapse to a relation over the first two jets whose
multiplier is a nontrivial monomial in `q` and `ρ` — with the classification at jet orders zero, one
and two.  Exactly three things can happen:

* the base carries **Ritt's order-one form**, `ψ(u) = q^I ρ^J·u` with `(I,J) ≠ (0,0)` and `u ≠ 0`;
* the base carries an **affine transport equation** `ψ(u) = c'·u + h` with `h ≠ 0`;
* the surviving relation is solved by a **monomial** `κ·τ^{e₀}(dτ)^{e₁}` with `κ` shift-fixed and
  the multiplier exactly `q^{e₀+e₁}ρ^{−e₁}` — the tautology `σ(τ^{e₀}(dτ)^{e₁}) = q^{e₀+e₁}ρ^{−e₁}·τ^{e₀}(dτ)^{e₁}`.

The first two are refuted for a rational map with no cocycle and no affine connection.  The third is
a genuine solution of the abstract relation and is the remaining content of Ritt's classification.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- **The trichotomy forced by a collapse of the jet tower.** -/
theorem ritt_affine_or_monomial_of_collapse (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ)) {n : ℕ}
    (htr : ∀ j, j < n → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ))
    (W : L) (A : ℕ → K) (hW0 : W ≠ 0) (hWmem : W ∈ Fr.jetPrefixField τ n)
    (hrel : Fr.σ W = algebraMap K L (q / Fr.ρ ^ n) * W
        + ∑ j ∈ Finset.range n, algebraMap K L (A j) * Fr.d^[j] τ) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u c' h : K), u ≠ 0 ∧ c' ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ u = c' * u + h) ∨
    (∃ (V : L) (κ : K) (e₀ e₁ : ℤ), V ≠ 0 ∧ κ ≠ 0 ∧ Fr.ψ κ = κ ∧
      V = algebraMap K L κ * τ ^ e₀ * (Fr.d τ) ^ e₁ ∧
      Fr.σ V = algebraMap K L (q ^ (e₀ + e₁) * Fr.ρ ^ (-e₁)) * V) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  obtain ⟨n', V, c', g', A', i', k', hn'2, hV0, hVmem, hc'0, hc'ik, hpair, hVrel⟩ :=
    exists_nontrivial_level_two_relation Fr hqconst hshift hq hdρ htr W A hW0 hWmem hrel
  interval_cases n'
  · -- the relation is already in the base
    have hbot : Fr.jetPrefixField τ 0 = (⊥ : IntermediateField K L) := by
      rw [RittFrame.jetPrefixField,
        show {x : L | ∃ j < 0, x = Fr.d^[j] τ} = (∅ : Set L) by ext x; simp]
      exact IntermediateField.adjoin_empty K L
    rw [hbot, IntermediateField.mem_bot] at hVmem
    obtain ⟨u, hu⟩ := hVmem
    have hu0 : u ≠ 0 := fun h => hV0 (by rw [← hu, h, map_zero])
    have hbase : Fr.ψ u = c' * u + g' := by
      refine (algebraMap K L).injective ?_
      rw [map_add, map_mul, ← Fr.comp, hu]
      simpa using hVrel
    by_cases hg : g' = 0
    · refine Or.inl ⟨u, i', k', hu0, hpair, ?_⟩
      rw [hbase, hg, add_zero, hc'ik]
    · exact Or.inr (Or.inl ⟨u, c', g', hu0, hc'0, hg, hbase⟩)
  · -- the relation is over the first jet
    have hVrel' : Fr.σ V = algebraMap K L c' * V
        + (algebraMap K L (A' 0) * τ + algebraMap K L g') := by
      rw [hVrel, Finset.sum_range_one]
      simp only [Function.iterate_zero_apply]
      ring
    rcases level_one_classification Fr hq hshift htr0 hV0 hVmem hc'0 hVrel' with
        ⟨w, s, hw0, hs0, hweq⟩ | ⟨w, s, h, hw0, hh0, -, hweq⟩ |
        ⟨u, j, hu0, hα1, hβ1, hVeq, hueq⟩
    · exact Or.inl ⟨w, s, 0, hw0, (by rintro ⟨hh, -⟩; exact hs0 hh), by rw [hweq]; simp⟩
    · exact Or.inr (Or.inl ⟨w, q ^ s * c', h, hw0,
        mul_ne_zero (zpow_ne_zero _ hq) hc'0, hh0, hweq⟩)
    · have hval : q ^ (-j) * c' = q ^ (i' - j) * Fr.ρ ^ k' := by
        rw [hc'ik, show i' - j = i' + (-j) by ring, zpow_add₀ hq]
        ring
      by_cases htriv : i' - j = 0 ∧ k' = 0
      · refine Or.inr (Or.inr ⟨V, u, j, 0, hV0, hu0, ?_, ?_, ?_⟩)
        · rw [hueq, hval, htriv.1, htriv.2, zpow_zero, zpow_zero, one_mul, one_mul]
        · rw [hVeq, zpow_zero, mul_one]
        · have hz : Fr.σ V = algebraMap K L c' * V := by
            rw [hVrel', hα1, hβ1]
            simp
          have hij : i' = j := by omega
          have hscal : c' = q ^ (j + (0 : ℤ)) * Fr.ρ ^ (-(0 : ℤ)) := by
            rw [hc'ik, htriv.2, hij, add_zero, neg_zero, zpow_zero, mul_one]
          rw [hz, hscal]
      · exact Or.inl ⟨u, i' - j, k', hu0, htriv, by rw [hueq, hval]⟩
  · -- the relation is over the first two jets
    have hVrel' : Fr.σ V = algebraMap K L c' * V
        + (algebraMap K L (A' 1) * Fr.d τ
          + (algebraMap K L (A' 0) * τ + algebraMap K L g')) := by
      rw [hVrel, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Function.iterate_zero_apply, Function.iterate_one]
      ring
    rcases level_two_classification Fr hqconst hshift hq htr0 htr1 hV0 hVmem hc'0 hc'ik hVrel'
      with hritt | haff | ⟨κ, e₀, e₁, hκ0, hκfix, hαz, hβz, hgz, hVeq, hi, hk⟩
    · exact Or.inl hritt
    · exact Or.inr (Or.inl haff.2)
    · refine Or.inr (Or.inr ⟨V, κ, e₀, e₁, hV0, hκ0, hκfix, hVeq, ?_⟩)
      have hz : Fr.σ V = algebraMap K L c' * V := by
        rw [hVrel', hαz, hβz, hgz]
        simp
      have hscal : c' = q ^ (e₀ + e₁) * Fr.ρ ^ (-e₁) := by rw [hc'ik, hi, hk]
      rw [hz, hscal]

end GaloisForLFunctions.HTGeometry
