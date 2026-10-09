import GaloisForLFunctions.RHTower.ComplexFugacityChainDatum
import GaloisForLFunctions.RHTower.LeeYangProducerFieldDensity

/-!
# Field density of complex-fugacity chain producers of Ξ

A family of complex-fugacity chains (`cChainDatum`) whose normalised partition functions converge
locally uniformly to `E·Ξ` (`E` entire and zero-free) must eventually satisfy the field-density
bound `Σ_j max(λ_j − 2π/T, 0) ≤ (2π/T) N_Ξ(T + η)`.  The chains are multi-affine Lee–Yang data
(`degreeOf_cChainPoly`), so this is an instance of
`LeeYangCount.eventually_fieldDensity_le_xiZeroCount`.

With harmonic fields the left side is `(T/2π)·(log(T/2π) + O(1))`-sized and saturates Ξ's count to
leading order, so every chain producer of Ξ has harmonic-or-sparser field density.
-/

open Complex Metric Set Filter Topology

namespace RHTower.LeeYangChain

/-- The chain partition function with exponential fields of frequencies `freq`. -/
noncomputable def cChainRestr (N : ℕ) (α : ℕ → ℂ) (freq : Fin (N + 1) → ℝ) (z : ℂ) : ℂ :=
  cChainZ α (chainExt N fun j => Complex.exp (-(I * (freq j : ℂ) * z))) N

theorem cChainDatum_restr (N : ℕ) (α : ℕ → ℂ) (hα : ∀ k, ‖α k‖ ≤ 1)
    (freq : Fin (N + 1) → ℝ) (hfreq : ∀ j, 0 < freq j) (z : ℂ) :
    (cChainDatum N α hα freq hfreq).restr z = cChainRestr N α freq z := by
  rw [LeeYangCount.LeeYangDatum.restr, cChainRestr]
  exact eval_cChainPoly N α _

/-- **Field-density law for chain producers of Ξ.** -/
theorem eventually_fieldDensity_le_xiZeroCount_cChain {β : Type*} {p : Filter β}
    (N : β → ℕ) (α : β → ℕ → ℂ) (hα : ∀ b k, ‖α b k‖ ≤ 1)
    (freq : ∀ b, Fin (N b + 1) → ℝ) (hfreq : ∀ b j, 0 < freq b j)
    (κ : β → ℂ) (hκ : ∀ b, κ b ≠ 0) {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hEne : ∀ z, E z ≠ 0)
    (hconv : TendstoLocallyUniformly (fun b z => κ b * cChainRestr (N b) (α b) (freq b) z)
      (fun z => E z * XiC z) p)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), E z * XiC z ≠ 0) :
    ∀ᶠ b in p, ∑ j, max (freq b j - 2 * Real.pi / T) 0 ≤
      2 * Real.pi / T * (xiZeroCount (T + η) : ℝ) := by
  have h := LeeYangCount.eventually_fieldDensity_le_xiZeroCount
    (fun b => cChainDatum (N b) (α b) (hα b) (freq b) (hfreq b))
    (fun b j => cChainDatum_degreeOf (N b) (α b) (hα b) (freq b) (hfreq b) j) κ hκ hE hEne
    (by simpa only [cChainDatum_restr] using hconv) hT hη hη1 hsph
  exact h

/-- **Γ-density form.** Chain producers of Ξ eventually have
`Σ_j max(λ_j − 2π/T, 0) ≤ log(T/2π) − 1 + C/√T` for `T ≥ 4`.  With harmonic fields `λ_j = 1/j` the
left side is `log(T/2π) + γ − H_{J₀−1} − 1 + O(1/T)`, so a harmonic chain must start at `J₀ ≥ 2`. -/
theorem exists_eventually_fieldDensity_le_gammaDensity_cChain : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {β : Type*} {p : Filter β} (N : β → ℕ) (α : β → ℕ → ℂ), (∀ b k, ‖α b k‖ ≤ 1) →
      ∀ (freq : ∀ b, Fin (N b + 1) → ℝ), (∀ b j, 0 < freq b j) → ∀ (κ : β → ℂ),
      (∀ b, κ b ≠ 0) → ∀ {E : ℂ → ℂ}, Differentiable ℂ E → (∀ z, E z ≠ 0) →
      TendstoLocallyUniformly (fun b z => κ b * cChainRestr (N b) (α b) (freq b) z)
        (fun z => E z * XiC z) p →
      ∀ {T η : ℝ}, 4 ≤ T → 0 < η → η ≤ 1 →
      (∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), E z * XiC z ≠ 0) →
      ∀ᶠ b in p, ∑ j, max (freq b j - 2 * Real.pi / T) 0 ≤
        Real.log (T / (2 * Real.pi)) - 1 + C / Real.sqrt T := by
  obtain ⟨C, hC, h⟩ := LeeYangCount.exists_eventually_fieldDensity_le_gammaDensity
  refine ⟨C, hC, fun N α hα freq hfreq κ hκ E hE hEne hconv T η hT hη hη1 hsph => ?_⟩
  exact h (fun b => cChainDatum (N b) (α b) (hα b) (freq b) (hfreq b))
    (fun b j => cChainDatum_degreeOf (N b) (α b) (hα b) (freq b) (hfreq b) j) κ hκ hE hEne
    (by simpa only [cChainDatum_restr] using hconv) hT hη hη1 hsph

end RHTower.LeeYangChain
