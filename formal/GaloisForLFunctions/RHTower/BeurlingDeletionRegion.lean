import GaloisForLFunctions.RHTower.BeurlingPerronRegion
import GaloisForLFunctions.RHTower.BeurlingDeletionSawtooth

/-!
# Prime-deletion Beurling systems: the full region `β > β₀(α)`

Assume RH.  For every `1/2 < α < 4/5` and every `β₀(α) < β < 1/2`, where
`β₀(α) = 3α/(α + 4)` for `α ≤ 2/3` and `β₀(α) = 1/(3 − α)` for `α ≥ 2/3`, there is an
`[α, β]`-system (`exists_isAlphaBetaSystem_of_betaZero_lt`).

* **The sawtooth region** (`exists_isAlphaBetaSystem_of_sawtooth`).  The integers free of the
  deleted primes satisfy `N'(x) = a' x + O(x^{3α/(α+4) + η})` (`exists_norm_count_sub_le_saw`): the
  sawtooth assembly gives `N'(x) = A x + O(x^{3α/(α+4) + 5ε})` with `A = Σ μ_S(m)/m`, and `A` equals
  the Perron density `a'` because two asymptotics with exponents below `1` share their main term.
* **The Perron region** (`exists_isAlphaBetaSystem_of_perron`) covers `β > 1/(3 − α)`.
* **Comparisons** (`sawtooth_lt_perron_iff`, `sawtooth_lt_half_iff`, `perron_lt_hyperbola`).
  `3α/(α+4) < 1/(3 − α)` iff `α < 2/3`; `3α/(α+4) < 1/2` iff `α < 4/5`; and
  `1/(3 − α) < 2α/(α + 2)` on `(1/2, 1)`, the hyperbola exponent of Broucke–Debruyne–Révész.
-/

open Complex Finset Filter Topology Real

noncomputable section

namespace RHTower.BeurlingDeletion

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

theorem norm_count_le (X : ℝ) (hX : 0 ≤ X) : ‖D.count X‖ ≤ X + 1 := by
  unfold count
  calc ‖∑ n ∈ Finset.Iic ⌊X⌋₊, D.sFreeInd n‖ ≤ ∑ n ∈ Finset.Iic ⌊X⌋₊, ‖D.sFreeInd n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Iic ⌊X⌋₊, (1 : ℝ) := Finset.sum_le_sum fun n _ => D.norm_sFreeInd_le n
    _ = (⌊X⌋₊ : ℝ) + 1 := by simp
    _ ≤ X + 1 := by linarith [Nat.floor_le hX]

/-- **The sawtooth asymptotic.**  Under RH, `N'(x) = a' x + O(x^{3α/(α+4) + η})`. -/
theorem exists_norm_count_sub_le_saw (hRH : RiemannHypothesis) (hα1 : 1 / 2 < α) (hα : α < 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      ‖D.count X - D.density * X‖ ≤ C * X ^ (3 * α / (α + 4) + η) := by
  have hα0 : 0 < α := by linarith
  set ε := min (η / 5) (1 / 20) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε5 : ε ≤ η / 5 := min_le_left _ _
  have hε20 : ε ≤ 1 / 20 := min_le_right _ _
  obtain ⟨CM, hCM⟩ := D.exists_norm_sum_mobS_le hRH hα0 hα (η := ε) hε
  have hCM0 : 0 ≤ CM := by
    have := (norm_nonneg _).trans (hCM 1 le_rfl); simpa using this
  obtain ⟨CA, hCA0, hCA⟩ := D.exists_norm_mainSum_sub_le hRH hα0 hα hε (by linarith)
  obtain ⟨KB, hKB0, hKB⟩ := D.exists_norm_block_le hRH hα1 hα hε (by linarith)
  set C₁ := CA + 2 * CM + 2 * Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(α + ε))) n) +
    4 * KB * (1 / (2 * ε * Real.log 2) + 1) + 2 * CM / (1 - (α / 2 + ε)) with hC₁
  set X₀ := (8 : ℝ) ^ ((α + 4) / α) with hX₀
  have hX₀1 : 1 ≤ X₀ := Real.one_le_rpow (by norm_num) (by positivity)
  have hbig : ∀ X : ℝ, X₀ ≤ X →
      ‖D.count X - D.mobSum * X‖ ≤ C₁ * X ^ (3 * α / (α + 4) + 5 * ε) := fun X hX =>
    D.norm_count_sub_mobSum_le hα1 hα hε (by linarith) hCM0 hCA0 hKB0 hCM hCA hKB hX
  -- the main term is the Perron density
  set η' := (1 - 1 / (3 - α)) / 2 with hη'
  have h3 : 1 / (3 - α) < 1 / 2 := by rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hη'0 : 0 < η' := by rw [hη']; linarith
  obtain ⟨CP, hCP⟩ := D.exists_norm_count_sub_le hRH hα0 hα hη'0
  set e₁ := 3 * α / (α + 4) + 5 * ε with he₁
  set e₂ := 1 / (3 - α) + η' with he₂
  have he₁1 : e₁ < 1 := by
    have : 3 * α / (α + 4) < 3 / 5 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    rw [he₁]; linarith
  have he₂1 : e₂ < 1 := by rw [he₂, hη']; linarith
  have hdens : D.mobSum = D.density := by
    have hle : ∀ X : ℝ, max X₀ 1 ≤ X →
        ‖D.mobSum - D.density‖ ≤ C₁ * X ^ (e₁ - 1) + CP * X ^ (e₂ - 1) := by
      intro X hX
      have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
      have hX0 : 0 < X := by linarith
      have h1 := hbig X (le_trans (le_max_left _ _) hX)
      have h2 := hCP X hX1
      have hsum : ‖(D.mobSum - D.density) * X‖ ≤ C₁ * X ^ e₁ + CP * X ^ e₂ := by
        calc ‖(D.mobSum - D.density) * X‖ =
            ‖(D.count X - D.density * X) - (D.count X - D.mobSum * X)‖ := by congr 1; ring
          _ ≤ ‖D.count X - D.density * X‖ + ‖D.count X - D.mobSum * X‖ := norm_sub_le _ _
          _ ≤ CP * X ^ e₂ + C₁ * X ^ e₁ := add_le_add h2 h1
          _ = _ := by ring
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0] at hsum
      rw [Real.rpow_sub hX0, Real.rpow_sub hX0, Real.rpow_one]
      calc ‖D.mobSum - D.density‖ ≤ (C₁ * X ^ e₁ + CP * X ^ e₂) / X := (le_div_iff₀ hX0).mpr hsum
        _ = _ := by ring
    have hlim : Tendsto (fun X : ℝ => C₁ * X ^ (e₁ - 1) + CP * X ^ (e₂ - 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun X : ℝ => X ^ (e₁ - 1)) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := 1 - e₁) (by linarith)
        simpa [neg_sub] using this
      have h2 : Tendsto (fun X : ℝ => X ^ (e₂ - 1)) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := 1 - e₂) (by linarith)
        simpa [neg_sub] using this
      simpa using (h1.const_mul C₁).add (h2.const_mul CP)
    have h0 : ‖D.mobSum - D.density‖ ≤ 0 :=
      ge_of_tendsto hlim ((eventually_ge_atTop (max X₀ 1)).mono fun X hX => hle X hX)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  -- the bound for all `X ≥ 1`
  refine ⟨max C₁ ((2 + ‖D.density‖) * X₀), fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hpow : 1 ≤ X ^ (3 * α / (α + 4) + η) := Real.one_le_rpow hX (by positivity)
  by_cases hXX : X₀ ≤ X
  · calc ‖D.count X - D.density * X‖ = ‖D.count X - D.mobSum * X‖ := by rw [hdens]
      _ ≤ C₁ * X ^ (3 * α / (α + 4) + 5 * ε) := hbig X hXX
      _ ≤ C₁ * X ^ (3 * α / (α + 4) + η) := by
          have hC₁0 : 0 ≤ C₁ := by
            have := (norm_nonneg _).trans (hbig X hXX)
            exact nonneg_of_mul_nonneg_left this (by positivity)
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hC₁0
      _ ≤ max C₁ ((2 + ‖D.density‖) * X₀) * X ^ (3 * α / (α + 4) + η) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · push Not at hXX
    calc ‖D.count X - D.density * X‖ ≤ ‖D.count X‖ + ‖D.density * X‖ := norm_sub_le _ _
      _ ≤ (X + 1) + ‖D.density‖ * X := by
          refine add_le_add (D.norm_count_le X hX0.le) (le_of_eq ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
      _ ≤ (2 + ‖D.density‖) * X₀ := by nlinarith [norm_nonneg D.density]
      _ ≤ (2 + ‖D.density‖) * X₀ * X ^ (3 * α / (α + 4) + η) :=
          le_mul_of_one_le_right (by positivity) hpow
      _ ≤ max C₁ ((2 + ‖D.density‖) * X₀) * X ^ (3 * α / (α + 4) + η) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end DeletionData

/-- **The sawtooth region.**  Under RH, for `1/2 < α < 1` and `3α/(α + 4) < β < 1/2` there is an
`[α, β]`-system. -/
theorem exists_isAlphaBetaSystem_of_sawtooth (hRH : RiemannHypothesis) {α β : ℝ}
    (hα1 : 1 / 2 < α) (hα : α < 1) (hβ0 : 3 * α / (α + 4) < β) (hβ1 : β < 1 / 2) :
    ∃ B : BeurlingSystem, B.IsAlphaBetaSystem α β := by
  have hα0 : 0 < α := by linarith
  obtain ⟨D⟩ := exists_deletionData hα0 hα
  have hthr : 0 < 3 * α / (α + 4) := by positivity
  set γ : ℝ := (3 * α / (α + 4) + β) / 2 with hγ
  have hβpos : 0 < β := by linarith
  have hαβ : α / 2 < β := by
    have : α / 2 < 3 * α / (α + 4) := by
      rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    linarith
  obtain ⟨C, hC⟩ := D.exists_norm_count_sub_le_saw hRH hα1 hα (η := γ - 3 * α / (α + 4))
    (by linarith)
  refine ⟨deletionSystem D.S β hβpos, isAlphaBetaSystem_of_count hRH hα1 hα D hβpos hβ1 hαβ
    (by linarith) (by linarith) ⟨C, fun X hX => ?_⟩⟩
  have := hC X hX
  rwa [show 3 * α / (α + 4) + (γ - 3 * α / (α + 4)) = γ by ring] at this

/-- The threshold `β₀(α)`: `3α/(α+4)` for `α ≤ 2/3`, `1/(3 − α)` for `α ≥ 2/3`. -/
def betaZero (α : ℝ) : ℝ := if α ≤ 2 / 3 then 3 * α / (α + 4) else 1 / (3 - α)

/-- `3α/(α + 4) < 1/(3 − α)` iff `α < 2/3`, on `0 < α < 1`. -/
theorem sawtooth_lt_perron_iff {α : ℝ} (hα0 : 0 < α) (hα : α < 1) :
    3 * α / (α + 4) < 1 / (3 - α) ↔ α < 2 / 3 := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- `β₀(α) = min(3α/(α + 4), 1/(3 − α))` on `(0, 1)`. -/
theorem betaZero_eq_min {α : ℝ} (hα0 : 0 < α) (hα : α < 1) :
    betaZero α = min (3 * α / (α + 4)) (1 / (3 - α)) := by
  unfold betaZero
  split_ifs with h
  · rcases h.lt_or_eq with h' | h'
    · exact (min_eq_left ((sawtooth_lt_perron_iff hα0 hα).mpr h').le).symm
    · subst h'; norm_num
  · push Not at h
    refine (min_eq_right ?_).symm
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- `3α/(α + 4) < 1/2` iff `α < 4/5`. -/
theorem sawtooth_lt_half_iff {α : ℝ} (hα0 : 0 < α) : 3 * α / (α + 4) < 1 / 2 ↔ α < 4 / 5 := by
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  constructor <;> intro h <;> linarith

/-- `1/(3 − α) < 1/2` for `α < 1`. -/
theorem perron_lt_half {α : ℝ} (hα : α < 1) : 1 / (3 - α) < 1 / 2 := by
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith

/-- The small range is never the bottleneck: `α/(1 + α) < 3α/(α + 4)` for `α > 1/2`. -/
theorem small_lt_sawtooth {α : ℝ} (hα1 : 1 / 2 < α) : α / (1 + α) < 3 * α / (α + 4) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith

/-- `1/(3 − α) < 2α/(α + 2)` on `(1/2, 1)`: the Perron exponent beats the hyperbola exponent. -/
theorem perron_lt_hyperbola {α : ℝ} (hα1 : 1 / 2 < α) (hα : α < 1) :
    1 / (3 - α) < 2 * α / (α + 2) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The Perron region.**  Under RH, for every `1/2 < α < 4/5` and `β₀(α) < β < 1/2` there is an
`[α, β]`-system: a discrete Beurling system with `ψ(x) = x + O(x^{α+ε})`, `N(x) = a x + O(x^{β+ε})`,
neither exponent improvable. -/
theorem exists_isAlphaBetaSystem_of_betaZero_lt (hRH : RiemannHypothesis) {α β : ℝ}
    (hα1 : 1 / 2 < α) (hα : α < 4 / 5) (hβ0 : betaZero α < β) (hβ1 : β < 1 / 2) :
    ∃ B : BeurlingSystem, B.IsAlphaBetaSystem α β := by
  have hα' : α < 1 := by linarith
  unfold betaZero at hβ0
  split_ifs at hβ0 with h
  · exact exists_isAlphaBetaSystem_of_sawtooth hRH hα1 hα' hβ0 hβ1
  · exact exists_isAlphaBetaSystem_of_perron hRH hα1 hα' hβ0 hβ1

end RHTower.BeurlingDeletion
