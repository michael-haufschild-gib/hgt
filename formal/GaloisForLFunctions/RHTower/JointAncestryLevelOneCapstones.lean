import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochnerLevel
import GaloisForLFunctions.RHTower.JointAncestryWeilEulerProducerLaw

/-!
# The JAS capstones without side conditions

The diagonal Bochner bound (`abs_re_sub_half_le_of_jasProductPositiveAbove`) removes the quasi-RH
and no-chain hypotheses from every JAS capstone.  RH is equivalent to each of:
* full dressed positive semidefiniteness at level `1` (`riemannHypothesis_iff_jasDressedPSD_one`);
* dressed PSD on the characters of all large primes at level `1`
  (`riemannHypothesis_iff_exists_jasDressedPSDAbove_one`);
* cosine-kernel positivity on large primes at level `1`
  (`riemannHypothesis_iff_exists_jasCosinePositiveAbove_one`);
* Weil positivity on harmonic Euler vectors of large primes
  (`riemannHypothesis_iff_exists_weilEulerPositiveAbove_one`);
* PSD at infinity at every level `σ > 1` (`riemannHypothesis_iff_forall_gt_one_jasDressedPSDAtInfinity`).

Under positivity at a level `σ ∈ [1, 3/2]` alone, every zero has `Re ρ ≤ σ − ½`
(`xiZeroHalfPlaneBound_of_jasDressedPSDAbove`).
-/

namespace RHTower

noncomputable section

theorem xiZeroHalfPlaneBound_of_jasDressedPSDAbove {X : ℕ} {σ : ℝ} (h : JasDressedPSDAbove X σ)
    (hσ : 1 ≤ σ) : XiZeroHalfPlaneBound (σ - 1) :=
  xiZeroHalfPlaneBound_of_jasProductPositiveAbove h.productPositive hσ

theorem riemannHypothesis_of_jasDressedPSDAbove {X : ℕ} {σ : ℝ} (h : JasDressedPSDAbove X σ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : RiemannHypothesis :=
  riemannHypothesis_of_jasProductPositiveAbove h.productPositive hσ0 hσ1

/-- **RH ⟺ dressed PSD at level `1`.** -/
theorem riemannHypothesis_iff_jasDressedPSD_one : RiemannHypothesis ↔ JasDressedPSD 1 :=
  ⟨fun hRH => (jasDressedPSD_zero_of_riemannHypothesis hRH).mono (by norm_num),
    fun h => riemannHypothesis_of_jasDressedPSDAbove (h.above 0) (by norm_num) le_rfl⟩

/-- **RH ⟺ dressed PSD on large primes at level `1`.** -/
theorem riemannHypothesis_iff_exists_jasDressedPSDAbove_one :
    RiemannHypothesis ↔ ∃ X : ℕ, JasDressedPSDAbove X 1 :=
  ⟨fun hRH => ⟨0, (riemannHypothesis_iff_jasDressedPSD_one.mp hRH).above 0⟩,
    fun ⟨_, h⟩ => riemannHypothesis_of_jasDressedPSDAbove h (by norm_num) le_rfl⟩

/-- **RH ⟺ cosine-kernel positivity on large primes at level `1`.** -/
theorem riemannHypothesis_iff_exists_jasCosinePositiveAbove_one :
    RiemannHypothesis ↔ ∃ X : ℕ, JasCosinePositiveAbove X 1 := by
  rw [riemannHypothesis_iff_exists_jasProductPositiveAbove_one]
  exact exists_congr fun _ => jasProductPositiveAbove_iff_jasCosinePositiveAbove

/-- **RH ⟺ Weil positivity on harmonic Euler vectors of large primes.** -/
theorem riemannHypothesis_iff_exists_weilEulerPositiveAbove_one :
    RiemannHypothesis ↔ ∃ X : ℕ, WeilEulerPositiveAbove X 1 := by
  rw [riemannHypothesis_iff_exists_jasDressedPSDAbove_one]
  exact exists_congr fun _ => jasDressedPSDAbove_iff_weilEulerPositiveAbove (by norm_num)

/-- **RH ⟺ PSD at infinity at every level above `1`.**  Each level `σ > 1` gives the half-plane
`σ − 1`; their intersection is the critical line. -/
theorem riemannHypothesis_iff_forall_gt_one_jasDressedPSDAtInfinity :
    RiemannHypothesis ↔ ∀ σ : ℝ, 1 < σ → JasDressedPSDAtInfinity σ := by
  constructor
  · intro hRH σ hσ
    exact forall_jasDressedPSDAtInfinity_of_riemannHypothesis hRH (by linarith)
  · intro h
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨X, hX⟩ := h (1 + ε) (by linarith)
    have := xiZeroHalfPlaneBound_of_jasDressedPSDAbove hX (by linarith) ρ hρ
    linarith

end

end RHTower
