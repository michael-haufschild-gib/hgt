import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeReadsThePrimesCausally
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# The lattice selects the von Mangoldt weight

Run the lattice canonical system with an arbitrary prime weight `λ` in place of `Λ`
(`weilSeqW λ φ h`). The Weil cone is `{Λ}` under RH and empty otherwise (RHTower
`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`). In the language of growing windows:

* **Selection** (`lattice_selects_vonMangoldt`): the lattice evolutions of every bump at every step
  have positive margins for the weight `λ` iff RH holds and `λ = Λ` on `n ≥ 2`. Only one weight keeps
  every lattice of Spec ℤ from degenerating, and it does so exactly under RH.
* **Rigidity intervals collapse to a point** (`exists_lattice_failure_of_ne`): changing the weight of
  a single prime power `n₀` to any `t ≠ Λ(n₀)` makes some lattice margin nonpositive. Together with
  `posDef_update_iff`, no value other than `Λ(n₀)` lies in the admissible intervals of `n₀` at every
  lattice and stage.
* **Every kick is necessary; the free evolution fails** (`exists_lattice_failure_of_delete`,
  `exists_free_lattice_failure`): deleting one prime power, or all of them, makes some lattice
  degenerate. The archimedean place and the pole cannot sustain the evolution alone.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri

/-- Weights that agree on `n ≥ 2` have the same Weil sequences. -/
theorem weilSeqW_congr_weight {lam lam' : ℕ → ℝ} (hl : ∀ n, 2 ≤ n → lam n = lam' n)
    (φ : ℝ → ℝ) (h : ℝ) : weilSeqW lam φ h = weilSeqW lam' φ h := by
  funext d
  unfold weilSeqW
  rw [RHTower.weilFullFunctional_congr hl]

/-- The zero test has zero weighted Weil energy. -/
theorem weilFullFunctional_weilTest_zero (lam : ℕ → ℝ) :
    (RHTower.weilFullFunctional lam
      (EF.weilTest (fun u => ((0 : ℝ → ℝ) u : ℂ)) (fun u => ((0 : ℝ → ℝ) u : ℂ)))).re = 0 := by
  have hk : EF.weilTest (fun u => ((0 : ℝ → ℝ) u : ℂ)) (fun u => ((0 : ℝ → ℝ) u : ℂ)) =
      (0 : ℂ) • EF.weilTest (fun u => ((0 : ℝ → ℝ) u : ℂ)) (fun u => ((0 : ℝ → ℝ) u : ℂ)) := by
    funext x
    rw [RHTower.WeilSpectral.weilTest_apply]
    simp
  rw [hk, RHTower.WeilSpectral.weilFullFunctional_smul, zero_mul, Complex.zero_re]

/-- **The lattice selects `Λ`.** For a prime weight `λ`, all lattice margins of every nonzero bump at
every step are positive iff RH holds and `λ = Λ` on `n ≥ 2`. -/
theorem lattice_selects_vonMangoldt (lam : ℕ → ℝ) :
    (∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h → ∀ n : ℕ, 0 < levinsonErr (weilSeqW lam φ h) n) ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  constructor
  · intro hE
    rw [← RHTower.WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt]
    refine RHTower.WeilSpectral.weilPositiveFull_of_real fun g hg hgc => ?_
    by_cases hg0 : g = 0
    · subst hg0
      exact (weilFullFunctional_weilTest_zero lam).ge
    · have h0 := hE g ⟨hg, hgc⟩ hg0 1 one_pos 0
      rw [levinsonErr_zero, weilSeqW, latticeTranslate_zero] at h0
      exact h0.le
  · rintro ⟨hRH, hl⟩ φ hφ hφ0 h hh n
    rw [weilSeqW_congr_weight (lam' := fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hl]
    exact riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh n

/-- **Rigidity intervals collapse to a point.** Giving a single prime power `n₀` any weight
`t ≠ Λ(n₀)` makes some lattice margin of some bump at some step nonpositive. -/
theorem exists_lattice_failure_of_ne {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {t : ℝ}
    (ht : t ≠ ArithmeticFunction.vonMangoldt n₀) :
    ∃ φ ∈ realTests, φ ≠ 0 ∧ ∃ h : ℝ, 0 < h ∧ ∃ n : ℕ,
      levinsonErr (weilSeqW (Function.update (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n₀ t)
        φ h) n ≤ 0 := by
  by_contra hc
  push Not at hc
  have hsel := ((lattice_selects_vonMangoldt _).mp fun φ hφ hφ0 h hh n =>
    hc φ hφ hφ0 h hh n).2 n₀ hn₀
  rw [Function.update_self] at hsel
  exact ht hsel

/-- **Every kick is necessary.** Deleting a single prime power `n₀` (weight `0` there) makes some
lattice margin of some bump at some step nonpositive. -/
theorem exists_lattice_failure_of_delete {n₀ : ℕ} (hn₀ : IsPrimePow n₀) :
    ∃ φ ∈ realTests, φ ≠ 0 ∧ ∃ h : ℝ, 0 < h ∧ ∃ n : ℕ,
      levinsonErr (weilSeqW (Function.update (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) n₀ 0)
        φ h) n ≤ 0 :=
  exists_lattice_failure_of_ne hn₀.two_le
    (ArithmeticFunction.vonMangoldt_pos_iff.mpr hn₀).ne

/-- **The free evolution leaves the cone.** With every prime weight removed (archimedean place and
pole only), some lattice margin of some bump at some step is nonpositive. -/
theorem exists_free_lattice_failure :
    ∃ φ ∈ realTests, φ ≠ 0 ∧ ∃ h : ℝ, 0 < h ∧ ∃ n : ℕ, levinsonErr (weilSeqW (fun _ => 0) φ h) n ≤ 0 := by
  by_contra hc
  push Not at hc
  have hsel := ((lattice_selects_vonMangoldt _).mp fun φ hφ hφ0 h hh n =>
    hc φ hφ hφ0 h hh n).2 2 le_rfl
  have : (0 : ℝ) < ArithmeticFunction.vonMangoldt 2 :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr (Nat.prime_two.isPrimePow)
  linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
