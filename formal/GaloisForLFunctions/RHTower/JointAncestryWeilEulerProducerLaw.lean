import GaloisForLFunctions.RHTower.JointAncestryLargePrimeAttainment
import GaloisForLFunctions.RHTower.JointAncestryPositivityAtInfinity

/-!
# The large-prime producer law in Weil form

`WeilEulerPositiveAbove X σ` says that Weil's lag form `Σ_{m,n} c_m c̄_n Φ(log n − log m)` is
nonnegative on every Euler vector `c_m = e_w(m) m^{−σ}` built from a finite set of primes `p > X`
and a unimodular `w`.  For `σ > ½` it is the same as large-prime JAS positivity
(`jasDressedPSDAbove_iff_weilEulerPositiveAbove`), so the large-prime producer theory transfers:

* one `X` gives Weil positivity at every exponent `σ ≥ 3/2`
  (`exists_weilEulerPositiveAbove_three_halves`);
* Weil positivity on large-prime Euler vectors at an exponent `σ ≥ 1` forces the zero-free strip
  `|Re ρ − ½| ≤ σ − 1`, unless `sup |Re ρ − ½| = ½` (`weilEuler_zeroFree_or_edge`);
* RH holds iff Weil positivity holds on large-prime harmonic Euler vectors (exponent `1`) and some
  half-plane bound below `½` holds (`riemannHypothesis_iff_weilEulerPositiveAbove_one_and_quasi`).
-/

open Complex

namespace RHTower

noncomputable section

/-- Weil positivity on every Euler vector `m ↦ e_w(m) m^{−σ}` over a finite set of primes `> X`. -/
def WeilEulerPositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → ∀ w : ↥P → ℂ, (∀ i, ‖w i‖ = 1) →
    0 ≤ (weilEulerForm P w σ).re

theorem jasDressedPSDAbove_iff_weilEulerPositiveAbove {X : ℕ} {σ : ℝ} (hσ : 1 / 2 < σ) :
    JasDressedPSDAbove X σ ↔ WeilEulerPositiveAbove X σ :=
  ⟨fun h P hP w hw => weilEulerForm_nonneg_of_on hσ (h P hP) P subset_rfl w hw,
    fun h S hS => jasDressedPSDOn_of_weilEulerForm_nonneg hσ S fun P hP w hw =>
      h P (fun p hp => hS p (hP hp)) w hw⟩

/-- **Weil positivity on large-prime Euler vectors at every exponent `≥ 3/2`.** -/
theorem exists_weilEulerPositiveAbove_three_halves :
    ∃ X : ℕ, ∀ σ : ℝ, 3 / 2 ≤ σ → WeilEulerPositiveAbove X σ := by
  obtain ⟨X, hX⟩ := exists_jasDressedPSDAbove_three_halves
  exact ⟨X, fun σ hσ =>
    (jasDressedPSDAbove_iff_weilEulerPositiveAbove (by linarith)).mp (hX σ hσ)⟩

/-- **Weil-form producer dichotomy.**  Weil positivity on large-prime Euler vectors at an exponent
`σ ≥ 1` forces `|Re ρ − ½| ≤ σ − 1` for every zero, unless the zeros accumulate at
`Re s ∈ {0, 1}`. -/
theorem weilEuler_zeroFree_or_edge {X : ℕ} {σ : ℝ} (hσ : 1 ≤ σ) (h : WeilEulerPositiveAbove X σ) :
    (∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ σ - 1) ∨
      sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) = 1 / 2 :=
  jasDressedPSDAbove_zeroFree_or_edge hσ
    ((jasDressedPSDAbove_iff_weilEulerPositiveAbove (by linarith)).mpr h)

/-- **Single-exponent Weil capstone.**  RH holds iff Weil's lag form is nonnegative on every
harmonic Euler vector `m ↦ e_w(m)/m` over a finite set of sufficiently large primes, and some
half-plane bound below `½` holds. -/
theorem riemannHypothesis_iff_weilEulerPositiveAbove_one_and_quasi :
    RiemannHypothesis ↔ (∃ X : ℕ, WeilEulerPositiveAbove X 1) ∧
      ∃ alpha : ℝ, alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  rw [riemannHypothesis_iff_exists_jasDressedPSDAbove_one_and_quasi]
  refine and_congr ⟨fun ⟨X, hX⟩ => ⟨X, ?_⟩, fun ⟨X, hX⟩ => ⟨X, ?_⟩⟩ Iff.rfl
  · exact (jasDressedPSDAbove_iff_weilEulerPositiveAbove (by norm_num)).mp hX
  · exact (jasDressedPSDAbove_iff_weilEulerPositiveAbove (by norm_num)).mpr hX

end

end RHTower
