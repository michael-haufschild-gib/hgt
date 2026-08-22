import GaloisForLFunctions.HTGeometry.KleinbockMargulis.TheoremA
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Transference

/-!
# Extremality: the simultaneous form of Theorem A

Theorem A says a nondegenerate manifold is *strongly extremal*: almost every parameter is not very
well multiplicatively approximable.  Transference converts that into the simultaneous statement
used by first-return exponents: almost every parameter has simultaneous Diophantine exponent
exactly `1/n`, i.e. for every `η > 0` only finitely many `q ≥ 1` satisfy
`‖q y‖_{ℤⁿ} ≤ q^{-1/n-η}`.
-/

open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d n : ℕ}

/-- `¬ VWA` is exactly the statement that the simultaneous Diophantine exponent is `1/n`: every
strictly better exponent is achieved only finitely often. -/
theorem finite_of_not_vwa {y : Fin n → ℝ} (h : ¬ VWA y) {ε : ℝ} (hε : 0 < ε) :
    {q : ℕ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
      |(q : ℝ) * y i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)}.Finite := by
  by_contra hc
  exact h ⟨ε, hε, hc⟩

/-- **Theorem A, simultaneous form.**  On a `C^l` map whose degenerate locus is null, almost every
parameter is *not* simultaneously very well approximable. -/
theorem theoremA_simultaneous [NeZero d] (hn : 0 < n) {l : ℕ} (hl : 1 ≤ l)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) {F : (Fin d → ℝ) → (Fin n → ℝ)}
    (hF : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) F y)
    (hdeg : volume {x ∈ U | ¬ NondegAt l F x} = 0) :
    volume {x ∈ U | VWA fun i => F x i} = 0 := by
  refine measure_mono_null (fun x hx => ?_) (theoremA hl hU hF hdeg)
  exact ⟨hx.1, vwma_of_vwa hn hx.2⟩

/-- The exponent statement itself, with `VWA` unfolded: for almost every parameter of a
nondegenerate map, no `η > 0` admits infinitely many integers `q ≥ 1` bringing `q · F x` within
`q^{-1/n-η}` of `ℤⁿ`.  So the simultaneous Diophantine exponent is exactly `1/n` almost everywhere. -/
theorem measure_exists_dioph_exponent_eq_zero [NeZero d] (hn : 0 < n) {l : ℕ} (hl : 1 ≤ l)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) {F : (Fin d → ℝ) → (Fin n → ℝ)}
    (hF : ∀ y ∈ U, ContDiffAt ℝ ((l : ℕ)) F y)
    (hdeg : volume {x ∈ U | ¬ NondegAt l F x} = 0) :
    volume {x ∈ U | ∃ ε : ℝ, 0 < ε ∧
      ¬ ({q : ℕ | 1 ≤ q ∧ ∃ p : Fin n → ℤ, ∀ i,
          |(q : ℝ) * F x i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((n : ℝ))⁻¹ - ε)}).Finite} = 0 :=
  theoremA_simultaneous hn hl hU hF hdeg

/-- **Theorem A, simultaneous all-order form.**  This is the form a spectral family uses: the
nondegeneracy order need not be uniform, only the all-order degenerate locus must be null. -/
theorem theoremA_simultaneous_allOrders [NeZero d] (hn : 0 < n) {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {F : (Fin d → ℝ) → (Fin n → ℝ)}
    (hF : ∀ y ∈ U, ∀ l : ℕ, ContDiffAt ℝ ((l : ℕ)) F y)
    (hdeg : volume {x ∈ U | ∀ l : ℕ, 1 ≤ l → ¬ NondegAt l F x} = 0) :
    volume {x ∈ U | VWA fun i => F x i} = 0 := by
  refine measure_mono_null (fun x hx => ?_) (theoremA_allOrders hU hF hdeg)
  exact ⟨hx.1, vwma_of_vwa hn hx.2⟩

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
