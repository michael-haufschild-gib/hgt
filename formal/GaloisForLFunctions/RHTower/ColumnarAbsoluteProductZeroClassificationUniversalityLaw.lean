import GaloisForLFunctions.RHTower.ColumnarInterferential
import GaloisForLFunctions.RHTower.ExplicitAperiodicZero
import GaloisForLFunctions.RHTower.PeriodicityDichotomy

/-!
# Columnar absolute-product zero classification universality

Where a carrier is simultaneously represented by one exponential column times an absolutely
convergent residual product, its zeros are exactly the column zeros and inherit the column's full
vertical lattice.  Hence an aperiodic zero must lie beyond the region where at least one of those
two representations remains valid.
-/

namespace RHTower

/-- **Columnar absolute-product zero classification.** If the residual factor is represented at
`s` by an absolutely convergent product in the half-ball, then a carrier zero at `s` is equivalent
to a column zero together with its full vertical lattice. -/
theorem columnarAbsoluteProduct_zero_iff_columnar_and_verticalLattice
    {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F R : ℂ → ℂ} {ψ : ℂ → ℂ} {f : ℕ → ℂ → ℂ}
    {b : ℕ} (hb : 2 ≤ b) {s : ℂ}
    (hfac : ∀ z ∈ Ω, F z = ψ ((b : ℂ) ^ (-z)) * R z)
    (hs : s ∈ Ω)
    (hsum : Summable fun n => ‖f n s‖)
    (hhalf : ∀ n, ‖f n s‖ ≤ 1 / 2)
    (hrep : (∏' n, (1 + f n s)) = R s) :
    F s = 0 ↔
      ψ ((b : ℂ) ^ (-s)) = 0 ∧
        ∀ k : ℤ,
          F (s + (k * (2 * Real.pi / Real.log b)) * Complex.I) = 0 := by
  have hRne : R s ≠ 0 :=
    no_interferential_zero_in_product_region hsum hhalf hrep
  constructor
  · intro hzero
    have hproduct : ψ ((b : ℂ) ^ (-s)) * R s = 0 := by
      rw [← hfac s hs, hzero]
    have hψ : ψ ((b : ℂ) ^ (-s)) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right hRne
    exact ⟨hψ, columnar_zero_periodic hΩshift hb hfac hs hψ⟩
  · rintro ⟨hψ, hperiod⟩
    rw [hfac s hs, hψ, zero_mul]

/-- **Aperiodic-zero product-boundary law.** A carrier has no aperiodic zero at a point where its
column factorization and an absolutely convergent residual-product representation both hold. -/
theorem not_aperiodicZeroAt_of_columnarAbsoluteProductRegion
    {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F R : ℂ → ℂ} {ψ : ℂ → ℂ} {f : ℕ → ℂ → ℂ}
    {b : ℕ} (hb : 2 ≤ b) {s : ℂ}
    (hfac : ∀ z ∈ Ω, F z = ψ ((b : ℂ) ^ (-z)) * R z)
    (hs : s ∈ Ω)
    (hsum : Summable fun n => ‖f n s‖)
    (hhalf : ∀ n, ‖f n s‖ ≤ 1 / 2)
    (hrep : (∏' n, (1 + f n s)) = R s) :
    ¬AperiodicZeroAt F s := by
  intro haper
  have hclass :=
    (columnarAbsoluteProduct_zero_iff_columnar_and_verticalLattice
      hΩshift hb hfac hs hsum hhalf hrep).mp haper.1
  apply haper.2
  refine ⟨2 * Real.pi / Real.log b, ?_, ?_⟩
  have hb1 : (1 : ℝ) < b := by
    exact_mod_cast (show 1 < b by omega)
  · exact div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos hb1)
  · intro k
    simpa only [Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat, Complex.ofReal_div,
      Complex.ofReal_mul, Complex.ofReal_natCast] using hclass.2 k

/-- The explicit linear aperiodic-zero carrier cannot admit both representations at its zero. -/
theorem simpleZeroAt_columnarAbsoluteProductRegion_impossible
    (ρ : ℂ) {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {R : ℂ → ℂ} {ψ : ℂ → ℂ} {f : ℕ → ℂ → ℂ}
    {b : ℕ} (hb : 2 ≤ b)
    (hfac : ∀ z ∈ Ω, simpleZeroAt ρ z = ψ ((b : ℂ) ^ (-z)) * R z)
    (hρ : ρ ∈ Ω)
    (hsum : Summable fun n => ‖f n ρ‖)
    (hhalf : ∀ n, ‖f n ρ‖ ≤ 1 / 2)
    (hrep : (∏' n, (1 + f n ρ)) = R ρ) :
    False :=
  not_aperiodicZeroAt_of_columnarAbsoluteProductRegion
    hΩshift hb hfac hρ hsum hhalf hrep (simpleZeroAt_aperiodicZeroAt ρ)

end RHTower
