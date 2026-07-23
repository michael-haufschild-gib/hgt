import GaloisForLFunctions.RHTower.ColumnarAbsoluteProductZeroClassificationUniversalityLaw
import GaloisForLFunctions.RHTower.SingleColumnZeroLatticeUniversalityLaw

/-!
# Columnar absolute-product zero-line/lattice universality law

An absolutely convergent residual product makes the zero set of a columnar carrier equal to its
column zero set and propagates every zero through a vertical lattice.  For an explicit
nonzero-amplitude exponential column, independent modulus rigidity fixes the real coordinate.
Together these mechanisms give an exact geometric and arithmetic classification of every carrier
zero in the product region.
-/

namespace RHTower

/-- **Columnar absolute-product zero-line/lattice universality law.**  In the absolute-product
region, a full-carrier zero is exactly an explicit column zero on its forced logarithmic vertical
line together with the complete carrier zero lattice. -/
theorem columnarAbsoluteProduct_zero_iff_columnEquation_zeroLine_and_carrierLattice
    {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F R : ℂ → ℂ} {f : ℕ → ℂ → ℂ}
    {A : ℂ} (hA : A ≠ 0) {b : ℕ} (hb : 2 ≤ b) {s : ℂ}
    (hfac : ∀ z ∈ Ω,
      F z = (1 - A * (b : ℂ) ^ (-z)) * R z)
    (hs : s ∈ Ω)
    (hsum : Summable fun n => ‖f n s‖)
    (hhalf : ∀ n, ‖f n s‖ ≤ 1 / 2)
    (hrep : (∏' n, (1 + f n s)) = R s) :
    F s = 0 ↔
      (1 - A * (b : ℂ) ^ (-s) = 0) ∧
      s.re = Real.log ‖A‖ / Real.log b ∧
      ∀ k : ℤ,
        F (s + (k * (2 * Real.pi / Real.log b)) * Complex.I) = 0 := by
  have hclass :=
    columnarAbsoluteProduct_zero_iff_columnar_and_verticalLattice
      (F := F) (R := R) (ψ := fun q => 1 - A * q) (f := f)
      (b := b) (s := s) hΩshift hb hfac hs hsum hhalf hrep
  constructor
  · intro hzero
    have hcolumn := hclass.mp hzero
    have hgeometry :=
      singleColumn_zeroLine_and_verticalLattice hA hb hcolumn.1
    exact ⟨hcolumn.1, hgeometry.1, hcolumn.2⟩
  · rintro ⟨hcolumn, _hline, hlattice⟩
    exact hclass.mpr ⟨hcolumn, hlattice⟩

end RHTower
