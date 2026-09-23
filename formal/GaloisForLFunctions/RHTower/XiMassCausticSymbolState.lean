import GaloisForLFunctions.RHTower.XiMassCausticJetOperator
import GaloisForLFunctions.RHTower.XiMassCausticSymbolDefect

/-!
# The caustic symbol is the diagonal of the jet operator

Writing `α = a·w/Z`, `β = w/Z²`, the height system sends a state `(A, B)` to `(A₁, B₁)` with
`A₁ = A′ − αB` and `B₁ = B′ − αA − βB`.  Applying it twice and subtracting from `4a⁴` gives, in the
`K₁` slot,

`4a⁴B − (B₁′ − αA₁ − βB₁) = (4a⁴ − α²)·B + (αA′ − B₁′ + βB₁)`,

and `4a⁴ − α² = 4a⁴ − a²w²/Z²` is exactly the caustic symbol.  Every other term carries an explicit
factor `1/Z` or a coefficient derivative, both of which are one order smaller on the cone.

So the entire gain of a caustic-null jet is the vanishing of that symbol at the balance slope, which
`XiMassCausticSymbolDefect.exists_norm_xiMassCausticSymbol_le` bounds by `C/√u` on the window
`|h − κ_B u| ≤ √u`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The caustic symbol at a complex height. -/
def xiMassCausticSymbolC (a : ℝ) (τ w : ℂ) : ℂ :=
  4 * (a : ℂ) ^ (4 : ℕ) - (a : ℂ) ^ (2 : ℕ) * w ^ (2 : ℕ) / (τ ^ (2 : ℕ) + w ^ (2 : ℕ))

theorem xiMassCausticSymbolC_ofReal (a sigma u h : ℝ) :
    xiMassCausticSymbolC a ((sigma : ℂ) + (u : ℂ) * Complex.I) (h : ℂ)
      = xiMassCausticSymbol a sigma u h := by
  rw [xiMassCausticSymbolC, xiMassCausticSymbol, xiMassSpacelikePropagationArgument_eq]

/-- The symbol is `4a⁴` minus the square of the transport rate `α = a·w/Z`. -/
theorem xiMassCausticSymbolC_eq_sub_sq {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re) :
    xiMassCausticSymbolC a τ w
      = 4 * (a : ℂ) ^ (4 : ℕ) - ((a : ℂ) * w / xiMassHeightRadius τ w) ^ (2 : ℕ) := by
  have hZ2 : xiMassHeightRadius τ w ^ (2 : ℕ) = τ ^ (2 : ℕ) + w ^ (2 : ℕ) := xiMassHeightRadius_sq hw
  rw [xiMassCausticSymbolC, div_pow, mul_pow, hZ2]

/-- **The `K₁` diagonal of the caustic combination.**  The symbol multiplies `B`; everything else
carries a transport factor or a coefficient derivative. -/
theorem xiCaustic_K1_coefficient {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re)
    (A A' B B' B₁' : ℂ) :
    4 * (a : ℂ) ^ (4 : ℕ) * B
        - (B₁'
          - (a : ℂ) * w / xiMassHeightRadius τ w
              * (A' - (a : ℂ) * w / xiMassHeightRadius τ w * B)
          - w / xiMassHeightRadius τ w ^ (2 : ℕ)
              * (B' - (a : ℂ) * w / xiMassHeightRadius τ w * A
                - w / xiMassHeightRadius τ w ^ (2 : ℕ) * B))
      = xiMassCausticSymbolC a τ w * B
        + ((a : ℂ) * w / xiMassHeightRadius τ w * A' - B₁'
          + w / xiMassHeightRadius τ w ^ (2 : ℕ)
              * (B' - (a : ℂ) * w / xiMassHeightRadius τ w * A
                - w / xiMassHeightRadius τ w ^ (2 : ℕ) * B)) := by
  rw [xiMassCausticSymbolC_eq_sub_sq hw]
  ring

/-- **The `K₀` diagonal of the caustic combination.**  No symbol appears: the whole coefficient is a
transport term against the `K₁` slot plus a coefficient derivative. -/
theorem xiCaustic_K0_coefficient {a : ℝ} {τ w : ℂ} (A A₁' B₁' : ℂ) :
    4 * (a : ℂ) ^ (4 : ℕ) * A - (A₁' - (a : ℂ) * w / xiMassHeightRadius τ w * B₁')
      = 4 * (a : ℂ) ^ (4 : ℕ) * A - A₁' + (a : ℂ) * w / xiMassHeightRadius τ w * B₁' := by
  ring

end

end RHTower
