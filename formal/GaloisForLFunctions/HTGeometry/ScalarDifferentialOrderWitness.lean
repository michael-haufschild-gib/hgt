import GaloisForLFunctions.HTGeometry.HypertranscendentalObservableNet
import GaloisForLFunctions.HTGeometry.ScalarDifferentialRationalOrder

/-!
# Exact scalar differential orders exist

The scalar-order layer consumes `HypertranscendentalOver F x` together with
`HasScalarDifferentialOrder F x z n` — an element visible at resolution `n + 1` but not at `n`.  The
two are never exhibited on a common object, so the layer could a priori be about an empty
configuration.

It is not: for a hypertranscendental clock the `n`-th jet has order exactly `n`.  Exact jet
visibility (`differentialJet_mem_jetObservableField_iff_lt`) says the `n`-th jet is visible at
resolution `N` precisely when `n < N`, which is both halves of the definition at once.

* **`hasScalarDifferentialOrder_differentialJet`** — the `n`-th jet has order `n`;
* `hasScalarDifferentialOrder_self` — the clock itself has order zero;
* **`exists_hypertranscendental_scalarDifferentialOrder`** — the pair is jointly realized in every
  order.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

/-- **The `n`-th jet of a hypertranscendental clock has scalar differential order exactly `n`.** -/
theorem hasScalarDifferentialOrder_differentialJet {x : E} (hx : HypertranscendentalOver F x)
    (n : ℕ) : HasScalarDifferentialOrder F x (differentialJet n x) n := by
  refine ⟨(differentialJet_mem_jetObservableField_iff_lt hx n (n + 1)).mpr (Nat.lt_succ_self n),
    fun hmem => ?_⟩
  exact absurd ((differentialJet_mem_jetObservableField_iff_lt hx n n).mp hmem) (lt_irrefl n)

/-- The clock itself has order zero. -/
theorem hasScalarDifferentialOrder_self {x : E} (hx : HypertranscendentalOver F x) :
    HasScalarDifferentialOrder F x x 0 := by
  have h := hasScalarDifferentialOrder_differentialJet hx 0
  rwa [differentialJet_zero] at h

/-- **Joint realization.**  Hypertranscendence of the clock and an exact scalar differential order
occur together, in every order, so the scalar-order layer is not vacuous. -/
theorem exists_hypertranscendental_scalarDifferentialOrder {x : E}
    (hx : HypertranscendentalOver F x) (n : ℕ) :
    ∃ z : E, HypertranscendentalOver F x ∧ HasScalarDifferentialOrder F x z n :=
  ⟨differentialJet n x, hx, hasScalarDifferentialOrder_differentialJet hx n⟩

end GaloisForLFunctions.HTGeometry
