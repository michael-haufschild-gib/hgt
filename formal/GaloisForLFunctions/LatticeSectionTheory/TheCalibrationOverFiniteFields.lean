import GaloisForLFunctions.LatticeSectionTheory.BidegreeCountsSeeNoPrimitiveClass
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDefectOfAGraphIsTwiceItsDegree
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw

/-!
# Calibration over finite fields: the primitive `h¹` of a graph is a count

On the Frobenius windows of a curve datum over `𝔽_q` the Künneth count is the same object as on
the scaling surface, and its laws can be checked against Weil.

* **Curves** (`unitary_iff_forall_window_kunneth`). The Künneth count is an effectivity function on
  every Frobenius window iff the datum is unitary (RH for the curve).
* **Fakes** (`goldenDatum_not_forall_window_kunneth`). On the golden datum `1 − 5X + 5X²` —
  integral point counts, functional equation, Beurling structure — some window carries no
  Künneth Riemann inequality.
* **Genus one** (`genusOne_kunneth_h1_graphCycle`, `genusOne_kunneth_h1_frobenius`). On the window
  `{Δ, Γ_F}` of a genus-one datum the `h¹` of the Künneth count on the graph class of `m − nF` is
  the Künneth part plus `deg(m − nF) = m² − a m n + q n²`; for `1 − F` the primitive part is the
  number of rational points `N₁`. Over a curve the primitive `h¹` is a degree of a correspondence —
  the order of its kernel — and its nonnegativity is Hasse's bound.

This is what the primitive `h¹` must become over `ℤ`: the degree of a correspondence, read as a
count.
-/

noncomputable section

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory

/-- **Curves.** The Künneth count is an effectivity function on every Frobenius window iff the
curve datum is unitary. -/
theorem unitary_iff_forall_window_kunneth {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ W : Finset ℕ,
      RiemannInequality (D.windowSurface W) 0 0 (kunnethH0 (D.windowSurface W)) ∧
        DegreeBounded (D.windowSurface W) (kunnethH0 (D.windowSurface W)) := by
  rw [← D.windowSurface_hodgeIndex_iff_unitary]
  exact forall_congr' fun W => (kunneth_effectivity_iff _).symm

/-- **The golden fake.** Some Frobenius window of the golden datum carries no Künneth Riemann
inequality. -/
theorem goldenDatum_not_forall_window_kunneth :
    ¬ ∀ W : Finset ℕ,
      RiemannInequality (goldenDatum.windowSurface W) 0 0 (kunnethH0 (goldenDatum.windowSurface W)) :=
  fun h => goldenDatum_not_unitary ((goldenDatum.windowSurface_hodgeIndex_iff_unitary).mp
    fun W => (riemannInequality_kunnethH0_iff _).mp (h W))

/-- **Genus one: the primitive `h¹` of a graph is its degree.** On the window `{Δ, Γ_F}`,
`h_K(Γ) + h_K(−Γ) − χ(Γ) = h¹_K(Γ) + deg(m − nF)` for the graph class `Γ` of `m − nF`. -/
theorem genusOne_kunneth_h1_graphCycle {ι : Type*} [Fintype ι] (D : CurveDatum ι)
    (hg : Fintype.card ι = 2) (m n : ℝ) :
    kunnethH0 (D.windowSurface {0, 1}) (D.graphCycle m n) +
        kunnethH0 (D.windowSurface {0, 1}) (0 - D.graphCycle m n) -
        eulerChar (D.windowSurface {0, 1}) 0 0 (D.graphCycle m n) =
      kunnethH1 (D.windowSurface {0, 1}) (D.graphCycle m n) + D.endDeg m n := by
  have h := kunneth_h1_sub_eq_half_defect (D.windowSurface {0, 1}) (D.graphCycle m n)
  rw [(D.defect_graphCycle_of_genusOne hg m n).1] at h
  linarith

/-- **The graph of `1 − F`**: its primitive `h¹` is the number of rational points. -/
theorem genusOne_kunneth_h1_frobenius {ι : Type*} [Fintype ι] (D : CurveDatum ι)
    (hg : Fintype.card ι = 2) :
    kunnethH0 (D.windowSurface {0, 1}) (D.graphCycle 1 1) +
        kunnethH0 (D.windowSurface {0, 1}) (0 - D.graphCycle 1 1) -
        eulerChar (D.windowSurface {0, 1}) 0 0 (D.graphCycle 1 1) =
      kunnethH1 (D.windowSurface {0, 1}) (D.graphCycle 1 1) + D.pointCount 1 := by
  rw [genusOne_kunneth_h1_graphCycle D hg, D.endDeg_one_one]

end GaloisForLFunctions.LatticeSectionTheory
