import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartDifferential
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCoefficientMap

/-! A scalar-compatible map of chart lattices acts on homogeneous
columns and carries their cocycles and primitives to the new lattice. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S M N κ : Type} [Field k] [CommRing S] [Algebra k S] [LinearOrder κ]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] {d : ℕ}

/-- Maps commuting with the scalar action commute with the weighted
column differential, including the chart normalization of coefficients. -/
theorem isMap_columnMap (T : WeightedChartSystem k d S M) (U : WeightedChartSystem k d S N)
    (f : M →ₗ[k] N) (hX : T.X = U.X) (hY : T.Y = U.Y)
    (hact : ∀ a v, f (T.act a v) = U.act a (f v))
    (I J : Finset (Fin (d + 1))) (hf : T.M I J ≤ (U.M I J).comap f)
    (n : κ → ℕ × ℕ) (z : κ → S) :
    IsMap (T.columnComplex n z I J) (U.columnComplex n z I J) (mapCochain f) := by
  intro q v hv
  refine ⟨acx_mem_terms_iff.mpr (fun L => ?_), ?_⟩
  · have hm := acx_mem_terms_iff.mp hv L
    change f (v L) ∈ if (L.card : ℤ) = q then U.scaledCoefficients n I J L else ⊥
    split_ifs at hm ⊢ with hL
    · obtain ⟨u, hu, he⟩ : ∃ u ∈ T.M I J,
          T.act ((∏ l ∈ L, T.weightUnit n (chartIndex I) (chartIndex J) l : Sˣ) : S) u = v L := hm
      refine ⟨f u, hf hu, ?_⟩
      rw [← he, hact]
      simp only [weightUnit, hX, hY]
    · rw [(Submodule.mem_bot k).mp hm, map_zero]
      exact zero_mem _
  · change mapCochain f (wd (fun l => T.act (z l)) v) =
      wd (fun l => U.act (z l)) (mapCochain f v)
    funext L
    simp only [mapCochain_apply, wd_apply, map_sum, map_zsmul, hact]

end GlobalTheory.WH.WeightedChartSystem
