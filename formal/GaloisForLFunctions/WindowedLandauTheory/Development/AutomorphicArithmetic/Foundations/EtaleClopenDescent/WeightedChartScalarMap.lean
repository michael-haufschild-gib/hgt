import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCoefficientMap

/-! A map of scalar rings and regular chart lattices induces a map
of the joined weighted Čech complexes. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S R M N κ : Type} [Field k] [CommRing S] [Algebra k S] [CommRing R] [Algebra k R]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [LinearOrder κ] {d : ℕ}

/-- The map on coefficients commutes with all homogeneous weights
and sends the scaled chart lattices into the corresponding lattices. -/
theorem isMap_of_scalarMap (T : WeightedChartSystem k d S M) (U : WeightedChartSystem k d R N)
    (g : S →ₐ[k] R) (f : M →ₗ[k] N)
    (hX : ∀ i, Units.map g.toMonoidHom (T.X i) = U.X i)
    (hY : ∀ j, Units.map g.toMonoidHom (T.Y j) = U.Y j)
    (hact : ∀ s v, f (T.act s v) = U.act (g s) (f v))
    (hM : ∀ I J, I.Nonempty → J.Nonempty → T.M I J ≤ (U.M I J).comap f)
    (n : κ → ℕ × ℕ) (z : κ → S) :
    IsMap (T.complex n z) (U.complex n (g ∘ z)) (mapCochain f) := by
  have hweights (s : ChartPair d ⊕ₗ κ) (v : M) :
      f (T.weights z s v) = U.weights (g ∘ z) s (f v) := by
    rcases hs : ofLex s with a | a
    · rw [weights, hs, Sum.elim_inl, hact, map_one, weights, hs, Sum.elim_inl]
    · rw [weights, hs, Sum.elim_inr, hact, weights, hs, Sum.elim_inr]
      rfl
  have hscale (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (L : Finset κ) :
      T.scaledCoefficients n I J L ≤ (U.scaledCoefficients n I J L).comap f := by
    let i := chartIndex I
    let j := chartIndex J
    let a := ∏ l ∈ L, T.weightUnit n i j l
    let b := ∏ l ∈ L, U.weightUnit n i j l
    have hab : Units.map g.toMonoidHom a = b := by
      dsimp only [a, b]
      rw [map_prod]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [weightUnit, map_mul, map_pow, map_pow, hX, hY]
      rfl
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨f v, hM I J hI hJ hv, ?_⟩
    change U.act (b : R) (f v) = f (T.act (a : S) v)
    have he : g (a : S) = (b : R) := congrArg (fun u : Rˣ => (u : R)) hab
    rw [hact, he]
  intro m c hc
  refine ⟨acx_mem_terms_iff.mpr (fun s => ?_), ?_⟩
  · have hm := acx_mem_terms_iff.mp hc s
    change f (c s) ∈ if (s.card : ℤ) = m then U.mixedCoefficients n (rgt s) (lft s) else ⊥
    by_cases hdeg : (s.card : ℤ) = m
    · rw [if_pos hdeg, mixedCoefficients] at hm ⊢
      by_cases h : (lft (lft s)).Nonempty ∧ (rgt (lft s)).Nonempty
      · rw [if_pos h] at hm ⊢
        exact hscale _ _ h.1 h.2 _ hm
      · rw [if_neg h] at hm ⊢
        exact (Submodule.mem_bot k).mpr (by rw [(Submodule.mem_bot k).mp hm, map_zero])
    · rw [if_neg hdeg] at hm ⊢
      exact (Submodule.mem_bot k).mpr (by rw [(Submodule.mem_bot k).mp hm, map_zero])
  · change mapCochain f (wd (T.weights z) c) = wd (U.weights (g ∘ z)) (mapCochain f c)
    funext s
    simp only [mapCochain_apply, wd_apply, map_sum, map_zsmul, hweights]

end GlobalTheory.WH.WeightedChartSystem
