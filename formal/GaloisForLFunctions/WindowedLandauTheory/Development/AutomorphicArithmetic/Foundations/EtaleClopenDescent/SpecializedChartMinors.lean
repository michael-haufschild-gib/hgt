import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartMinors
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedWeightedCech

/-! When the homogeneous weights specialize to zero, the minors with
one coordinate row have the same specialization on every chart. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E D : Type} [Field k] [CommRing S] [Algebra k S] [AddCommGroup E] [Module k E]
  [CommRing D] [Algebra k D] {d : ℕ} (T : WeightedChartSystem k d S E)

/-- The specialization of a one-coordinate-row minor is independent
of the chart when the specialized homogeneous weights vanish. -/
theorem map_orderedMinor_singleton_eq
    (f : S →ₐ[k] D) (hf : ∀ l, f (T.homogeneousMinor l) = 0)
    (L : Finset (DiagonalIndex d)) (i j : Fin (d + 1)) :
    f (orderedMinor T.minorRows (uni {i} L)) = f (orderedMinor T.minorRows (uni {j} L)) := by
  let r (l : Fin (d + 1) ⊕ₗ DiagonalIndex d) (a : Fin (d + 1)) := f (T.minorRows l a)
  let c := orderedMinor r
  let w (l : Fin (d + 1) ⊕ₗ DiagonalIndex d) : Module.End k D :=
    Algebra.lsmul k k D (∑ a, r l a * 1)
  have hclosed : wd w c = 0 := by
    have h := wd_orderedMinor_eq_zero (Algebra.lsmul k k D) r (fun _ => 1) (1 : D)
    have hc : (fun s => Algebra.lsmul k k D (c s) (1 : D)) = c := by
      funext s
      exact mul_one (c s)
    change wd w (fun s => Algebra.lsmul k k D (c s) (1 : D)) = 0 at h
    rwa [hc] at h
  have hrow (l : Fin (d + 1) ⊕ₗ DiagonalIndex d) :
      ∑ a, r l a * 1 = f (Sum.elim (fun _ => (1 : S)) T.homogeneousMinor (ofLex l)) := by
    have he := congrArg f (T.sum_minorRows_eq_weight l)
    simpa only [map_sum, map_mul, map_one, Pi.one_apply, r] using he
  have hw₁ : (fun a : Fin (d + 1) => w (toLex (Sum.inl a))) = 1 := by
    funext a
    change Algebra.lsmul k k D (∑ b, r (toLex (Sum.inl a)) b * 1) = 1
    rw [hrow]
    simp
  have hw₀ : (fun l : DiagonalIndex d => w (toLex (Sum.inr l))) = 0 := by
    funext l
    change Algebra.lsmul k k D (∑ b, r (toLex (Sum.inr l)) b * 1) = 0
    rw [hrow]
    simp [hf]
  have heq (a b : Fin (d + 1)) (hab : a < b) : c (uni {a} L) = c (uni {b} L) := by
    let U : Finset (Fin (d + 1)) := {a, b}
    have hδ : deltaL k (Fin (d + 1)) D (fun I => c (uni I L)) U = 0 := by
      have h := congrFun hclosed (uni U L)
      rw [wd_uni, hw₁, hw₀, wd_one] at h
      simpa only [wd_apply (0 : DiagonalIndex d → Module.End k D), Pi.zero_apply,
        LinearMap.zero_apply, smul_zero, Finset.sum_const_zero, add_zero] using h
    have ha : U.erase a = {b} := by simp [U, hab.ne]
    have hb : U.erase b = {a} := by
      rw [show U = {b, a} by exact Finset.pair_comm a b]
      simp [hab.ne.symm]
    have hsa : GlobalTheory.cubeSign U a = 1 := by
      change (-1 : ℤ) ^ (U.filter (· < a)).card = 1
      simp [U, Finset.filter_insert, Finset.filter_singleton, not_lt_of_ge hab.le]
    have hsb : GlobalTheory.cubeSign U b = -1 := by
      change (-1 : ℤ) ^ (U.filter (· < b)).card = -1
      simp [U, Finset.filter_insert, Finset.filter_singleton, hab]
    rw [deltaL_apply, show (∑ l ∈ U, GlobalTheory.cubeSign U l • c (uni (U.erase l) L)) =
      GlobalTheory.cubeSign U a • c (uni (U.erase a) L) +
      GlobalTheory.cubeSign U b • c (uni (U.erase b) L) from Finset.sum_pair hab.ne,
      ha, hb, hsa, hsb, one_smul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at hδ
    exact hδ.symm
  change f.toRingHom (orderedMinor T.minorRows (uni {i} L)) =
    f.toRingHom (orderedMinor T.minorRows (uni {j} L))
  rw [map_orderedMinor, map_orderedMinor]
  change c (uni {i} L) = c (uni {j} L)
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact heq i j hij
  · rfl
  · exact (heq j i hji).symm

end GlobalTheory.WH.WeightedChartSystem
