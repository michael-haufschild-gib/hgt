import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OrderedCechCup

/-! The ordered Čech cup product preserves chart regularity and sends
cocycles to cocycles. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.CechDR

variable {k ι E M N : Type*} [Field k] [LinearOrder ι]
  [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

private def cupHom (μ : E →ₗ[k] M →ₗ[k] N) (b : Finset ι → M) : E →+ (Finset ι → N) where
  toFun a J := μ a (b J)
  map_zero' := funext fun J => LinearMap.congr_fun μ.map_zero (b J)
  map_add' a a' := funext fun J => LinearMap.congr_fun (μ.map_add a a') (b J)

/-- The ordered cup product with a bilinear map on coefficients. -/
def cechCup (μ : E →ₗ[k] M →ₗ[k] N) (a : Finset ι → E) (b : Finset ι → M) :
    Finset ι → N :=
  orderedCup (cupHom μ b) a

theorem cechCup_apply (μ : E →ₗ[k] M →ₗ[k] N) (a : Finset ι → E) (b : Finset ι → M)
    (U : Finset ι) :
    cechCup μ a b U = ∑ j ∈ U, μ (a (U.filter (· ≤ j))) (b (U.filter (j ≤ ·))) := rfl

/-- Cup product with a right cocycle commutes with the Čech differential. -/
theorem deltaL_cechCup_of_rightCycle (μ : E →ₗ[k] M →ₗ[k] N)
    (a : Finset ι → E) (b : Finset ι → M) (ha : a ∅ = 0) (hb : b ∅ = 0)
    (hdb : deltaL k ι M b = 0) :
    deltaL k ι N (cechCup μ a b) = cechCup μ (deltaL k ι E a) b := by
  funext U
  change cechDModule ℤ (orderedCup (cupHom μ b) a) U =
    orderedCup (cupHom μ b) (cechDModule ℤ a) U
  rw [delta_orderedCup (cupHom μ b) a (fun y => by change μ y (b ∅) = 0; rw [hb, map_zero]) ha]
  refine add_eq_left.mpr (Finset.sum_eq_zero fun j _ => ?_)
  have eval_zero (y : E) (V : Finset ι) : cechDModule ℤ (cupHom μ b y) V = 0 := by
    have hV : cechDModule ℤ b V = 0 := congrFun hdb V
    have e := congrArg (μ y) hV
    change ∑ i ∈ V, cubeSign V i • μ y (b (V.erase i)) = 0
    simpa only [cechDModule, map_sum, map_zsmul, map_zero] using e
  rw [eval_zero, smul_zero]

theorem card_filter_le_add_card_filter_ge (U : Finset ι) (j : ι) (hj : j ∈ U) :
    (U.filter (· ≤ j)).card + (U.filter (j ≤ ·)).card = U.card + 1 := by
  have h : U.filter (j ≤ ·) = insert j (U.filter (j < ·)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hi, hji⟩
      rcases hji.eq_or_lt with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨hi, hlt⟩
    · rintro (rfl | ⟨hi, hlt⟩)
      · exact ⟨hj, le_rfl⟩
      · exact ⟨hi, hlt.le⟩
  rw [h, Finset.card_insert_of_notMem (by simp), ← Nat.add_assoc]
  simpa only [not_le] using
    congrArg (· + 1) (Finset.card_filter_add_card_filter_not (s := U) (fun i => i ≤ j))

/-- Each nonzero cup summand uses two nonempty subintersections whose
degrees add to the output degree. -/
theorem cechCup_mem (μ : E →ₗ[k] M →ₗ[k] N)
    (A : Finset ι → Submodule k E) (B : Finset ι → Submodule k M) (C : Finset ι → Submodule k N)
    (hC : ∀ {I J U}, I.Nonempty → J.Nonempty → I ⊆ U → J ⊆ U →
      ∀ {x y}, x ∈ A I → y ∈ B J → μ x y ∈ C U)
    {a : Finset ι → E} {b : Finset ι → M} {p q : ℤ}
    (ha : a ∈ cechC A p) (hb : b ∈ cechC B q) :
    cechCup μ a b ∈ cechC C (p + q) := by
  refine Submodule.mem_pi.mpr fun U _ => ?_
  rw [cechCup_apply]
  refine Submodule.sum_mem _ fun j hj => ?_
  let I := U.filter (· ≤ j)
  let J := U.filter (j ≤ ·)
  have hI := (Submodule.mem_pi.mp ha) I (Set.mem_univ _)
  have hJ := (Submodule.mem_pi.mp hb) J (Set.mem_univ _)
  split_ifs at hI hJ with hp hq
  · have hu : U.Nonempty ∧ (U.card : ℤ) = p + q + 1 := by
      have hcard : I.card + J.card = U.card + 1 := card_filter_le_add_card_filter_ge U j hj
      exact ⟨⟨j, hj⟩, by have := hp.2; have := hq.2; omega⟩
    rw [if_pos hu]
    exact hC hp.1 hq.1 (Finset.filter_subset _ _) (Finset.filter_subset _ _) hI hJ
  · rw [(Submodule.mem_bot k).mp hJ, map_zero]
    exact zero_mem _
  · rw [(Submodule.mem_bot k).mp hI, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  · rw [(Submodule.mem_bot k).mp hI, map_zero, LinearMap.zero_apply]
    exact zero_mem _

end GlobalTheory.CechDR
