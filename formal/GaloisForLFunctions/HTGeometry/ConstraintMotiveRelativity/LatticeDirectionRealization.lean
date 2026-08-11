import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.WeightedCoordinatePort
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.SymmetricSquareRoot
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.LatticeDirectionPortLaw
import Mathlib

/-!
# Exact nested Hilbert realization of a lattice-direction capacity family

Every increasing family `G_n = A₀ + ∑_i c_i(n) a_i ⊗ a_i` with nonnegative nondecreasing weights
vanishing at `n = 0` is the Gram family of a nested surjective finite-dimensional port tower.  The
realization uses the spectral decomposition of `A₀` for the baseline coordinates and one coordinate
per marked direction and per capacity increment `Δ_i(k) = c_i(k+1) - c_i(k)`.
-/

open Filter GaloisForLFunctions.HTGeometry
open scoped Topology RealInnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section Realization

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable {r : ℕ} (L : LatticeDirectionData Y r)

theorem LatticeDirectionData.base_isSymmetric : L.base.IsSymmetric := L.base_symm

theorem LatticeDirectionData.base_nonneg (x : Y) : 0 ≤ ⟪L.base x, x⟫ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (L.base_pos x hx).le

theorem LatticeDirectionData.gram_apply (n : ℕ) (z : Y) :
    L.gram n z = L.base z + ∑ i, (L.weight i n * ⟪L.dir i, z⟫) • L.dir i := by
  simp only [LatticeDirectionData.gram, LinearMap.add_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply, rankOne_apply, smul_smul]

/-- The directions of the realizing coordinate port. -/
noncomputable def latDir : Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ) → Y
  | Sum.inl m => eigBasis L.base_isSymmetric m
  | Sum.inr p => L.dir p.1

/-- The weights of the realizing coordinate port. -/
noncomputable def latWt : Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ) → ℝ
  | Sum.inl m => Real.sqrt (eigVal L.base_isSymmetric m)
  | Sum.inr p => Real.sqrt (L.weight p.1 (p.2 + 1) - L.weight p.1 p.2)

/-- The coordinate set of stage `n`. -/
noncomputable def latStageSet (n : ℕ) : Finset (Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)) :=
  Finset.univ.image Sum.inl ∪ ((Finset.univ ×ˢ Finset.range n).image Sum.inr)

omit [FiniteDimensional ℝ Y] in
theorem latStageSet_mono : Monotone (latStageSet (Y := Y) (r := r)) := by
  intro m n hmn
  refine Finset.union_subset_union_right ?_
  refine Finset.image_subset_image ?_
  refine Finset.product_subset_product (Finset.Subset.refl _) ?_
  exact fun k hk => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk) hmn)

omit [FiniteDimensional ℝ Y] in
theorem mem_latStageSet_inl (n : ℕ) (m : Fin (Module.finrank ℝ Y)) :
    (Sum.inl m : Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)) ∈ latStageSet (Y := Y) (r := r) n := by
  refine Finset.mem_union_left _ ?_
  exact Finset.mem_image.2 ⟨m, Finset.mem_univ m, rfl⟩

omit [FiniteDimensional ℝ Y] in
theorem mem_latStageSet_inr {n : ℕ} {i : Fin r} {k : ℕ} (hk : k < n) :
    (Sum.inr (i, k) : Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)) ∈ latStageSet (Y := Y) (r := r) n := by
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_image.2 ⟨(i, k), Finset.mem_product.2 ⟨Finset.mem_univ i,
    Finset.mem_range.2 hk⟩, rfl⟩

omit [FiniteDimensional ℝ Y] in
theorem latStageSet_iUnion :
    (⋃ n, ((latStageSet (Y := Y) (r := r) n : Finset _) : Set (Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ))))
      = Set.univ := by
  refine Set.eq_univ_of_forall fun j => ?_
  rcases j with m | ⟨i, k⟩
  · exact Set.mem_iUnion.2 ⟨0, mem_latStageSet_inl (Y := Y) (r := r) 0 m⟩
  · exact Set.mem_iUnion.2 ⟨k + 1, mem_latStageSet_inr (Y := Y) (r := r) (Nat.lt_succ_self k)⟩

/-- **The stage Gram operator of the realization is the lattice-direction Gram operator.** -/
theorem latGram_eq (hz : ∀ i, L.weight i 0 = 0) (n : ℕ) (z : Y) :
    portGram (weightedPort (latDir L) (latWt L)) (portStage (latStageSet (Y := Y) (r := r) n))
      (portStage_le (latDir L) (latWt L) (latStageSet (Y := Y) (r := r) n)) z = L.gram n z := by
  classical
  rw [portGram_portStage]
  have hdisj : Disjoint (Finset.univ.image (Sum.inl : Fin (Module.finrank ℝ Y) →
      Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)))
      ((Finset.univ ×ˢ Finset.range n).image Sum.inr) := by
    refine Finset.disjoint_left.2 ?_
    rintro j hj1 hj2
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hj1
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hj2
    exact Sum.inl_ne_inr hp.symm
  have hsplit : latStageSet (Y := Y) (r := r) n
      = Finset.univ.image (Sum.inl : Fin (Module.finrank ℝ Y) →
          Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ))
        ∪ ((Finset.univ ×ˢ Finset.range n).image Sum.inr) := rfl
  rw [hsplit, Finset.sum_union hdisj]
  rw [Finset.sum_image (fun a _ b _ h => Sum.inl_injective h),
    Finset.sum_image (fun a _ b _ h => Sum.inr_injective h)]
  have hbase : ∑ m, ((latWt L (Sum.inl m)) ^ 2 * ⟪latDir L (Sum.inl m), z⟫) •
      latDir L (Sum.inl m) = L.base z := by
    rw [apply_eq_sum L.base_isSymmetric z]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hw : (latWt L (Sum.inl m)) ^ 2 = eigVal L.base_isSymmetric m :=
      Real.sq_sqrt (eigVal_nonneg L.base_isSymmetric L.base_nonneg m)
    show ((latWt L (Sum.inl m)) ^ 2 * ⟪latDir L (Sum.inl m), z⟫) • latDir L (Sum.inl m) = _
    rw [hw]
    rfl
  have hincr : ∑ p ∈ Finset.univ ×ˢ Finset.range n,
      ((latWt L (Sum.inr p)) ^ 2 * ⟪latDir L (Sum.inr p), z⟫) • latDir L (Sum.inr p)
      = ∑ i, (L.weight i n * ⟪L.dir i, z⟫) • L.dir i := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hterm : ∀ k ∈ Finset.range n,
        ((latWt L (Sum.inr (i, k))) ^ 2 * ⟪latDir L (Sum.inr (i, k)), z⟫) •
          latDir L (Sum.inr (i, k))
        = ((L.weight i (k + 1) - L.weight i k) * ⟪L.dir i, z⟫) • L.dir i := by
      intro k _
      have hw : (latWt L (Sum.inr (i, k))) ^ 2 = L.weight i (k + 1) - L.weight i k :=
        Real.sq_sqrt (by linarith [L.weight_mono i (Nat.le_succ k)])
      show ((latWt L (Sum.inr (i, k))) ^ 2 * ⟪latDir L (Sum.inr (i, k)), z⟫) •
        latDir L (Sum.inr (i, k)) = _
      rw [hw]
      rfl
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ← Finset.sum_mul,
      Finset.sum_range_sub (fun k => L.weight i k), hz i, sub_zero]
  rw [hbase, hincr, L.gram_apply]

/-- Every stage of the realization fills the output. -/
theorem latPortFilling (n : ℕ) :
    PortFilling (weightedPort (latDir L) (latWt L)) (portStage (latStageSet (Y := Y) (r := r) n)) := by
  classical
  intro y
  set b := eigBasis L.base_isSymmetric with hb
  set μ := eigVal L.base_isSymmetric with hμ
  have hpos : ∀ m, 0 < μ m := fun m => eigVal_pos L.base_isSymmetric L.base_pos m
  set l : (Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)) →₀ ℝ :=
    ∑ m, Finsupp.single (Sum.inl m) (⟪b m, y⟫ / Real.sqrt (μ m)) with hl
  have hmem : portEmb l ∈ (weightedPort (latDir L) (latWt L)).domain := ⟨l, rfl⟩
  refine ⟨⟨portEmb l, hmem⟩, ?_, ?_⟩
  · have hexp : portEmb (J := Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)) l
        = ∑ m, (⟪b m, y⟫ / Real.sqrt (μ m)) • portBasis (Sum.inl m) := by
      rw [hl, map_sum]
      exact Finset.sum_congr rfl fun m _ => portEmb_single _ _
    show portEmb (J := Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)) l
      ∈ portStage (latStageSet (Y := Y) (r := r) n)
    rw [hexp]
    refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨Sum.inl m, mem_latStageSet_inl (Y := Y) (r := r) n m, rfl⟩
  · rw [weightedPort_apply (latDir L) (latWt L) l hmem, hl, map_sum]
    have hterm : ∀ m : Fin (Module.finrank ℝ Y),
        portMass (latDir L) (latWt L)
          (Finsupp.single (Sum.inl m) (⟪b m, y⟫ / Real.sqrt (μ m)))
          = ⟪b m, y⟫ • b m := by
      intro m
      rw [portMass_single]
      have hsq : Real.sqrt (μ m) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hpos m))
      show (⟪b m, y⟫ / Real.sqrt (μ m)) • (Real.sqrt (μ m) • b m) = ⟪b m, y⟫ • b m
      rw [smul_smul, div_mul_cancel₀ _ hsq]
    rw [Finset.sum_congr rfl fun m _ => hterm m]
    conv_rhs => rw [← (eigBasis L.base_isSymmetric).sum_repr y]
    exact Finset.sum_congr rfl fun m _ => by
      rw [(eigBasis L.base_isSymmetric).repr_apply_apply]

theorem latStage_iSup :
    (⨆ n, portStage (latStageSet (Y := Y) (r := r) n))
      = (weightedPort (latDir L) (latWt L)).domain := by
  rw [weightedPort_domain]
  have hrange : LinearMap.range (portEmb (J := Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)))
      = Submodule.span ℝ (Set.range (portBasis (J := Fin (Module.finrank ℝ Y) ⊕ (Fin r × ℕ)))) :=
    Finsupp.range_linearCombination (R := ℝ) (v := portBasis)
  rw [hrange]
  refine le_antisymm (iSup_le fun n => Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, -, rfl⟩
    exact Submodule.subset_span ⟨j, rfl⟩
  · rintro _ ⟨j, rfl⟩
    rcases j with m | ⟨i, k⟩
    · exact Submodule.mem_iSup_of_mem 0
        (Submodule.subset_span ⟨Sum.inl m, mem_latStageSet_inl (Y := Y) (r := r) 0 m, rfl⟩)
    · exact Submodule.mem_iSup_of_mem (k + 1)
        (Submodule.subset_span ⟨Sum.inr (i, k),
          mem_latStageSet_inr (Y := Y) (r := r) (Nat.lt_succ_self k), rfl⟩)

/-- **Exact nested Hilbert realization.**  Every finite marked lattice-direction family with
weights vanishing at the base is the Gram family of a nested surjective finite-dimensional port
tower. -/
noncomputable def latTower : HilbertPortTower (weightedPort (latDir L) (latWt L)) where
  stage n := portStage (latStageSet (Y := Y) (r := r) n)
  mono := fun m n hmn => Submodule.span_mono (Set.image_mono
    (by exact_mod_cast latStageSet_mono (Y := Y) (r := r) hmn))
  exhaust := latStage_iSup L
  base := 0
  filling := fun n _ => latPortFilling L n
  finite := fun n => portStage_finiteDimensional _

theorem latTower_gram (hz : ∀ i, L.weight i 0 = 0) (n : ℕ) :
    (latTower L).gram n = L.gram n := by
  ext z
  show portGram (weightedPort (latDir L) (latWt L))
      (portStage (latStageSet (Y := Y) (r := r) (0 + n)))
      (portStage_le (latDir L) (latWt L) _) z = L.gram n z
  rw [latGram_eq L hz (0 + n) z, Nat.zero_add]

/-- **Relation-valued realization.**  The vertical fibre of the realizing port is exactly the
divergent span. -/
theorem latTower_multivaluedHorizon (hz : ∀ i, L.weight i 0 = 0) :
    multivaluedHorizon (weightedPort (latDir L) (latWt L)) = (L.divergentSpan : Set Y) :=
  multivaluedHorizon_eq_divergentSpan (latTower L) L (latTower_gram L hz)

end Realization

end HTGeometry.ConstraintMotiveRelativity
