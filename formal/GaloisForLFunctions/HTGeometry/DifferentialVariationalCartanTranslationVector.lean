import GaloisForLFunctions.HTGeometry.DifferentialVariationalEuclideanTranslationLength

/-!
# Intrinsic vector-valued Cartan translation length

Every fundamental-weight coordinate of a projective Cartan displacement is nonnegative and
subadditive along an isometric orbit.  Fekete convergence for all finitely many prefix sums then
reconstructs the full normalized dominant Cartan vector.  The limit is balanced, dominant, and
independent of both lattice base point and finite operator basis.
-/

open Filter Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem topSum_nonneg_of_antitone_sum_zero {r : ℕ}
    (v : Fin r → ℝ) (hv : Antitone v) (hsum : ∑ i, v i = 0)
    (k : ℕ) (hk : k ≤ r) : 0 ≤ topSum k v := by
  rw [DiffOp.topSum_eq_sum_firstIdx_of_antitone v hv k hk]
  by_cases hk0 : k = 0
  · subst k
    simp [firstIdx]
  by_cases hkr : k = r
  · subst k
    rw [firstIdx_self]
    exact le_of_eq hsum.symm
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hklt : k < r := lt_of_le_of_ne hk hkr
  let q : Fin r := ⟨k - 1, by omega⟩
  have hqle : (k : ℝ) * v q ≤ ∑ i ∈ firstIdx r k, v i := by
    calc
      (k : ℝ) * v q = ∑ _i ∈ firstIdx r k, v q := by
        rw [Finset.sum_const, card_firstIdx hk]
        simp [nsmul_eq_mul]
      _ ≤ ∑ i ∈ firstIdx r k, v i := by
        apply Finset.sum_le_sum
        intro i hi
        apply hv
        change (i : ℕ) ≤ k - 1
        have := mem_firstIdx.mp hi
        omega
  by_contra hneg
  have hheadneg : (∑ i ∈ firstIdx r k, v i) < 0 := lt_of_not_ge hneg
  have hqneg : v q < 0 := by
    have hmulneg : (k : ℝ) * v q < 0 := lt_of_le_of_lt hqle hheadneg
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
    nlinarith
  let tail : Finset (Fin r) := Finset.univ.filter fun i => k ≤ (i : ℕ)
  have htailne : tail.Nonempty := by
    refine ⟨⟨k, hklt⟩, ?_⟩
    simp [tail]
  have htailneg : (∑ i ∈ tail, v i) < 0 := by
    exact Finset.sum_neg (fun i hi => by
      have hik : k ≤ (i : ℕ) := (Finset.mem_filter.mp hi).2
      have hqi : q ≤ i := by
        change k - 1 ≤ (i : ℕ)
        omega
      exact lt_of_le_of_lt (hv hqi) hqneg) htailne
  have hpartition :
      (∑ i, v i) = (∑ i ∈ firstIdx r k, v i) + ∑ i ∈ tail, v i := by
    rw [← Finset.sum_union]
    · apply Finset.sum_congr
      · ext i
        simp [firstIdx, tail]
        omega
      · intro i hi
        rfl
    · rw [Finset.disjoint_left]
      intro i hi hti
      rw [mem_firstIdx] at hi
      have := (Finset.mem_filter.mp hti).2
      omega
  rw [hsum] at hpartition
  linarith

namespace DiffOp

variable {K : Type*} [Field K] [Differential K]

theorem differentialVariationalProjectiveEuclideanRelativePosition_antitone
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    Antitone (differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) := by
  refine Quotient.inductionOn₂ x y ?_
  intro L M i j hij
  change completedPseudoDiffOpEuclideanRelativePosition L M j ≤
    completedPseudoDiffOpEuclideanRelativePosition L M i
  simp only [completedPseudoDiffOpEuclideanRelativePosition, centeredCoweight]
  exact sub_le_sub_right
    (by exact_mod_cast completedPseudoDiffOpDominantRelativePosition_antitone L M hij) _

theorem differentialVariationalProjectiveEuclideanRelativePosition_sum_eq_zero
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    ∑ i, (differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) i = 0 := by
  exact (differentialVariationalProjectiveEuclideanRelativePosition x y).2

theorem differentialVariationalProjectiveEuclideanRelativePosition_topSum_nonneg
    {r : ℕ}
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) :
    0 ≤ topSum k
      (differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) := by
  exact topSum_nonneg_of_antitone_sum_zero _
    (differentialVariationalProjectiveEuclideanRelativePosition_antitone x y)
    (differentialVariationalProjectiveEuclideanRelativePosition_sum_eq_zero x y) k hk

theorem differentialVariationalProjectiveEuclideanRelativePosition_topSum_triangle
    {r : ℕ}
    (x y z : DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) :
    topSum k (differentialVariationalProjectiveEuclideanRelativePosition x z : Fin r → ℝ) ≤
      topSum k (differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) +
        topSum k (differentialVariationalProjectiveEuclideanRelativePosition y z : Fin r → ℝ) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro L M N
  exact completedPseudoDiffOpCenteredCartan_topSum_triangle L M N k hk

end DiffOp

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

noncomputable def differentialVariationalCartanPrefixOrbitGauge
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) : SubadditiveClockGauge (DifferentialFieldAut C K) where
  cost σ := topSum k
    (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
      x (σ.projectiveBuildingAction b x) : Fin r → ℝ)
  cost_nonneg σ :=
    DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_topSum_nonneg
      x (σ.projectiveBuildingAction b x) k hk
  cost_one := by
    rw [DifferentialFieldAut.projectiveBuildingAction_one]
    have hzero :
        (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x x : Fin r → ℝ) = 0 := by
      funext i
      exact DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_self_apply x i
    rw [hzero]
    simp [topSum, firstIdx, sortDesc_eq_comp]
  cost_mul_le σ τ := by
    rw [DifferentialFieldAut.projectiveBuildingAction_mul]
    calc
      topSum k
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
            (τ.projectiveBuildingAction b (σ.projectiveBuildingAction b x)) : Fin r → ℝ) ≤
        topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
              (τ.projectiveBuildingAction b x) : Fin r → ℝ) +
          topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
              (τ.projectiveBuildingAction b x)
              (τ.projectiveBuildingAction b (σ.projectiveBuildingAction b x)) : Fin r → ℝ) :=
        DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_topSum_triangle
          x (τ.projectiveBuildingAction b x)
            (τ.projectiveBuildingAction b (σ.projectiveBuildingAction b x)) k hk
      _ = topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
              (τ.projectiveBuildingAction b x) : Fin r → ℝ) +
          topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
              (σ.projectiveBuildingAction b x) : Fin r → ℝ) := by
        rw [τ.projectiveBuildingAction_euclideanRelativePosition]
      _ = topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
              (σ.projectiveBuildingAction b x) : Fin r → ℝ) +
          topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
              (τ.projectiveBuildingAction b x) : Fin r → ℝ) := add_comm _ _

noncomputable def differentialVariationalCartanPrefixTranslationLength
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) (σ : DifferentialFieldAut C K) : ℝ :=
  (differentialVariationalCartanPrefixOrbitGauge b x k hk).translationLength σ

theorem tendsto_differentialVariationalCartan_normalizedPrefix
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) (σ : DifferentialFieldAut C K) :
    Tendsto (fun n : ℕ =>
      topSum k
        (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
          ((σ ^ n).projectiveBuildingAction b x) : Fin r → ℝ) / n)
      atTop (nhds (differentialVariationalCartanPrefixTranslationLength b x k hk σ)) := by
  exact (differentialVariationalCartanPrefixOrbitGauge b x k hk).tendsto_normalizedOrbitCost σ

noncomputable def differentialVariationalCartanTranslationVector
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) : Fin r → ℝ :=
  fun i =>
    differentialVariationalCartanPrefixTranslationLength b x (i + 1) (by omega) σ -
      differentialVariationalCartanPrefixTranslationLength b x i (by omega) σ

theorem tendsto_differentialVariationalCartanTranslationVector
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    Tendsto (fun n : ℕ => fun i : Fin r =>
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
        ((σ ^ n).projectiveBuildingAction b x) : Fin r → ℝ) i / n)
      atTop (nhds (differentialVariationalCartanTranslationVector b x σ)) := by
  rw [tendsto_pi_nhds]
  intro i
  have hsucc := tendsto_differentialVariationalCartan_normalizedPrefix
    b x (i + 1) (by omega) σ
  have hbase := tendsto_differentialVariationalCartan_normalizedPrefix
    b x i (by omega) σ
  have hsub := hsucc.sub hbase
  convert hsub using 1
  · funext n
    let v : Fin r → ℝ :=
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
        ((σ ^ n).projectiveBuildingAction b x) : Fin r → ℝ)
    have hv := DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_antitone
      x ((σ ^ n).projectiveBuildingAction b x)
    have hs : topSum (i + 1) v = topSum i v + v i := by
      rw [DiffOp.topSum_eq_sum_firstIdx_of_antitone v hv (i + 1) (by omega),
        DiffOp.topSum_eq_sum_firstIdx_of_antitone v hv i (by omega)]
      exact finiteVectorPrefixSum_succ v i
    change v i / n = topSum (i + 1) v / n - topSum i v / n
    rw [hs]
    ring
  · rfl

theorem differentialVariationalCartanTranslationVector_sum_eq_zero
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    ∑ i, differentialVariationalCartanTranslationVector b x σ i = 0 := by
  have hvec := tendsto_differentialVariationalCartanTranslationVector b x σ
  rw [tendsto_pi_nhds] at hvec
  have hsum : Tendsto (fun n : ℕ => ∑ i : Fin r,
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
        ((σ ^ n).projectiveBuildingAction b x) : Fin r → ℝ) i / n)
      atTop (nhds (∑ i, differentialVariationalCartanTranslationVector b x σ i)) := by
    exact tendsto_finsetSum Finset.univ fun i _ => hvec i
  have hzero : (fun n : ℕ => ∑ i : Fin r,
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
        ((σ ^ n).projectiveBuildingAction b x) : Fin r → ℝ) i / n) =
      fun _ => 0 := by
    funext n
    rw [← Finset.sum_div,
      DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_sum_eq_zero,
      zero_div]
  rw [hzero] at hsum
  exact tendsto_nhds_unique hsum tendsto_const_nhds

theorem differentialVariationalCartanTranslationVector_antitone
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    Antitone (differentialVariationalCartanTranslationVector b x σ) := by
  intro i j hij
  have hvec := tendsto_differentialVariationalCartanTranslationVector b x σ
  rw [tendsto_pi_nhds] at hvec
  have hdiff := (hvec j).sub (hvec i)
  have hle : differentialVariationalCartanTranslationVector b x σ j -
      differentialVariationalCartanTranslationVector b x σ i ≤ 0 := by
    apply le_of_tendsto' hdiff
    intro n
    apply sub_nonpos.mpr
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_antitone
      x ((σ ^ n).projectiveBuildingAction b x) hij
  linarith

theorem differentialVariationalCartanPrefixOrbitGauge_cost_base_le
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) (σ : DifferentialFieldAut C K) :
    (differentialVariationalCartanPrefixOrbitGauge b x k hk).cost σ ≤
      (differentialVariationalCartanPrefixOrbitGauge b y k hk).cost σ +
        (topSum k
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) +
        topSum k
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y x : Fin r → ℝ)) := by
  change topSum k
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
        (σ.projectiveBuildingAction b x) : Fin r → ℝ) ≤
    topSum k
        (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y
          (σ.projectiveBuildingAction b y) : Fin r → ℝ) + _
  calc
    topSum k
        (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
          (σ.projectiveBuildingAction b x) : Fin r → ℝ) ≤
      topSum k
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) +
        topSum k
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y
            (σ.projectiveBuildingAction b x) : Fin r → ℝ) :=
      DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_topSum_triangle
        x y (σ.projectiveBuildingAction b x) k hk
    _ ≤ topSum k
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) +
        (topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y
              (σ.projectiveBuildingAction b y) : Fin r → ℝ) +
          topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
              (σ.projectiveBuildingAction b y)
              (σ.projectiveBuildingAction b x) : Fin r → ℝ)) := by
      gcongr
      exact DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_topSum_triangle
        y (σ.projectiveBuildingAction b y) (σ.projectiveBuildingAction b x) k hk
    _ = topSum k
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y
            (σ.projectiveBuildingAction b y) : Fin r → ℝ) +
        (topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) +
          topSum k
            (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y x : Fin r → ℝ)) := by
      rw [σ.projectiveBuildingAction_euclideanRelativePosition]
      ring

noncomputable def differentialVariationalCartanPrefixOrbitGauge_boundedComparison
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) :
    SubadditiveClockGauge.BoundedComparison
      (differentialVariationalCartanPrefixOrbitGauge b x k hk)
      (differentialVariationalCartanPrefixOrbitGauge b y k hk) where
  forwardOverhead :=
    topSum k
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) +
    topSum k
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y x : Fin r → ℝ)
  backwardOverhead :=
    topSum k
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition y x : Fin r → ℝ) +
    topSum k
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ)
  cost_le_forward := differentialVariationalCartanPrefixOrbitGauge_cost_base_le b x y k hk
  cost_le_backward := differentialVariationalCartanPrefixOrbitGauge_cost_base_le b y x k hk

theorem differentialVariationalCartanPrefixTranslationLength_base_independent
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) (σ : DifferentialFieldAut C K) :
    differentialVariationalCartanPrefixTranslationLength b x k hk σ =
      differentialVariationalCartanPrefixTranslationLength b y k hk σ := by
  exact (differentialVariationalCartanPrefixOrbitGauge_boundedComparison
    b x y k hk).translationLength_eq σ

theorem differentialVariationalCartanTranslationVector_base_independent
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalCartanTranslationVector b x σ =
      differentialVariationalCartanTranslationVector b y σ := by
  funext i
  unfold differentialVariationalCartanTranslationVector
  rw [differentialVariationalCartanPrefixTranslationLength_base_independent b x y,
    differentialVariationalCartanPrefixTranslationLength_base_independent b x y]

theorem differentialVariationalCartanPrefixOrbitGauge_cost_changeBasis
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) (σ : DifferentialFieldAut C K) :
    (differentialVariationalCartanPrefixOrbitGauge b
      (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
        (variationalOreCompletedBasisTransition b c) x) k hk).cost σ =
      (differentialVariationalCartanPrefixOrbitGauge c x k hk).cost σ := by
  change topSum k
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
        (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
          (variationalOreCompletedBasisTransition b c) x)
        (σ.projectiveBuildingAction b
          (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
            (variationalOreCompletedBasisTransition b c) x)) : Fin r → ℝ) =
    topSum k
      (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
        (σ.projectiveBuildingAction c x) : Fin r → ℝ)
  unfold DifferentialFieldAut.projectiveBuildingAction
  rw [← variationalOreProjectiveBuildingAction_changeBasis σ.fixes σ.deriv_comm b c x]
  unfold DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
  rw [DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_mapLinear]

noncomputable def differentialVariationalCartanPrefixOrbitGauge_changeBasisComparison
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) :
    SubadditiveClockGauge.BoundedComparison
      (differentialVariationalCartanPrefixOrbitGauge b
        (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
          (variationalOreCompletedBasisTransition b c) x) k hk)
      (differentialVariationalCartanPrefixOrbitGauge c x k hk) where
  forwardOverhead := 0
  backwardOverhead := 0
  cost_le_forward := fun σ => by
    rw [differentialVariationalCartanPrefixOrbitGauge_cost_changeBasis b c x k hk σ,
      add_zero]
  cost_le_backward := fun σ => by
    rw [differentialVariationalCartanPrefixOrbitGauge_cost_changeBasis b c x k hk σ,
      add_zero]

theorem differentialVariationalCartanPrefixTranslationLength_basis_independent
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (k : ℕ) (hk : k ≤ r) (σ : DifferentialFieldAut C K) :
    differentialVariationalCartanPrefixTranslationLength b x k hk σ =
      differentialVariationalCartanPrefixTranslationLength c y k hk σ := by
  rw [differentialVariationalCartanPrefixTranslationLength_base_independent b x
    (DiffOp.mapDifferentialVariationalProjectiveBuildingCarrierMatrix
      (variationalOreCompletedBasisTransition b c) y) k hk σ]
  exact (differentialVariationalCartanPrefixOrbitGauge_changeBasisComparison
    b c y k hk).translationLength_eq σ

theorem differentialVariationalCartanTranslationVector_basis_independent
    {r : ℕ}
    (b c : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalCartanTranslationVector b x σ =
      differentialVariationalCartanTranslationVector c y σ := by
  funext i
  unfold differentialVariationalCartanTranslationVector
  rw [differentialVariationalCartanPrefixTranslationLength_basis_independent b c x y,
    differentialVariationalCartanPrefixTranslationLength_basis_independent b c x y]

end

end GaloisForLFunctions.HTGeometry
