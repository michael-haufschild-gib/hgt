import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuadraticIncidence
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# A cofinal block-triangle nuclear carrier

The full completed-endpoint RVM relocation is Schatten-1 but couples every marked prime.  Exact
finite-moment admission benefits from an orthogonal source-cycle reserve whose norm can be made
arbitrarily small.  This module selects pairwise disjoint, arbitrarily late positive
completed-endpoint triangles and places a normalized symmetric three-cycle on each block.

The resulting operator is source-defined, self-adjoint, Schatten-1, has zero diagonal, and retains
nonzero cycle holonomy on every selected block.  Geometric block weights give an absolute nuclear
budget without evaluating any source coefficient.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- Least-information choice of one positive consecutive-prime source triangle beyond `N`. -/
def routeKCofinalTriangleWitness (N : ℕ) : ℕ :=
  Classical.choose (exists_cofinal_positive_physicalEndpoint_pair_triangle N)

theorem routeKCofinalTriangleWitness_spec (N : ℕ) :
    N ≤ routeKCofinalTriangleWitness N ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (nthPrimeSubtype (routeKCofinalTriangleWitness N))
        (nthPrimeSubtype (routeKCofinalTriangleWitness N + 1)) ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (nthPrimeSubtype (routeKCofinalTriangleWitness N + 1))
        (nthPrimeSubtype (routeKCofinalTriangleWitness N + 2)) ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (nthPrimeSubtype (routeKCofinalTriangleWitness N + 2))
        (nthPrimeSubtype (routeKCofinalTriangleWitness N)) :=
  Classical.choose_spec
    (exists_cofinal_positive_physicalEndpoint_pair_triangle N)

/-- Recursive disjoint-block schedule. -/
def routeKCofinalTriangleStart : ℕ → ℕ
  | 0 => routeKCofinalTriangleWitness 0
  | n + 1 =>
      routeKCofinalTriangleWitness (routeKCofinalTriangleStart n + 3)

theorem routeKCofinalTriangleStart_add_three_le_succ (n : ℕ) :
    routeKCofinalTriangleStart n + 3 ≤
      routeKCofinalTriangleStart (n + 1) := by
  rw [routeKCofinalTriangleStart]
  exact (routeKCofinalTriangleWitness_spec
    (routeKCofinalTriangleStart n + 3)).1

theorem routeKCofinalTriangleStart_strictMono :
    StrictMono routeKCofinalTriangleStart := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := routeKCofinalTriangleStart_add_three_le_succ n
  omega

theorem routeKCofinalTriangleStart_self_le (n : ℕ) :
    n ≤ routeKCofinalTriangleStart n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have h := routeKCofinalTriangleStart_add_three_le_succ n
      omega

/-- Three prime vertices of selected block `n`. -/
def routeKCofinalTrianglePrime
    (n : ℕ) : Fin 3 → Nat.Primes :=
  ![nthPrimeSubtype (routeKCofinalTriangleStart n),
    nthPrimeSubtype (routeKCofinalTriangleStart n + 1),
    nthPrimeSubtype (routeKCofinalTriangleStart n + 2)]

/-- Cyclic successor vertex. -/
def routeKCofinalTrianglePrimeNext
    (n : ℕ) : Fin 3 → Nat.Primes :=
  ![nthPrimeSubtype (routeKCofinalTriangleStart n + 1),
    nthPrimeSubtype (routeKCofinalTriangleStart n + 2),
    nthPrimeSubtype (routeKCofinalTriangleStart n)]

@[simp] theorem routeKCofinalTrianglePrimeNext_zero (n : ℕ) :
    routeKCofinalTrianglePrimeNext n 0 =
      routeKCofinalTrianglePrime n 1 := by
  simp [routeKCofinalTrianglePrime, routeKCofinalTrianglePrimeNext]

@[simp] theorem routeKCofinalTrianglePrimeNext_one (n : ℕ) :
    routeKCofinalTrianglePrimeNext n 1 =
      routeKCofinalTrianglePrime n 2 := by
  simp [routeKCofinalTrianglePrime, routeKCofinalTrianglePrimeNext]

@[simp] theorem routeKCofinalTrianglePrimeNext_two (n : ℕ) :
    routeKCofinalTrianglePrimeNext n 2 =
      routeKCofinalTrianglePrime n 0 := by
  simp [routeKCofinalTrianglePrime, routeKCofinalTrianglePrimeNext]

theorem routeKCofinalTriangleStart_positiveResponses (n : ℕ) :
    0 < xiPhysicalEndpointCompletedPairResponse
        (routeKCofinalTrianglePrime n 0)
        (routeKCofinalTrianglePrimeNext n 0) ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (routeKCofinalTrianglePrime n 1)
        (routeKCofinalTrianglePrimeNext n 1) ∧
      0 < xiPhysicalEndpointCompletedPairResponse
        (routeKCofinalTrianglePrime n 2)
        (routeKCofinalTrianglePrimeNext n 2) := by
  cases n with
  | zero =>
      simpa [routeKCofinalTrianglePrime,
        routeKCofinalTrianglePrimeNext,
        routeKCofinalTriangleStart] using
        (routeKCofinalTriangleWitness_spec 0).2
  | succ k =>
      simpa [routeKCofinalTrianglePrime,
        routeKCofinalTrianglePrimeNext,
        routeKCofinalTriangleStart] using
        (routeKCofinalTriangleWitness_spec
          (routeKCofinalTriangleStart k + 3)).2

theorem routeKCofinalTrianglePrime_injective (n : ℕ) :
    Function.Injective (routeKCofinalTrianglePrime n) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    have hindex := nthPrimeSubtype_injective
      (by simpa [routeKCofinalTrianglePrime] using hij)
    omega

theorem routeKCofinalTrianglePrime_disjoint
    {m n : ℕ} (hmn : m < n) (i j : Fin 3) :
    routeKCofinalTrianglePrime m i ≠
      routeKCofinalTrianglePrime n j := by
  have hstep :
      routeKCofinalTriangleStart m + 3 ≤
        routeKCofinalTriangleStart (m + 1) :=
    routeKCofinalTriangleStart_add_three_le_succ m
  have hmono :
      routeKCofinalTriangleStart (m + 1) ≤
        routeKCofinalTriangleStart n :=
    routeKCofinalTriangleStart_strictMono.monotone (by omega)
  fin_cases i <;> fin_cases j
  all_goals
    intro heq
    have hindex := nthPrimeSubtype_injective
      (by simpa [routeKCofinalTrianglePrime] using heq)
    omega

/-- Actual RVM-relocation edge on selected block `n`. -/
def routeKCofinalTriangleRawEdge
    (n : ℕ) (i : Fin 3) : ℝ :=
  routeKPhysicalEndpointRVMTriangleEdge
    (routeKCofinalTrianglePrime n 0)
    (routeKCofinalTrianglePrime n 1)
    (routeKCofinalTrianglePrime n 2) i

theorem routeKCofinalTriangleRawEdge_pos
    (n : ℕ) (i : Fin 3) :
    0 < routeKCofinalTriangleRawEdge n i := by
  rcases routeKCofinalTriangleStart_positiveResponses n with
    ⟨h01, h12, h20⟩
  fin_cases i
  · simp only [routeKCofinalTriangleRawEdge,
      routeKPhysicalEndpointRVMTriangleEdge]
    exact mul_pos
      (sq_pos_of_ne_zero
        (sub_ne_zero.mpr
          (routeKPrimeRVMReciprocal_injective.ne
            ((routeKCofinalTrianglePrime_injective n).ne (by decide)))))
      h01
  · simp only [routeKCofinalTriangleRawEdge,
      routeKPhysicalEndpointRVMTriangleEdge]
    exact mul_pos
      (sq_pos_of_ne_zero
        (sub_ne_zero.mpr
          (routeKPrimeRVMReciprocal_injective.ne
            ((routeKCofinalTrianglePrime_injective n).ne (by decide)))))
      h12
  · simp only [routeKCofinalTriangleRawEdge,
      routeKPhysicalEndpointRVMTriangleEdge]
    exact mul_pos
      (sq_pos_of_ne_zero
        (sub_ne_zero.mpr
          (routeKPrimeRVMReciprocal_injective.ne
            ((routeKCofinalTrianglePrime_injective n).ne (by decide)))))
      h20

/-- Coefficient-independent normalization denominator for block `n`. -/
def routeKCofinalTriangleDenominator (n : ℕ) : ℝ :=
  1 + ∑ i : Fin 3, |routeKCofinalTriangleRawEdge n i|

theorem routeKCofinalTriangleDenominator_pos (n : ℕ) :
    0 < routeKCofinalTriangleDenominator n := by
  rw [routeKCofinalTriangleDenominator]
  positivity

/-- Geometrically summable positive source edge amplitude. -/
def routeKCofinalTriangleAmplitude
    (n : ℕ) (i : Fin 3) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1) *
    routeKCofinalTriangleRawEdge n i /
      routeKCofinalTriangleDenominator n

theorem routeKCofinalTriangleAmplitude_pos
    (n : ℕ) (i : Fin 3) :
    0 < routeKCofinalTriangleAmplitude n i := by
  rw [routeKCofinalTriangleAmplitude]
  exact div_pos
    (mul_pos (pow_pos (by norm_num) _)
      (routeKCofinalTriangleRawEdge_pos n i))
    (routeKCofinalTriangleDenominator_pos n)

theorem abs_routeKCofinalTriangleAmplitude_le
    (n : ℕ) (i : Fin 3) :
    |routeKCofinalTriangleAmplitude n i| ≤
      (1 / 2 : ℝ) ^ (n + 1) := by
  rw [abs_of_pos (routeKCofinalTriangleAmplitude_pos n i),
    routeKCofinalTriangleAmplitude]
  have hedge :
      routeKCofinalTriangleRawEdge n i ≤
        routeKCofinalTriangleDenominator n := by
    rw [routeKCofinalTriangleDenominator]
    have hi :
        |routeKCofinalTriangleRawEdge n i| ≤
          ∑ j : Fin 3, |routeKCofinalTriangleRawEdge n j| :=
      Finset.single_le_sum
        (fun j _ => abs_nonneg (routeKCofinalTriangleRawEdge n j))
        (Finset.mem_univ i)
    rw [abs_of_pos (routeKCofinalTriangleRawEdge_pos n i)] at hi
    linarith
  rw [div_le_iff₀ (routeKCofinalTriangleDenominator_pos n)]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (n + 1)]

/-- One oriented rank-one half-edge.  The two `Fin 2` orientations are adjoint to each other. -/
def routeKCofinalTriangleRankOneTerm
    (idx : ℕ × Fin 3 × Fin 2) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  if idx.2.2 = 0 then
    (routeKCofinalTriangleAmplitude idx.1 idx.2.1 : ℂ) •
      InnerProductSpace.rankOne ℂ
        (routeKPrimeBasis (routeKCofinalTrianglePrime idx.1 idx.2.1))
        (routeKPrimeBasis (routeKCofinalTrianglePrimeNext idx.1 idx.2.1))
  else
    (routeKCofinalTriangleAmplitude idx.1 idx.2.1 : ℂ) •
      InnerProductSpace.rankOne ℂ
        (routeKPrimeBasis (routeKCofinalTrianglePrimeNext idx.1 idx.2.1))
        (routeKPrimeBasis (routeKCofinalTrianglePrime idx.1 idx.2.1))

theorem routeKCofinalTriangleRankOneTerm_hasRankLE
    (idx : ℕ × Fin 3 × Fin 2) :
    HasRankLE (routeKCofinalTriangleRankOneTerm idx) 1 := by
  rw [routeKCofinalTriangleRankOneTerm]
  split_ifs
  · apply hasRankLE_smul
    simpa using hasRankLE_sum_range_rankOne
      (fun _ : ℕ =>
        routeKPrimeBasis (routeKCofinalTrianglePrime idx.1 idx.2.1))
      (fun _ : ℕ =>
        routeKPrimeBasis (routeKCofinalTrianglePrimeNext idx.1 idx.2.1)) 1
  · apply hasRankLE_smul
    simpa using hasRankLE_sum_range_rankOne
      (fun _ : ℕ =>
        routeKPrimeBasis (routeKCofinalTrianglePrimeNext idx.1 idx.2.1))
      (fun _ : ℕ =>
        routeKPrimeBasis (routeKCofinalTrianglePrime idx.1 idx.2.1)) 1

theorem norm_routeKCofinalTriangleRankOneTerm
    (idx : ℕ × Fin 3 × Fin 2) :
    ‖routeKCofinalTriangleRankOneTerm idx‖ =
      |routeKCofinalTriangleAmplitude idx.1 idx.2.1| := by
  rw [routeKCofinalTriangleRankOneTerm]
  split_ifs <;>
    simp_rw [routeKPrimeBasis] <;>
    rw [norm_smul, InnerProductSpace.norm_rankOne,
      Complex.norm_real, Real.norm_eq_abs,
      lp.norm_single (by norm_num : (0 : ENNReal) < 2),
      lp.norm_single (by norm_num : (0 : ENNReal) < 2),
      norm_one, mul_one]
  all_goals simp

theorem summable_norm_routeKCofinalTriangleRankOneTerm :
    Summable (fun idx : ℕ × Fin 3 × Fin 2 =>
      ‖routeKCofinalTriangleRankOneTerm idx‖) := by
  have hmajor :
      Summable (fun idx : ℕ × Fin 3 × Fin 2 =>
        (1 / 2 : ℝ) ^ (idx.1 + 1)) := by
    rw [summable_prod_of_nonneg
      (fun _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)]
    constructor
    · intro n
      exact Summable.of_finite
    · have hgeo :
          Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
        exact
          (summable_geometric_of_norm_lt_one
            (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).mul_left (1 / 2)
            |>.congr (fun n => by ring)
      simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul] using
        hgeo.mul_left 6
  refine Summable.of_nonneg_of_le
    (fun idx => norm_nonneg _)
    ?_ hmajor
  intro idx
  rw [norm_routeKCofinalTriangleRankOneTerm]
  exact abs_routeKCofinalTriangleAmplitude_le idx.1 idx.2.1

/-- Absolutely nuclear, block-diagonal cofinal source-cycle carrier. -/
def routeKCofinalTriangleNuclearCarrier :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  ∑' idx : ℕ × Fin 3 × Fin 2,
    routeKCofinalTriangleRankOneTerm idx

theorem routeKCofinalTriangleNuclearCarrier_memSchattenClass_one :
    MemSchattenClass 1 routeKCofinalTriangleNuclearCarrier :=
  memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    routeKCofinalTriangleRankOneTerm
    routeKCofinalTriangleRankOneTerm_hasRankLE
    summable_norm_routeKCofinalTriangleRankOneTerm

/-- One explicitly symmetric selected triangle block. -/
def routeKCofinalTriangleSymmetricBlock
    (n : ℕ) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  ∑ i : Fin 3,
    (routeKCofinalTriangleAmplitude n i : ℂ) •
      (InnerProductSpace.rankOne ℂ
          (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i)) +
        InnerProductSpace.rankOne ℂ
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))
          (routeKPrimeBasis (routeKCofinalTrianglePrime n i)))

theorem routeKCofinalTriangleRankOneTerm_sum_fiber
    (n : ℕ) :
    ∑ io : Fin 3 × Fin 2,
        routeKCofinalTriangleRankOneTerm (n, io) =
      routeKCofinalTriangleSymmetricBlock n := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp [routeKCofinalTriangleRankOneTerm, smul_add]

theorem routeKCofinalTriangleNuclearCarrier_eq_tsum_blocks :
    routeKCofinalTriangleNuclearCarrier =
      ∑' n : ℕ, routeKCofinalTriangleSymmetricBlock n := by
  rw [routeKCofinalTriangleNuclearCarrier,
    (Summable.of_norm
      summable_norm_routeKCofinalTriangleRankOneTerm).tsum_prod]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  exact routeKCofinalTriangleRankOneTerm_sum_fiber n

theorem routeKCofinalTriangleSymmetricBlock_isSelfAdjoint
    (n : ℕ) :
    IsSelfAdjoint (routeKCofinalTriangleSymmetricBlock n) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff',
    routeKCofinalTriangleSymmetricBlock]
  change star (∑ i : Fin 3,
    (routeKCofinalTriangleAmplitude n i : ℂ) •
      (InnerProductSpace.rankOne ℂ
          (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i)) +
        InnerProductSpace.rankOne ℂ
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))
          (routeKPrimeBasis (routeKCofinalTrianglePrime n i)))) = _
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_smul, star_add]
  change
    star (routeKCofinalTriangleAmplitude n i : ℂ) •
        (ContinuousLinearMap.adjoint
            (InnerProductSpace.rankOne ℂ
              (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
              (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))) +
          ContinuousLinearMap.adjoint
            (InnerProductSpace.rankOne ℂ
              (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))
              (routeKPrimeBasis (routeKCofinalTrianglePrime n i)))) =
      (routeKCofinalTriangleAmplitude n i : ℂ) •
        (InnerProductSpace.rankOne ℂ
            (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
            (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i)) +
          InnerProductSpace.rankOne ℂ
            (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))
            (routeKPrimeBasis (routeKCofinalTrianglePrime n i)))
  rw [InnerProductSpace.adjoint_rankOne,
    InnerProductSpace.adjoint_rankOne]
  simp [add_comm]

theorem routeKCofinalTriangleNuclearCarrier_isSelfAdjoint :
    IsSelfAdjoint routeKCofinalTriangleNuclearCarrier := by
  rw [routeKCofinalTriangleNuclearCarrier_eq_tsum_blocks,
    ContinuousLinearMap.isSelfAdjoint_iff']
  change star (∑' n : ℕ, routeKCofinalTriangleSymmetricBlock n) = _
  rw [tsum_star]
  apply tsum_congr
  intro n
  exact routeKCofinalTriangleSymmetricBlock_isSelfAdjoint n

theorem routeKCofinalTriangleNuclearCarrier_isHilbertSchmidt :
    routeKCofinalTriangleNuclearCarrier.IsHilbertSchmidt := by
  obtain ⟨S, U, _, hU, hfac⟩ :=
    routeKCofinalTriangleNuclearCarrier_memSchattenClass_one.one_isTraceClass
  rw [hfac]
  exact hU.comp_left S

theorem inner_routeKPrimeBasis_routeKPrimeBasis
    (p q : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p) (routeKPrimeBasis q) =
      if p = q then 1 else 0 := by
  by_cases hpq : p = q
  · subst q
    simp [routeKPrimeBasis]
  · simp [routeKPrimeBasis, lp.inner_single_left, hpq]

theorem routeKCofinalTriangleSymmetricBlock_matrix
    (n : ℕ) (p q : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis q)) =
      ∑ i : Fin 3, (routeKCofinalTriangleAmplitude n i : ℂ) *
        (((if p = routeKCofinalTrianglePrime n i then 1 else 0) *
            (if routeKCofinalTrianglePrimeNext n i = q then 1 else 0)) +
          ((if p = routeKCofinalTrianglePrimeNext n i then 1 else 0) *
            (if routeKCofinalTrianglePrime n i = q then 1 else 0))) := by
  let L : (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (routeKPrimeBasis p)).comp
      (ContinuousLinearMap.apply ℂ RouteKPrimeHilbert (routeKPrimeBasis q))
  change L (routeKCofinalTriangleSymmetricBlock n) = _
  rw [routeKCofinalTriangleSymmetricBlock, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change
    (routeKCofinalTriangleAmplitude n i : ℂ) *
      inner ℂ (routeKPrimeBasis p)
        ((InnerProductSpace.rankOne ℂ
              (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
              (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i)) +
            InnerProductSpace.rankOne ℂ
              (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))
              (routeKPrimeBasis (routeKCofinalTrianglePrime n i)))
          (routeKPrimeBasis q)) = _
  rw [add_apply, inner_add_right,
    InnerProductSpace.inner_right_rankOne_apply,
    InnerProductSpace.inner_right_rankOne_apply,
    inner_routeKPrimeBasis_routeKPrimeBasis,
    inner_routeKPrimeBasis_routeKPrimeBasis,
    inner_routeKPrimeBasis_routeKPrimeBasis,
    inner_routeKPrimeBasis_routeKPrimeBasis]

theorem routeKCofinalTriangleSymmetricBlock_selectedEdge
    (n : ℕ) (i : Fin 3) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))) =
      (routeKCofinalTriangleAmplitude n i : ℂ) := by
  rw [routeKCofinalTriangleSymmetricBlock_matrix]
  fin_cases i <;>
    simp [Fin.sum_univ_three,
      (routeKCofinalTrianglePrime_injective n).eq_iff]

theorem routeKCofinalTriangleSymmetricBlock_otherBlock_selectedEdge_zero
    {m n : ℕ} (hmn : m ≠ n) (i : Fin 3) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
        (routeKCofinalTriangleSymmetricBlock m
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))) = 0 := by
  rcases lt_or_gt_of_ne hmn with hmnlt | hmnlt
  · fin_cases i <;>
      rw [routeKCofinalTriangleSymmetricBlock_matrix] <;>
      simp [Fin.sum_univ_three,
        routeKCofinalTrianglePrime_disjoint hmnlt]
  · have hnm : n < m := hmnlt
    fin_cases i <;>
      rw [routeKCofinalTriangleSymmetricBlock_matrix] <;>
      simp [Fin.sum_univ_three,
        routeKCofinalTrianglePrime_disjoint hnm]

theorem summable_routeKCofinalTriangleSymmetricBlock :
    Summable routeKCofinalTriangleSymmetricBlock := by
  have hterm :
      Summable routeKCofinalTriangleRankOneTerm :=
    Summable.of_norm summable_norm_routeKCofinalTriangleRankOneTerm
  have hblock :
      Summable (fun n : ℕ =>
        ∑' io : Fin 3 × Fin 2,
          routeKCofinalTriangleRankOneTerm (n, io)) :=
    hterm.prod
  exact hblock.congr fun n => by
    rw [tsum_fintype]
    exact routeKCofinalTriangleRankOneTerm_sum_fiber n

/-- Exact selected-block source matrix entry of the global nuclear carrier. -/
theorem routeKCofinalTriangleNuclearCarrier_selectedEdge
    (n : ℕ) (i : Fin 3) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
        (routeKCofinalTriangleNuclearCarrier
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))) =
      (routeKCofinalTriangleAmplitude n i : ℂ) := by
  let L : (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n i))).comp
      (ContinuousLinearMap.apply ℂ RouteKPrimeHilbert
        (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i)))
  rw [routeKCofinalTriangleNuclearCarrier_eq_tsum_blocks]
  have hmap := L.map_tsum summable_routeKCofinalTriangleSymmetricBlock
  rw [show inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
      ((∑' m, routeKCofinalTriangleSymmetricBlock m)
        (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))) =
      ∑' m, inner ℂ
        (routeKPrimeBasis (routeKCofinalTrianglePrime n i))
        (routeKCofinalTriangleSymmetricBlock m
          (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n i))) by
    simpa [L] using hmap]
  rw [tsum_eq_single n]
  · exact routeKCofinalTriangleSymmetricBlock_selectedEdge n i
  · intro m hmn
    exact routeKCofinalTriangleSymmetricBlock_otherBlock_selectedEdge_zero
      hmn i

/-- Every selected global triangle has nonzero holonomy. -/
theorem routeKCofinalTriangleNuclearCarrier_selectedHolonomy_ne_zero
    (n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))
        (routeKCofinalTriangleNuclearCarrier
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))) *
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))
        (routeKCofinalTriangleNuclearCarrier
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))) *
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))
        (routeKCofinalTriangleNuclearCarrier
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))) ≠ 0 := by
  have h :
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))
          (routeKCofinalTriangleNuclearCarrier
            (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n 0))) *
        inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))
          (routeKCofinalTriangleNuclearCarrier
            (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n 1))) *
        inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))
          (routeKCofinalTriangleNuclearCarrier
            (routeKPrimeBasis (routeKCofinalTrianglePrimeNext n 2))) ≠ 0 := by
    rw [routeKCofinalTriangleNuclearCarrier_selectedEdge,
      routeKCofinalTriangleNuclearCarrier_selectedEdge,
      routeKCofinalTriangleNuclearCarrier_selectedEdge]
    exact mul_ne_zero
      (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (routeKCofinalTriangleAmplitude_pos n 0).ne')
        (Complex.ofReal_ne_zero.mpr
          (routeKCofinalTriangleAmplitude_pos n 1).ne'))
      (Complex.ofReal_ne_zero.mpr
        (routeKCofinalTriangleAmplitude_pos n 2).ne')
  simpa using h

/-- Selected cycle blocks occur beyond every prime index. -/
theorem exists_cofinal_routeKCofinalTriangleNuclearCarrier_holonomy
    (N : ℕ) :
    ∃ n : ℕ, N ≤ routeKCofinalTriangleStart n ∧
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))
          (routeKCofinalTriangleNuclearCarrier
            (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))) *
        inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))
          (routeKCofinalTriangleNuclearCarrier
            (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))) *
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))
          (routeKCofinalTriangleNuclearCarrier
            (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))) ≠ 0 := by
  exact ⟨N, routeKCofinalTriangleStart_self_le N,
    routeKCofinalTriangleNuclearCarrier_selectedHolonomy_ne_zero N⟩

/-- Rank-one expansion of the carrier after discarding its first `K` triangle blocks. -/
def routeKCofinalTriangleTailTerm
    (K : ℕ) (idx : ℕ × Fin 3 × Fin 2) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  routeKCofinalTriangleRankOneTerm (idx.1 + K, idx.2)

theorem summable_norm_routeKCofinalTriangleTailTerm (K : ℕ) :
    Summable (fun idx : ℕ × Fin 3 × Fin 2 =>
      ‖routeKCofinalTriangleTailTerm K idx‖) := by
  have hinj : Function.Injective
      (fun idx : ℕ × Fin 3 × Fin 2 => (idx.1 + K, idx.2)) := by
    rintro ⟨a, ia⟩ ⟨b, ib⟩ hab
    simp only [Prod.mk.injEq] at hab ⊢
    exact ⟨Nat.add_right_cancel hab.1, hab.2⟩
  exact summable_norm_routeKCofinalTriangleRankOneTerm.comp_injective hinj

/-- Cofinal nuclear carrier whose first active block is block `K`. -/
def routeKCofinalTriangleNuclearCarrierFrom (K : ℕ) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  ∑' idx : ℕ × Fin 3 × Fin 2,
    routeKCofinalTriangleTailTerm K idx

theorem routeKCofinalTriangleNuclearCarrierFrom_memSchattenClass_one
    (K : ℕ) :
    MemSchattenClass 1 (routeKCofinalTriangleNuclearCarrierFrom K) := by
  apply memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    (routeKCofinalTriangleTailTerm K)
  · intro idx
    exact routeKCofinalTriangleRankOneTerm_hasRankLE (idx.1 + K, idx.2)
  · exact summable_norm_routeKCofinalTriangleTailTerm K

theorem summable_routeKCofinalTriangleSymmetricBlock_add (K : ℕ) :
    Summable (fun n : ℕ => routeKCofinalTriangleSymmetricBlock (n + K)) :=
  summable_routeKCofinalTriangleSymmetricBlock.comp_injective
    (fun _ _ h => Nat.add_right_cancel h)

theorem routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks
    (K : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K =
      ∑' n : ℕ, routeKCofinalTriangleSymmetricBlock (n + K) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom,
    ((Summable.of_norm
      (summable_norm_routeKCofinalTriangleTailTerm K)).tsum_prod)]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  exact routeKCofinalTriangleRankOneTerm_sum_fiber (n + K)

theorem routeKCofinalTriangleNuclearCarrierFrom_isSelfAdjoint
    (K : ℕ) :
    IsSelfAdjoint (routeKCofinalTriangleNuclearCarrierFrom K) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks,
    ContinuousLinearMap.isSelfAdjoint_iff']
  change star (∑' n : ℕ,
    routeKCofinalTriangleSymmetricBlock (n + K)) = _
  rw [tsum_star]
  apply tsum_congr
  intro n
  exact routeKCofinalTriangleSymmetricBlock_isSelfAdjoint (n + K)

theorem routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt
    (K : ℕ) :
    (routeKCofinalTriangleNuclearCarrierFrom K).IsHilbertSchmidt := by
  have hmem :
      MemSchattenClass 1 (routeKCofinalTriangleNuclearCarrierFrom K) :=
    routeKCofinalTriangleNuclearCarrierFrom_memSchattenClass_one K
  have htrace := hmem.one_isTraceClass
  obtain ⟨S, U, _, hU, hfac⟩ := htrace
  rw [hfac]
  exact hU.comp_left S

/-- Exact selected edge after the finite block cut. -/
theorem routeKCofinalTriangleNuclearCarrierFrom_selectedEdge
    (K n : ℕ) (i : Fin 3) :
    inner ℂ (routeKPrimeBasis
        (routeKCofinalTrianglePrime (n + K) i))
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKPrimeBasis
          (routeKCofinalTrianglePrimeNext (n + K) i))) =
      (routeKCofinalTriangleAmplitude (n + K) i : ℂ) := by
  let L : (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (routeKPrimeBasis
      (routeKCofinalTrianglePrime (n + K) i))).comp
      (ContinuousLinearMap.apply ℂ RouteKPrimeHilbert
        (routeKPrimeBasis
          (routeKCofinalTrianglePrimeNext (n + K) i)))
  rw [routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks]
  have hmap := L.map_tsum
    (summable_routeKCofinalTriangleSymmetricBlock_add K)
  rw [show inner ℂ
      (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) i))
      ((∑' m, routeKCofinalTriangleSymmetricBlock (m + K))
        (routeKPrimeBasis
          (routeKCofinalTrianglePrimeNext (n + K) i))) =
      ∑' m, inner ℂ
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) i))
        (routeKCofinalTriangleSymmetricBlock (m + K)
          (routeKPrimeBasis
            (routeKCofinalTrianglePrimeNext (n + K) i))) by
    simpa [L] using hmap]
  rw [tsum_eq_single n]
  · exact routeKCofinalTriangleSymmetricBlock_selectedEdge (n + K) i
  · intro m hmn
    apply routeKCofinalTriangleSymmetricBlock_otherBlock_selectedEdge_zero
    exact fun h => hmn (Nat.add_right_cancel h)

/-- Every retained block still has exact nonzero holonomy. -/
theorem routeKCofinalTriangleNuclearCarrierFrom_selectedHolonomy_ne_zero
    (K n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))) *
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))) *
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))) ≠ 0 := by
  have h :
      inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis
              (routeKCofinalTrianglePrimeNext (n + K) 0))) *
        inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis
              (routeKCofinalTrianglePrimeNext (n + K) 1))) *
        inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis
              (routeKCofinalTrianglePrimeNext (n + K) 2))) ≠ 0 := by
    rw [routeKCofinalTriangleNuclearCarrierFrom_selectedEdge,
      routeKCofinalTriangleNuclearCarrierFrom_selectedEdge,
      routeKCofinalTriangleNuclearCarrierFrom_selectedEdge]
    exact mul_ne_zero
      (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (routeKCofinalTriangleAmplitude_pos (n + K) 0).ne')
        (Complex.ofReal_ne_zero.mpr
          (routeKCofinalTriangleAmplitude_pos (n + K) 1).ne'))
      (Complex.ofReal_ne_zero.mpr
        (routeKCofinalTriangleAmplitude_pos (n + K) 2).ne')
  simpa using h

theorem nthPrimeEquiv_symm_routeKCofinalTrianglePrime
    (n : ℕ) (i : Fin 3) :
    nthPrimeEquiv.symm (routeKCofinalTrianglePrime n i) =
      routeKCofinalTriangleStart n + i := by
  fin_cases i
  · change nthPrimeEquiv.symm
      (nthPrimeEquiv (routeKCofinalTriangleStart n)) = _
    exact nthPrimeEquiv.symm_apply_apply _
  · change nthPrimeEquiv.symm
      (nthPrimeEquiv (routeKCofinalTriangleStart n + 1)) = _
    exact nthPrimeEquiv.symm_apply_apply _
  · change nthPrimeEquiv.symm
      (nthPrimeEquiv (routeKCofinalTriangleStart n + 2)) = _
    exact nthPrimeEquiv.symm_apply_apply _

theorem nthPrimeEquiv_symm_routeKCofinalTrianglePrimeNext_ge
    (n : ℕ) (i : Fin 3) :
    routeKCofinalTriangleStart n ≤
      nthPrimeEquiv.symm (routeKCofinalTrianglePrimeNext n i) := by
  fin_cases i
  · change routeKCofinalTriangleStart n ≤
      nthPrimeEquiv.symm
        (nthPrimeEquiv (routeKCofinalTriangleStart n + 1))
    rw [nthPrimeEquiv.symm_apply_apply]
    omega
  · change routeKCofinalTriangleStart n ≤
      nthPrimeEquiv.symm
        (nthPrimeEquiv (routeKCofinalTriangleStart n + 2))
    rw [nthPrimeEquiv.symm_apply_apply]
    omega
  · change routeKCofinalTriangleStart n ≤
      nthPrimeEquiv.symm
        (nthPrimeEquiv (routeKCofinalTriangleStart n))
    rw [nthPrimeEquiv.symm_apply_apply]

/-- Every selected block annihilates all marked-prime basis vectors before its start index. -/
theorem routeKCofinalTriangleSymmetricBlock_basis_eq_zero_of_index_lt_start
    {n : ℕ} {p : Nat.Primes}
    (hp : nthPrimeEquiv.symm p < routeKCofinalTriangleStart n) :
    routeKCofinalTriangleSymmetricBlock n (routeKPrimeBasis p) = 0 := by
  apply lp.ext
  funext q
  have hpPrime :
      ∀ i : Fin 3, routeKCofinalTrianglePrime n i ≠ p := by
    intro i hip
    have hindex := congrArg nthPrimeEquiv.symm hip
    rw [nthPrimeEquiv_symm_routeKCofinalTrianglePrime] at hindex
    omega
  have hpNext :
      ∀ i : Fin 3, routeKCofinalTrianglePrimeNext n i ≠ p := by
    intro i hip
    have hindex := congrArg nthPrimeEquiv.symm hip
    have hge :=
      nthPrimeEquiv_symm_routeKCofinalTrianglePrimeNext_ge n i
    omega
  have hinner :
      inner ℂ (routeKPrimeBasis q)
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis p)) = 0 := by
    rw [routeKCofinalTriangleSymmetricBlock_matrix]
    apply Finset.sum_eq_zero
    intro i _
    simp [hpPrime i, hpNext i]
  simpa [routeKPrimeBasis, lp.inner_single_left] using hinner

/-- Cutting before block `K` isolates the carrier from every prime index below `K`. -/
theorem routeKCofinalTriangleNuclearCarrierFrom_basis_eq_zero_of_index_lt
    {K : ℕ} {p : Nat.Primes} (hp : nthPrimeEquiv.symm p < K) :
    routeKCofinalTriangleNuclearCarrierFrom K
        (routeKPrimeBasis p) = 0 := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks]
  let A :
      (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ]
        RouteKPrimeHilbert :=
    ContinuousLinearMap.apply ℂ RouteKPrimeHilbert (routeKPrimeBasis p)
  have hmap :=
    A.map_tsum (summable_routeKCofinalTriangleSymmetricBlock_add K)
  rw [show
      (∑' n : ℕ, routeKCofinalTriangleSymmetricBlock (n + K))
          (routeKPrimeBasis p) =
        ∑' n : ℕ, routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis p) by
      simpa [A] using hmap]
  have hzero :
      (fun n : ℕ => routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKPrimeBasis p)) = 0 := by
    funext n
    apply routeKCofinalTriangleSymmetricBlock_basis_eq_zero_of_index_lt_start
    have hstart : n + K ≤ routeKCofinalTriangleStart (n + K) :=
      routeKCofinalTriangleStart_self_le (n + K)
    omega
  rw [hzero]
  exact tsum_zero

/-- A triangle edge never returns to its starting prime. -/
theorem routeKCofinalTrianglePrime_ne_next
    (n : ℕ) (i : Fin 3) :
    routeKCofinalTrianglePrime n i ≠
      routeKCofinalTrianglePrimeNext n i := by
  fin_cases i
  · change nthPrimeEquiv (routeKCofinalTriangleStart n) ≠
      nthPrimeEquiv (routeKCofinalTriangleStart n + 1)
    exact nthPrimeEquiv.injective.ne (by omega)
  · change nthPrimeEquiv (routeKCofinalTriangleStart n + 1) ≠
      nthPrimeEquiv (routeKCofinalTriangleStart n + 2)
    exact nthPrimeEquiv.injective.ne (by omega)
  · change nthPrimeEquiv (routeKCofinalTriangleStart n + 2) ≠
      nthPrimeEquiv (routeKCofinalTriangleStart n)
    exact nthPrimeEquiv.injective.ne (by omega)

/-- Every finite triangle block has exactly zero diagonal. -/
theorem routeKCofinalTriangleSymmetricBlock_diagonal_zero
    (n : ℕ) (p : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis p)) = 0 := by
  rw [routeKCofinalTriangleSymmetricBlock_matrix]
  apply Finset.sum_eq_zero
  intro i _
  have hne := routeKCofinalTrianglePrime_ne_next n i
  by_cases hp : p = routeKCofinalTrianglePrime n i
  · simp [hp, hne, Ne.symm hne]
  · by_cases hn : p = routeKCofinalTrianglePrimeNext n i
    · simp [hn, hne, Ne.symm hne]
    · simp [hp, hn]

/-- The cofinal trace-class carrier has no diagonal contamination at any marked prime. -/
theorem routeKCofinalTriangleNuclearCarrierFrom_diagonal_zero
    (K : ℕ) (p : Nat.Primes) :
    inner ℂ (routeKPrimeBasis p)
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKPrimeBasis p)) = 0 := by
  let L :
      (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (routeKPrimeBasis p)).comp
      (ContinuousLinearMap.apply ℂ RouteKPrimeHilbert
        (routeKPrimeBasis p))
  rw [routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks]
  have hmap :=
    L.map_tsum (summable_routeKCofinalTriangleSymmetricBlock_add K)
  rw [show
      inner ℂ (routeKPrimeBasis p)
        ((∑' n, routeKCofinalTriangleSymmetricBlock (n + K))
          (routeKPrimeBasis p)) =
        ∑' n, inner ℂ (routeKPrimeBasis p)
          (routeKCofinalTriangleSymmetricBlock (n + K)
            (routeKPrimeBasis p)) by
      simpa [L] using hmap]
  have hzero :
      (fun n : ℕ =>
        inner ℂ (routeKPrimeBasis p)
          (routeKCofinalTriangleSymmetricBlock (n + K)
            (routeKPrimeBasis p))) = 0 := by
    funext n
    exact routeKCofinalTriangleSymmetricBlock_diagonal_zero (n + K) p
  rw [hzero]
  exact tsum_zero

end

end RHTower
