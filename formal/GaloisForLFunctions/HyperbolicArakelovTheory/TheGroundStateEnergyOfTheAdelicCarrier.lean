import GaloisForLFunctions.HyperbolicArakelovTheory.TheRestrictedGreenProductHasSummableSources

/-!
# Ground-state energy on the restricted adelic carrier

The actual weighted adjacency has a symmetric matrix on every finite
configuration. Its energy splits into interior edge squares, outgoing
boundary energy, and the source potential of the restricted Green product.
Common coordinate agreement supplies a strictly positive intrinsic mass.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicAdjacency CoupledProductObstruction PrimeFibres

/-- Actual neighbours in the restricted product, with one coordinate changed. -/
def neighborVertices (p : Prime) (y : FiniteVertices) : Finset FiniteVertices :=
  (neighbors p (y.1 p)).image (replaceVertex p y)

def localEntry (p : Prime) (y z : FiniteVertices) : ℝ :=
  if z ∈ neighborVertices p y then weight p else 0

def adjacencyKernel (y z : FiniteVertices) : ℝ := ∑' p, localEntry p y z

/-- Extend the charges on a finite configuration by zero. -/
def finiteSource (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) : ℝ := if y ∈ F then f y else 0

theorem localAdj_eq_sum_vertices (p : Prime) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) : localAdj p f y = ∑ z ∈ neighborVertices p y, f z := by
  rw [neighborVertices, Finset.sum_image (replaceVertex_injective p y).injOn]
  rfl

theorem mem_neighborVertices_iff (p : Prime) (y z : FiniteVertices) :
    z ∈ neighborVertices p y ↔ SameFibre p y z ∧ Adjacent p (y.1 p) (z.1 p) := by
  constructor
  · rintro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨?_, ?_⟩
    · intro q hq
      exact (replaceVertex_away p y w q hq).symm
    · rw [replaceVertex_at]
      exact (mem_neighbors p _ _).mp hw
  · rintro ⟨hf, ha⟩
    exact Finset.mem_image.mpr ⟨z.1 p, (mem_neighbors p _ _).mpr ha,
      eq_replace_of_sameFibre p hf⟩

theorem neighborVertices_symm (p : Prime) (y z : FiniteVertices) :
    z ∈ neighborVertices p y ↔ y ∈ neighborVertices p z := by
  rw [mem_neighborVertices_iff, mem_neighborVertices_iff]
  constructor <;> rintro ⟨hf, ha⟩
  · exact ⟨fun q hq => (hf q hq).symm, adjacent_symm p _ _ ha⟩
  · exact ⟨fun q hq => (hf q hq).symm, adjacent_symm p _ _ ha⟩

theorem localEntry_nonneg (p : Prime) (y z : FiniteVertices) : 0 ≤ localEntry p y z := by
  unfold localEntry
  split_ifs
  · exact (weight_pos p).le
  · exact le_rfl

theorem adjacencyKernel_nonneg (y z : FiniteVertices) : 0 ≤ adjacencyKernel y z :=
  tsum_nonneg (fun p => localEntry_nonneg p y z)

theorem adjacencyKernel_symm (y z : FiniteVertices) :
    adjacencyKernel y z = adjacencyKernel z y := by
  apply tsum_congr
  intro p
  simp only [localEntry, neighborVertices_symm p y z]

/-- The positive product row dominates each matrix entry and proves its summability. -/
theorem summable_localEntry (y z : FiniteVertices) : Summable (fun p => localEntry p y z) := by
  apply Summable.of_nonneg_of_le (fun p => localEntry_nonneg p y z) _ (product_inDomain z y)
  intro p
  unfold localEntry
  split_ifs with hz
  · rw [placeTerm, localAdj_eq_sum_vertices]
    have h := Finset.single_le_sum (fun w _ => (product_pos z w).le) hz
    rw [product_self] at h
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (weight_pos p).le
  · exact placeTerm_nonneg p (fun w => (product_pos z w).le) y

theorem placeTerm_finiteSource (p : Prime) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) (y : FiniteVertices) :
    placeTerm p (finiteSource F f) y = ∑ z ∈ F, localEntry p y z * f z := by
  have hfilt : (∑ z ∈ neighborVertices p y, if z ∈ F then f z else 0) =
      ∑ z ∈ F, if z ∈ neighborVertices p y then f z else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext z
    simp only [Finset.mem_filter, and_comm]
  rw [placeTerm, localAdj_eq_sum_vertices]
  change weight p * (∑ z ∈ neighborVertices p y, if z ∈ F then f z else 0) = _
  rw [hfilt, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  unfold localEntry
  split_ifs <;> simp only [mul_zero, zero_mul]

theorem finiteSource_hasSum (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) :
    HasSum (fun p => placeTerm p (finiteSource F f) y)
      (∑ z ∈ F, adjacencyKernel y z * f z) := by
  simp_rw [placeTerm_finiteSource]
  exact hasSum_sum (fun z _ => (summable_localEntry y z).hasSum.mul_right (f z))

/-- Every finite signed charge is in the domain of the full prime sum. -/
theorem finiteSource_inDomain (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    InDomain (finiteSource F f) := fun y => (finiteSource_hasSum F f y).summable

theorem adjacency_finiteSource (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) :
    adjacency (finiteSource F f) y = ∑ z ∈ F, adjacencyKernel y z * f z :=
  (finiteSource_hasSum F f y).tsum_eq

/-- Energy of the actual weighted operator on a finite configuration. -/
def energy (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) : ℝ :=
  edge * ∑ y ∈ F, f y ^ 2 - ∑ y ∈ F, f y * adjacency (finiteSource F f) y

def boundary (x : FiniteVertices) (F : Finset FiniteVertices) (y : FiniteVertices) : ℝ :=
  adjacency (finiteGreenProduct x) y - adjacency (finiteSource F (finiteGreenProduct x)) y

def boundaryEnergy (x : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) : ℝ :=
  ∑ y ∈ F, boundary x F y * f y ^ 2 / finiteGreenProduct x y

def interiorEnergy (x : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y ∈ F, ∑ z ∈ F, adjacencyKernel y z *
    finiteGreenProduct x y * finiteGreenProduct x z *
    (f y / finiteGreenProduct x y - f z / finiteGreenProduct x z) ^ 2

theorem boundary_nonneg (x : FiniteVertices) (F : Finset FiniteVertices)
    (y : FiniteVertices) : 0 ≤ boundary x F y := by
  apply sub_nonneg.mpr
  apply adjacency_mono (finiteSource_inDomain F _) (product_inDomain x) _ y
  intro z
  unfold finiteSource
  split_ifs
  · exact le_rfl
  · exact (product_pos x z).le

theorem boundaryEnergy_nonneg (x : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) : 0 ≤ boundaryEnergy x F f :=
  Finset.sum_nonneg fun y _ => div_nonneg
    (mul_nonneg (boundary_nonneg x F y) (sq_nonneg (f y))) (product_pos x y).le

theorem interiorEnergy_nonneg (x : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) : 0 ≤ interiorEnergy x F f :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun z _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (adjacencyKernel_nonneg y z)
      (product_pos x y).le) (product_pos x z).le) (sq_nonneg _))

private theorem edge_square (x y z : FiniteVertices) (f : FiniteVertices → ℝ) :
    adjacencyKernel y z * finiteGreenProduct x y * finiteGreenProduct x z *
        (f y / finiteGreenProduct x y - f z / finiteGreenProduct x z) ^ 2 =
      f y ^ 2 / finiteGreenProduct x y * (adjacencyKernel y z * finiteGreenProduct x z) +
      f z ^ 2 / finiteGreenProduct x z * (adjacencyKernel z y * finiteGreenProduct x y) -
      2 * (f y * (adjacencyKernel y z * f z)) := by
  rw [adjacencyKernel_symm z y]
  field_simp [(product_pos x y).ne', (product_pos x z).ne']
  ring

/-- Symmetry turns the two square terms into the same weighted row sum. -/
theorem interiorEnergy_eq (x : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) :
    interiorEnergy x F f =
      (∑ y ∈ F, f y ^ 2 / finiteGreenProduct x y *
        adjacency (finiteSource F (finiteGreenProduct x)) y) -
      ∑ y ∈ F, f y * adjacency (finiteSource F f) y := by
  have hrow : (∑ y ∈ F, ∑ z ∈ F, f y ^ 2 / finiteGreenProduct x y *
      (adjacencyKernel y z * finiteGreenProduct x z)) =
      ∑ y ∈ F, f y ^ 2 / finiteGreenProduct x y *
        adjacency (finiteSource F (finiteGreenProduct x)) y := by
    simp_rw [← Finset.mul_sum, ← adjacency_finiteSource]
  have hcol : (∑ y ∈ F, ∑ z ∈ F, f z ^ 2 / finiteGreenProduct x z *
      (adjacencyKernel z y * finiteGreenProduct x y)) =
      ∑ y ∈ F, f y ^ 2 / finiteGreenProduct x y *
        adjacency (finiteSource F (finiteGreenProduct x)) y := by
    rw [Finset.sum_comm]
    exact hrow
  have hcross : (∑ y ∈ F, ∑ z ∈ F, 2 * (f y * (adjacencyKernel y z * f z))) =
      2 * ∑ y ∈ F, f y * adjacency (finiteSource F f) y := by
    simp_rw [← Finset.mul_sum, ← adjacency_finiteSource]
  unfold interiorEnergy
  simp_rw [edge_square, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hrow, hcol, hcross]
  ring

/-- Exact energy decomposition for the full weighted prime adjacency. -/
theorem energy_decomposition (x : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) :
    energy F f = (∑ y ∈ F, profile x y * f y ^ 2) +
      boundaryEnergy x F f + interiorEnergy x F f := by
  have hpoint (y : FiniteVertices) : edge * f y ^ 2 =
      profile x y * f y ^ 2 + boundary x F y * f y ^ 2 / finiteGreenProduct x y +
        f y ^ 2 / finiteGreenProduct x y *
          adjacency (finiteSource F (finiteGreenProduct x)) y := by
    unfold boundary
    apply (mul_right_cancel₀ (product_pos x y).ne')
    field_simp [(product_pos x y).ne']
    linear_combination f y ^ 2 * product_source x y
  have hsum := Finset.sum_congr (s₁ := F) rfl (fun y _ => hpoint y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [energy, interiorEnergy_eq]
  change edge * (∑ y ∈ F, f y ^ 2) - _ = _ +
    (∑ y ∈ F, boundary x F y * f y ^ 2 / finiteGreenProduct x y) + _
  linarith only [hsum]

/-- Source mass from places at which the whole configuration agrees with its centre. -/
def agreementMass (x : FiniteVertices) (F : Finset FiniteVertices) : ℝ :=
  ∑' p : Prime, if ∀ y ∈ F, x.1 p = y.1 p then massTerm p else 0

theorem agreementMass_summable (x : FiniteVertices) (F : Finset FiniteVertices) :
    Summable (fun p : Prime => if ∀ y ∈ F, x.1 p = y.1 p then massTerm p else 0) := by
  apply Summable.of_nonneg_of_le _ _ summable_massTerm
  · intro p
    split_ifs
    · exact (massTerm_pos p).le
    · exact le_rfl
  · intro p
    split_ifs
    · exact le_rfl
    · exact (massTerm_pos p).le

theorem agreementMass_le_profile (x : FiniteVertices) (F : Finset FiniteVertices)
    (y : FiniteVertices) (hy : y ∈ F) : agreementMass x F ≤ profile x y := by
  apply Summable.tsum_le_tsum _ (agreementMass_summable x F) (profile_summable x y)
  intro p
  by_cases hp : ∀ z ∈ F, x.1 p = z.1 p
  · rw [if_pos hp, if_pos (hp y hy)]
  · rw [if_neg hp]
    split_ifs
    · exact (massTerm_pos p).le
    · exact le_rfl

/-- A prime outside the finitely many varying coordinates contributes positive mass. -/
theorem agreementMass_pos (x : FiniteVertices) (F : Finset FiniteVertices) :
    0 < agreementMass x F := by
  let S := x.2.toFinset ∪ F.biUnion (fun y => y.2.toFinset)
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (S.sup (fun p => p.1) + 1)
  let p : Prime := ⟨q, hprime⟩
  have hp : p ∉ S := by
    intro hp
    have hle := Finset.le_sup (f := fun r : Prime => r.1) hp
    change q ≤ S.sup (fun r => r.1) at hle
    omega
  have hx : x.1 p = baseVertex p := by
    by_contra h
    exact hp (Finset.mem_union_left _ (x.2.mem_toFinset.mpr h))
  have hcommon : ∀ y ∈ F, x.1 p = y.1 p := by
    intro y hy
    rw [hx]
    symm
    by_contra h
    exact hp (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨y, hy, y.2.mem_toFinset.mpr h⟩))
  have hle := (agreementMass_summable x F).le_tsum p (fun r _ => by
    split_ifs
    · exact (massTerm_pos r).le
    · exact le_rfl)
  rw [if_pos hcommon] at hle
  exact (massTerm_pos p).trans_le hle

/-- The coercivity constant depends only on relative coordinate agreement. -/
theorem agreementMass_smul (a : FiniteAdelicGroup) (x : FiniteVertices)
    (F : Finset FiniteVertices) :
    agreementMass (a • x) (F.image (fun y => a • y)) = agreementMass x F := by
  have he (p : Prime) : (∀ y ∈ F.image (fun z => a • z), (a • x).1 p = y.1 p) ↔
      ∀ y ∈ F, x.1 p = y.1 p := by
    constructor
    · intro h y hy
      exact (MulAction.injective (a p))
        (h (a • y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
    · intro h z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact congrArg (fun v => a p • v) (h y hy)
  unfold agreementMass
  apply tsum_congr
  intro p
  by_cases h : ∀ y ∈ F, x.1 p = y.1 p
  · rw [if_pos h, if_pos ((he p).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((he p).mp h'))]

/-- Every finite configuration has an explicit, strictly positive energy gap. -/
theorem energy_coercive (x : FiniteVertices) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) :
    agreementMass x F * (∑ y ∈ F, f y ^ 2) ≤ energy F f := by
  calc
    agreementMass x F * (∑ y ∈ F, f y ^ 2) =
        ∑ y ∈ F, agreementMass x F * f y ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ y ∈ F, profile x y * f y ^ 2 :=
      Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_right
        (agreementMass_le_profile x F y hy) (sq_nonneg _)
    _ ≤ energy F f := by
      rw [energy_decomposition x F f]
      linarith only [boundaryEnergy_nonneg x F f, interiorEnergy_nonneg x F f]

theorem energy_pos_iff (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    0 < energy F f ↔ ∃ y ∈ F, f y ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    have hz : ∀ y ∈ F, f y = 0 := by
      intro y hy
      by_contra hne
      exact hn ⟨y, hy, hne⟩
    have he : energy F f = 0 := by
      unfold energy
      rw [Finset.sum_eq_zero (fun y hy => by rw [hz y hy]; ring),
        Finset.sum_eq_zero (fun y hy => by rw [hz y hy]; ring)]
      ring
    exact (ne_of_gt h) he
  · rintro ⟨y, hy, hne⟩
    have hs : 0 < ∑ z ∈ F, f z ^ 2 :=
      Finset.sum_pos' (fun z _ => sq_nonneg _) ⟨y, hy, sq_pos_of_ne_zero hne⟩
    exact (mul_pos (agreementMass_pos y F) hs).trans_le (energy_coercive y F f)

#print axioms finiteSource_inDomain
#print axioms energy_decomposition
#print axioms agreementMass_pos
#print axioms agreementMass_smul
#print axioms energy_coercive
#print axioms energy_pos_iff

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
