import GaloisForLFunctions.HyperbolicArakelovTheory.TheMinimalBranchOfTheAdelicGreenKernel

/-!
# A single-point Green kernel on finite products of prime trees

The product of the critical local kernels has a positive source on coordinate
hyperplanes. Its normalization bounds the occupation sum for the sum of the
actual adjacency operators. This constructs the least nonnegative single-point
Green kernel at the sum of the local tempered parameters, with no growth
condition on competing supersolutions.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.FiniteProductGreen
open FullAdelic AdelicAdjacency AdelicRadial AdelicGreen

abbrev Prime := {p : ℕ // p.Prime}
abbrev Vertices {ι : Type*} (p : ι → Prime) := ∀ i, LocalVertex (p i)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prime)

/-- Sum of the local tempered spectral parameters. -/
def edge : ℝ := ∑ i, 2 * Real.sqrt (p i).1

/-- Each step changes one actual prime vertex and retains all other coordinates. -/
def adjacency : Module.End ℝ (Vertices p → ℝ) where
  toFun f y := ∑ i, ∑ z ∈ neighbors (p i) (y i), f (Function.update y i z)
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- The critical positive iteration operator. Its row sum need not be one. -/
def step : Module.End ℝ (Vertices p → ℝ) := (edge p)⁻¹ • adjacency p

def pointMass (x y : Vertices p) : ℝ := if x = y then 1 else 0

def source (x : Vertices p) : Vertices p → ℝ := (edge p)⁻¹ • pointMass p x

/-- One weighted occupation term, using only the actual adjacency operator. -/
def occupationTerm (x : Vertices p) (n : ℕ) (y : Vertices p) : ℝ :=
  ((step p) ^ n) (source p x) y

def greenPartial (x : Vertices p) (N : ℕ) (y : Vertices p) : ℝ :=
  ∑ n ∈ Finset.range N, occupationTerm p x n y

/-- The minimal critical candidate is defined directly by its walk occupation series. -/
def green (x y : Vertices p) : ℝ := ∑' n, occupationTerm p x n y

/-- Product of genuine local Green kernels, used as a comparison function. -/
def productKernel (x y : Vertices p) : ℝ :=
  ∏ i, localGreen (p i) (1 / 2) (x i) (y i)

/-- Remaining factors after the indicated prime coordinate is removed. -/
def transverseProduct (i : ι) (x y : Vertices p) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, localGreen (p j) (1 / 2) (x j) (y j)

/-- Total source strength of the product kernel at its corner. -/
def cornerMass (x : Vertices p) : ℝ := ∑ i, transverseProduct p i x x

def barrier (x y : Vertices p) : ℝ := productKernel p x y / cornerMass p x

/-- Nonnegative supersolutions for the single full-product point source. -/
def supersolutions (x : Vertices p) : Set (Vertices p → ℝ) :=
  {u | (∀ y, 0 ≤ u y) ∧ ∀ y, pointMass p x y ≤ edge p * u y - adjacency p u y}

omit [DecidableEq ι] in
theorem productKernel_pos (x y : Vertices p) : 0 < productKernel p x y :=
  Finset.prod_pos fun i _ => localGreen_pos (p i) (by norm_num) _ _

theorem transverseProduct_pos (i : ι) (x y : Vertices p) :
    0 < transverseProduct p i x y :=
  Finset.prod_pos fun j _ => localGreen_pos (p j) (by norm_num) _ _

theorem productKernel_split (i : ι) (x y : Vertices p) :
    productKernel p x y = localGreen (p i) (1 / 2) (x i) (y i) * transverseProduct p i x y :=
  (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

private theorem productKernel_update (i : ι) (x y : Vertices p) (z : LocalVertex (p i)) :
    productKernel p x (Function.update y i z) =
      localGreen (p i) (1 / 2) (x i) z * transverseProduct p i x y := by
  rw [productKernel_split p i, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- The product kernel has coordinate-hyperplane sources, not just a point source. -/
theorem productKernel_source (x y : Vertices p) :
    edge p * productKernel p x y - adjacency p (productKernel p x) y =
      ∑ i, (if x i = y i then 1 else 0) * transverseProduct p i x y := by
  change (∑ i, 2 * Real.sqrt (p i).1) * productKernel p x y -
    (∑ i, ∑ z ∈ neighbors (p i) (y i), productKernel p x (Function.update y i z)) = _
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [productKernel_update p i]
  rw [← Finset.sum_mul, productKernel_split p i]
  rw [show 2 * Real.sqrt (p i).1 *
      (localGreen (p i) (1 / 2) (x i) (y i) * transverseProduct p i x y) -
      (∑ z ∈ neighbors (p i) (y i), localGreen (p i) (1 / 2) (x i) z) *
        transverseProduct p i x y =
      (2 * Real.sqrt (p i).1 * localGreen (p i) (1 / 2) (x i) (y i) -
        ∑ z ∈ neighbors (p i) (y i), localGreen (p i) (1 / 2) (x i) z) *
        transverseProduct p i x y by ring,
    localGreen_tempered_resolvent]

private theorem adjacency_div (f : Vertices p → ℝ) (c : ℝ) (y : Vertices p) :
    adjacency p (fun z => f z / c) y = adjacency p f y / c := by
  change (∑ i, ∑ z ∈ neighbors (p i) (y i), f (Function.update y i z) / c) = _
  simp only [← Finset.sum_div]
  rfl

section Nonempty
variable [Nonempty ι]

omit [DecidableEq ι] in
theorem edge_pos : 0 < edge p := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (by exact_mod_cast (p i).2.pos))

theorem cornerMass_pos (x : Vertices p) : 0 < cornerMass p x :=
  Finset.sum_pos (fun i _ => transverseProduct_pos p i x x) Finset.univ_nonempty

/-- The product source supplies an explicit supersolution for the single corner source. -/
theorem barrier_mem (x : Vertices p) : barrier p x ∈ supersolutions p x := by
  refine ⟨fun y => (div_pos (productKernel_pos p x y) (cornerMass_pos p x)).le, fun y => ?_⟩
  change pointMass p x y ≤ edge p * (productKernel p x y / cornerMass p x) -
    adjacency p (fun z => productKernel p x z / cornerMass p x) y
  rw [adjacency_div, ← mul_div_assoc, ← sub_div, productKernel_source]
  by_cases hxy : x = y
  · subst y
    simp only [pointMass, if_true, one_mul]
    change 1 ≤ cornerMass p x / cornerMass p x
    rw [div_self (cornerMass_pos p x).ne']
  · rw [pointMass, if_neg hxy]
    apply div_nonneg _ (cornerMass_pos p x).le
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by split_ifs <;> norm_num) (transverseProduct_pos p i x y).le

theorem step_mono : Monotone (step p) := by
  intro f g h y
  change (edge p)⁻¹ * (∑ i, ∑ z ∈ neighbors (p i) (y i), f (Function.update y i z)) ≤
    (edge p)⁻¹ * (∑ i, ∑ z ∈ neighbors (p i) (y i), g (Function.update y i z))
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun z _ => h _) (inv_nonneg.mpr (edge_pos p).le)

private theorem iter_mono (n : ℕ) : Monotone ((step p) ^ n) := by
  induction n with
  | zero => intro f g h; exact h
  | succ n ih =>
    intro f g h y
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    exact step_mono p (ih h) y

private theorem iter_nonneg (n : ℕ) {f : Vertices p → ℝ} (hf : ∀ y, 0 ≤ f y)
    (y : Vertices p) : 0 ≤ ((step p) ^ n) f y := by
  have h := iter_mono p n (show (0 : Vertices p → ℝ) ≤ f from hf) y
  simpa only [map_zero, Pi.zero_apply] using h

theorem occupationTerm_nonneg (x : Vertices p) (n : ℕ) (y : Vertices p) :
    0 ≤ occupationTerm p x n y := by
  apply iter_nonneg
  intro z
  change 0 ≤ (edge p)⁻¹ * pointMass p x z
  exact mul_nonneg (inv_nonneg.mpr (edge_pos p).le) (by unfold pointMass; split_ifs <;> norm_num)

omit [Nonempty ι] in
private theorem telescope (f : Vertices p → ℝ) (N : ℕ) (y : Vertices p) :
    (∑ n ∈ Finset.range N, ((step p) ^ n) (f - step p f) y) =
      f y - ((step p) ^ N) f y := by
  have ht (n : ℕ) : ((step p) ^ n) (f - step p f) y =
      ((step p) ^ n) f y - ((step p) ^ (n + 1)) f y := by
    rw [map_sub, Pi.sub_apply, pow_succ, Module.End.mul_apply]
  simp_rw [ht]
  rw [Finset.sum_range_sub']
  simp only [pow_zero, Module.End.one_apply]

/-- Finite walks lie below every nonnegative supersolution, without a boundary assumption. -/
theorem greenPartial_le (x : Vertices p) {u : Vertices p → ℝ}
    (hu : u ∈ supersolutions p x) (N : ℕ) (y : Vertices p) : greenPartial p x N y ≤ u y := by
  have hd : source p x ≤ u - step p u := by
    intro z
    have h := div_le_div_of_nonneg_right (hu.2 z) (edge_pos p).le
    rw [sub_div, mul_div_cancel_left₀ _ (edge_pos p).ne'] at h
    change (edge p)⁻¹ * pointMass p x z ≤ u z - (edge p)⁻¹ * adjacency p u z
    simpa only [div_eq_mul_inv, mul_comm] using h
  calc
    _ ≤ ∑ n ∈ Finset.range N, ((step p) ^ n) (u - step p u) y :=
      Finset.sum_le_sum fun n _ => iter_mono p n hd y
    _ = u y - ((step p) ^ N) u y := telescope p u N y
    _ ≤ u y := sub_le_self _ (iter_nonneg p N hu.1 y)

/-- Occupation converges at the sum of all local tempered edges. -/
theorem summable_occupation (x y : Vertices p) : Summable (fun n => occupationTerm p x n y) :=
  summable_of_sum_range_le (occupationTerm_nonneg p x · y)
    (fun N => greenPartial_le p x (barrier_mem p x) N y)

theorem green_nonneg (x y : Vertices p) : 0 ≤ green p x y :=
  tsum_nonneg (occupationTerm_nonneg p x · y)

/-- The global point source is bounded by the normalized product of the local Green kernels. -/
theorem green_le_product (x y : Vertices p) :
    green p x y ≤ productKernel p x y / cornerMass p x :=
  le_of_tendsto (summable_occupation p x y).hasSum.tendsto_sum_nat
    (Eventually.of_forall fun N => greenPartial_le p x (barrier_mem p x) N y)

omit [Nonempty ι] in
private theorem occupation_succ (x : Vertices p) (n : ℕ) (y : Vertices p) :
    occupationTerm p x (n + 1) y =
      (∑ i, ∑ z ∈ neighbors (p i) (y i), occupationTerm p x n (Function.update y i z)) / edge p := by
  rw [occupationTerm, pow_succ', Module.End.mul_apply]
  change (edge p)⁻¹ * _ = _
  rw [div_eq_mul_inv, mul_comm]
  rfl

/-- The occupation kernel solves the genuine single-point source equation on the whole product. -/
theorem green_source (x y : Vertices p) :
    edge p * green p x y - adjacency p (green p x) y = pointMass p x y := by
  have hs : HasSum (fun n =>
      (∑ i, ∑ z ∈ neighbors (p i) (y i), occupationTerm p x n (Function.update y i z)) / edge p)
      (adjacency p (green p x) y / edge p) := by
    apply HasSum.div_const
    apply hasSum_sum
    intro i _
    exact hasSum_sum fun z _ => (summable_occupation p x (Function.update y i z)).hasSum
  have hshift := (hasSum_nat_add_iff' (f := fun n => occupationTerm p x n y) 1).mpr
    (summable_occupation p x y).hasSum
  simp only [occupation_succ p] at hshift
  have he := hs.unique hshift
  simp only [Finset.sum_range_one, occupationTerm, pow_zero, Module.End.one_apply,
    source, Pi.smul_apply, smul_eq_mul] at he
  change adjacency p (green p x) y / edge p = green p x y - (edge p)⁻¹ * pointMass p x y at he
  have h := congrArg (fun t : ℝ => edge p * t) he
  rw [mul_div_cancel₀ _ (edge_pos p).ne', mul_sub, ← mul_assoc,
    mul_inv_cancel₀ (edge_pos p).ne', one_mul] at h
  linarith only [h]

/-- The global critical Green kernel is minimal among all nonnegative supersolutions. -/
theorem green_isLeast (x : Vertices p) : IsLeast (supersolutions p x) (green p x) := by
  refine ⟨⟨green_nonneg p x, fun y => (green_source p x y).symm.le⟩, ?_⟩
  intro u hu y
  exact le_of_tendsto (summable_occupation p x y).hasSum.tendsto_sum_nat
    (Eventually.of_forall fun N => greenPartial_le p x hu N y)

#print axioms productKernel_source
#print axioms summable_occupation
#print axioms green_source
#print axioms green_isLeast
#print axioms green_le_product

end Nonempty
end GaloisForLFunctions.HyperbolicArakelovTheory.FiniteProductGreen
