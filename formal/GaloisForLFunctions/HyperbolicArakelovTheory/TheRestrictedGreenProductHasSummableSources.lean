import GaloisForLFunctions.HyperbolicArakelovTheory.ThePrimeFibresRecoverArithmeticContact
import Mathlib.Analysis.PSeries

/-!
# Summable sources of the restricted critical Green product

Weight the actual prime adjacency operators by `p⁻²`. Their tempered
parameters are summable. The restricted product of normalized local Green
kernels has an exact, nonnegative global source, with positive mass at its
centre. Its normalization supplies a point-source barrier on all restricted
adelic vertices, without truncating the number of varying places.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicAdjacency AdelicGreen CoupledProductObstruction

abbrev Prime := {p : ℕ // p.Prime}

/-- Fixed arithmetic damping of the local adjacency operators. -/
def weight (p : Prime) : ℝ := 1 / (p.1 : ℝ) ^ 2

def localMass (p : Prime) : ℝ := ((p.1 : ℝ) - 1) / Real.sqrt p.1

def edgeTerm (p : Prime) : ℝ := weight p * (2 * Real.sqrt p.1)
def massTerm (p : Prime) : ℝ := weight p * localMass p

def edge : ℝ := ∑' p : Prime, edgeTerm p
def mass : ℝ := ∑' p : Prime, massTerm p

def localAdj (p : Prime) (f : FiniteVertices → ℝ) (y : FiniteVertices) : ℝ :=
  ∑ z ∈ neighbors p (y.1 p), f (replaceVertex p y z)

def placeTerm (p : Prime) (f : FiniteVertices → ℝ) (y : FiniteVertices) : ℝ :=
  weight p * localAdj p f y

/-- The sum over all finite places; convergence is recorded by `InDomain`. -/
def adjacency (f : FiniteVertices → ℝ) (y : FiniteVertices) : ℝ := ∑' p, placeTerm p f y

/-- Absolute convergence of the actual weighted adjacency sum at every vertex. -/
def InDomain (f : FiniteVertices → ℝ) : Prop := ∀ y, Summable (fun p => placeTerm p f y)

def profile (x y : FiniteVertices) : ℝ :=
  ∑' p : Prime, if x.1 p = y.1 p then massTerm p else 0

def pointMass (x y : FiniteVertices) : ℝ := if x = y then 1 else 0

def barrier (x y : FiniteVertices) : ℝ := finiteGreenProduct x y / mass

/-- Simultaneous finite adelic transport preserves the actual local neighbour sum. -/
theorem localAdj_smul (p : Prime) (a : FiniteAdelicGroup) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) : localAdj p f (a • y) = localAdj p (fun z => f (a • z)) y := by
  change (∑ z ∈ neighbors p (a p • y.1 p), f (replaceVertex p (a • y) z)) = _
  rw [neighbors_smul, Finset.sum_image (MulAction.injective (a p)).injOn]
  apply Finset.sum_congr rfl
  intro z _
  rw [← smul_replaceVertex]

theorem adjacency_smul (a : FiniteAdelicGroup) (f : FiniteVertices → ℝ) (y : FiniteVertices) :
    adjacency f (a • y) = adjacency (fun z => f (a • z)) y := by
  simp only [adjacency, placeTerm, localAdj_smul]

private theorem prime_pos (p : Prime) : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos

private theorem prime_one_lt (p : Prime) : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt

theorem weight_pos (p : Prime) : 0 < weight p := one_div_pos.mpr (sq_pos_of_pos (prime_pos p))

theorem localMass_pos (p : Prime) : 0 < localMass p :=
  div_pos (sub_pos.mpr (prime_one_lt p)) (Real.sqrt_pos.mpr (prime_pos p))

theorem product_pos (x y : FiniteVertices) : 0 < finiteGreenProduct x y := by
  rw [finiteGreenProduct, finprod_eq_prod _ (hasFiniteMulSupport_localFactor x y)]
  exact Finset.prod_pos fun p _ => localFactor_pos p _ _

theorem product_self (x : FiniteVertices) : finiteGreenProduct x x = 1 := by
  simp only [finiteGreenProduct, localFactor_self, finprod_one]

/-- Changing one coordinate changes exactly one factor of the restricted product. -/
theorem product_replace (p : Prime) (x y : FiniteVertices) (z : LocalVertex p) :
    finiteGreenProduct x (replaceVertex p y z) =
      finiteGreenProduct x y * localFactor p (x.1 p) z / localFactor p (x.1 p) (y.1 p) := by
  let hs := hasFiniteMulSupport_localFactor x y
  let S := insert p hs.toFinset
  have hp : p ∈ S := Finset.mem_insert_self _ _
  have hexpand (v : FiniteVertices) (hv : ∀ q, q ≠ p → v.1 q = y.1 q) :
      finiteGreenProduct x v = ∏ q ∈ S, localFactor q (x.1 q) (v.1 q) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro q hq
    by_cases h : q = p
    · subst q; exact hp
    · apply Finset.mem_insert_of_mem
      apply hs.mem_toFinset.mpr
      change localFactor q (x.1 q) (y.1 q) ≠ 1
      change localFactor q (x.1 q) (v.1 q) ≠ 1 at hq
      simpa only [hv q h] using hq
  have herase :
      (∏ q ∈ S.erase p, localFactor q (x.1 q) ((replaceVertex p y z).1 q)) =
        ∏ q ∈ S.erase p, localFactor q (x.1 q) (y.1 q) := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [replaceVertex_away p y z q (Finset.mem_erase.mp hq).1]
  rw [hexpand y (fun _ _ => rfl),
    hexpand (replaceVertex p y z) (replaceVertex_away p y z)]
  rw [← Finset.mul_prod_erase S _ hp, ← Finset.mul_prod_erase S _ hp,
    replaceVertex_at, herase]
  field_simp [(localFactor_pos p (x.1 p) (y.1 p)).ne']

/-- The normalized local product factor retains its explicit critical source. -/
theorem factor_source (p : Prime) (x y : LocalVertex p) :
    2 * Real.sqrt p.1 * localFactor p x y -
      (∑ z ∈ neighbors p y, localFactor p x z) = if x = y then localMass p else 0 := by
  have h := localGreen_tempered_resolvent p x y
  simp_rw [← PrimeFibres.normalized_localGreen]
  change 2 * Real.sqrt p.1 * (localMass p * localGreen p (1 / 2) x y) -
    (∑ z ∈ neighbors p y, localMass p * localGreen p (1 / 2) x z) = _
  rw [← Finset.mul_sum]
  by_cases he : x = y
  · rw [if_pos he] at h ⊢
    linear_combination localMass p * h
  · rw [if_neg he] at h ⊢
    linear_combination localMass p * h

/-- The restricted product has a coordinate source at every place where the vertices agree. -/
theorem localAdj_product (p : Prime) (x y : FiniteVertices) :
    localAdj p (finiteGreenProduct x) y =
      finiteGreenProduct x y *
        (2 * Real.sqrt p.1 - if x.1 p = y.1 p then localMass p else 0) := by
  have hs := factor_source p (x.1 p) (y.1 p)
  have he : localAdj p (finiteGreenProduct x) y =
      finiteGreenProduct x y * (∑ z ∈ neighbors p (y.1 p), localFactor p (x.1 p) z) /
        localFactor p (x.1 p) (y.1 p) := by
    simp only [localAdj, product_replace, ← Finset.sum_div, ← Finset.mul_sum]
  rw [he]
  by_cases hxy : x.1 p = y.1 p
  · rw [if_pos hxy, hxy, localFactor_self] at hs
    rw [if_pos hxy, hxy, localFactor_self, div_one]
    rw [show (∑ z ∈ neighbors p (y.1 p), localFactor p (y.1 p) z) =
      2 * Real.sqrt p.1 - localMass p by linarith only [hs]]
  · rw [if_neg hxy] at hs ⊢
    rw [sub_zero, show (∑ z ∈ neighbors p (y.1 p), localFactor p (x.1 p) z) =
      2 * Real.sqrt p.1 * localFactor p (x.1 p) (y.1 p) by linarith only [hs]]
    field_simp [(localFactor_pos p (x.1 p) (y.1 p)).ne']

theorem edgeTerm_pos (p : Prime) : 0 < edgeTerm p :=
  mul_pos (weight_pos p) (mul_pos (by norm_num) (Real.sqrt_pos.mpr (prime_pos p)))

theorem massTerm_pos (p : Prime) : 0 < massTerm p := mul_pos (weight_pos p) (localMass_pos p)

private theorem edgeTerm_rpow (p : Prime) : edgeTerm p = 2 * (p.1 : ℝ) ^ (-3 / 2 : ℝ) := by
  rw [show (-3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub (prime_pos p),
    Real.rpow_two, ← Real.sqrt_eq_rpow]
  unfold edgeTerm weight
  ring

theorem summable_edgeTerm : Summable edgeTerm := by
  have hs := ((Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).subtype
    Nat.Prime).mul_left 2
  rw [show edgeTerm = (fun p : Prime => 2 * (p.1 : ℝ) ^ (-3 / 2 : ℝ)) from
    funext edgeTerm_rpow]
  exact hs

theorem massTerm_le_edgeTerm (p : Prime) : massTerm p ≤ edgeTerm p := by
  apply mul_le_mul_of_nonneg_left _ (weight_pos p).le
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (prime_pos p))).mpr
  nlinarith only [prime_pos p, Real.sq_sqrt (prime_pos p).le]

theorem summable_massTerm : Summable massTerm :=
  Summable.of_nonneg_of_le (fun p => (massTerm_pos p).le) massTerm_le_edgeTerm summable_edgeTerm

theorem edge_pos : 0 < edge :=
  (edgeTerm_pos ⟨2, Nat.prime_two⟩).trans_le
    (summable_edgeTerm.le_tsum ⟨2, Nat.prime_two⟩ (fun p _ => (edgeTerm_pos p).le))

theorem mass_pos : 0 < mass :=
  (massTerm_pos ⟨2, Nat.prime_two⟩).trans_le
    (summable_massTerm.le_tsum ⟨2, Nat.prime_two⟩ (fun p _ => (massTerm_pos p).le))

theorem placeTerm_nonneg (p : Prime) {f : FiniteVertices → ℝ} (hf : ∀ y, 0 ≤ f y)
    (y : FiniteVertices) : 0 ≤ placeTerm p f y :=
  mul_nonneg (weight_pos p).le (Finset.sum_nonneg fun _ _ => hf _)

theorem placeTerm_mono (p : Prime) {f g : FiniteVertices → ℝ} (h : f ≤ g)
    (y : FiniteVertices) : placeTerm p f y ≤ placeTerm p g y :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ => h _) (weight_pos p).le

private theorem placeTerm_product_le (p : Prime) (x y : FiniteVertices) :
    placeTerm p (finiteGreenProduct x) y ≤ edgeTerm p * finiteGreenProduct x y := by
  rw [placeTerm, localAdj_product]
  have hn : 0 ≤ if x.1 p = y.1 p then localMass p else 0 := by
    split_ifs
    · exact (localMass_pos p).le
    · exact le_rfl
  have h := mul_le_mul_of_nonneg_left (sub_le_self (2 * Real.sqrt p.1) hn)
    (product_pos x y).le
  have hw := mul_le_mul_of_nonneg_left h (weight_pos p).le
  simpa only [edgeTerm, mul_left_comm, mul_assoc, mul_comm] using hw

theorem product_inDomain (x : FiniteVertices) : InDomain (finiteGreenProduct x) := by
  intro y
  exact Summable.of_nonneg_of_le (fun p => placeTerm_nonneg p (fun z => (product_pos x z).le) y)
    (fun p => placeTerm_product_le p x y) (summable_edgeTerm.mul_right _)

theorem profile_summable (x y : FiniteVertices) :
    Summable (fun p : Prime => if x.1 p = y.1 p then massTerm p else 0) := by
  apply Summable.of_nonneg_of_le _ _ summable_massTerm
  · intro p
    split_ifs
    · exact (massTerm_pos p).le
    · exact le_rfl
  · intro p
    split_ifs
    · exact le_rfl
    · exact (massTerm_pos p).le

theorem profile_nonneg (x y : FiniteVertices) : 0 ≤ profile x y := by
  apply tsum_nonneg
  intro p
  split_ifs
  · exact (massTerm_pos p).le
  · exact le_rfl

theorem profile_self (x : FiniteVertices) : profile x x = mass := by
  simp only [profile, mass, ite_true]

/-- Exact global source identity, with every countable place sum proved convergent. -/
theorem product_source (x y : FiniteVertices) :
    edge * finiteGreenProduct x y - adjacency (finiteGreenProduct x) y =
      finiteGreenProduct x y * profile x y := by
  have ht (p : Prime) : placeTerm p (finiteGreenProduct x) y =
      edgeTerm p * finiteGreenProduct x y -
        finiteGreenProduct x y * (if x.1 p = y.1 p then massTerm p else 0) := by
    rw [placeTerm, localAdj_product]
    unfold edgeTerm massTerm
    split_ifs <;> ring
  unfold adjacency
  simp_rw [ht]
  rw [(summable_edgeTerm.mul_right _).tsum_sub ((profile_summable x y).mul_left _),
    tsum_mul_right, tsum_mul_left]
  change edge * finiteGreenProduct x y -
    (edge * finiteGreenProduct x y - finiteGreenProduct x y * profile x y) = _
  ring

theorem placeTerm_div (p : Prime) (f : FiniteVertices → ℝ) (c : ℝ) (y : FiniteVertices) :
    placeTerm p (fun z => f z / c) y = placeTerm p f y / c := by
  simp only [placeTerm, localAdj, ← Finset.sum_div, mul_div_assoc]

theorem adjacency_div (f : FiniteVertices → ℝ) (c : ℝ) (y : FiniteVertices) :
    adjacency (fun z => f z / c) y = adjacency f y / c := by
  simp only [adjacency, placeTerm_div, tsum_div_const]

theorem barrier_nonneg (x y : FiniteVertices) : 0 ≤ barrier x y :=
  (div_pos (product_pos x y) mass_pos).le

theorem barrier_inDomain (x : FiniteVertices) : InDomain (barrier x) := by
  intro y
  change Summable (fun p => placeTerm p (fun z => finiteGreenProduct x z / mass) y)
  simp_rw [placeTerm_div]
  exact (product_inDomain x y).div_const mass

/-- The full restricted product supplies a unit point-source supersolution. -/
theorem barrier_source (x y : FiniteVertices) :
    pointMass x y ≤ edge * barrier x y - adjacency (barrier x) y := by
  change pointMass x y ≤ edge * (finiteGreenProduct x y / mass) -
    adjacency (fun z => finiteGreenProduct x z / mass) y
  rw [adjacency_div, ← mul_div_assoc, ← sub_div, product_source]
  by_cases h : x = y
  · subst y
    rw [pointMass, if_pos rfl, product_self, profile_self, one_mul, div_self mass_pos.ne']
  · rw [pointMass, if_neg h]
    exact div_nonneg (mul_nonneg (product_pos x y).le (profile_nonneg x y)) mass_pos.le

/-- Domination by the product barrier proves the operator domain, rather than assuming it. -/
theorem inDomain_of_le_barrier (x : FiniteVertices) {f : FiniteVertices → ℝ}
    (hf : ∀ y, 0 ≤ f y) (hbound : f ≤ barrier x) : InDomain f := by
  intro y
  exact Summable.of_nonneg_of_le (fun p => placeTerm_nonneg p hf y)
    (fun p => placeTerm_mono p hbound y) (barrier_inDomain x y)

theorem adjacency_nonneg {f : FiniteVertices → ℝ} (hf : ∀ y, 0 ≤ f y) (y : FiniteVertices) :
    0 ≤ adjacency f y := tsum_nonneg (fun p => placeTerm_nonneg p hf y)

theorem adjacency_mono {f g : FiniteVertices → ℝ} (hf : InDomain f) (hg : InDomain g)
    (h : f ≤ g) (y : FiniteVertices) : adjacency f y ≤ adjacency g y :=
  Summable.tsum_le_tsum (fun p => placeTerm_mono p h y) (hf y) (hg y)

#print axioms summable_edgeTerm
#print axioms product_source
#print axioms barrier_inDomain
#print axioms barrier_source

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
