import GaloisForLFunctions.HyperbolicArakelovTheory.TheCriticalGreenKernelOnFiniteAdelicProducts

/-!
# Uniform collapse of the unweighted adelic Green kernels

The single-point critical Green kernel on a finite product of prime trees
is bounded by the diagonal of each included local kernel, hence by `2/√p`
for every included prime. Along the directed finite place sets the kernels
therefore converge uniformly to zero, even when both vertices vary.
A nonzero infinite-place diagonal cannot be obtained by this unweighted limit.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.FiniteProductGreen
open FullAdelic AdelicRadial AdelicGreen

private theorem localGreen_le_diagonal (p : Prime) (x y : LocalVertex p) :
    localGreen p (1 / 2) x y ≤ localGreen p (1 / 2) x x := by
  have hs : Real.sqrt (localRatio p x y) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (localRatio_le_one p x y)
  have hdiag := (localGreen_pos p (by norm_num : (0 : ℝ) < 1 / 2) x x).le
  rw [localGreen_self] at hdiag ⊢
  rw [localGreen, ← Real.sqrt_eq_rpow]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hdiag

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (p : ι → Prime)

/-- Every finite-stage diagonal retains at least its time-zero occupation mass. -/
theorem one_div_edge_le_green_self (x : Vertices p) : 1 / edge p ≤ green p x x := by
  have hs := green_source p x x
  rw [pointMass, if_pos rfl] at hs
  have ha : 0 ≤ adjacency p (green p x) x :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun z _ => green_nonneg p x _
  apply (div_le_iff₀ (edge_pos p)).mpr
  nlinarith only [hs, ha]

/-- Every included local diagonal bounds the entire product Green kernel. -/
theorem green_le_local_diagonal (i : ι) (x y : Vertices p) :
    green p x y ≤ localGreen (p i) (1 / 2) (x i) (x i) := by
  have hprod : productKernel p x y ≤ productKernel p x x :=
    Finset.prod_le_prod (fun j _ => (localGreen_pos (p j) (by norm_num) _ _).le)
      (fun j _ => localGreen_le_diagonal (p j) _ _)
  have hmass : transverseProduct p i x x ≤ cornerMass p x :=
    Finset.single_le_sum (fun j _ => (transverseProduct_pos p j x x).le) (Finset.mem_univ i)
  apply (green_le_product p x y).trans
  apply (div_le_iff₀ (cornerMass_pos p x)).mpr
  calc
    _ ≤ productKernel p x x := hprod
    _ = localGreen (p i) (1 / 2) (x i) (x i) * transverseProduct p i x x :=
      productKernel_split p i x x
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (localGreen_pos (p i) (by norm_num) _ _).le

/-- A single large prime forces smallness independently of every other place and both vertices. -/
theorem green_le_two_div_sqrt (i : ι) (x y : Vertices p) :
    green p x y ≤ 2 / Real.sqrt (p i).1 := by
  have hp2 : (2 : ℝ) ≤ (p i).1 := by exact_mod_cast (p i).2.two_le
  have hp0 : (0 : ℝ) < (p i).1 := by linarith only [hp2]
  have hs := Real.sqrt_pos.mpr hp0
  have hd : 0 < (p i).1 - (1 : ℝ) := by linarith only [hp2]
  apply (green_le_local_diagonal p i x y).trans
  rw [localGreen_tempered_self, div_le_div_iff₀ hd hs]
  nlinarith only [hp2, Real.sq_sqrt hp0.le]

/-- Restriction of full finite adelic vertices to a finite place set. -/
def cutoffKernel (S : Finset Prime) (x y : FiniteVertices) : ℝ :=
  green (fun p : S => p.1) (fun p => x.1 p.1) (fun p => y.1 p.1)

/-- The directed finite-place kernels collapse uniformly, with both vertices quantified after the cutoff. -/
theorem cutoffKernel_uniform_zero {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : Finset Prime in atTop, ∀ x y : FiniteVertices, |cutoffKernel S x y| < ε := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => 2 / Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  obtain ⟨q, hNq, hq⟩ := Nat.exists_infinite_primes N
  let Q : Prime := ⟨q, hq⟩
  filter_upwards [eventually_ge_atTop ({Q} : Finset Prime)] with S hS x y
  have hmem : Q ∈ S := hS (Finset.mem_singleton_self Q)
  letI : Nonempty S := ⟨⟨Q, hmem⟩⟩
  change |green (fun p : S => p.1) (fun p => x.1 p.1) (fun p => y.1 p.1)| < ε
  rw [abs_of_nonneg (green_nonneg (fun p : S => p.1) _ _)]
  exact (green_le_two_div_sqrt (fun p : S => p.1) ⟨Q, hmem⟩ _ _).trans_lt (hN q hNq)

/-- No nonzero pointwise Green kernel remains under unweighted exhaustion of the finite places. -/
theorem tendsto_cutoffKernel_zero (x y : FiniteVertices) :
    Tendsto (fun S : Finset Prime => cutoffKernel S x y) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cutoffKernel_uniform_zero hε] with S hS
  simpa only [Real.dist_eq, sub_zero] using hS x y

#print axioms green_le_local_diagonal
#print axioms one_div_edge_le_green_self
#print axioms green_le_two_div_sqrt
#print axioms cutoffKernel_uniform_zero
#print axioms tendsto_cutoffKernel_zero

end GaloisForLFunctions.HyperbolicArakelovTheory.FiniteProductGreen
