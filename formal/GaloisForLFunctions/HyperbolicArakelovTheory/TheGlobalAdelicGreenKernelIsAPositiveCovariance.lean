import GaloisForLFunctions.HyperbolicArakelovTheory.TheDirichletGreenKernelsOfTheAdelicCarrier
import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedGreenKernelOnTheFullAdelicProduct

/-!
# Dirichlet exhaustion of the weighted adelic Green kernel

Finite inverse precision kernels increase to the actual global minimal
Green kernel. The product barrier passes their limit through all prime
adjacencies. This realizes reciprocity and covariance positivity on the
full restricted adelic vertex carrier.
-/

set_option autoImplicit false
noncomputable section
open Filter Matrix
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicAdjacency CoupledProductObstruction

/-- The actual global unit-source solution bounds every finite Dirichlet kernel. -/
theorem dirichletGreen_le_green (F : Finset FiniteVertices) (x y : FiniteVertices) :
    dirichletGreen F x y ≤ green x y := by
  by_cases hy : y ∈ F
  · apply precision_comparison F (dirichletGreen F x) (green x) _ y hy
    intro z hz
    rw [dirichletGreen_source F x z hz]
    have hm := adjacency_mono (finiteSource_inDomain F (green x)) (green_inDomain x)
      (show finiteSource F (green x) ≤ green x from fun w => by
        unfold finiteSource
        split_ifs
        · exact le_rfl
        · exact green_nonneg x w) z
    have hg := green_source x z
    unfold precision
    linarith only [hm, hg]
  · rw [dirichletGreen_outside F x y hy]
    exact green_nonneg x y

private def dirichletLimit (x y : FiniteVertices) : ℝ :=
  ⨆ F : Finset FiniteVertices, dirichletGreen F x y

private theorem dirichlet_bddAbove (x y : FiniteVertices) :
    BddAbove (Set.range (fun F : Finset FiniteVertices => dirichletGreen F x y)) := by
  refine ⟨barrier x y, ?_⟩
  rintro _ ⟨F, rfl⟩
  exact dirichletGreen_le_barrier F x y

private theorem tendsto_dirichletLimit (x y : FiniteVertices) :
    Tendsto (fun F : Finset FiniteVertices => dirichletGreen F x y) atTop
      (𝓝 (dirichletLimit x y)) :=
  tendsto_atTop_ciSup (dirichletGreen_mono x y) (dirichlet_bddAbove x y)

private theorem dirichletLimit_nonneg (x y : FiniteVertices) : 0 ≤ dirichletLimit x y :=
  (dirichletGreen_nonneg ∅ x y).trans (le_ciSup (dirichlet_bddAbove x y) ∅)

private theorem dirichletLimit_le_barrier (x : FiniteVertices) : dirichletLimit x ≤ barrier x :=
  fun y => ciSup_le (fun F => dirichletGreen_le_barrier F x y)

private theorem dirichletLimit_inDomain (x : FiniteVertices) : InDomain (dirichletLimit x) :=
  inDomain_of_le_barrier x (dirichletLimit_nonneg x) (dirichletLimit_le_barrier x)

private theorem tendsto_adjacency_dirichlet (x y : FiniteVertices) :
    Tendsto (fun F : Finset FiniteVertices => adjacency (dirichletGreen F x) y) atTop
      (𝓝 (adjacency (dirichletLimit x) y)) := by
  apply tendsto_tsum_of_dominated_convergence (barrier_inDomain x y)
  · intro p
    exact (tendsto_finsetSum (neighbors p (y.1 p))
      (fun z _ => tendsto_dirichletLimit x (replaceVertex p y z))).const_mul (weight p)
  · exact Eventually.of_forall fun F p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (placeTerm_nonneg p (dirichletGreen_nonneg F x) y)]
      exact placeTerm_mono p (dirichletGreen_le_barrier F x) y

private theorem dirichletLimit_source (x y : FiniteVertices) :
    edge * dirichletLimit x y - adjacency (dirichletLimit x) y = pointMass x y := by
  have he : (fun F : Finset FiniteVertices =>
      edge * dirichletGreen F x y - adjacency (dirichletGreen F x) y) =ᶠ[atTop]
      (fun _ => pointMass x y) := by
    apply eventually_atTop.mpr
    refine ⟨{y}, fun F hF => ?_⟩
    have hy : y ∈ F := hF (Finset.mem_singleton_self y)
    simpa only [precision, finiteSource_dirichletGreen] using dirichletGreen_source F x y hy
  exact tendsto_nhds_unique
    (((tendsto_dirichletLimit x y).const_mul edge).sub (tendsto_adjacency_dirichlet x y))
    (tendsto_const_nhds.congr' he.symm)

private theorem dirichletLimit_eq_green (x : FiniteVertices) : dirichletLimit x = green x := by
  apply le_antisymm
  · intro y
    exact ciSup_le (fun F => dirichletGreen_le_green F x y)
  · apply (green_isLeast x).2
    exact ⟨dirichletLimit_nonneg x, dirichletLimit_inDomain x,
      fun y => (dirichletLimit_source x y).symm.le⟩

/-- Finite Dirichlet inverses recover the previously constructed all-prime Green kernel. -/
theorem green_eq_iSup_dirichlet (x y : FiniteVertices) :
    green x y = ⨆ F : Finset FiniteVertices, dirichletGreen F x y := by
  exact (congrFun (dirichletLimit_eq_green x) y).symm

theorem tendsto_dirichletGreen (x y : FiniteVertices) :
    Tendsto (fun F : Finset FiniteVertices => dirichletGreen F x y) atTop (𝓝 (green x y)) := by
  simpa only [dirichletLimit_eq_green] using tendsto_dirichletLimit x y

/-- Reciprocity is inherited from finite symmetric inverse precision matrices. -/
theorem green_symm (x y : FiniteVertices) : green x y = green y x := by
  simp only [green_eq_iSup_dirichlet, dirichletGreen_symm _ x y]

/-- Potential of a finite real charge under the actual global Green kernel. -/
def greenPotential (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) : ℝ := ∑ x ∈ F, f x * green x y

def greenEnergy (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) : ℝ :=
  ∑ y ∈ F, f y * greenPotential F f y

/-- Nonnegative finite inverse energies pass to the global covariance limit. -/
theorem greenEnergy_nonneg (S : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    0 ≤ greenEnergy S f := by
  have ht : Tendsto (fun F : Finset FiniteVertices =>
      ∑ y ∈ S, f y * (∑ x ∈ S, f x * dirichletGreen F x y)) atTop
      (𝓝 (greenEnergy S f)) :=
    tendsto_finsetSum S (fun y _ =>
      (tendsto_finsetSum S (fun x _ => (tendsto_dirichletGreen x y).const_mul (f x))).const_mul (f y))
  apply ge_of_tendsto ht
  exact eventually_atTop.mpr ⟨S, fun F hSF => dirichletGreen_quadratic_nonneg S F hSF f⟩

private theorem greenPotential_extension (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f : FiniteVertices → ℝ) (y : FiniteVertices) :
    greenPotential F (finiteSource S f) y = greenPotential S f y :=
  sum_finiteSource_mul S F hSF f (fun x => green x y)

private theorem greenEnergy_extension (S F : Finset FiniteVertices) (hSF : S ⊆ F)
    (f : FiniteVertices → ℝ) : greenEnergy F (finiteSource S f) = greenEnergy S f := by
  simp only [greenEnergy, greenPotential_extension S F hSF]
  exact sum_finiteSource_mul S F hSF f (greenPotential S f)

private theorem sum_pointMass_mul (F : Finset FiniteVertices) (x : FiniteVertices)
    (f : FiniteVertices → ℝ) :
    (∑ y ∈ F, pointMass x y * f y) = finiteSource F f x := by
  simp [pointMass, finiteSource]

private theorem greenPotential_perturb (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (x : FiniteVertices) (hx : x ∈ F) (t : ℝ) (y : FiniteVertices) :
    greenPotential F (fun z => f z + t * pointMass x z) y =
      greenPotential F f y + t * green x y := by
  simp only [greenPotential, add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum, sum_pointMass_mul, finiteSource, if_pos hx]

private theorem greenEnergy_perturb (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (x : FiniteVertices) (hx : x ∈ F) (t : ℝ) :
    greenEnergy F (fun z => f z + t * pointMass x z) =
      greenEnergy F f + 2 * t * greenPotential F f x + t ^ 2 * green x x := by
  have hp (y : FiniteVertices) :
      (f y + t * pointMass x y) * (greenPotential F f y + t * green x y) =
      f y * greenPotential F f y + t * (f y * green y x) +
        t * (pointMass x y * greenPotential F f y) +
        t ^ 2 * (pointMass x y * green x y) := by
    rw [green_symm x y]
    ring
  simp_rw [greenEnergy, greenPotential_perturb F f x hx t, hp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_pointMass_mul,
    finiteSource, if_pos hx]
  change (∑ y ∈ F, f y * greenPotential F f y) + t * greenPotential F f x +
    t * greenPotential F f x + t ^ 2 * green x x = _
  ring

/-- A zero-energy charge has zero potential at every adelic vertex. -/
theorem greenPotential_eq_zero_of_energy_zero (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) (hf : greenEnergy F f = 0) (y : FiniteVertices) :
    greenPotential F f y = 0 := by
  let E := insert y F
  let g := finiteSource F f
  have hFE : F ⊆ E := Finset.subset_insert _ _
  have hE : greenEnergy E g = 0 := (greenEnergy_extension F E hFE f).trans hf
  have hp : greenPotential E g y = greenPotential F f y := greenPotential_extension F E hFE f y
  have hpos := greenEnergy_nonneg E
    (fun z => g z + (-greenPotential F f y / green y y) * pointMass y z)
  rw [greenEnergy_perturb E g y (Finset.mem_insert_self _ _), hE, hp, zero_add] at hpos
  have he : 2 * (-greenPotential F f y / green y y) * greenPotential F f y +
      (-greenPotential F f y / green y y) ^ 2 * green y y =
        -(greenPotential F f y) ^ 2 / green y y := by
    field_simp [(green_self_pos y).ne']
    ring
  rw [he] at hpos
  have hs : 0 ≤ -(greenPotential F f y) ^ 2 := by
    have hm := mul_nonneg hpos (green_self_pos y).le
    field_simp [(green_self_pos y).ne'] at hm
    exact hm
  nlinarith only [hs, sq_nonneg (greenPotential F f y)]

private theorem placeTerm_greenPotential (p : Prime) (F : Finset FiniteVertices)
    (f : FiniteVertices → ℝ) (y : FiniteVertices) :
    placeTerm p (greenPotential F f) y = ∑ x ∈ F, f x * placeTerm p (green x) y := by
  simp only [placeTerm, localAdj, greenPotential, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem greenPotential_hasSum (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) :
    HasSum (fun p => placeTerm p (greenPotential F f) y)
      (∑ x ∈ F, f x * adjacency (green x) y) := by
  simp_rw [placeTerm_greenPotential]
  exact hasSum_sum (fun x _ => (green_inDomain x y).hasSum.mul_left (f x))

theorem greenPotential_inDomain (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    InDomain (greenPotential F f) := fun y => (greenPotential_hasSum F f y).summable

/-- Finite signed Green potentials retain their exact original charge as source. -/
theorem greenPotential_source (F : Finset FiniteVertices) (f : FiniteVertices → ℝ)
    (y : FiniteVertices) :
    edge * greenPotential F f y - adjacency (greenPotential F f) y = finiteSource F f y := by
  rw [show adjacency (greenPotential F f) y = ∑ x ∈ F, f x * adjacency (green x) y from
    (greenPotential_hasSum F f y).tsum_eq]
  rw [greenPotential, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ x ∈ F, f x * (edge * green x y - adjacency (green x) y) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x ∈ F, pointMass y x * f x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [green_source]
      simp only [pointMass, eq_comm, mul_comm]
    _ = _ := sum_pointMass_mul F y f

/-- The unit-source law rules out a nonzero finite charge in the covariance radical. -/
theorem greenEnergy_pos_iff (F : Finset FiniteVertices) (f : FiniteVertices → ℝ) :
    0 < greenEnergy F f ↔ ∃ y ∈ F, f y ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    have hz : ∀ y ∈ F, f y = 0 := by
      intro y hy
      by_contra hne
      exact hn ⟨y, hy, hne⟩
    have he : greenEnergy F f = 0 := Finset.sum_eq_zero
      (fun y hy => by rw [hz y hy, zero_mul])
    exact (ne_of_gt h) he
  · rintro ⟨y, hy, hne⟩
    have hnn := greenEnergy_nonneg F f
    apply lt_of_le_of_ne hnn
    intro hz
    have he : greenPotential F f = 0 :=
      funext (greenPotential_eq_zero_of_energy_zero F f hz.symm)
    have hs := greenPotential_source F f y
    rw [he] at hs
    simp only [Pi.zero_apply, adjacency, placeTerm, localAdj, Finset.sum_const_zero,
      mul_zero, tsum_zero, sub_self, finiteSource, if_pos hy] at hs
    exact hne hs.symm

#print axioms green_eq_iSup_dirichlet
#print axioms green_symm
#print axioms greenEnergy_nonneg
#print axioms greenPotential_source
#print axioms greenEnergy_pos_iff

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
