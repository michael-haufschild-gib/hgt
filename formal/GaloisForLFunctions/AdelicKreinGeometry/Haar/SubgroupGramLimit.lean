import GaloisForLFunctions.AdelicKreinGeometry.Haar.SubgroupMovingBounds
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SubgroupNormControl
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PrimePowerGrids
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ConstantMatrixInertia
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# Infinite index for proper subgroup successors with continuous dilations

A finite prime height gives geometric bounds on fixed diagonal norms and moving
off-diagonal correlations along prime-power grids. Continuity of the dilation
reading makes the fixed Gram matrices converge to `J - I` in every dimension.
-/

open Complex Finset Filter Topology Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

private def primeGridError (p h N : ℕ) : ℝ :=
  (p : ℝ) ^ h * ((p : ℝ) ^ (N + 1))⁻¹

private theorem tendsto_primeGridError {p : ℕ} (hp : p.Prime) (h : ℕ) :
    Tendsto (primeGridError p h) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (p : ℝ) ^ h * ((p : ℝ) ^ (N + 1))⁻¹) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_primeGridReciprocal hp).const_mul ((p : ℝ) ^ h)

private theorem subgroupOrder_primeGrid_bound {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {p h : ℕ} (hp : p.Prime)
    (hbound : ∀ q : ℚ, q ∈ H → padicNorm p q ≤ (p : ℚ) ^ h)
    (N : ℕ) {q : ℚ} (hq : q ≠ 0)
    (hlarge : (p : ℚ) ^ (N + 1) ≤ padicNorm p q) :
    (rationalSubgroupOrder H q : ℝ)⁻¹ ≤ primeGridError p h N := by
  have hb := reciprocal_subgroupOrder_le_prime_power H h1 hp hbound hq hlarge
  change (rationalSubgroupOrder H q : ℝ)⁻¹ ≤ (p : ℝ) ^ h * ((p : ℝ) ^ (N + 1))⁻¹
  have hR := (Rat.cast_le (K := ℝ)).mpr hb
  simpa only [Rat.cast_inv, Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow] using hR

/-- Fixed diagonal norms tend to zero on the prime-power grid. -/
theorem tendsto_subgroup_primeGrid_projection_pairing {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {p h : ℕ} (hp : p.Prime)
    (hbound : ∀ q : ℚ, q ∈ H → padicNorm p q ≤ (p : ℚ) ^ h)
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hs : HasSubgroupSuccessor H k) (hperiod : ∀ g, k (g * translation 1) = k g)
    (n : ℕ) (i : Fin n) :
    Tendsto (fun N => kernelColumnPairing k
      (translationFixedProjection k hperiod (primeGridStep p N n)
        (kernelColumnPoint k (dilation (primeGridUnit hp N i))))
      (translationFixedProjection k hperiod (primeGridStep p N n)
        (kernelColumnPoint k (dilation (primeGridUnit hp N i))))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_primeGridError hp h).eventually (gt_mem_nhds hε)] with N hN
  have hq : primeGridStep p N n / (primeGridUnit hp N i : ℚ) ≠ 0 := by
    apply div_ne_zero _ (primeGridUnit hp N i).ne_zero
    exact inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))
  have hb := subgroupOrder_primeGrid_bound h1 hp hbound N hq
    (primeGridStep_div_norm_lower hp N n i)
  rw [dist_zero_right, subgroup_successor_projection_pairing h1 hk hi hs hperiod,
    affSlope_dilation, norm_inv, Complex.norm_natCast]
  exact hb.trans_lt hN

/-- Moving correlations between distinct grid columns tend to zero. -/
theorem tendsto_subgroup_primeGrid_moving_pairing {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {p h : ℕ} (hp : p.Prime)
    (hbound : ∀ q : ℚ, q ∈ H → padicNorm p q ≤ (p : ℚ) ^ h)
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hs : HasSubgroupSuccessor H k) (hperiod : ∀ g, k (g * translation 1) = k g)
    (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    Tendsto (fun N => kernelColumnPairing k
      (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N i))
      (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N j)))
      atTop (𝓝 0) := by
  have hforward (N : ℕ) (i j : Fin n) (hlt : i.val < j.val) :
      normSq (kernelColumnPairing k
        (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N i))
        (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N j))) ≤
        primeGridError p h N := by
    obtain ⟨m, hm⟩ := primeGridUnit_eq_nat_mul_step hp N n j
    have hmove := normSq_movingDilationColumn_pairing_le_inv_subgroupOrder h1 hk hi hs hperiod
      (primeGridStep p N n) (primeGridUnit hp N i) (primeGridUnit hp N j) hm
    exact hmove.trans (subgroupOrder_primeGrid_bound h1 hp hbound N
      (div_ne_zero (primeGridUnit hp N j).ne_zero (primeGridUnit hp N i).ne_zero)
      (primeGridRatio_norm_lower hp N hlt))
  have hpoint (N : ℕ) : normSq (kernelColumnPairing k
      (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N i))
      (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N j))) ≤
        primeGridError p h N := by
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hforward N i j hlt
    · have hb := hforward N j i hgt
      rw [kernelColumnPairing_conj_symm hk, Complex.normSq_eq_norm_sq,
        ← Complex.star_def, norm_star, ← Complex.normSq_eq_norm_sq]
      exact hb
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_primeGridError hp h).eventually (gt_mem_nhds (sq_pos_of_pos hε))]
    with N hN
  have hb := hpoint N
  rw [Complex.normSq_eq_norm_sq] at hb
  rw [dist_zero_right]
  nlinarith only [hb, hN, hε, norm_nonneg (kernelColumnPairing k
    (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N i))
    (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N j)))]

/-- The fixed-projection Gram limit has zero diagonal and unit off-diagonal. -/
theorem tendsto_subgroup_primeGrid_projected_gram {H : AddSubgroup ℚ}
    (h1 : (1 : ℚ) ∈ H) {p h : ℕ} (hp : p.Prime)
    (hbound : ∀ q : ℚ, q ∈ H → padicNorm p q ≤ (p : ℚ) ^ h)
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hs : HasSubgroupSuccessor H k) (hperiod : ∀ g, k (g * translation 1) = k g)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ))
    (n : ℕ) (i j : Fin n) :
    Tendsto (fun N => kernelColumnGram k (fun a : Fin n =>
      translationFixedProjection k hperiod (primeGridStep p N n)
        (kernelColumnPoint k (dilation (primeGridUnit hp N a)))) i j)
      atTop (𝓝 ((Matrix.of (fun _ _ : Fin n => (1 : ℂ)) - 1) i j)) := by
  have hf1 : f 1 = 1 := by
    have he := hdil 1 (by norm_num)
    simpa only [map_one, hasSubgroupSuccessor_one hs, Units.val_one, Rat.cast_one] using he.symm
  by_cases hij : i = j
  · subst j
    simpa only [kernelColumnGram, Matrix.sub_apply, Matrix.of_apply,
      Matrix.one_apply_eq, sub_self] using
      tendsto_subgroup_primeGrid_projection_pairing h1 hp hbound hk hi hs hperiod n i
  · have hz := tendsto_subgroup_primeGrid_moving_pairing h1 hp hbound hk hi hs hperiod n hij
    have hpos (N : ℕ) :
        (0 : ℚ) < (((primeGridUnit hp N i)⁻¹ * primeGridUnit hp N j : ℚˣ) : ℚ) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos (inv_pos.mpr (primeGridUnit_pos hp N i)) (primeGridUnit_pos hp N j)
    have hratio : Tendsto (fun N =>
        ((((primeGridUnit hp N i)⁻¹ * primeGridUnit hp N j : ℚˣ) : ℚ) : ℝ))
        atTop (𝓝 1) := by
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val, Rat.cast_mul, Rat.cast_inv,
        inv_one, one_mul] using
        ((tendsto_primeGridUnit hp i).inv₀ one_ne_zero).mul (tendsto_primeGridUnit hp j)
    have hfull := hf.tendsto.comp hratio
    have hentry (N : ℕ) : kernelColumnGram k (fun a : Fin n =>
        translationFixedProjection k hperiod (primeGridStep p N n)
          (kernelColumnPoint k (dilation (primeGridUnit hp N a)))) i j =
        f (((primeGridUnit hp N i)⁻¹ * primeGridUnit hp N j : ℚˣ) : ℚ) -
          kernelColumnPairing k
            (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N i))
            (movingDilationColumn k hperiod (primeGridStep p N n) (primeGridUnit hp N j)) := by
      have hspl := kernelColumnPairing_projection_decomposition hk (translation (primeGridStep p N n))
        (kernel_translation_locally_periodic hperiod (primeGridStep p N n))
        (kernelColumnPoint k (dilation (primeGridUnit hp N i)))
        (kernelColumnPoint k (dilation (primeGridUnit hp N j)))
      have hfullpair : kernelColumnPairing k
          (kernelColumnPoint k (dilation (primeGridUnit hp N i)))
          (kernelColumnPoint k (dilation (primeGridUnit hp N j))) =
          f (((primeGridUnit hp N i)⁻¹ * primeGridUnit hp N j : ℚˣ) : ℚ) := by
        rw [kernelColumnPairing_point_left hk]
        change k ((dilation (primeGridUnit hp N i))⁻¹ * dilation (primeGridUnit hp N j)) = _
        rw [← map_inv, ← map_mul]
        exact hdil _ (hpos N)
      rw [hfullpair] at hspl
      have he := eq_sub_of_add_eq hspl.symm
      simpa only [kernelColumnGram, translationFixedProjection, movingDilationColumn_eq_sub] using he
    have hlim := (hfull.sub hz).congr' (Eventually.of_forall fun N => (hentry N).symm)
    simpa only [hf1, sub_zero, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply_ne hij] using hlim

/-- A proper successor subgroup containing one forces infinite index at continuous dilations. -/
theorem negIndex_eq_top_of_integer_invariant_subgroup_continuous_dilation
    {H : AddSubgroup ℚ} (h1 : (1 : ℚ) ∈ H) (hproper : H ≠ ⊤)
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) (hs : HasSubgroupSuccessor H k)
    (hperiod : ∀ g, k (g * translation 1) = k g)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ)) : negIndex k = ⊤ := by
  obtain ⟨p, h, hp, hbound⟩ := exists_padicNorm_bound_on_rational_subgroup H h1 hproper
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    let A : Matrix (Fin (r + 2)) (Fin (r + 2)) ℂ := Matrix.of (fun _ _ => 1) - 1
    have hA : A.IsHermitian := by
      ext i j
      change conj ((1 : ℂ) - (if j = i then 1 else 0)) =
        (1 : ℂ) - (if i = j then 1 else 0)
      by_cases hij : i = j
      · simp only [hij, ite_true, sub_self, map_zero]
      · simp only [hij, Ne.symm hij, ite_false, sub_zero, map_one]
    have hc := tendsto_subgroup_primeGrid_projected_gram h1 hp hbound hk hi hs hperiod hf hdil (r + 2)
    obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hA hc).exists
    have hlow := constant_sub_one_index_lower (1 : ℂ) (r + 1)
    have hu := hermNegIndex_kernelColumnGram_le hk hi (fun a : Fin (r + 2) =>
      translationFixedProjection k hperiod (primeGridStep p N (r + 2))
        (kernelColumnPoint k (dilation (primeGridUnit hp N a))))
    have he : r + 1 ≤ r := hlow.trans (hN.trans hu)
    omega
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

#print axioms tendsto_subgroup_primeGrid_projected_gram
#print axioms negIndex_eq_top_of_integer_invariant_subgroup_continuous_dilation
end GaloisForLFunctions.AdelicKreinGeometry
