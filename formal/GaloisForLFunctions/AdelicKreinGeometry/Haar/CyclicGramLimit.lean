import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicHecke
import GaloisForLFunctions.BiarithmeticGeometry.Affine.NearIdentityGrids
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ConstantMatrixInertia
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# Infinite index from cyclic Haar Gram limits

For an integer-invariant Haar kernel, continuity of the dilation reading makes
fixed-projection Grams converge to `J − I`. Their arbitrarily large negative
index contradicts every finite bound on the kernel's column Grams.
-/

open Complex Finset Filter Topology Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The fixed part of each near-identity grid column has norm tending to zero. -/
theorem tendsto_nearIdentity_projection_pairing {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (i : ℕ) :
    Tendsto (fun N => kernelColumnPairing k
      (translationFixedProjection k hp (nearIdentityStep N)
        (kernelColumnPoint k (dilation (nearIdentityUnit N i))))
      (translationFixedProjection k hp (nearIdentityStep N)
        (kernelColumnPoint k (dilation (nearIdentityUnit N i))))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb : Tendsto (fun N => (nearIdentityStep N : ℝ)) atTop (𝓝 0) := by
    simpa only [nearIdentityStep, Rat.cast_pow, Rat.cast_inv, Rat.cast_add,
      Rat.cast_natCast, Rat.cast_one, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hinv.pow 2
  have hq : Tendsto (fun N => ((nearIdentityStep N /
      (nearIdentityUnit N i : ℚ) : ℚ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Rat.cast_div, div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv, zero_mul] using
      hb.mul ((tendsto_nearIdentityUnit i).inv₀ one_ne_zero)
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp hq
  apply hC.congr'
  filter_upwards [] with N
  simp only [Function.comp_apply]
  rw [integer_successor_projection_pairing hk hs hp, nearIdentityStep_div_den,
    nearIdentityStep_div]
  simp only [Rat.cast_inv, Rat.cast_natCast, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- Moving correlations of distinct near-identity grid columns tend to zero. -/
theorem tendsto_nearIdentity_moving_pairing {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) {i j : ℕ} (hij : i ≠ j) :
    Tendsto (fun N => kernelColumnPairing k
      (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N i))
      (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N j)))
      atTop (𝓝 0) := by
  have hratio : Tendsto (fun N => ((nearIdentityUnit N j : ℚ) : ℝ) /
      ((nearIdentityUnit N i : ℚ) : ℝ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, inv_one, mul_one] using
      (tendsto_nearIdentityUnit j).mul ((tendsto_nearIdentityUnit i).inv₀ one_ne_zero)
  have habs : Tendsto (fun N => |((nearIdentityUnit N j : ℚ) : ℝ) /
      ((nearIdentityUnit N i : ℚ) : ℝ) - 1|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hratio.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [habs.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with N hN
  have hne : (nearIdentityUnit N j : ℚ) / (nearIdentityUnit N i : ℚ) ≠ 1 := by
    intro he
    have hu : nearIdentityUnit N j = nearIdentityUnit N i :=
      Units.ext ((div_eq_one_iff_eq (nearIdentityUnit N i).ne_zero).mp he)
    exact hij ((nearIdentityUnit_injective N hu).symm)
  have hb := (normSq_movingDilationColumn_pairing_le_inv_den hk hi hs hp
    (nearIdentityStep N) (nearIdentityUnit N i) (nearIdentityUnit N j)
    (nearIdentityUnit_eq_nat_mul_step N j)).trans
      (inv_den_le_abs_sub_one _ hne)
  rw [Rat.cast_div, Complex.normSq_eq_norm_sq] at hb
  rw [dist_zero_right]
  nlinarith only [hb, hN, hε, norm_nonneg (kernelColumnPairing k
    (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N i))
    (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N j)))]

/-- Fixed projection Grams converge to the matrix with zero diagonal and unit off-diagonal. -/
theorem tendsto_nearIdentity_projected_gram {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ))
    (n : ℕ) (i j : Fin n) :
    Tendsto (fun N => kernelColumnGram k (fun a : Fin n =>
      translationFixedProjection k hp (nearIdentityStep N)
        (kernelColumnPoint k (dilation (nearIdentityUnit N a)))) i j)
      atTop (𝓝 ((Matrix.of (fun _ _ : Fin n => (1 : ℂ)) - 1) i j)) := by
  have hf1 : f 1 = 1 := by
    have h := hdil 1 (by norm_num)
    simpa only [map_one, hasIntegerSuccessor_one hs, Units.val_one, Rat.cast_one] using h.symm
  by_cases hij : i = j
  · subst j
    simpa only [kernelColumnGram, Matrix.sub_apply, Matrix.of_apply,
      Matrix.one_apply_eq, sub_self] using tendsto_nearIdentity_projection_pairing hk hs hp i
  · have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    have hz := tendsto_nearIdentity_moving_pairing hk hi hs hp hne
    have hpos (N : ℕ) :
        (0 : ℚ) < (((nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j : ℚˣ) : ℚ) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      exact mul_pos (inv_pos.mpr (nearIdentityUnit_pos N i)) (nearIdentityUnit_pos N j)
    have hfull := hf.tendsto.comp (tendsto_nearIdentityRatio i j)
    have hentry (N : ℕ) : kernelColumnGram k (fun a : Fin n =>
        translationFixedProjection k hp (nearIdentityStep N)
          (kernelColumnPoint k (dilation (nearIdentityUnit N a)))) i j =
        f (((nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j : ℚˣ) : ℚ) -
          kernelColumnPairing k
            (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N i))
            (movingDilationColumn k hp (nearIdentityStep N) (nearIdentityUnit N j)) := by
      have hspl := kernelColumnPairing_projection_decomposition hk (translation (nearIdentityStep N))
        (kernel_translation_locally_periodic hp (nearIdentityStep N))
        (kernelColumnPoint k (dilation (nearIdentityUnit N i)))
        (kernelColumnPoint k (dilation (nearIdentityUnit N j)))
      have hfullpair : kernelColumnPairing k
          (kernelColumnPoint k (dilation (nearIdentityUnit N i)))
          (kernelColumnPoint k (dilation (nearIdentityUnit N j))) =
          f (((nearIdentityUnit N i)⁻¹ * nearIdentityUnit N j : ℚˣ) : ℚ) := by
        rw [kernelColumnPairing_point_left hk]
        change k ((dilation (nearIdentityUnit N i))⁻¹ * dilation (nearIdentityUnit N j)) = _
        rw [← map_inv, ← map_mul]
        exact hdil _ (hpos N)
      rw [hfullpair] at hspl
      have he := eq_sub_of_add_eq hspl.symm
      simpa only [kernelColumnGram, translationFixedProjection,
        movingDilationColumn_eq_sub] using he
    have hlim := (hfull.sub hz).congr' (Eventually.of_forall fun N => (hentry N).symm)
    simpa only [hf1, sub_zero, Matrix.sub_apply, Matrix.of_apply,
      Matrix.one_apply_ne hij] using hlim

/-- An integer-invariant Haar kernel with continuous dilation reading has infinite negative index. -/
theorem negIndex_eq_top_of_integer_invariant_haar_continuous_dilation
    {k : AffineGroupQ → ℂ} (hk : IsHermKernel k) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ)) :
    negIndex k = ⊤ := by
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    let H : Matrix (Fin (r + 2)) (Fin (r + 2)) ℂ := Matrix.of (fun _ _ => 1) - 1
    have hH : H.IsHermitian := by
      ext i j
      change conj ((1 : ℂ) - (if j = i then 1 else 0)) =
        (1 : ℂ) - (if i = j then 1 else 0)
      by_cases hij : i = j
      · simp only [hij, ite_true, sub_self, map_zero]
      · simp only [hij, Ne.symm hij, ite_false, sub_zero, map_one]
    have hc := tendsto_nearIdentity_projected_gram hk hi hs hp hf hdil (r + 2)
    obtain ⟨N, hN⟩ := (eventually_le_hermNegIndex hH hc).exists
    have hlow := constant_sub_one_index_lower (1 : ℂ) (r + 1)
    have hu := hermNegIndex_kernelColumnGram_le hk hi (fun a : Fin (r + 2) =>
      translationFixedProjection k hp (nearIdentityStep N)
        (kernelColumnPoint k (dilation (nearIdentityUnit N a))))
    have he : r + 1 ≤ r := hlow.trans (hN.trans hu)
    omega
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

#print axioms tendsto_nearIdentity_projected_gram
#print axioms negIndex_eq_top_of_integer_invariant_haar_continuous_dilation
end GaloisForLFunctions.AdelicKreinGeometry
