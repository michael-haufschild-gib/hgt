import GaloisForLFunctions.RHTower.DeningerSigmaSeminorm
import GaloisForLFunctions.RHTower.DeningerSeminormInducedCompleted
import GaloisForLFunctions.RHTower.DeningerNuclearTsum

/-!
# A countable direct sum of nuclear spaces is nuclear

The comparison map of two direct sum seminorms is the sum, over all coordinates, of the coordinate
comparison maps conjugated by the coordinate projection and the coordinate inclusion.  Unlike the
product, that sum is infinite, so the masses of the coordinate nuclear representations have to be
made summable.  They can be: enlarging the dominating weight on a coordinate divides the mass of the
comparison map on that coordinate by the same factor, so choosing the weights to grow geometrically
along an injection of the index set into the natural numbers forces the masses to be summable.

The sum then converges in the operator norm, and its value is identified with the comparison map on
the dense subspace of classes of vectors of the direct sum — where only finitely many coordinates
contribute.

* `deningerSigma_eq_sum_single` : a vector of a direct sum is the sum of its coordinate vectors.
* `deningerIsNuclearSpaceC_sigma` : **a countable direct sum of nuclear spaces is nuclear.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap

open scoped NNReal

section Support

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {ι : Type*} [DecidableEq ι] {F : ι → Type*}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- A vector of a direct sum is the sum of its coordinate vectors, over any finite set containing
its support. -/
theorem deningerSigma_eq_sum_single (x : Π₀ i, F i) (s : Finset ι) (hs : ∀ i ∉ s, x i = 0) :
    x = ∑ i ∈ s, DFinsupp.lsingle (R := 𝕜) i (x i) := by
  refine DFinsupp.ext fun j => ?_
  have hval : ∀ i : ι, (DFinsupp.lsingle (R := 𝕜) i (x i)) j = (DFinsupp.single i (x i)) j := by
    intro i
    rw [DFinsupp.lsingle_apply]
  rw [DFinsupp.finsetSum_apply]
  simp only [hval]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single_of_mem j hj (fun i _ hi => DFinsupp.single_eq_of_ne (Ne.symm hi)),
      DFinsupp.single_eq_same]
  · rw [hs j hj]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    have hne : j ≠ i := by
      rintro rfl
      exact hj hi
    exact DFinsupp.single_eq_of_ne hne

end Support

section SigmaNuclear

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {ι : Type} [DecidableEq ι] [Countable ι] {F : ι → Type*}
variable [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

omit [CompleteSpace 𝕜] in
/-- **A countable direct sum of nuclear spaces is nuclear.** -/
theorem deningerIsNuclearSpaceC_sigma {κ : ι → Type*} (P : ∀ i, SeminormFamily 𝕜 (F i) (κ i))
    (hP : ∀ i, DeningerIsNuclearSpaceC (P i)) :
    DeningerIsNuclearSpaceC (deningerSigmaFamily P) := by
  classical
  rintro ⟨a, c⟩
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  choose b C hle hnucC using fun i => hP i (a i)
  choose M hMnn hMle using fun i => (hnucC i).exists_nuclearLe
  -- the dominating weights
  obtain ⟨v, hvreal⟩ : ∃ v : ι → ℝ≥0, ∀ i,
      (v i : ℝ) = ((c i : ℝ) + 1) * (|C i| + 1) * (M i + 1) * 2 ^ e i := by
    refine ⟨fun i =>
      (c i + 1) * (Real.toNNReal |C i| + 1) * (Real.toNNReal (M i) + 1) * 2 ^ e i, fun i => ?_⟩
    push_cast [Real.coe_toNNReal _ (abs_nonneg (C i)), Real.coe_toNNReal _ (hMnn i)]
    ring
  have hcnn : ∀ i, (0 : ℝ) ≤ (c i : ℝ) := fun i => (c i).coe_nonneg
  have htpos : ∀ i, (1 : ℝ) ≤ (2 : ℝ) ^ e i := fun i => one_le_pow₀ (by norm_num)
  have hvge : ∀ i, (1 : ℝ) ≤ (v i : ℝ) := by
    intro i
    rw [hvreal i]
    have h1 : (1 : ℝ) ≤ ((c i : ℝ) + 1) * (|C i| + 1) := by
      nlinarith [hcnn i, abs_nonneg (C i)]
    have h2 : (1 : ℝ) ≤ ((c i : ℝ) + 1) * (|C i| + 1) * (M i + 1) := by
      nlinarith [hMnn i]
    nlinarith [htpos i]
  have hvpos : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => lt_of_lt_of_le one_pos (hvge i)
  have hvabs : ∀ i, (c i : ℝ) * |C i| ≤ (v i : ℝ) := by
    intro i
    rw [hvreal i]
    have hA : (0 : ℝ) ≤ ((c i : ℝ) + 1) * (|C i| + 1) := by positivity
    have h1 : (c i : ℝ) * |C i| ≤ ((c i : ℝ) + 1) * (|C i| + 1) := by
      nlinarith [hcnn i, abs_nonneg (C i)]
    have h2 : ((c i : ℝ) + 1) * (|C i| + 1)
        ≤ ((c i : ℝ) + 1) * (|C i| + 1) * (M i + 1) :=
      le_mul_of_one_le_right hA (by linarith [hMnn i])
    have hB : (0 : ℝ) ≤ ((c i : ℝ) + 1) * (|C i| + 1) * (M i + 1) := by
      nlinarith [hA, hMnn i]
    have h3 : ((c i : ℝ) + 1) * (|C i| + 1) * (M i + 1)
        ≤ ((c i : ℝ) + 1) * (|C i| + 1) * (M i + 1) * 2 ^ e i :=
      le_mul_of_one_le_right hB (htpos i)
    linarith
  have hvmass : ∀ i, (c i : ℝ) * ((v i : ℝ)⁻¹ * M i) ≤ (1 / 2 : ℝ) ^ e i := by
    intro i
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ e i := by positivity
    have hkey : (c i : ℝ) * M i * 2 ^ e i ≤ (v i : ℝ) := by
      rw [hvreal i]
      have hstep : (c i : ℝ) * M i ≤ ((c i : ℝ) + 1) * (M i + 1) := by
        have hexp : ((c i : ℝ) + 1) * (M i + 1)
            = (c i : ℝ) * M i + ((c i : ℝ) + M i + 1) := by ring
        rw [hexp]
        linarith [hcnn i, hMnn i]
      have hfac : ((c i : ℝ) + 1) ≤ ((c i : ℝ) + 1) * (|C i| + 1) :=
        le_mul_of_one_le_right (by linarith [hcnn i]) (by linarith [abs_nonneg (C i)])
      have hstep2 : ((c i : ℝ) + 1) * (M i + 1)
          ≤ ((c i : ℝ) + 1) * (|C i| + 1) * (M i + 1) :=
        mul_le_mul_of_nonneg_right hfac (by linarith [hMnn i])
      exact mul_le_mul_of_nonneg_right (hstep.trans hstep2) (le_of_lt h2pos)
    have heq : (c i : ℝ) * ((v i : ℝ)⁻¹ * M i) = ((c i : ℝ) * M i) / (v i : ℝ) := by
      rw [div_eq_mul_inv]
      ring
    have hinv : ((1 : ℝ) / 2) ^ e i * 2 ^ e i = 1 := by
      rw [← mul_pow]
      norm_num
    rw [heq, div_le_iff₀ (hvpos i)]
    calc (c i : ℝ) * M i = ((c i : ℝ) * M i * 2 ^ e i) * ((1 / 2 : ℝ) ^ e i) := by
          rw [mul_assoc, mul_comm ((2 : ℝ) ^ e i) ((1 / 2 : ℝ) ^ e i), hinv, mul_one]
      _ ≤ (v i : ℝ) * ((1 / 2 : ℝ) ^ e i) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = (1 / 2 : ℝ) ^ e i * (v i : ℝ) := mul_comm _ _
  -- the two seminorms
  have hsingle : ∀ (i : ι) (u : F i),
      deningerSigmaFamily P (a, c) (DFinsupp.lsingle (R := 𝕜) i u) = (c i : ℝ) * P i (a i) u := by
    intro i u
    rw [DFinsupp.lsingle_apply, deningerSigmaFamily, deningerSigmaSeminorm_single,
      smul_apply, NNReal.smul_def, smul_eq_mul]
  have hprojle : ∀ (i : ι) (x : Π₀ j, F j),
      (v i : ℝ) * P i (b i) (x i) ≤ deningerSigmaFamily P (b, v) x := by
    intro i x
    have h := deningerSigmaSeminorm_proj_le (fun j => v j • P j (b j)) x i
    rw [smul_apply, NNReal.smul_def, smul_eq_mul] at h
    exact h
  have hdom : ∀ x, deningerSigmaFamily P (a, c) x ≤ 1 * deningerSigmaFamily P (b, v) x := by
    intro x
    rw [one_mul, deningerSigmaFamily_apply, deningerSigmaFamily_apply]
    have hsum1 := deningerSigmaSummable (fun i => c i • P i (a i)) x
    have hsum2 := deningerSigmaSummable (fun i => v i • P i (b i)) x
    have hcoe1 : ∀ i, ((c i • P i (a i)) : Seminorm 𝕜 (F i)) (x i)
        = (c i : ℝ) * P i (a i) (x i) := fun i => by
      rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    have hcoe2 : ∀ i, ((v i • P i (b i)) : Seminorm 𝕜 (F i)) (x i)
        = (v i : ℝ) * P i (b i) (x i) := fun i => by
      rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    simp only [hcoe1] at hsum1
    simp only [hcoe2] at hsum2
    refine hsum1.tsum_le_tsum (fun i => ?_) hsum2
    calc (c i : ℝ) * P i (a i) (x i)
        ≤ (c i : ℝ) * (|C i| * P i (b i) (x i)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hcnn i)
          exact deningerSeminorm_le_abs (hle i) (x i)
      _ = ((c i : ℝ) * |C i|) * P i (b i) (x i) := by ring
      _ ≤ (v i : ℝ) * P i (b i) (x i) :=
          mul_le_mul_of_nonneg_right (hvabs i) (apply_nonneg _ _)
  refine ⟨(b, v), 1, hdom, ?_⟩
  -- the coordinate maps
  have hproj : ∀ i : ι, ∀ x : Π₀ j, F j,
      P i (b i) ((DFinsupp.lapply (R := 𝕜) i) x)
        ≤ (v i : ℝ)⁻¹ * deningerSigmaFamily P (b, v) x := by
    intro i x
    rw [DFinsupp.lapply_apply, ← div_eq_inv_mul, le_div_iff₀ (hvpos i), mul_comm]
    exact hprojle i x
  have hincl : ∀ i : ι, ∀ u : F i,
      deningerSigmaFamily P (a, c) ((DFinsupp.lsingle (R := 𝕜) i) u) ≤ (c i : ℝ) * P i (a i) u :=
    fun i u => le_of_eq (hsingle i u)
  obtain ⟨proj, hprojdef⟩ : ∃ proj : ∀ i : ι,
      DeningerSeminormCompletion (deningerSigmaFamily P (b, v)) →L[𝕜]
        DeningerSeminormCompletion (P i (b i)),
      ∀ i, proj i = deningerSeminormInducedC (DFinsupp.lapply (R := 𝕜) i) (hproj i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨incl, hincldef⟩ : ∃ incl : ∀ i : ι, DeningerSeminormCompletion (P i (a i)) →L[𝕜]
      DeningerSeminormCompletion (deningerSigmaFamily P (a, c)),
      ∀ i, incl i = deningerSeminormInducedC (DFinsupp.lsingle (R := 𝕜) i) (hincl i) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ι → (DeningerSeminormCompletion (deningerSigmaFamily P (b, v)) →L[𝕜]
      DeningerSeminormCompletion (deningerSigmaFamily P (a, c))),
      ∀ i, G i = (incl i).comp ((deningerSeminormComparisonC (hle i)).comp (proj i)) :=
    ⟨_, fun _ => rfl⟩
  -- the masses are summable
  have hprojnorm : ∀ i, ‖proj i‖ ≤ (v i : ℝ)⁻¹ := by
    intro i
    rw [hprojdef i]
    exact deningerSeminormInducedC_norm_le (le_of_lt (inv_pos.mpr (hvpos i))) _ (hproj i)
  have hinclnorm : ∀ i, ‖incl i‖ ≤ (c i : ℝ) := by
    intro i
    rw [hincldef i]
    exact deningerSeminormInducedC_norm_le (hcnn i) _ (hincl i)
  have hGmass : ∀ i, DeningerIsNuclearLe (G i) ((1 / 2 : ℝ) ^ e i) := by
    intro i
    rw [hG i]
    have h1 := (hMle i).compR (proj i)
    have h2 := h1.compL (incl i)
    refine h2.mono ?_
    refine le_trans ?_ (hvmass i)
    have hstep1 : ‖proj i‖ * M i ≤ (v i : ℝ)⁻¹ * M i :=
      mul_le_mul_of_nonneg_right (hprojnorm i) (hMnn i)
    have hnn : (0 : ℝ) ≤ (v i : ℝ)⁻¹ * M i :=
      mul_nonneg (le_of_lt (inv_pos.mpr (hvpos i))) (hMnn i)
    calc ‖incl i‖ * (‖proj i‖ * M i) ≤ ‖incl i‖ * ((v i : ℝ)⁻¹ * M i) :=
          mul_le_mul_of_nonneg_left hstep1 (norm_nonneg _)
      _ ≤ (c i : ℝ) * ((v i : ℝ)⁻¹ * M i) := mul_le_mul_of_nonneg_right (hinclnorm i) hnn
  have hNsummable : Summable fun i : ι => (1 / 2 : ℝ) ^ e i := by
    have hgeo : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact hgeo.comp_injective he
  have hGnorm : ∀ i, ‖G i‖ ≤ (1 / 2 : ℝ) ^ e i := fun i => (hGmass i).norm_le
  have hGsummable : Summable G := by
    refine Summable.of_norm ?_
    exact Summable.of_nonneg_of_le (fun i => norm_nonneg _) hGnorm hNsummable
  obtain ⟨S', hS'⟩ := hGsummable
  have hpt : ∀ z, HasSum (fun i => G i z) (S' z) := fun z =>
    (ContinuousLinearMap.apply 𝕜
      (DeningerSeminormCompletion (deningerSigmaFamily P (a, c))) z).hasSum hS'
  have hS'nuc : DeningerIsNuclearLe S' (∑' i : ι, (1 / 2 : ℝ) ^ e i) :=
    DeningerIsNuclearLe.tsum hGmass hNsummable hpt
  -- the sum is the comparison map
  have hGmk : ∀ (i : ι) (x : Π₀ j, F j),
      G i (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x)
        = deningerSeminormMkC (deningerSigmaFamily P (a, c))
            (DFinsupp.lsingle (R := 𝕜) i (x i)) := by
    intro i x
    have h1 : proj i (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x)
        = deningerSeminormMkC (P i (b i)) (x i) := by
      rw [hprojdef i, deningerSeminormInducedC_mkC, DFinsupp.lapply_apply]
    have h2 : deningerSeminormComparisonC (hle i) (deningerSeminormMkC (P i (b i)) (x i))
        = deningerSeminormMkC (P i (a i)) (x i) :=
      deningerSeminormComparisonC_mkC (hle i) (x i)
    have h3 : incl i (deningerSeminormMkC (P i (a i)) (x i))
        = deningerSeminormMkC (deningerSigmaFamily P (a, c))
            (DFinsupp.lsingle (R := 𝕜) i (x i)) := by
      rw [hincldef i]
      exact deningerSeminormInducedC_mkC _ _ (x i)
    rw [hG i]
    simp only [ContinuousLinearMap.comp_apply]
    rw [h1, h2, h3]
  have hSeq : deningerSeminormComparisonC hdom = S' := by
    refine DFunLike.coe_injective ?_
    refine (deningerDenseRange_toComplL (deningerSigmaFamily P (b, v))).equalizer
      (deningerSeminormComparisonC hdom).continuous S'.continuous ?_
    funext z
    obtain ⟨x, rfl⟩ := deningerSeminormMk_surjective (deningerSigmaFamily P (b, v)) z
    have hfin := x.finite_support
    have hsupp : ∀ i ∉ hfin.toFinset, x i = 0 := by
      intro i hi
      by_contra hne
      exact hi (hfin.mem_toFinset.mpr hne)
    have hzero : ∀ i ∉ hfin.toFinset,
        G i (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x) = 0 := by
      intro i hi
      rw [hGmk, hsupp i hi, map_zero, map_zero]
    have hfinsum : HasSum (fun i => G i (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x))
        (∑ i ∈ hfin.toFinset, G i (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x)) :=
      hasSum_sum_of_ne_finset_zero hzero
    have hvalue : ∑ i ∈ hfin.toFinset,
        G i (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x)
          = deningerSeminormMkC (deningerSigmaFamily P (a, c)) x := by
      simp only [hGmk]
      rw [← map_sum, ← deningerSigma_eq_sum_single (𝕜 := 𝕜) x hfin.toFinset hsupp]
    show deningerSeminormComparisonC hdom
        (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x)
      = S' (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x)
    rw [deningerSeminormComparisonC_mkC hdom x]
    rw [(hpt (deningerSeminormMkC (deningerSigmaFamily P (b, v)) x)).unique hfinsum, hvalue]
  rw [hSeq]
  exact hS'nuc.isNuclear

end SigmaNuclear

end RHTower
