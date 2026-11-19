import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.WeilGaussianSemigroup
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.WeilPairScattering
import GaloisForLFunctions.HilbertMetric.GaussianMetricRankOneFracture
import GaloisForLFunctions.HTGeometry.FiniteMatrixOrthogonalSum
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Positivity and kernels at repeated Gaussian jump labels

For positive semidefinite input, the kernel at every positive time equals
the kernel of the joint-label block projection. The two forms dominate
one another, with upper factor the number of distinct labels. A signed
Weil matrix becomes positive definite at some time exactly when every
retained diagonal block is positive definite. It then stays positive
definite for all sufficiently large times.
-/

noncomputable section
open Matrix Finset Filter
open scoped Topology Matrix
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.Blocks
open HilbertMetric
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
variable {n d : ℕ}

/-- Joint jumps retain precisely the pairs in the same label fiber. -/
def keep (y : Fin n → Fin d → ℝ) (A : Mat n) : Mat n := by
  classical
  exact fun i j => if y i = y j then A i j else 0

/-- Real Gaussian jump evolution in the weak-step normalization. -/
def evolve (t : ℝ) (y : Fin n → Fin d → ℝ) (A : Mat n) : Mat n :=
  (finiteGaussianDistanceGram y (t/8)).hadamard A

private theorem keep_keep (t : ℝ) (y : Fin n → Fin d → ℝ) (A : Mat n) :
    keep y (evolve t y A) = keep y A := by
  classical
  ext i j
  by_cases h : y i = y j <;> simp [keep,evolve,Matrix.hadamard,finiteGaussianDistanceGram,h]

private theorem keep_pd (y : Fin n → Fin d → ℝ) {A : Mat n} (h : A.PosDef) : (keep y A).PosDef := by
  classical
  let s := univ.image y
  let tag (i : Fin n) : s := ⟨y i,mem_image_of_mem y (mem_univ i)⟩
  let f := fun i : Fin n => (tag i,i)
  have hf : Function.Injective f := fun _ _ hh => congrArg Prod.snd hh
  have H := (HTGeometry.matrixFamilyBlockDiagonal_posDef (A := fun _ : s => A) (fun _ => h)).submatrix hf
  convert H using 1
  ext i j
  by_cases h : y i = y j
  · have ht : tag i = tag j := Subtype.ext h
    simp [keep,HTGeometry.matrixFamilyBlockDiagonal,f,ht,h]
  · have ht : tag i ≠ tag j := fun he => h (congrArg Subtype.val he)
    simp [keep,HTGeometry.matrixFamilyBlockDiagonal,f,ht,h]

private theorem zero_cost (y : Fin n → Fin d → ℝ) (i j : Fin n) :
    ∑ k, (y i k-y j k)^2 = 0 ↔ y i = y j := by
  rw [sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (y i k-y j k))]
  simp only [mem_univ,forall_true_left,sq_eq_zero_iff,sub_eq_zero,funext_iff]

/-- Entrywise large-time limit for every real form, including indefinite forms. -/
theorem evolve_limit (y : Fin n → Fin d → ℝ) (A : Mat n) :
    Tendsto (fun t : ℝ => evolve t y A) atTop (𝓝 (keep y A)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases h : y i = y j
  · simpa [keep,evolve,Matrix.hadamard,finiteGaussianDistanceGram,h] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A i j) atTop (𝓝 (A i j)))
  · let c := ∑ k, (y i k-y j k)^2
    have hc : 0 < c := lt_of_le_of_ne (sum_nonneg fun _ _ => sq_nonneg _) (fun he => h ((zero_cost _ _ _).mp he.symm))
    have hlim := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (div_pos hc (by norm_num : (0:ℝ)<8))))
    have he (t : ℝ) : -(t/8)*c = -((c/8)*t) := by ring
    simpa only [keep,if_neg h,evolve,Matrix.hadamard,finiteGaussianDistanceGram,← show c = _ from rfl,
      he,Function.comp_def,id_eq,zero_mul] using hlim.mul_const (A i j)

private theorem evo_hermitian (t : ℝ) (y : Fin n → Fin d → ℝ) {A : Mat n} (hA : A.IsHermitian) :
    (evolve t y A).IsHermitian := by
  ext i j
  have h : ∑ k, (y j k-y i k)^2 = ∑ k, (y i k-y j k)^2 := sum_congr rfl fun _ _ => by ring
  change Real.exp (_*_) * A j i = Real.exp (_*_) * A i j
  rw [h,show A j i = A i j from congrFun (congrFun hA i) j]

private theorem eventual_iff (y : Fin n → Fin d → ℝ) {A : Mat n} (hA : A.IsHermitian) :
    ((∃ t, (evolve t y A).PosDef) ↔ (keep y A).PosDef) ∧
    ((∀ᶠ t : ℝ in atTop, (evolve t y A).PosDef) ↔ (keep y A).PosDef) := by
  have necessary {t} (h : (evolve t y A).PosDef) : (keep y A).PosDef := keep_keep t y A ▸ keep_pd y h
  have tail (h : (keep y A).PosDef) : ∀ᶠ t : ℝ in atTop, (evolve t y A).PosDef :=
    HTGeometry.posDef_eventually_of_tendsto h (Eventually.of_forall fun t => evo_hermitian t y hA)
      (fun i j => (tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp (evolve_limit y A)) i)) j)
  exact ⟨⟨fun ⟨_,h⟩ => necessary h,fun h => (tail h).exists⟩,
    ⟨fun h => let ⟨_,ht⟩ := h.exists; necessary ht,tail⟩⟩

private def signedGram (p : Fin n → {x : ℝ // 1 ≤ x}) : Mat n :=
  fun i j => bareMixedEnergy (probe (p i).val) (probe (p j).val)

private theorem signed_herm (p : Fin n → {x : ℝ // 1 ≤ x}) : (signedGram p).IsHermitian := by
  ext i j
  change bareMixedEnergy _ _ = bareMixedEnergy _ _
  apply bareMixedEnergy_probe_symm <;> linarith only [(p i).property,(p j).property]

/-- A finite signed Weil bank can become strictly positive exactly when
all equal-label blocks are strictly positive. When attainable, strict
positivity holds at every sufficiently late time. -/
theorem signed_weil_eventual (y : Fin n → Fin d → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    ((∃ t, (evolve t y (signedGram p)).PosDef) ↔ (keep y (signedGram p)).PosDef) ∧
    ((∀ᶠ t : ℝ in atTop, (evolve t y (signedGram p)).PosDef) ↔ (keep y (signedGram p)).PosDef) :=
  eventual_iff y (signed_herm p)

/-- The real path is the joint-jump flow of the actual complex probe bank. -/
theorem evolve_signed_complex (t : ℝ) (y : Fin n → Fin d → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    (evolve t y (signedGram p)).map (algebraMap ℝ ℂ) =
      jumpEvolution t (fun k i => y i k) (probeGram fun i => (p i).val) := by
  ext i j
  change ((Real.exp (-(t/8)*∑ k, (y i k-y j k)^2)*signedGram p i j : ℝ) : ℂ) = _
  simp only [jumpEvolution,Matrix.of_apply,jointCost,gapCost,Complex.ofReal_mul,div_eq_mul_inv,
    ← Finset.sum_mul]
  congr 3 <;> ring

private theorem diag_quad {m : ℕ} (c : ℝ) (v : Fin m → ℝ) :
    v ⬝ᵥ (diagonal (fun _ => c)) *ᵥ v = c*(v ⬝ᵥ v) := by
  simp [Matrix.diagonal_mulVec,dotProduct,Finset.mul_sum,mul_left_comm,mul_assoc]

private theorem compressed_bounds {m : ℕ} (t : ℝ) (z : Fin m → Fin d → ℝ)
    (hz : Function.Injective z) (ht : 0 < t) :
    let K := finiteGaussianDistanceGram z (t/8)
    ∃ μ > (0:ℝ), (K-diagonal (fun _ => μ)).PosSemidef ∧ (diagonal (fun _ => (m:ℝ))-K).PosSemidef := by
  intro K
  have hp : K.PosDef := finiteGaussianDistanceGram_posDef_of_injective_of_pos z hz (div_pos ht (by norm_num))
  obtain ⟨μ,hμ,hle⟩ := HTGeometry.posDef_coercive hp
  have hnorm (i j) : |K i j| ≤ 1 := by
    change |Real.exp _| ≤ 1
    rw [abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sum_nonneg fun _ _ => sq_nonneg _)
  refine ⟨μ,hμ,Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hp.1.sub (isHermitian_diagonal _),?_⟩,
    Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨(isHermitian_diagonal _).sub hp.1,?_⟩⟩
  · intro v
    simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,diag_quad,sub_nonneg] using hle v
  · intro v
    have h := (le_abs_self _).trans (HTGeometry.abs_dotProduct_mulVec_le K zero_le_one hnorm v)
    simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,diag_quad,sub_nonneg,mul_one] using h

private theorem quad_scale (a : ℝ) (A : Mat n) (v : Fin n → ℝ) :
    v ⬝ᵥ (a • A) *ᵥ v = a*(v ⬝ᵥ A *ᵥ v) := by
  simp only [dotProduct,mulVec,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Uniform comparison on the positive cone. The upper constant is the
number of distinct joint labels. The lower constant depends only on the
labels and time, independently of the tested matrix. -/
theorem positive_time_comparison (logTime : ℝ) (y : Fin n → Fin d → ℝ) :
    ∃ μ > (0:ℝ), ∀ A : Mat n, A.PosSemidef →
      (evolve (Real.exp logTime) y A-μ • keep y A).PosSemidef ∧
      (((univ.image y).card:ℝ) • keep y A-evolve (Real.exp logTime) y A).PosSemidef := by
  classical
  let s := univ.image y
  let E := Fintype.equivFin s
  let tag (i : Fin n) : s := ⟨y i,mem_image_of_mem y (mem_univ i)⟩
  let r := fun i => E (tag i)
  let z := fun i => (E.symm i).val
  have hz : Function.Injective z := Subtype.val_injective.comp E.symm.injective
  have hzr (i) : z (r i) = y i := congrArg Subtype.val (E.symm_apply_apply (tag i))
  have hr (i j) : r i = r j ↔ y i = y j := E.injective.eq_iff.trans Subtype.ext_iff
  have hm : Fintype.card s = (univ.image y).card := Fintype.card_coe s
  obtain ⟨μ,hμ,hlo,hhi⟩ := compressed_bounds (Real.exp logTime) z hz (Real.exp_pos _)
  refine ⟨μ,hμ,fun A hA => ⟨?_,?_⟩⟩
  · convert ((hlo.submatrix r).hadamard hA) using 1
    ext i j
    by_cases he : y i = y j <;>
      simp [evolve,keep,Matrix.hadamard,Matrix.diagonal_apply,finiteGaussianDistanceGram,hr,he,hzr] <;> ring
  · convert ((hhi.submatrix r).hadamard hA) using 1
    ext i j
    by_cases he : y i = y j <;>
      simp [evolve,keep,Matrix.hadamard,Matrix.diagonal_apply,finiteGaussianDistanceGram,hr,he,hzr,hm] <;> ring

private theorem keep_psd (y : Fin n → Fin d → ℝ) {A : Mat n} (hA : A.PosSemidef) : (keep y A).PosSemidef := by
  classical
  let s := univ.image y
  let tag (i : Fin n) : s := ⟨y i,mem_image_of_mem y (mem_univ i)⟩
  have H := ((Matrix.PosSemidef.one : (1 : Matrix s s ℝ).PosSemidef).submatrix tag).hadamard hA
  convert H using 1
  ext i j
  have h : tag i = tag j ↔ y i = y j := Subtype.ext_iff
  by_cases he : y i = y j <;> simp [keep,Matrix.one_apply,Matrix.hadamard,h,he]

/-- At every positive time the Gaussian jump form of any Gram bank has
exactly the kernel of its block projection, even if labels repeat.
Consequently all positive times have identical ranks. -/
theorem positive_time_kernel {m : ℕ} (logTime : ℝ) (y : Fin n → Fin d → ℝ)
    (B : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    (evolve (Real.exp logTime) y (Bᴴ*B)) *ᵥ v = 0 ↔ keep y (Bᴴ*B) *ᵥ v = 0 := by
  let A := Bᴴ*B
  let J := evolve (Real.exp logTime) y A
  let P := keep y A
  have hA : A.PosSemidef := posSemidef_conjTranspose_mul_self B
  have hP : P.PosSemidef := keep_psd y hA
  obtain ⟨μ,hμ,H⟩ := positive_time_comparison logTime y
  obtain ⟨hl,hu⟩ := H A hA
  have hJ : J.PosSemidef := by
    have h := hl.add (hP.smul hμ.le)
    simpa only [P,sub_add_cancel] using h
  change J *ᵥ v = 0 ↔ P *ᵥ v = 0
  rw [← hJ.dotProduct_mulVec_zero_iff,← hP.dotProduct_mulVec_zero_iff,star_trivial]
  have hlo := hl.dotProduct_mulVec_nonneg v
  have hhi := hu.dotProduct_mulVec_nonneg v
  simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,quad_scale] at hlo hhi
  change 0 ≤ v ⬝ᵥ J *ᵥ v - μ*(v ⬝ᵥ P *ᵥ v) at hlo
  change 0 ≤ _*(v ⬝ᵥ P *ᵥ v) - v ⬝ᵥ J *ᵥ v at hhi
  have hpos := hP.dotProduct_mulVec_nonneg v
  have hjpos := hJ.dotProduct_mulVec_nonneg v
  rw [star_trivial] at hpos hjpos
  constructor
  · intro h
    rw [h,zero_sub,neg_nonneg] at hlo
    exact le_antisymm (nonpos_of_mul_nonpos_right hlo hμ) hpos
  · intro h
    rw [h,mul_zero,zero_sub,neg_nonneg] at hhi
    exact le_antisymm hhi hjpos

#print axioms evolve_limit
#print axioms signed_weil_eventual
#print axioms evolve_signed_complex
#print axioms positive_time_comparison
#print axioms positive_time_kernel
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.Blocks
