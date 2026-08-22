import GaloisForLFunctions.HTGeometry.HilbertCompletionWeakNull
import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The tensor-square Calkin lower bound

A one-particle "shell datum" for a finite family of operators `L i` consists of bounded weakly-null
input sequences `f i` that are asymptotically orthonormal, and a unit test sequence `v` reading the
scale matrix: `⟪v n, L j (f i n)⟫ → δ_{ij}`.

Such a datum amplifies to the tensor square.  The elementary tensors `f i n ⊗ f j n` are again
asymptotically orthonormal and weakly null, `v n ⊗ v n` is again a unit test vector, and the scale
matrix of the tensor family `L i ⊗ L j` is the product of the two one-particle scale matrices.
Consequently the **full weighted coefficient energy of a finite ordered pair section survives every
compact perturbation**:

`(∑_α ‖d α‖²)^{1/2} ≤ ‖∑_α d α • (L α.1 ⊗ L α.2) − K‖`.

Everything happens in `UniformSpace.Completion (H ⊗[ℂ] H)`, the genuine Hilbert tensor square, so
`IsCompactOperator` means what it should.
-/

namespace RHTower

open Filter Topology UniformSpace
open scoped BigOperators TensorProduct

section ShellDatum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A one-particle shell datum for a finite operator family. -/
structure ShellDatum (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The operator family. -/
  L : ι → H →L[ℂ] H
  /-- The input sequences. -/
  f : ι → ℕ → H
  /-- The test sequence. -/
  v : ℕ → H
  /-- The inputs are contractive. -/
  norm_f : ∀ i n, ‖f i n‖ ≤ 1
  /-- The test vectors are unit vectors. -/
  norm_v : ∀ n, ‖v n‖ = 1
  /-- The inputs are weakly null. -/
  weak_f : ∀ (i : ι) (l : H →L[ℂ] ℂ), Tendsto (fun n => l (f i n)) atTop (𝓝 0)
  /-- The inputs are asymptotically orthonormal. -/
  inner_f : ∀ i k : ι,
    Tendsto (fun n => inner ℂ (f i n) (f k n)) atTop (𝓝 (if i = k then (1 : ℂ) else 0))
  /-- The test sequence reads the scale matrix. -/
  inner_Lf : ∀ i j : ι,
    Tendsto (fun n => inner ℂ (v n) (L j (f i n))) atTop (𝓝 (if i = j then (1 : ℂ) else 0))

variable (S : ShellDatum H ι)

/-- The two-particle input vectors, in the algebraic tensor square. -/
noncomputable def ShellDatum.pairInput (u : ι × ι → ℂ) (n : ℕ) : H ⊗[ℂ] H :=
  ∑ b : ι × ι, (u b • S.f b.1 n) ⊗ₜ[ℂ] S.f b.2 n

/-- The two-particle test vector. -/
noncomputable def ShellDatum.pairTest (n : ℕ) : H ⊗[ℂ] H := S.v n ⊗ₜ[ℂ] S.v n

/-- The two-particle operator section. -/
noncomputable def ShellDatum.pairSection (d : ι × ι → ℂ) :
    (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H) :=
  ∑ a : ι × ι, TensorProduct.mapL (d a • S.L a.1) (S.L a.2)

omit [CompleteSpace H] in
/-- The section is the card's coefficient-weighted ordered pair sum. -/
theorem ShellDatum.pairSection_eq (d : ι × ι → ℂ) :
    S.pairSection d = ∑ a : ι × ι, d a • TensorProduct.mapL (S.L a.1) (S.L a.2) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  exact TensorProduct.mapL_smul_left (d a) (S.L a.1) (S.L a.2)

omit [CompleteSpace H] in
theorem ShellDatum.norm_pairTest (n : ℕ) : ‖S.pairTest n‖ = 1 := by
  rw [ShellDatum.pairTest, TensorProduct.norm_tmul, S.norm_v n, mul_one]

omit [CompleteSpace H] in
/-- The scale matrix of the tensor family is the product of the one-particle scale matrices. -/
theorem ShellDatum.inner_pairTest_map (a b : ι × ι) :
    Tendsto (fun n => inner ℂ (S.pairTest n)
        (TensorProduct.mapL (S.L a.1) (S.L a.2) (S.f b.1 n ⊗ₜ[ℂ] S.f b.2 n)))
      atTop (𝓝 (if b = a then (1 : ℂ) else 0)) := by
  have hmap : ∀ n : ℕ,
      inner ℂ (S.pairTest n)
          (TensorProduct.mapL (S.L a.1) (S.L a.2) (S.f b.1 n ⊗ₜ[ℂ] S.f b.2 n))
        = inner ℂ (S.v n) (S.L a.1 (S.f b.1 n)) * inner ℂ (S.v n) (S.L a.2 (S.f b.2 n)) := by
    intro n
    rw [ShellDatum.pairTest]
    have hval : TensorProduct.mapL (S.L a.1) (S.L a.2) (S.f b.1 n ⊗ₜ[ℂ] S.f b.2 n)
        = (S.L a.1 (S.f b.1 n)) ⊗ₜ[ℂ] (S.L a.2 (S.f b.2 n)) :=
      TensorProduct.mapL_tmul _ _ _ _
    rw [hval, TensorProduct.inner_tmul]
  simp only [hmap]
  have hlim := (S.inner_Lf b.1 a.1).mul (S.inner_Lf b.2 a.2)
  have hprod : ((if b.1 = a.1 then (1 : ℂ) else 0) * (if b.2 = a.2 then (1 : ℂ) else 0))
      = if b = a then (1 : ℂ) else 0 := by
    by_cases h1 : b.1 = a.1 <;> by_cases h2 : b.2 = a.2 <;>
      simp [h1, h2, Prod.ext_iff]
  rw [← hprod]
  exact hlim

omit [CompleteSpace H] in
/-- The two-particle inputs are uniformly bounded. -/
theorem ShellDatum.norm_pairInput_le (u : ι × ι → ℂ) (n : ℕ) :
    ‖S.pairInput u n‖ ≤ ∑ b : ι × ι, ‖u b‖ := by
  rw [ShellDatum.pairInput]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b _ => ?_
  rw [TensorProduct.norm_tmul, norm_smul]
  have h1 := S.norm_f b.1 n
  have h2 := S.norm_f b.2 n
  have hprod : ‖S.f b.1 n‖ * ‖S.f b.2 n‖ ≤ 1 := by
    nlinarith [norm_nonneg (S.f b.1 n), norm_nonneg (S.f b.2 n)]
  calc ‖u b‖ * ‖S.f b.1 n‖ * ‖S.f b.2 n‖ = ‖u b‖ * (‖S.f b.1 n‖ * ‖S.f b.2 n‖) := by ring
    _ ≤ ‖u b‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖u b‖ := mul_one _

omit [CompleteSpace H] in
/-- The two-particle inputs are asymptotically orthonormal: their squared norm converges to the
squared coefficient mass. -/
theorem ShellDatum.inner_pairInput_tendsto (u : ι × ι → ℂ) :
    Tendsto (fun n => inner ℂ (S.pairInput u n) (S.pairInput u n)) atTop
      (𝓝 (∑ b : ι × ι, (starRingEnd ℂ) (u b) * u b)) := by
  have hexp : (fun n => inner ℂ (S.pairInput u n) (S.pairInput u n))
      = fun n => ∑ b : ι × ι, ∑ c : ι × ι, u b * (starRingEnd ℂ) (u c) *
          (inner ℂ (S.f c.1 n) (S.f b.1 n) * inner ℂ (S.f c.2 n) (S.f b.2 n)) := by
    funext n
    simp only [ShellDatum.pairInput, sum_inner, inner_sum, TensorProduct.inner_tmul,
      inner_smul_left, inner_smul_right]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  rw [hexp]
  have hlim : Tendsto (fun n => ∑ b : ι × ι, ∑ c : ι × ι, u b * (starRingEnd ℂ) (u c) *
        (inner ℂ (S.f c.1 n) (S.f b.1 n) * inner ℂ (S.f c.2 n) (S.f b.2 n))) atTop
      (𝓝 (∑ b : ι × ι, ∑ c : ι × ι, u b * (starRingEnd ℂ) (u c) *
        ((if c.1 = b.1 then (1 : ℂ) else 0) * (if c.2 = b.2 then (1 : ℂ) else 0)))) := by
    refine tendsto_finsetSum _ fun b _ => tendsto_finsetSum _ fun c _ => ?_
    exact ((S.inner_f c.1 b.1).mul (S.inner_f c.2 b.2)).const_mul _
  have hval : (∑ b : ι × ι, ∑ c : ι × ι, u b * (starRingEnd ℂ) (u c) *
        ((if c.1 = b.1 then (1 : ℂ) else 0) * (if c.2 = b.2 then (1 : ℂ) else 0)))
      = ∑ b : ι × ι, (starRingEnd ℂ) (u b) * u b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single b]
    · simp
      ring
    · intro c _ hcb
      have hzero : ((if c.1 = b.1 then (1 : ℂ) else 0) * (if c.2 = b.2 then (1 : ℂ) else 0)) = 0 := by
        by_cases h1 : c.1 = b.1
        · by_cases h2 : c.2 = b.2
          · exact absurd (Prod.ext_iff.mpr ⟨h1, h2⟩) hcb
          · simp [h2]
        · simp [h1]
      rw [hzero, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ b) hmem
  rw [← hval]
  exact hlim

omit [CompleteSpace H] in
/-- The two-particle inputs are weakly null against the algebraic tensor square. -/
theorem ShellDatum.weak_pairInput (u : ι × ι → ℂ) (y : H ⊗[ℂ] H) :
    Tendsto (fun n => inner ℂ y (S.pairInput u n)) atTop (𝓝 (0 : ℂ)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      have hexp : (fun n => inner ℂ (a ⊗ₜ[ℂ] b) (S.pairInput u n))
          = fun n => ∑ e : ι × ι, u e * (inner ℂ a (S.f e.1 n) * inner ℂ b (S.f e.2 n)) := by
        funext n
        simp only [ShellDatum.pairInput, inner_sum, TensorProduct.inner_tmul, inner_smul_right]
        exact Finset.sum_congr rfl fun e _ => by ring
      rw [hexp]
      have hzero : (0 : ℂ) = ∑ _e : ι × ι, (0 : ℂ) := by simp
      rw [hzero]
      refine tendsto_finsetSum _ fun e _ => ?_
      have hA : Tendsto (fun n => inner ℂ a (S.f e.1 n)) atTop (𝓝 (0 : ℂ)) := by
        simpa using S.weak_f e.1 (innerSL ℂ a)
      have hB : ∀ n, ‖inner ℂ b (S.f e.2 n)‖ ≤ ‖b‖ := by
        intro n
        calc ‖inner ℂ b (S.f e.2 n)‖ ≤ ‖b‖ * ‖S.f e.2 n‖ := norm_inner_le_norm _ _
          _ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left (S.norm_f e.2 n) (norm_nonneg b)
          _ = ‖b‖ := mul_one _
      have hprod : Tendsto (fun n => inner ℂ a (S.f e.1 n) * inner ℂ b (S.f e.2 n)) atTop
          (𝓝 (0 : ℂ)) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hnorm : Tendsto (fun n => ‖inner ℂ a (S.f e.1 n)‖) atTop (𝓝 0) :=
          tendsto_zero_iff_norm_tendsto_zero.mp hA
        have hg : Tendsto (fun n => ‖inner ℂ a (S.f e.1 n)‖ * ‖b‖) atTop (𝓝 0) := by
          simpa using hnorm.mul_const ‖b‖
        refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)
      simpa using hprod.const_mul (u e)
  | add y1 y2 h1 h2 =>
      have hexp : (fun n => inner ℂ (y1 + y2) (S.pairInput u n))
          = fun n => inner ℂ y1 (S.pairInput u n) + inner ℂ y2 (S.pairInput u n) := by
        funext n
        rw [inner_add_left]
      rw [hexp]
      simpa using h1.add h2

omit [CompleteSpace H] in
/-- The two-particle pairing reads the coefficient contraction. -/
theorem ShellDatum.inner_pairTest_pairSection_tendsto (d u : ι × ι → ℂ) :
    Tendsto (fun n => inner ℂ (S.pairTest n) (S.pairSection d (S.pairInput u n))) atTop
      (𝓝 (∑ a : ι × ι, d a * u a)) := by
  have hexp : (fun n => inner ℂ (S.pairTest n) (S.pairSection d (S.pairInput u n)))
      = fun n => ∑ a : ι × ι, ∑ b : ι × ι, d b * u a *
          (inner ℂ (S.v n) (S.L b.1 (S.f a.1 n)) * inner ℂ (S.v n) (S.L b.2 (S.f a.2 n))) := by
    funext n
    have hterm : ∀ a b : ι × ι,
        TensorProduct.mapL (d a • S.L a.1) (S.L a.2) ((u b • S.f b.1 n) ⊗ₜ[ℂ] S.f b.2 n)
          = (d a • (u b • S.L a.1 (S.f b.1 n))) ⊗ₜ[ℂ] (S.L a.2 (S.f b.2 n)) := by
      intro a b
      rw [TensorProduct.mapL_tmul]
      congr 1
      rw [smul_apply, map_smul]
    simp only [ShellDatum.pairSection, ShellDatum.pairInput, ShellDatum.pairTest,
      sum_apply, map_sum, inner_sum, hterm, TensorProduct.inner_tmul,
      inner_smul_right]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hexp]
  have hlim : Tendsto (fun n => ∑ a : ι × ι, ∑ b : ι × ι, d b * u a *
        (inner ℂ (S.v n) (S.L b.1 (S.f a.1 n)) * inner ℂ (S.v n) (S.L b.2 (S.f a.2 n)))) atTop
      (𝓝 (∑ a : ι × ι, ∑ b : ι × ι, d b * u a *
        ((if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2 = b.2 then (1 : ℂ) else 0)))) := by
    refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
    exact ((S.inner_Lf a.1 b.1).mul (S.inner_Lf a.2 b.2)).const_mul _
  have hval : (∑ a : ι × ι, ∑ b : ι × ι, d b * u a *
        ((if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2 = b.2 then (1 : ℂ) else 0)))
      = ∑ a : ι × ι, d a * u a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      have hzero : ((if a.1 = b.1 then (1 : ℂ) else 0) * (if a.2 = b.2 then (1 : ℂ) else 0)) = 0 := by
        by_cases h1 : a.1 = b.1
        · by_cases h2 : a.2 = b.2
          · exact absurd (Prod.ext_iff.mpr ⟨h1.symm, h2.symm⟩) hba
          · simp [h2]
        · simp [h1]
      rw [hzero, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ a) hmem
  rw [← hval]
  exact hlim

end ShellDatum

end RHTower
