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

/-- The uniform-`ℂ`-action instance on a Hilbert tensor product.  Stated as a lemma so that
concrete carriers can obtain it without a deep instance search. -/
theorem tensorProduct_uniformContinuousConstSMul {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    UniformContinuousConstSMul ℂ (E ⊗[ℂ] F) := inferInstance

/-- The normed group of the completed Hilbert tensor product, as a lemma for shallow instantiation. -/
@[reducible] noncomputable def tensorCompletion_normedAddCommGroup {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    NormedAddCommGroup (Completion (E ⊗[ℂ] F)) := inferInstance

/-- The normed space structure of the completed Hilbert tensor product. -/
@[reducible] noncomputable def tensorCompletion_normedSpace {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    NormedSpace ℂ (Completion (E ⊗[ℂ] F)) := inferInstance

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

omit [CompleteSpace H] in
/-- Two scalars on the two factors of a tensor map can be merged into the first factor. -/
theorem mapL_smul_smul (c₁ c₂ : ℂ) (f g : H →L[ℂ] H) :
    TensorProduct.mapL (c₁ • f) (c₂ • g) = TensorProduct.mapL ((c₁ * c₂) • f) g := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
      rw [TensorProduct.mapL_tmul, TensorProduct.mapL_tmul, smul_apply, smul_apply, smul_apply,
        ← TensorProduct.smul_tmul, smul_smul, mul_comm c₂ c₁]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]

/-! ## The tensor-square Calkin lower bound -/

omit [CompleteSpace H] in
/-- **Card `(1)`/`(2)`: the full weighted coefficient energy of a finite ordered pair section
survives every compact perturbation of the Hilbert tensor square.** -/
theorem ShellDatum.tensor_calkin_lower (d : ι × ι → ℂ)
    (K : Completion (H ⊗[ℂ] H) →L[ℂ] Completion (H ⊗[ℂ] H)) (hK : IsCompactOperator K) :
    Real.sqrt (∑ a : ι × ι, ‖d a‖ ^ (2 : ℕ)) ≤ ‖(S.pairSection d).completion - K‖ := by
  set E : ℝ := ∑ a : ι × ι, ‖d a‖ ^ (2 : ℕ) with hE
  have hEnonneg : 0 ≤ E := by
    rw [hE]
    refine Finset.sum_nonneg fun a _ => ?_
    positivity
  rcases eq_or_lt_of_le hEnonneg with hE0 | hEpos
  · rw [← hE0, Real.sqrt_zero]
    exact norm_nonneg ((S.pairSection d).completion - K)
  set R : ℝ := Real.sqrt E with hR
  have hRpos : 0 < R := Real.sqrt_pos.mpr hEpos
  have hRsq : R * R = E := Real.mul_self_sqrt hEnonneg
  set u : ι × ι → ℂ := fun a => (starRingEnd ℂ) (d a) / (R : ℂ) with hu
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have husum : (∑ a : ι × ι, (starRingEnd ℂ) (u a) * u a) = 1 := by
    have hterm : ∀ a : ι × ι, (starRingEnd ℂ) (u a) * u a
        = ((‖d a‖ ^ (2 : ℕ) : ℝ) : ℂ) / ((R : ℂ) * (R : ℂ)) := by
      intro a
      rw [hu]
      simp only [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
      rw [div_mul_div_comm]
      congr 1
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_div]
    rw [show ((R : ℂ) * (R : ℂ)) = ((E : ℝ) : ℂ) by exact_mod_cast hRsq]
    rw [← Complex.ofReal_sum]
    rw [hE]
    exact div_self (by exact_mod_cast hEpos.ne')
  have hdusum : (∑ a : ι × ι, d a * u a) = ((R : ℝ) : ℂ) := by
    have hterm : ∀ a : ι × ι, d a * u a = ((‖d a‖ ^ (2 : ℕ) : ℝ) : ℂ) / (R : ℂ) := by
      intro a
      rw [hu, mul_div_assoc']
      congr 1
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_div, ← Complex.ofReal_sum, ← hE]
    rw [show ((E : ℝ) : ℂ) = ((R : ℂ) * (R : ℂ)) by exact_mod_cast hRsq.symm]
    field_simp
  -- the two-particle sequences
  have hsq : ∀ n, ((‖S.pairInput u n‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = inner ℂ (S.pairInput u n) (S.pairInput u n) := by
    intro n
    exact_mod_cast (inner_self_eq_norm_sq_to_K (S.pairInput u n)).symm
  have hnormsq : Tendsto (fun n => ‖S.pairInput u n‖ ^ (2 : ℕ)) atTop (𝓝 1) := by
    have h := S.inner_pairInput_tendsto u
    rw [husum] at h
    have h2 : Tendsto (fun n => ((‖S.pairInput u n‖ ^ (2 : ℕ) : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      simpa [hsq] using h
    have h3 := (Complex.continuous_re.tendsto (1 : ℂ)).comp h2
    simp only [Function.comp_def, Complex.ofReal_re, Complex.one_re] at h3
    exact h3
  have hnorm1 : Tendsto (fun n => ‖S.pairInput u n‖) atTop (𝓝 1) := by
    have h := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hnormsq
    simp only [Function.comp_def] at h
    have hrw : ∀ n, Real.sqrt (‖S.pairInput u n‖ ^ (2 : ℕ)) = ‖S.pairInput u n‖ := fun n =>
      Real.sqrt_sq (norm_nonneg _)
    simpa [hrw, Real.sqrt_one] using h
  -- compact operator kills the weakly null lifted sequence
  have hbound : ∀ n, ‖S.pairInput u n‖ ≤ ∑ b : ι × ι, ‖u b‖ := S.norm_pairInput_le u
  have hCnonneg : (0 : ℝ) ≤ ∑ b : ι × ι, ‖u b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have hcoebound : ∀ n, ‖((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))‖
      ≤ ∑ b : ι × ι, ‖u b‖ := by
    intro n
    rw [Completion.norm_coe]
    exact hbound n
  have hweak := fun l => HTGeometry.completion_weakly_tendsto_zero
    (E := H ⊗[ℂ] H) (S.pairInput u) (∑ b : ι × ι, ‖u b‖) hCnonneg hbound
    (S.weak_pairInput u) l
  have hKzero : Tendsto
      (fun n => ‖K ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))‖) atTop (𝓝 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null K hK
      (fun n => ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H)))
      (∑ b : ι × ι, ‖u b‖) hcoebound hweak
  -- the pairing
  set T : (H ⊗[ℂ] H) →L[ℂ] (H ⊗[ℂ] H) := S.pairSection d with hT
  have hpair : ∀ n, inner ℂ ((S.pairTest n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))
        (T.completion ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H)))
      = inner ℂ (S.pairTest n) (T (S.pairInput u n)) := by
    intro n
    rw [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe]
  have hpairlim : Tendsto (fun n => ‖inner ℂ ((S.pairTest n : H ⊗[ℂ] H) :
      Completion (H ⊗[ℂ] H)) (T.completion ((S.pairInput u n : H ⊗[ℂ] H) :
        Completion (H ⊗[ℂ] H)))‖) atTop (𝓝 R) := by
    have h := (S.inner_pairTest_pairSection_tendsto d u).norm
    rw [hdusum] at h
    simp only [hpair]
    simpa [Complex.norm_real, Real.norm_of_nonneg hRpos.le] using h
  -- the upper estimate
  have hupper : ∀ n, ‖inner ℂ ((S.pairTest n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))
        (T.completion ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H)))‖
      ≤ ‖T.completion - K‖ * ‖S.pairInput u n‖
        + ‖K ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))‖ := by
    intro n
    have hw : ‖((S.pairTest n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))‖ = 1 := by
      rw [Completion.norm_coe, S.norm_pairTest n]
    have hx : ‖((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))‖
        = ‖S.pairInput u n‖ := Completion.norm_coe _
    have hsplit : T.completion ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))
        = (T.completion - K) ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))
          + K ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H)) := by
      simp
    rw [hsplit, inner_add_right]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ?_ ?_
    · refine (norm_inner_le_norm _ _).trans ?_
      rw [hw, one_mul]
      refine ((T.completion - K).le_opNorm _).trans ?_
      rw [hx]
    · refine (norm_inner_le_norm _ _).trans ?_
      rw [hw, one_mul]
  have hrhs : Tendsto (fun n => ‖T.completion - K‖ * ‖S.pairInput u n‖
      + ‖K ((S.pairInput u n : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))‖) atTop
      (𝓝 (‖T.completion - K‖ * 1 + 0)) := (hnorm1.const_mul _).add hKzero
  have hfinal := le_of_tendsto_of_tendsto hpairlim hrhs (Eventually.of_forall hupper)
  simpa using hfinal

end ShellDatum

end RHTower
