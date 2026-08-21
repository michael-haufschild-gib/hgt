import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The determinant of a degenerating block pencil

Proposition 5.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), produces a Hermitian family of period integrals of the shape

```text
M(L)_{ij} = a_{ij} L + b_{ij} + o(1),      a_{ij} = 0 whenever i ≤ k or j ≤ k,
```

with `B = (b_{ij})_{i,j ≤ k}` and `A = (a_{ij})_{i,j > k}` positive definite.  Proposition 5.2 then
reads off

```text
det M(L) = det B · det A · L^{m−k} + O(L^{m−k−1}).
```

The mechanism is a single column-scaling: dividing the last `m−k` rows by `L` turns the pencil into
a family converging to the block-triangular matrix `fromBlocks B C 0 A`, whose determinant is
`det B · det A`, while multiplying the determinant by `L^{−(m−k)}`.  No positivity is needed for
the asymptotic itself; positivity only guarantees that the leading coefficient does not vanish,
which is what the logarithmic form of the statement requires.
-/

open Filter Topology Matrix

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The degenerating pencil: a block matrix whose lower-right block grows linearly in `L`, the
other blocks staying bounded, perturbed by a family `E` tending to zero entrywise. -/
noncomputable def blockPencil (A : Matrix κ κ 𝕜) (B : Matrix ι ι 𝕜) (C : Matrix ι κ 𝕜)
    (D : Matrix κ ι 𝕜) (F : Matrix κ κ 𝕜) (E : ℝ → Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜) (L : ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜 :=
  Matrix.fromBlocks B C D (fun a b => (L : 𝕜) * A a b + F a b) + E L

/-- The scaling coefficients: leave the first block of rows alone, divide the second by `L`. -/
noncomputable def pencilScale (L : ℝ) : ι ⊕ κ → 𝕜 :=
  Sum.elim (fun _ => (1 : 𝕜)) (fun _ => ((L : 𝕜))⁻¹)

omit [DecidableEq ι] [DecidableEq κ] in
theorem prod_pencilScale (L : ℝ) :
    (∏ i, pencilScale (𝕜 := 𝕜) (ι := ι) (κ := κ) L i) = ((L : 𝕜))⁻¹ ^ Fintype.card κ := by
  rw [Fintype.prod_sum_type]
  simp [pencilScale]

theorem tendsto_ofReal_inv_atTop :
    Tendsto (fun L : ℝ => ((L : 𝕜))⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun L : ℝ => ((L⁻¹ : ℝ) : 𝕜)) atTop (𝓝 ((0 : ℝ) : 𝕜)) :=
    (RCLike.continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_inv_atTop_zero
  simpa [RCLike.ofReal_inv] using h

/-- **The leading asymptotic of the pencil determinant.**

`det M(L) / L^{#κ} → det B · det A` as `L → ∞`.  This is the determinant expansion behind
Proposition 5.2 of Dai–Yoshikawa. -/
theorem tendsto_det_blockPencil_div
    (A : Matrix κ κ 𝕜) (B : Matrix ι ι 𝕜) (C : Matrix ι κ 𝕜) (D : Matrix κ ι 𝕜)
    (F : Matrix κ κ 𝕜) (E : ℝ → Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜)
    (hE : ∀ i j, Tendsto (fun L => E L i j) atTop (𝓝 0)) :
    Tendsto (fun L : ℝ => (blockPencil A B C D F E L).det / (L : 𝕜) ^ Fintype.card κ)
      atTop (𝓝 (B.det * A.det)) := by
  set Q : ℝ → Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜 :=
    fun L => Matrix.of fun i j => pencilScale L i * blockPencil A B C D F E L i j with hQ
  set P : Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜 := Matrix.fromBlocks B C 0 A with hP
  have hdetQ : ∀ L : ℝ,
      (Q L).det = (blockPencil A B C D F E L).det / (L : 𝕜) ^ Fintype.card κ := by
    intro L
    rw [hQ]
    rw [Matrix.det_mul_column, prod_pencilScale, inv_pow, inv_mul_eq_div]
  have hinv := tendsto_ofReal_inv_atTop (𝕜 := 𝕜)
  have hQP : Tendsto Q atTop (𝓝 P) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    match i, j with
    | Sum.inl a, Sum.inl b =>
        have hval : ∀ L : ℝ, Q L (Sum.inl a) (Sum.inl b) = B a b + E L (Sum.inl a) (Sum.inl b) := by
          intro L; simp [hQ, blockPencil, pencilScale]
        have hlim : P (Sum.inl a) (Sum.inl b) = B a b := by simp [hP]
        simp only [hval, hlim]
        simpa using (tendsto_const_nhds (x := B a b) (f := atTop (α := ℝ))).add
          (hE (Sum.inl a) (Sum.inl b))
    | Sum.inl a, Sum.inr b =>
        have hval : ∀ L : ℝ, Q L (Sum.inl a) (Sum.inr b) = C a b + E L (Sum.inl a) (Sum.inr b) := by
          intro L; simp [hQ, blockPencil, pencilScale]
        have hlim : P (Sum.inl a) (Sum.inr b) = C a b := by simp [hP]
        simp only [hval, hlim]
        simpa using (tendsto_const_nhds (x := C a b) (f := atTop (α := ℝ))).add
          (hE (Sum.inl a) (Sum.inr b))
    | Sum.inr a, Sum.inl b =>
        have hval : ∀ L : ℝ, Q L (Sum.inr a) (Sum.inl b)
            = ((L : 𝕜))⁻¹ * (D a b + E L (Sum.inr a) (Sum.inl b)) := by
          intro L; simp [hQ, blockPencil, pencilScale]
        have hlim : P (Sum.inr a) (Sum.inl b) = 0 := by simp [hP]
        simp only [hval, hlim]
        simpa using hinv.mul ((tendsto_const_nhds (x := D a b) (f := atTop (α := ℝ))).add
          (hE (Sum.inr a) (Sum.inl b)))
    | Sum.inr a, Sum.inr b =>
        have hlim : P (Sum.inr a) (Sum.inr b) = A a b := by simp [hP]
        rw [hlim]
        have hg : Tendsto
            (fun L : ℝ => A a b + ((L : 𝕜))⁻¹ * (F a b + E L (Sum.inr a) (Sum.inr b)))
            atTop (𝓝 (A a b)) := by
          simpa using (tendsto_const_nhds (x := A a b) (f := atTop (α := ℝ))).add
            (hinv.mul ((tendsto_const_nhds (x := F a b) (f := atTop (α := ℝ))).add
              (hE (Sum.inr a) (Sum.inr b))))
        refine hg.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
        have hL0 : ((L : 𝕜)) ≠ 0 := by
          simpa using (RCLike.ofReal_ne_zero (K := 𝕜)).mpr (ne_of_gt hL)
        simp only [hQ, blockPencil, pencilScale, Matrix.of_apply, Sum.elim_inr,
          Matrix.add_apply, Matrix.fromBlocks_apply₂₂]
        field_simp
        ring
  have hdet : Tendsto (fun L : ℝ => (Q L).det) atTop (𝓝 P.det) :=
    (continuous_id'.matrix_det.tendsto P).comp hQP
  rw [hP, Matrix.det_fromBlocks_zero₂₁] at hdet
  exact hdet.congr fun L => hdetQ L

/-! ## The logarithmic form

Proposition 5.2 states the conclusion as `log det M(L) = (#κ) log L + γ₀ + o(1)`.  Over `ℝ` that is
the previous theorem read through the logarithm, valid as soon as the leading coefficient
`det B · det A` is positive — which for Dai–Yoshikawa is exactly the positive definiteness of `A`
and `B` proved in Proposition 5.1 (3). -/

/-- **Proposition 5.2 of Dai–Yoshikawa, logarithmic form.**

`log det M(L) − (#κ) log L → log (det B · det A)`. -/
theorem tendsto_log_det_blockPencil_sub
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) (B : Matrix ι ι ℝ) (C : Matrix ι κ ℝ) (D : Matrix κ ι ℝ)
    (F : Matrix κ κ ℝ) (E : ℝ → Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hE : ∀ i j, Tendsto (fun L => E L i j) atTop (𝓝 0))
    (hpos : 0 < B.det * A.det) :
    Tendsto (fun L : ℝ =>
        Real.log (blockPencil A B C D F E L).det
          - (Fintype.card κ : ℝ) * Real.log L) atTop (𝓝 (Real.log (B.det * A.det))) := by
  have hratio := tendsto_det_blockPencil_div (𝕜 := ℝ) A B C D F E hE
  have hlog : Tendsto
      (fun L : ℝ => Real.log ((blockPencil A B C D F E L).det / (L : ℝ) ^ Fintype.card κ))
      atTop (𝓝 (Real.log (B.det * A.det))) :=
    ((Real.continuousAt_log (ne_of_gt hpos)).tendsto).comp hratio
  refine hlog.congr' ?_
  have hev : ∀ᶠ L : ℝ in atTop,
      0 < (blockPencil A B C D F E L).det / (L : ℝ) ^ Fintype.card κ :=
    hratio.eventually (lt_mem_nhds hpos)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have hLpow : (0 : ℝ) < L ^ Fintype.card κ := pow_pos hL0 _
  have hdetpos : 0 < (blockPencil A B C D F E L).det := by
    have := (div_pos_iff).mp hL
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · exact absurd hLpow (not_lt.mpr h2.le)
  rw [Real.log_div (ne_of_gt hdetpos) (ne_of_gt hLpow), Real.log_pow]

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
