import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedDiagonalSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedChartDenominators

/-! Homogenizing the differences of finite chart generators gives
equations regular on all normalized chart pairs. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

variable (h : IsPd k x)

/-- Homogeneous equations that specialize to zero on the diagonal
and include the differences of a generating set on every chart. -/
structure NormalizedDiagonalEquations {κ : Type} [LinearOrder κ]
    (n : κ → ℕ × ℕ) (z : κ → E ⊗[k] E) : Prop where
  admitted : (normalizedDiagonalSystem (E := E) h 0 0).Admitted n z
  vanishes : ∀ l, Algebra.TensorProduct.lmul' k (z l) = 0
  generates : ∀ i, Algebra.adjoin k {b : E | b ∈ rB k E x {i} ∧
    ∃ l N, n l = (N, N) ∧
      z l = (((normalizedDiagonalSystem (E := E) h 0 0).X i ^ N *
        (normalizedDiagonalSystem (E := E) h 0 0).Y i ^ N : (E ⊗[k] E)ˣ) : E ⊗[k] E) *
          (b ⊗ₜ[k] (1 : E) - (1 : E) ⊗ₜ[k] b)} = rB k E x {i}

private theorem tensor_generator_eq (a u v b : E) (hu : u ≠ 0) (hv : v ≠ 0) (N : ℕ) :
    ((a ^ N) ⊗ₜ[k] (a ^ N)) * (b ⊗ₜ[k] (1 : E) - (1 : E) ⊗ₜ[k] b) =
      ((((a / u) ^ N * b) ⊗ₜ[k] ((a / v) ^ N)) -
        (((a / u) ^ N) ⊗ₜ[k] ((a / v) ^ N * b))) * ((u ^ N) ⊗ₜ[k] (v ^ N)) := by
  have h₁ : (a / u) ^ N * u ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a hu]
  have h₂ : (a / v) ^ N * v ^ N = a ^ N := by rw [← mul_pow, div_mul_cancel₀ a hv]
  have h₃ : (a / u) ^ N * b * u ^ N = a ^ N * b := by rw [mul_right_comm, h₁]
  have h₄ : (a / v) ^ N * b * v ^ N = a ^ N * b := by rw [mul_right_comm, h₂]
  simp only [sub_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h₁, h₂, h₃, h₄]

private theorem normalizedDiagonalSystem_XY_pow (i j : Fin (d + 1)) (N : ℕ) :
    let T := normalizedDiagonalSystem (E := E) h 0 0
    ((T.X i ^ N * T.Y j ^ N : (E ⊗[k] E)ˣ) : E ⊗[k] E) =
      ((algebraMap F E (x i) ^ N) ⊗ₜ[k] (algebraMap F E (x j) ^ N)) := by
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, normalizedDiagonalSystem_X,
    normalizedDiagonalSystem_Y, Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Finite homogeneous equations for the function-field diagonal
come from finite generators of the smooth affine charts. -/
theorem IsFinCover.exists_normalizedDiagonalEquations (H : IsFinCover k E x) :
    ∃ m : ℕ, ∃ (n : Fin m → ℕ × ℕ) (z : Fin m → E ⊗[k] E),
      NormalizedDiagonalEquations H.pd n z := by
  classical
  have hex (i : Fin (d + 1)) : ∃ G : Finset E, Algebra.adjoin k (G : Set E) = rB k E x {i} := by
    letI := H.smooth i
    exact (Subalgebra.fg_iff_finiteType _).mpr inferInstance
  choose G hG using hex
  let P := Finset.univ.biUnion (fun i => (G i).image (fun b => (i, b)))
  have hp {i : Fin (d + 1)} {b : E} : (i, b) ∈ P ↔ b ∈ G i := by
    simp [P]
  have hreg (a : P) : a.1.2 ∈ rB k E x {a.1.1} :=
    hG a.1.1 ▸ Algebra.subset_adjoin (hp.mp a.property)
  choose N hN using fun a : P => H.pd.exists_uniform_pow_mul_mem_rB a.1.1 a.1.2 (hreg a)
  let e := P.equivFin.symm
  let T := normalizedDiagonalSystem (E := E) H.pd 0 0
  let f (a : P) : E ⊗[k] E :=
    ((T.X a.1.1 ^ N a * T.Y a.1.1 ^ N a : (E ⊗[k] E)ˣ) : E ⊗[k] E) *
      (a.1.2 ⊗ₜ[k] (1 : E) - (1 : E) ⊗ₜ[k] a.1.2)
  refine ⟨P.card, fun l => (N (e l), N (e l)), fun l => f (e l), ?_, ?_, ?_⟩
  · intro i j l
    let a := e l
    let U := T.X i ^ N a * T.Y j ^ N a
    have hf : f a =
        ((((algebraMap F E (x a.1.1 / x i) ^ N a) * a.1.2) ⊗ₜ[k]
          (algebraMap F E (x a.1.1 / x j) ^ N a)) -
          ((algebraMap F E (x a.1.1 / x i) ^ N a) ⊗ₜ[k]
            ((algebraMap F E (x a.1.1 / x j) ^ N a) * a.1.2))) * (U : E ⊗[k] E) := by
      dsimp only [f, U, T]
      rw [normalizedDiagonalSystem_XY_pow, normalizedDiagonalSystem_XY_pow]
      simp only [map_div₀]
      exact tensor_generator_eq (algebraMap F E (x a.1.1)) _ _ a.1.2
        ((map_ne_zero _).mpr (H.pd.ne i)) ((map_ne_zero _).mpr (H.pd.ne j)) (N a)
    change f a * (U⁻¹ : (E ⊗[k] E)ˣ) ∈ tensorChartRing (rB k E x {i}) (rB k E x {j})
    rw [hf, mul_assoc, Units.mul_inv, mul_one]
    exact sub_mem
      (tmul_mem_tensorChartRing (hN a i)
        (pow_mem (chartRatio_mem_rB (k := k) (Finset.mem_singleton_self j) a.1.1) _))
      (tmul_mem_tensorChartRing
        (pow_mem (chartRatio_mem_rB (k := k) (Finset.mem_singleton_self i) a.1.1) _) (hN a j))
  · intro l
    simp only [f, map_mul, map_sub, Algebra.TensorProduct.lmul'_apply_tmul, mul_one,
      one_mul, sub_self, mul_zero]
  · intro i
    refine le_antisymm (Algebra.adjoin_le fun b hb => hb.1) ?_
    refine le_trans (le_of_eq (hG i).symm) (Algebra.adjoin_mono ?_)
    intro b hb
    let a : P := ⟨(i, b), hp.mpr hb⟩
    refine ⟨hreg a, e.symm a, N a, ?_, ?_⟩
    · rw [Equiv.apply_symm_apply]
    · simp only [Equiv.apply_symm_apply]
      rfl

end GlobalTheory.PD
