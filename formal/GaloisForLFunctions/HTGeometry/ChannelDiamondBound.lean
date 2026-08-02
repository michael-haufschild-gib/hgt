import GaloisForLFunctions.HTGeometry.KroneckerAmplification

/-!
# Completely bounded bounds for unitary channels

The completely bounded norm of a map of matrices is its operator norm after amplification by an
arbitrary ancilla; the diamond norm of a channel is the completely bounded norm of its adjoint, and
for a difference of unitary conjugations the two agree.  Since amplifying a conjugation conjugates
by the Kronecker product with the identity, and that product has the same norm bound, the
finite-horizon C⋆ estimate for a single ancilla-free observable already gives the completely
bounded estimate for all ancillas at once:

`½ ‖Ad_{exp(-itH)} - Ad_{exp(-itK)}‖_cb ≤ |t| ‖H - K‖`.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The matrix algebra is a C⋆-algebra for the operator norm. -/
local instance instCStarAlgebraMatrix : CStarAlgebra (Matrix d d ℂ) where

/-- A completely bounded bound: one constant which bounds every ancilla amplification. -/
def IsCbBound (Φ : Matrix d d ℂ → Matrix d d ℂ) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (X : Matrix (d × Fin n) (d × Fin n) ℂ), ‖amplify Φ (Fin n) X‖ ≤ c * ‖X‖

/-- The completely bounded norm: the least completely bounded bound. -/
def cbNorm (Φ : Matrix d d ℂ → Matrix d d ℂ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ IsCbBound Φ c}

theorem cbNorm_le_of_isCbBound {Φ : Matrix d d ℂ → Matrix d d ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : IsCbBound Φ c) : cbNorm Φ ≤ c :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hc, h⟩

theorem IsCbBound.mono {Φ : Matrix d d ℂ → Matrix d d ℂ} {c c' : ℝ} (h : IsCbBound Φ c)
    (hcc : c ≤ c') : IsCbBound Φ c' := by
  intro n X
  exact le_trans (h n X) (mul_le_mul_of_nonneg_right hcc (norm_nonneg X))

omit [Fintype d] [DecidableEq d] in
theorem amplify_sub (Φ Ψ : Matrix d d ℂ → Matrix d d ℂ) {n : Type*} [Fintype n]
    (X : Matrix (d × n) (d × n) ℂ) :
    amplify (fun O => Φ O - Ψ O) n X = amplify Φ n X - amplify Ψ n X := rfl

/-- **Completely bounded stability of unitary conjugation.**  The difference of two unitary
conjugations is completely bounded by twice the distance of the unitaries. -/
theorem isCbBound_conjugation_sub {U V : Matrix d d ℂ}
    (hU : U ∈ unitary (Matrix d d ℂ)) (hV : V ∈ unitary (Matrix d d ℂ)) :
    IsCbBound (fun O => U * O * star U - V * O * star V) (2 * ‖U - V‖) := by
  intro n X
  have hamp : amplify (fun O => U * O * star U - V * O * star V) (Fin n) X
      = (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * X * star (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        - (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * X
            * star (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [amplify_sub, amplify_conj, amplify_conj]
  have hUk := kronecker_one_mem_unitary (n := Fin n) hU
  have hVk := kronecker_one_mem_unitary (n := Fin n) hV
  have hbound := unitary_conjugation_norm_sub_le (A := Matrix (d × Fin n) (d × Fin n) ℂ)
    (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) X hUk hVk
  have hdiff : (U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) - (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
      = (U - V) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext p q
    show U p.1 q.1 * (1 : Matrix (Fin n) (Fin n) ℂ) p.2 q.2
        - V p.1 q.1 * (1 : Matrix (Fin n) (Fin n) ℂ) p.2 q.2
      = (U p.1 q.1 - V p.1 q.1) * (1 : Matrix (Fin n) (Fin n) ℂ) p.2 q.2
    ring
  have hnorm : ‖(U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
      - (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))‖ ≤ ‖U - V‖ := by
    rw [hdiff]
    exact l2_opNorm_kronecker_one_le _
  rw [hamp]
  refine le_trans hbound ?_
  have hstep : 2 * ‖(U ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
      - (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))‖ ≤ 2 * ‖U - V‖ := by
    linarith
  exact mul_le_mul_of_nonneg_right hstep (norm_nonneg X)

/-- **Finite-horizon completely bounded channel law.**  For self-adjoint generators the unitary
channels they generate differ, completely boundedly, by at most twice the elapsed time times the
distance of the generators. -/
theorem isCbBound_unitaryEvolution_sub (H K : Matrix d d ℂ) (hH : IsSelfAdjoint H)
    (hK : IsSelfAdjoint K) (t : ℝ) :
    IsCbBound (fun O =>
        NormedSpace.exp (t • ((-Complex.I) • H)) * O
            * star (NormedSpace.exp (t • ((-Complex.I) • H)))
          - NormedSpace.exp (t • ((-Complex.I) • K)) * O
            * star (NormedSpace.exp (t • ((-Complex.I) • K))))
      (2 * (|t| * ‖H - K‖)) := by
  letI : NormedAlgebra ℚ (Matrix d d ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (Matrix d d ℂ)
  have hbaseH : (-Complex.I) • H ∈ skewAdjoint (Matrix d d ℂ) := by
    rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]
    simp
  have hbaseK : (-Complex.I) • K ∈ skewAdjoint (Matrix d d ℂ) := by
    rw [skewAdjoint.mem_iff, star_smul, hK.star_eq]
    simp
  have hskewH : (t : ℝ) • ((-Complex.I) • H) ∈ skewAdjoint (Matrix d d ℂ) :=
    skewAdjoint.smul_mem t hbaseH
  have hskewK : (t : ℝ) • ((-Complex.I) • K) ∈ skewAdjoint (Matrix d d ℂ) :=
    skewAdjoint.smul_mem t hbaseK
  have hU : NormedSpace.exp (t • ((-Complex.I) • H)) ∈ unitary (Matrix d d ℂ) :=
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskewH
  have hV : NormedSpace.exp (t • ((-Complex.I) • K)) ∈ unitary (Matrix d d ℂ) :=
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskewK
  refine (isCbBound_conjugation_sub hU hV).mono ?_
  have hdist := selfAdjoint_unitaryEvolution_norm_sub_le (A := Matrix d d ℂ) H K hH hK t
  linarith

/-- **The diamond-norm form.**  Half the completely bounded distance of the two unitary channels is
at most the elapsed time times the distance of the generators. -/
theorem cbNorm_unitaryEvolution_sub_le (H K : Matrix d d ℂ) (hH : IsSelfAdjoint H)
    (hK : IsSelfAdjoint K) (t : ℝ) :
    (1 / 2 : ℝ) * cbNorm (fun O =>
        NormedSpace.exp (t • ((-Complex.I) • H)) * O
            * star (NormedSpace.exp (t • ((-Complex.I) • H)))
          - NormedSpace.exp (t • ((-Complex.I) • K)) * O
            * star (NormedSpace.exp (t • ((-Complex.I) • K)))) ≤ |t| * ‖H - K‖ := by
  have hpos : (0 : ℝ) ≤ 2 * (|t| * ‖H - K‖) := by positivity
  have hle := cbNorm_le_of_isCbBound hpos (isCbBound_unitaryEvolution_sub H K hH hK t)
  linarith

end

end GaloisForLFunctions.HTGeometry
