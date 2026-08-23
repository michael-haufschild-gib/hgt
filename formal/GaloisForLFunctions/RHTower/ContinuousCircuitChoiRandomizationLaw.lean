import GaloisForLFunctions.HTGeometry.ProjectiveSpectralCircuitHardIntervalLaw
import GaloisForLFunctions.RHTower.AutonomousReturnReflection

/-!
# Continuous-circuit Choi and randomization laws

Projective exclusion from the compact image of arbitrary continuous two-qubit
circuits automatically has one positive operational Choi-error margin.
Moreover, finite classical randomization over short unitary circuits cannot
improve their pure-Choi witness: weighted fidelity is bounded by the best
branch.  Thus the same error certificate applies to randomized simulation
algorithms, independently of their number of branches.
-/

open Matrix Set Topology
open scoped Matrix.Norms.L2Operator BigOperators NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-- **Unitary channels are projective unitaries.**  Two finite unitaries have
zero normalized Choi trace distance exactly when their matrices differ by one
unit-modulus global phase. -/
theorem choiDist_eq_zero_iff_exists_unitaryPhase
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {U V : Matrix n n ℂ}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    choiDist U V = 0 ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ V = c • U := by
  have hn : 0 < Fintype.card n := Fintype.card_pos
  have hUnorm : ‖choiVector U‖ = 1 := norm_choiVector_eq_one hn hU
  have hVnorm : ‖choiVector V‖ = 1 := norm_choiVector_eq_one hn hV
  constructor
  · intro hzero
    have hinnerLe : ‖inner ℂ (choiVector U) (choiVector V)‖ ≤ 1 := by
      simpa [hUnorm, hVnorm] using
        (norm_inner_le_norm (𝕜 := ℂ) (choiVector U) (choiVector V))
    have hdefNonneg : 0 ≤ 1 - ‖inner ℂ (choiVector U) (choiVector V)‖ ^ 2 := by
      nlinarith [norm_nonneg (inner ℂ (choiVector U) (choiVector V))]
    have hdefZero : 1 - ‖inner ℂ (choiVector U) (choiVector V)‖ ^ 2 = 0 := by
      exact (Real.sqrt_eq_zero hdefNonneg).mp hzero
    have hinner : ‖inner ℂ (choiVector U) (choiVector V)‖ = 1 := by
      nlinarith [norm_nonneg (inner ℂ (choiVector U) (choiVector V))]
    have hUne : choiVector U ≠ 0 := by
      apply norm_ne_zero_iff.mp
      simp [hUnorm]
    have hVne : choiVector V ≠ 0 := by
      apply norm_ne_zero_iff.mp
      simp [hVnorm]
    obtain ⟨c, hcne, hc⟩ :=
      (norm_inner_eq_norm_iff hUne hVne).mp (by simpa [hUnorm, hVnorm, hinner])
    have hcnorm : ‖c‖ = 1 := by
      rw [hc, norm_smul, hUnorm] at hVnorm
      simpa using hVnorm
    refine ⟨c, hcnorm, ?_⟩
    ext i j
    have hentry := congrArg
      (fun z : EuclideanSpace ℂ (n × n) => z (i, j)) hc
    change V i j / (Real.sqrt (Fintype.card n) : ℂ) =
      c * (U i j / (Real.sqrt (Fintype.card n) : ℂ)) at hentry
    have hsqrt : (Real.sqrt (Fintype.card n) : ℂ) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
    field_simp at hentry
    simpa [Matrix.smul_apply, smul_eq_mul] using hentry
  · rintro ⟨c, hc, rfl⟩
    have hchoi : choiVector (c • U) = c • choiVector U := by
      ext p
      simp [choiVector, smul_eq_mul, div_eq_mul_inv, mul_assoc]
    rw [choiDist, pureStateTraceDistance, hchoi, inner_smul_right,
      norm_mul, hc, one_mul, inner_self_eq_norm_sq_to_K, hUnorm]
    simp

/-- Choi distance from one fixed matrix varies continuously with the second
matrix on every nonempty finite carrier. -/
theorem continuous_choiDist_left
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (U : Matrix n n ℂ) : Continuous (fun V : Matrix n n ℂ => choiDist U V) := by
  have hn : 0 < Fintype.card n := Fintype.card_pos
  have hfEq : (fun V : Matrix n n ℂ => choiDist U V) = fun V => Real.sqrt
      (1 - (‖Matrix.trace (Uᴴ * V)‖ / Fintype.card n) ^ 2) := by
    funext V
    exact choiDist_eq hn U V
  rw [hfEq]
  fun_prop

/-- **Compact projective exclusion is operationally robust.**  If no
continuous two-qubit circuit in a gate budget agrees with `U` up to global
phase, then one positive normalized Choi trace distance excludes the whole
continuous circuit image. -/
theorem exists_positive_choiDist_of_projectiveCircuit_exclusion
    {n s : ℕ}
    {U : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hU : Uᴴ * U = 1)
    (hexclude : ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
      ∀ c : ℂ, ‖c‖ = 1 →
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≠ c • U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
      ε ≤ choiDist U
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
  let S := TwoQubitArchitecture.circuitMatrixImageAtMost n s
  let f : Matrix (Fin n → Bool) (Fin n → Bool) ℂ → ℝ := fun V => choiDist U V
  have hn : 0 < Fintype.card (Fin n → Bool) := Fintype.card_pos
  have hf : Continuous f := by
    have hfEq : f = fun V => Real.sqrt
        (1 - (‖Matrix.trace (Uᴴ * V)‖ /
          Fintype.card (Fin n → Bool)) ^ 2) := by
      funext V
      exact choiDist_eq hn U V
    rw [hfEq]
    fun_prop
  have hScompact : IsCompact S :=
    TwoQubitArchitecture.isCompact_circuitMatrixImageAtMost n s
  have hSne : S.Nonempty := by
    let A : TwoQubitArchitecture n 0 := ⟨Fin.elim0, fun r => Fin.elim0 r⟩
    refine ⟨(A.contraction Fin.elim0 :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ), ?_⟩
    change (A.contraction Fin.elim0 :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈
        TwoQubitArchitecture.circuitMatrixImageAtMost n s
    rw [TwoQubitArchitecture.circuitMatrixImageAtMost]
    refine ⟨A.contraction Fin.elim0, ?_, rfl⟩
    rw [TwoQubitArchitecture.circuitImageAtMost]
    simp only [Set.mem_iUnion]
    refine ⟨⟨0, Nat.zero_lt_succ s⟩, ?_⟩
    rw [TwoQubitArchitecture.circuitImageExact]
    simp only [Set.mem_iUnion, Set.mem_range]
    exact ⟨A, Fin.elim0, rfl⟩
  have hzero : (0 : ℝ) ∉ f '' S := by
    rintro ⟨V, hVS, hfVzero⟩
    have hVzero : choiDist U V = 0 := by simpa [f] using hfVzero
    obtain ⟨Vg, hVgS, rfl⟩ := hVS
    obtain ⟨C, hCs, hCeval⟩ :=
      TwoQubitArchitecture.mem_circuitImageAtMost_iff.mp hVgS
    have hVunit :
        ((Vg : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)ᴴ *
          (Vg : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) = 1 := Vg.2.1
    obtain ⟨c, hc, hphase⟩ :=
      (choiDist_eq_zero_iff_exists_unitaryPhase hU hVunit).mp hVzero
    apply hexclude C hCs c hc
    simpa [hCeval] using hphase
  let ε := Metric.infDist 0 (f '' S)
  have hε : 0 < ε :=
    (((hScompact.image hf).isClosed.notMem_iff_infDist_pos (hSne.image f)).mp hzero)
  refine ⟨ε, hε, ?_⟩
  intro C hCs
  have hCmem : (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ S := by
    change (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈
      TwoQubitArchitecture.circuitMatrixImageAtMost n s
    rw [TwoQubitArchitecture.circuitMatrixImageAtMost]
    refine ⟨C.eval, ?_, rfl⟩
    exact TwoQubitArchitecture.mem_circuitImageAtMost_iff.mpr ⟨C, hCs, rfl⟩
  have hinf := Metric.infDist_le_dist_of_mem (x := (0 : ℝ))
    (show f (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ f '' S from
      ⟨_, hCmem, rfl⟩)
  simpa [ε, f, Real.dist_eq, abs_of_nonneg (choiDist_nonneg U _)] using hinf

/-- **Finite randomization cannot beat the best branch on a pure Choi
witness.**  A common Choi-distance floor for unitary branches gives the same
squared-fidelity deficit for every probability mixture, independent of its
support size. -/
theorem randomizedChoiFidelity_le_of_choiDist_floor
    {q C : Type*} [Fintype q] [DecidableEq q] [Nonempty q]
    [Fintype C]
    {U : Matrix q q ℂ} (hU : Uᴴ * U = 1)
    (V : C → Matrix.unitaryGroup q ℂ)
    (weight : C → ℝ≥0) (hweight : ∑ i, weight i = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : ∀ i, ε ≤ choiDist U (V i : Matrix q q ℂ)) :
    (∑ i, (weight i : ℝ) *
      ‖inner ℂ (choiVector U) (choiVector (V i : Matrix q q ℂ))‖ ^ 2) ≤
        1 - ε ^ 2 := by
  have hn : 0 < Fintype.card q := Fintype.card_pos
  have hUnorm : ‖choiVector U‖ = 1 := norm_choiVector_eq_one hn hU
  have hterm : ∀ i,
      ‖inner ℂ (choiVector U) (choiVector (V i : Matrix q q ℂ))‖ ^ 2 ≤
        1 - ε ^ 2 := by
    intro i
    have hVnorm : ‖choiVector (V i : Matrix q q ℂ)‖ = 1 :=
      norm_choiVector_eq_one hn (V i).2.1
    have hinnerLe :
        ‖inner ℂ (choiVector U) (choiVector (V i : Matrix q q ℂ))‖ ≤ 1 := by
      simpa [hUnorm, hVnorm] using
        (norm_inner_le_norm (𝕜 := ℂ) (choiVector U)
          (choiVector (V i : Matrix q q ℂ)))
    have hdef : 0 ≤ 1 -
        ‖inner ℂ (choiVector U) (choiVector (V i : Matrix q q ℂ))‖ ^ 2 := by
      nlinarith [norm_nonneg
        (inner ℂ (choiVector U) (choiVector (V i : Matrix q q ℂ)))]
    have hdistsq : choiDist U (V i : Matrix q q ℂ) ^ 2 =
        1 - ‖inner ℂ (choiVector U)
          (choiVector (V i : Matrix q q ℂ))‖ ^ 2 := by
      rw [choiDist, pureStateTraceDistance, Real.sq_sqrt hdef]
    have hsq : ε ^ 2 ≤ choiDist U (V i : Matrix q q ℂ) ^ 2 := by
      exact (sq_le_sq₀ hε (choiDist_nonneg U _)).2 (hsep i)
    rw [hdistsq] at hsq
    linarith
  calc
    (∑ i, (weight i : ℝ) *
        ‖inner ℂ (choiVector U) (choiVector (V i : Matrix q q ℂ))‖ ^ 2) ≤
        ∑ i, (weight i : ℝ) * (1 - ε ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hterm i) (NNReal.coe_nonneg _)
    _ = (∑ i, (weight i : ℝ)) * (1 - ε ^ 2) := by
      rw [Finset.sum_mul]
    _ = 1 - ε ^ 2 := by
      have hwReal : (∑ i, (weight i : ℝ)) = 1 := by exact_mod_cast hweight
      rw [hwReal, one_mul]

end
end GaloisForLFunctions.RHTower
