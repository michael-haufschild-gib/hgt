import GaloisForLFunctions.HTGeometry.InjectiveDenseRangePolarUnitary
import GaloisForLFunctions.HTGeometry.CompactRieszProjectionTrace
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.RHTower.TraceNorm
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect

/-!
# Pure trace-one densities

A positive trace-class operator `T` with `Tr T = 1` satisfies `Tr T² ≤ 1`, with equality exactly
for the pure states `|e⟩⟨e|`, `‖e‖ = 1`.  Indeed `‖T‖ ≤ ‖T‖₁ = 1`, so `‖Tx‖² ≤ ⟨x, Tx⟩` and
`T - T²` is positive; if `Tr T² = 1` its trace vanishes, hence `T = T²` is a compact orthogonal
projection, of finite rank equal to its trace `1`.
-/

open Filter Topology
open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For positive `T`, `‖T x‖² ≤ ‖T‖ Re⟨x, T x⟩`. -/
theorem norm_apply_sq_le_of_isPositive {T : H →L[ℂ] H} (hT : T.IsPositive) (x : H) :
    ‖T x‖ ^ 2 ≤ ‖T‖ * RCLike.re ⟪x, T x⟫_ℂ := by
  have hT0 : 0 ≤ T := (nonneg_iff_isPositive T).2 hT
  set R := CFC.sqrt T
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg T
  have hRpos : R.IsPositive := (nonneg_iff_isPositive R).1 hR0
  have hRR : R ∘L R = T := CFC.sqrt_mul_sqrt_self T hT0
  have hRsa : adjoint R = R := hRpos.isSelfAdjoint.adjoint_eq
  have hRnorm : ‖R‖ ^ 2 = ‖T‖ := by
    rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self R, hRsa, hRR]
  have hRx : ‖R x‖ ^ 2 = RCLike.re ⟪x, T x⟫_ℂ := by
    rw [← hRR, comp_apply, ← adjoint_inner_left R, hRsa, inner_self_eq_norm_sq]
  calc ‖T x‖ ^ 2 = ‖R (R x)‖ ^ 2 := by rw [← comp_apply, hRR]
    _ ≤ (‖R‖ * ‖R x‖) ^ 2 := by
        gcongr
        exact le_opNorm R (R x)
    _ = ‖T‖ * RCLike.re ⟪x, T x⟫_ℂ := by rw [mul_pow, hRnorm, hRx]

theorem norm_le_one_of_opTrace_eq_one {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hS : MemSchattenClass 1 T) (htr : opTrace T = 1) : ‖T‖ ≤ 1 := by
  have h := norm_le_traceNorm_of_memSchattenClass_one hS
  rwa [traceNorm_eq_re_opTrace_of_isPositive hS hT, htr, Complex.one_re] at h

/-- A positive trace-class operator of trace zero vanishes. -/
theorem eq_zero_of_isPositive_of_opTrace_eq_zero {S : H →L[ℂ] H} (hS : S.IsPositive)
    (hmem : MemSchattenClass 1 S) (htr : opTrace S = 0) : S = 0 := by
  have h := norm_le_traceNorm_of_memSchattenClass_one hmem
  rw [traceNorm_eq_re_opTrace_of_isPositive hmem hS, htr, Complex.zero_re] at h
  exact norm_le_zero_iff.1 h

/-- **Purity.**  A positive trace-one density with `Tr T² = 1` is a pure state `|e⟩⟨e|`. -/
theorem exists_eq_rankOne_of_opTrace_sq_eq_one {T : H →L[ℂ] H} (hT : T.IsPositive)
    (hS : MemSchattenClass 1 T) (htr : opTrace T = 1) (hsq : opTrace (T ∘L T) = 1) :
    ∃ e : H, ‖e‖ = 1 ∧ T = rankOne ℂ e e := by
  have hnorm := norm_le_one_of_opTrace_eq_one hT hS htr
  have hsa : adjoint T = T := hT.isSelfAdjoint.adjoint_eq
  -- `T - T²` is positive
  have hdiffpos : (T - T ∘L T).IsPositive := by
    refine ⟨?_, fun x => ?_⟩
    · have : IsSelfAdjoint (T - T ∘L T) := by
        rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub, adjoint_comp, hsa]
      exact this.isSymmetric
    · rw [ContinuousLinearMap.reApplyInnerSelf, sub_apply, inner_sub_left, map_sub, comp_apply]
      have h1 : RCLike.re ⟪T (T x), x⟫_ℂ = ‖T x‖ ^ 2 := by
        rw [← adjoint_inner_right, hsa, inner_self_eq_norm_sq]
      have h2 : RCLike.re ⟪T x, x⟫_ℂ = RCLike.re ⟪x, T x⟫_ℂ := by
        rw [← adjoint_inner_left, hsa]
      rw [h1, h2]
      have h3 := norm_apply_sq_le_of_isPositive hT x
      have h4 : 0 ≤ RCLike.re ⟪x, T x⟫_ℂ := by
        rw [← h2, ← ContinuousLinearMap.reApplyInnerSelf]
        exact hT.2 x
      nlinarith
  have hmemsq : MemSchattenClass 1 (T ∘L T) := memSchattenClass_one_comp_left hS T
  have hmemdiff : MemSchattenClass 1 (T - T ∘L T) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (T ∘L T)]
    exact memSchattenClass_one_add (hS.isCompactOperator one_pos)
      ((memSchattenClass_one_smul hmemsq _).isCompactOperator one_pos) hS
      (memSchattenClass_one_smul hmemsq _)
  have hidem : T ∘L T = T := by
    have h0 := eq_zero_of_isPositive_of_opTrace_eq_zero hdiffpos hmemdiff (by
      rw [opTrace_sub_of_memSchattenClass_one hS hmemsq, htr, hsq, sub_self])
    exact (sub_eq_zero.1 h0).symm
  -- the range is finite-dimensional and is a one-dimensional orthogonal projection
  set V := LinearMap.range (T : H →ₗ[ℂ] H)
  have hidem' : IsIdempotentElem T := by
    rw [IsIdempotentElem, ContinuousLinearMap.mul_def, hidem]
  haveI : FiniteDimensional ℂ V :=
    finiteDimensional_range_of_isCompactOperator_of_isIdempotentElem
      (hS.isCompactOperator one_pos) hidem'
  set b := stdOrthonormalBasis ℂ V
  have hfix : ∀ v ∈ V, T v = v := by
    rintro _ ⟨y, rfl⟩
    exact congrArg (fun A : H →L[ℂ] H => A y) hidem
  have hexpand : ∀ x, T x = ∑ i, ⟪(b i : H), x⟫_ℂ • (b i : H) := by
    intro x
    have hTx : T x ∈ V := ⟨x, rfl⟩
    have hcoord : T x = ∑ i, ⟪(b i : H), T x⟫_ℂ • (b i : H) := by
      have h := b.sum_repr' ⟨T x, hTx⟩
      have := congrArg Subtype.val h
      simpa using this.symm
    rw [hcoord]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← adjoint_inner_left T, hsa, hfix _ (b i).2]
  have hTsum : T = ∑ i, rankOne ℂ (b i : H) (b i : H) := by
    refine ContinuousLinearMap.ext fun x => ?_
    rw [hexpand]
    simp [rankOne_apply]
  have hnb : ∀ a, ‖(b a : H)‖ = 1 := fun a => (Submodule.coe_norm (b a)).trans (b.orthonormal.1 a)
  have hrk : ∀ a, MemSchattenClass 1 (rankOne ℂ (b a : H) (b a : H)) := fun a =>
    memSchattenClass_of_hasRankLE one_pos (by
      have h := hasRankLE_sum_range_rankOne (fun _ : ℕ => (b a : H)) (fun _ => (b a : H)) 1
      rwa [Finset.sum_range_one] at h)
  have hadd : ∀ s : Finset (Fin (Module.finrank ℂ V)),
      MemSchattenClass 1 (∑ i ∈ s, rankOne ℂ (b i : H) (b i : H)) ∧
        opTrace (∑ i ∈ s, rankOne ℂ (b i : H) (b i : H)) = (s.card : ℂ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, by simp [opTrace]⟩
      have h := hasRankLE_sum_range_rankOne (fun _ : ℕ => (0 : H)) (fun _ => (0 : H)) 0
      rw [Finset.sum_range_zero] at h
      rw [Finset.sum_empty]
      exact memSchattenClass_of_hasRankLE one_pos h
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine ⟨memSchattenClass_one_add ((hrk a).isCompactOperator one_pos)
        (ih.1.isCompactOperator one_pos) (hrk a) ih.1, ?_⟩
      rw [opTrace_add_of_memSchattenClass_one (hrk a) ih.1, ih.2, opTrace_rankOne,
        inner_self_eq_norm_sq_to_K, hnb a, Finset.card_insert_of_notMem ha]
      push_cast
      ring
  have htrace : opTrace T = (Module.finrank ℂ V : ℂ) := by
    rw [hTsum, (hadd Finset.univ).2, Finset.card_univ, Fintype.card_fin]
  rw [htr] at htrace
  have hd : Module.finrank ℂ V = 1 := by exact_mod_cast htrace.symm
  have hcard : Fintype.card (Fin (Module.finrank ℂ V)) = 1 := by simp [hd]
  obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.1 hcard
  refine ⟨(b i₀ : H), hnb i₀, ?_⟩
  rw [hTsum, Fintype.sum_eq_single i₀ (fun i hi => absurd (hi₀ i) hi)]

end GaloisForLFunctions.HTGeometry
