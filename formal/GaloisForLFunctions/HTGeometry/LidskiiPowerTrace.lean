/-
# Traces of operators diagonal on the signed greedy family

The signed greedy eigenvectors of a compact self-adjoint operator diagonalize far more than the
operator itself: any operator acting on them by scalars and killing their joint orthogonal
complement has its trace computed by the same Hilbert-basis extension.  Powers of the operator are
the case of interest, and give Lidskii's identity for every power trace at once.

Main results:
* `opTrace_eq_tsum_of_sgVec_diagonal` — **the trace of an operator diagonal on the greedy family**.
* `opTrace_pow_eq_tsum_sgVal_pow` — **Lidskii for power traces**: `tr(Sᵐ) = ∑ₙ λₙ(S)ᵐ`.
-/
import GaloisForLFunctions.HTGeometry.LidskiiSelfAdjoint

open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The trace of an operator diagonal on the signed greedy family.**  If `T` acts on the greedy
eigenvectors of a compact self-adjoint `S` by scalars supported where `S` is alive, and kills every
vector killed by `S`, then the trace of `T` is the sum of those scalars. -/
theorem opTrace_eq_tsum_of_sgVec_diagonal {S T : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) {μ : ℕ → ℂ}
    (hdiag : ∀ n, T (sgVec S n) = μ n • sgVec S n)
    (hsupp : ∀ n, sgVal S n = 0 → μ n = 0)
    (hkill : ∀ u : H, S u = 0 → T u = 0)
    {A B : H →L[ℂ] H} (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) (hT : T = A ∘L B) :
    opTrace T = ∑' n, μ n := by
  classical
  have hlive_unit : ∀ n, sgVal S n ≠ 0 → ‖sgVec S n‖ = 1 := by
    intro n hn
    rcases norm_sgVec_zero_or_one S n with h | h
    · exact absurd (sgVal_zero_of_dead h) hn
    · exact h
  have hdead : ∀ n, sgVal S n = 0 → sgVec S n = 0 := by
    intro n h0
    refine sgVec_eq_zero_of_orthSup_eq_zero S ?_
    rw [← abs_sgVal hcpt hsym n, h0, abs_zero]
  have hinj : ∀ {m n : ℕ}, sgVal S m ≠ 0 → sgVal S n ≠ 0 → sgVec S m = sgVec S n → m = n := by
    intro m n hm hn hmn
    by_contra hne
    have h0 := inner_sgVec_sgVec_of_ne S hne
    rw [hmn, inner_self_eq_norm_sq_to_K, hlive_unit n hn] at h0
    norm_num at h0
  have hmu_live : ∀ n, μ n ≠ 0 → sgVal S n ≠ 0 := fun n hn h0 => hn (hsupp n h0)
  have hval : ∀ n, sgVal S n ≠ 0 → inner ℂ (sgVec S n) (T (sgVec S n)) = μ n := by
    intro n hn
    rw [hdiag n, inner_smul_right, inner_self_eq_norm_sq_to_K, hlive_unit n hn]
    norm_num
  have hA_orth : Orthonormal ℂ
      (Subtype.val : (sgVec S '' {n | sgVal S n ≠ 0}) → H) := by
    rw [orthonormal_subtype_iff_ite]
    rintro u ⟨m, hm, rfl⟩ z ⟨n, hn, rfl⟩
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, hlive_unit m hm]
      norm_num
    · rw [if_neg fun h => hmn (hinj hm hn h), inner_sgVec_sgVec_of_ne S hmn]
  obtain ⟨w, b, hAw, hb⟩ := hA_orth.exists_hilbertBasis_extension
  have horthw : ∀ u ∈ w, ∀ z ∈ w, u ≠ z → inner ℂ u z = 0 := by
    have hw_orth : Orthonormal ℂ (Subtype.val : w → H) := hb ▸ b.orthonormal
    rw [orthonormal_subtype_iff_ite] at hw_orth
    intro u hu z hz huz
    have h2 := hw_orth u hu z hz
    rwa [if_neg huz] at h2
  have h1 : opTrace T = ∑' v : w, inner ℂ (v : H) (T (v : H)) := by
    rw [hT, opTrace_comp_eq_tsum_basis hA hB b]
    exact tsum_congr fun v => by rw [show b v = (v : H) from congrFun hb v, ← hT]
  rw [h1]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun p => ⟨sgVec S p.1, hAw ⟨p.1, ?_, rfl⟩⟩) ?_ ?_ ?_
  · exact hmu_live _ p.2
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ h
    exact Subtype.ext (hinj (hmu_live m hm) (hmu_live n hn) (congrArg Subtype.val h))
  · rintro ⟨u, hu⟩ hfu
    simp only [Function.mem_support, ne_eq] at hfu
    have huA : u ∈ sgVec S '' {n | sgVal S n ≠ 0} := by
      by_contra huA
      have horth_all : ∀ n, inner ℂ (sgVec S n) u = 0 := by
        intro n
        rcases eq_or_ne (sgVal S n) 0 with h0 | hne0
        · rw [hdead n h0]
          exact inner_zero_left _
        · have hmem : sgVec S n ∈ w := hAw ⟨n, hne0, rfl⟩
          refine horthw _ hmem _ hu fun h => huA ?_
          rw [← h]
          exact ⟨n, hne0, rfl⟩
      have hSu : S u = 0 := apply_eq_zero_of_forall_inner_sgVec hcpt hsym horth_all
      exact hfu (by rw [hkill u hSu, inner_zero_right])
    obtain ⟨n, hn, hun⟩ := huA
    have hmun : μ n ≠ 0 := by
      intro h0
      refine hfu ?_
      rw [← hun, hval n hn, h0]
    exact ⟨⟨n, hmun⟩, Subtype.ext hun⟩
  · rintro ⟨n, hn⟩
    exact hval n (hmu_live n hn)

/-- **Lidskii for power traces.**  Every power trace of a compact self-adjoint operator which is
trace class in that power is the corresponding power sum of its eigenvalues. -/
theorem opTrace_pow_eq_tsum_sgVal_pow {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) {m : ℕ} (hm : 0 < m) {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) (hS : S ^ m = A ∘L B) :
    opTrace (S ^ m) = ∑' n, ((sgVal S n : ℝ) : ℂ) ^ m := by
  have hpow : ∀ (j n : ℕ),
      (S ^ j) (sgVec S n) = (((sgVal S n : ℝ) : ℂ) ^ j) • sgVec S n := by
    intro j n
    induction j with
    | zero => simp
    | succ k ih =>
        have hstep : (S ^ (k + 1)) (sgVec S n) = (S ^ k) (S (sgVec S n)) := by
          rw [pow_succ]
          rfl
        rw [hstep, apply_sgVec, map_smul, ih, smul_smul, pow_succ]
        congr 1
        ring
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  refine opTrace_eq_tsum_of_sgVec_diagonal hcpt hsym (fun n => hpow (k + 1) n) ?_ ?_ hA hB hS
  · intro n h0
    rw [h0]
    simp
  · intro u hu
    have hstep : (S ^ (k + 1)) u = (S ^ k) (S u) := by
      rw [pow_succ]
      rfl
    rw [hstep, hu, map_zero]

end ContinuousLinearMap
