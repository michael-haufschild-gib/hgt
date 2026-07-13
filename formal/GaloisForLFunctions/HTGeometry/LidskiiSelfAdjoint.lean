/-
# Lidskii's theorem for self-adjoint trace-class operators

The signed greedy diagonalization: for a compact self-adjoint operator, the exhaustion by
norm-attaining eigenvectors proceeds exactly as in the positive case — the invariant-subspace
recursion degenerates to orthogonal complements — except that the eigenvalue realizing each
constrained norm carries a sign.  The signed greedy values `Re⟨eₙ, S eₙ⟩` are eigenvalues of `S`
in decreasing absolute value with multiplicity, every nonzero eigenvalue of `S` appears among
them, and `S` kills their joint orthogonal complement.  Computing the basis-independent trace of
a trace-class self-adjoint operator on a Hilbert-basis extension of the greedy family therefore
gives Lidskii's identity: the trace is the sum of the eigenvalues.

Proved here:
* `IsSignedStep`, `sgVec`, `sgVal` — the signed greedy data, with `apply_sgVec`
  (`S eₙ = sgVal n • eₙ` unconditionally), orthogonality, and `abs_sgVal`
  (`|sgVal n|` is the constrained norm).
* `sgOrthSup_tendsto_zero`, `apply_eq_zero_of_forall_inner_sgVec` — the exhaustion is complete.
* `exists_sgVal_eq_of_eigenvalue` — **no eigenvalue is missed**: every nonzero eigenvalue of a
  compact self-adjoint operator appears among the signed greedy values.
* `opTrace_eq_tsum_sgVal` — **Lidskii's theorem for self-adjoint trace-class operators**:
  `tr S = ∑ₙ λₙ(S)`, the trace is the sum of the eigenvalues.
-/
import GaloisForLFunctions.HTGeometry.GreedySingularValues
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One signed greedy step at stage `n`: a unit vector orthogonal to the previous stages, on
which `S` acts by a real scalar of absolute value the constrained norm. -/
def IsSignedStep (S : H →L[ℂ] H) (v : ℕ → H) (n : ℕ) (x : H) : Prop :=
  ‖x‖ = 1 ∧ (∀ m < n, inner ℂ (v m) x = 0) ∧
    ∃ c : ℝ, |c| = orthSup S v n ∧ S x = (c : ℂ) • x

open Classical in
/-- The signed greedy eigenvector sequence of a compact self-adjoint operator. -/
noncomputable def sgVec (S : H →L[ℂ] H) : ℕ → H
  | n =>
    if orthSup S (fun m => if _hm : m < n then sgVec S m else 0) n = 0 then 0
    else if h : ∃ x : H, IsSignedStep S (fun m => if _hm : m < n then sgVec S m else 0) n x
    then h.choose else 0
termination_by n => n

/-- The signed greedy eigenvalues: `Re⟨eₙ, S eₙ⟩`. -/
noncomputable def sgVal (S : H →L[ℂ] H) (n : ℕ) : ℝ :=
  RCLike.re (inner ℂ (sgVec S n) (S (sgVec S n)))

omit [CompleteSpace H] in
theorem sgOrthSup_eq_prev (S : H →L[ℂ] H) (n : ℕ) :
    orthSup S (sgVec S) n = orthSup S (fun m => if _hm : m < n then sgVec S m else 0) n :=
  orthSup_congr S fun m hm => by simp only [dif_pos hm]

omit [CompleteSpace H] in
theorem isSignedStep_of_prev {S : H →L[ℂ] H} {n : ℕ} {x : H}
    (h : IsSignedStep S (fun m => if _hm : m < n then sgVec S m else 0) n x) :
    IsSignedStep S (sgVec S) n x := by
  obtain ⟨hu, ho, c, hc, heq⟩ := h
  refine ⟨hu, fun m hm => ?_, c, ?_, heq⟩
  · have h2 := ho m hm
    simp only [dif_pos hm] at h2
    exact h2
  · rw [sgOrthSup_eq_prev]
    exact hc

omit [CompleteSpace H] in
theorem sgVec_zero_or_step (S : H →L[ℂ] H) (n : ℕ) :
    sgVec S n = 0 ∨ IsSignedStep S (sgVec S) n (sgVec S n) := by
  rw [sgVec]
  split_ifs with h0 hex
  · exact Or.inl rfl
  · exact Or.inr (isSignedStep_of_prev hex.choose_spec)
  · exact Or.inl rfl

omit [CompleteSpace H] in
theorem sgVec_eq_zero_of_orthSup_eq_zero (S : H →L[ℂ] H) {n : ℕ}
    (h : orthSup S (sgVec S) n = 0) : sgVec S n = 0 := by
  rw [sgVec, if_pos]
  rw [← sgOrthSup_eq_prev]
  exact h

omit [CompleteSpace H] in
theorem inner_sgVec_sgVec_of_lt (S : H →L[ℂ] H) {m n : ℕ} (h : m < n) :
    inner ℂ (sgVec S m) (sgVec S n) = 0 := by
  rcases sgVec_zero_or_step S n with h0 | hg
  · rw [h0]
    exact inner_zero_right _
  · exact hg.2.1 m h

omit [CompleteSpace H] in
theorem inner_sgVec_sgVec_of_ne (S : H →L[ℂ] H) {m n : ℕ} (h : m ≠ n) :
    inner ℂ (sgVec S m) (sgVec S n) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact inner_sgVec_sgVec_of_lt S hlt
  · rw [← inner_conj_symm, inner_sgVec_sgVec_of_lt S hgt, map_zero]

omit [CompleteSpace H] in
theorem sgVal_zero_of_dead {S : H →L[ℂ] H} {n : ℕ} (h : sgVec S n = 0) : sgVal S n = 0 := by
  rw [sgVal, h, inner_zero_left]
  simp

omit [CompleteSpace H] in
theorem sgVal_eq_of_step {S : H →L[ℂ] H} {n : ℕ}
    (h : IsSignedStep S (sgVec S) n (sgVec S n)) :
    ∃ c : ℝ, |c| = orthSup S (sgVec S) n
      ∧ S (sgVec S n) = (c : ℂ) • sgVec S n ∧ sgVal S n = c := by
  obtain ⟨hu, ho, c, hc, heq⟩ := h
  refine ⟨c, hc, heq, ?_⟩
  rw [sgVal, heq, inner_smul_right, RCLike.mul_re]
  have h1 : RCLike.im ((c : ℝ) : ℂ) = 0 := by simp
  have h2 : RCLike.re ((c : ℝ) : ℂ) = c := by simp
  rw [h1, h2, inner_self_eq_norm_sq, inner_self_im, hu]
  ring

omit [CompleteSpace H] in
/-- **The signed greedy eigen-equation**, unconditionally:
`S (sgVec S n) = sgVal S n • sgVec S n`. -/
theorem apply_sgVec (S : H →L[ℂ] H) (n : ℕ) :
    S (sgVec S n) = ((sgVal S n : ℝ) : ℂ) • sgVec S n := by
  rcases sgVec_zero_or_step S n with h | h
  · rw [h, map_zero, smul_zero]
  · obtain ⟨c, hc, heq, hval⟩ := sgVal_eq_of_step h
    rw [heq, hval]

omit [CompleteSpace H] in
theorem norm_sgVec_zero_or_one (S : H →L[ℂ] H) (n : ℕ) :
    sgVec S n = 0 ∨ ‖sgVec S n‖ = 1 := by
  rcases sgVec_zero_or_step S n with h | h
  · exact Or.inl h
  · exact Or.inr h.1

/-- A live signed stage is a genuine signed step. -/
theorem isSignedStep_sgVec {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (n : ℕ) (hne : orthSup S (sgVec S) n ≠ 0) :
    IsSignedStep S (sgVec S) n (sgVec S n) := by
  have hne' : orthSup S (fun m => if _hm : m < n then sgVec S m else 0) n ≠ 0 := by
    rw [← sgOrthSup_eq_prev]
    exact hne
  have hv : ∀ m < n, ∃ c : ℝ,
      S ((fun m => if _hm : m < n then sgVec S m else 0) m)
        = (c : ℂ) • (fun m => if _hm : m < n then sgVec S m else 0) m := by
    intro m hm
    simp only [dif_pos hm]
    exact ⟨sgVal S m, apply_sgVec S m⟩
  have hex : ∃ x : H, IsSignedStep S (fun m => if _hm : m < n then sgVec S m else 0) n x := by
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      exists_signed_eigenvector_orthSup hcpt hsym
        (fun m => if _hm : m < n then sgVec S m else 0) n hv hne'
    exact ⟨x, hx1, hx2, hx3⟩
  have hval : sgVec S n = hex.choose := by
    rw [sgVec, if_neg hne', dif_pos hex]
  rw [hval]
  exact isSignedStep_of_prev hex.choose_spec

/-- The absolute value of the signed greedy value is the constrained norm. -/
theorem abs_sgVal {S : H →L[ℂ] H} (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) (n : ℕ) :
    |sgVal S n| = orthSup S (sgVec S) n := by
  rcases eq_or_ne (orthSup S (sgVec S) n) 0 with h0 | hne
  · rw [sgVal_zero_of_dead (sgVec_eq_zero_of_orthSup_eq_zero S h0), h0, abs_zero]
  · obtain ⟨c, hc, heq, hval⟩ := sgVal_eq_of_step (isSignedStep_sgVec hcpt hsym n hne)
    rw [hval, hc]

/-- The constrained norms of the signed exhaustion vanish at infinity. -/
theorem sgOrthSup_tendsto_zero {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) :
    Filter.Tendsto (fun n => orthSup S (sgVec S) n) Filter.atTop (nhds 0) := by
  have hant : Antitone (fun n => orthSup S (sgVec S) n) := orthSup_antitone S (sgVec S)
  have hbdd : BddBelow (Set.range (fun n => orthSup S (sgVec S) n)) := by
    refine ⟨0, ?_⟩
    rintro r ⟨n, rfl⟩
    exact orthSup_nonneg S (sgVec S) n
  have htend := tendsto_atTop_ciInf hant hbdd
  have hinf_nonneg : 0 ≤ ⨅ n, orthSup S (sgVec S) n :=
    le_ciInf fun n => orthSup_nonneg S (sgVec S) n
  rcases eq_or_lt_of_le hinf_nonneg with h0 | hc
  · rwa [← h0] at htend
  · exfalso
    set c := ⨅ n, orthSup S (sgVec S) n with hc_def
    have hc_le : ∀ n, c ≤ orthSup S (sgVec S) n := fun n => ciInf_le hbdd n
    have hcne : ∀ n, orthSup S (sgVec S) n ≠ 0 := fun n =>
      ne_of_gt (lt_of_lt_of_le hc (hc_le n))
    have hstep : ∀ n, IsSignedStep S (sgVec S) n (sgVec S n) := fun n =>
      isSignedStep_sgVec hcpt hsym n (hcne n)
    have habs : ∀ n, |sgVal S n| = orthSup S (sgVec S) n := abs_sgVal hcpt hsym
    have hnorm_smul : ∀ n, ‖((sgVal S n : ℝ) : ℂ) • sgVec S n‖ ^ 2 = sgVal S n ^ 2 := by
      intro n
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, (hstep n).1, mul_one, sq_abs]
    have hsep : ∀ m n, m ≠ n → 2 * c ^ 2 ≤ ‖S (sgVec S m) - S (sgVec S n)‖ ^ 2 := by
      intro m n hmn
      rw [apply_sgVec, apply_sgVec]
      have hinner : RCLike.re
          (inner ℂ (((sgVal S m : ℝ) : ℂ) • sgVec S m)
            (((sgVal S n : ℝ) : ℂ) • sgVec S n)) = 0 := by
        rw [inner_smul_left, inner_smul_right, inner_sgVec_sgVec_of_ne S hmn]
        simp
      rw [norm_sub_sq (𝕜 := ℂ), hinner, hnorm_smul m, hnorm_smul n]
      have h1 : c ^ 2 ≤ sgVal S m ^ 2 := by
        have h2 := hc_le m
        rw [← habs m] at h2
        nlinarith [abs_nonneg (sgVal S m), le_of_lt hc, sq_abs (sgVal S m)]
      have h2 : c ^ 2 ≤ sgVal S n ^ 2 := by
        have h3 := hc_le n
        rw [← habs n] at h3
        nlinarith [abs_nonneg (sgVal S n), le_of_lt hc, sq_abs (sgVal S n)]
      nlinarith
    have hK : IsCompact (closure (⇑S '' Metric.closedBall 0 1)) :=
      (isCompactOperator_iff_isCompact_closure_image_closedBall
        (↑S : H →ₗ[ℂ] H) one_pos).mp hcpt
    have hmem : ∀ n, S (sgVec S n) ∈ closure (⇑S '' Metric.closedBall 0 1) := by
      intro n
      refine subset_closure ⟨sgVec S n, ?_, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact le_of_eq (hstep n).1
    obtain ⟨a, -, φ, hφ, hconv⟩ := hK.isSeqCompact.subseq_of_frequently_in
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hmem))
    have hcauchy : CauchySeq (fun k => S (sgVec S (φ k))) := hconv.cauchySeq
    rw [Metric.cauchySeq_iff] at hcauchy
    obtain ⟨N, hN⟩ := hcauchy c hc
    have h1 := hN (N + 1) (Nat.le_succ N) N le_rfl
    have hne_idx : φ (N + 1) ≠ φ N := Nat.ne_of_gt (hφ (Nat.lt_succ_self N))
    have hsep' := hsep (φ (N + 1)) (φ N) hne_idx
    rw [dist_eq_norm] at h1
    nlinarith [norm_nonneg (S (sgVec S (φ (N + 1))) - S (sgVec S (φ N)))]

/-- **Completeness of the signed exhaustion**: `S` kills the joint orthogonal complement. -/
theorem apply_eq_zero_of_forall_inner_sgVec {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) {x : H} (hx : ∀ n, inner ℂ (sgVec S n) x = 0) : S x = 0 := by
  have hb : ∀ n, ‖S x‖ ≤ orthSup S (sgVec S) n * ‖x‖ := fun n =>
    norm_le_orthSup_mul_norm S (sgVec S) n fun m _ => hx m
  have hlim : Filter.Tendsto (fun n => orthSup S (sgVec S) n * ‖x‖) Filter.atTop (nhds 0) := by
    simpa using (sgOrthSup_tendsto_zero hcpt hsym).mul_const ‖x‖
  have hle : ‖S x‖ ≤ 0 := ge_of_tendsto' hlim hb
  simpa using le_antisymm hle (norm_nonneg _)

/-- **No eigenvalue is missed**: every nonzero eigenvalue of a compact self-adjoint operator
appears among the signed greedy values. -/
theorem exists_sgVal_eq_of_eigenvalue {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) {c : ℂ} {v : H} (hv : v ≠ 0) (heig : S v = c • v) (hc : c ≠ 0) :
    ∃ n, ((sgVal S n : ℝ) : ℂ) = c := by
  by_contra hall
  push Not at hall
  have horth : ∀ n, inner ℂ (sgVec S n) v = 0 := by
    intro n
    have h1 : inner ℂ (sgVec S n) (S v) = c * inner ℂ (sgVec S n) v := by
      rw [heig, inner_smul_right]
    have h2 : inner ℂ (sgVec S n) (S v)
        = ((sgVal S n : ℝ) : ℂ) * inner ℂ (sgVec S n) v := by
      calc inner ℂ (sgVec S n) (S v)
          = inner ℂ (S (sgVec S n)) v := (hsym (sgVec S n) v).symm
        _ = inner ℂ (((sgVal S n : ℝ) : ℂ) • sgVec S n) v := by rw [apply_sgVec]
        _ = ((sgVal S n : ℝ) : ℂ) * inner ℂ (sgVec S n) v := by
            rw [inner_smul_left]
            congr 1
            simp
    have h3 : (c - ((sgVal S n : ℝ) : ℂ)) * inner ℂ (sgVec S n) v = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4).symm (hall n)
    · exact h4
  have hSv : S v = 0 := apply_eq_zero_of_forall_inner_sgVec hcpt hsym horth
  rw [heig] at hSv
  rcases smul_eq_zero.mp hSv with h | h
  · exact hc h
  · exact hv h

/-- **Lidskii's theorem for self-adjoint trace-class operators.**  The trace of a self-adjoint
operator that factors through Hilbert–Schmidt operators is the sum of its eigenvalues, in
decreasing absolute value with multiplicity: compute the basis-independent trace on a Hilbert
basis extending the signed greedy family, where the diagonal reads off the eigenvalues and the
complement is killed. -/
theorem opTrace_eq_tsum_sgVal {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) {A B : H →L[ℂ] H}
    (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt) (hS : S = A ∘L B) :
    opTrace S = ∑' n, ((sgVal S n : ℝ) : ℂ) := by
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
  have h1 : opTrace S = ∑' v : w, inner ℂ (v : H) (S (v : H)) := by
    rw [hS, opTrace_comp_eq_tsum_basis hA hB b]
    exact tsum_congr fun v => by rw [show b v = (v : H) from congrFun hb v, ← hS]
  rw [h1]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun p => ⟨sgVec S p.1, hAw ⟨p.1, ?_, rfl⟩⟩) ?_ ?_ ?_
  · have hp := p.2
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hp
    exact hp
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ h
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hm hn
    exact Subtype.ext (hinj hm hn (congrArg Subtype.val h))
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
      exact hfu (by rw [hSu, inner_zero_right])
    obtain ⟨n, hn, hun⟩ := huA
    refine ⟨⟨n, ?_⟩, Subtype.ext hun⟩
    simpa [Complex.ofReal_eq_zero] using hn
  · rintro ⟨n, hn⟩
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hn
    show inner ℂ (sgVec S n) (S (sgVec S n)) = ((sgVal S n : ℝ) : ℂ)
    rw [apply_sgVec, inner_smul_right, inner_self_eq_norm_sq_to_K, hlive_unit n hn]
    norm_num

end ContinuousLinearMap
