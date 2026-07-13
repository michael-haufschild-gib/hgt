/-
# The greedy spectral exhaustion of a positive compact self-adjoint operator

The eigenvalues of a positive compact self-adjoint operator `S`, in decreasing order with
multiplicity, are constructed greedily: `svVal S n` is the norm of `S` constrained to the
orthogonal complement of the previously chosen eigenvectors `svVec S 0, …, svVec S (n−1)`, and
`svVec S n` is a unit eigenvector realizing it (`0` once the constrained norm is exhausted).
Each step exists by the norm-attaining eigenvalue on the invariant orthogonal complement.

The two structural facts that make the sequence exhaust the spectrum:
* the values tend to zero — otherwise the unit eigenvectors form an orthonormal sequence whose
  images under `S` stay uniformly separated, contradicting compactness;
* a vector orthogonal to every `svVec S n` is annihilated by `S`, since `‖S x‖ ≤ svVal S n·‖x‖`
  for every `n`.

Proved here:
* `IsGreedyStep`, `svVec`, `svVal` — the greedy data.
* `svVec_zero_or_greedyStep`, `isGreedyStep_svVec` — each step is either exhausted or a genuine
  unit eigenvector for the constrained norm; under compactness, self-adjointness, and positivity
  the step is genuine whenever the constrained norm has not vanished.
* `apply_svVec` — `S (svVec S n) = svVal S n • svVec S n`, unconditionally.
* `inner_svVec_svVec_of_ne`, `svVal_nonneg`, `svVal_antitone`, `svVec_eq_zero_of_svVal_eq_zero`,
  `norm_apply_le_of_orth` — the order and orthogonality structure.
* `svVal_tendsto_zero` — the greedy values vanish at infinity.
* `apply_eq_zero_of_forall_inner_svVec` — completeness: `S` kills the joint orthogonal
  complement of the greedy family.
-/
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue

open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One admissible greedy step at stage `n`: a unit vector orthogonal to the first `n` members of
`v` on which `S` acts as multiplication by the constrained norm `orthSup S v n`. -/
def IsGreedyStep (S : H →L[ℂ] H) (v : ℕ → H) (n : ℕ) (x : H) : Prop :=
  ‖x‖ = 1 ∧ (∀ m < n, inner ℂ (v m) x = 0) ∧ S x = (orthSup S v n : ℂ) • x

omit [CompleteSpace H] in
/-- The constrained norm reads the family only below the stage. -/
theorem orthSup_congr (S : H →L[ℂ] H) {v w : ℕ → H} {n : ℕ} (h : ∀ m < n, v m = w m) :
    orthSup S v n = orthSup S w n := by
  unfold orthSup
  congr 1
  ext r
  constructor <;> rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
  · exact ⟨y, ⟨hy1, fun m hm => by rw [← h m hm]; exact hy2 m hm⟩, rfl⟩
  · exact ⟨y, ⟨hy1, fun m hm => by rw [h m hm]; exact hy2 m hm⟩, rfl⟩

open Classical in
/-- The greedy eigenvector sequence: at stage `n`, a unit eigenvector of `S` for the constrained
norm of the orthogonal complement of the previous stages — `0` once the constrained norm is
exhausted (or if no eigenvector exists, which cannot happen for positive compact self-adjoint
`S`). -/
noncomputable def svVec (S : H →L[ℂ] H) : ℕ → H
  | n =>
    if orthSup S (fun m => if _hm : m < n then svVec S m else 0) n = 0 then 0
    else if h : ∃ x : H, IsGreedyStep S (fun m => if _hm : m < n then svVec S m else 0) n x
    then h.choose else 0
termination_by n => n

/-- The greedy values: the constrained norms along the greedy sequence.  For `S = T†T` these are
the squared singular values of `T`, in decreasing order with multiplicity. -/
noncomputable def svVal (S : H →L[ℂ] H) (n : ℕ) : ℝ := orthSup S (svVec S) n

omit [CompleteSpace H] in
theorem svVal_eq_orthSup_prev (S : H →L[ℂ] H) (n : ℕ) :
    svVal S n = orthSup S (fun m => if _hm : m < n then svVec S m else 0) n :=
  orthSup_congr S fun m hm => by simp only [dif_pos hm]

omit [CompleteSpace H] in
/-- Transfer a greedy step stated for the guarded family to the full greedy family. -/
theorem isGreedyStep_of_prev {S : H →L[ℂ] H} {n : ℕ} {x : H}
    (h : IsGreedyStep S (fun m => if _hm : m < n then svVec S m else 0) n x) :
    IsGreedyStep S (svVec S) n x := by
  obtain ⟨hu, ho, he⟩ := h
  refine ⟨hu, fun m hm => ?_, ?_⟩
  · have h2 := ho m hm
    simp only [dif_pos hm] at h2
    exact h2
  · rw [show orthSup S (svVec S) n
      = orthSup S (fun m => if hm : m < n then svVec S m else 0) n
      from svVal_eq_orthSup_prev S n]
    exact he

omit [CompleteSpace H] in
/-- Each greedy stage is either exhausted (`svVec S n = 0`) or a genuine greedy step. -/
theorem svVec_zero_or_greedyStep (S : H →L[ℂ] H) (n : ℕ) :
    svVec S n = 0 ∨ IsGreedyStep S (svVec S) n (svVec S n) := by
  rw [svVec]
  split_ifs with h0 hex
  · exact Or.inl rfl
  · exact Or.inr (isGreedyStep_of_prev hex.choose_spec)
  · exact Or.inl rfl

omit [CompleteSpace H] in
/-- An exhausted stage emits the zero vector. -/
theorem svVec_eq_zero_of_svVal_eq_zero (S : H →L[ℂ] H) {n : ℕ} (h : svVal S n = 0) :
    svVec S n = 0 := by
  rw [svVec, if_pos]
  rw [← svVal_eq_orthSup_prev]
  exact h

omit [CompleteSpace H] in
/-- **The greedy eigen-equation**, unconditionally: `S (svVec S n) = svVal S n • svVec S n`. -/
theorem apply_svVec (S : H →L[ℂ] H) (n : ℕ) :
    S (svVec S n) = (svVal S n : ℂ) • svVec S n := by
  rcases svVec_zero_or_greedyStep S n with h | h
  · rw [h]
    simp
  · exact h.2.2

omit [CompleteSpace H] in
theorem inner_svVec_svVec_of_lt (S : H →L[ℂ] H) {m n : ℕ} (h : m < n) :
    inner ℂ (svVec S m) (svVec S n) = 0 := by
  rcases svVec_zero_or_greedyStep S n with h0 | hg
  · rw [h0]
    exact inner_zero_right _
  · exact hg.2.1 m h

omit [CompleteSpace H] in
theorem inner_svVec_svVec_of_ne (S : H →L[ℂ] H) {m n : ℕ} (h : m ≠ n) :
    inner ℂ (svVec S m) (svVec S n) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact inner_svVec_svVec_of_lt S hlt
  · rw [← inner_conj_symm, inner_svVec_svVec_of_lt S hgt, map_zero]

omit [CompleteSpace H] in
theorem svVal_nonneg (S : H →L[ℂ] H) (n : ℕ) : 0 ≤ svVal S n :=
  orthSup_nonneg S (svVec S) n

omit [CompleteSpace H] in
theorem svVal_antitone (S : H →L[ℂ] H) : Antitone (svVal S) :=
  orthSup_antitone S (svVec S)

omit [CompleteSpace H] in
/-- The constrained-norm bound along the greedy family. -/
theorem norm_apply_le_of_orth (S : H →L[ℂ] H) {x : H} (n : ℕ)
    (hx : ∀ m < n, inner ℂ (svVec S m) x = 0) : ‖S x‖ ≤ svVal S n * ‖x‖ :=
  norm_le_orthSup_mul_norm S (svVec S) n hx

/-- **A live greedy stage is a genuine greedy step.**  For positive compact self-adjoint `S`, if
the constrained norm has not vanished then the greedy vector is a unit eigenvector for it. -/
theorem isGreedyStep_svVec {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (hpos : ∀ x : H, 0 ≤ RCLike.re (inner ℂ x (S x)))
    (n : ℕ) (hne : svVal S n ≠ 0) : IsGreedyStep S (svVec S) n (svVec S n) := by
  have hne' : orthSup S (fun m => if hm : m < n then svVec S m else 0) n ≠ 0 := by
    rw [← svVal_eq_orthSup_prev]
    exact hne
  have hv : ∀ m < n, ∃ c : ℝ,
      S ((fun m => if hm : m < n then svVec S m else 0) m)
        = (c : ℂ) • (fun m => if hm : m < n then svVec S m else 0) m := by
    intro m hm
    simp only [dif_pos hm]
    exact ⟨svVal S m, apply_svVec S m⟩
  have hex : ∃ x : H, IsGreedyStep S (fun m => if hm : m < n then svVec S m else 0) n x := by
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      exists_eigenvector_orthSup hcpt hsym hpos
        (fun m => if hm : m < n then svVec S m else 0) n hv hne'
    exact ⟨x, hx1, hx2, hx3⟩
  have hval : svVec S n = hex.choose := by
    rw [svVec, if_neg hne', dif_pos hex]
  rw [hval]
  exact isGreedyStep_of_prev hex.choose_spec

/-- The unit norm of a live greedy vector. -/
theorem norm_svVec_of_ne_zero {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (hpos : ∀ x : H, 0 ≤ RCLike.re (inner ℂ x (S x)))
    {n : ℕ} (hne : svVal S n ≠ 0) : ‖svVec S n‖ = 1 :=
  (isGreedyStep_svVec hcpt hsym hpos n hne).1

/-- **The greedy values vanish at infinity.**  Otherwise the greedy vectors form an infinite
orthonormal family whose images under `S` are uniformly separated, and no subsequence of them can
converge — contradicting the compactness of `S`. -/
theorem svVal_tendsto_zero {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (hpos : ∀ x : H, 0 ≤ RCLike.re (inner ℂ x (S x))) :
    Filter.Tendsto (svVal S) Filter.atTop (nhds 0) := by
  have hant : Antitone (svVal S) := svVal_antitone S
  have hbdd : BddBelow (Set.range (svVal S)) := by
    refine ⟨0, ?_⟩
    rintro r ⟨n, rfl⟩
    exact svVal_nonneg S n
  have htend := tendsto_atTop_ciInf hant hbdd
  have hinf_nonneg : 0 ≤ ⨅ n, svVal S n := le_ciInf fun n => svVal_nonneg S n
  rcases eq_or_lt_of_le hinf_nonneg with h0 | hc
  · rwa [← h0] at htend
  · exfalso
    set c := ⨅ n, svVal S n with hc_def
    have hc_le : ∀ n, c ≤ svVal S n := fun n => ciInf_le hbdd n
    have hcne : ∀ n, svVal S n ≠ 0 := fun n => ne_of_gt (lt_of_lt_of_le hc (hc_le n))
    have hstep : ∀ n, IsGreedyStep S (svVec S) n (svVec S n) := fun n =>
      isGreedyStep_svVec hcpt hsym hpos n (hcne n)
    have hnorm_smul : ∀ n, ‖(svVal S n : ℂ) • svVec S n‖ ^ 2 = svVal S n ^ 2 := by
      intro n
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (svVal_nonneg S n), (hstep n).1, mul_one]
    have hsep : ∀ m n, m ≠ n → 2 * c ^ 2 ≤ ‖S (svVec S m) - S (svVec S n)‖ ^ 2 := by
      intro m n hmn
      rw [apply_svVec, apply_svVec]
      have hinner : RCLike.re
          (inner ℂ ((svVal S m : ℂ) • svVec S m) ((svVal S n : ℂ) • svVec S n)) = 0 := by
        rw [inner_smul_left, inner_smul_right, inner_svVec_svVec_of_ne S hmn]
        simp
      rw [norm_sub_sq (𝕜 := ℂ), hinner, hnorm_smul m, hnorm_smul n]
      have h1 : c ^ 2 ≤ svVal S m ^ 2 := by
        have := hc_le m
        nlinarith [svVal_nonneg S m, le_of_lt hc]
      have h2 : c ^ 2 ≤ svVal S n ^ 2 := by
        have := hc_le n
        nlinarith [svVal_nonneg S n, le_of_lt hc]
      nlinarith
    have hK : IsCompact (closure (⇑S '' Metric.closedBall 0 1)) :=
      (isCompactOperator_iff_isCompact_closure_image_closedBall
        (↑S : H →ₗ[ℂ] H) one_pos).mp hcpt
    have hmem : ∀ n, S (svVec S n) ∈ closure (⇑S '' Metric.closedBall 0 1) := by
      intro n
      refine subset_closure ⟨svVec S n, ?_, rfl⟩
      rw [mem_closedBall_zero_iff]
      exact le_of_eq (hstep n).1
    obtain ⟨a, -, φ, hφ, hconv⟩ := hK.isSeqCompact.subseq_of_frequently_in
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hmem))
    have hcauchy : CauchySeq (fun k => S (svVec S (φ k))) := hconv.cauchySeq
    rw [Metric.cauchySeq_iff] at hcauchy
    obtain ⟨N, hN⟩ := hcauchy c hc
    have h1 := hN (N + 1) (Nat.le_succ N) N le_rfl
    have hne_idx : φ (N + 1) ≠ φ N := Nat.ne_of_gt (hφ (Nat.lt_succ_self N))
    have hsep' := hsep (φ (N + 1)) (φ N) hne_idx
    rw [dist_eq_norm] at h1
    nlinarith [norm_nonneg (S (svVec S (φ (N + 1))) - S (svVec S (φ N)))]

/-- **Completeness of the greedy exhaustion.**  A vector orthogonal to every greedy vector is
annihilated by `S`: its image is bounded by every greedy value. -/
theorem apply_eq_zero_of_forall_inner_svVec {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (hpos : ∀ x : H, 0 ≤ RCLike.re (inner ℂ x (S x)))
    {x : H} (hx : ∀ n, inner ℂ (svVec S n) x = 0) : S x = 0 := by
  have hb : ∀ n, ‖S x‖ ≤ svVal S n * ‖x‖ := fun n =>
    norm_apply_le_of_orth S n fun m _ => hx m
  have hlim : Filter.Tendsto (fun n => svVal S n * ‖x‖) Filter.atTop (nhds 0) := by
    simpa using (svVal_tendsto_zero hcpt hsym hpos).mul_const ‖x‖
  have hle : ‖S x‖ ≤ 0 := ge_of_tendsto' hlim hb
  simpa using le_antisymm hle (norm_nonneg _)

end ContinuousLinearMap
