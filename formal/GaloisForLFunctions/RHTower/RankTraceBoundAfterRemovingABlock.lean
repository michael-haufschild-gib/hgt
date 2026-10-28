import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.VonNeumann
import Mathlib.Algebra.Order.Chebyshev

/-!
# The rank–trace bound after removing a block of bounded dimension

Let `G` be Hermitian and `G = P + Q`, where `rank P ≤ r` and the range of `Q` lies in a subspace
of dimension at most `k`. Write `λ₀ ≥ λ₁ ≥ …` for the eigenvalues of `G`. Then

  `tr G − (λ₀ + ⋯ + λ_{k−1}) ≤ √(r · ‖G‖²_F)`,

and, when the left side is nonnegative, `(tr G − Σ_{i<k} λᵢ)² ≤ r · ‖G‖²_F`
(`rtrace_sub_topEigenvalueSum_le`, `sq_rtrace_sub_topEigenvalueSum_le`).

For the zero Gram matrices of the inertia method, `P` collects critical zeros and `Q` the
indefinite blocks of `p` off-line pairs, so `k = 2p`. Each off-line pair then costs at most two
top eigenvalues of `G`, instead of entering through the positive index of `Q`. No sign of `P` is
used.

Proof. Enlarge the subspace to an orthogonal projection `E` of rank exactly `k`
(`exists_projection_rank_eq_of_rank_le`) and compress by `F = 1 − E`. Since `F Q = 0`,
`F G F = F P F` has rank at most `r`.
* Ky Fan (`re_trace_mul_projection_le`, from von Neumann's trace inequality) gives
  `tr(F G F) = tr G − tr(G E) ≥ tr G − Σ_{i<k} λᵢ`.
* Cauchy–Schwarz on eigenvalues gives `(tr A)² ≤ rank A · ‖A‖²_F` for Hermitian `A`
  (`sq_rtrace_le_rank_mul_frobSq`).
* Compression does not increase the Frobenius norm (`frobSq_compression_le`).

The nonnegativity hypothesis in the squared form cannot be dropped. For `G = Q = diag(−5, 0)`,
`P = 0`, `k = 1` the left side is `−5`, whose square exceeds `r · ‖G‖²_F = 0`.
-/

open Matrix Finset

noncomputable section

namespace RHTower

open RiemannGaussian.HermitianRankTrace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The sum `λ₀ + ⋯ + λ_{k−1}` of the `k` largest eigenvalues of a Hermitian matrix (all of
them when `k` exceeds the size). -/
def topEigenvalueSum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Fin (Fintype.card n) => (i : ℕ) < k), hA.eigenvalues₀ i

theorem topEigenvalueSum_of_card_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : Fintype.card n ≤ k) : topEigenvalueSum hA k = rtrace A := by
  rw [topEigenvalueSum, filter_true_of_mem fun i _ => lt_of_lt_of_le i.2 hk,
    rtrace_eq_sum_eigenvalues hA]
  exact (sum_eigenvalues_reindex hA fun x => x).symm

/-! ### Frobenius norm -/

omit [DecidableEq n] in
theorem frobSq_nonneg' (A : Matrix n n 𝕜) : 0 ≤ frobSq A := by
  rw [frobSq, trace, map_sum]
  refine sum_nonneg fun i _ => ?_
  rw [diag_apply, mul_apply, map_sum]
  refine sum_nonneg fun j _ => ?_
  rw [conjTranspose_apply, RCLike.star_def, mul_comm, RCLike.mul_conj]
  norm_cast
  positivity

omit [DecidableEq n] in
theorem frobSq_conjTranspose (A : Matrix n n 𝕜) : frobSq Aᴴ = frobSq A := by
  rw [frobSq, frobSq, conjTranspose_conjTranspose, trace_mul_comm]

/-- An orthogonal projection splits the squared Frobenius norm:
`‖X‖²_F = ‖X F‖²_F + ‖X (1 − F)‖²_F`. -/
theorem frobSq_eq_add_of_projection {F : Matrix n n 𝕜} (hF : F.IsHermitian) (hFF : F * F = F)
    (X : Matrix n n 𝕜) : frobSq X = frobSq (X * F) + frobSq (X * (1 - F)) := by
  have hE : (1 - F)ᴴ = 1 - F := by rw [conjTranspose_sub, conjTranspose_one, hF.eq]
  have hEE : (1 - F) * (1 - F) = 1 - F := by
    rw [sub_mul, mul_sub, mul_sub, hFF, one_mul, mul_one, one_mul]; abel
  have hsplit : ∀ M : Matrix n n 𝕜, Mᴴ = M → M * M = M →
      (Xᴴ * X * M).trace = ((X * M)ᴴ * (X * M)).trace := by
    intro M hM hMM
    rw [conjTranspose_mul, hM]
    calc (Xᴴ * X * M).trace = (Xᴴ * X * (M * M)).trace := by rw [hMM]
      _ = (M * (Xᴴ * X * M)).trace := by rw [← mul_assoc, trace_mul_comm]
      _ = (M * Xᴴ * (X * M)).trace := by simp only [mul_assoc]
  rw [frobSq, frobSq, frobSq, ← hsplit F hF.eq hFF, ← hsplit (1 - F) hE hEE, ← map_add,
    ← trace_add, ← mul_add, add_sub_cancel, mul_one]

/-- Compression by an orthogonal projection does not increase the Frobenius norm. -/
theorem frobSq_compression_le {F : Matrix n n 𝕜} (hF : F.IsHermitian) (hFF : F * F = F)
    (X : Matrix n n 𝕜) : frobSq (F * X * F) ≤ frobSq X := by
  have hright : ∀ Y : Matrix n n 𝕜, frobSq (Y * F) ≤ frobSq Y := fun Y => by
    rw [frobSq_eq_add_of_projection hF hFF Y]
    linarith [frobSq_nonneg' (Y * (1 - F))]
  have hleft : frobSq (F * X) ≤ frobSq X := by
    rw [← frobSq_conjTranspose (F * X), conjTranspose_mul, hF.eq, ← frobSq_conjTranspose X]
    exact hright Xᴴ
  exact (hright (F * X)).trans hleft

/-! ### Rank–trace for Hermitian matrices -/

/-- `(tr A)² ≤ rank A · ‖A‖²_F` for Hermitian `A`: Cauchy–Schwarz over the nonzero
eigenvalues. -/
theorem sq_rtrace_le_rank_mul_frobSq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    rtrace A ^ 2 ≤ A.rank * frobSq A := by
  set s := univ.filter fun i => hA.eigenvalues i ≠ 0
  have hrank : A.rank = #s := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have htr : rtrace A = ∑ i ∈ s, hA.eigenvalues i := by
    rw [rtrace_eq_sum_eigenvalues hA, sum_filter_ne_zero]
  have hfr : frobSq A = ∑ i ∈ s, hA.eigenvalues i ^ 2 := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hA, sum_filter_of_ne]
    intro i _ h
    exact fun h0 => h (by rw [h0]; ring)
  rw [hrank, htr, hfr]
  exact sq_sum_le_card_mul_sum_sq

/-! ### Orthogonal projections -/

/-- Spectral decomposition `E = U D Uᴴ` with `U` unitary and `D` the real eigenvalue diagonal. -/
theorem eq_eigenvectorUnitary_mul_diagonal {E : Matrix n n 𝕜} (hE : E.IsHermitian) :
    E = (hE.eigenvectorUnitary : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ hE.eigenvalues) *
      star (hE.eigenvectorUnitary : Matrix n n 𝕜) := by
  conv_lhs => rw [hE.spectral_theorem, Unitary.conjStarAlgAut_apply]

/-- The eigenvalues of an orthogonal projection are `0` and `1`. -/
theorem eigenvalues_eq_zero_or_one {E : Matrix n n 𝕜} (hE : E.IsHermitian) (hEE : E * E = E)
    (i : n) : hE.eigenvalues i = 0 ∨ hE.eigenvalues i = 1 := by
  set U : Matrix n n 𝕜 := ↑hE.eigenvectorUnitary
  set D : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hE.eigenvalues)
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hE.eigenvectorUnitary.2
  have hED : E = U * D * star U := eq_eigenvectorUnitary_mul_diagonal hE
  -- `U D D Uᴴ = E E = E = U D Uᴴ`; conjugating back by `U` gives `D D = D`
  have hD : D * D = D := by
    have h1 : U * (D * D) * star U = U * D * star U := by
      rw [← hED, ← hEE]
      conv_rhs => rw [hED]
      calc U * (D * D) * star U = U * D * (star U * U) * D * star U := by
            rw [hUU, mul_one]; simp only [mul_assoc]
        _ = U * D * star U * (U * D * star U) := by simp only [mul_assoc]
    calc D * D = star U * (U * (D * D) * star U) * U := by
          simp only [← mul_assoc, hUU, one_mul]; rw [mul_assoc, hUU, mul_one]
      _ = star U * (U * D * star U) * U := by rw [h1]
      _ = D := by simp only [← mul_assoc, hUU, one_mul]; rw [mul_assoc, hUU, mul_one]
  have hi := congrFun (congrFun hD i) i
  simp only [D, diagonal_mul_diagonal, diagonal_apply_eq, Function.comp_apply] at hi
  have hx : hE.eigenvalues i * hE.eigenvalues i = hE.eigenvalues i := by exact_mod_cast hi
  have : hE.eigenvalues i * (hE.eigenvalues i - 1) = 0 := by rw [mul_sub, hx]; ring
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- An antitone `0/1` sequence on `Fin m` is the indicator of its first `c` places, where `c` is
the number of ones. -/
theorem eq_ite_of_antitone_of_zero_or_one {m : ℕ} {e : Fin m → ℝ} (he : Antitone e)
    (h01 : ∀ i, e i = 0 ∨ e i = 1) (i : Fin m) :
    e i = if (i : ℕ) < #(univ.filter fun j => e j ≠ 0) then 1 else 0 := by
  rcases h01 i with h | h
  · rw [h, if_neg]
    rw [not_lt, ← Fin.card_Iio i]
    refine card_le_card fun j hj => ?_
    rw [mem_filter] at hj
    rw [mem_Iio]
    by_contra hji
    have := he (not_lt.1 hji)
    rcases h01 j with h' | h'
    · exact hj.2 h'
    · linarith
  · rw [h, if_pos]
    rw [Nat.lt_iff_add_one_le, ← Fin.card_Iic i]
    refine card_le_card fun j hj => ?_
    rw [mem_Iic] at hj
    rw [mem_filter]
    refine ⟨mem_univ _, fun h0 => ?_⟩
    have := he hj
    linarith

/-- Sorted eigenvalues of an orthogonal projection of rank `k`: `k` ones followed by zeros. -/
theorem eigenvalues₀_projection {E : Matrix n n 𝕜} (hE : E.IsHermitian) (hEE : E * E = E)
    (i : Fin (Fintype.card n)) : hE.eigenvalues₀ i = if (i : ℕ) < E.rank then 1 else 0 := by
  have h01 : ∀ j, hE.eigenvalues₀ j = 0 ∨ hE.eigenvalues₀ j = 1 := fun j => by
    rw [← eigenvalues_eigEquiv hE]; exact eigenvalues_eq_zero_or_one hE hEE _
  have hrank : E.rank = #(univ.filter fun j => hE.eigenvalues₀ j ≠ 0) := by
    rw [hE.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    exact card_eigenvalues_reindex hE (· ≠ 0)
  rw [hrank]
  exact eq_ite_of_antitone_of_zero_or_one hE.eigenvalues₀_antitone h01 i

/-- **Ky Fan's maximum principle** (upper half): for an orthogonal projection `E` of rank `k`,
`Re tr(G E) ≤ λ₀(G) + ⋯ + λ_{k−1}(G)`. -/
theorem re_trace_mul_projection_le {G E : Matrix n n 𝕜} (hG : G.IsHermitian)
    (hE : E.IsHermitian) (hEE : E * E = E) :
    RCLike.re (G * E).trace ≤ topEigenvalueSum hG E.rank := by
  refine (vonNeumann_trace_ineq hG hE).trans_eq ?_
  simp only [eigenvalues₀_projection hE hEE, mul_ite, mul_one, mul_zero, topEigenvalueSum,
    sum_filter]

/-- Every Hermitian `E` of rank at most `k ≤ card n` is fixed by an orthogonal projection of
rank exactly `k`: `E' E = E`. For an orthogonal projection `E` this says `range E ⊆ range E'`. -/
theorem exists_projection_rank_eq_of_rank_le {E : Matrix n n 𝕜} (hE : E.IsHermitian) {k : ℕ} (hEk : E.rank ≤ k) (hkn : k ≤ Fintype.card n) :
    ∃ E' : Matrix n n 𝕜, E'.IsHermitian ∧ E' * E' = E' ∧ E'.rank = k ∧ E' * E = E := by
  set s := univ.filter fun i => hE.eigenvalues i ≠ 0
  have hs : #s ≤ k := by
    rwa [hE.rank_eq_card_non_zero_eigs, Fintype.card_subtype] at hEk
  obtain ⟨t, hst, ht⟩ := exists_superset_card_eq hs hkn
  set U : Matrix n n 𝕜 := ↑hE.eigenvectorUnitary
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hE.eigenvectorUnitary.2
  set w : n → 𝕜 := fun i => if i ∈ t then 1 else 0
  set D' : Matrix n n 𝕜 := diagonal w
  set D : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hE.eigenvalues)
  have hED : E = U * D * star U := eq_eigenvectorUnitary_mul_diagonal hE
  have hww : ∀ i, w i * w i = w i := fun i => by by_cases h : i ∈ t <;> simp [w, h]
  have hwD : D' * D = D := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i ∈ t
    · simp [w, h]
    · have : hE.eigenvalues i = 0 := by
        by_contra h0
        exact h (hst (mem_filter.2 ⟨mem_univ _, h0⟩))
      simp [w, h, this]
  have hD'D' : D' * D' = D' := by rw [diagonal_mul_diagonal]; exact congrArg _ (funext hww)
  have hD'H : D'ᴴ = D' := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : i ∈ t <;> simp [w, h]
  refine ⟨U * D' * star U, ?_, ?_, ?_, ?_⟩
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, hD'H, ← star_eq_conjTranspose,
      star_star, ← star_eq_conjTranspose, mul_assoc]
  · calc U * D' * star U * (U * D' * star U) = U * D' * (star U * U) * D' * star U := by
          simp only [mul_assoc]
      _ = U * D' * star U := by rw [hUU, mul_one, mul_assoc U D' D', hD'D']
  · have hle : (U * D' * star U).rank ≤ D'.rank :=
      (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    have hge : D'.rank ≤ (U * D' * star U).rank := by
      have : D' = star U * (U * D' * star U) * U := by
        simp only [← mul_assoc, hUU, one_mul]; rw [mul_assoc, hUU, mul_one]
      calc D'.rank = (star U * (U * D' * star U) * U).rank := by rw [← this]
        _ ≤ (U * D' * star U).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    rw [le_antisymm hle hge, rank_diagonal, Fintype.card_subtype, ← ht]
    congr 1
    ext i
    by_cases h : i ∈ t <;> simp [w, h]
  · calc U * D' * star U * E = U * D' * (star U * U) * D * star U := by
          rw [hED]; simp only [mul_assoc]
      _ = E := by rw [hUU, mul_one, mul_assoc U D' D, hwD, hED]

/-! ### The bound -/

/-- Compression by an orthogonal projection `F` that kills the block `G − P`: the compressed
trace satisfies `(tr F G F)² ≤ rank P · ‖G‖²_F`. -/
theorem sq_rtrace_compression_le {G P F : Matrix n n 𝕜} (hG : G.IsHermitian)
    (hF : F.IsHermitian) (hFF : F * F = F) {r : ℕ} (hr : P.rank ≤ r)
    (hkill : F * (G - P) = 0) : rtrace (F * G * F) ^ 2 ≤ r * frobSq G := by
  have hFGF : F * G * F = F * P * F := by
    rw [mul_sub, sub_eq_zero] at hkill; rw [hkill]
  have hA : (F * G * F).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, hF.eq, hG.eq, mul_assoc]
  have hrank : ((F * G * F).rank : ℝ) ≤ r := by
    rw [hFGF]
    exact_mod_cast ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)).trans hr
  calc rtrace (F * G * F) ^ 2 ≤ (F * G * F).rank * frobSq (F * G * F) :=
        sq_rtrace_le_rank_mul_frobSq hA
    _ ≤ r * frobSq (F * G * F) := mul_le_mul_of_nonneg_right hrank (frobSq_nonneg' _)
    _ ≤ r * frobSq G := mul_le_mul_of_nonneg_left (frobSq_compression_le hF hFF G) (by positivity)

/-- **Codimension-robust rank–trace bound.** If `G` is Hermitian, `rank P ≤ r`, and
`E (G − P) = G − P` for a Hermitian `E` of rank at most `k` (so `G − P` has range in a subspace of
dimension at most `k`), then `tr G − (λ₀ + ⋯ + λ_{k−1}) ≤ √(r · ‖G‖²_F)`. -/
theorem rtrace_sub_topEigenvalueSum_le {G P E : Matrix n n 𝕜} (hG : G.IsHermitian)
    (hE : E.IsHermitian) {k r : ℕ} (hEk : E.rank ≤ k) (hr : P.rank ≤ r)
    (hrange : E * (G - P) = G - P) :
    rtrace G - topEigenvalueSum hG k ≤ Real.sqrt (r * frobSq G) := by
  rcases le_or_gt (Fintype.card n) k with hkn | hkn
  · rw [topEigenvalueSum_of_card_le hG hkn, sub_self]
    exact Real.sqrt_nonneg _
  obtain ⟨E', hE', hE'E', hrk, hE'E⟩ :=
    exists_projection_rank_eq_of_rank_le hE hEk hkn.le
  set F : Matrix n n 𝕜 := 1 - E'
  have hF : F.IsHermitian := by
    rw [IsHermitian, conjTranspose_sub, conjTranspose_one, hE'.eq]
  have hFF : F * F = F := by
    simp only [F, sub_mul, mul_sub, hE'E', one_mul, mul_one]; abel
  have hkill : F * (G - P) = 0 := by
    rw [← hrange, ← mul_assoc, sub_mul, one_mul, hE'E, sub_self, zero_mul]
  have htr : rtrace (F * G * F) = rtrace G - RCLike.re (G * E').trace := by
    rw [rtrace, trace_mul_comm, ← mul_assoc, hFF, trace_mul_comm, mul_sub, mul_one, trace_sub,
      map_sub, rtrace]
  have hKyFan := re_trace_mul_projection_le hG hE' hE'E'
  rw [hrk] at hKyFan
  calc rtrace G - topEigenvalueSum hG k ≤ rtrace (F * G * F) := by rw [htr]; linarith
    _ ≤ |rtrace (F * G * F)| := le_abs_self _
    _ ≤ Real.sqrt (r * frobSq G) :=
        Real.abs_le_sqrt (sq_rtrace_compression_le hG hF hFF (r := r) hr hkill)

/-- Squared form: `(tr G − Σ_{i<k} λᵢ)² ≤ r · ‖G‖²_F` when the left base is nonnegative,
i.e. `r ≥ (tr G − Σ_{i<k} λᵢ)² / ‖G‖²_F`. -/
theorem sq_rtrace_sub_topEigenvalueSum_le {G P E : Matrix n n 𝕜} (hG : G.IsHermitian)
    (hE : E.IsHermitian) {k r : ℕ} (hEk : E.rank ≤ k) (hr : P.rank ≤ r)
    (hrange : E * (G - P) = G - P) (h0 : 0 ≤ rtrace G - topEigenvalueSum hG k) :
    (rtrace G - topEigenvalueSum hG k) ^ 2 ≤ r * frobSq G := by
  have h := rtrace_sub_topEigenvalueSum_le hG hE hEk hr hrange
  have hnn : 0 ≤ (r : ℝ) * frobSq G := mul_nonneg (Nat.cast_nonneg r) (frobSq_nonneg' G)
  calc (rtrace G - topEigenvalueSum hG k) ^ 2 ≤ Real.sqrt (r * frobSq G) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = r * frobSq G := Real.sq_sqrt hnn

end RHTower
