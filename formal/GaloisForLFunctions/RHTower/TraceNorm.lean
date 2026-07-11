/-
The trace norm and the normed-ideal structure of the Schatten 1-class.

`traceNorm T = ∑ₙ aₙ(T)` is a genuine norm on the trace class, compatible with the operator
algebra.  Homogeneity and the ideal bounds come from the variational definition of the
approximation numbers.  The triangle inequality comes from Horn-type majorization: the singular
values of `S + T` are read off by its own singular pairs, `sₙ(S+T) = Re⟨fₙ, (S+T) eₙ⟩`, and
pairing any trace-class operator against orthonormal families is dominated by its trace norm —
expand by the singular value decomposition, swap the sums, and apply Cauchy–Schwarz with Bessel
on both sides.

Proved here:
* `hasRankLE_smul`, `hasRankLE_comp_left`, `hasRankLE_comp_right` — rank bounds under scalar
  multiples and composition.
* `approxNumber_zero_op`, `approxNumber_zero_eq_norm`, `approxNumber_smul`,
  `approxNumber_comp_le_left`, `approxNumber_comp_le_right` — the approximation-number algebra.
* `traceNorm` — with `traceNorm_zero`, `traceNorm_smul`, `norm_le_traceNorm`,
  `traceNorm_eq_zero_iff`, and the ideal bounds `traceNorm_comp_left_le`,
  `traceNorm_comp_right_le`.
* `sum_norm_inner_le_traceNorm` — **Horn-type majorization**: `∑ₙ |⟨gₙ, S hₙ⟩| ≤ traceNorm S`
  over orthonormal-with-zeros families.
* `summable_approxNumber_add`, `traceNorm_add_le` — **the triangle inequality**: the Schatten
  1-class is closed under addition with `‖S+T‖₁ ≤ ‖S‖₁ + ‖T‖₁`, hence a normed ideal.
* `memSchattenClass_one_add`, `memSchattenClass_one_smul`, `memSchattenClass_one_comp_left`,
  `memSchattenClass_one_comp_right` — the Schatten 1-class ideal axioms.
-/
import GaloisForLFunctions.PolarDecomposition
import GaloisForLFunctions.RHTower.TraceNormBound

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The approximation-number algebra -/

omit [CompleteSpace H] in
theorem hasRankLE_smul {F : H →L[ℂ] H} {n : ℕ} (h : HasRankLE F n) (c : ℂ) :
    HasRankLE (c • F) n := by
  obtain ⟨V, hfd, hle, hmem⟩ := h
  exact ⟨V, hfd, hle, fun x => by rw [smul_apply]; exact V.smul_mem c (hmem x)⟩

omit [CompleteSpace H] in
theorem hasRankLE_comp_right {F : H →L[ℂ] H} {n : ℕ} (h : HasRankLE F n) (B : H →L[ℂ] H) :
    HasRankLE (F ∘L B) n := by
  obtain ⟨V, hfd, hle, hmem⟩ := h
  exact ⟨V, hfd, hle, fun x => by rw [comp_apply]; exact hmem (B x)⟩

omit [CompleteSpace H] in
theorem hasRankLE_comp_left {F : H →L[ℂ] H} {n : ℕ} (h : HasRankLE F n) (A : H →L[ℂ] H) :
    HasRankLE (A ∘L F) n := by
  obtain ⟨V, hfd, hle, hmem⟩ := h
  haveI : Module.Finite ℂ (V.map (A : H →ₗ[ℂ] H)) := Module.Finite.map V _
  refine ⟨V.map (A : H →ₗ[ℂ] H), inferInstance,
    (Submodule.finrank_map_le _ V).trans hle, fun x => ?_⟩
  rw [comp_apply]
  exact Submodule.mem_map_of_mem (hmem x)

omit [CompleteSpace H] in
theorem approxNumber_zero_op (n : ℕ) : approxNumber (0 : H →L[ℂ] H) n = 0 :=
  le_antisymm (by simpa using approxNumber_le_norm (0 : H →L[ℂ] H) n)
    (approxNumber_nonneg _ n)

theorem approxNumber_smul (T : H →L[ℂ] H) (c : ℂ) (n : ℕ) :
    approxNumber (c • T) n = ‖c‖ * approxNumber T n := by
  have haux : ∀ (d : ℂ), d ≠ 0 → ∀ S : H →L[ℂ] H,
      approxNumber (d • S) n ≤ ‖d‖ * approxNumber S n := by
    intro d hd S
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hd' : (0 : ℝ) < ‖d‖ := norm_pos_iff.mpr hd
    obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt S n
      (lt_add_of_pos_right _ (by positivity : (0 : ℝ) < ε / ‖d‖))
    have h1 : approxNumber (d • S) n ≤ ‖d • S - d • F‖ :=
      approxNumber_le _ n _ (hasRankLE_smul hF d)
    rw [← smul_sub, norm_smul] at h1
    calc approxNumber (d • S) n ≤ ‖d‖ * ‖S - F‖ := h1
      _ ≤ ‖d‖ * (approxNumber S n + ε / ‖d‖) :=
          mul_le_mul_of_nonneg_left hFlt.le (norm_nonneg d)
      _ = ‖d‖ * approxNumber S n + ε := by field_simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp [approxNumber_zero_op]
  · refine le_antisymm (haux c hc T) ?_
    have h2 := haux c⁻¹ (inv_ne_zero hc) (c • T)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h2
    have hc' : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    calc ‖c‖ * approxNumber T n
        ≤ ‖c‖ * (‖c‖⁻¹ * approxNumber (c • T) n) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg c)
      _ = approxNumber (c • T) n := by field_simp

omit [CompleteSpace H] in
theorem approxNumber_zero_eq_norm (T : H →L[ℂ] H) : approxNumber T 0 = ‖T‖ := by
  refine le_antisymm (approxNumber_le_norm T 0) ?_
  refine le_csInf (approxNumber_set_nonempty T 0) ?_
  rintro r ⟨F, hF, rfl⟩
  obtain ⟨V, hfd, hle, hmem⟩ := hF
  have hV : V = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hle)
  have hF0 : F = 0 := by
    ext x
    have hx := hmem x
    rw [hV, Submodule.mem_bot] at hx
    simp [hx]
  rw [hF0, sub_zero]

omit [CompleteSpace H] in
theorem approxNumber_comp_le_left (A T : H →L[ℂ] H) (n : ℕ) :
    approxNumber (A ∘L T) n ≤ ‖A‖ * approxNumber T n := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [zero_comp, approxNumber_zero_op, norm_zero, zero_mul]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hA' : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hA
    obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt T n
      (lt_add_of_pos_right _ (by positivity : (0 : ℝ) < ε / ‖A‖))
    have h1 : approxNumber (A ∘L T) n ≤ ‖A ∘L T - A ∘L F‖ :=
      approxNumber_le _ n _ (hasRankLE_comp_left hF A)
    have h2 : A ∘L T - A ∘L F = A ∘L (T - F) := (comp_sub A T F).symm
    rw [h2] at h1
    calc approxNumber (A ∘L T) n ≤ ‖A‖ * ‖T - F‖ := h1.trans (A.opNorm_comp_le (T - F))
      _ ≤ ‖A‖ * (approxNumber T n + ε / ‖A‖) :=
          mul_le_mul_of_nonneg_left hFlt.le (norm_nonneg A)
      _ = ‖A‖ * approxNumber T n + ε := by field_simp

omit [CompleteSpace H] in
theorem approxNumber_comp_le_right (T B : H →L[ℂ] H) (n : ℕ) :
    approxNumber (T ∘L B) n ≤ approxNumber T n * ‖B‖ := by
  rcases eq_or_ne B 0 with rfl | hB
  · rw [comp_zero, approxNumber_zero_op, norm_zero, mul_zero]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hB' : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
    obtain ⟨F, hF, hFlt⟩ := exists_hasRankLE_norm_sub_lt T n
      (lt_add_of_pos_right _ (by positivity : (0 : ℝ) < ε / ‖B‖))
    have h1 : approxNumber (T ∘L B) n ≤ ‖T ∘L B - F ∘L B‖ :=
      approxNumber_le _ n _ (hasRankLE_comp_right hF B)
    have h2 : T ∘L B - F ∘L B = (T - F) ∘L B := (sub_comp T F B).symm
    rw [h2] at h1
    calc approxNumber (T ∘L B) n ≤ ‖T - F‖ * ‖B‖ := h1.trans ((T - F).opNorm_comp_le B)
      _ ≤ (approxNumber T n + ε / ‖B‖) * ‖B‖ :=
          mul_le_mul_of_nonneg_right hFlt.le (norm_nonneg B)
      _ = approxNumber T n * ‖B‖ + ε := by field_simp

/-! ### The trace norm -/

variable (H) in
/-- The **trace norm**: the sum of the approximation numbers. -/
noncomputable def traceNorm (T : H →L[ℂ] H) : ℝ := ∑' n, approxNumber T n

omit [CompleteSpace H] in
theorem traceNorm_nonneg (T : H →L[ℂ] H) : 0 ≤ traceNorm H T :=
  tsum_nonneg fun n => approxNumber_nonneg T n

omit [CompleteSpace H] in
theorem traceNorm_zero : traceNorm H (0 : H →L[ℂ] H) = 0 := by
  unfold traceNorm
  simp [approxNumber_zero_op]

/-- Homogeneity of the trace norm. -/
theorem traceNorm_smul (c : ℂ) (T : H →L[ℂ] H) :
    traceNorm H (c • T) = ‖c‖ * traceNorm H T := by
  unfold traceNorm
  rw [← tsum_mul_left]
  exact tsum_congr fun n => approxNumber_smul T c n

omit [CompleteSpace H] in
/-- The operator norm is dominated by the trace norm. -/
theorem norm_le_traceNorm {T : H →L[ℂ] H} (h : Summable (fun n => approxNumber T n)) :
    ‖T‖ ≤ traceNorm H T := by
  rw [← approxNumber_zero_eq_norm]
  exact h.le_tsum 0 fun n _ => approxNumber_nonneg T n

omit [CompleteSpace H] in
/-- Definiteness of the trace norm on the trace class. -/
theorem traceNorm_eq_zero_iff {T : H →L[ℂ] H} (h : Summable (fun n => approxNumber T n)) :
    traceNorm H T = 0 ↔ T = 0 := by
  constructor
  · intro h0
    have h1 := norm_le_traceNorm h
    rw [h0] at h1
    exact norm_le_zero_iff.mp h1
  · rintro rfl
    exact traceNorm_zero

theorem summable_approxNumber_smul {T : H →L[ℂ] H}
    (h : Summable (fun n => approxNumber T n)) (c : ℂ) :
    Summable (fun n => approxNumber (c • T) n) :=
  (h.mul_left ‖c‖).congr fun n => (approxNumber_smul T c n).symm

omit [CompleteSpace H] in
theorem summable_approxNumber_comp_left {T : H →L[ℂ] H}
    (h : Summable (fun n => approxNumber T n)) (A : H →L[ℂ] H) :
    Summable (fun n => approxNumber (A ∘L T) n) :=
  Summable.of_nonneg_of_le (fun n => approxNumber_nonneg _ n)
    (fun n => approxNumber_comp_le_left A T n) (h.mul_left ‖A‖)

omit [CompleteSpace H] in
theorem summable_approxNumber_comp_right {T : H →L[ℂ] H}
    (h : Summable (fun n => approxNumber T n)) (B : H →L[ℂ] H) :
    Summable (fun n => approxNumber (T ∘L B) n) :=
  Summable.of_nonneg_of_le (fun n => approxNumber_nonneg _ n)
    (fun n => approxNumber_comp_le_right T B n) (h.mul_right ‖B‖)

omit [CompleteSpace H] in
/-- The left ideal bound for the trace norm. -/
theorem traceNorm_comp_left_le {T : H →L[ℂ] H}
    (h : Summable (fun n => approxNumber T n)) (A : H →L[ℂ] H) :
    traceNorm H (A ∘L T) ≤ ‖A‖ * traceNorm H T := by
  unfold traceNorm
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => approxNumber_comp_le_left A T n)
    (summable_approxNumber_comp_left h A) (h.mul_left ‖A‖)

omit [CompleteSpace H] in
/-- The right ideal bound for the trace norm. -/
theorem traceNorm_comp_right_le {T : H →L[ℂ] H}
    (h : Summable (fun n => approxNumber T n)) (B : H →L[ℂ] H) :
    traceNorm H (T ∘L B) ≤ traceNorm H T * ‖B‖ := by
  unfold traceNorm
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun n => approxNumber_comp_le_right T B n)
    (summable_approxNumber_comp_right h B) (h.mul_right ‖B‖)

/-! ### Horn-type majorization -/

omit [CompleteSpace H] in
/-- Bessel over an orthonormal-with-zeros family, against a fixed vector. -/
theorem sum_inner_sq_le_of_orthonormal_with_zeros (v : ℕ → H)
    (hv : ∀ n, v n = 0 ∨ ‖v n‖ = 1)
    (horth : ∀ m n, m ≠ n → inner ℂ (v m) (v n) = 0) (y : H) (s : Finset ℕ) :
    ∑ n ∈ s, ‖inner ℂ (v n) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  classical
  have hsplit : ∑ n ∈ s, ‖inner ℂ (v n) y‖ ^ 2
      = ∑ n ∈ s.filter (fun n => v n ≠ 0), ‖inner ℂ (v n) y‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun n => v n ≠ 0)]
    have hz : ∑ n ∈ s.filter (fun n => ¬v n ≠ 0), ‖inner ℂ (v n) y‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have h0 := (Finset.mem_filter.mp hn).2
      rw [not_not] at h0
      rw [h0, inner_zero_left]
      simp
    rw [hz, add_zero]
  rw [hsplit]
  set t := s.filter (fun n => v n ≠ 0) with ht
  have horthsub : Orthonormal ℂ (fun p : {n : ℕ // n ∈ t} => v p.1) := by
    rw [orthonormal_iff_ite]
    intro p q
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K]
      rcases hv p.1 with h | h
      · exact absurd h (Finset.mem_filter.mp p.2).2
      · rw [h]; norm_num
    · rw [if_neg hpq]
      refine horth p.1 q.1 fun h => hpq (Subtype.ext h)
  have hbessel := horthsub.sum_inner_products_le (s := t.attach) y
  calc ∑ n ∈ t, ‖inner ℂ (v n) y‖ ^ 2
      = ∑ p ∈ t.attach, ‖inner ℂ (v p.1) y‖ ^ 2 :=
        (Finset.sum_attach t (fun n => ‖inner ℂ (v n) y‖ ^ 2)).symm
    _ ≤ ‖y‖ ^ 2 := hbessel

/-- **Horn-type majorization.**  Pairing a trace-class operator against orthonormal-with-zeros
families is dominated by the trace norm: expand by the singular value decomposition, swap the
sums, and apply Cauchy–Schwarz with Bessel on both families. -/
theorem sum_norm_inner_le_traceNorm {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsum : Summable (fun n => approxNumber S n)) {g h : ℕ → H}
    (hg1 : ∀ n, g n = 0 ∨ ‖g n‖ = 1) (hgo : ∀ m n, m ≠ n → inner ℂ (g m) (g n) = 0)
    (hh1 : ∀ n, h n = 0 ∨ ‖h n‖ = 1) (hho : ∀ m n, m ≠ n → inner ℂ (h m) (h n) = 0)
    (s : Finset ℕ) :
    ∑ n ∈ s, ‖inner ℂ (g n) (S (h n))‖ ≤ traceNorm H S := by
  classical
  have hsv : Summable (fun k => singVal S k) :=
    hsum.congr fun k => approxNumber_eq_singVal hcpt k
  have hnorm_le_one : ∀ (v : ℕ → H), (∀ n, v n = 0 ∨ ‖v n‖ = 1) → ∀ n, ‖v n‖ ≤ 1 := by
    intro v hv n
    rcases hv n with h0 | h1
    · rw [h0, norm_zero]; norm_num
    · rw [h1]
  have hsv1 : ∀ n, svVal (energyOp S) n ≠ 0 → ‖svVec (energyOp S) n‖ = 1 := fun n hn =>
    norm_svVec_of_ne_zero (energyOp_compact hcpt) (energyOp_symmetric S) (energyOp_pos S) hn
  have he_unit : ∀ k, svVec (energyOp S) k = 0 ∨ ‖svVec (energyOp S) k‖ = 1 := by
    intro k
    rcases eq_or_ne (svVal (energyOp S) k) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr (hsv1 k hne)
  have hf_unit : ∀ k, svdVec S k = 0 ∨ ‖svdVec S k‖ = 1 := by
    intro k
    rcases eq_or_ne (singVal S k) 0 with h0 | hne
    · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
    · exact Or.inr (norm_svdVec_sq hcpt hne)
  -- the SVD pairing for each n
  have hpair : ∀ n, HasSum
      (fun k => (((singVal S k : ℝ) : ℂ) * inner ℂ (svVec (energyOp S) k) (h n))
        * inner ℂ (g n) (svdVec S k)) (inner ℂ (g n) (S (h n))) := by
    intro n
    have h1 := (hasSum_svd hcpt (h n)).mapL (innerSL ℂ (g n))
    simpa only [innerSL_apply_apply, inner_smul_right, mul_comm] using h1
  -- the pointwise product bound
  set q : ℕ → ℕ → ℝ := fun n k =>
    singVal S k * (‖inner ℂ (svVec (energyOp S) k) (h n)‖ * ‖inner ℂ (g n) (svdVec S k)‖)
    with hq
  have hq_le : ∀ n k, q n k ≤ singVal S k := by
    intro n k
    rw [hq]
    have h1 : ‖inner ℂ (svVec (energyOp S) k) (h n)‖ ≤ 1 := by
      calc ‖inner ℂ (svVec (energyOp S) k) (h n)‖
          ≤ ‖svVec (energyOp S) k‖ * ‖h n‖ := norm_inner_le_norm _ _
        _ ≤ 1 * 1 := mul_le_mul (hnorm_le_one _ he_unit k) (hnorm_le_one _ hh1 n)
            (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h2 : ‖inner ℂ (g n) (svdVec S k)‖ ≤ 1 := by
      calc ‖inner ℂ (g n) (svdVec S k)‖
          ≤ ‖g n‖ * ‖svdVec S k‖ := norm_inner_le_norm _ _
        _ ≤ 1 * 1 := mul_le_mul (hnorm_le_one _ hg1 n) (hnorm_le_one _ hf_unit k)
            (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc singVal S k * (‖inner ℂ (svVec (energyOp S) k) (h n)‖
          * ‖inner ℂ (g n) (svdVec S k)‖)
        ≤ singVal S k * (1 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (singVal_nonneg S k)
          exact mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = singVal S k := by ring
  have hq_nonneg : ∀ n k, 0 ≤ q n k := fun n k => by
    rw [hq]
    exact mul_nonneg (singVal_nonneg S k) (by positivity)
  have hq_summable : ∀ n, Summable (q n) := fun n =>
    Summable.of_nonneg_of_le (hq_nonneg n) (hq_le n) hsv
  -- per-n bound by the q-series
  have hbound : ∀ n, ‖inner ℂ (g n) (S (h n))‖ ≤ ∑' k, q n k := by
    intro n
    have hsummable_norm : Summable (fun k =>
        ‖(((singVal S k : ℝ) : ℂ) * inner ℂ (svVec (energyOp S) k) (h n))
          * inner ℂ (g n) (svdVec S k)‖) := by
      refine (hq_summable n).congr fun k => ?_
      rw [hq]
      simp only
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (singVal_nonneg S k), mul_assoc]
    calc ‖inner ℂ (g n) (S (h n))‖
        = ‖∑' k, (((singVal S k : ℝ) : ℂ) * inner ℂ (svVec (energyOp S) k) (h n))
            * inner ℂ (g n) (svdVec S k)‖ := by rw [(hpair n).tsum_eq]
      _ ≤ ∑' k, ‖(((singVal S k : ℝ) : ℂ) * inner ℂ (svVec (energyOp S) k) (h n))
            * inner ℂ (g n) (svdVec S k)‖ := norm_tsum_le_tsum_norm hsummable_norm
      _ = ∑' k, q n k := by
          refine tsum_congr fun k => ?_
          rw [hq]
          simp only
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (singVal_nonneg S k), mul_assoc]
  -- swap the sums
  have hswap : ∑ n ∈ s, ∑' k, q n k = ∑' k, ∑ n ∈ s, q n k :=
    (Summable.tsum_finsetSum fun n _ => hq_summable n).symm
  -- per-k bound after the swap
  have hperk : ∀ k, ∑ n ∈ s, q n k ≤ singVal S k := by
    intro k
    rw [hq]
    simp only
    rw [← Finset.mul_sum]
    have hCS : ∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖
          * ‖inner ℂ (g n) (svdVec S k)‖
        ≤ Real.sqrt (∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖ ^ 2)
          * Real.sqrt (∑ n ∈ s, ‖inner ℂ (g n) (svdVec S k)‖ ^ 2) := by
      have h1 := Finset.sum_mul_sq_le_sq_mul_sq s
        (fun n => ‖inner ℂ (svVec (energyOp S) k) (h n)‖)
        (fun n => ‖inner ℂ (g n) (svdVec S k)‖)
      have h2 : 0 ≤ ∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖
          * ‖inner ℂ (g n) (svdVec S k)‖ := Finset.sum_nonneg fun n _ => by positivity
      calc ∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖
            * ‖inner ℂ (g n) (svdVec S k)‖
          = Real.sqrt ((∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖
              * ‖inner ℂ (g n) (svdVec S k)‖) ^ 2) := (Real.sqrt_sq h2).symm
        _ ≤ Real.sqrt ((∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖ ^ 2)
              * ∑ n ∈ s, ‖inner ℂ (g n) (svdVec S k)‖ ^ 2) := Real.sqrt_le_sqrt h1
        _ = _ := Real.sqrt_mul (Finset.sum_nonneg fun n _ => by positivity) _
    have hB1 : ∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖ ^ 2 ≤ 1 := by
      have hflip : ∀ n, ‖inner ℂ (svVec (energyOp S) k) (h n)‖
          = ‖inner ℂ (h n) (svVec (energyOp S) k)‖ := by
        intro n
        rw [← inner_conj_symm, RCLike.norm_conj]
      calc ∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖ ^ 2
          = ∑ n ∈ s, ‖inner ℂ (h n) (svVec (energyOp S) k)‖ ^ 2 :=
            Finset.sum_congr rfl fun n _ => by rw [hflip]
        _ ≤ ‖svVec (energyOp S) k‖ ^ 2 :=
            sum_inner_sq_le_of_orthonormal_with_zeros h hh1 hho _ s
        _ ≤ 1 := by
            have := hnorm_le_one _ he_unit k
            nlinarith [norm_nonneg (svVec (energyOp S) k)]
    have hB2 : ∑ n ∈ s, ‖inner ℂ (g n) (svdVec S k)‖ ^ 2 ≤ 1 := by
      calc ∑ n ∈ s, ‖inner ℂ (g n) (svdVec S k)‖ ^ 2
          ≤ ‖svdVec S k‖ ^ 2 :=
            sum_inner_sq_le_of_orthonormal_with_zeros g hg1 hgo _ s
        _ ≤ 1 := by
            have := hnorm_le_one _ hf_unit k
            nlinarith [norm_nonneg (svdVec S k)]
    calc singVal S k * ∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖
          * ‖inner ℂ (g n) (svdVec S k)‖
        ≤ singVal S k * (Real.sqrt (∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖ ^ 2)
            * Real.sqrt (∑ n ∈ s, ‖inner ℂ (g n) (svdVec S k)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS (singVal_nonneg S k)
      _ ≤ singVal S k * (1 * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (singVal_nonneg S k)
          refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) zero_le_one
          · calc Real.sqrt (∑ n ∈ s, ‖inner ℂ (svVec (energyOp S) k) (h n)‖ ^ 2)
                ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hB1
              _ = 1 := Real.sqrt_one
          · calc Real.sqrt (∑ n ∈ s, ‖inner ℂ (g n) (svdVec S k)‖ ^ 2)
                ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hB2
              _ = 1 := Real.sqrt_one
      _ = singVal S k := by ring
  -- assemble
  have hsummable_swap : Summable (fun k => ∑ n ∈ s, q n k) :=
    summable_sum fun n _ => hq_summable n
  calc ∑ n ∈ s, ‖inner ℂ (g n) (S (h n))‖
      ≤ ∑ n ∈ s, ∑' k, q n k := Finset.sum_le_sum fun n _ => hbound n
    _ = ∑' k, ∑ n ∈ s, q n k := hswap
    _ ≤ ∑' k, singVal S k := Summable.tsum_le_tsum hperk hsummable_swap hsv
    _ = traceNorm H S := tsum_congr fun k => (approxNumber_eq_singVal hcpt k).symm

/-! ### The triangle inequality -/

/-- Every partial sum of `aₙ(S+T)` is bounded by `‖S‖₁ + ‖T‖₁`. -/
theorem sum_approxNumber_add_le {S T : H →L[ℂ] H}
    (hScpt : IsCompactOperator S) (hTcpt : IsCompactOperator T)
    (hS : Summable (fun n => approxNumber S n)) (hT : Summable (fun n => approxNumber T n))
    (s : Finset ℕ) :
    ∑ n ∈ s, approxNumber (S + T) n ≤ traceNorm H S + traceNorm H T := by
  classical
  have hMcpt : IsCompactOperator (S + T) := hScpt.add hTcpt
  have hsymM := energyOp_symmetric (S + T)
  have hposM := energyOp_pos (S + T)
  have hScptM := energyOp_compact hMcpt
  set e : ℕ → H := svVec (energyOp (S + T)) with he
  set f : ℕ → H := svdVec (S + T) with hf
  have he_unit : ∀ k, e k = 0 ∨ ‖e k‖ = 1 := by
    intro k
    rcases eq_or_ne (svVal (energyOp (S + T)) k) 0 with h0 | hne
    · exact Or.inl (svVec_eq_zero_of_svVal_eq_zero _ h0)
    · exact Or.inr (norm_svVec_of_ne_zero hScptM hsymM hposM hne)
  have hf_unit : ∀ k, f k = 0 ∨ ‖f k‖ = 1 := by
    intro k
    rcases eq_or_ne (singVal (S + T) k) 0 with h0 | hne
    · exact Or.inl (svdVec_eq_zero_of_singVal_eq_zero _ h0)
    · exact Or.inr (norm_svdVec_sq hMcpt hne)
  have he_orth : ∀ m n, m ≠ n → inner ℂ (e m) (e n) = 0 := fun m n hmn =>
    inner_svVec_svVec_of_ne _ hmn
  have hf_orth : ∀ m n, m ≠ n → inner ℂ (f m) (f n) = 0 := fun m n hmn =>
    inner_svdVec_svdVec_of_ne _ hmn
  have hkey : ∀ n, approxNumber (S + T) n
      ≤ ‖inner ℂ (f n) (S (e n))‖ + ‖inner ℂ (f n) (T (e n))‖ := by
    intro n
    rw [approxNumber_eq_singVal hMcpt n]
    have h1 : singVal (S + T) n
        = RCLike.re (inner ℂ (f n) ((S + T) (e n))) := by
      rw [hf, he, inner_svdVec_apply hMcpt n]
      simp
    rw [h1]
    calc RCLike.re (inner ℂ (f n) ((S + T) (e n)))
        = RCLike.re (inner ℂ (f n) (S (e n))) + RCLike.re (inner ℂ (f n) (T (e n))) := by
          rw [add_apply, inner_add_right, map_add]
      _ ≤ ‖inner ℂ (f n) (S (e n))‖ + ‖inner ℂ (f n) (T (e n))‖ :=
          add_le_add (RCLike.re_le_norm _) (RCLike.re_le_norm _)
  calc ∑ n ∈ s, approxNumber (S + T) n
      ≤ ∑ n ∈ s, (‖inner ℂ (f n) (S (e n))‖ + ‖inner ℂ (f n) (T (e n))‖) :=
        Finset.sum_le_sum fun n _ => hkey n
    _ = (∑ n ∈ s, ‖inner ℂ (f n) (S (e n))‖) + ∑ n ∈ s, ‖inner ℂ (f n) (T (e n))‖ :=
        Finset.sum_add_distrib
    _ ≤ traceNorm H S + traceNorm H T :=
        add_le_add
          (sum_norm_inner_le_traceNorm hScpt hS hf_unit hf_orth he_unit he_orth s)
          (sum_norm_inner_le_traceNorm hTcpt hT hf_unit hf_orth he_unit he_orth s)

/-- The Schatten 1-class is closed under addition. -/
theorem summable_approxNumber_add {S T : H →L[ℂ] H}
    (hScpt : IsCompactOperator S) (hTcpt : IsCompactOperator T)
    (hS : Summable (fun n => approxNumber S n)) (hT : Summable (fun n => approxNumber T n)) :
    Summable (fun n => approxNumber (S + T) n) :=
  summable_of_sum_le (fun n => approxNumber_nonneg _ n)
    (sum_approxNumber_add_le hScpt hTcpt hS hT)

/-- **The triangle inequality for the trace norm.** -/
theorem traceNorm_add_le {S T : H →L[ℂ] H}
    (hScpt : IsCompactOperator S) (hTcpt : IsCompactOperator T)
    (hS : Summable (fun n => approxNumber S n)) (hT : Summable (fun n => approxNumber T n)) :
    traceNorm H (S + T) ≤ traceNorm H S + traceNorm H T :=
  Real.tsum_le_of_sum_le (fun n => approxNumber_nonneg _ n)
    (sum_approxNumber_add_le hScpt hTcpt hS hT)

/-! ### The Schatten 1-class ideal axioms -/

omit [CompleteSpace H] in
private theorem memSchattenClass_one_iff_summable {T : H →L[ℂ] H} :
    MemSchattenClass 1 T ↔ Summable (fun n => approxNumber T n) := by
  constructor
  · intro h1
    exact h1.congr fun n => Real.rpow_one _
  · intro h1
    exact h1.congr fun n => (Real.rpow_one _).symm

/-- The Schatten 1-class is closed under addition. -/
theorem memSchattenClass_one_add {S T : H →L[ℂ] H}
    (hScpt : IsCompactOperator S) (hTcpt : IsCompactOperator T)
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (S + T) :=
  memSchattenClass_one_iff_summable.mpr
    (summable_approxNumber_add hScpt hTcpt
      (memSchattenClass_one_iff_summable.mp hS) (memSchattenClass_one_iff_summable.mp hT))

/-- The Schatten 1-class is closed under scalar multiplication. -/
theorem memSchattenClass_one_smul {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T) (c : ℂ) :
    MemSchattenClass 1 (c • T) :=
  memSchattenClass_one_iff_summable.mpr
    (summable_approxNumber_smul (memSchattenClass_one_iff_summable.mp hT) c)

omit [CompleteSpace H] in
/-- The Schatten 1-class is a left ideal. -/
theorem memSchattenClass_one_comp_left {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T)
    (A : H →L[ℂ] H) : MemSchattenClass 1 (A ∘L T) :=
  memSchattenClass_one_iff_summable.mpr
    (summable_approxNumber_comp_left (memSchattenClass_one_iff_summable.mp hT) A)

omit [CompleteSpace H] in
/-- The Schatten 1-class is a right ideal. -/
theorem memSchattenClass_one_comp_right {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T)
    (B : H →L[ℂ] H) : MemSchattenClass 1 (T ∘L B) :=
  memSchattenClass_one_iff_summable.mpr
    (summable_approxNumber_comp_right (memSchattenClass_one_iff_summable.mp hT) B)

end RHTower
