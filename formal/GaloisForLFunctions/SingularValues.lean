/-
# Singular values of a compact operator on a complex Hilbert space

The singular values of a compact `T` are the square roots of the greedy eigenvalues of the energy
operator `T†T` — positive, compact, self-adjoint — in decreasing order with multiplicity.  The
greedy eigenvectors have pairwise-orthogonal images under `T` with `‖T eₙ‖² = μₙ`, and a vector
orthogonal to all of them is annihilated by `T`.  Extending the live greedy vectors to a Hilbert
basis therefore computes the Hilbert–Schmidt series of `T` exactly on the greedy family, giving
the unconditional `ℝ≥0∞` identity `∑ᵢ ‖T bᵢ‖² = ∑ₙ μₙ` over any Hilbert basis: `T` is
Hilbert–Schmidt precisely when its singular values are square-summable, with
`‖T‖²_HS = ∑ₙ sₙ²`.

Proved here:
* `energyOp` — `T†T`, with `energyOp_symmetric`, `inner_energyOp_self` (`⟨x, T†T x⟩ = ‖T x‖²`),
  `energyOp_pos`, `energyOp_compact`.
* `singVal` — the singular values `sₙ = √μₙ`, nonnegative and antitone, `singVal_sq`.
* `norm_apply_svVec_sq` — `‖T eₙ‖² = μₙ·‖eₙ‖²` on the greedy family.
* `norm_apply_le_singVal_of_orth` — `‖T x‖ ≤ sₙ·‖x‖` for `x` orthogonal to the first `n` greedy
  vectors.
* `tsum_ennreal_svVal_eq` — the master `ℝ≥0∞` identity: the Hilbert–Schmidt series of `T` equals
  `∑ₙ μₙ`.
* `isHilbertSchmidt_iff_summable_svVal`, `hsNormSq_eq_tsum_svVal` — **the Schatten-2 dictionary**:
  `T` is Hilbert–Schmidt iff `∑ₙ sₙ² < ∞`, and then `‖T‖²_HS = ∑ₙ sₙ²`.
-/
import GaloisForLFunctions.GreedySingularValues
import GaloisForLFunctions.HilbertSchmidtOperator

open scoped InnerProductSpace ComplexConjugate

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The energy operator `T†T` of `T`. -/
noncomputable def energyOp (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint T ∘L T

theorem energyOp_symmetric (T : H →L[ℂ] H) : (energyOp T).IsSymmetric := by
  intro x y
  show inner ℂ ((ContinuousLinearMap.adjoint T ∘L T) x) y
    = inner ℂ x ((ContinuousLinearMap.adjoint T ∘L T) y)
  rw [comp_apply, comp_apply, adjoint_inner_left, adjoint_inner_right]

theorem re_inner_energyOp_self (T : H →L[ℂ] H) (x : H) :
    RCLike.re (inner ℂ x (energyOp T x)) = ‖T x‖ ^ 2 := by
  rw [energyOp, comp_apply, adjoint_inner_right]
  exact inner_self_eq_norm_sq _

theorem energyOp_pos (T : H →L[ℂ] H) :
    ∀ x : H, 0 ≤ RCLike.re (inner ℂ x (energyOp T x)) := by
  intro x
  rw [re_inner_energyOp_self]
  positivity

theorem energyOp_compact {T : H →L[ℂ] H} (hcpt : IsCompactOperator T) :
    IsCompactOperator (energyOp T) :=
  hcpt.clm_comp (ContinuousLinearMap.adjoint T)

/-- The **singular values** of `T`: the square roots of the greedy eigenvalues of `T†T`, in
decreasing order with multiplicity. -/
noncomputable def singVal (T : H →L[ℂ] H) (n : ℕ) : ℝ :=
  Real.sqrt (svVal (energyOp T) n)

theorem singVal_nonneg (T : H →L[ℂ] H) (n : ℕ) : 0 ≤ singVal T n := Real.sqrt_nonneg _

theorem singVal_sq (T : H →L[ℂ] H) (n : ℕ) : singVal T n ^ 2 = svVal (energyOp T) n :=
  Real.sq_sqrt (svVal_nonneg _ n)

theorem singVal_antitone (T : H →L[ℂ] H) : Antitone (singVal T) := fun _ _ h =>
  Real.sqrt_le_sqrt (svVal_antitone (energyOp T) h)

/-- On the greedy family the squared image norm is the greedy value:
`‖T eₙ‖² = μₙ·‖eₙ‖²`. -/
theorem norm_apply_svVec_sq (T : H →L[ℂ] H) (n : ℕ) :
    ‖T (svVec (energyOp T) n)‖ ^ 2
      = svVal (energyOp T) n * ‖svVec (energyOp T) n‖ ^ 2 := by
  rw [← re_inner_energyOp_self T, apply_svVec, inner_smul_right, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The tail bound: `‖T x‖ ≤ sₙ·‖x‖` for `x` orthogonal to the first `n` greedy vectors. -/
theorem norm_apply_le_singVal_of_orth (T : H →L[ℂ] H) {x : H} (n : ℕ)
    (hx : ∀ m < n, inner ℂ (svVec (energyOp T) m) x = 0) :
    ‖T x‖ ≤ singVal T n * ‖x‖ := by
  have hsq : ‖T x‖ ^ 2 ≤ svVal (energyOp T) n * ‖x‖ ^ 2 := by
    rw [← re_inner_energyOp_self T x]
    calc RCLike.re (inner ℂ x (energyOp T x))
        ≤ ‖inner ℂ x (energyOp T x)‖ := RCLike.re_le_norm _
      _ ≤ ‖x‖ * ‖energyOp T x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (svVal (energyOp T) n * ‖x‖) := by
          have := norm_apply_le_of_orth (energyOp T) n hx
          exact mul_le_mul_of_nonneg_left this (norm_nonneg x)
      _ = svVal (energyOp T) n * ‖x‖ ^ 2 := by ring
  calc ‖T x‖ = Real.sqrt (‖T x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (svVal (energyOp T) n * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = singVal T n * ‖x‖ := by
        rw [Real.sqrt_mul (svVal_nonneg _ n), Real.sqrt_sq (norm_nonneg x), singVal]

section Master

variable {T : H →L[ℂ] H}

private theorem summable_iff_ennreal_ne_top {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) :
    Summable g ↔ ∑' i, ENNReal.ofReal (g i) ≠ ⊤ := by
  constructor
  · intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg hg hs]
    exact ENNReal.ofReal_ne_top
  · intro h
    exact (ENNReal.summable_toReal h).congr fun i => ENNReal.toReal_ofReal (hg i)

/-- **The master `ℝ≥0∞` identity.**  The Hilbert–Schmidt series of a compact `T` over any Hilbert
basis is the sum of the greedy eigenvalues of `T†T`: extend the live greedy vectors — pairwise
orthonormal — to a Hilbert basis; on it, `T` has squared norms `μₙ` along the greedy family and
vanishes on the rest by completeness of the exhaustion. -/
theorem tsum_ennreal_svVal_eq (hcpt : IsCompactOperator T) :
    ∑' i, ENNReal.ofReal (‖T (hsBasis ℂ H i)‖ ^ 2)
      = ∑' n, ENNReal.ofReal (svVal (energyOp T) n) := by
  classical
  have hsym := energyOp_symmetric T
  have hpos := energyOp_pos T
  have hScpt := energyOp_compact hcpt
  have hinj : ∀ {m n : ℕ}, svVal (energyOp T) m ≠ 0 → svVal (energyOp T) n ≠ 0 →
      svVec (energyOp T) m = svVec (energyOp T) n → m = n := by
    intro m n hm hn hmn
    by_contra hne
    have h0 := inner_svVec_svVec_of_ne (energyOp T) hne
    rw [hmn, inner_self_eq_norm_sq_to_K,
      norm_svVec_of_ne_zero hScpt hsym hpos hn] at h0
    norm_num at h0
  have hA_orth : Orthonormal ℂ
      (Subtype.val : (svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0}) → H) := by
    rw [orthonormal_subtype_iff_ite]
    rintro x ⟨m, hm, rfl⟩ y ⟨n, hn, rfl⟩
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K,
        norm_svVec_of_ne_zero hScpt hsym hpos hm]
      norm_num
    · rw [if_neg fun h => hmn (hinj hm hn h), inner_svVec_svVec_of_ne (energyOp T) hmn]
  obtain ⟨w, b, hAw, hb⟩ := hA_orth.exists_hilbertBasis_extension
  have horthw : ∀ u ∈ w, ∀ v ∈ w, u ≠ v → inner ℂ u v = 0 := by
    have hw_orth : Orthonormal ℂ (Subtype.val : w → H) := hb ▸ b.orthonormal
    rw [orthonormal_subtype_iff_ite] at hw_orth
    intro u hu v hv huv
    have := hw_orth u hu v hv
    rwa [if_neg huv] at this
  have hbasis : ∑' i, ENNReal.ofReal (‖T (hsBasis ℂ H i)‖ ^ 2)
      = ∑' x : w, ENNReal.ofReal (‖T (b x)‖ ^ 2) :=
    (hsE_eq_adjoint (hsBasis ℂ H) (hsBasis ℂ H) T).trans
      (hsE_eq_adjoint b (hsBasis ℂ H) T).symm
  rw [hbasis]
  simp only [hb]
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun p => ⟨svVec (energyOp T) p.1, hAw ⟨p.1, ?_, rfl⟩⟩) ?_ ?_ ?_
  · have hp := p.2
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hp
    exact ne_of_gt hp
  · rintro ⟨m, hm⟩ ⟨n, hn⟩ h
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hm hn
    have h' : svVec (energyOp T) m = svVec (energyOp T) n := congrArg Subtype.val h
    exact Subtype.ext (hinj (ne_of_gt hm) (ne_of_gt hn) h')
  · rintro ⟨u, hu⟩ hfu
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hfu
    have hTu : T u ≠ 0 := by
      intro h
      rw [h] at hfu
      simp at hfu
    have huA : u ∈ svVec (energyOp T) '' {n | svVal (energyOp T) n ≠ 0} := by
      by_contra huA
      have horth_all : ∀ n, inner ℂ (svVec (energyOp T) n) u = 0 := by
        intro n
        rcases eq_or_ne (svVal (energyOp T) n) 0 with h0 | hne0
        · rw [svVec_eq_zero_of_svVal_eq_zero (energyOp T) h0]
          exact inner_zero_left _
        · have hmem : svVec (energyOp T) n ∈ w := hAw ⟨n, hne0, rfl⟩
          refine horthw _ hmem _ hu fun h => huA ?_
          rw [← h]
          exact ⟨n, hne0, rfl⟩
      have hSu : energyOp T u = 0 :=
        apply_eq_zero_of_forall_inner_svVec hScpt hsym hpos horth_all
      have hz : (‖T u‖ ^ 2 : ℝ) = 0 := by
        rw [← re_inner_energyOp_self T u, hSu, inner_zero_right]
        simp
      exact hTu (by simpa [pow_eq_zero_iff] using hz)
    obtain ⟨n, hn, hun⟩ := huA
    have hgn : ENNReal.ofReal (svVal (energyOp T) n) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_le_of_ne (svVal_nonneg _ n) (Ne.symm hn)
    exact ⟨⟨n, hgn⟩, Subtype.ext hun.symm⟩
  · rintro ⟨n, hn⟩
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hn
    have hne0 : svVal (energyOp T) n ≠ 0 := ne_of_gt hn
    have hunit : ‖svVec (energyOp T) n‖ = 1 :=
      norm_svVec_of_ne_zero hScpt hsym hpos hne0
    show ENNReal.ofReal (‖T (svVec (energyOp T) n)‖ ^ 2)
      = ENNReal.ofReal (svVal (energyOp T) n)
    rw [norm_apply_svVec_sq, hunit]
    norm_num

/-- **The Schatten-2 summability dictionary.**  A compact operator is Hilbert–Schmidt exactly when
its singular values are square-summable. -/
theorem isHilbertSchmidt_iff_summable_svVal (hcpt : IsCompactOperator T) :
    T.IsHilbertSchmidt ↔ Summable (svVal (energyOp T)) := by
  rw [isHilbertSchmidt_iff_summable (hsBasis ℂ H),
    summable_iff_ennreal_ne_top (fun i => by positivity),
    summable_iff_ennreal_ne_top (fun n => svVal_nonneg _ n),
    tsum_ennreal_svVal_eq hcpt]

/-- **The Schatten-2 norm identity.**  For a compact Hilbert–Schmidt operator,
`‖T‖²_HS = ∑ₙ sₙ² = ∑ₙ μₙ`. -/
theorem hsNormSq_eq_tsum_svVal (hcpt : IsCompactOperator T) (hHS : T.IsHilbertSchmidt) :
    hsNormSq T = ∑' n, svVal (energyOp T) n := by
  have hsummable : Summable (svVal (energyOp T)) :=
    (isHilbertSchmidt_iff_summable_svVal hcpt).mp hHS
  have hENN := tsum_ennreal_svVal_eq hcpt
  have hsum_can : Summable (fun i => ‖T (hsBasis ℂ H i)‖ ^ 2) := hHS
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum_can,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => svVal_nonneg _ n) hsummable] at hENN
  have hval := congrArg ENNReal.toReal hENN
  rw [ENNReal.toReal_ofReal (tsum_nonneg fun i => by positivity),
    ENNReal.toReal_ofReal (tsum_nonneg fun n => svVal_nonneg _ n)] at hval
  exact hval

end Master

end ContinuousLinearMap
