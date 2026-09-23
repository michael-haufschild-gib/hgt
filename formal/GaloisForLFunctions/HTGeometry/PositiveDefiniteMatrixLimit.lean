import Mathlib

/-!
# Coercivity and stability of real positive-definite matrices

A real positive-definite matrix bounds its quadratic form below by a positive multiple of the squared
Euclidean length (`posDef_coercive`).  The bound is uniform, so positive-definiteness is an *open*
condition on the matrix entries: any family of Hermitian matrices whose entries converge to those of a
positive-definite matrix is eventually positive-definite (`posDef_eventually_of_tendsto`).  The
elementary entrywise estimate `abs_dotProduct_mulVec_le` controls the quadratic form of a perturbation
by the largest entry.

These are the finite-dimensional stability facts behind eventual positivity of a moment-Hankel tower
whose entries approach those of a genuine positive-definite Gram matrix under a limiting regime.
-/

open Matrix Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Coercivity of a real positive-definite matrix.**  If `M` is positive definite then its
quadratic form dominates a positive multiple of the squared Euclidean length: there is `μ > 0` with
`μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ M *ᵥ x` for every `x`.  Proved by minimising the continuous quadratic form over
the compact unit sphere `{x | x ⬝ᵥ x = 1}` and rescaling. -/
theorem posDef_coercive {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x : Fin n → ℝ, μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ M *ᵥ x := by
  have hfc : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ M *ᵥ x) := by fun_prop
  have hhom : ∀ (c : ℝ) (x : Fin n → ℝ), (c • x) ⬝ᵥ M *ᵥ (c • x) = c ^ (2 : ℕ) * (x ⬝ᵥ M *ᵥ x) := by
    intro c x
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨1, one_pos, fun x => by rw [Subsingleton.elim x 0]; simp⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  set S : Set (Fin n → ℝ) := {x | x ⬝ᵥ x = 1} with hS
  have hScl : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hSbd : Bornology.IsBounded S := by
    apply (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    have hle : x i ^ (2 : ℕ) ≤ x ⬝ᵥ x := by
      rw [dotProduct, sq]
      exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [hx] at hle
    have : |x i| ≤ 1 := by nlinarith [sq_abs (x i), abs_nonneg (x i)]
    simpa [Real.norm_eq_abs] using this
  have hScompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSbd
  have hSne : S.Nonempty := by
    refine ⟨Pi.single 0 1, ?_⟩
    rw [hS, Set.mem_setOf_eq, single_dotProduct, Pi.single_eq_same, mul_one]
  obtain ⟨x₀, hx₀S, hx₀min⟩ := hScompact.exists_isMinOn hSne hfc.continuousOn
  have hx₀ne : x₀ ≠ 0 := by
    intro h; rw [hS, Set.mem_setOf_eq, h] at hx₀S; simp [dotProduct] at hx₀S
  set μ : ℝ := x₀ ⬝ᵥ M *ᵥ x₀ with hμ
  have hμpos : 0 < μ := by
    have := hM.re_dotProduct_pos hx₀ne
    simpa [Matrix.star_eq_conjTranspose, star_trivial] using this
  refine ⟨μ, hμpos, fun x => ?_⟩
  rcases eq_or_ne (x ⬝ᵥ x) 0 with hx0 | hx0
  · rw [(dotProduct_self_eq_zero (v := x)).mp hx0]; simp
  · have hspos : 0 < x ⬝ᵥ x := lt_of_le_of_ne
      (by rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Ne.symm hx0)
    set s : ℝ := x ⬝ᵥ x with hsdef
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
    have hyS : ((Real.sqrt s)⁻¹ • x) ⬝ᵥ ((Real.sqrt s)⁻¹ • x) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hsdef, ← mul_assoc,
        ← mul_inv, Real.mul_self_sqrt hspos.le, inv_mul_cancel₀ hspos.ne']
    have hxeq : (Real.sqrt s) • ((Real.sqrt s)⁻¹ • x) = x := by
      rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
    have hfx : x ⬝ᵥ M *ᵥ x
        = s * (((Real.sqrt s)⁻¹ • x) ⬝ᵥ M *ᵥ ((Real.sqrt s)⁻¹ • x)) := by
      conv_lhs => rw [← hxeq]
      rw [hhom, Real.sq_sqrt hspos.le]
    have hfy : μ ≤ ((Real.sqrt s)⁻¹ • x) ⬝ᵥ M *ᵥ ((Real.sqrt s)⁻¹ • x) :=
      isMinOn_iff.mp hx₀min _ hyS
    rw [hfx]
    calc μ * s = s * μ := mul_comm _ _
      _ ≤ s * (((Real.sqrt s)⁻¹ • x) ⬝ᵥ M *ᵥ ((Real.sqrt s)⁻¹ • x)) :=
          mul_le_mul_of_nonneg_left hfy hspos.le

/-- **Entrywise quadratic-form bound.**  If every entry of `N` has absolute value at most `ε ≥ 0`,
then `|x ⬝ᵥ N *ᵥ x| ≤ n * ε * (x ⬝ᵥ x)`, by the triangle inequality and Cauchy–Schwarz. -/
theorem abs_dotProduct_mulVec_le {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hN : ∀ p q, |N p q| ≤ ε) (x : Fin n → ℝ) :
    |x ⬝ᵥ N *ᵥ x| ≤ (n : ℝ) * ε * (x ⬝ᵥ x) := by
  have hexp : x ⬝ᵥ N *ᵥ x = ∑ p, ∑ q, x p * N p q * x q := by
    rw [dotProduct]
    apply Finset.sum_congr rfl; intro p _
    rw [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  rw [hexp]
  have hstep : |∑ p, ∑ q, x p * N p q * x q| ≤ ε * (∑ p, |x p|) ^ (2 : ℕ) := by
    calc |∑ p, ∑ q, x p * N p q * x q|
        ≤ ∑ p, ∑ q, |x p| * ε * |x q| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          apply Finset.sum_le_sum; intro p _
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          apply Finset.sum_le_sum; intro q _
          rw [abs_mul, abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left (hN p q) (abs_nonneg _)
      _ = ε * (∑ p, |x p|) ^ (2 : ℕ) := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro p _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _; ring
  refine hstep.trans ?_
  have hsq : (∑ p, |x p|) ^ (2 : ℕ) ≤ (n : ℝ) * ∑ p, |x p| ^ (2 : ℕ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ)) (fun p => |x p|)
    simpa using h
  calc ε * (∑ p, |x p|) ^ (2 : ℕ) ≤ ε * ((n : ℝ) * ∑ p, |x p| ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hsq hε
    _ = (n : ℝ) * ε * (x ⬝ᵥ x) := by
        rw [dotProduct]
        simp_rw [sq_abs, ← sq]
        ring

/-- **Positive-definiteness is eventually preserved under entrywise convergence.**  If a family of
Hermitian matrices `M i` has entries converging (along a filter `l`) to those of a positive-definite
matrix `M₀`, then `M i` is positive definite eventually.  Proved from coercivity of `M₀` and the
entrywise perturbation bound: once every entry is within `μ / (n+1)` of `M₀`'s, the quadratic form of
`M i` stays coercive. -/
theorem posDef_eventually_of_tendsto {n : ℕ} {ι : Type*} {l : Filter ι}
    {M : ι → Matrix (Fin n) (Fin n) ℝ} {M₀ : Matrix (Fin n) (Fin n) ℝ}
    (hM₀ : M₀.PosDef) (hHerm : ∀ᶠ i in l, (M i).IsHermitian)
    (htend : ∀ p q, Tendsto (fun i => M i p q) l (𝓝 (M₀ p q))) :
    ∀ᶠ i in l, (M i).PosDef := by
  obtain ⟨μ, hμpos, hcoer⟩ := posDef_coercive hM₀
  set ε₀ : ℝ := μ / (n + 1) with hε₀
  have hε₀pos : 0 < ε₀ := div_pos hμpos (by positivity)
  have hclose : ∀ᶠ i in l, ∀ p q, |M i p q - M₀ p q| ≤ ε₀ := by
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_all]
    intro q
    filter_upwards [Metric.tendsto_nhds.mp (htend p q) ε₀ hε₀pos] with i hi
    rw [Real.dist_eq] at hi
    exact hi.le
  filter_upwards [hHerm, hclose] with i hHi hclosei
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hHi, fun x hx => ?_⟩
  rw [star_trivial]
  have hxpos : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne (by rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Ne.symm (fun h => hx ((dotProduct_self_eq_zero).mp h)))
  have hsplit : x ⬝ᵥ M i *ᵥ x = x ⬝ᵥ M₀ *ᵥ x + x ⬝ᵥ (M i - M₀) *ᵥ x := by
    have hMi : M i = M₀ + (M i - M₀) := by abel
    conv_lhs => rw [hMi]
    rw [add_mulVec, dotProduct_add]
  have hbound : |x ⬝ᵥ (M i - M₀) *ᵥ x| ≤ (n : ℝ) * ε₀ * (x ⬝ᵥ x) :=
    abs_dotProduct_mulVec_le _ hε₀pos.le (fun p q => by
      rw [Matrix.sub_apply]; exact hclosei p q) x
  have hlow : (n : ℝ) * ε₀ < μ := by
    rw [hε₀, ← mul_div_assoc, div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
    nlinarith [hμpos]
  have hc := hcoer x
  have habs := (abs_le.mp hbound).1
  nlinarith [hc, habs, hxpos, hlow, hsplit, mul_pos (sub_pos.mpr hlow) hxpos]

end GaloisForLFunctions.HTGeometry
