import GaloisForLFunctions.HTGeometry.StrongConvergenceDense
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Uniformly coercive families have convergent solutions

A self-adjoint form bounded below by `δ` moves norms up: the solution of `B x = y` obeys
`‖x‖ ≤ δ⁻¹ ‖y‖`.  If a whole family is uniformly coercive and uniformly bounded, and converges
strongly to a positive multiple of the identity on a dense set, then the solutions of `B_j x_j = s_j`
converge — *strongly*, not merely weakly — to `c⁻¹ s` for any norm-convergent sources `s_j → s`, and
the response pairings converge to `‖s‖²/c`.

The estimate is the whole proof: `B_j (x_j − c⁻¹ s) = s_j − c⁻¹ B_j s`, and coercivity turns the
right side, which tends to zero, into a bound on the left.  Two families with a common strong limit
therefore have the same response, which is source blindness.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Coercivity moves norms up.** -/
private theorem norm_le_of_coercive {B : H →L[ℂ] H} {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ x : H, δ * ‖x‖ ^ (2 : ℕ) ≤ (inner ℂ (B x) x).re) (x : H) :
    ‖x‖ ≤ δ⁻¹ * ‖B x‖ := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · have hx : 0 < ‖x‖ := norm_pos_iff.mpr h
    have h1 : δ * ‖x‖ ^ (2 : ℕ) ≤ ‖B x‖ * ‖x‖ := by
      refine le_trans (hcoer x) (le_trans (Complex.re_le_norm _) ?_)
      exact norm_inner_le_norm _ _
    rw [inv_mul_eq_div, le_div_iff₀ hδ]
    nlinarith [h1, hx]

/-- **The solutions converge strongly.** -/
theorem tendsto_solution_of_coercive_family
    {B : ℕ → H →L[ℂ] H} {δ M c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hM0 : 0 ≤ M)
    (hcoer : ∀ j, ∀ y : H, δ * ‖y‖ ^ (2 : ℕ) ≤ (inner ℂ (B j y) y).re)
    (hbound : ∀ j, ‖B j‖ ≤ M) (hcM : ‖(c : ℂ)‖ ≤ M)
    {D : Set H} (hD : Dense D)
    (hconv : ∀ g ∈ D, Tendsto (fun j => B j g) atTop (𝓝 ((c : ℂ) • g)))
    {s : H} {sseq : ℕ → H} (hs : Tendsto sseq atTop (𝓝 s))
    {x : ℕ → H} (hx : ∀ j, B j (x j) = sseq j) :
    Tendsto x atTop (𝓝 ((c : ℂ)⁻¹ • s)) := by
  have hcne : (c : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hc.ne'
  set S : H →L[ℂ] H := (c : ℂ) • ContinuousLinearMap.id ℂ H with hSdef
  have hSbound : ‖S‖ ≤ M := by
    rw [hSdef, norm_smul]
    refine le_trans (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)) ?_
    rw [mul_one]
    exact hcM
  have hstrong : ∀ v : H, Tendsto (fun j => B j v) atTop (𝓝 (S v)) := by
    intro v
    refine tendsto_of_dense_of_uniform_bound hM0 (Filter.Eventually.of_forall hbound) hSbound hD
      (fun g hg => ?_) v
    exact hconv g hg
  have hdiff : Tendsto (fun j => sseq j - (c : ℂ)⁻¹ • B j s) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (c : ℂ)⁻¹ • B j s) atTop (𝓝 ((c : ℂ)⁻¹ • S s)) :=
      (hstrong s).const_smul _
    have h2 : (c : ℂ)⁻¹ • S s = s := by
      have hSs : S s = (c : ℂ) • s := by rw [hSdef]; rfl
      rw [hSs, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [h2] at h1
    simpa using hs.sub h1
  have hdom : ∀ j, ‖x j - (c : ℂ)⁻¹ • s‖ ≤ δ⁻¹ * ‖sseq j - (c : ℂ)⁻¹ • B j s‖ := by
    intro j
    have hBapply : B j (x j - (c : ℂ)⁻¹ • s) = sseq j - (c : ℂ)⁻¹ • B j s := by
      rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul, hx j]
    have h := norm_le_of_coercive hδ (hcoer j) (x j - (c : ℂ)⁻¹ • s)
    rwa [hBapply] at h
  have hgo : Tendsto (fun j => δ⁻¹ * ‖sseq j - (c : ℂ)⁻¹ • B j s‖) atTop (𝓝 0) := by
    have h := hdiff.norm
    have h2 := h.const_mul δ⁻¹
    simpa using h2
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun j => norm_nonneg _) hdom hgo)

/-- **Source blindness.**  The response pairing converges to `‖s‖²/c`, so any two families with the
same coercivity, bound and strong limit have the same limiting response. -/
theorem tendsto_inner_solution_of_coercive_family
    {B : ℕ → H →L[ℂ] H} {δ M c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hM0 : 0 ≤ M)
    (hcoer : ∀ j, ∀ y : H, δ * ‖y‖ ^ (2 : ℕ) ≤ (inner ℂ (B j y) y).re)
    (hbound : ∀ j, ‖B j‖ ≤ M) (hcM : ‖(c : ℂ)‖ ≤ M)
    {D : Set H} (hD : Dense D)
    (hconv : ∀ g ∈ D, Tendsto (fun j => B j g) atTop (𝓝 ((c : ℂ) • g)))
    {s : H} {sseq : ℕ → H} (hs : Tendsto sseq atTop (𝓝 s))
    {x : ℕ → H} (hx : ∀ j, B j (x j) = sseq j) :
    Tendsto (fun j => (inner ℂ (sseq j) (x j) : ℂ)) atTop
      (𝓝 (((‖s‖ ^ (2 : ℕ) : ℝ) : ℂ) / (c : ℂ))) := by
  have hxlim := tendsto_solution_of_coercive_family hδ hc hM0 hcoer hbound hcM hD hconv hs hx
  have hinner : Tendsto (fun j => (inner ℂ (sseq j) (x j) : ℂ)) atTop
      (𝓝 (inner ℂ s ((c : ℂ)⁻¹ • s))) := by
    exact Tendsto.inner hs hxlim
  have hval : (inner ℂ s ((c : ℂ)⁻¹ • s) : ℂ) = ((‖s‖ ^ (2 : ℕ) : ℝ) : ℂ) / (c : ℂ) := by
    rw [inner_smul_right]
    have hself : (inner ℂ s s : ℂ) = ((‖s‖ : ℂ) ^ (2 : ℕ)) := inner_self_eq_norm_sq_to_K s
    rw [hself]
    push_cast
    ring
  rwa [hval] at hinner

end GaloisForLFunctions.HTGeometry
