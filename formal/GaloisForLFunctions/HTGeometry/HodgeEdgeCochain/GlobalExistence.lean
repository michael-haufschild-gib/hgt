import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.Energy
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Global existence and uniqueness for the two-field edge-cochain system

This file formalises Lemma 2 of Boudourides, *Hodge Coercivity and Global Dynamics in Two-Field
Edge-Cochain Systems with MHD-Type Cancellation* (arXiv:2608.19360): for every initial datum the
system (5)–(6) has a unique global solution.

Mathlib supplies only local existence (Picard–Lindelöf), so the continuation step is built here.
The device is a *cut-off* of the whole vector field outside a ball of radius `R+1`.  Because the
cut-off multiplies the entire field by a scalar, the exact cancellation identity survives, so the
a priori energy bound `energy_le_apriori_scaled` applies to the truncated system *directly* — no
first-exit-time argument is needed.  Choosing `R` above the a priori bound on `[0,T]` makes the
cut-off equal to `1` along the trajectory, so the truncated solution is a genuine solution.

## Main results

* `exists_solution_of_bounded_lipschitz` — reusable ODE infrastructure: a globally bounded,
  globally Lipschitz time-independent field has a solution on every symmetric interval.
* `exists_isSolutionOn_Icc` — a solution of (5)–(6) on `[0,T]` for every `T`.
* `exists_isSolutionOn_Ici` — **Lemma 2**: a global solution on `[0,∞)`.
* `isSolutionOn_unique` — uniqueness.
-/

open Set Metric
open scoped InnerProductSpace NNReal

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

/-! ## Generic ODE infrastructure -/

section GenericODE

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Global solution for a bounded Lipschitz field.**  A time-independent vector field that is
globally bounded and globally Lipschitz admits, for every initial point and every `T`, a solution
on the whole interval `[-T, T]`.  Unlike the local Picard–Lindelöf statement this has no smallness
restriction on `T`, because the bound `L` does not grow with the radius. -/
theorem exists_solution_of_bounded_lipschitz {F : X → X} {L K : ℝ≥0}
    (hL : ∀ x, ‖F x‖ ≤ L) (hK : LipschitzWith K F) (x₀ : X) (T : ℝ≥0) :
    ∃ α : ℝ → X, α 0 = x₀ ∧
      ∀ t ∈ Ioo (-(T : ℝ)) (T : ℝ), HasDerivAt α (F (α t)) t := by
  have hmem : (0 : ℝ) ∈ Icc (-(T : ℝ)) (T : ℝ) := by
    have hT : (0 : ℝ) ≤ (T : ℝ) := T.coe_nonneg
    exact ⟨by linarith, hT⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => F)
      (tmin := -(T : ℝ)) (tmax := (T : ℝ)) ⟨0, hmem⟩ x₀ (L * T) 0 L K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => hL x)
      (hK.lipschitzOnWith.mono (subset_univ _)) ?_
    have hT : (0 : ℝ) ≤ (T : ℝ) := T.coe_nonneg
    have : max ((T : ℝ) - 0) (0 - -(T : ℝ)) = (T : ℝ) := by simp
    rw [show (⟨0, hmem⟩ : Icc (-(T : ℝ)) (T : ℝ)).1 = 0 from rfl, this]
    push_cast
    simp
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, hα0, fun t ht => ?_⟩
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end GenericODE

/-! ## A piecewise-linear cut-off -/

section Cutoff

/-- The cut-off `χ_R`: equal to `1` on `[0,R]`, to `0` beyond `R+1`, affine in between. -/
noncomputable def cutoff (R r : ℝ) : ℝ := max (min (R + 1 - r) 1) 0

theorem cutoff_nonneg (R r : ℝ) : 0 ≤ cutoff R r := le_max_right _ _

theorem cutoff_le_one (R r : ℝ) : cutoff R r ≤ 1 :=
  max_le (min_le_right _ _) zero_le_one

theorem cutoff_eq_one {R r : ℝ} (h : r ≤ R) : cutoff R r = 1 := by
  have h1 : (1 : ℝ) ≤ R + 1 - r := by linarith
  rw [cutoff, min_eq_right h1, max_eq_left zero_le_one]

theorem cutoff_eq_zero {R r : ℝ} (h : R + 1 ≤ r) : cutoff R r = 0 := by
  have h1 : R + 1 - r ≤ 0 := by linarith
  rw [cutoff, min_eq_left (le_trans h1 zero_le_one), max_eq_right h1]

theorem abs_cutoff_sub_le (R r r' : ℝ) : |cutoff R r - cutoff R r'| ≤ |r - r'| := by
  have hmax : ∀ a b : ℝ, |max a 0 - max b 0| ≤ |a - b| := fun a b => by
    rcases le_total a b with h | h <;> rcases le_total a 0 with ha | ha <;>
      rcases le_total b 0 with hb | hb <;>
      simp [abs_le, *] <;> constructor <;> linarith [abs_nonneg (a - b),
        le_abs_self (a - b), neg_abs_le (a - b)]
  have hmin : ∀ a b : ℝ, |min a 1 - min b 1| ≤ |a - b| := fun a b => by
    rcases le_total a b with h | h <;> rcases le_total a 1 with ha | ha <;>
      rcases le_total b 1 with hb | hb <;>
      simp [abs_le, *] <;> constructor <;> linarith [abs_nonneg (a - b),
        le_abs_self (a - b), neg_abs_le (a - b)]
  refine le_trans (hmax _ _) (le_trans (hmin _ _) (le_of_eq ?_))
  rw [show R + 1 - r - (R + 1 - r') = -(r - r') by ring, abs_neg]

end Cutoff

/-! ## The truncated two-field vector field -/

section TruncatedField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (nu eta : ℝ) (f g : E)

/-- The full two-field vector field of (5)–(6) on the product phase space. -/
noncomputable def fullField : E × E → E × E :=
  fun p => (velocityField A B nu f p.1 p.2, magneticField A B eta g p.1 p.2)

/-- The vector field cut off outside the ball of radius `R + 1`.  The cut-off is a *scalar*
multiple of the whole field, so the exact cancellation identity is preserved. -/
noncomputable def truncField (R : ℝ) : E × E → E × E :=
  fun p => cutoff R ‖p‖ • fullField A B nu eta f g p

/-- The uniform bound on the truncated field. -/
noncomputable def truncBound (R : ℝ) : ℝ :=
  (nu + eta) * ‖A‖ * (R + 1) + 2 * ‖B‖ * (R + 1) ^ 2 + ‖f‖ + ‖g‖

/-- The Lipschitz modulus of the full field on the ball of radius `R + 1`. -/
noncomputable def fieldLip (R : ℝ) : ℝ := (nu + eta) * ‖A‖ + 4 * ‖B‖ * (R + 1)

variable {A B nu eta f g}

theorem truncBound_nonneg (hnu : 0 ≤ nu) (heta : 0 ≤ eta) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ truncBound A B nu eta f g R := by
  have h1 : (0 : ℝ) ≤ R + 1 := by linarith
  have := norm_nonneg A
  have := norm_nonneg B
  have := norm_nonneg f
  have := norm_nonneg g
  unfold truncBound
  positivity

theorem fieldLip_nonneg (hnu : 0 ≤ nu) (heta : 0 ≤ eta) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ fieldLip A B nu eta R := by
  have h1 : (0 : ℝ) ≤ R + 1 := by linarith
  have := norm_nonneg A
  have := norm_nonneg B
  unfold fieldLip
  positivity

theorem norm_velocityField_le (hnu : 0 ≤ nu) {M : ℝ} {u h : E} (hu : ‖u‖ ≤ M) (hh : ‖h‖ ≤ M) :
    ‖velocityField A B nu f u h‖ ≤ nu * ‖A‖ * M + 2 * ‖B‖ * M ^ 2 + ‖f‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg u) hu
  have h1 : ‖-(nu • A u)‖ ≤ nu * ‖A‖ * M := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnu]
    have hA1 : ‖A u‖ ≤ ‖A‖ * ‖u‖ := A.le_opNorm u
    have hA2 : ‖A‖ * ‖u‖ ≤ ‖A‖ * M := mul_le_mul_of_nonneg_left hu (norm_nonneg A)
    nlinarith [norm_nonneg (A u)]
  have hsq : ∀ x : E, ‖x‖ ≤ M → ‖B x x‖ ≤ ‖B‖ * M ^ 2 := by
    intro x hx
    refine le_trans (B.le_opNorm₂ x x) ?_
    have hprod : ‖x‖ * ‖x‖ ≤ M * M := mul_le_mul hx hx (norm_nonneg x) hM
    have := mul_le_mul_of_nonneg_left hprod (norm_nonneg B)
    nlinarith [this]
  have h2 := hsq u hu
  have h3 := hsq h hh
  have e : velocityField A B nu f u h = -(nu • A u) + B u u + -(B h h) + f := by
    simp only [velocityField]; abel
  have hsplit : ‖velocityField A B nu f u h‖
      ≤ ‖-(nu • A u)‖ + ‖B u u‖ + ‖B h h‖ + ‖f‖ := by
    rw [e]
    have t1 := norm_add_le (-(nu • A u) + B u u + -(B h h)) f
    have t2 := norm_add_le (-(nu • A u) + B u u) (-(B h h))
    have t3 := norm_add_le (-(nu • A u)) (B u u)
    have t4 : ‖-(B h h)‖ = ‖B h h‖ := norm_neg _
    linarith
  linarith

theorem norm_magneticField_le (heta : 0 ≤ eta) {M : ℝ} {u h : E} (hu : ‖u‖ ≤ M)
    (hh : ‖h‖ ≤ M) :
    ‖magneticField A B eta g u h‖ ≤ eta * ‖A‖ * M + 2 * ‖B‖ * M ^ 2 + ‖g‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg u) hu
  have h1 : ‖-(eta • A h)‖ ≤ eta * ‖A‖ * M := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg heta]
    have hA1 : ‖A h‖ ≤ ‖A‖ * ‖h‖ := A.le_opNorm h
    have hA2 : ‖A‖ * ‖h‖ ≤ ‖A‖ * M := mul_le_mul_of_nonneg_left hh (norm_nonneg A)
    nlinarith [norm_nonneg (A h)]
  have hmix : ∀ x y : E, ‖x‖ ≤ M → ‖y‖ ≤ M → ‖B x y‖ ≤ ‖B‖ * M ^ 2 := by
    intro x y hx hy
    refine le_trans (B.le_opNorm₂ x y) ?_
    have hprod : ‖x‖ * ‖y‖ ≤ M * M := mul_le_mul hx hy (norm_nonneg y) hM
    have := mul_le_mul_of_nonneg_left hprod (norm_nonneg B)
    nlinarith [this]
  have h2 := hmix u h hu hh
  have h3 := hmix h u hh hu
  have e : magneticField A B eta g u h = -(eta • A h) + B u h + -(B h u) + g := by
    simp only [magneticField]; abel
  have hsplit : ‖magneticField A B eta g u h‖
      ≤ ‖-(eta • A h)‖ + ‖B u h‖ + ‖B h u‖ + ‖g‖ := by
    rw [e]
    have t1 := norm_add_le (-(eta • A h) + B u h + -(B h u)) g
    have t2 := norm_add_le (-(eta • A h) + B u h) (-(B h u))
    have t3 := norm_add_le (-(eta • A h)) (B u h)
    have t4 : ‖-(B h u)‖ = ‖B h u‖ := norm_neg _
    linarith
  linarith

theorem norm_fullField_le (hnu : 0 ≤ nu) (heta : 0 ≤ eta) {M : ℝ} {p : E × E} (hp : ‖p‖ ≤ M) :
    ‖fullField A B nu eta f g p‖ ≤ (nu + eta) * ‖A‖ * M + 2 * ‖B‖ * M ^ 2 + ‖f‖ + ‖g‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg p) hp
  have h1 : ‖p.1‖ ≤ M := le_trans (norm_fst_le p) hp
  have h2 : ‖p.2‖ ≤ M := le_trans (norm_snd_le p) hp
  have hv := norm_velocityField_le (A := A) (B := B) (f := f) hnu h1 h2
  have hm := norm_magneticField_le (A := A) (B := B) (g := g) heta h1 h2
  have hAnn := norm_nonneg A
  have hfnn := norm_nonneg f
  have hgnn := norm_nonneg g
  have hMA : 0 ≤ ‖A‖ * M := mul_nonneg hAnn hM
  have hkey : ‖fullField A B nu eta f g p‖
      = max ‖velocityField A B nu f p.1 p.2‖ ‖magneticField A B eta g p.1 p.2‖ :=
    Prod.norm_def _
  rw [hkey]
  refine max_le ?_ ?_ <;> nlinarith

theorem norm_fullField_sub_le (hnu : 0 ≤ nu) (heta : 0 ≤ eta) {M : ℝ} {p q : E × E}
    (hp : ‖p‖ ≤ M) (hq : ‖q‖ ≤ M) :
    ‖fullField A B nu eta f g p - fullField A B nu eta f g q‖
      ≤ fieldLip A B nu eta (M - 1) * ‖p - q‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg p) hp
  have hp1 : ‖p.1‖ ≤ M := le_trans (norm_fst_le p) hp
  have hp2 : ‖p.2‖ ≤ M := le_trans (norm_snd_le p) hp
  have hq1 : ‖q.1‖ ≤ M := le_trans (norm_fst_le q) hq
  have hq2 : ‖q.2‖ ≤ M := le_trans (norm_snd_le q) hq
  have hd1 : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have hd2 : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  have hAnn := norm_nonneg A
  have hBnn := norm_nonneg B
  have hdnn : (0 : ℝ) ≤ ‖p - q‖ := norm_nonneg _
  -- velocity component
  have hVsplit : ‖velocityField A B nu f p.1 p.2 - velocityField A B nu f q.1 q.2‖
      ≤ ‖-(nu • A (p.1 - q.1))‖ + ‖B p.1 p.1 - B q.1 q.1‖ + ‖B p.2 p.2 - B q.2 q.2‖ := by
    rw [velocityField_sub]
    have t1 := norm_sub_le (-(nu • A (p.1 - q.1)) + (B p.1 p.1 - B q.1 q.1))
      (B p.2 p.2 - B q.2 q.2)
    have t2 := norm_add_le (-(nu • A (p.1 - q.1))) (B p.1 p.1 - B q.1 q.1)
    linarith
  have hVA : ‖-(nu • A (p.1 - q.1))‖ ≤ nu * ‖A‖ * ‖p - q‖ := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnu]
    have hA1 : ‖A (p.1 - q.1)‖ ≤ ‖A‖ * ‖p.1 - q.1‖ := A.le_opNorm _
    have hA2 : ‖A‖ * ‖p.1 - q.1‖ ≤ ‖A‖ * ‖p - q‖ := mul_le_mul_of_nonneg_left hd1 hAnn
    nlinarith [norm_nonneg (A (p.1 - q.1))]
  have hVB1 : ‖B p.1 p.1 - B q.1 q.1‖ ≤ 2 * ‖B‖ * M * ‖p - q‖ := by
    refine le_trans (norm_interaction_diag_sub_le B hp1 hq1) ?_
    exact mul_le_mul_of_nonneg_left hd1 (by positivity)
  have hVB2 : ‖B p.2 p.2 - B q.2 q.2‖ ≤ 2 * ‖B‖ * M * ‖p - q‖ := by
    refine le_trans (norm_interaction_diag_sub_le B hp2 hq2) ?_
    exact mul_le_mul_of_nonneg_left hd2 (by positivity)
  -- magnetic component
  have hMsplit : ‖magneticField A B eta g p.1 p.2 - magneticField A B eta g q.1 q.2‖
      ≤ ‖-(eta • A (p.2 - q.2))‖ + ‖B p.1 p.2 - B q.1 q.2‖ + ‖B p.2 p.1 - B q.2 q.1‖ := by
    rw [magneticField_sub]
    have t1 := norm_sub_le (-(eta • A (p.2 - q.2)) + (B p.1 p.2 - B q.1 q.2))
      (B p.2 p.1 - B q.2 q.1)
    have t2 := norm_add_le (-(eta • A (p.2 - q.2))) (B p.1 p.2 - B q.1 q.2)
    linarith
  have hMA : ‖-(eta • A (p.2 - q.2))‖ ≤ eta * ‖A‖ * ‖p - q‖ := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg heta]
    have hA1 : ‖A (p.2 - q.2)‖ ≤ ‖A‖ * ‖p.2 - q.2‖ := A.le_opNorm _
    have hA2 : ‖A‖ * ‖p.2 - q.2‖ ≤ ‖A‖ * ‖p - q‖ := mul_le_mul_of_nonneg_left hd2 hAnn
    nlinarith [norm_nonneg (A (p.2 - q.2))]
  have hMB1 : ‖B p.1 p.2 - B q.1 q.2‖ ≤ 2 * ‖B‖ * M * ‖p - q‖ := by
    refine le_trans (norm_interaction_mixed_sub_le B hp1 hp2 hq1 hq2) ?_
    have : ‖p.1 - q.1‖ + ‖p.2 - q.2‖ ≤ 2 * ‖p - q‖ := by linarith
    nlinarith [mul_nonneg hBnn hM]
  have hMB2 : ‖B p.2 p.1 - B q.2 q.1‖ ≤ 2 * ‖B‖ * M * ‖p - q‖ := by
    refine le_trans (norm_interaction_mixed_sub_le B hp2 hp1 hq2 hq1) ?_
    have : ‖p.2 - q.2‖ + ‖p.1 - q.1‖ ≤ 2 * ‖p - q‖ := by linarith
    nlinarith [mul_nonneg hBnn hM]
  have hkey : ‖fullField A B nu eta f g p - fullField A B nu eta f g q‖
      = max ‖velocityField A B nu f p.1 p.2 - velocityField A B nu f q.1 q.2‖
          ‖magneticField A B eta g p.1 p.2 - magneticField A B eta g q.1 q.2‖ :=
    Prod.norm_def _
  have hMeq : M - 1 + 1 = M := by ring
  rw [hkey, fieldLip, hMeq]
  refine max_le ?_ ?_ <;> nlinarith [mul_nonneg (mul_nonneg hnu hAnn) hdnn,
    mul_nonneg (mul_nonneg heta hAnn) hdnn]


theorem norm_truncField_le (hnu : 0 ≤ nu) (heta : 0 ≤ eta) {R : ℝ} (hR : 0 ≤ R) (p : E × E) :
    ‖truncField A B nu eta f g R p‖ ≤ truncBound A B nu eta f g R := by
  have hc0 := cutoff_nonneg R ‖p‖
  have hc1 := cutoff_le_one R ‖p‖
  have hnorm : ‖truncField A B nu eta f g R p‖
      = cutoff R ‖p‖ * ‖fullField A B nu eta f g p‖ := by
    rw [truncField, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  rcases le_or_gt ‖p‖ (R + 1) with hp | hp
  · have hb := norm_fullField_le (A := A) (B := B) (f := f) (g := g) hnu heta hp
    have hfnn : 0 ≤ ‖fullField A B nu eta f g p‖ := norm_nonneg _
    rw [hnorm, truncBound]
    nlinarith
  · have hc : cutoff R ‖p‖ = 0 := cutoff_eq_zero (le_of_lt hp)
    rw [hnorm, hc, zero_mul]
    exact truncBound_nonneg hnu heta hR

theorem norm_truncField_sub_le (hnu : 0 ≤ nu) (heta : 0 ≤ eta) {R : ℝ} (hR : 0 ≤ R)
    (p q : E × E) :
    ‖truncField A B nu eta f g R p - truncField A B nu eta f g R q‖
      ≤ (truncBound A B nu eta f g R + fieldLip A B nu eta R) * ‖p - q‖ := by
  have hLB := truncBound_nonneg (A := A) (B := B) (f := f) (g := g) hnu heta hR
  have hLN := fieldLip_nonneg (A := A) (B := B) (nu := nu) (eta := eta) hnu heta hR
  have hdnn : (0 : ℝ) ≤ ‖p - q‖ := norm_nonneg _
  have hcut : |cutoff R ‖p‖ - cutoff R ‖q‖| ≤ ‖p - q‖ :=
    le_trans (abs_cutoff_sub_le R ‖p‖ ‖q‖) (abs_norm_sub_norm_le p q)
  rcases le_or_gt ‖p‖ (R + 1) with hp | hp
  · rcases le_or_gt ‖q‖ (R + 1) with hq | hq
    · have hsplit : truncField A B nu eta f g R p - truncField A B nu eta f g R q
          = (cutoff R ‖p‖ - cutoff R ‖q‖) • fullField A B nu eta f g p
            + cutoff R ‖q‖ • (fullField A B nu eta f g p - fullField A B nu eta f g q) := by
        simp only [truncField, sub_smul, smul_sub]
        abel
      have hb := norm_fullField_le (A := A) (B := B) (f := f) (g := g) hnu heta hp
      have hl := norm_fullField_sub_le (A := A) (B := B) (f := f) (g := g) hnu heta hp hq
      have hMeq : R + 1 - 1 = R := by ring
      rw [hMeq] at hl
      have hc0 := cutoff_nonneg R ‖q‖
      have hc1 := cutoff_le_one R ‖q‖
      have hfnn : 0 ≤ ‖fullField A B nu eta f g p‖ := norm_nonneg _
      have hsnn : 0 ≤ ‖fullField A B nu eta f g p - fullField A B nu eta f g q‖ := norm_nonneg _
      have t1 : ‖(cutoff R ‖p‖ - cutoff R ‖q‖) • fullField A B nu eta f g p‖
          ≤ ‖p - q‖ * truncBound A B nu eta f g R := by
        rw [norm_smul, Real.norm_eq_abs]
        have hbb : ‖fullField A B nu eta f g p‖ ≤ truncBound A B nu eta f g R := by
          rw [truncBound]; linarith
        exact mul_le_mul hcut hbb hfnn hdnn
      have t2 : ‖cutoff R ‖q‖ • (fullField A B nu eta f g p - fullField A B nu eta f g q)‖
          ≤ fieldLip A B nu eta R * ‖p - q‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
        nlinarith
      have t3 := norm_add_le ((cutoff R ‖p‖ - cutoff R ‖q‖) • fullField A B nu eta f g p)
        (cutoff R ‖q‖ • (fullField A B nu eta f g p - fullField A B nu eta f g q))
      rw [hsplit]
      nlinarith
    · have hcq : cutoff R ‖q‖ = 0 := cutoff_eq_zero (le_of_lt hq)
      have hsplit : truncField A B nu eta f g R p - truncField A B nu eta f g R q
          = cutoff R ‖p‖ • fullField A B nu eta f g p := by
        simp [truncField, hcq]
      have hb := norm_fullField_le (A := A) (B := B) (f := f) (g := g) hnu heta hp
      have hc0 := cutoff_nonneg R ‖p‖
      have hfnn : 0 ≤ ‖fullField A B nu eta f g p‖ := norm_nonneg _
      have hcp : cutoff R ‖p‖ ≤ ‖p - q‖ := by
        have : |cutoff R ‖p‖ - cutoff R ‖q‖| = cutoff R ‖p‖ := by
          rw [hcq, sub_zero, abs_of_nonneg hc0]
        linarith [hcut, this.symm ▸ hcut]
      have hbb : ‖fullField A B nu eta f g p‖ ≤ truncBound A B nu eta f g R := by
        rw [truncBound]; linarith
      rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      nlinarith
  · rcases le_or_gt ‖q‖ (R + 1) with hq | hq
    · have hcp : cutoff R ‖p‖ = 0 := cutoff_eq_zero (le_of_lt hp)
      have hsplit : truncField A B nu eta f g R p - truncField A B nu eta f g R q
          = -(cutoff R ‖q‖ • fullField A B nu eta f g q) := by
        simp [truncField, hcp]
      have hb := norm_fullField_le (A := A) (B := B) (f := f) (g := g) hnu heta hq
      have hc0 := cutoff_nonneg R ‖q‖
      have hfnn : 0 ≤ ‖fullField A B nu eta f g q‖ := norm_nonneg _
      have hcq : cutoff R ‖q‖ ≤ ‖p - q‖ := by
        have hz : |cutoff R ‖p‖ - cutoff R ‖q‖| = cutoff R ‖q‖ := by
          rw [hcp, zero_sub, abs_neg, abs_of_nonneg hc0]
        linarith [hcut, hz.symm ▸ hcut]
      have hbb : ‖fullField A B nu eta f g q‖ ≤ truncBound A B nu eta f g R := by
        rw [truncBound]; linarith
      rw [hsplit, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      nlinarith
    · have hcp : cutoff R ‖p‖ = 0 := cutoff_eq_zero (le_of_lt hp)
      have hcq : cutoff R ‖q‖ = 0 := cutoff_eq_zero (le_of_lt hq)
      have : truncField A B nu eta f g R p - truncField A B nu eta f g R q = 0 := by
        simp [truncField, hcp, hcq]
      rw [this, norm_zero]
      positivity


end TruncatedField

/-! ## Global existence -/

section GlobalSolutions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E} {nu eta : ℝ} {f g : E}

/-- **Existence on every compact interval.**  The cut-off field is globally bounded and globally
Lipschitz, hence has a solution on `[0,T]`; the a priori energy bound forces the cut-off to equal
`1` along that solution, so it solves the original system. -/
theorem exists_isSolutionOn_Icc (hB : IsCancelling B) (hA : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ)
    (hnu : 0 ≤ nu) (heta : 0 ≤ eta) (u₀ h₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u h : ℝ → E, u 0 = u₀ ∧ h 0 = h₀ ∧ IsSolutionOn A B nu eta f g u h (Icc 0 T) := by
  classical
  set rho : ℝ := (‖u₀‖ ^ 2 + ‖h₀‖ ^ 2) * Real.exp T + (‖f‖ ^ 2 + ‖g‖ ^ 2) * (Real.exp T - 1)
    with hrhodef
  have hexpT : (1 : ℝ) ≤ Real.exp T := Real.one_le_exp hT
  have hrho0 : 0 ≤ rho := by
    have h1 : (0 : ℝ) ≤ ‖u₀‖ ^ 2 + ‖h₀‖ ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ Real.exp T - 1 := by linarith
    have h4 : (0 : ℝ) ≤ Real.exp T := le_trans zero_le_one hexpT
    rw [hrhodef]
    positivity
  set R : ℝ := Real.sqrt rho with hRdef
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  set L : ℝ≥0 := ⟨truncBound A B nu eta f g R, truncBound_nonneg hnu heta hR0⟩ with hLdef
  have hKnn : 0 ≤ truncBound A B nu eta f g R + fieldLip A B nu eta R :=
    add_nonneg (truncBound_nonneg hnu heta hR0) (fieldLip_nonneg hnu heta hR0)
  set K : ℝ≥0 := ⟨truncBound A B nu eta f g R + fieldLip A B nu eta R, hKnn⟩ with hKdef
  have hbound : ∀ x : E × E, ‖truncField A B nu eta f g R x‖ ≤ (L : ℝ) :=
    fun x => norm_truncField_le hnu heta hR0 x
  have hlip : LipschitzWith K (truncField A B nu eta f g R) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact norm_truncField_sub_le hnu heta hR0 x y
  obtain ⟨alpha, halpha0, halpha⟩ :=
    exists_solution_of_bounded_lipschitz hbound hlip (u₀, h₀) ⟨T + 1, by linarith⟩
  refine ⟨fun t => (alpha t).1, fun t => (alpha t).2, by simp [halpha0], by simp [halpha0], ?_⟩
  -- the components form a rescaled solution
  have hsub : Icc (0 : ℝ) T ⊆ Ioo (-((T : ℝ) + 1)) ((T : ℝ) + 1) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcoe : ((⟨T + 1, by linarith⟩ : ℝ≥0) : ℝ) = T + 1 := rfl
  have hscaled : IsScaledSolutionOn A B nu eta f g (fun t => cutoff R ‖alpha t‖)
      (fun t => (alpha t).1) (fun t => (alpha t).2) (Icc 0 T) := by
    intro t ht
    have hd : HasDerivAt alpha (truncField A B nu eta f g R (alpha t)) t := by
      have := halpha t (by rw [hcoe] at *; exact hsub ht)
      exact this
    constructor
    · have := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hd
      simpa [truncField, fullField] using this
    · have := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hd
      simpa [truncField, fullField] using this
  -- the a priori energy bound
  have hE := energy_le_apriori_scaled hB hA hnu heta (fun t => cutoff_nonneg R ‖alpha t‖)
    (fun t => cutoff_le_one R ‖alpha t‖) hscaled
  have hEle : ∀ t ∈ Icc (0 : ℝ) T,
      energy (fun t => (alpha t).1) (fun t => (alpha t).2) t ≤ rho := by
    intro t ht
    have h1 := hE t ht
    have h2 : Real.exp t ≤ Real.exp T := Real.exp_le_exp.mpr ht.2
    have h0 : energy (fun t => (alpha t).1) (fun t => (alpha t).2) 0 = ‖u₀‖ ^ 2 + ‖h₀‖ ^ 2 := by
      simp [energy, halpha0]
    rw [h0] at h1
    have hc1 : (0 : ℝ) ≤ ‖u₀‖ ^ 2 + ‖h₀‖ ^ 2 := by positivity
    have hc2 : (0 : ℝ) ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by positivity
    rw [hrhodef]
    nlinarith
  -- so the cut-off equals one along the trajectory
  have hcut1 : ∀ t ∈ Icc (0 : ℝ) T, cutoff R ‖alpha t‖ = 1 := by
    intro t ht
    refine cutoff_eq_one ?_
    have hEt := hEle t ht
    have h1 : ‖(alpha t).1‖ ^ 2 ≤ rho := by
      have : (0 : ℝ) ≤ ‖(alpha t).2‖ ^ 2 := by positivity
      simp only [energy] at hEt
      linarith
    have h2 : ‖(alpha t).2‖ ^ 2 ≤ rho := by
      have : (0 : ℝ) ≤ ‖(alpha t).1‖ ^ 2 := by positivity
      simp only [energy] at hEt
      linarith
    have k1 : ‖(alpha t).1‖ ≤ R := by
      rw [hRdef]
      exact (Real.le_sqrt (norm_nonneg _)).mpr h1
    have k2 : ‖(alpha t).2‖ ≤ R := by
      rw [hRdef]
      exact (Real.le_sqrt (norm_nonneg _)).mpr h2
    rw [Prod.norm_def]
    exact max_le k1 k2
  intro t ht
  have hs := hscaled t ht
  rw [hcut1 t ht, one_smul] at hs
  exact hs

end GlobalSolutions

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
