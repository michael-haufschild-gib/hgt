import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The renormalization survival law

A *regularized family* is a family of real quadratic forms `Q_r` on a finite set of modes whose
renormalized part `Q_r − s_r B` converges to a limit form `A`. The divergent part `s_r B` is the
*counterterm*; its null cone `{x : B(x, x) = 0}` is the *survival cone*.

* **Survival** (`quad_nonneg_of_regularized`). If every `Q_r` is positive semidefinite, the limit
  `A` is nonnegative on the survival cone, whatever the divergence `s_r` does.
* **The counterterm of a positive regularization is positive** (`counterterm_nonneg`) when
  `s_r → +∞`.
* **The counterterm is an invariant** (`counterterm_eq_smul`, `survivalCone_eq_of_regularized`).
  Two renormalizations of one family with divergent coefficients have proportional counterterms;
  the survival cone does not depend on the renormalization scheme.
* **Finsler–Debreu converse** (`exists_quad_add_smul_pos`). If `B ⪰ 0` and `A` is positive on the
  survival cone minus the origin, then `A + sB` is positive definite for all large `s`
  (compactness of the unit sphere).
* **The survival equivalence** (`quad_nonneg_on_survivalCone_iff`). For `B ⪰ 0`: `A ≥ 0` on the
  survival cone iff `A + sB + εI` is eventually positive for every `ε > 0`.
* **Scalar counterterms carry nothing** (`survivalCone_one`, `exists_quad_add_smul_one_pos`). For
  the identity counterterm the survival cone is `{0}` and every symmetric form is the renormalized
  limit of positive definite forms.
* **Rank-one counterterms** (`quad_vecMulVec_self`, `mem_survivalCone_vecMulVec_iff`). For
  `B = v vᵀ` the survival cone is the hyperplane `⟪v, x⟫ = 0`.

So positivity passes through a scale limit exactly on the survival cone of the counterterm: a
scalar divergence destroys all of it, a rank-`k` divergence leaves codimension `k`.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

variable {ι : Type*} [Fintype ι]

/-- The quadratic form `x ↦ Σ_{i,j} x_i A_{ij} x_j` of a real kernel. -/
def quad (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := ∑ i, ∑ j, x i * A i j * x j

/-- The survival cone of a counterterm `B`: its null vectors. -/
def survivalCone (B : Matrix ι ι ℝ) : Set (ι → ℝ) := {x | quad B x = 0}

theorem quad_add (A B : Matrix ι ι ℝ) (x : ι → ℝ) : quad (A + B) x = quad A x + quad B x := by
  simp only [quad, Matrix.add_apply, mul_add, add_mul, sum_add_distrib]

theorem quad_smul (c : ℝ) (A : Matrix ι ι ℝ) (x : ι → ℝ) : quad (c • A) x = c * quad A x := by
  simp only [quad, Matrix.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem quad_sub (A B : Matrix ι ι ℝ) (x : ι → ℝ) : quad (A - B) x = quad A x - quad B x := by
  simp only [quad, Matrix.sub_apply, mul_sub, sub_mul, sum_sub_distrib]

/-- The form is homogeneous of degree two. -/
theorem quad_smul_vec (A : Matrix ι ι ℝ) (t : ℝ) (x : ι → ℝ) :
    quad A (t • x) = t ^ 2 * quad A x := by
  simp only [quad, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem quad_zero_vec (A : Matrix ι ι ℝ) : quad A 0 = 0 := by simp [quad]

theorem continuous_quad (A : Matrix ι ι ℝ) : Continuous (quad A) := by
  unfold quad
  fun_prop

/-- The identity form is the squared Euclidean norm. -/
theorem quad_one [DecidableEq ι] (x : ι → ℝ) : quad (1 : Matrix ι ι ℝ) x = ∑ i, x i ^ 2 := by
  simp only [quad, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    sum_ite_eq, mem_univ, if_true]
  exact sum_congr rfl fun i _ => by ring

/-- A rank-one counterterm `v vᵀ` has form `⟪v, x⟫²`. -/
theorem quad_vecMulVec_self (v x : ι → ℝ) :
    quad (Matrix.vecMulVec v v) x = (∑ i, v i * x i) ^ 2 := by
  simp only [quad, Matrix.vecMulVec_apply, sq, sum_mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- The survival cone of a rank-one counterterm is the hyperplane orthogonal to its vector. -/
theorem mem_survivalCone_vecMulVec_iff (v x : ι → ℝ) :
    x ∈ survivalCone (Matrix.vecMulVec v v) ↔ ∑ i, v i * x i = 0 := by
  simp only [survivalCone, Set.mem_setOf_eq, quad_vecMulVec_self, sq_eq_zero_iff]

/-- The survival cone of the identity counterterm is the origin. -/
theorem survivalCone_one [DecidableEq ι] : survivalCone (1 : Matrix ι ι ℝ) = {0} := by
  ext x
  simp only [survivalCone, Set.mem_setOf_eq, quad_one, Set.mem_singleton_iff]
  rw [sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (x i)]
  simp only [mem_univ, true_implies, sq_eq_zero_iff]
  exact ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩

/-! ### Survival -/

/-- The renormalized part `Q_r − s_r B` converges, so its form converges at every vector. -/
theorem tendsto_quad_renormalized {α : Type*} {l : Filter α} {Q : α → Matrix ι ι ℝ}
    {s : α → ℝ} {A B : Matrix ι ι ℝ}
    (hlim : ∀ i j, Tendsto (fun a => Q a i j - s a * B i j) l (𝓝 (A i j))) (x : ι → ℝ) :
    Tendsto (fun a => quad (Q a) x - s a * quad B x) l (𝓝 (quad A x)) := by
  have h : Tendsto (fun a => ∑ i, ∑ j, x i * (Q a i j - s a * B i j) * x j) l
      (𝓝 (quad A x)) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      ((hlim i j).const_mul (x i)).mul_const (x j)
  refine h.congr fun a => ?_
  simp only [quad, mul_sum]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- **Survival.** The renormalized limit of positive semidefinite forms is nonnegative on the
survival cone of the counterterm. -/
theorem quad_nonneg_of_regularized {α : Type*} {l : Filter α} [l.NeBot]
    {Q : α → Matrix ι ι ℝ} {s : α → ℝ} {A B : Matrix ι ι ℝ}
    (hQ : ∀ᶠ a in l, ∀ x, 0 ≤ quad (Q a) x)
    (hlim : ∀ i j, Tendsto (fun a => Q a i j - s a * B i j) l (𝓝 (A i j)))
    {x : ι → ℝ} (hx : x ∈ survivalCone B) : 0 ≤ quad A x := by
  have h := tendsto_quad_renormalized hlim x
  rw [show quad B x = 0 from hx] at h
  simp only [mul_zero, sub_zero] at h
  exact ge_of_tendsto h (hQ.mono fun a ha => ha x)

/-- **The counterterm of a positive regularization is positive**: if `s_r → +∞`, the leading form
`B` of a positive semidefinite family is positive semidefinite. -/
theorem counterterm_nonneg {α : Type*} {l : Filter α} [l.NeBot]
    {Q : α → Matrix ι ι ℝ} {s : α → ℝ} {A B : Matrix ι ι ℝ}
    (hQ : ∀ᶠ a in l, ∀ x, 0 ≤ quad (Q a) x) (hs : Tendsto s l atTop)
    (hlim : ∀ i j, Tendsto (fun a => Q a i j - s a * B i j) l (𝓝 (A i j))) (x : ι → ℝ) :
    0 ≤ quad B x := by
  by_contra hneg
  rw [not_le] at hneg
  -- `quad (Q a) x = (renormalized part) + s_a quad B x → −∞`.
  have hren := tendsto_quad_renormalized hlim x
  have hdiv : Tendsto (fun a => s a * quad B x) l atBot :=
    hs.atTop_mul_const_of_neg hneg
  have hsum : Tendsto (fun a => (quad (Q a) x - s a * quad B x) + s a * quad B x) l atBot :=
    tendsto_atBot_add_left_of_ge' l (quad A x + 1)
      ((hren.eventually (gt_mem_nhds (by linarith : quad A x < quad A x + 1))).mono
        fun a ha => ha.le) hdiv
  have hneg' : ∀ᶠ a in l, quad (Q a) x < 0 := by
    refine (hsum.eventually (eventually_lt_atBot 0)).mono fun a ha => ?_
    simpa using ha
  obtain ⟨a, ha1, ha2⟩ := (hneg'.and hQ).exists
  exact (lt_irrefl 0) (lt_of_le_of_lt (ha2 x) ha1)

/-! ### The counterterm is an invariant of the family -/

omit [Fintype ι] in
/-- **Counterterm uniqueness.** If one renormalization `Q − sB` converges with `s → +∞` and another
`Q − tC` converges with `C ≠ 0`, then `t/s` converges to some `c` and `B = c C`. -/
theorem counterterm_eq_smul {α : Type*} {l : Filter α} [l.NeBot]
    {Q : α → Matrix ι ι ℝ} {s t : α → ℝ} {A A' B C : Matrix ι ι ℝ}
    (hB : ∀ i j, Tendsto (fun a => Q a i j - s a * B i j) l (𝓝 (A i j)))
    (hC : ∀ i j, Tendsto (fun a => Q a i j - t a * C i j) l (𝓝 (A' i j)))
    (hs : Tendsto s l atTop) {i₀ j₀ : ι} (hC0 : C i₀ j₀ ≠ 0) :
    ∃ c : ℝ, Tendsto (fun a => t a / s a) l (𝓝 c) ∧ B = c • C := by
  -- `(t/s) C − B = ((Q − sB) − (Q − tC))/s → 0`.
  have hdiff : ∀ i j, Tendsto (fun a => t a / s a * C i j - B i j) l (𝓝 0) := by
    intro i j
    have h := ((hB i j).sub (hC i j)).div_atTop hs
    refine h.congr' ?_
    filter_upwards [hs.eventually_ne_atTop 0] with a ha
    field_simp
    ring
  have hratio : ∀ i j, Tendsto (fun a => t a / s a * C i j) l (𝓝 (B i j)) := fun i j => by
    simpa using (hdiff i j).add_const (B i j)
  set c := B i₀ j₀ / C i₀ j₀
  have hc : Tendsto (fun a => t a / s a) l (𝓝 c) := by
    have h := (hratio i₀ j₀).div_const (C i₀ j₀)
    refine h.congr fun a => ?_
    field_simp
  refine ⟨c, hc, ?_⟩
  ext i j
  exact tendsto_nhds_unique (hratio i j) ((hc.mul_const (C i j)).congr fun a => rfl)
    |>.trans (by simp [Matrix.smul_apply, smul_eq_mul])

/-- **The survival cone is scheme independent.** If the family renormalizes with a nonzero
counterterm `B` and divergence `s → +∞`, then every counterterm `C` of every other renormalization
has the same survival cone. -/
theorem survivalCone_eq_of_regularized {α : Type*} {l : Filter α} [l.NeBot]
    {Q : α → Matrix ι ι ℝ} {s t : α → ℝ} {A A' B C : Matrix ι ι ℝ}
    (hB : ∀ i j, Tendsto (fun a => Q a i j - s a * B i j) l (𝓝 (A i j)))
    (hC : ∀ i j, Tendsto (fun a => Q a i j - t a * C i j) l (𝓝 (A' i j)))
    (hs : Tendsto s l atTop) (hB0 : B ≠ 0) :
    survivalCone C = survivalCone B := by
  -- A zero counterterm would make `Q` converge, hence `B = (sB)/s → 0`.
  have hC0 : ∃ i₀ j₀, C i₀ j₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hB0
    ext i j
    have h := ((hC i j).sub (hB i j)).div_atTop hs
    have h' : Tendsto (fun a => B i j) l (𝓝 0) := h.congr' (by
      filter_upwards [hs.eventually_ne_atTop 0] with a ha
      rw [hcon i j]
      field_simp
      ring)
    exact tendsto_nhds_unique tendsto_const_nhds h'
  obtain ⟨i₀, j₀, hij⟩ := hC0
  obtain ⟨c, -, hBc⟩ := counterterm_eq_smul hB hC hs hij
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hB0 (by rw [hBc, zero_smul])
  ext x
  simp only [survivalCone, Set.mem_setOf_eq, hBc, quad_smul, mul_eq_zero, hc0, false_or]

/-! ### The Finsler–Debreu converse -/

/-- **Finsler–Debreu.** If `B ⪰ 0` and `A` is positive on the nonzero null vectors of `B`, then
`A + sB` is positive definite for every large `s`. -/
theorem exists_quad_add_smul_pos (A B : Matrix ι ι ℝ) (hB : ∀ x, 0 ≤ quad B x)
    (hA : ∀ x, x ≠ 0 → quad B x = 0 → 0 < quad A x) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s, s₀ ≤ s → ∀ x, x ≠ 0 → 0 < quad A x + s * quad B x := by
  set S : Set (ι → ℝ) := Metric.sphere 0 1
  have hS : IsCompact S := isCompact_sphere 0 1
  -- A bound for `|A|` on the sphere.
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_quad A).continuousOn
  -- The sphere vectors where `A ≤ 0`; there `B` is bounded below by some `b > 0`.
  set K : Set (ι → ℝ) := S ∩ {x | quad A x ≤ 0}
  have hK : IsCompact K := hS.inter_right (isClosed_le (continuous_quad A) continuous_const)
  have hKb : ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, b ≤ quad B x := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun x hx => by rw [hKe] at hx; exact hx.elim⟩
    obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hKne (continuous_quad B).continuousOn
    refine ⟨quad B x₀, ?_, fun x hx => hx₀min hx⟩
    rcases (hB x₀).lt_or_eq with h | h
    · exact h
    · have hx₀ne : x₀ ≠ 0 := by
        intro h0
        have := hx₀K.1
        rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at this
        exact zero_ne_one this
      exact absurd hx₀K.2 (not_le.mpr (hA x₀ hx₀ne h.symm))
  obtain ⟨b, hb, hbK⟩ := hKb
  refine ⟨(|C| + 1) / b, by positivity, fun s hs x hx => ?_⟩
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  -- Reduce to the unit sphere by homogeneity.
  have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : ι → ℝ := ‖x‖⁻¹ • x
  have huS : u ∈ S := by
    rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
  have hxu : x = ‖x‖ • u := by rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hu : 0 < quad A u + s * quad B u := by
    by_cases hAu : 0 < quad A u
    · exact add_pos_of_pos_of_nonneg hAu (mul_nonneg hs0 (hB u))
    · have huK : u ∈ K := ⟨huS, le_of_not_gt hAu⟩
      have hAC : -|C| ≤ quad A u := by
        have h1 := hC u huS
        rw [Real.norm_eq_abs] at h1
        linarith [neg_abs_le (quad A u), le_abs_self C]
      have hsb : |C| + 1 ≤ s * quad B u := by
        have h2 : (|C| + 1) / b * b ≤ s * quad B u :=
          mul_le_mul hs (hbK u huK) hb.le hs0
        rwa [div_mul_cancel₀ _ hb.ne'] at h2
      linarith
  have hAx := quad_smul_vec A ‖x‖ u
  have hBx := quad_smul_vec B ‖x‖ u
  rw [← hxu] at hAx hBx
  rw [hAx, hBx, mul_left_comm, ← mul_add]
  exact mul_pos (pow_pos ht 2) hu

/-- **The survival equivalence.** For a positive semidefinite counterterm `B`, the limit form `A` is
nonnegative on the survival cone iff for every `ε > 0` the regularized forms `A + sB + εI` are
positive semidefinite for all large `s`. -/
theorem quad_nonneg_on_survivalCone_iff [DecidableEq ι] (A B : Matrix ι ι ℝ)
    (hB : ∀ x, 0 ≤ quad B x) :
    (∀ x ∈ survivalCone B, 0 ≤ quad A x) ↔
      ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℝ, ∀ s, s₀ ≤ s → ∀ x,
        0 ≤ quad A x + s * quad B x + ε * ∑ i, x i ^ 2 := by
  constructor
  · intro hA ε hε
    have hpos : ∀ x, x ≠ 0 → quad B x = 0 → 0 < quad (A + ε • 1) x := by
      intro x hx hBx
      rw [quad_add, quad_smul, quad_one]
      have hsq : 0 < ∑ i, x i ^ 2 := by
        have hne : quad (1 : Matrix ι ι ℝ) x ≠ 0 := fun h =>
          hx (by simpa [survivalCone_one] using (show x ∈ survivalCone 1 from h))
        rw [quad_one] at hne
        exact lt_of_le_of_ne (sum_nonneg fun i _ => sq_nonneg (x i)) (Ne.symm hne)
      exact add_pos_of_nonneg_of_pos (hA x hBx) (mul_pos hε hsq)
    obtain ⟨s₀, -, hs₀⟩ := exists_quad_add_smul_pos (A + ε • 1) B hB hpos
    refine ⟨s₀, fun s hs x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [quad_zero_vec]
    · have := hs₀ s hs x hx
      rw [quad_add, quad_smul, quad_one] at this
      linarith
  · intro h x hx
    by_contra hneg
    rw [not_le] at hneg
    set N : ℝ := ∑ i, x i ^ 2
    have hN : 0 ≤ N := sum_nonneg fun i _ => sq_nonneg (x i)
    obtain ⟨s₀, hs₀⟩ := h (-quad A x / (2 * (N + 1))) (div_pos (by linarith) (by positivity))
    have h1 := hs₀ s₀ le_rfl x
    rw [show quad B x = 0 from hx, mul_zero, add_zero] at h1
    have h2 : -quad A x / (2 * (N + 1)) * N ≤ -quad A x / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

/-! ### Scalar counterterms carry no positivity -/

/-- **Scalar counterterms carry nothing.** Every real kernel `A` becomes positive definite after
adding a large multiple of the identity: with the identity as counterterm, every form is the
renormalized limit of positive definite forms. -/
theorem exists_quad_add_smul_one_pos [DecidableEq ι] (A : Matrix ι ι ℝ) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ ∀ s, s₀ ≤ s → ∀ x, x ≠ 0 → 0 < quad A x + s * ∑ i, x i ^ 2 := by
  obtain ⟨s₀, hs₀, h⟩ := exists_quad_add_smul_pos A 1
    (fun x => by rw [quad_one]; exact sum_nonneg fun i _ => sq_nonneg (x i))
    (fun x hx hBx => absurd (show x ∈ survivalCone 1 from hBx) (by
      rw [survivalCone_one]; exact hx))
  exact ⟨s₀, hs₀, fun s hs x hx => by simpa only [quad_one] using h s hs x hx⟩

/-- The regularized family `A + s I` with `s → +∞` realizes any `A` as a renormalized limit of
eventually positive semidefinite forms. -/
theorem regularized_one_realizes [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (∀ᶠ s : ℝ in atTop, ∀ x, 0 ≤ quad (A + s • 1) x) ∧
      ∀ i j, Tendsto (fun s : ℝ => (A + s • 1) i j - s * (1 : Matrix ι ι ℝ) i j) atTop
        (𝓝 (A i j)) := by
  obtain ⟨s₀, -, h⟩ := exists_quad_add_smul_one_pos A
  refine ⟨(eventually_ge_atTop s₀).mono fun s hs x => ?_, fun i j => ?_⟩
  · by_cases hx : x = 0
    · subst hx; simp [quad_zero_vec]
    · rw [quad_add, quad_smul, quad_one]
      exact (h s hs x hx).le
  · refine tendsto_const_nhds.congr fun s => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
