import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHessianOfALorentzianPolynomialTricklesDown

/-!
# The mixed Hessians of a Lorentzian polynomial are hyperbolic

For a homogeneous polynomial `f = Σ_β c_β x^β` write `∂^γ f = γ! c_γ` for `|γ| = deg f`, and for
directions `v_1, …, v_m` let `dval c [v_1, …, v_m] γ = ∂_{v_1} ⋯ ∂_{v_m} ∂^γ f` (`dval`), a
constant when `m + |γ| = deg f`. The **mixed Hessian** `mixHess c vs γ` is the Hessian of the
quadratic `∂_{vs} ∂^γ f`; `mixHess c [] γ` is the quadratic derivative `quadDeriv c γ`.

* **Polarization is linkage** (`mixHess_cons`, `bil_mixHess_link`): the mixed Hessian along
  `v :: vs` is `H = Σ_i v_i H_i` with `H_i` the mixed Hessian along `vs` of `∂_i ∂^γ f`, and
  `H_i(u, v) = (H u)_i`. The links of `H` are the mixed Hessians of the partial derivatives,
  weighted by the first direction (`weightedTrickleDown_of_links`).
* **The mixed Hessians trickle down** (`isHyperbolic_mixHess`): for a Lorentzian polynomial and
  nonnegative directions every mixed Hessian has one positive square. Induction on the number of
  directions: each step is the weighted Metzler Hodge index theorem with weights the first
  direction, connectivity coming from M-convexity of the support above `γ`
  (`isMConvex_shift`); nonnegative directions by continuity.
* **The Alexandrov–Fenchel inequalities** (`alexandrov_fenchel`):
  `D(u, v, vs)² ≥ D(u, u, vs) D(v, v, vs)` for nonnegative `u, vs`; for the volume polynomial
  of convex bodies these are the classical mixed-volume inequalities. Specialized to two
  directions they are the **Khovanskii–Teissier inequalities** (`khovanskii_teissier`): the
  mixed sequence `k ↦ D(u^k, v^{n−k})`, which is `k!(n−k)!` times the coefficient sequence of
  the restriction `t ↦ f(t u + v)`, is log-concave.
-/

noncomputable section

open Matrix Finset
open scoped Nat

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι]

/-! ### Mixed derivative values and mixed Hessians -/

/-- The mixed derivative values `∂_{v_1} ⋯ ∂_{v_m} ∂^γ f`, with `∂^γ f = γ! c_γ`. -/
def dval (c : (ι →₀ ℕ) → ℝ) : List (ι → ℝ) → (ι →₀ ℕ) → ℝ
  | [], γ => mfact γ * c γ
  | v :: vs, γ => ∑ i, v i * dval c vs (γ + Finsupp.single i 1)

/-- The **mixed Hessian**: the Hessian of the quadratic `∂_{vs} ∂^γ f`. -/
def mixHess (c : (ι →₀ ℕ) → ℝ) (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) : Matrix ι ι ℝ :=
  Matrix.of fun j k => dval c vs (γ + Finsupp.single j 1 + Finsupp.single k 1)

variable {c : (ι →₀ ℕ) → ℝ}

theorem mixHess_apply (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) (j k : ι) :
    mixHess c vs γ j k = dval c vs (γ + Finsupp.single j 1 + Finsupp.single k 1) := rfl

theorem mixHess_isSymm (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) : (mixHess c vs γ).IsSymm :=
  Matrix.IsSymm.ext fun j k => by
    simp only [mixHess, Matrix.of_apply, add_assoc, add_comm (Finsupp.single j 1)]

theorem mixHess_nil (γ : ι →₀ ℕ) : mixHess c [] γ = quadDeriv c γ := rfl

theorem mixHess_cons_apply (v : ι → ℝ) (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) (j k : ι) :
    mixHess c (v :: vs) γ j k = ∑ i, v i * mixHess c vs (γ + Finsupp.single i 1) j k := by
  simp only [mixHess, Matrix.of_apply, dval]
  refine sum_congr rfl fun i _ => ?_
  congr 2
  abel

theorem mixHess_cons (v : ι → ℝ) (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) :
    mixHess c (v :: vs) γ = ∑ i, v i • mixHess c vs (γ + Finsupp.single i 1) := by
  ext j k
  simp [mixHess_cons_apply, Matrix.sum_apply]

/-- **The links of a mixed Hessian**: `H_i(u, v) = (H u)_i`, `H_i` the mixed Hessian of `∂_i ∂^γ f`. -/
theorem bil_mixHess_link (v : ι → ℝ) (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) (i : ι) (u : ι → ℝ) :
    bil (mixHess c vs (γ + Finsupp.single i 1)) u v = (mixHess c (v :: vs) γ *ᵥ u) i := by
  simp only [bil, dotProduct, mulVec, mixHess_apply, dval, mul_sum, sum_mul]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

/-- The bilinear form of a mixed Hessian is one more mixed derivative value. -/
theorem bil_mixHess (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) (u v : ι → ℝ) :
    bil (mixHess c vs γ) u v = dval c (u :: v :: vs) γ := by
  simp only [bil, dotProduct, mulVec, mixHess_apply, dval, mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

theorem dval_cons_cons (v w : ι → ℝ) (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) :
    dval c (v :: w :: vs) γ = dval c (w :: v :: vs) γ := by
  simp only [dval, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [add_right_comm γ]
  ring

/-- Mixed derivatives commute: `dval` depends on the directions only as a multiset. -/
theorem dval_perm {vs ws : List (ι → ℝ)} (h : vs.Perm ws) (γ : ι →₀ ℕ) :
    dval c vs γ = dval c ws γ := by
  induction h generalizing γ with
  | nil => rfl
  | cons v _ ih => simp only [dval, ih]
  | swap v w vs => exact dval_cons_cons w v vs γ
  | trans _ _ ih₁ ih₂ => exact (ih₁ γ).trans (ih₂ γ)

/-! ### Sign and support -/

theorem dval_nonneg (hc : ∀ β, 0 ≤ c β) :
    ∀ vs : List (ι → ℝ), (∀ v ∈ vs, ∀ i, 0 ≤ v i) → ∀ γ, 0 ≤ dval c vs γ
  | [], _, γ => mul_nonneg (mfact_pos γ).le (hc γ)
  | v :: vs, hvs, γ => sum_nonneg fun i _ => mul_nonneg (hvs v (by simp) i)
      (dval_nonneg hc vs (fun w hw => hvs w (by simp [hw])) _)

/-- For positive directions, `∂_{vs} ∂^γ f ≠ 0` iff `f` has a monomial above `γ` of the right
degree. -/
theorem dval_pos_iff (hc : ∀ β, 0 ≤ c β) :
    ∀ vs : List (ι → ℝ), (∀ v ∈ vs, ∀ i, 0 < v i) → ∀ γ,
      0 < dval c vs γ ↔ ∃ α : ι →₀ ℕ, Finsupp.degree α = vs.length ∧ c (γ + α) ≠ 0
  | [], _, γ => by
    simp only [dval, List.length_nil, Finsupp.degree_eq_zero_iff, exists_eq_left, add_zero]
    constructor
    · intro h h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
    · intro h; exact mul_pos (mfact_pos γ) (lt_of_le_of_ne (hc γ) (Ne.symm h))
  | v :: vs, hvs, γ => by
    have hv : ∀ i, 0 < v i := hvs v (by simp)
    have hvs' : ∀ w ∈ vs, ∀ i, 0 < w i := fun w hw => hvs w (by simp [hw])
    have ih := dval_pos_iff hc vs hvs'
    simp only [dval, List.length_cons]
    constructor
    · intro h
      obtain ⟨i, -, hi⟩ : ∃ i ∈ univ, 0 < v i * dval c vs (γ + Finsupp.single i 1) := by
        by_contra hneg
        push Not at hneg
        exact absurd h (not_lt.mpr (sum_nonpos hneg))
      obtain ⟨α, hα, hcα⟩ := (ih _).mp (pos_of_mul_pos_right hi (hv i).le)
      refine ⟨Finsupp.single i 1 + α, ?_, ?_⟩
      · rw [map_add, Finsupp.degree_single, hα]; omega
      · rwa [← add_assoc]
    · rintro ⟨α, hα, hcα⟩
      obtain ⟨i, hi⟩ : ∃ i, 1 ≤ α i := by
        by_contra hneg
        push Not at hneg
        have : α = 0 := Finsupp.ext fun i => by have := hneg i; simp; omega
        rw [this, map_zero] at hα
        omega
      have hle : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.mpr hi
      refine sum_pos' (fun j _ => mul_nonneg (hv j).le
        (dval_nonneg hc vs (fun w hw j => (hvs' w hw j).le) _)) ⟨i, mem_univ i, ?_⟩
      refine mul_pos (hv i) ((ih _).mpr ⟨α - Finsupp.single i 1, ?_, ?_⟩)
      · have := degree_add_single (α - Finsupp.single i 1) i
        rw [tsub_add_cancel_of_le hle, hα] at this
        omega
      · rwa [add_assoc, add_tsub_cancel_of_le hle]

variable [DecidableEq ι]

omit [Fintype ι] in
/-- The support above `γ`, `{δ : c_{γ + δ} ≠ 0}`, of an M-convex support is M-convex. -/
theorem isMConvex_shift (hM : IsMConvex {β | c β ≠ 0}) (γ : ι →₀ ℕ) :
    IsMConvex {δ | c (γ + δ) ≠ 0} := by
  intro α hα β hβ l hlt
  obtain ⟨j, hj, hmem⟩ := hM _ hα _ hβ l (by simp only [Finsupp.add_apply]; omega)
  refine ⟨j, by simp only [Finsupp.add_apply] at hj; omega, ?_⟩
  have e : γ + (α - Finsupp.single l 1 + Finsupp.single j 1) =
      γ + α - Finsupp.single l 1 + Finsupp.single j 1 := by
    ext p
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> subst_vars <;> omega
  show c (γ + (α - Finsupp.single l 1 + Finsupp.single j 1)) ≠ 0
  rw [e]
  exact hmem

/-! ### Trickle-down -/

omit [DecidableEq ι] in
/-- **Trickle-down from links.** If `Q[u] = Σ_i x_i L_i[u]` with hyperbolic, symmetric,
entrywise nonnegative links satisfying `L_i(u, x) = (Q u)_i`, then `Q` satisfies `(TD_x)`. -/
theorem weightedTrickleDown_of_links {Q : Matrix ι ι ℝ} {L : ι → Matrix ι ι ℝ} {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) (hLs : ∀ i, (L i).IsSymm) (hLnn : ∀ i j k, 0 ≤ L i j k)
    (hL : ∀ i, IsHyperbolic (L i)) (hsum : ∀ u, qf Q u = ∑ i, x i * qf (L i) u)
    (hlink : ∀ i u, bil (L i) u x = (Q *ᵥ u) i) : WeightedTrickleDown x Q := by
  intro v
  have hxx : ∀ i, qf (L i) x = (Q *ᵥ x) i := fun i => hlink i x
  have hxv : ∀ i, bil (L i) x v = (Q *ᵥ v) i := fun i => by
    rw [bil_comm (hLs i)]; exact hlink i v
  have hQx0 : ∀ i, 0 ≤ (Q *ᵥ x) i := fun i => by
    rw [← hxx, qf_eq_sum]
    exact sum_nonneg fun j _ => sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (hx j).le (hLnn i j k)) (hx k).le
  have hterm : ∀ i, x i * qf (L i) v ≤ x i * (Q *ᵥ v) i ^ 2 / (Q *ᵥ x) i := fun i => by
    rcases (hQx0 i).lt_or_eq with hpos | hzero
    · have hcs := hL i x v (by rw [hxx]; exact hpos)
      rw [hxx, hxv] at hcs
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (by rw [le_div_iff₀ hpos]; linarith) (hx i).le
    · have hz := eq_zero_of_qf_eq_zero (hLnn i) hx (by rw [hxx, ← hzero])
      have : qf (L i) v = 0 := by simp [qf, bil, dotProduct, mulVec, hz]
      rw [this, ← hzero, div_zero, mul_zero]
  rw [hsum]
  exact sum_le_sum fun i _ => hterm i

/-- **The mixed Hessians at positive directions are hyperbolic.** -/
theorem isHyperbolic_mixHess_of_pos {d : ℕ} (hc : IsLorentzianPoly d c) :
    ∀ (vs : List (ι → ℝ)) (γ : ι →₀ ℕ), Finsupp.degree γ + vs.length + 2 = d →
      (∀ v ∈ vs, ∀ i, 0 < v i) → IsHyperbolic (mixHess c vs γ)
  | [], γ, hd, _ => by rw [mixHess_nil]; exact hc.2.2.2 γ (by simpa using hd)
  | v :: vs, γ, hd, hvs => by
    have hc0 := hc.1
    have hdeg := hc.2.1
    have hM := hc.2.2.1
    have hv : ∀ i, 0 < v i := hvs v (by simp)
    have hvs' : ∀ w ∈ vs, ∀ i, 0 < w i := fun w hw => hvs w (by simp [hw])
    have hvs0 : ∀ w ∈ v :: vs, ∀ i, 0 ≤ w i := fun w hw i => (hvs w hw i).le
    simp only [List.length_cons] at hd
    refine isHyperbolic_of_weightedTrickleDown_active (mixHess_isSymm _ _)
      (fun j k => dval_nonneg hc0 _ hvs0 _) hv
      (weightedTrickleDown_of_links hv (fun i => mixHess_isSymm _ _)
        (fun i j k => dval_nonneg hc0 _ (fun w hw j => (hvs' w hw j).le) _)
        (fun i => isHyperbolic_mixHess_of_pos hc vs _
          (by rw [degree_add_single]; omega) hvs')
        (fun u => by rw [mixHess_cons, qf_sum']; simp only [qf_smul'])
        (fun i u => bil_mixHess_link v vs γ i u)) ?_
    intro w hw a b ha hb
    -- the degree of the support above `γ`
    have hdδ : ∀ δ ∈ {δ | c (γ + δ) ≠ 0}, Finsupp.degree δ = vs.length + 3 := fun δ hδ => by
      have := hdeg _ hδ
      rw [map_add] at this
      omega
    -- every active variable occurs above `γ`
    have hmono : ∀ p, 0 < (mixHess c (v :: vs) γ *ᵥ v) p → ∃ δ : ι →₀ ℕ, c (γ + δ) ≠ 0 ∧ 1 ≤ δ p :=
        fun p hp => by
      obtain ⟨k, -, hk⟩ : ∃ k ∈ univ, 0 < mixHess c (v :: vs) γ p k * v k := by
        by_contra h
        push Not at h
        exact absurd hp (not_lt.mpr (sum_nonpos h))
      obtain ⟨α, -, hα⟩ := (dval_pos_iff hc0 _ hvs _).mp (pos_of_mul_pos_left hk (hv k).le)
      refine ⟨Finsupp.single p 1 + Finsupp.single k 1 + α, by rwa [← add_assoc, ← add_assoc], ?_⟩
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> omega
    -- the variables of one monomial above `γ` are joined by nonzero entries
    have hclique : ∀ δ ∈ {δ | c (γ + δ) ≠ 0}, ∀ p q, 1 ≤ δ p → 1 ≤ δ q → w p = w q := by
      intro δ hδ p q hp hq
      by_cases hpq : p = q
      · rw [hpq]
      have hle : Finsupp.single p 1 + Finsupp.single q 1 ≤ δ := by
        refine Finsupp.le_def.mpr fun t => ?_
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split_ifs <;> subst_vars <;> first | omega | exact absurd rfl hpq
      refine hw p q (ne_of_gt ((dval_pos_iff hc0 _ hvs _).mpr
        ⟨δ - (Finsupp.single p 1 + Finsupp.single q 1), ?_, ?_⟩))
      · have h1 := hdδ δ hδ
        have h2 : Finsupp.degree (δ - (Finsupp.single p 1 + Finsupp.single q 1)) +
            Finsupp.degree (Finsupp.single p 1 + Finsupp.single q 1) = Finsupp.degree δ := by
          rw [← map_add, tsub_add_cancel_of_le hle]
        rw [map_add, Finsupp.degree_single, Finsupp.degree_single] at h2
        simp only [List.length_cons]
        omega
      · rw [add_assoc γ, add_assoc γ, add_tsub_cancel_of_le hle]; exact hδ
    obtain ⟨δ, hδ, hδa⟩ := hmono a ha
    obtain ⟨δ', hδ', hδb⟩ := hmono b hb
    exact mconvex_path (isMConvex_shift hM γ) hdδ (by omega) w hclique _ δ δ' hδ hδ' rfl a b
      hδa hδb

omit [DecidableEq ι] in
theorem continuous_dval (vs : List (ι → ℝ)) (γ : ι →₀ ℕ) :
    Continuous fun t : ℝ => dval c (vs.map fun v i => v i + t) γ := by
  induction vs generalizing γ with
  | nil => exact continuous_const
  | cons v vs ih =>
    simp only [List.map_cons, dval]
    exact continuous_finsetSum _ fun i _ => (continuous_const.add continuous_id).mul (ih _)

/-- **The mixed Hessians of a Lorentzian polynomial along nonnegative directions are
hyperbolic**: every mixed quadratic derivative `∂_{v_1} ⋯ ∂_{v_m} ∂^γ f`, `v_t ≥ 0`, has one
positive square. -/
theorem isHyperbolic_mixHess {d : ℕ} (hc : IsLorentzianPoly d c) {vs : List (ι → ℝ)}
    {γ : ι →₀ ℕ} (hd : Finsupp.degree γ + vs.length + 2 = d) (hvs : ∀ v ∈ vs, ∀ i, 0 ≤ v i) :
    IsHyperbolic (mixHess c vs γ) := by
  have h := isHyperbolic_of_continuous (Q := fun t => mixHess c (vs.map fun v i => v i + t) γ)
    (fun j k => by simp only [mixHess_apply]; exact continuous_dval vs _)
    (fun t ht => isHyperbolic_mixHess_of_pos hc _ γ (by simpa using hd) fun w hw i => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      linarith [hvs v hv i])
  simpa using h

/-! ### Alexandrov–Fenchel and Khovanskii–Teissier -/

/-- **The Alexandrov–Fenchel inequalities** of a Lorentzian polynomial:
`D(u, v, vs)² ≥ D(u, u, vs) D(v, v, vs)` for nonnegative `u, vs` and every `v`. -/
theorem alexandrov_fenchel {d : ℕ} (hc : IsLorentzianPoly d c) {vs : List (ι → ℝ)}
    {γ : ι →₀ ℕ} (hd : Finsupp.degree γ + vs.length + 2 = d) (hvs : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (v : ι → ℝ) :
    dval c (u :: u :: vs) γ * dval c (v :: v :: vs) γ ≤ dval c (u :: v :: vs) γ ^ 2 := by
  have hH := isHyperbolic_mixHess hc hd hvs
  rw [← bil_mixHess, ← bil_mixHess, ← bil_mixHess]
  rcases (show 0 ≤ qf (mixHess c vs γ) u from by
      rw [qf, bil_mixHess]
      exact dval_nonneg hc.1 _ (by simp only [List.mem_cons]; rintro w (rfl | rfl | hw) <;>
        first | exact hu | exact hvs w hw) _).lt_or_eq with hpos | hzero
  · exact hH u v hpos
  · rw [qf] at hzero
    rw [← hzero, zero_mul]
    positivity

/-- **The Khovanskii–Teissier inequalities**: the mixed sequence `k ↦ D(u^k, v^{n − k})` of a
Lorentzian polynomial along nonnegative directions is log-concave. -/
theorem khovanskii_teissier {n : ℕ} (hc : IsLorentzianPoly n c) {u v : ι → ℝ}
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) {k m : ℕ} (hkm : k + m + 2 = n) :
    dval c (List.replicate (k + 2) u ++ List.replicate m v) 0 *
        dval c (List.replicate k u ++ List.replicate (m + 2) v) 0 ≤
      dval c (List.replicate (k + 1) u ++ List.replicate (m + 1) v) 0 ^ 2 := by
  set vs := List.replicate k u ++ List.replicate m v
  have hvs : ∀ w ∈ vs, ∀ i, 0 ≤ w i := fun w hw => by
    rcases List.mem_append.mp hw with h | h
    · rw [List.eq_of_mem_replicate h]; exact hu
    · rw [List.eq_of_mem_replicate h]; exact hv
  have h1 : List.replicate (k + 2) u ++ List.replicate m v = u :: u :: vs := by
    simp [vs, List.replicate_succ]
  have h2 : (List.replicate k u ++ List.replicate (m + 2) v).Perm (v :: v :: vs) := by
    simp only [List.replicate_succ, vs]
    exact List.perm_middle.trans (List.Perm.cons v List.perm_middle)
  have h3 : (List.replicate (k + 1) u ++ List.replicate (m + 1) v).Perm (u :: v :: vs) := by
    simp only [List.replicate_succ, List.cons_append, vs]
    exact List.Perm.cons u List.perm_middle
  rw [h1, dval_perm h2, dval_perm h3]
  exact alexandrov_fenchel hc (by simp [vs]; omega) hvs hu v

end GaloisForLFunctions.ArithmeticLorentzianGeometry
