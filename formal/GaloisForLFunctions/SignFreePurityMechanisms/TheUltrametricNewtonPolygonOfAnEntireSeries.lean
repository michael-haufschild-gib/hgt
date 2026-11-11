import GaloisForLFunctions.SignFreePurityMechanisms.TheUltrametricNewtonPolygonSeparatesTheRoots

/-!
# The ultrametric Newton polygon of an entire series

Let `L` be a complete ultrametric field and `F(u) = ∑ aₖ uᵏ` an entire series (`‖aₖ‖ Rᵏ → 0` for
every `R`) with nonzero coefficients of strictly log-concave norms,
`‖aₖ‖ ‖aₖ₊₂‖ < ‖aₖ₊₁‖²`. Its Newton polygon has infinitely many sides, all of length one, with
slopes `r_d = ‖a_d‖ / ‖a_{d+1}‖` (`radius`), strictly increasing in `d`.

* Every zero lies on one of the spheres `‖u‖ = r_d`: elsewhere one term is strictly largest
  (`exists_radius_of_eval_eq_zero`).
* On the sphere `‖u‖ = r_d` the two terms of degrees `d, d + 1` have the same size and all others are
  smaller by a fixed factor. Dividing by `uᵈ`, `F(u) = 0` is the fixed-point equation of a
  contraction of the sphere, so it has a zero there (`exists_eval_eq_zero`).
* Each zero `u` on that sphere is simple in the strongest sense: `‖F(v)‖ = r_dᵈ ‖a_{d+1}‖ ‖v − u‖`
  for every `v` on the sphere (`norm_eval_eq`); in particular the zero on each sphere is unique.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.SignFreePurityMechanisms

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]

/-- An entire series whose Newton polygon has only sides of length one. -/
structure EntireSimpleSlopes (a : ℕ → L) : Prop where
  ne_zero : ∀ k, a k ≠ 0
  concave : ∀ k, ‖a k‖ * ‖a (k + 2)‖ < ‖a (k + 1)‖ ^ 2
  tendsto : ∀ R : ℝ, Tendsto (fun k => ‖a k‖ * R ^ k) atTop (𝓝 0)

namespace EntireSimpleSlopes

/-- The value of the series `∑ aₖ uᵏ`. -/
noncomputable def eval (a : ℕ → L) (u : L) : L := ∑' k, a k * u ^ k

/-- The slope of the side joining the vertices `d` and `d + 1`. -/
noncomputable def radius (a : ℕ → L) (d : ℕ) : ℝ := ‖a d‖ / ‖a (d + 1)‖

/-- The terms of degree other than `d, d + 1`, divided by `uᵈ`. -/
noncomputable def restTerm (a : ℕ → L) (d : ℕ) (u : L) (k : ℕ) : L :=
  if k = d + 1 then 0 else if k = d then 0 else a k * u ^ ((k : ℤ) - d)

/-- The sum of the terms of degree other than `d, d + 1`, divided by `uᵈ`. -/
noncomputable def rest (a : ℕ → L) (d : ℕ) (u : L) : L := ∑' k, restTerm a d u k

variable {a : ℕ → L} (h : EntireSimpleSlopes a)
include h

omit [IsUltrametricDist L] in
theorem norm_pos (k : ℕ) : 0 < ‖a k‖ := norm_pos_iff.mpr (h.ne_zero k)

omit [IsUltrametricDist L] in
theorem radius_pos (d : ℕ) : 0 < radius a d := div_pos (h.norm_pos d) (h.norm_pos (d + 1))

omit [IsUltrametricDist L] in
/-- The slopes increase strictly. -/
theorem radius_lt (d : ℕ) : radius a d < radius a (d + 1) := by
  unfold radius
  rw [div_lt_div_iff₀ (h.norm_pos _) (h.norm_pos _)]
  nlinarith [h.concave d]

omit [IsUltrametricDist L] in
theorem radius_strictMono : StrictMono (radius a) := strictMono_nat_of_lt_succ h.radius_lt

omit [IsUltrametricDist L] in
/-- On every sphere the term sizes are strictly log-concave. -/
theorem isStrictLogConcave {r : ℝ} (hr : 0 < r) (n : ℕ) :
    IsStrictLogConcave (fun k => ‖a k‖ * r ^ k) n where
  pos k _ := mul_pos (h.norm_pos k) (pow_pos hr k)
  concave k _ := by
    have hlt := mul_lt_mul_of_pos_right (h.concave k) (pow_pos hr (2 * k + 2))
    calc ‖a k‖ * r ^ k * (‖a (k + 2)‖ * r ^ (k + 2))
        = ‖a k‖ * ‖a (k + 2)‖ * r ^ (2 * k + 2) := by ring
      _ < ‖a (k + 1)‖ ^ 2 * r ^ (2 * k + 2) := hlt
      _ = (‖a (k + 1)‖ * r ^ (k + 1)) ^ 2 := by ring

omit [IsUltrametricDist L] in
theorem tendsto_norm_term (u : L) : Tendsto (fun k => ‖a k * u ^ k‖) atTop (𝓝 0) := by
  simpa only [norm_mul, norm_pow] using h.tendsto ‖u‖

variable [CompleteSpace L]

omit h in
/-- A sequence tending to zero in a complete ultrametric field is summable. -/
theorem summable_of_tendsto {f : ℕ → L} (hf : Tendsto (fun k => ‖f k‖) atTop (𝓝 0)) :
    Summable f := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hf

omit h in
/-- Off a finite set, terms tending to zero below `M` are uniformly below some `δ < M`. -/
theorem exists_lt_bound {t : ℕ → ℝ} {M : ℝ} (hM : 0 < M) (E : Finset ℕ)
    (ht : Tendsto t atTop (𝓝 0)) (hlt : ∀ k ∉ E, t k < M) :
    ∃ δ, 0 ≤ δ ∧ δ < M ∧ ∀ k ∉ E, t k ≤ δ := by
  classical
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hM)))
  let t' : ℕ → ℝ := fun k => if k ∈ E then 0 else t k
  have hne : (range (K₀ + 1)).Nonempty := ⟨0, mem_range.mpr (Nat.succ_pos _)⟩
  set B := (range (K₀ + 1)).sup' hne t'
  refine ⟨max (M / 2) B, le_trans (half_pos hM).le (le_max_left _ _), ?_, fun k hk => ?_⟩
  · refine max_lt (half_lt_self hM) ((sup'_lt_iff hne).mpr fun k _ => ?_)
    by_cases hkE : k ∈ E
    · simp only [t', if_pos hkE]
      exact hM
    · simp only [t', if_neg hkE]
      exact hlt k hkE
  · by_cases hk' : K₀ ≤ k
    · exact le_trans (hK₀ k hk').le (le_max_left _ _)
    · have : t' k ≤ B := le_sup' t' (mem_range.mpr (by omega))
      simp only [t', if_neg hk] at this
      exact le_trans this (le_max_right _ _)

/-! ### The two terms on a sphere -/

omit [IsUltrametricDist L] [CompleteSpace L] in
theorem term_succ_eq (d : ℕ) :
    ‖a (d + 1)‖ * radius a d ^ (d + 1) = ‖a d‖ * radius a d ^ d := by
  have hne := (h.norm_pos (d + 1)).ne'
  rw [pow_succ, radius]
  field_simp

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- On the sphere of radius `r_d`, every term other than those of degrees `d, d + 1` is strictly
smaller than these two. -/
theorem term_lt (d : ℕ) {k : ℕ} (hkd : k ≠ d) (hkd1 : k ≠ d + 1) :
    ‖a k‖ * radius a d ^ k < ‖a d‖ * radius a d ^ d := by
  have hlc := h.isStrictLogConcave (h.radius_pos d) (k + d + 3)
  have heq := h.term_succ_eq d
  rcases lt_or_gt_of_ne hkd with hk | hk
  · exact hlc.lt_of_le_succ (i := d) (by omega) heq.ge hk
  · exact hlc.lt_of_succ_le (i := d) heq.le (by omega) (by omega)

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- A uniform gap on the sphere: all other terms are at most `δ < ‖a_d‖ r_dᵈ`. -/
theorem exists_gap (d : ℕ) : ∃ δ, 0 ≤ δ ∧ δ < ‖a d‖ * radius a d ^ d ∧
    ∀ k, k ≠ d → k ≠ d + 1 → ‖a k‖ * radius a d ^ k ≤ δ := by
  obtain ⟨δ, h0, hlt, hδ⟩ := exists_lt_bound (mul_pos (h.norm_pos d) (pow_pos (h.radius_pos d) d))
    {d, d + 1} (h.tendsto (radius a d)) (fun k hk => by
      simp only [mem_insert, mem_singleton, not_or] at hk
      exact h.term_lt d hk.1 hk.2)
  exact ⟨δ, h0, hlt, fun k hk1 hk2 => hδ k (by simp [hk1, hk2])⟩

/-! ### Dividing by `uᵈ` -/

omit h [CompleteSpace L] in
/-- `‖uʲ − vʲ‖ ≤ r^{j−1} ‖u − v‖` on the sphere of radius `r`, for every integer `j`. -/
theorem norm_zpow_sub_zpow_le {u v : L} {r : ℝ} (hr : 0 < r) (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (j : ℤ) : ‖u ^ j - v ^ j‖ ≤ r ^ (j - 1) * ‖u - v‖ := by
  have hnat : ∀ n : ℕ, ‖u ^ n - v ^ n‖ ≤ r ^ ((n : ℤ) - 1) * ‖u - v‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [pow_zero, sub_self, norm_zero]
      exact mul_nonneg (zpow_nonneg hr.le _) (norm_nonneg _)
    rw [← (Commute.all u v).geom_sum₂_mul n, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (zpow_nonneg hr.le _)
      fun i hi => ?_
    rw [norm_mul, norm_pow, norm_pow, hu, hv, ← pow_add,
      show i + (n - 1 - i) = n - 1 by have := mem_range.mp hi; omega]
    rw [← zpow_natCast, Nat.cast_sub (by omega), Nat.cast_one]
  rcases j with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact hnat n
  · have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hu ▸ hr.ne')
    have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (hv ▸ hr.ne')
    rw [zpow_negSucc, zpow_negSucc, inv_sub_inv (pow_ne_zero _ hu0) (pow_ne_zero _ hv0),
      norm_div, norm_mul, norm_pow, norm_pow, hu, hv, norm_sub_rev]
    have h1 := hnat (n + 1)
    rw [div_le_iff₀ (mul_pos (pow_pos hr _) (pow_pos hr _))]
    calc ‖u ^ (n + 1) - v ^ (n + 1)‖ ≤ r ^ (((n + 1 : ℕ) : ℤ) - 1) * ‖u - v‖ := h1
      _ = r ^ (Int.negSucc n - 1) * ‖u - v‖ * (r ^ (n + 1) * r ^ (n + 1)) := by
        rw [← zpow_natCast, ← zpow_add₀ hr.ne', mul_assoc, mul_comm ‖u - v‖, ← mul_assoc,
          ← zpow_add₀ hr.ne']
        congr 2
        rw [Int.negSucc_eq]
        push_cast
        ring

omit [IsUltrametricDist L] [CompleteSpace L] in
theorem norm_restTerm_le {d : ℕ} {u : L} (hu : ‖u‖ = radius a d) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ k, k ≠ d → k ≠ d + 1 → ‖a k‖ * radius a d ^ k ≤ δ) (k : ℕ) :
    ‖restTerm a d u k‖ ≤ δ / radius a d ^ d := by
  have hr := h.radius_pos d
  unfold restTerm
  split_ifs with h1 h2
  · rw [norm_zero]; positivity
  · rw [norm_zero]; positivity
  · rw [norm_mul, norm_zpow, hu, zpow_sub₀ hr.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hδ k h2 h1) (pow_pos hr d).le

theorem summable_restTerm (d : ℕ) {u : L} (hu : u ≠ 0) : Summable (restTerm a d u) := by
  apply summable_of_tendsto
  have hlim : Tendsto (fun k => ‖a k * u ^ k‖ / ‖u‖ ^ d) atTop (𝓝 0) := by
    simpa only [zero_div] using (h.tendsto_norm_term u).div_const (‖u‖ ^ d)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim
  unfold restTerm
  split_ifs
  · rw [norm_zero]; positivity
  · rw [norm_zero]; positivity
  · rw [norm_mul, norm_zpow, zpow_sub₀ (norm_ne_zero_iff.mpr hu), zpow_natCast, zpow_natCast,
      norm_mul, norm_pow, mul_div_assoc]

/-- **Dividing by `uᵈ`.** `F(u) = uᵈ (a_d + a_{d+1} u + rest(u))` for `u ≠ 0`. -/
theorem eval_eq (d : ℕ) {u : L} (hu : u ≠ 0) :
    eval a u = u ^ d * (a d + a (d + 1) * u + rest a d u) := by
  classical
  set f : ℕ → L := fun k => a k * u ^ ((k : ℤ) - d)
  have hf : Summable f := by
    apply summable_of_tendsto
    have hlim : Tendsto (fun k => ‖a k * u ^ k‖ / ‖u‖ ^ d) atTop (𝓝 0) := by
      simpa only [zero_div] using (h.tendsto_norm_term u).div_const (‖u‖ ^ d)
    refine hlim.congr fun k => ?_
    simp only [f, norm_mul, norm_zpow, norm_pow, zpow_sub₀ (norm_ne_zero_iff.mpr hu),
      zpow_natCast, mul_div_assoc]
  have hterm : ∀ k, a k * u ^ k = u ^ d * f k := by
    intro k
    simp only [f]
    rw [mul_left_comm, ← zpow_natCast u d, ← zpow_natCast u k, ← zpow_add₀ hu, add_sub_cancel]
  have hg : Summable fun k => if k = d then 0 else f k :=
    (hf.indicator {d}ᶜ).congr fun k => by
      simp only [Set.indicator, Set.mem_compl_iff, Set.mem_singleton_iff, ite_not]
  rw [eval, tsum_congr hterm, tsum_mul_left, hf.tsum_eq_add_tsum_ite d,
    hg.tsum_eq_add_tsum_ite (d + 1)]
  simp only [f, if_neg (show d + 1 ≠ d by omega), sub_self, zpow_zero, mul_one]
  have hX : a (d + 1) * u ^ (((d + 1 : ℕ) : ℤ) - d) = a (d + 1) * u := by
    push_cast
    rw [add_sub_cancel_left, zpow_one]
  rw [hX, rest, add_assoc]
  rfl

omit [CompleteSpace L] in
theorem norm_rest_le {d : ℕ} {u : L} (hu : ‖u‖ = radius a d) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ k, k ≠ d → k ≠ d + 1 → ‖a k‖ * radius a d ^ k ≤ δ) :
    ‖rest a d u‖ ≤ δ / radius a d ^ d :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity [h.radius_pos d])
    (h.norm_restTerm_le hu hδ0 hδ)

/-- `rest` is Lipschitz on the sphere with constant `δ / r^{d+1}`. -/
theorem norm_rest_sub_le {d : ℕ} {u v : L} (hu : ‖u‖ = radius a d) (hv : ‖v‖ = radius a d)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ k, k ≠ d → k ≠ d + 1 → ‖a k‖ * radius a d ^ k ≤ δ) :
    ‖rest a d u - rest a d v‖ ≤ δ / radius a d ^ (d + 1) * ‖u - v‖ := by
  have hr := h.radius_pos d
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hu ▸ hr.ne')
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (hv ▸ hr.ne')
  rw [rest, rest, ← (h.summable_restTerm d hu0).tsum_sub (h.summable_restTerm d hv0)]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
  change ‖restTerm a d u k - restTerm a d v k‖ ≤ _
  unfold restTerm
  split_ifs with h1 h2
  · rw [sub_self, norm_zero]; positivity
  · rw [sub_self, norm_zero]; positivity
  · rw [← mul_sub, norm_mul]
    calc ‖a k‖ * ‖u ^ ((k : ℤ) - d) - v ^ ((k : ℤ) - d)‖
        ≤ ‖a k‖ * (radius a d ^ ((k : ℤ) - d - 1) * ‖u - v‖) :=
          mul_le_mul_of_nonneg_left (norm_zpow_sub_zpow_le hr hu hv _) (norm_nonneg _)
      _ = ‖a k‖ * radius a d ^ k / radius a d ^ (d + 1) * ‖u - v‖ := by
          rw [show (k : ℤ) - d - 1 = (k : ℤ) - ((d + 1 : ℕ) : ℤ) by push_cast; ring,
            zpow_sub₀ hr.ne', zpow_natCast, zpow_natCast]
          ring
      _ ≤ δ / radius a d ^ (d + 1) * ‖u - v‖ := by
          gcongr
          exact hδ k h2 h1

/-! ### Zeros -/

/-- **Simplicity.** If `u` is a zero on the sphere of radius `r_d`, then
`‖F(v)‖ = r_dᵈ ‖a_{d+1}‖ ‖v − u‖` on that sphere. -/
theorem norm_eval_eq {d : ℕ} {u v : L} (hu : ‖u‖ = radius a d) (hu0 : eval a u = 0)
    (hv : ‖v‖ = radius a d) :
    ‖eval a v‖ = radius a d ^ d * ‖a (d + 1)‖ * ‖v - u‖ := by
  have hr := h.radius_pos d
  have hun : u ≠ 0 := norm_ne_zero_iff.mp (hu ▸ hr.ne')
  have hvn : v ≠ 0 := norm_ne_zero_iff.mp (hv ▸ hr.ne')
  obtain ⟨δ, hδ0, hδlt, hδ⟩ := h.exists_gap d
  have hzero : a d + a (d + 1) * u + rest a d u = 0 := by
    rw [h.eval_eq d hun] at hu0
    exact (mul_eq_zero.mp hu0).resolve_left (pow_ne_zero _ hun)
  have hdiff : a d + a (d + 1) * v + rest a d v =
      a (d + 1) * (v - u) + (rest a d v - rest a d u) := by
    linear_combination hzero
  have hM : ‖a (d + 1)‖ * radius a d ^ (d + 1) = ‖a d‖ * radius a d ^ d := h.term_succ_eq d
  have hinner : ‖a d + a (d + 1) * v + rest a d v‖ = ‖a (d + 1)‖ * ‖v - u‖ := by
    rw [hdiff]
    by_cases hvu : v = u
    · subst hvu
      simp
    have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvu)
    have hlip := h.norm_rest_sub_le hv hu hδ0 hδ
    have hlt : ‖rest a d v - rest a d u‖ < ‖a (d + 1) * (v - u)‖ := by
      rw [norm_mul]
      refine lt_of_le_of_lt hlip (mul_lt_mul_of_pos_right ?_ hpos)
      rw [div_lt_iff₀ (pow_pos hr _), hM]
      exact hδlt
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, norm_mul]
  rw [h.eval_eq d hvn, norm_mul, norm_pow, hv, hinner, mul_assoc]

/-- On each sphere `‖u‖ = r_d` there is at most one zero. -/
theorem eq_of_eval_eq_zero {d : ℕ} {u v : L} (hu : ‖u‖ = radius a d) (hu0 : eval a u = 0)
    (hv : ‖v‖ = radius a d) (hv0 : eval a v = 0) : v = u := by
  have := h.norm_eval_eq hu hu0 hv
  rw [hv0, norm_zero] at this
  have hr := h.radius_pos d
  have hc : 0 < radius a d ^ d * ‖a (d + 1)‖ := mul_pos (pow_pos hr d) (h.norm_pos _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (v - u)]))

/-- **Existence on each sphere.** The zero equation divided by `uᵈ` is the fixed-point equation
of a contraction of the sphere `‖u‖ = r_d`. -/
theorem exists_eval_eq_zero (d : ℕ) : ∃ u : L, ‖u‖ = radius a d ∧ eval a u = 0 := by
  have hr := h.radius_pos d
  have ha1 := h.norm_pos (d + 1)
  obtain ⟨δ, hδ0, hδlt, hδ⟩ := h.exists_gap d
  have hM : ‖a (d + 1)‖ * radius a d ^ (d + 1) = ‖a d‖ * radius a d ^ d := h.term_succ_eq d
  set M := ‖a d‖ * radius a d ^ d with hMdef
  have hMpos : 0 < M := mul_pos (h.norm_pos d) (pow_pos hr d)
  set Φ : L → L := fun u => -(a d + rest a d u) / a (d + 1)
  set s : Set L := Metric.sphere 0 (radius a d)
  have hsphere : ∀ {u : L}, u ∈ s ↔ ‖u‖ = radius a d := by
    intro u
    simp only [s, mem_sphere_iff_norm, sub_zero]
  have hmaps : Set.MapsTo Φ s s := by
    intro u hu
    rw [hsphere] at hu ⊢
    have hfirst : ‖-(a d) / a (d + 1)‖ = radius a d := by rw [norm_div, norm_neg]; rfl
    have hsecond : ‖-(rest a d u) / a (d + 1)‖ < radius a d := by
      rw [norm_div, norm_neg, div_lt_iff₀ ha1]
      calc ‖rest a d u‖ ≤ δ / radius a d ^ d := h.norm_rest_le hu hδ0 hδ
        _ < M / radius a d ^ d := div_lt_div_of_pos_right hδlt (pow_pos hr d)
        _ = radius a d * ‖a (d + 1)‖ := by
          rw [hMdef, mul_div_assoc, div_self (pow_pos hr d).ne', mul_one, radius,
            div_mul_cancel₀ _ ha1.ne']
    have hΦ : Φ u = -(a d) / a (d + 1) + -(rest a d u) / a (d + 1) := by
      simp only [Φ, neg_add, add_div]
    rw [hΦ, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hfirst]; exact hsecond.ne'),
      hfirst, max_eq_left hsecond.le]
  set κ : ℝ := δ / M
  have hκ0 : 0 ≤ κ := div_nonneg hδ0 hMpos.le
  have hκ1 : κ < 1 := (div_lt_one hMpos).mpr hδlt
  have hlip : ∀ u v : s, dist (hmaps.restrict Φ s s u) (hmaps.restrict Φ s s v) ≤
      (⟨κ, hκ0⟩ : NNReal) * dist u v := by
    intro u v
    have hu := hsphere.mp u.2
    have hv := hsphere.mp v.2
    simp only [Set.MapsTo.restrict, Subtype.dist_eq, dist_eq_norm]
    change ‖Φ (u : L) - Φ (v : L)‖ ≤ κ * ‖(u : L) - v‖
    have : Φ u - Φ v = -(rest a d u - rest a d v) / a (d + 1) := by
      simp only [Φ]
      ring
    rw [this, norm_div, norm_neg, div_le_iff₀ ha1]
    calc ‖rest a d u - rest a d v‖ ≤ δ / radius a d ^ (d + 1) * ‖(u : L) - v‖ :=
          h.norm_rest_sub_le hu hv hδ0 hδ
      _ = κ * ‖(u : L) - v‖ * ‖a (d + 1)‖ := by
          rw [show κ = δ / (‖a (d + 1)‖ * radius a d ^ (d + 1)) by simp only [κ, hM]]
          field_simp
  have hcontr : ContractingWith ⟨κ, hκ0⟩ (hmaps.restrict Φ s s) :=
    ⟨by rw [← NNReal.coe_lt_coe]; exact hκ1, LipschitzWith.of_dist_le_mul hlip⟩
  have hx₀ : -(a d) / a (d + 1) ∈ s := by
    rw [hsphere, norm_div, norm_neg]
    rfl
  obtain ⟨u, hus, hfix, -⟩ := hcontr.exists_fixedPoint' (Metric.isClosed_sphere.isComplete)
    hmaps hx₀ (edist_ne_top _ _)
  have hu := hsphere.mp hus
  have hun : u ≠ 0 := norm_ne_zero_iff.mp (hu ▸ hr.ne')
  refine ⟨u, hu, ?_⟩
  have hfix' : -(a d + rest a d u) / a (d + 1) = u := hfix
  have hzero : a d + a (d + 1) * u + rest a d u = 0 := by
    rw [div_eq_iff (h.ne_zero _)] at hfix'
    linear_combination -hfix'
  rw [h.eval_eq d hun, hzero, mul_zero]

omit [IsUltrametricDist L] h [CompleteSpace L] in
theorem eval_zero : eval a 0 = a 0 := by
  rw [eval, tsum_eq_single 0 fun k hk => by rw [zero_pow hk, mul_zero], pow_zero, mul_one]

omit [IsUltrametricDist L] [CompleteSpace L] in
theorem radius_eq_of_term_eq {k : ℕ} {r : ℝ} (hr : 0 < r)
    (heq : ‖a k‖ * r ^ k = ‖a (k + 1)‖ * r ^ (k + 1)) : r = radius a k := by
  rw [radius, eq_div_iff (h.norm_pos _).ne']
  rw [pow_succ] at heq
  have := mul_right_cancel₀ (pow_pos hr k).ne' (by linear_combination heq.symm :
    r * ‖a (k + 1)‖ * r ^ k = ‖a k‖ * r ^ k)
  linarith

/-- **Every zero lies on a side of the Newton polygon.** -/
theorem exists_radius_of_eval_eq_zero {u : L} (hu0 : eval a u = 0) :
    ∃ d, ‖u‖ = radius a d := by
  classical
  have hun : u ≠ 0 := fun h0 => h.ne_zero 0 (by rw [h0, eval_zero] at hu0; exact hu0)
  set r := ‖u‖
  have hr : 0 < r := norm_pos_iff.mpr hun
  set t : ℕ → ℝ := fun k => ‖a k‖ * r ^ k
  have ht0 : 0 < t 0 := by simp only [t, pow_zero, mul_one]; exact h.norm_pos 0
  -- a largest term
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp ((h.tendsto r).eventually (gt_mem_nhds ht0))
  obtain ⟨m, -, hmax⟩ := exists_max_image (range (K₀ + 1)) t ⟨0, by simp⟩
  have hglob : ∀ k, t k ≤ t m := by
    intro k
    by_cases hk : k ≤ K₀
    · exact hmax k (mem_range.mpr (by omega))
    · exact (hK₀ k (by omega)).le.trans (hmax 0 (by simp))
  by_contra hno
  push Not at hno
  -- the largest term is unique: two largest terms are adjacent and give a slope
  have hstrict : ∀ k, k ≠ m → t k < t m := by
    intro k hk
    refine lt_of_le_of_ne (hglob k) fun heq => ?_
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · by_cases hkm : k + 1 = m
      · subst hkm
        exact hno k (h.radius_eq_of_term_eq hr heq)
      · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have := (h.isStrictLogConcave hr (j + 2)).lt_of_le_succ (i := j) (by omega)
          (hglob j) (show k < j by omega)
        exact (this.trans_le (hglob j)).ne heq
    · by_cases hkm : k = m + 1
      · subst hkm
        exact hno m (h.radius_eq_of_term_eq hr heq.symm)
      · have := (h.isStrictLogConcave hr (k + 3)).lt_of_succ_le (i := m) (hglob (m + 1))
          (show m + 2 ≤ k by omega) (by omega)
        exact this.ne heq
  -- then one term dominates and the series cannot vanish
  obtain ⟨δ, hδ0, hδlt, hδ⟩ := exists_lt_bound (lt_of_lt_of_le ht0 (hglob 0)) {m}
    (h.tendsto r) (fun k hk => hstrict k (by simpa using hk))
  have hsum : Summable fun k => a k * u ^ k := summable_of_tendsto (h.tendsto_norm_term u)
  have hrest : ‖∑' k, if k = m then (0 : L) else a k * u ^ k‖ < ‖a m * u ^ m‖ := by
    rw [norm_mul, norm_pow]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hδ0
      fun k => ?_) hδlt
    split_ifs with hk
    · rw [norm_zero]
      exact hδ0
    · rw [norm_mul, norm_pow]
      exact hδ k (by simpa using hk)
  rw [eval, hsum.tsum_eq_add_tsum_ite m] at hu0
  have := congrArg norm hu0
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne', max_eq_left hrest.le,
    norm_zero, norm_mul, norm_pow] at this
  exact (mul_pos (h.norm_pos m) (pow_pos hr m)).ne' this

end EntireSimpleSlopes

end GaloisForLFunctions.SignFreePurityMechanisms
