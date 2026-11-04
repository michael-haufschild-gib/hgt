import GaloisForLFunctions.ZeroConfigurationGeometry.LaguerreStepsNeverDeepenTheConfiguration

/-!
# Heat steps never shrink the mesh

`HeatTimeSpreadsTheConfiguration` proves an averaged repulsion law: the total squared gap grows at
a fixed rate. This module proves the pointwise one. For a real configuration with simple points,
the *mesh* is the least distance between two points.

* **First-order steps** (`meshGe_add_smul_derivative`, `nodup_roots_add_smul_derivative`). If `p`
  has real simple roots with mesh `≥ μ`, so does `p + cp'` for every real `c`.
* **Heat steps** (`meshGe_heatStep`, `iterate_heatStep`). The same holds for
  `p − c²p'' = (1 − cD)(1 + cD)p`, and for every number of heat steps.

Proof. At a root `y` of `p + cp'` the logarithmic derivative `φ = Σ_k 1/(y − x_k)` equals `−1/c`.
Two roots `y < y'` closer than `μ` would give `Σ_k 1/((y − x_k)(y' − x_k)) = 0`. With no root of
`p` between them, every term is positive. With exactly one, `x₀ = y + u = y' − v`, its term is
`−1/(uv)`. Each other root at distance `D ≥ μ` from `x₀` contributes `1/((D − u)(D + v))` on the
left and `1/((D − v)(D + u))` on the right. Since the roots are `μ`-separated, the left side is at
most the telescoping sum `Σ_m 1/((md + v)((m + 1)d + v)) < 1/(dv)` with `d = u + v < μ`
(`sum_le_sum_range_of_sep`, `sum_range_inv_mul_lt`), and the right side is below `1/(du)`.
Together they are below `1/(uv)`: a contradiction. The roots stay simple because
`p'' = p(φ² − Σ_k 1/(y − x_k)²)` (`eval_derivative_derivative_eq`), so at a double root
`(p + cp')' = −c p Σ_k 1/(y − x_k)²` would vanish.

The equally spaced lattice is the extremal case: the telescoping bound is the lattice sum.
-/

open Polynomial Filter Topology

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-! ### Separated sums -/

/-- **Counting along one side.** For `μ`-separated positions all at distance `≥ μ` below `c`, and
`F` nonnegative and decreasing on `[μ, ∞)`, `Σ_x F(c − x) ≤ Σ_{m < |A|} F((m + 1)μ)`. -/
theorem sum_le_sum_range_of_sep {α : Type*} [DecidableEq α] (pos : α → ℝ) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∀ (n : ℕ) (A : Finset α) (c : ℝ) (F : ℝ → ℝ), A.card = n →
      (∀ D, μ ≤ D → 0 ≤ F D) → (∀ D D', μ ≤ D → D ≤ D' → F D' ≤ F D) →
      (∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → μ ≤ |pos x - pos x'|) → (∀ x ∈ A, μ ≤ c - pos x) →
      ∑ x ∈ A, F (c - pos x) ≤ ∑ m ∈ Finset.range n, F (((m : ℝ) + 1) * μ) := by
  intro n
  induction n with
  | zero =>
    intro A c F hA _ _ _ _
    rw [Finset.card_eq_zero.mp hA]
    simp
  | succ n ih =>
    intro A c F hA hF0 hFm hsep hle
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image A pos hne
    have hcard : (A.erase a).card = n := by rw [Finset.card_erase_of_mem ha]; omega
    have hsub : ∀ x ∈ A.erase a, μ ≤ pos a - pos x := fun x hx => by
      have hxA := Finset.mem_of_mem_erase hx
      have h1 := hsep x hxA a ha (Finset.ne_of_mem_erase hx)
      have h2 := hmax x hxA
      rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at h1
    have hIH := ih (A.erase a) (pos a) (fun D => F (D + μ)) hcard
      (fun D hD => hF0 _ (by linarith)) (fun D D' hD hDD' => hFm _ _ (by linarith) (by linarith))
      (fun x hx x' hx' h => hsep x (Finset.mem_of_mem_erase hx) x' (Finset.mem_of_mem_erase hx') h)
      hsub
    have hstep : ∑ x ∈ A.erase a, F (c - pos x) ≤ ∑ x ∈ A.erase a, F (pos a - pos x + μ) :=
      Finset.sum_le_sum fun x hx =>
        hFm _ _ (by linarith [hsub x hx]) (by linarith [hle a ha])
    have hfirst : F (c - pos a) ≤ F ((((0 : ℕ) : ℝ) + 1) * μ) := by
      refine hFm _ _ (by simp) ?_
      simpa using hle a ha
    rw [← Finset.insert_erase ha, Finset.sum_insert (Finset.notMem_erase a A),
      Finset.sum_range_succ']
    have hshift : ∑ m ∈ Finset.range n, F (((m : ℝ) + 1) * μ + μ) =
        ∑ m ∈ Finset.range n, F ((((m + 1 : ℕ) : ℝ) + 1) * μ) :=
      Finset.sum_congr rfl fun m _ => by push_cast; ring_nf
    linarith [hstep.trans hIH, hshift ▸ (le_refl (∑ m ∈ Finset.range n, F (((m : ℝ) + 1) * μ + μ)))]

/-- **The telescoping bound.** For `u, v > 0` and `u + v ≤ μ`,
`Σ_{m<M} 1/(((m + 1)μ − u)((m + 1)μ + v)) < 1/((u + v)v)`. -/
theorem sum_range_inv_mul_lt {u v μ : ℝ} (hu : 0 < u) (hv : 0 < v) (hμ : u + v ≤ μ) (M : ℕ) :
    ∑ m ∈ Finset.range M, 1 / ((((m : ℝ) + 1) * μ - u) * (((m : ℝ) + 1) * μ + v)) <
      1 / ((u + v) * v) := by
  set d := u + v with hd
  have hd0 : 0 < d := by linarith
  have hterm : ∀ m : ℕ, 1 / ((((m : ℝ) + 1) * μ - u) * (((m : ℝ) + 1) * μ + v)) ≤
      1 / d * (1 / ((m : ℝ) * d + v) - 1 / (((m : ℝ) + 1) * d + v)) := by
    intro m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (m : ℝ) * d + v ≤ ((m : ℝ) + 1) * μ - u := by nlinarith
    have h2 : ((m : ℝ) + 1) * d + v ≤ ((m : ℝ) + 1) * μ + v := by nlinarith
    have hp1 : 0 < (m : ℝ) * d + v := by positivity
    have hp2 : 0 < ((m : ℝ) + 1) * d + v := by positivity
    have e : 1 / d * (1 / ((m : ℝ) * d + v) - 1 / (((m : ℝ) + 1) * d + v)) =
        1 / (((m : ℝ) * d + v) * (((m : ℝ) + 1) * d + v)) := by
      field_simp
      ring
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul h1 h2 hp2.le (by linarith))
  have htel : ∑ m ∈ Finset.range M, (1 / ((m : ℝ) * d + v) - 1 / (((m : ℝ) + 1) * d + v)) =
      1 / v - 1 / ((M : ℝ) * d + v) := by
    have := Finset.sum_range_sub' (fun m : ℕ => 1 / ((m : ℝ) * d + v)) M
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, zero_add] at this
    exact this
  have hM : 0 < 1 / ((M : ℝ) * d + v) := by positivity
  calc ∑ m ∈ Finset.range M, 1 / ((((m : ℝ) + 1) * μ - u) * (((m : ℝ) + 1) * μ + v))
      ≤ ∑ m ∈ Finset.range M, 1 / d * (1 / ((m : ℝ) * d + v) - 1 / (((m : ℝ) + 1) * d + v)) :=
        Finset.sum_le_sum fun m _ => hterm m
    _ = 1 / d * (1 / v - 1 / ((M : ℝ) * d + v)) := by rw [← Finset.mul_sum, htel]
    _ < 1 / d * (1 / v) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
    _ = 1 / (d * v) := by field_simp

/-- **Two close roots of a first-order step are impossible.** For a nonempty family of
`μ`-separated reals avoiding `a` and `b`, with `a < b < a + μ`,
`Σ_x 1/((a − x)(b − x)) ≠ 0`. -/
theorem sum_inv_mul_ne_zero {α : Type*} [DecidableEq α] (T : Finset α) (x : α → ℝ) {μ a b : ℝ}
    (hab : a < b) (hsmall : b - a < μ)
    (hsep : ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → μ ≤ |x w - x w'|)
    (ha : ∀ w ∈ T, x w ≠ a) (hb : ∀ w ∈ T, x w ≠ b) (hT : T.Nonempty) :
    ∑ w ∈ T, 1 / ((a - x w) * (b - x w)) ≠ 0 := by
  have hμ : 0 < μ := by linarith
  by_cases hin : ∀ w ∈ T, ¬ (a < x w ∧ x w < b)
  · -- no point between `a` and `b`: every term is positive
    refine ne_of_gt (Finset.sum_pos (fun w hw => ?_) hT)
    rcases lt_or_gt_of_ne (ha w hw) with h1 | h1
    · exact one_div_pos.mpr (mul_pos (by linarith) (by linarith))
    · have h2 : b < x w := by
        rcases lt_or_gt_of_ne (hb w hw) with h3 | h3
        · exact absurd ⟨h1, h3⟩ (hin w hw)
        · exact h3
      exact one_div_pos.mpr (mul_pos_of_neg_of_neg (by linarith) (by linarith))
  · -- exactly one point `x₀` between them
    push Not at hin
    obtain ⟨w₀, hw₀T, hw₀a, hw₀b⟩ := hin
    have huniq : ∀ w ∈ T, a < x w → x w < b → w = w₀ := by
      intro w hw h1 h2
      by_contra hne
      have h3 := hsep w hw w₀ hw₀T hne
      have : |x w - x w₀| < μ := by rw [abs_sub_lt_iff]; constructor <;> linarith
      linarith
    set x₀ := x w₀ with hx₀
    set u := x₀ - a with hu_def
    set v := b - x₀ with hv_def
    have hu : 0 < u := by rw [hu_def]; linarith
    have hv : 0 < v := by rw [hv_def]; linarith
    have huv : u + v < μ := by rw [hu_def, hv_def]; linarith
    have hterm0 : 1 / ((a - x₀) * (b - x₀)) = -(1 / (u * v)) := by
      rw [show a - x₀ = -u by rw [hu_def]; ring, show b - x₀ = v by rw [hv_def]]
      rw [neg_mul, one_div_neg_eq_neg_one_div]
    -- the other points lie left of `a` or right of `b`, at distance `≥ μ` from `x₀`
    have hside : ∀ w ∈ T.erase w₀, (x w < a ∧ μ ≤ x₀ - x w) ∨ (b < x w ∧ μ ≤ x w - x₀) := by
      intro w hw
      have hwT := Finset.mem_of_mem_erase hw
      have hne := Finset.ne_of_mem_erase hw
      have hd := hsep w hwT w₀ hw₀T hne
      rcases lt_or_gt_of_ne (ha w hwT) with h1 | h1
      · left
        refine ⟨h1, ?_⟩
        rwa [abs_sub_comm, abs_of_nonneg (by rw [← hx₀]; linarith)] at hd
      · right
        have h2 : b < x w := by
          rcases lt_or_gt_of_ne (hb w hwT) with h3 | h3
          · exact absurd (huniq w hwT h1 h3) hne
          · exact h3
        refine ⟨h2, ?_⟩
        rwa [abs_of_nonneg (by rw [← hx₀]; linarith)] at hd
    rw [← Finset.add_sum_erase T _ hw₀T, hterm0,
      ← Finset.sum_filter_add_sum_filter_not (T.erase w₀) (fun w => x w < a)]
    set L := (T.erase w₀).filter (fun w => x w < a) with hL
    set R := (T.erase w₀).filter (fun w => ¬ x w < a) with hR
    have hLmem : ∀ w ∈ L, w ∈ T ∧ x w < a ∧ μ ≤ x₀ - x w := fun w hw => by
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      rcases hside w hw1 with h | h
      · exact ⟨Finset.mem_of_mem_erase hw1, h⟩
      · exact absurd (by linarith [h.1] : ¬ x w < a) (not_not.mpr hw2)
    have hRmem : ∀ w ∈ R, w ∈ T ∧ b < x w ∧ μ ≤ x w - x₀ := fun w hw => by
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      rcases hside w hw1 with h | h
      · exact absurd h.1 hw2
      · exact ⟨Finset.mem_of_mem_erase hw1, h⟩
    -- the left side
    have hLb : ∑ w ∈ L, 1 / ((a - x w) * (b - x w)) < 1 / ((u + v) * v) := by
      have hcount := sum_le_sum_range_of_sep x hμ.le L.card L x₀
        (fun D => 1 / ((D - u) * (D + v))) rfl
        (fun D hD => one_div_nonneg.mpr (mul_nonneg (by linarith) (by linarith)))
        (fun D D' hD hDD' => one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
          (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)))
        (fun w hw w' hw' h => hsep w (hLmem w hw).1 w' (hLmem w' hw').1 h)
        (fun w hw => (hLmem w hw).2.2)
      have e : ∑ w ∈ L, 1 / ((a - x w) * (b - x w)) =
          ∑ w ∈ L, 1 / ((x₀ - x w - u) * (x₀ - x w + v)) :=
        Finset.sum_congr rfl fun w _ => by rw [hu_def, hv_def]; ring_nf
      rw [e]
      exact lt_of_le_of_lt hcount (sum_range_inv_mul_lt hu hv huv.le _)
    -- the right side, by reflection
    have hRb : ∑ w ∈ R, 1 / ((a - x w) * (b - x w)) < 1 / ((v + u) * u) := by
      have hcount := sum_le_sum_range_of_sep (fun w => -x w) hμ.le R.card R (-x₀)
        (fun D => 1 / ((D - v) * (D + u))) rfl
        (fun D hD => one_div_nonneg.mpr (mul_nonneg (by linarith) (by linarith)))
        (fun D D' hD hDD' => one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
          (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)))
        (fun w hw w' hw' h => by
          have := hsep w (hRmem w hw).1 w' (hRmem w' hw').1 h
          rwa [show -x w - -x w' = -(x w - x w') by ring, abs_neg])
        (fun w hw => by have := (hRmem w hw).2.2; linarith)
      have e : ∑ w ∈ R, 1 / ((a - x w) * (b - x w)) =
          ∑ w ∈ R, 1 / ((-x₀ - -x w - v) * (-x₀ - -x w + u)) :=
        Finset.sum_congr rfl fun w _ => by rw [hu_def, hv_def]; ring_nf
      rw [e]
      exact lt_of_le_of_lt hcount (sum_range_inv_mul_lt hv hu (by linarith) _)
    have hsum : 1 / ((u + v) * v) + 1 / ((v + u) * u) = 1 / (u * v) := by
      field_simp
      ring
    intro h0
    linarith

/-! ### Laguerre steps on real configurations -/

/-- Distinct roots of `p` are at distance at least `μ`. -/
def MeshGe (μ : ℝ) (p : ℂ[X]) : Prop := ∀ z ∈ p.roots, ∀ z' ∈ p.roots, z ≠ z' → μ ≤ ‖z - z'‖

theorem im_eq_zero_of_rootsInStrip_zero {p : ℂ[X]} (hp : RootsInStrip 0 p) {z : ℂ}
    (hz : z ∈ p.roots) : z.im = 0 :=
  abs_nonpos_iff.mp (hp z hz)

/-- A simple root of `p` is not a root of `p + cp'` for `c ≠ 0`. -/
theorem eval_ne_zero_of_root_add_smul_derivative {p : ℂ[X]} (hp0 : p ≠ 0) (hnd : p.roots.Nodup)
    {c : ℂ} (hc : c ≠ 0) {y : ℂ} (hy : (p + C c * derivative p).eval y = 0) : p.eval y ≠ 0 := by
  classical
  intro h0
  rw [eval_add, eval_mul, eval_C, h0, zero_add] at hy
  have hd : (derivative p).eval y = 0 := (mul_eq_zero.mp hy).resolve_left hc
  have h1 : 1 < p.rootMultiplicity y := (one_lt_rootMultiplicity_iff_isRoot hp0).mpr ⟨h0, hd⟩
  have h2 := Multiset.nodup_iff_count_le_one.mp hnd y
  rw [count_roots] at h2
  omega

/-- At a root of `p + cp'` off the roots of `p`, the logarithmic derivative is `−1/c`. -/
theorem one_add_mul_logDeriv_eq_zero {p : ℂ[X]} {c y : ℂ} (hy : (p + C c * derivative p).eval y = 0)
    (hpy : p.eval y ≠ 0) : 1 + c * (p.roots.map fun w => 1 / (y - w)).sum = 0 := by
  rw [eval_add, eval_mul, eval_C, (IsAlgClosed.splits p).eval_derivative_eq_eval_mul_sum hpy] at hy
  have : p.eval y * (1 + c * (p.roots.map fun w => 1 / (y - w)).sum) = 0 := by
    rw [← hy]; ring
  exact (mul_eq_zero.mp this).resolve_left hpy

/-- A sum over a nodup multiset is a sum over its finset. -/
theorem multiset_sum_map_eq_finset_sum {s : Multiset ℂ} (hs : s.Nodup) (f : ℂ → ℂ) :
    (s.map f).sum = ∑ w ∈ s.toFinset, f w := by
  rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hs]

/-- **First-order steps never shrink the mesh.** -/
theorem meshGe_add_smul_derivative {p : ℂ[X]} (hp0 : p ≠ 0) (hreal : RootsInStrip 0 p)
    (hnd : p.roots.Nodup) {μ : ℝ} (hmesh : MeshGe μ p) (c : ℝ) :
    MeshGe μ (p + C (c : ℂ) * derivative p) := by
  classical
  intro y hy y' hy' hne
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simp only [Complex.ofReal_zero, map_zero, zero_mul, add_zero] at hy hy'
    exact hmesh y hy y' hy' hne
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hq0 := add_smul_derivative_ne_zero hp0 (c : ℂ)
  have hqreal := rootsInStrip_add_smul_derivative hreal c hq0
  have hyr := im_eq_zero_of_rootsInStrip_zero hqreal hy
  have hyr' := im_eq_zero_of_rootsInStrip_zero hqreal hy'
  have hqy := (mem_roots hq0).mp hy
  have hqy' := (mem_roots hq0).mp hy'
  have hpy := eval_ne_zero_of_root_add_smul_derivative hp0 hnd hc' hqy
  have hpy' := eval_ne_zero_of_root_add_smul_derivative hp0 hnd hc' hqy'
  have hφ := one_add_mul_logDeriv_eq_zero hqy hpy
  have hφ' := one_add_mul_logDeriv_eq_zero hqy' hpy'
  set T := p.roots.toFinset with hT
  have hTmem : ∀ w ∈ T, w ∈ p.roots := fun w hw => Multiset.mem_toFinset.mp hw
  have hwr : ∀ w ∈ T, w.im = 0 := fun w hw => im_eq_zero_of_rootsInStrip_zero hreal (hTmem w hw)
  -- everything is real
  have hreal_eq : ∀ z : ℂ, z.im = 0 → z = (z.re : ℂ) := fun z hz => by
    apply Complex.ext <;> simp [hz]
  have hnorm : ‖y - y'‖ = |y.re - y'.re| := by
    rw [hreal_eq y hyr, hreal_eq y' hyr', ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    simp
  have hsum : ∀ z : ℂ, z.im = 0 → (∀ w ∈ T, w ≠ z) →
      (p.roots.map fun w => 1 / (z - w)).sum = ((∑ w ∈ T, 1 / (z.re - w.re) : ℝ) : ℂ) := by
    intro z hz _
    rw [multiset_sum_map_eq_finset_sum hnd, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hreal_eq z hz, hreal_eq w (hwr w hw)]
    push_cast
    simp
  have hyT : ∀ w ∈ T, w ≠ y := fun w hw h => hpy ((mem_roots hp0).mp (h ▸ hTmem w hw))
  have hyT' : ∀ w ∈ T, w ≠ y' := fun w hw h => hpy' ((mem_roots hp0).mp (h ▸ hTmem w hw))
  rw [hsum y hyr hyT] at hφ
  rw [hsum y' hyr' hyT'] at hφ'
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty, Complex.ofReal_zero, mul_zero, add_zero] at hφ
    exact one_ne_zero hφ
  -- real form of the two equations
  have hreφ : 1 + c * ∑ w ∈ T, 1 / (y.re - w.re) = 0 := by exact_mod_cast hφ
  have hreφ' : 1 + c * ∑ w ∈ T, 1 / (y'.re - w.re) = 0 := by exact_mod_cast hφ'
  have hre_ne : ∀ z : ℂ, z.im = 0 → (∀ w ∈ T, w ≠ z) → ∀ w ∈ T, w.re ≠ z.re := by
    intro z hz hzT w hw h
    exact hzT w hw (Complex.ext h (by rw [hwr w hw, hz]))
  have hsep : ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' → μ ≤ |w.re - w'.re| := by
    intro w hw w' hw' h
    have := hmesh w (hTmem w hw) w' (hTmem w' hw') h
    rwa [hreal_eq w (hwr w hw), hreal_eq w' (hwr w' hw'), ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at this
  -- two close roots would make the separated sum vanish
  have hyy : y.re ≠ y'.re := fun h => hne (Complex.ext h (by rw [hyr, hyr']))
  rw [hnorm]
  by_contra hlt
  push Not at hlt
  have key : ∀ a b : ℝ, a < b → b - a < μ →
      1 + c * ∑ w ∈ T, 1 / (a - w.re) = 0 → 1 + c * ∑ w ∈ T, 1 / (b - w.re) = 0 →
      (∀ w ∈ T, w.re ≠ a) → (∀ w ∈ T, w.re ≠ b) → False := by
    intro a b hab hsmall ha hb hTa hTb
    have hdiff : ∑ w ∈ T, (1 / (a - w.re) - 1 / (b - w.re)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have : c * (∑ w ∈ T, 1 / (a - w.re) - ∑ w ∈ T, 1 / (b - w.re)) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hc
    have hprod : ∑ w ∈ T, (1 / (a - w.re) - 1 / (b - w.re)) =
        (b - a) * ∑ w ∈ T, 1 / ((a - w.re) * (b - w.re)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      have h1 : a - w.re ≠ 0 := sub_ne_zero.mpr (hTa w hw).symm
      have h2 : b - w.re ≠ 0 := sub_ne_zero.mpr (hTb w hw).symm
      field_simp
      ring
    rw [hprod] at hdiff
    have := (mul_eq_zero.mp hdiff).resolve_left (by linarith)
    exact sum_inv_mul_ne_zero T (fun w => w.re) hab hsmall hsep hTa hTb hTne this
  rcases lt_or_gt_of_ne hyy with h | h
  · exact key _ _ h (by rw [abs_sub_lt_iff] at hlt; linarith) hreφ hreφ'
      (hre_ne y hyr hyT) (hre_ne y' hyr' hyT')
  · exact key _ _ h (by rw [abs_sub_lt_iff] at hlt; linarith) hreφ' hreφ
      (hre_ne y' hyr' hyT') (hre_ne y hyr hyT)

/-! ### Simplicity is preserved -/

/-- The logarithmic-derivative sum `Σ_w 1/(x − w)` has derivative `−Σ_w 1/(y − w)²` at `y`. -/
theorem hasDerivAt_sum_inv_sub (s : Multiset ℂ) {y : ℂ} (hy : ∀ w ∈ s, w ≠ y) :
    HasDerivAt (fun x => (s.map fun w => 1 / (x - w)).sum)
      (-(s.map fun w => 1 / (y - w) ^ 2).sum) y := by
  induction s using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const y (0 : ℂ)
  | cons a s ih =>
    have ha : y - a ≠ 0 := sub_ne_zero.mpr (hy a (Multiset.mem_cons_self a s)).symm
    have h0 : HasDerivAt (fun x : ℂ => x - a) 1 y := (hasDerivAt_id' y).sub_const a
    have h1 : HasDerivAt (fun x => 1 / (x - a)) (-(1 / (y - a) ^ 2)) y := by
      have h := (hasDerivAt_inv ha).comp y h0
      rw [show ((fun z : ℂ => z⁻¹) ∘ fun x : ℂ => x - a) = fun x => 1 / (x - a) by
        funext x; simp [one_div]] at h
      exact h.congr_deriv (by simp [one_div])
    have h2 := ih fun w hw => hy w (Multiset.mem_cons_of_mem hw)
    have h3 : HasDerivAt (fun x => 1 / (x - a) + (s.map fun w => 1 / (x - w)).sum)
        (-(1 / (y - a) ^ 2 + (s.map fun w => 1 / (y - w) ^ 2).sum)) y :=
      (h1.add h2).congr_deriv (by ring)
    simpa only [Multiset.map_cons, Multiset.sum_cons] using h3

/-- **The second logarithmic derivative.** Off the roots, `p'' = p (φ² − Σ_w 1/(y − w)²)` with
`φ = Σ_w 1/(y − w)`. -/
theorem eval_derivative_derivative_eq {p : ℂ[X]} {y : ℂ} (hpy : p.eval y ≠ 0) :
    (derivative (derivative p)).eval y =
      p.eval y * ((p.roots.map fun w => 1 / (y - w)).sum ^ 2 -
        (p.roots.map fun w => 1 / (y - w) ^ 2).sum) := by
  have hp0 : p ≠ 0 := fun h => hpy (by rw [h, eval_zero])
  have hy : ∀ w ∈ p.roots, w ≠ y := fun w hw h => hpy ((mem_roots hp0).mp (h ▸ hw))
  have hloc : (fun x => (derivative p).eval x) =ᶠ[𝓝 y]
      fun x => p.eval x * (p.roots.map fun w => 1 / (x - w)).sum := by
    filter_upwards [p.continuous.continuousAt.eventually_ne hpy] with x hx
    exact (IsAlgClosed.splits p).eval_derivative_eq_eval_mul_sum hx
  have hR := (p.hasDerivAt y).mul (hasDerivAt_sum_inv_sub p.roots hy)
  have h := ((derivative p).hasDerivAt y).unique (hR.congr_of_eventuallyEq hloc)
  rw [h, (IsAlgClosed.splits p).eval_derivative_eq_eval_mul_sum hpy]
  ring

theorem re_one_div_sub_sq_pos {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) (hzw : z ≠ w) :
    0 < (1 / (z - w) ^ 2).re := by
  have hr : z.re - w.re ≠ 0 := fun h => hzw (Complex.ext (sub_eq_zero.mp h) (by rw [hz, hw]))
  have e : z - w = ((z.re - w.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hz, hw]
  rw [e, show 1 / ((z.re - w.re : ℝ) : ℂ) ^ 2 = ((1 / (z.re - w.re) ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]
  positivity

/-- **First-order steps keep the roots simple.** -/
theorem nodup_roots_add_smul_derivative {p : ℂ[X]} (hp0 : p ≠ 0) (hreal : RootsInStrip 0 p)
    (hnd : p.roots.Nodup) (c : ℝ) : (p + C (c : ℂ) * derivative p).roots.Nodup := by
  classical
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simpa using hnd
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hq0 := add_smul_derivative_ne_zero hp0 (c : ℂ)
  have hqreal := rootsInStrip_add_smul_derivative hreal c hq0
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rw [count_roots]
  by_contra hlt
  push Not at hlt
  obtain ⟨hqy, hq'y⟩ := (one_lt_rootMultiplicity_iff_isRoot hq0).mp hlt
  have hyr := im_eq_zero_of_rootsInStrip_zero hqreal ((mem_roots hq0).mpr hqy)
  have hpy := eval_ne_zero_of_root_add_smul_derivative hp0 hnd hc' hqy
  have hφ := one_add_mul_logDeriv_eq_zero hqy hpy
  -- at `y` the derivative of `p + cp'` is `−c p(y) Σ_w 1/(y − w)²`
  have hder : (derivative (p + C (c : ℂ) * derivative p)).eval y =
      -(c : ℂ) * p.eval y * (p.roots.map fun w => 1 / (y - w) ^ 2).sum := by
    rw [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add, eval_add, eval_mul,
      eval_C, eval_derivative_derivative_eq hpy,
      (IsAlgClosed.splits p).eval_derivative_eq_eval_mul_sum hpy]
    linear_combination (p.eval y * (p.roots.map fun w => 1 / (y - w)).sum) * hφ
  -- and `Σ_w 1/(y − w)²` is a positive real
  have hroots : p.roots ≠ 0 := fun h0 => by
    rw [h0, Multiset.map_zero, Multiset.sum_zero, mul_zero, add_zero] at hφ
    exact one_ne_zero hφ
  have hS2 : 0 < (p.roots.map fun w => 1 / (y - w) ^ 2).sum.re := by
    have hsum : ∀ u : Multiset ℂ, u.sum.re = (u.map Complex.re).sum := fun u => by
      induction u using Multiset.induction_on <;> simp_all
    rw [hsum, Multiset.map_map]
    refine multiset_sum_pos (by simpa using hroots) fun r hr => ?_
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hr
    have hwy : y ≠ w := fun h => hpy ((mem_roots hp0).mp (h ▸ hw))
    exact re_one_div_sub_sq_pos hyr (im_eq_zero_of_rootsInStrip_zero hreal hw) hwy
  have h0 : (derivative (p + C (c : ℂ) * derivative p)).eval y = 0 := hq'y
  rw [hder] at h0
  have hne : (p.roots.map fun w => 1 / (y - w) ^ 2).sum ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hS2
    exact lt_irrefl _ hS2
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hc') hpy) hne h0

/-! ### Heat steps -/

/-- The heat step `p − c²p''`. -/
def heatStep (c : ℝ) (p : ℂ[X]) : ℂ[X] := p - C ((c : ℂ) ^ 2) * derivative (derivative p)

theorem heatStep_eq (c : ℝ) (p : ℂ[X]) :
    heatStep c p = p + C (c : ℂ) * derivative p +
      C ((-c : ℝ) : ℂ) * derivative (p + C (c : ℂ) * derivative p) := by
  simp only [heatStep, derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    Complex.ofReal_neg, map_neg, map_pow]
  ring

/-- **Heat steps keep real configurations real and simple, and never shrink the mesh.** -/
theorem heatStep_real_simple_mesh {p : ℂ[X]} (hp0 : p ≠ 0) (hreal : RootsInStrip 0 p)
    (hnd : p.roots.Nodup) {μ : ℝ} (hmesh : MeshGe μ p) (c : ℝ) :
    heatStep c p ≠ 0 ∧ RootsInStrip 0 (heatStep c p) ∧ (heatStep c p).roots.Nodup ∧
      MeshGe μ (heatStep c p) := by
  have hq0 := add_smul_derivative_ne_zero hp0 (c : ℂ)
  have hqr := rootsInStrip_add_smul_derivative hreal c hq0
  have hqn := nodup_roots_add_smul_derivative hp0 hreal hnd c
  have hqm := meshGe_add_smul_derivative hp0 hreal hnd hmesh c
  rw [heatStep_eq]
  exact ⟨add_smul_derivative_ne_zero hq0 _,
    rootsInStrip_add_smul_derivative hqr (-c) (add_smul_derivative_ne_zero hq0 _),
    nodup_roots_add_smul_derivative hq0 hqr hqn (-c), meshGe_add_smul_derivative hq0 hqr hqn hqm (-c)⟩

/-- **Heat steps never shrink the mesh.** -/
theorem meshGe_heatStep {p : ℂ[X]} (hp0 : p ≠ 0) (hreal : RootsInStrip 0 p) (hnd : p.roots.Nodup)
    {μ : ℝ} (hmesh : MeshGe μ p) (c : ℝ) : MeshGe μ (heatStep c p) :=
  (heatStep_real_simple_mesh hp0 hreal hnd hmesh c).2.2.2

/-- **The discrete heat flow keeps the mesh.** After any number of heat steps a real configuration
with simple points stays real and simple, and its mesh stays at least `μ`. -/
theorem iterate_heatStep {p : ℂ[X]} (hp0 : p ≠ 0) (hreal : RootsInStrip 0 p) (hnd : p.roots.Nodup)
    {μ : ℝ} (hmesh : MeshGe μ p) (c : ℝ) (n : ℕ) :
    (heatStep c)^[n] p ≠ 0 ∧ RootsInStrip 0 ((heatStep c)^[n] p) ∧
      ((heatStep c)^[n] p).roots.Nodup ∧ MeshGe μ ((heatStep c)^[n] p) := by
  induction n with
  | zero => exact ⟨hp0, hreal, hnd, hmesh⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [Function.iterate_succ_apply']
    exact heatStep_real_simple_mesh h1 h2 h3 h4 c

end GaloisForLFunctions.ZeroConfigurationGeometry
