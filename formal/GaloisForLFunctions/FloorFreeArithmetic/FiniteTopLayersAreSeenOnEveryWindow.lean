import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FiniteTopLayersNeedNoSeparation
import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalRankDecidesTheWindow

/-!
# Finite top layers are seen on every window

A finite exponential sum with distinct real frequencies cannot be small on a whole window,
however short: sampling at a small step turns it into a power sum with distinct unimodular
nodes, and the inverse Vandermonde matrix recovers a coefficient from consecutive samples.
The bound is uniform in the position of the window.

For a zero configuration with a finite nonempty active top layer this gives **uniform
attainment**: the trace normalized by its top exponent is bounded away from zero, in
absolute value, somewhere on every sufficiently late window of every positive length.
Its contrapositive is the non-attainment criterion: one late window on which the normalized
trace is small excludes a finite top layer at that depth.

* `exists_pos_forall_window_le_norm_realExpSum`: the window bound for exponential sums.
* `finite_top_seen_on_every_window`: uniform attainment for a finite top layer.
* `WindowNonAttainment`, `not_windowNonAttainment_of_finite_top`: the criterion.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality

/-! ### Exponential sums on short windows -/

/-- **Window bound for exponential sums.** Distinct real frequencies and a nonzero coefficient
vector give `‖Σ_j c_j e^{iλ_j u}‖ ≥ ε` at some point of every window `[T, T + L]`, with `ε`
independent of `T`. -/
theorem exists_pos_forall_window_le_norm_realExpSum {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (hlam : Function.Injective lam) (c : ι → ℂ) (hc : c ≠ 0) {L : ℝ}
    (hL : 0 < L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ, 0 ≤ T → ∃ u ∈ Icc T (T + L),
      ε ≤ ‖∑ j, c j * cexp (((lam j * u : ℝ) : ℂ) * I)‖ := by
  classical
  set k := Fintype.card ι with hk
  set e : Fin k ≃ ι := (Fintype.equivFin ι).symm with he
  set G : ℝ := ∑ j, |lam j| + 1 with hG
  have hsum0 : 0 ≤ ∑ j, |lam j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hG0 : 0 < G := by linarith only [hsum0, hG]
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- the sampling step: `k` samples fit in the window and the nodes stay distinct
  set h : ℝ := min (L / (k + 1)) (Real.pi / G) with hh
  have hh0 : 0 < h := lt_min (div_pos hL hk1) (div_pos Real.pi_pos hG0)
  have hhL : (k : ℝ) * h ≤ L := by
    have h1 : h ≤ L / (k + 1) := min_le_left _ _
    have h2 := (le_div_iff₀ hk1).mp h1
    nlinarith only [h2, hh0]
  have hhG : G * h ≤ Real.pi := by
    have h2 : h ≤ Real.pi / G := min_le_right _ _
    have h3 := (le_div_iff₀ hG0).mp h2
    linarith only [h3, mul_comm G h]
  set p : Fin k → ℂ := fun j => cexp (((lam (e j) * h : ℝ) : ℂ) * I) with hp
  have hunit : ∀ j, ‖p j‖ = 1 := fun j => Complex.norm_exp_ofReal_mul_I _
  have hinj : Function.Injective p := by
    intro i j hij
    by_contra hne
    have hd : e i ≠ e j := fun h' => hne (e.injective h')
    have hne' : lam (e i) ≠ lam (e j) := fun h' => hd (hlam h')
    have h1 : cexp ((((lam (e i) - lam (e j)) * h : ℝ) : ℂ) * I) = 1 := by
      have hsplit : (((lam (e i) - lam (e j)) * h : ℝ) : ℂ) * I =
          ((lam (e i) * h : ℝ) : ℂ) * I - ((lam (e j) * h : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [hsplit, Complex.exp_sub]
      exact div_eq_one_iff_eq (Complex.exp_ne_zero _) |>.mpr hij
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    have hreal : (lam (e i) - lam (e j)) * h = n * (2 * Real.pi) := by
      have him := congrArg Complex.im hn
      simpa using him
    have h3 : |lam (e i) - lam (e j)| ≤ ∑ j, |lam j| := by
      have hpair := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({e i, e j} : Finset ι)) (fun x _ _ => abs_nonneg (lam x))
      rw [Finset.sum_pair hd] at hpair
      exact (abs_sub _ _).trans hpair
    have hbound : |(lam (e i) - lam (e j)) * h| < 2 * Real.pi := by
      rw [abs_mul, abs_of_pos hh0]
      have h4 := mul_le_mul_of_nonneg_right h3 hh0.le
      nlinarith only [h4, hhG, hG, hh0, Real.pi_pos]
    have hn0 : n = 0 := by
      by_contra hn0
      have h5 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      rw [hreal, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hbound
      nlinarith only [hbound, h5, Real.pi_pos]
    rw [hn0, Int.cast_zero, zero_mul] at hreal
    rcases mul_eq_zero.mp hreal with h0 | h0
    · exact hne' (sub_eq_zero.mp h0)
    · exact hh0.ne' h0
  have hc' : (fun j => c (e j)) ≠ 0 := by
    intro h0
    apply hc
    funext i
    have h1 := congrFun h0 (e.symm i)
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using h1
  obtain ⟨ε, hε, hwin⟩ :=
    InfiniteRankWeilTheory.exists_pos_forall_window_le_norm_expSum p hinj hunit _ hc'
  refine ⟨ε, hε, fun T hT => ?_⟩
  -- the first sample beyond `T`
  set M : ℕ := ⌊T / h⌋₊ with hM
  obtain ⟨m, hm⟩ := hwin M
  have hMh : (M : ℝ) * h ≤ T := (le_div_iff₀ hh0).mp (Nat.floor_le (div_nonneg hT hh0.le))
  have hMh' : T < ((M : ℝ) + 1) * h := (div_lt_iff₀ hh0).mp (Nat.lt_floor_add_one _)
  have hmk : ((m : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast m.2
  have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨((M + 1 + (m : ℕ) : ℕ) : ℝ) * h, ⟨?_, ?_⟩, ?_⟩
  · push_cast
    nlinarith only [hMh', hm0, hh0]
  · push_cast
    nlinarith only [hMh, hmk, hhL, hh0]
  · refine hm.trans (le_of_eq ?_)
    rw [← e.sum_comp]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [hp]
    simp only
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

/-! ### Uniform attainment for a finite top layer -/

/-- The top trace of a finite layer as an exponential sum over the frequencies `±γ`. -/
theorem topTrace_eq_two_sided_sum {Z : ZeroConfig} {b : ℝ} (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) (u : ℝ) :
    ((topTrace Z b u : ℝ) : ℂ) =
      ∑ x : S ⊕ S, Sum.elim (fun z : S => evenCoeff Z (boxSpline 1 3) z)
          (fun z : S => conj (evenCoeff Z (boxSpline 1 3) z)) x *
        cexp (((Sum.elim (fun z : S => (z : ℂ).im) (fun z : S => -(z : ℂ).im) x * u : ℝ) : ℂ) * I) := by
  rw [topTrace_eq_positive_sum S hS hreal u, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  set g : ℂ := ∑ z ∈ S, (2 * evenCoeff Z (boxSpline 1 3) z) *
    cexp (((z.im * u : ℝ) : ℂ) * I) with hg
  have hre : ((g.re : ℝ) : ℂ) = (g + conj g) / 2 := by
    rw [Complex.add_conj]
    push_cast
    ring
  rw [hre, hg, map_sum, Finset.sum_coe_sort S (fun z : ℂ =>
      evenCoeff Z (boxSpline 1 3) z * cexp (((z.im * u : ℝ) : ℂ) * I)),
    Finset.sum_coe_sort S (fun z : ℂ =>
      conj (evenCoeff Z (boxSpline 1 3) z) * cexp (((-z.im * u : ℝ) : ℂ) * I)),
    ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hc : conj (cexp (((z.im * u : ℝ) : ℂ) * I)) = cexp (((-z.im * u : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [map_mul, map_mul, hc]
  simp only [map_ofNat]
  ring

/-- **Uniform attainment.** A finite nonempty active top layer makes the normalized trace at
least `c > 0` in absolute value somewhere on every late window of every length `L > 0`. -/
theorem finite_top_seen_on_every_window {Z : ZeroConfig} (hZ : TemperedConfig Z) {b L : ℝ}
    (htop : TopDepth Z b) (hL : 0 < L) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b) (hne : S.Nonempty)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) :
    ∃ c U : ℝ, 0 < c ∧ ∀ T : ℝ, U ≤ T → ∃ u ∈ Icc T (T + L), c ≤ |normTrace Z b u| := by
  classical
  set lam : S ⊕ S → ℝ := Sum.elim (fun z : S => (z : ℂ).im) (fun z : S => -(z : ℂ).im)
    with hlam
  set a : S ⊕ S → ℂ := Sum.elim (fun z : S => evenCoeff Z (boxSpline 1 3) z)
    (fun z : S => conj (evenCoeff Z (boxSpline 1 3) z)) with ha
  have hpos : ∀ z : S, 0 < (z : ℂ).im := fun z => ((hS z).mp z.2).2.1
  have him : ∀ z w : S, (z : ℂ).im = (w : ℂ).im → z = w := by
    intro z w h
    apply Subtype.ext
    apply Complex.ext
    · exact (((hS z).mp z.2).1).trans (((hS w).mp w.2).1).symm
    · exact h
  have hinj : Function.Injective lam := by
    rintro (z | z) (w | w) h
    · exact congrArg Sum.inl (him z w h)
    · simp only [hlam, Sum.elim_inl, Sum.elim_inr] at h
      linarith only [h, hpos z, hpos w]
    · simp only [hlam, Sum.elim_inl, Sum.elim_inr] at h
      linarith only [h, hpos z, hpos w]
    · exact congrArg Sum.inr (him z w (neg_injective h))
  have hane : a ≠ 0 := by
    obtain ⟨z, hz⟩ := hne
    intro h0
    have h1 := congrFun h0 (Sum.inl ⟨z, hz⟩)
    exact ((hS z).mp hz).2.2 h1
  obtain ⟨ε, hε, hwin⟩ := exists_pos_forall_window_le_norm_realExpSum lam hinj a hane hL
  have hrem := tendsto_normTrace_sub_topTrace hZ htop
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    ((tendsto_order.mp hrem).1 (-(ε / 2)) (by linarith only [hε]) |>.and
      ((tendsto_order.mp hrem).2 (ε / 2) (by linarith only [hε])))
  refine ⟨ε / 2, max V 0, by linarith only [hε], fun T hT => ?_⟩
  obtain ⟨u, hu, hbig⟩ := hwin T ((le_max_right V 0).trans hT)
  refine ⟨u, hu, ?_⟩
  obtain ⟨hlo, hhi⟩ := hV u (((le_max_left V 0).trans hT).trans hu.1)
  have htopbig : ε ≤ |topTrace Z b u| := by
    rw [← Complex.norm_real, topTrace_eq_two_sided_sum S hS hreal u]
    exact hbig
  have htri : |topTrace Z b u| ≤ |normTrace Z b u| + |normTrace Z b u - topTrace Z b u| := by
    have h := abs_sub_abs_le_abs_sub (topTrace Z b u) (normTrace Z b u)
    rw [abs_sub_comm (topTrace Z b u)] at h
    linarith only [h]
  have hsmall : |normTrace Z b u - topTrace Z b u| ≤ ε / 2 := abs_le.mpr ⟨hlo.le, hhi.le⟩
  linarith only [htopbig, htri, hsmall]

/-! ### The non-attainment criterion -/

/-- **Window non-attainment** at depth `b` and length `L`: on arbitrarily late windows of
length `L` the trace is of smaller order than `e^{bu}`. -/
def WindowNonAttainment (Z : ZeroConfig) (b L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u ∈ Icc T (T + L), |normTrace Z b u| ≤ ε

/-- Non-attainment is inherited by shorter windows. -/
theorem WindowNonAttainment.mono {Z : ZeroConfig} {b L L' : ℝ}
    (h : WindowNonAttainment Z b L) (hL : L' ≤ L) : WindowNonAttainment Z b L' := by
  intro ε hε U
  obtain ⟨T, hT, hwin⟩ := h ε hε U
  exact ⟨T, hT, fun u hu => hwin u ⟨hu.1, hu.2.trans (by linarith only [hL])⟩⟩

/-- A finite nonempty active top layer at depth `b` is attained on every window: window
non-attainment fails at every positive length. -/
theorem not_windowNonAttainment_of_finite_top {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {b L : ℝ} (htop : TopDepth Z b) (hL : 0 < L) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b) (hne : S.Nonempty)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) :
    ¬ WindowNonAttainment Z b L := by
  intro hN
  obtain ⟨c, U, hc, hwin⟩ := finite_top_seen_on_every_window hZ htop hL S hS hne hreal
  obtain ⟨T, hT, hsmall⟩ := hN (c / 2) (by linarith only [hc]) U
  obtain ⟨u, hu, hbig⟩ := hwin T hT
  linarith only [hsmall u hu, hbig, hc]

/-- An empty active top line gives non-attainment on every window: the normalized trace
tends to zero. -/
theorem windowNonAttainment_of_topTrace_eq_zero {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {b : ℝ} (htop : TopDepth Z b) (hzero : ∀ u, topTrace Z b u = 0) (L : ℝ) :
    WindowNonAttainment Z b L := by
  intro ε hε U
  have hrem := tendsto_normTrace_sub_topTrace hZ htop
  simp only [hzero, sub_zero] at hrem
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    ((tendsto_order.mp hrem).1 (-ε) (by linarith only [hε]) |>.and
      ((tendsto_order.mp hrem).2 ε hε))
  refine ⟨max U V, le_max_left _ _, fun u hu => ?_⟩
  obtain ⟨hlo, hhi⟩ := hV u ((le_max_right U V).trans hu.1)
  exact abs_le.mpr ⟨hlo.le, hhi.le⟩

end GaloisForLFunctions.FloorFreeArithmetic
