import GaloisForLFunctions.HTGeometry.IntervalSeparation

/-!
# Sturm comparison on a short arch

If a function vanishes at two points closer than `π/γ` and is positive in between, its Sturm
expression `g'' + γ² g` must take a strictly negative value on the arch.

The proof is the inhomogeneous Wronskian.  Against the comparison solution `w(t) = sin(γ(t-p))` the
Wronskian `φ = g'w - g w'` has derivative `(g'' + γ² g) w`.  If the Sturm expression never went
negative, `φ` would be nondecreasing from `φ(p) = 0`, while `φ(q) = g'(q) w(q) ≤ 0` because the arch
descends to its right endpoint — forcing `φ ≡ 0`, hence `g'' + γ² g ≡ 0` on the arch and
`g'(q) = 0`.  The energy `g'² + γ² g²` is then constant and vanishes at `q`, so `g ≡ 0`, contradicting
positivity.

This is the analytic input that converts the interval criterion of `IntervalSeparation` into an
effective one: it bounds how often the log-concavity of a comparison function can fail, because the
relevant Sturm expressions are again exponential polynomials.
-/

open Set Real

namespace GaloisForLFunctions.HTGeometry

/-- **Sturm comparison on a short arch.** -/
theorem exists_sturm_neg {g gd gdd h : ℝ → ℝ} {γ p q : ℝ} (hγ : 0 < γ)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ 2 * g t)
    (hpq : p < q) (hlen : q - p < π / γ)
    (hgp : g p = 0) (hgq : g q = 0) (hpos : ∀ t ∈ Ioo p q, 0 < g t) :
    ∃ ξ ∈ Ioo p q, h ξ < 0 := by
  by_contra hcon
  push Not at hcon
  -- the comparison solution
  set w : ℝ → ℝ := fun t => Real.sin (γ * (t - p)) with hw
  set wd : ℝ → ℝ := fun t => γ * Real.cos (γ * (t - p)) with hwd
  have hin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => γ * (s - p)) γ t := by
    intro t
    simpa using ((hasDerivAt_id t).sub_const p).const_mul γ
  have hwderiv : ∀ t, HasDerivAt w (wd t) t := by
    intro t
    refine ((hin t).sin).congr_deriv ?_
    rw [hwd]
    ring
  have hwdderiv : ∀ t, HasDerivAt wd (-(γ ^ 2) * w t) t := by
    intro t
    refine (((hin t).cos).const_mul γ).congr_deriv ?_
    rw [hw]
    ring
  have hγπ : γ * (q - p) < π := by
    rw [lt_div_iff₀ hγ] at hlen
    nlinarith
  have hwpos : ∀ t ∈ Ioc p q, 0 < w t := by
    intro t ht
    rw [hw]
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  -- the inhomogeneous Wronskian
  set φ : ℝ → ℝ := fun t => gd t * w t - g t * wd t with hφ
  have hφderiv : ∀ t, HasDerivAt φ (h t * w t) t := by
    intro t
    refine (((hgd t).mul (hwderiv t)).sub ((hg t).mul (hwdderiv t))).congr_deriv ?_
    rw [hh]
    ring
  have hφp : φ p = 0 := by
    show gd p * w p - g p * wd p = 0
    rw [hgp, hw]
    simp
  have hmono : MonotoneOn φ (Icc p q) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q)
      (fun t _ => ((hφderiv t).continuousAt).continuousWithinAt)
      (fun t _ => ((hφderiv t).differentiableAt).differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hφderiv t).deriv]
    exact mul_nonneg (hcon t ht) (le_of_lt (hwpos t ⟨ht.1, le_of_lt ht.2⟩))
  have hφq0 : 0 ≤ φ q := by
    have := hmono (left_mem_Icc.mpr hpq.le) (right_mem_Icc.mpr hpq.le) hpq.le
    linarith [hφp]
  -- the arch descends at its right endpoint
  have hgdq : gd q ≤ 0 := by
    have hslope := hasDerivAt_iff_tendsto_slope.mp (hg q)
    have hsub : Set.Iio q ⊆ ({q}ᶜ : Set ℝ) := fun x hx => ne_of_lt hx
    have htend : Filter.Tendsto (slope g q) (nhdsWithin q (Set.Iio q)) (nhds (gd q)) :=
      hslope.mono_left (nhdsWithin_mono q hsub)
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hpq)] with s hs1 hs2
    have hslt : s < q := hs1
    have hgs : 0 < g s := hpos s ⟨hs2, hslt⟩
    rw [slope_def_field, hgq]
    have hden : s - q < 0 := by linarith
    have hq : (g s - 0) / (s - q) < 0 := div_neg_of_pos_of_neg (by linarith) hden
    linarith
  have hwq : 0 < w q := hwpos q ⟨hpq, le_refl q⟩
  have hφq : φ q = gd q * w q := by
    show gd q * w q - g q * wd q = gd q * w q
    rw [hgq]
    ring
  have hφqle : φ q ≤ 0 := by
    rw [hφq]
    nlinarith
  have hφqz : φ q = 0 := le_antisymm hφqle hφq0
  have hgdqz : gd q = 0 := by
    rw [hφq] at hφqz
    exact (mul_eq_zero.mp hφqz).resolve_right (ne_of_gt hwq)
  -- the Wronskian vanishes identically, hence so does the Sturm expression
  have hφzero : ∀ t ∈ Icc p q, φ t = 0 := by
    intro t ht
    have h1 := hmono (left_mem_Icc.mpr hpq.le) ht ht.1
    have h2 := hmono ht (right_mem_Icc.mpr hpq.le) ht.2
    rw [hφp] at h1
    rw [hφqz] at h2
    linarith
  have hhzero : ∀ t ∈ Ioo p q, h t = 0 := by
    intro t ht
    have hev : φ =ᶠ[nhds t] (fun _ => (0 : ℝ)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
        (fun s hs => hφzero s (Ioo_subset_Icc_self hs))
    have h0 : HasDerivAt φ 0 t := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
    have huniq := (hφderiv t).unique h0
    exact (mul_eq_zero.mp huniq).resolve_right (ne_of_gt (hwpos t ⟨ht.1, le_of_lt ht.2⟩))
  -- the energy is constant and vanishes
  set E : ℝ → ℝ := fun t => gd t ^ 2 + γ ^ 2 * g t ^ 2 with hE
  have hEderiv : ∀ t, HasDerivAt E (2 * gd t * h t) t := by
    intro t
    have h1 : HasDerivAt (fun s => gd s ^ 2) (2 * gd t ^ 1 * gdd t) t := (hgd t).pow 2
    have h2 : HasDerivAt (fun s => γ ^ 2 * g s ^ 2) (γ ^ 2 * (2 * g t ^ 1 * gd t)) t :=
      ((hg t).pow 2).const_mul (γ ^ 2)
    refine (h1.add h2).congr_deriv ?_
    rw [hh]
    ring
  have hEmono : MonotoneOn E (Icc p q) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc p q)
      (fun t _ => ((hEderiv t).continuousAt).continuousWithinAt)
      (fun t _ => ((hEderiv t).differentiableAt).differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hEderiv t).deriv, hhzero t ht]
    simp
  have hEanti : AntitoneOn E (Icc p q) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc p q)
      (fun t _ => ((hEderiv t).continuousAt).continuousWithinAt)
      (fun t _ => ((hEderiv t).differentiableAt).differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hEderiv t).deriv, hhzero t ht]
    simp
  have hEq : E q = 0 := by
    show gd q ^ 2 + γ ^ 2 * g q ^ 2 = 0
    rw [hgq, hgdqz]
    ring
  have hmid : (p + q) / 2 ∈ Ioo p q := ⟨by linarith, by linarith⟩
  have h1 := hEmono (Ioo_subset_Icc_self hmid) (right_mem_Icc.mpr hpq.le) (le_of_lt hmid.2)
  have h2 := hEanti (Ioo_subset_Icc_self hmid) (right_mem_Icc.mpr hpq.le) (le_of_lt hmid.2)
  rw [hEq] at h1 h2
  have hEmid : E ((p + q) / 2) = 0 := le_antisymm h1 h2
  have hgmid : 0 < g ((p + q) / 2) := hpos _ hmid
  have hEmid' : gd ((p + q) / 2) ^ 2 + γ ^ 2 * g ((p + q) / 2) ^ 2 = 0 := hEmid
  have hpos1 : 0 < γ ^ 2 * g ((p + q) / 2) ^ 2 :=
    mul_pos (pow_pos hγ 2) (pow_pos hgmid 2)
  linarith [sq_nonneg (gd ((p + q) / 2))]


/-- The mirrored statement for a negative arch. -/
theorem exists_sturm_pos {g gd gdd h : ℝ → ℝ} {γ p q : ℝ} (hγ : 0 < γ)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ 2 * g t)
    (hpq : p < q) (hlen : q - p < π / γ)
    (hgp : g p = 0) (hgq : g q = 0) (hneg : ∀ t ∈ Ioo p q, g t < 0) :
    ∃ ξ ∈ Ioo p q, 0 < h ξ := by
  obtain ⟨ξ, hξ, hval⟩ := exists_sturm_neg (g := fun t => -g t) (gd := fun t => -gd t)
    (gdd := fun t => -gdd t) (h := fun t => -h t) hγ
    (fun t => (hg t).neg) (fun t => (hgd t).neg)
    (fun t => by rw [hh]; ring) hpq hlen (by rw [hgp]; ring) (by rw [hgq]; ring)
    (fun t ht => by have := hneg t ht; linarith)
  exact ⟨ξ, hξ, by linarith⟩

/-- **A zero of the Sturm expression between adjacent short arches.**  Two consecutive arches of
opposite sign, each shorter than `π/γ`, force `g'' + γ² g` to change sign, hence to vanish. -/
theorem exists_sturm_zero {g gd gdd h : ℝ → ℝ} {γ p q s : ℝ} (hγ : 0 < γ)
    (hg : ∀ t, HasDerivAt g (gd t) t) (hgd : ∀ t, HasDerivAt gd (gdd t) t)
    (hh : ∀ t, h t = gdd t + γ ^ 2 * g t) (hhcont : Continuous h)
    (hpq : p < q) (hqs : q < s)
    (hlen1 : q - p < π / γ) (hlen2 : s - q < π / γ)
    (hgp : g p = 0) (hgq : g q = 0) (hgs : g s = 0)
    (hpos : ∀ t ∈ Ioo p q, 0 < g t) (hneg : ∀ t ∈ Ioo q s, g t < 0) :
    ∃ ξ ∈ Ioo p s, h ξ = 0 := by
  obtain ⟨ξ₁, hξ₁, hv₁⟩ := exists_sturm_neg hγ hg hgd hh hpq hlen1 hgp hgq hpos
  obtain ⟨ξ₂, hξ₂, hv₂⟩ := exists_sturm_pos hγ hg hgd hh hqs hlen2 hgq hgs hneg
  have hlt : ξ₁ < ξ₂ := lt_trans hξ₁.2 hξ₂.1
  obtain ⟨ξ, hξmem, hξ0⟩ := intermediate_value_Ioo (le_of_lt hlt) hhcont.continuousOn
    (show (0 : ℝ) ∈ Ioo (h ξ₁) (h ξ₂) from ⟨hv₁, hv₂⟩)
  exact ⟨ξ, ⟨lt_trans hξ₁.1 hξmem.1, lt_trans hξmem.2 hξ₂.2⟩, hξ0⟩

end GaloisForLFunctions.HTGeometry
