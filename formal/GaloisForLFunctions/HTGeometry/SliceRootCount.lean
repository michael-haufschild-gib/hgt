import GaloisForLFunctions.HTGeometry.SliceRootHolomorphy

/-!
# The number of roots of a slice is locally constant

The zeroth moment of the logarithmic derivative counts the roots of a slice inside the circle.
Being a contour integral it is holomorphic in the remaining variables, and being a count it takes
values in the natural numbers; a continuous integer-valued function is locally constant, so on a
connected set of parameters the slices all have the same number of roots.

That fixed number is the degree of the Weierstrass polynomial.

* `HTGeometry.sliceMoment_zero_eq_card`;
* `HTGeometry.eventually_card_sliceRoots_eq`;
* `HTGeometry.card_sliceRoots_const_of_isPreconnected`.
-/

open Complex Metric
open scoped Real Topology

namespace HTGeometry

variable {n : ℕ}

/-- **The zeroth moment counts the roots.** -/
theorem sliceMoment_zero_eq_card {f : (Fin (n + 1) → ℂ) → ℂ} {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℂ} (hy : SliceAdmissible f t y) :
    sliceMoment f t 0 y = ((sliceRoots f t y).card : ℂ) := by
  rw [sliceMoment_eq_powerSum ht hy 0]
  have hmap : (sliceRoots f t y).map (fun x : ℂ => x ^ 0)
      = Multiset.replicate (sliceRoots f t y).card (1 : ℂ) := by
    rw [← Multiset.map_const']
    exact Multiset.map_congr rfl fun x _ => pow_zero x
  rw [hmap, Multiset.sum_replicate, nsmul_eq_mul, mul_one]

/-- Two natural numbers whose complex casts are less than one apart are equal. -/
theorem natCast_eq_of_norm_sub_lt_one {a b : ℕ} (h : ‖(a : ℂ) - (b : ℂ)‖ < 1) : a = b := by
  by_contra hne
  have hint : ((a : ℤ) - (b : ℤ)) ≠ 0 := by
    intro hcon
    exact hne (by omega)
  have hcast : ((a : ℂ) - (b : ℂ)) = (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) := by
    push_cast
    ring
  rw [hcast] at h
  have hone : (1 : ℝ) ≤ ‖(((a : ℤ) - (b : ℤ) : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    have : (1 : ℤ) ≤ |(a : ℤ) - (b : ℤ)| := Int.one_le_abs hint
    exact_mod_cast this
  linarith

/-- **The number of roots is locally constant.** -/
theorem eventually_card_sliceRoots_eq {f : (Fin (n + 1) → ℂ) → ℂ} {U : Set (Fin (n + 1) → ℂ)}
    {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) {y₀ : Fin n → ℂ} (hy₀ : y₀ ∈ V) :
    ∀ᶠ y in 𝓝[V] y₀, (sliceRoots f t y).card = (sliceRoots f t y₀).card := by
  have hcont : ContinuousWithinAt (sliceMoment f t 0) V y₀ :=
    ((differentiableOn_sliceMoment hU hV hf ht hdisc hnez 0).continuousOn) y₀ hy₀
  have hball : ∀ᶠ y in 𝓝[V] y₀, ‖sliceMoment f t 0 y - sliceMoment f t 0 y₀‖ < 1 := by
    have := hcont.tendsto
    have hmem : Metric.ball (sliceMoment f t 0 y₀) 1 ∈ 𝓝 (sliceMoment f t 0 y₀) :=
      Metric.ball_mem_nhds _ one_pos
    filter_upwards [this hmem] with y hy
    simpa [Complex.dist_eq] using Metric.mem_ball.1 hy
  filter_upwards [hball, self_mem_nhdsWithin] with y hy hyV
  rw [sliceMoment_zero_eq_card ht (hadm y hyV), sliceMoment_zero_eq_card ht (hadm y₀ hy₀)] at hy
  exact natCast_eq_of_norm_sub_lt_one hy

/-- **On a connected set of parameters every slice has the same number of roots.** -/
theorem card_sliceRoots_const_of_isPreconnected {f : (Fin (n + 1) → ℂ) → ℂ}
    {U : Set (Fin (n + 1) → ℂ)} {V : Set (Fin n → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f U) {t : ℝ} (ht : 0 < t)
    (hdisc : ∀ y ∈ V, ∀ z : ℂ, ‖z‖ ≤ t → (Fin.cons z y : Fin (n + 1) → ℂ) ∈ U)
    (hnez : ∀ y ∈ V, ∀ ζ : ℂ, ‖ζ‖ = t → f (Fin.cons ζ y) ≠ 0)
    (hadm : ∀ y ∈ V, SliceAdmissible f t y) (hVconn : IsPreconnected V)
    {y₀ y₁ : Fin n → ℂ} (h₀ : y₀ ∈ V) (h₁ : y₁ ∈ V) :
    (sliceRoots f t y₀).card = (sliceRoots f t y₁).card := by
  refine hVconn.constant (f := fun y => (sliceRoots f t y).card) ?_ h₀ h₁
  intro y hy
  have hloc := eventually_card_sliceRoots_eq hU hV hf ht hdisc hnez hadm hy
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  exact hloc.mono fun w hw => hw.symm

end HTGeometry
