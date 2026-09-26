import GaloisForLFunctions.RHTower.CircleZeroFreeDatumSeamMargin

/-!
# Seam margin of a truncated Euler product

For a finite set `S` of integers `≥ 2` let `E_S(s) = Π_{p ∈ S} (1 − p^{−s})^{−1}`.  It is
holomorphic and zero-free on `Re s > 0`.  On every closed disc contained in `Re s ≥ σ₁ > 0`,

`1 − ‖(1 − P) U† P‖² ≥ Π_{p ∈ S} (1 − p^{−σ₁}) / (1 + p^{−σ₁})`
(`truncatedEulerDisc_one_sub_seam_sq_ge`),

uniformly in the height and the radius, because `|1 − p^{−s}|` lies between `1 − p^{−σ₁}` and
`1 + p^{−σ₁}`.  Inside the critical strip the truncated Euler phase is therefore uniformly
contracting at every height.  Its margin tends to `0` as `S` exhausts the primes exactly when
`Σ_p p^{−σ₁} = ∞`, i.e. for `σ₁ ≤ 1`.  Route 1's seam for `ζ` differs from this one by the phase
of the tail product `ζ / E_S`, which carries all the zeros.
-/

noncomputable section

open Complex Metric

namespace RHTower

/-- The truncated Euler product `Π_{p ∈ S} (1 − p^{−s})^{−1}`. -/
def truncatedEuler (S : Finset ℕ) (s : ℂ) : ℂ := ∏ p ∈ S, (1 - (p : ℂ) ^ (-s))⁻¹

theorem norm_natCast_cpow_neg {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]

theorem rpow_neg_lt_one {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 0 < σ) : (p : ℝ) ^ (-σ) < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

theorem one_sub_cpow_ne_zero {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have := congrArg norm h1
  rw [norm_natCast_cpow_neg hp, norm_one] at this
  exact (rpow_neg_lt_one hp hs).ne this

theorem norm_one_sub_cpow_bounds {p : ℕ} (hp : 2 ≤ p) {σ₁ : ℝ} {s : ℂ} (hs : σ₁ ≤ s.re) :
    1 - (p : ℝ) ^ (-σ₁) ≤ ‖1 - (p : ℂ) ^ (-s)‖ ∧ ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-σ₁) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hle : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-σ₁) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hn := norm_natCast_cpow_neg hp s
  constructor
  · have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hn] at this
    linarith
  · have := norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hn] at this
    linarith

theorem differentiableAt_truncatedEuler (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (truncatedEuler S) s := by
  unfold truncatedEuler
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  have hp2 := hS p hp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  exact ((differentiableAt_const _).sub
    ((differentiableAt_id.neg).const_cpow (Or.inl hp0))).inv (one_sub_cpow_ne_zero hp2 hs)

theorem truncatedEuler_ne_zero (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    truncatedEuler S s ≠ 0 := by
  unfold truncatedEuler
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact inv_ne_zero (one_sub_cpow_ne_zero (hS p hp) hs)

/-- The disc datum of `E_S` on a disc contained in `Re s ≥ σ₁ > 0`. -/
def truncatedEulerDiscDatum (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) {σ₁ : ℝ} (hσ₁ : 0 < σ₁)
    (c : ℂ) (t : ℝ) (ht : 0 < t) (hc : σ₁ + t ≤ c.re) : DiscArgumentDatum where
  c := c
  t := t
  R := t + σ₁ / 4
  U := {s : ℂ | σ₁ / 2 < s.re}
  F := truncatedEuler S
  t_pos := ht
  t_lt_R := by linarith
  isOpen := isOpen_lt continuous_const Complex.continuous_re
  closedBall_subset := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (z.re - c.re)
    show σ₁ / 2 < z.re
    linarith
  differentiableOn := fun s hs => by
    have : 0 < s.re := by
      have := hs; simp only [Set.mem_setOf_eq] at this; linarith
    exact (differentiableAt_truncatedEuler S hS this).differentiableWithinAt
  ne_zero := fun ζ hζ => by
    apply truncatedEuler_ne_zero S hS
    rw [mem_sphere, dist_eq_norm] at hζ
    have h1 : |(ζ - c).re| ≤ ‖ζ - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (ζ.re - c.re)
    linarith

/-- **Height-uniform margin of the truncated Euler phase.** -/
theorem truncatedEulerDisc_one_sub_seam_sq_ge (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) {σ₁ : ℝ}
    (hσ₁ : 0 < σ₁) (c : ℂ) (t : ℝ) (ht : 0 < t) (hc : σ₁ + t ≤ c.re) :
    (∏ p ∈ S, (1 - (p : ℝ) ^ (-σ₁)) / (1 + (p : ℝ) ^ (-σ₁))) ≤
      1 - ‖(truncatedEulerDiscDatum S hS hσ₁ c t ht hc).circlePhase.datum.adjointHankelSeam‖ ^ 2 := by
  have hre : ∀ z ∈ closedBall c t, σ₁ ≤ z.re := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (z.re - c.re)
    linarith
  set m : ℝ := ∏ p ∈ S, (1 + (p : ℝ) ^ (-σ₁))⁻¹ with hm
  set M : ℝ := ∏ p ∈ S, (1 - (p : ℝ) ^ (-σ₁))⁻¹ with hM
  have hlow : ∀ p ∈ S, 0 < 1 - (p : ℝ) ^ (-σ₁) := fun p hp => by
    have := rpow_neg_lt_one (hS p hp) hσ₁; linarith
  have hpow_nn : ∀ p ∈ S, 0 ≤ (p : ℝ) ^ (-σ₁) := fun p _ =>
    Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hmpos : 0 < m := Finset.prod_pos fun p hp => by
    have := hpow_nn p hp; positivity
  have hbounds : ∀ ζ ∈ sphere c t, m ≤ ‖truncatedEuler S ζ‖ ∧ ‖truncatedEuler S ζ‖ ≤ M := by
    intro ζ hζ
    have hζre := hre ζ (sphere_subset_closedBall hζ)
    unfold truncatedEuler
    rw [norm_prod]
    constructor
    · apply Finset.prod_le_prod
      · intro p hp; have := hpow_nn p hp; positivity
      · intro p hp
        obtain ⟨h1, h2⟩ := norm_one_sub_cpow_bounds (hS p hp) hζre
        have hpos : 0 < ‖1 - (p : ℂ) ^ (-ζ)‖ := lt_of_lt_of_le (hlow p hp) h1
        rw [norm_inv]
        exact inv_anti₀ hpos h2
    · apply Finset.prod_le_prod
      · intro p _; exact norm_nonneg _
      · intro p hp
        obtain ⟨h1, _⟩ := norm_one_sub_cpow_bounds (hS p hp) hζre
        rw [norm_inv]
        exact inv_anti₀ (hlow p hp) h1
  have h := (truncatedEulerDiscDatum S hS hσ₁ c t ht hc).one_sub_seam_sq_ge
    (fun z hz => truncatedEuler_ne_zero S hS (by linarith [hre z hz])) hmpos hbounds
  have hval : m / M = ∏ p ∈ S, (1 - (p : ℝ) ^ (-σ₁)) / (1 + (p : ℝ) ^ (-σ₁)) := by
    rw [hm, hM, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have h1 := hlow p hp
    have h2 : 0 < 1 + (p : ℝ) ^ (-σ₁) := by have := hpow_nn p hp; linarith
    field_simp
  rw [hval] at h
  exact h

end RHTower
