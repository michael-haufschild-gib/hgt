import GaloisForLFunctions.ArithmeticDiscreteness.TheCuspRepelsAtPolynomialScale
import GaloisForLFunctions.ArithmeticDiscreteness.TheCuspIsTheOnlyConsistentTangency
import GaloisForLFunctions.ArithmeticDiscreteness.ConsistentTangenciesAreTheOnlySourceOfNearCoincidences

/-!
# The cusp carrier repels at polynomial scale

A complete polynomial collide-or-repel law for a non-product integral carrier. The cusp carrier
`D(s) = (1 − 2^{−s})² − (1 − 3^{−s})³` has near-coincidences at every scale
(`cuspCarrier_collision_or_close_pair`), and they are polynomially separated
(`cuspCarrier_collide_or_repel`): there are `c, C > 0` with `‖s − s'‖ ≥ c (2 + T)^{−C}` for
distinct zeros with `2 ≤ |Im s|, |Im s'| ≤ T`.

Mechanism.
* **Zero strip** (`cuspCarrier_zero_re`). All zeros have `−2 < Re s < 3`.
* **Away from the cusp** (`exists_cusp_far_gap`). On the compact part of the Bohr band
  `K[−2, 3]` where `|1 − x| ≥ r` or `|1 − y| ≥ r`, `|H|` is bounded below on `G = 0`, because the
  cusp is the only consistent tangency (`cusp_consistent_tangency_eq`); two close zeros there
  would force a small derivative (`norm_deriv_mul_le_of_two_zeros`).
* **Near the cusp** (`cusp_local_repulsion`). The midpoint stays near the cusp (`Lipschitz`
  bound `norm_cpow_neg_sub_le`), and the local law applies.
-/

open Complex Metric Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- `|1 − 3^{−s}|³ > |1 − 2^{−s}|²` once `Re s ≤ −2`. -/
theorem cuspCarrier_ne_zero_left {s : ℂ} (hs : s.re ≤ -2) : cuspCarrier s ≠ 0 := by
  intro h0
  set u := -s.re with hu
  have hu2 : 2 ≤ u := by linarith
  have h3 : ‖(3 : ℂ) ^ (-s)‖ = (3 : ℝ) ^ u := by rw [norm_three_cpow_neg, hu]
  have h2 : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ u := by rw [norm_two_cpow_neg, hu]
  have hb : (3 : ℝ) ^ u - 1 ≤ ‖1 - (3 : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le ((3 : ℂ) ^ (-s)) 1
    rw [norm_one, h3, norm_sub_rev] at this; linarith
  have ha : ‖1 - (2 : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ u + 1 := by
    have := norm_sub_le (1 : ℂ) ((2 : ℂ) ^ (-s)); rw [norm_one, h2] at this; linarith
  -- `3^u − 2^u ≥ 5 · 2^{u−2} ≥ 5`
  have h32 : (2 : ℝ) ^ (u - 2) ≤ (3 : ℝ) ^ (u - 2) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (u - 2) := Real.one_le_rpow (by norm_num) (by linarith)
  have e3 : (3 : ℝ) ^ u = 9 * (3 : ℝ) ^ (u - 2) := by
    rw [show u = 2 + (u - 2) by ring, Real.rpow_add (by norm_num)]; norm_num
  have e2 : (2 : ℝ) ^ u = 4 * (2 : ℝ) ^ (u - 2) := by
    rw [show u = 2 + (u - 2) by ring, Real.rpow_add (by norm_num)]; norm_num
  have hgap : (2 : ℝ) ^ u + 1 + 1 ≤ (3 : ℝ) ^ u - 1 := by rw [e3, e2]; nlinarith
  have heq : ‖1 - (3 : ℂ) ^ (-s)‖ ^ 3 = ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 := by
    have : (1 - (2 : ℂ) ^ (-s)) ^ 2 = (1 - (3 : ℂ) ^ (-s)) ^ 3 := by
      unfold cuspCarrier at h0; linear_combination h0
    rw [← norm_pow, ← norm_pow, this]
  have hA0 : 0 ≤ ‖1 - (2 : ℂ) ^ (-s)‖ := norm_nonneg _
  have hpos : 1 ≤ (2 : ℝ) ^ u + 1 := by linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) u]
  have hB : (2 : ℝ) ^ u + 2 ≤ ‖1 - (3 : ℂ) ^ (-s)‖ := by linarith
  nlinarith [pow_le_pow_left₀ (by linarith) hB 3, pow_le_pow_left₀ hA0 ha 2]

/-- `|2·2^{−s}|` dominates the rest once `Re s ≥ 3`. -/
theorem cuspCarrier_ne_zero_right {s : ℂ} (hs : 3 ≤ s.re) : cuspCarrier s ≠ 0 := by
  intro h0
  set x := (2 : ℂ) ^ (-s) with hx
  set y := (3 : ℂ) ^ (-s) with hy
  have hX : ‖x‖ = (2 : ℝ) ^ (-s.re) := norm_two_cpow_neg s
  have hY : ‖y‖ = (3 : ℝ) ^ (-s.re) := norm_three_cpow_neg s
  have hX0 : 0 < ‖x‖ := by rw [hX]; positivity
  have hX8 : ‖x‖ ≤ 1 / 8 := by
    rw [hX]
    calc (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 8 := by norm_num
  -- `|y| ≤ (8/27)|x|`
  have hYX : ‖y‖ ≤ 8 / 27 * ‖x‖ := by
    have e : (3 : ℝ) ^ (-s.re) = (2 / 3 : ℝ) ^ s.re * (2 : ℝ) ^ (-s.re) := by
      rw [Real.div_rpow (by norm_num) (by norm_num), Real.rpow_neg (by norm_num),
        Real.rpow_neg (by norm_num)]
      field_simp
    have h23 : (2 / 3 : ℝ) ^ s.re ≤ (2 / 3 : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hs
    rw [hY, e, hX]
    have : (2 / 3 : ℝ) ^ (3 : ℝ) = 8 / 27 := by norm_num
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-s.re)]
  have hY0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hY1 : ‖y‖ ≤ 1 / 27 := by nlinarith
  -- `D = −2x + 3y + x² − 3y² + y³`
  have hD : -2 * x + 3 * y + x ^ 2 - 3 * y ^ 2 + y ^ 3 = 0 := by
    unfold cuspCarrier at h0; rw [← hx, ← hy] at h0; linear_combination h0
  have hrest : ‖3 * y + x ^ 2 - 3 * y ^ 2 + y ^ 3‖ ≤ 3 * ‖y‖ + ‖x‖ ^ 2 + 3 * ‖y‖ ^ 2 + ‖y‖ ^ 3 := by
    have e1 := norm_add_le (3 * y + x ^ 2 - 3 * y ^ 2) (y ^ 3)
    have e2 := norm_sub_le (3 * y + x ^ 2) (3 * y ^ 2)
    have e3 := norm_add_le (3 * y) (x ^ 2)
    rw [norm_pow] at e1 e3
    rw [norm_mul, norm_pow, show ‖(3 : ℂ)‖ = 3 by norm_num] at e2
    rw [norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num] at e3
    linarith
  have hlhs : 2 * ‖x‖ = ‖3 * y + x ^ 2 - 3 * y ^ 2 + y ^ 3‖ := by
    have : 2 * x = 3 * y + x ^ 2 - 3 * y ^ 2 + y ^ 3 := by linear_combination -hD
    rw [← this, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  nlinarith [sq_nonneg ‖y‖, mul_nonneg hY0 (sq_nonneg ‖y‖)]

/-- **Zero strip.** -/
theorem cuspCarrier_zero_re {s : ℂ} (hs : cuspCarrier s = 0) : -2 < s.re ∧ s.re < 3 := by
  constructor
  · by_contra h; push Not at h; exact cuspCarrier_ne_zero_left h hs
  · by_contra h; push Not at h; exact cuspCarrier_ne_zero_right h hs

/-! ### Repulsion away from the tangency set -/

/-- Points of `K[a, b]` have coordinates of modulus `p_i^{−σ}` for one `σ ∈ [a, b]`. -/
theorem exists_norm_eq_of_mem_bohrBand {d : ℕ} {p : Fin d → ℝ} (hp : ∀ i, 0 < p i) {a b : ℝ}
    {x : Fin d → ℂ} (hx : x ∈ bohrBand p a b) :
    ∃ σ ∈ Icc a b, ∀ i, ‖x i‖ = (p i) ^ (-σ) := by
  obtain ⟨⟨σ, u⟩, ⟨hσ, hu⟩, rfl⟩ := hx
  refine ⟨σ, hσ, fun i => ?_⟩
  have hui : ‖u i‖ = 1 := mem_sphere_zero_iff_norm.mp (hu i (mem_univ i))
  show ‖(((p i) ^ (-σ) : ℝ) : ℂ) * u i‖ = _
  rw [norm_mul, hui, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (hp i) _)]

/-- **Repulsion off the tangency set.** Let `D = G((p_i^{−s}))`, `D' = H((p_i^{−s}))` with all zeros
in `a ≤ Re s ≤ b`, and let `ρ` be continuous on the Bohr lift. If every consistent tangency has
`ρ < r`, then zeros `s` with `ρ(p^{−s}) ≥ r` are uniformly separated from all other zeros. -/
theorem repulsion_off_tangency_set {d : ℕ} (p : Fin d → ℝ) (hp : ∀ i, 0 < p i)
    {a b : ℝ} {D : ℂ → ℂ} (hD : Differentiable ℂ D) {G H : (Fin d → ℂ) → ℂ}
    (hG : Continuous G) (hH : Continuous H) (hDG : ∀ s, D s = G (bohrPoint p s))
    (hDH : ∀ s, deriv D s = H (bohrPoint p s)) (hstrip : ∀ s, D s = 0 → a ≤ s.re ∧ s.re ≤ b)
    {ρ : (Fin d → ℂ) → ℝ} (hρ : Continuous ρ) {r : ℝ}
    (hno : ∀ x ∈ bohrBand p a b, r ≤ ρ x → G x = 0 → H x ≠ 0) :
    ∃ δ > 0, ∀ s s' : ℂ, D s = 0 → D s' = 0 → s ≠ s' → r ≤ ρ (bohrPoint p s) →
      δ ≤ ‖s' - s‖ := by
  -- the gap: `|H|` has a positive minimum on the compact set `K[a, b] ∩ {ρ ≥ r} ∩ {G = 0}`
  obtain ⟨η, hη, hgap⟩ : ∃ η > 0, ∀ x ∈ bohrBand p a b, r ≤ ρ x → G x = 0 → η ≤ ‖H x‖ := by
    set Z := (bohrBand p a b ∩ {x | r ≤ ρ x}) ∩ {x | G x = 0}
    have hZc : IsCompact Z := ((isCompact_bohrBand p hp a b).inter_right
      (isClosed_le continuous_const hρ)).inter_right (isClosed_eq hG continuous_const)
    rcases Z.eq_empty_or_nonempty with h0 | hne
    · refine ⟨1, one_pos, fun x hx hr hGx => ?_⟩
      exact absurd (show x ∈ Z from ⟨⟨hx, hr⟩, hGx⟩) (by rw [h0]; exact id)
    · obtain ⟨x₀, hx₀, hmin⟩ := hZc.exists_isMinOn hne (continuous_norm.comp hH).continuousOn
      exact ⟨‖H x₀‖, norm_pos_iff.mpr (hno x₀ hx₀.1.1 hx₀.1.2 hx₀.2),
        fun x hx hr hGx => hmin ⟨⟨hx, hr⟩, hGx⟩⟩
  obtain ⟨M₀, hM₀⟩ := (isCompact_bohrBand p hp (a - 1) (b + 1)).exists_bound_of_continuousOn
    hG.continuousOn
  set M := max M₀ 1 with hM
  refine ⟨min (1 / 4) (η / (8 * M)), lt_min (by norm_num) (by positivity),
    fun s s' hs hs' hne hr => ?_⟩
  by_cases hfar : 1 / 4 < ‖s' - s‖
  · exact (min_le_left _ _).trans hfar.le
  push Not at hfar
  obtain ⟨ha, hb⟩ := hstrip s hs
  have hbound : ∀ z ∈ closedBall s 1, ‖D z‖ ≤ M := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre := (abs_re_le_norm (z - s)).trans hz
    rw [sub_re] at hre
    rw [hDG]
    exact (hM₀ _ (bohrPoint_mem_bohrBand p hp (by linarith [(abs_le.mp hre).1])
      (by linarith [(abs_le.mp hre).2]))).trans (le_max_left _ _)
  have h := norm_deriv_mul_le_of_two_zeros isOpen_univ hD.differentiableOn
    (by norm_num : (0 : ℝ) < 1) (subset_univ _) hbound (by linarith : ‖s' - s‖ ≤ 1 / 4) hs hs'
  have hder : η ≤ ‖deriv D s‖ := by
    rw [hDH]
    exact hgap _ (bohrPoint_mem_bohrBand p hp ha hb) hr (by rw [← hDG]; exact hs)
  have hpos : 0 < ‖s' - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have h2 : η * ‖s' - s‖ ≤ 8 * M * ‖s' - s‖ * ‖s' - s‖ := by
    have := (mul_le_mul_of_nonneg_right hder hpos.le).trans h
    rw [sq] at this; linarith
  have h3 : η ≤ 8 * M * ‖s' - s‖ := le_of_mul_le_mul_right h2 hpos
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### The cusp carrier on its Bohr lift -/

/-- The Bohr lift of the cusp carrier. -/
def cuspG (x : Fin 2 → ℂ) : ℂ := (1 - x 0) ^ 2 - (1 - x 1) ^ 3

/-- The Bohr lift of its derivative. -/
def cuspH (x : Fin 2 → ℂ) : ℂ :=
  2 * (1 - x 0) * (Complex.log 2 * x 0) - 3 * (1 - x 1) ^ 2 * (Complex.log 3 * x 1)

/-- The distance of a Bohr point from the cusp `(1, 1)`. -/
def cuspDist (x : Fin 2 → ℂ) : ℝ := max ‖1 - x 0‖ ‖1 - x 1‖

theorem bohrPoint_cusp_zero (s : ℂ) : bohrPoint ![2, 3] s 0 = (2 : ℂ) ^ (-s) := by
  simp [bohrPoint]

theorem bohrPoint_cusp_one (s : ℂ) : bohrPoint ![2, 3] s 1 = (3 : ℂ) ^ (-s) := by
  simp [bohrPoint]

/-- Away from the cusp, the Bohr lift of the cusp carrier has no consistent tangency. -/
theorem cusp_no_tangency_off_cusp {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ bohrBand ![2, 3] (-2) 3, r ≤ cuspDist x → cuspG x = 0 → cuspH x ≠ 0 := by
  intro x hx hρ hG hH
  obtain ⟨σ, -, hσ⟩ := exists_norm_eq_of_mem_bohrBand (fun i => by fin_cases i <;> norm_num) hx
  have e2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have e3 : Complex.log 3 = ((Real.log 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have h0 := hσ 0
  have h1 := hσ 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [cuspH, e2, e3] at hH
  obtain ⟨hx0, hx1⟩ := cusp_consistent_tangency_eq h0 h1 hG hH
  rw [cuspDist, hx0, hx1, sub_self, norm_zero, max_self] at hρ
  linarith

/-! ### Moving to the midpoint -/

/-- `|P^{−z} − P^{−w}| ≤ 2 P^{−Re w} log P · |z − w|` when `log P · |z − w| ≤ 1`. -/
theorem norm_cpow_neg_sub_le {P : ℝ} (hP : 1 < P) {z w : ℂ} (h : Real.log P * ‖z - w‖ ≤ 1) :
    ‖((P : ℝ) : ℂ) ^ (-z) - ((P : ℝ) : ℂ) ^ (-w)‖ ≤ 2 * P ^ (-w.re) * Real.log P * ‖z - w‖ := by
  have hP0 : ((P : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < P).ne'
  have hlog : Complex.log ((P : ℝ) : ℂ) = ((Real.log P : ℝ) : ℂ) :=
    (Complex.ofReal_log (by linarith)).symm
  have hw : ‖((P : ℝ) : ℂ) ^ (-w)‖ = P ^ (-w.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), neg_re]
  rw [Complex.cpow_def_of_ne_zero hP0, hlog] at hw
  rw [Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero hP0, hlog]
  have e : Complex.exp (((Real.log P : ℝ) : ℂ) * -z) - Complex.exp (((Real.log P : ℝ) : ℂ) * -w) =
      Complex.exp (((Real.log P : ℝ) : ℂ) * -w) *
        (Complex.exp (((Real.log P : ℝ) : ℂ) * (w - z)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; ring_nf
  have hn : ‖((Real.log P : ℝ) : ℂ) * (w - z)‖ = Real.log P * ‖z - w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos hP),
      norm_sub_rev]
  have h1 := Complex.norm_exp_sub_one_le (hn.le.trans h)
  rw [e, norm_mul, hw]
  rw [hn] at h1
  have hpos : 0 < P ^ (-w.re) := Real.rpow_pos_of_pos (by linarith) _
  nlinarith

/-- The midpoint of two close zeros near the cusp is near the cusp. -/
theorem midpoint_near_cusp {s s' : ℂ} {r₀ : ℝ} (hre : -2 < s.re) (hclose : ‖s' - s‖ ≤ 1 / 16)
    (hr : ‖s' - s‖ ≤ r₀ / 36) (h2 : ‖1 - (2 : ℂ) ^ (-s)‖ ≤ r₀ / 2)
    (h3 : ‖1 - (3 : ℂ) ^ (-s)‖ ≤ r₀ / 2) :
    ‖1 - (2 : ℂ) ^ (-((s + s') / 2))‖ ≤ r₀ ∧ ‖1 - (3 : ℂ) ^ (-((s + s') / 2))‖ ≤ r₀ := by
  have hm : ‖(s + s') / 2 - s‖ = ‖s' - s‖ / 2 := by
    rw [show (s + s') / 2 - s = (s' - s) / 2 by ring, norm_div,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hL2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hL3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hL2' : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hL3' : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hp2 : (2 : ℝ) ^ (-s.re) ≤ 4 := by
    calc (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hp3 : (3 : ℝ) ^ (-s.re) ≤ 9 := by
    calc (3 : ℝ) ^ (-s.re) ≤ (3 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 9 := by norm_num
  have hn0 : 0 ≤ ‖s' - s‖ := norm_nonneg _
  have l2 := norm_cpow_neg_sub_le (P := 2) (by norm_num) (z := (s + s') / 2) (w := s)
    (by rw [hm]; nlinarith)
  have l3 := norm_cpow_neg_sub_le (P := 3) (by norm_num) (z := (s + s') / 2) (w := s)
    (by rw [hm]; nlinarith)
  simp only [Complex.ofReal_ofNat] at l2 l3
  rw [hm] at l2 l3
  have p2 : 0 ≤ (2 : ℝ) ^ (-s.re) := by positivity
  have p3 : 0 ≤ (3 : ℝ) ^ (-s.re) := by positivity
  have t2 := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) ((2 : ℂ) ^ (-s)) ((2 : ℂ) ^ (-((s + s') / 2)))
  have t3 := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) ((3 : ℂ) ^ (-s)) ((3 : ℂ) ^ (-((s + s') / 2)))
  rw [norm_sub_rev ((2 : ℂ) ^ (-s))] at t2
  rw [norm_sub_rev ((3 : ℂ) ^ (-s))] at t3
  have b2 : 2 * (2 : ℝ) ^ (-s.re) * Real.log 2 * (‖s' - s‖ / 2) ≤ 4 * ‖s' - s‖ := by
    have : (2 : ℝ) ^ (-s.re) * Real.log 2 ≤ 4 := by nlinarith
    nlinarith
  have b3 : 2 * (3 : ℝ) ^ (-s.re) * Real.log 3 * (‖s' - s‖ / 2) ≤ 18 * ‖s' - s‖ := by
    have : (3 : ℝ) ^ (-s.re) * Real.log 3 ≤ 18 := by nlinarith
    nlinarith
  constructor <;> linarith

/-! ### The global law -/

/-- **The cusp carrier repels at polynomial scale.** Distinct zeros `s ≠ s'` of
`(1 − 2^{−s})² − (1 − 3^{−s})³` with `|Im s| ≥ 2` satisfy `‖s' − s‖ ≥ c (2 + |Im s|)^{−C}`. -/
theorem cuspCarrier_collide_or_repel :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ s s' : ℂ, cuspCarrier s = 0 → cuspCarrier s' = 0 → s ≠ s' →
      2 ≤ |s.im| → c * (2 + |s.im|) ^ (-C) ≤ ‖s' - s‖ := by
  obtain ⟨r₀, hr₀, κ, K, hκ, hK, hloc⟩ := cusp_local_repulsion
  have hp : ∀ i, 0 < (![2, 3] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> norm_num
  obtain ⟨δ, hδ, hgap⟩ := repulsion_off_tangency_set ![2, 3] hp (a := -2) (b := 3)
    differentiable_cuspCarrier (G := cuspG) (H := cuspH) (by unfold cuspG; fun_prop)
    (by unfold cuspH; fun_prop)
    (fun s => by rw [cuspG, bohrPoint_cusp_zero, bohrPoint_cusp_one]; rfl)
    (fun s => by
      rw [(hasDerivAt_cuspCarrier s).deriv, cuspH, bohrPoint_cusp_zero, bohrPoint_cusp_one])
    (fun s hs => ⟨(cuspCarrier_zero_re hs).1.le, (cuspCarrier_zero_re hs).2.le⟩)
    (ρ := cuspDist) (by unfold cuspDist; fun_prop) (cusp_no_tangency_off_cusp (r := r₀ / 2)
      (by positivity))
  refine ⟨min (min δ (min (1 / 16) (r₀ / 36))) (κ * 2 ^ (-K)), K, by positivity, hK,
    fun s s' hs hs' hne him => ?_⟩
  set c := min (min δ (min (1 / 16) (r₀ / 36))) (κ * 2 ^ (-K)) with hc
  have hX1 : (2 + |s.im|) ^ (-K) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg s.im]) (by linarith)
  have hX0 : 0 < (2 + |s.im|) ^ (-K) := Real.rpow_pos_of_pos (by positivity) _
  have hc0 : 0 < c := by positivity
  have hcX : c * (2 + |s.im|) ^ (-K) ≤ c := mul_le_of_le_one_right hc0.le hX1
  -- far apart
  by_cases hfar : min (1 / 16) (r₀ / 36) < ‖s' - s‖
  · exact hcX.trans ((min_le_left _ _).trans ((min_le_right _ _).trans hfar.le))
  push Not at hfar
  have h16 : ‖s' - s‖ ≤ 1 / 16 := hfar.trans (min_le_left _ _)
  have h36 : ‖s' - s‖ ≤ r₀ / 36 := hfar.trans (min_le_right _ _)
  -- away from the cusp
  by_cases hρ : r₀ / 2 ≤ cuspDist (bohrPoint ![2, 3] s)
  · exact hcX.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (hgap s s' hs hs' hne hρ)))
  push Not at hρ
  -- near the cusp: the local law at the midpoint
  rw [cuspDist, bohrPoint_cusp_zero, bohrPoint_cusp_one] at hρ
  obtain ⟨hm2, hm3⟩ := midpoint_near_cusp (cuspCarrier_zero_re hs).1 h16 h36
    ((le_max_left _ _).trans hρ.le) ((le_max_right _ _).trans hρ.le)
  have hmim : |((s + s') / 2).im - s.im| ≤ 1 / 32 := by
    rw [← sub_im]
    refine (abs_im_le_norm _).trans ?_
    rw [show (s + s') / 2 - s = (s' - s) / 2 by ring, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hm1 : 1 ≤ |((s + s') / 2).im| := by
    have := abs_sub_abs_le_abs_sub ((s + s') / 2).im s.im
    have := abs_sub_abs_le_abs_sub s.im ((s + s') / 2).im
    rw [abs_sub_comm] at hmim
    linarith [abs_sub_comm s.im ((s + s') / 2).im]
  have hloc' := hloc s s' hs hs' hne h16 hm2 hm3 hm1
  have hmX : 2 + |((s + s') / 2).im| ≤ 2 * (2 + |s.im|) := by
    have := abs_sub_abs_le_abs_sub ((s + s') / 2).im s.im
    linarith [abs_nonneg s.im]
  have hpow : (2 * (2 + |s.im|)) ^ (-K) ≤ (2 + |((s + s') / 2).im|) ^ (-K) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hmX (by linarith)
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hpow
  have hsq : ‖s' - s‖ ^ 2 ≤ ‖s' - s‖ := by
    have := norm_nonneg (s' - s); nlinarith
  calc c * (2 + |s.im|) ^ (-K) ≤ κ * 2 ^ (-K) * (2 + |s.im|) ^ (-K) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hX0.le
    _ = κ * (2 ^ (-K) * (2 + |s.im|) ^ (-K)) := by ring
    _ ≤ κ * (2 + |((s + s') / 2).im|) ^ (-K) := mul_le_mul_of_nonneg_left hpow hκ.le
    _ ≤ ‖s' - s‖ ^ 2 := hloc'
    _ ≤ ‖s' - s‖ := hsq

end GaloisForLFunctions.ArithmeticDiscreteness
