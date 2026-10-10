import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.PrimeCountingLiLandau
import GaloisForLFunctions.RHTower.ZetaMultipleLandauZeroFree

/-!
# Squarefree discrepancy bounds and the halving cascade of zeta zeros

Let `E(x) = #{n ≤ x squarefree} - (6/π²) x`. Its Mellin moment `G(s) = ∫_1^∞ E(x) x^{-s-1} dx`
satisfies `(s - 1) s G(s) ζ(2s) = (s - 1)ζ(s) - (6/π²) s ζ(2s)`. If `|E(x)| ≤ C x^α`, then `G`
is holomorphic on `Re s > α`.

* **Halving law** (`riemannZeta_half_eq_zero_of_bound`). Under `|E(x)| ≤ C x^α`, every zero `ρ`
  of `ζ` with `2α < Re ρ < 1` has `ζ(ρ/2) = 0`. At `s = ρ/2` the left side vanishes through
  `ζ(2s) = ζ(ρ)`, and the right side is `(s - 1)ζ(s)`.
* **Cascade** (`riemannZeta_ne_zero_of_squarefree_bound`). Halving and the functional equation
  send a zero `z` to the zero `1 - z/2`. The orbit `z_k = 2/3 + (-1/2)^k (ρ - 2/3)` converges to
  `2/3`, and its real parts stay between `Re ρ` and `1 - Re ρ/2`. If both exceed `2α`, every
  `z_k` is a zero, so `ζ(2/3) = 0` by continuity, which is false. Hence `|E(x)| ≤ C x^α` makes `ζ`
  zero-free on the band `2α < Re s < 2 - 4α`, and on all of `Re s > 2α` when `α ≤ ¼`.
* **Receiver** (`riemannHypothesis_of_squarefree_quarter_bound`). `E(x) = O(x^{¼+ε})` for every
  `ε > 0` implies RH.
* **Ω-result** (`not_squarefree_bound_of_lt_quarter`). Unconditionally `E(x) ≠ O(x^α)` for every
  `α < ¼`. Hardy's critical zeros lie in the excluded band.
-/

open Filter Topology MeasureTheory Set Asymptotics Complex

namespace RHTower.SquarefreeDiscrepancy

noncomputable section

/-! ## Holomorphy and the pole-cleared identity under a power bound -/

/-- A power bound for the discrepancy makes the moment holomorphic on `Re s > α`. -/
theorem differentiableAt_moment_of_bound {α C : ℝ}
    (hB : ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ α) {s : ℂ} (hs : α < s.re) :
    DifferentiableAt ℂ moment s := by
  have htop : kernel =O[atTop] (fun x : ℝ => x ^ (-(-α))) := by
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    by_cases hx1 : 1 < x
    · simp only [kernel, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from hx1), Complex.norm_real,
        Real.norm_eq_abs]
      exact (hB x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg (by linarith) _))
    · simp only [kernel, indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx1), norm_zero]
      positivity
  have hm : DifferentiableAt ℂ (mellin kernel) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_kernel htop
      (by rw [Complex.neg_re]; linarith) (kernel_isBigO_zero (-s.re - 1))
      (by rw [Complex.neg_re]; linarith)
  exact hm.comp s differentiableAt_id.neg

/-- **Pole-cleared identity on `Re s > α`.** With `Z(w) = (w - 1)ζ(w)`,
`(s - 1) s G(s) Z(2s) = (2s - 1) Z(s) - (6/π²) s Z(2s)`. -/
theorem moment_identity_of_bound {α C : ℝ} (hα : α < 2)
    (hB : ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ α) {s : ℂ} (hs : α < s.re) :
    (s - 1) * s * moment s * zetaResidueUnit (2 * s) =
      (2 * s - 1) * zetaResidueUnit s -
        (Sieve.squarefreeDensity : ℂ) * s * zetaResidueUnit (2 * s) := by
  set U : Set ℂ := {z : ℂ | α < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hz2 : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => zetaResidueUnit (2 * w)) z := fun z =>
    (analyticAt_zetaResidueUnit (2 * z)).comp (by fun_prop)
  have hl : AnalyticOnNhd ℂ
      (fun z => (z - 1) * z * moment z * zetaResidueUnit (2 * z)) U := by
    intro z hz
    have hm : AnalyticAt ℂ moment z := by
      refine DifferentiableOn.analyticAt (s := U) (fun w hw => ?_) (hUo.mem_nhds hz)
      exact (differentiableAt_moment_of_bound hB hw).differentiableWithinAt
    exact (((analyticAt_id.sub analyticAt_const).mul analyticAt_id).mul hm).mul (hz2 z)
  have hr : AnalyticOnNhd ℂ (fun z => (2 * z - 1) * zetaResidueUnit z -
      (Sieve.squarefreeDensity : ℂ) * z * zetaResidueUnit (2 * z)) U := fun z _ =>
    ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).mul (analyticAt_zetaResidueUnit z)
      |>.sub ((analyticAt_const.mul analyticAt_id).mul (hz2 z))
  have hev : (fun z => (z - 1) * z * moment z * zetaResidueUnit (2 * z)) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => (2 * z - 1) * zetaResidueUnit z -
        (Sieve.squarefreeDensity : ℂ) * z * zetaResidueUnit (2 * z)) := by
    have hgt : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz1
    have hz2ne : 2 * z ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.mul_re, Complex.one_re] at this
      norm_num at this
      linarith
    have h := moment_identity (show 1 / 2 < z.re by linarith)
    have hZ2 : zetaResidueUnit (2 * z) = (2 * z - 1) * riemannZeta (2 * z) := by
      rw [zetaResidueUnit, Function.update_of_ne hz2ne]
    rw [hZ2]
    linear_combination (2 * z - 1) * h
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr (convex_halfSpace_re_gt α).isPreconnected
    (show (2 : ℂ) ∈ U by simp [hU]; linarith) hev hs

/-! ## The halving law -/

/-- **Halving law.** Under `|E(x)| ≤ C x^α`, a zero `ρ` with `2α < Re ρ < 1` forces
`ζ(ρ/2) = 0`. -/
theorem riemannZeta_half_eq_zero_of_bound {α C : ℝ}
    (hB : ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ α) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h2α : 2 * α < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta (ρ / 2) = 0 := by
  have hs : α < (ρ / 2).re := by
    rw [Complex.div_re]; simp; nlinarith [Complex.normSq_nonneg ρ]
  have hid := moment_identity_of_bound (by linarith) hB hs
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at h1; linarith
  have hZρ : zetaResidueUnit ρ = 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
  rw [show 2 * (ρ / 2) = ρ by ring, hZρ, mul_zero, mul_zero, sub_zero] at hid
  have hne : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hZ : zetaResidueUnit (ρ / 2) = 0 := by
    rcases mul_eq_zero.mp hid.symm with h | h
    · exact absurd h hne
    · exact h
  have hhalf1 : ρ / 2 ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.div_re] at this
    simp at this
    nlinarith [Complex.normSq_nonneg ρ]
  rw [zetaResidueUnit, Function.update_of_ne hhalf1] at hZ
  rcases mul_eq_zero.mp hZ with h | h
  · exact absurd (sub_eq_zero.mp h) hhalf1
  · exact h

/-! ## The cascade -/

/-- The orbit `z_k = 2/3 + (-1/2)^k (ρ - 2/3)` of `z ↦ 1 - z/2`. -/
def cascadeOrbit (ρ : ℂ) (k : ℕ) : ℂ := 2 / 3 + ((-1 / 2 : ℂ)) ^ k * (ρ - 2 / 3)

theorem cascadeOrbit_succ (ρ : ℂ) (k : ℕ) :
    cascadeOrbit ρ (k + 1) = 1 - cascadeOrbit ρ k / 2 := by
  unfold cascadeOrbit; ring

theorem cascadeOrbit_re (ρ : ℂ) (k : ℕ) :
    (cascadeOrbit ρ k).re = 2 / 3 + (-1 / 2 : ℝ) ^ k * (ρ.re - 2 / 3) := by
  unfold cascadeOrbit
  have : ((-1 / 2 : ℂ)) ^ k = (((-1 / 2 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.add_re, Complex.re_ofReal_mul]
  simp

/-- The real parts of the orbit lie between `Re ρ` and `1 - Re ρ/2`. -/
theorem cascadeOrbit_re_bounds (ρ : ℂ) (k : ℕ) :
    min ρ.re (1 - ρ.re / 2) ≤ (cascadeOrbit ρ k).re ∧
      (cascadeOrbit ρ k).re ≤ max ρ.re (1 - ρ.re / 2) := by
  rw [cascadeOrbit_re]
  set t : ℝ := (-1 / 2 : ℝ) ^ k with ht
  have hbounds : -(1 / 2) ≤ t ∧ t ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [ht, hk, pow_zero]; norm_num
    · have habs : |t| ≤ 1 / 2 := by
        rw [ht, abs_pow, show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num]
        calc (1 / 2 : ℝ) ^ k ≤ (1 / 2) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
          _ = 1 / 2 := pow_one _
      constructor <;> linarith [abs_le.mp habs]
  obtain ⟨hlo, hhi⟩ := hbounds
  have e1 : 2 / 3 + 1 * (ρ.re - 2 / 3) = ρ.re := by ring
  have e2 : 2 / 3 + (-(1 / 2)) * (ρ.re - 2 / 3) = 1 - ρ.re / 2 := by ring
  rcases le_total (ρ.re - 2 / 3) 0 with hd | hd
  · constructor
    · refine le_trans (min_le_left _ _) ?_
      nlinarith
    · refine le_trans ?_ (le_max_right _ _)
      nlinarith
  · constructor
    · refine le_trans (min_le_right _ _) ?_
      nlinarith
    · refine le_trans ?_ (le_max_left _ _)
      nlinarith

theorem tendsto_cascadeOrbit (ρ : ℂ) :
    Tendsto (cascadeOrbit ρ) atTop (𝓝 (2 / 3)) := by
  have hpow : Tendsto (fun k : ℕ => ((-1 / 2 : ℂ)) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have h := (hpow.mul_const (ρ - 2 / 3)).const_add (2 / 3 : ℂ)
  rw [zero_mul, add_zero] at h
  exact h

/-- `ζ(2/3) ≠ 0`. -/
theorem riemannZeta_two_thirds_ne_zero : riemannZeta (2 / 3) ≠ 0 := by
  obtain ⟨r, hr, hZ⟩ := exists_zetaResidueUnit_ofReal_eq_pos (show (0 : ℝ) < 2 / 3 by norm_num)
  intro h
  have h1 : ((2 / 3 : ℝ) : ℂ) ≠ 1 := by norm_num
  rw [zetaResidueUnit, Function.update_of_ne h1] at hZ
  push_cast at hZ
  rw [h, mul_zero] at hZ
  exact (by exact_mod_cast hr.ne' : (r : ℂ) ≠ 0) hZ.symm

/-- **Halving cascade.** If every zero `ρ` with `2α < Re ρ < 1` has `ζ(ρ/2) = 0`, then `ζ` has no
zero `s` with `2α < Re s` and `2α < 1 - Re s/2`: the orbit of `z ↦ 1 - z/2` would consist of zeros
converging to `2/3`. -/
theorem riemannZeta_ne_zero_of_halving {α : ℝ} (hα : 0 ≤ α)
    (hhalf : ∀ ρ : ℂ, riemannZeta ρ = 0 → 2 * α < ρ.re → ρ.re < 1 → riemannZeta (ρ / 2) = 0)
    {s : ℂ} (h1 : 2 * α < s.re) (h2 : 2 * α < 1 - s.re / 2) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hs0 : 0 < s.re := by linarith
  have hmin : 2 * α < min s.re (1 - s.re / 2) := lt_min h1 h2
  have hmax : max s.re (1 - s.re / 2) < 1 := max_lt hs1 (by linarith)
  have hzeros : ∀ k : ℕ, riemannZeta (cascadeOrbit s k) = 0 := by
    intro k
    induction k with
    | zero => simpa [cascadeOrbit] using hz
    | succ k ih =>
      obtain ⟨hlo, hhi⟩ := cascadeOrbit_re_bounds s k
      have hre1 : 2 * α < (cascadeOrbit s k).re := lt_of_lt_of_le hmin hlo
      have hre2 : (cascadeOrbit s k).re < 1 := lt_of_le_of_lt hhi hmax
      have hhalf := hhalf _ ih hre1 hre2
      have hre0 : 0 < (cascadeOrbit s k / 2).re := by
        rw [Complex.div_re]; simp; nlinarith [Complex.normSq_nonneg (cascadeOrbit s k)]
      have hre1' : (cascadeOrbit s k / 2).re < 1 := by
        rw [Complex.div_re]; simp; nlinarith [Complex.normSq_nonneg (cascadeOrbit s k)]
      rw [cascadeOrbit_succ]
      exact (riemannZeta_one_sub_eq_zero_iff hre0 hre1').mpr hhalf
  have hcont : ContinuousAt riemannZeta (2 / 3 : ℂ) :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have hlim := hcont.tendsto.comp (tendsto_cascadeOrbit s)
  have h0 : Tendsto (fun k => riemannZeta (cascadeOrbit s k)) atTop (𝓝 0) := by
    simp only [hzeros]; exact tendsto_const_nhds
  exact riemannZeta_two_thirds_ne_zero (tendsto_nhds_unique hlim h0)

/-- **Zero-free band from a squarefree power bound.** If `|E(x)| ≤ C x^α` on `x ≥ 1`, then
`ζ(s) ≠ 0` whenever `2α < Re s` and `2α < 1 - Re s/2`. -/
theorem riemannZeta_ne_zero_of_squarefree_bound {α C : ℝ} (hα : 0 ≤ α)
    (hB : ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ α) {s : ℂ} (h1 : 2 * α < s.re)
    (h2 : 2 * α < 1 - s.re / 2) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_halving hα
    (fun _ hz hre1 hre2 => riemannZeta_half_eq_zero_of_bound hB hz hre1 hre2) h1 h2

/-- For `α ≤ ¼` the band is the whole half-plane `Re s > 2α`. -/
theorem riemannZeta_ne_zero_of_squarefree_bound_of_le_quarter {α C : ℝ} (hα : 0 ≤ α)
    (hα4 : α ≤ 1 / 4) (hB : ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ α) {s : ℂ}
    (h1 : 2 * α < s.re) :
    riemannZeta s ≠ 0 := by
  rcases lt_or_ge s.re 1 with hs | hs
  · exact riemannZeta_ne_zero_of_squarefree_bound hα hB h1 (by linarith)
  · exact riemannZeta_ne_zero_of_one_le_re hs

/-- **Squarefree receiver.** If `E(x) = O(x^{¼+ε})` for every `ε > 0`, then RH holds. -/
theorem riemannHypothesis_of_squarefree_quarter_bound
    (hB : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ (1 / 4 + ε)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs hz
  have hs1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  set ε : ℝ := min ((s.re - 1 / 2) / 4) ((1 - s.re) / 8) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := hB ε hε0
  have hε1 : ε ≤ (s.re - 1 / 2) / 4 := min_le_left _ _
  have hε2 : ε ≤ (1 - s.re) / 8 := min_le_right _ _
  exact riemannZeta_ne_zero_of_squarefree_bound (by linarith) hC (by linarith) (by linarith) hz

/-- **Ω-result.** Unconditionally, `E(x) = O(x^α)` fails for every `α < ¼`. -/
theorem not_squarefree_bound_of_lt_quarter {α : ℝ} (hα : α < 1 / 4) :
    ¬ ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ α := by
  rintro ⟨C, hC⟩
  obtain ⟨s, hs, hz⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
  have hC' : ∀ x : ℝ, 1 ≤ x → |error x| ≤ |C| * x ^ (max α 0) := by
    intro x hx
    calc |error x| ≤ C * x ^ α := hC x hx
      _ ≤ |C| * x ^ α := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * x ^ (max α 0) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)) (abs_nonneg C)
  have hmax : max α 0 < 1 / 4 := max_lt hα (by norm_num)
  exact riemannZeta_ne_zero_of_squarefree_bound (le_max_right _ _) hC' (by rw [hs]; linarith)
    (by rw [hs]; linarith) hz

end

end RHTower.SquarefreeDiscrepancy
