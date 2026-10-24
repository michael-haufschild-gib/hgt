import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw
import GaloisForLFunctions.RHTower.KiKimLeeWeylHorizon
import GaloisForLFunctions.RHTower.XiSliceHeatFiniteHeadReduction
import GaloisForLFunctions.RHTower.XiSliceHeatThresholdTouching
import GaloisForLFunctions.RHTower.XiSliceHeatThresholdVerificationHeight
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime
import GaloisForLFunctions.HTGeometry.PolynomialMinimumModulus

/-!
# Collision Mass Conservation, Small-Time Weyl–Jensen Bounds, and Critical-Heat Positivity

This module completes the global collision-mass and critical-heat theory for the de Bruijn–Newman
deformation `H_t` (`riemannHeat t`) and the horizontal slice heat transfer `xiSliceHeatTransfer`:

1. **Quantization and Simplicity Characterization (`even_collisionMass`, `even_nonrealZeroCount`,
   `collisionMass_eq_zero_iff_simple`, `sum_collisionMass_Ioc_eq_sub`):**
   Every collision mass `collisionMass t` and nonreal zero count `nonrealZeroCount t` is an even
   integer, so any nonzero collision or nonreal count is at least `2`. At any positive time `t > 0`,
   `collisionMass t = 0` iff all real zeros of `H_t` are simple, and `nonrealZeroCount t = 0` iff
   `collisionMass s = 0` for all `s > t`. On every interval `(t, u]` (`0 < t ≤ u`), the drop
   `nonrealZeroCount t − nonrealZeroCount u` equals the exact sum of `collisionMass s` over
   `s ∈ (t, u]`.
2. **Last-Collision Theorem, De Bruijn–Newman Constant, and Zero-Width Bounds
   (`isGreatest_collisionTimes_newmanConstant`, `newmanConstant_eq_sSup_collisionTimes`,
   `wdHeatThreshold_le_third_sq_zetaZeroWidth`):**
   Whenever `newmanConstant > 0`, `collisionMass newmanConstant ≥ 2` and `newmanConstant` is the
   greatest positive collision time; in all cases `newmanConstant = sSup {s > 0 | collisionMass s ≠ 0}`.
   Moreover, `collisionMass s = 0` for all `s > zetaZeroWidth² / 2`, while the WD heat threshold
   satisfies the sharper zero-width bound `wdHeatThreshold ≤ zetaZeroWidth² / 3`.
3. **Small-Time (`t → 0⁺`) Conservation and Unconditional Weyl–Jensen Bounds
   (`sum_all_collisionMass_eq_card_nonrealCopies`, `exists_nonrealZeroCount_and_collisionMass_le_weyl`):**
   When `Ξ` has finitely many nonreal zeros, `{s > 0 | collisionMass s ≠ 0}` is finite and the sum
   of `collisionMass s` over all `s > 0` equals the exact number of off-line zeros of `Ξ` counted
   with multiplicity. Unconditionally, combining the Weyl heat horizon
   (`riemannHeat_zeros_real_simple_weyl`) with a uniform disk zero-count bound
   (`exists_sum_zeroMult_riemannHeat_ball_le`) controls both
   `nonrealZeroCount t = ∑_{s > t} collisionMass s` and `collisionMass t` as `t → 0⁺` by
   `C_ε · R_ε(t) log(2 + 3 R_ε(t))` with `R_ε(t) = max(X₀, 2π e^{(3/2 + ε)/t}) + 1`.
4. **Critical-Heat and Retained Finite-Head Positivity Bridges
   (`wdHeatThreshold_le_of_finiteHead_poly_nonneg`,
   `forall_collisionMass_eq_zero_iff_forall_pos_finiteHead_poly_nonneg`):**
   Excluding positive-time collision mass (`∀ t > 0, collisionMass t = 0`) is equivalent to
   all-height retained finite-head heat polynomial coefficient positivity for every `λ > 0`.
-/

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SquareRootThreshold

namespace RHTower.DeBruijn

noncomputable section

/-! ## 1. Parity, quantization, and interval conservation of collision mass -/

/-- Every collision mass `collisionMass t` is an even natural number, since each summand
`m − m % 2` is even. -/
theorem even_collisionMass (t : ℝ) : Even (collisionMass t) := by
  unfold collisionMass
  refine Finset.even_sum _ fun z _ => ?_
  set m := zeroMult (riemannHeat t) z
  exact ⟨m / 2, by omega⟩

/-- Whenever `collisionMass t ≠ 0`, at least one conjugate pair collides (`2 ≤ collisionMass t`). -/
theorem two_le_collisionMass_of_ne_zero {t : ℝ} (h : collisionMass t ≠ 0) :
    2 ≤ collisionMass t := by
  obtain ⟨k, hk⟩ := even_collisionMass t
  omega

/-- Each summand of `collisionMass t` is at most the zero multiplicity at that point, so
`collisionMass t` is bounded by the total multiplicity of the real multiple zeros of `H_t`. -/
theorem collisionMass_le_sum_zeroMult (t : ℝ) :
    collisionMass t ≤ ∑ z ∈ realMultipleZeros t, zeroMult (riemannHeat t) z := by
  unfold collisionMass
  exact Finset.sum_le_sum fun z _ => Nat.sub_le _ _

/-- Any point `z ∈ realMultipleZeros t` contributes at least `2` to `collisionMass t`. -/
theorem two_le_collisionMass_of_mem {t : ℝ} {z : ℂ} (hz : z ∈ realMultipleZeros t) :
    2 ≤ collisionMass t := by
  have ht : 0 < t ∧ t ≤ 1 / 8 := by
    by_contra h
    rw [realMultipleZeros, dif_neg h] at hz
    exact Finset.notMem_empty _ hz
  obtain ⟨hz0, -, hdz⟩ := (mem_realMultipleZeros ht.1 ht.2).mp hz
  have hm := two_le_zeroMult_riemannHeat ht.1.le hz0 hdz
  have hle := Finset.single_le_sum
    (f := fun w => zeroMult (riemannHeat t) w - zeroMult (riemannHeat t) w % 2)
    (fun _ _ => Nat.zero_le _) hz
  unfold collisionMass
  omega

/-- At any time `t`, `collisionMass t ≠ 0` iff `realMultipleZeros t` is nonempty. -/
theorem collisionMass_ne_zero_iff_nonempty (t : ℝ) :
    collisionMass t ≠ 0 ↔ (realMultipleZeros t).Nonempty := by
  constructor
  · intro h
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    unfold collisionMass at h
    rw [hemp, Finset.sum_empty] at h
    exact h rfl
  · rintro ⟨z, hz⟩
    have := two_le_collisionMass_of_mem hz
    omega

/-- At any time `t`, `collisionMass t = 0` iff `realMultipleZeros t = ∅`. -/
theorem collisionMass_eq_zero_iff_empty (t : ℝ) :
    collisionMass t = 0 ↔ realMultipleZeros t = ∅ := by
  have h := (collisionMass_ne_zero_iff_nonempty t).trans Finset.nonempty_iff_ne_empty
  exact not_iff_not.mp h

/-- For `t > 0`, `collisionMass t = 0` iff every real zero of `H_t` is simple. -/
theorem collisionMass_eq_zero_iff_simple {t : ℝ} (ht : 0 < t) :
    collisionMass t = 0 ↔ ∀ x : ℝ, riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0 := by
  rw [collisionMass_eq_zero_iff_empty]
  rcases le_or_gt t (1 / 8) with ht8 | ht8
  · constructor
    · intro hemp x hx hdx
      have hmem : (x : ℂ) ∈ realMultipleZeros t :=
        (mem_realMultipleZeros ht ht8).mpr ⟨hx, Complex.ofReal_im x, hdx⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty _ hmem
    · intro hsimple
      refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨hz0, hzim, hdz⟩ := (mem_realMultipleZeros ht ht8).mp hz
      have hzre : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hzim])
      rw [← hzre] at hz0 hdz
      exact hsimple z.re hz0 hdz
  · simp only [realMultipleZeros, dif_neg (not_and.mpr fun _ => not_le.mpr ht8), true_iff]
    intro x hx
    exact (riemannHeat_zeros_real_simple_of_eighth_le ht8.le hx).2

/-- For every `t : ℝ`, `nonrealZeroCount t` is an even natural number. -/
theorem even_nonrealZeroCount (t : ℝ) : Even (nonrealZeroCount t) := by
  by_cases ht : 0 < t
  · rw [nonrealZeroCount_eq_sum_collisionMass ht]
    exact Finset.even_sum _ fun s _ => even_collisionMass s
  · simp [nonrealZeroCount, ht]

/-- Whenever `nonrealZeroCount t ≠ 0`, `2 ≤ nonrealZeroCount t`. -/
theorem two_le_nonrealZeroCount_of_ne_zero {t : ℝ} (h : nonrealZeroCount t ≠ 0) :
    2 ≤ nonrealZeroCount t := by
  obtain ⟨k, hk⟩ := even_nonrealZeroCount t
  omega

/-- Every collision mass after time `t > 0` is bounded by `nonrealZeroCount t`. -/
theorem collisionMass_le_nonrealZeroCount {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    collisionMass s ≤ nonrealZeroCount t := by
  by_cases hs : collisionMass s = 0
  · rw [hs]; exact Nat.zero_le _
  · rw [nonrealZeroCount_eq_sum_collisionMass ht]
    refine Finset.single_le_sum (fun _ _ => Nat.zero_le _) ?_
    exact (finite_collisionTimes ht).mem_toFinset.mpr ⟨hts, hs⟩

/-- For `t > 0`, `nonrealZeroCount t = 0` iff no collision occurs after time `t`. -/
theorem nonrealZeroCount_eq_zero_iff_forall_collisionMass_eq_zero {t : ℝ} (ht : 0 < t) :
    nonrealZeroCount t = 0 ↔ ∀ s > t, collisionMass s = 0 := by
  constructor
  · intro h0 s hts
    have hle := collisionMass_le_nonrealZeroCount ht hts
    omega
  · intro hall
    rw [nonrealZeroCount_eq_sum_collisionMass ht]
    refine Finset.sum_eq_zero fun s hs => ?_
    exact hall s ((finite_collisionTimes ht).mem_toFinset.mp hs).1

/-- **Interval collision conservation.** For `0 < t ≤ u`, the total collision mass in `(t, u]`
equals the exact drop `nonrealZeroCount t − nonrealZeroCount u`. -/
theorem sum_collisionMass_Ioc_eq_sub {t u : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    ∑ s ∈ (finite_collisionTimes ht).toFinset.filter (fun s => s ≤ u), collisionMass s =
      nonrealZeroCount t - nonrealZeroCount u := by
  classical
  have hu : 0 < u := lt_of_lt_of_le ht htu
  set Ft := (finite_collisionTimes ht).toFinset
  set Fu := (finite_collisionTimes hu).toFinset
  have hFu_eq : Fu = Ft.filter (fun s => ¬ s ≤ u) := by
    ext s
    simp only [Fu, Ft, Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq, not_le]
    exact ⟨fun ⟨hsu, hc⟩ => ⟨⟨lt_of_le_of_lt htu hsu, hc⟩, hsu⟩, fun ⟨⟨_, hc⟩, hsu⟩ => ⟨hsu, hc⟩⟩
  have hsplit := (Finset.sum_filter_add_sum_filter_not Ft (fun s => s ≤ u) collisionMass).symm
  rw [← nonrealZeroCount_eq_sum_collisionMass ht, ← hFu_eq,
    ← nonrealZeroCount_eq_sum_collisionMass hu] at hsplit
  omega

/-! ## 2. The De Bruijn–Newman constant, last collision, and zero-width bounds -/

/-- A positive time `t > 0` lies in `realRootedTimes` iff `nonrealZeroCount t = 0`. -/
theorem mem_realRootedTimes_iff_nonrealZeroCount_eq_zero {t : ℝ} (ht : 0 < t) :
    t ∈ realRootedTimes ↔ nonrealZeroCount t = 0 := by
  rw [nonrealZeroCount_eq ht, Finset.sum_eq_zero_iff]
  constructor
  · intro h z hz
    exfalso
    obtain ⟨hz0, hzim⟩ := (riemannHeat_nonreal_zeros_finite ht).mem_toFinset.mp hz
    exact hzim (h.2 z hz0)
  · intro h
    refine ⟨ht.le, fun z hz => ?_⟩
    by_contra hzim
    have hmem : z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset :=
      (riemannHeat_nonreal_zeros_finite ht).mem_toFinset.mpr ⟨hz, hzim⟩
    have h1 := one_le_zeroMult_riemannHeat ht.le hz
    have h0 := h z hmem
    omega

/-- A positive time `t > 0` lies in `realRootedTimes` iff `collisionMass s = 0` for all `s > t`. -/
theorem mem_realRootedTimes_iff_forall_collisionMass_eq_zero {t : ℝ} (ht : 0 < t) :
    t ∈ realRootedTimes ↔ ∀ s > t, collisionMass s = 0 :=
  (mem_realRootedTimes_iff_nonrealZeroCount_eq_zero ht).trans
    (nonrealZeroCount_eq_zero_iff_forall_collisionMass_eq_zero ht)

/-- For `t > 0`, `newmanConstant ≤ t` iff `nonrealZeroCount t = 0`. -/
theorem newmanConstant_le_iff_nonrealZeroCount_eq_zero {t : ℝ} (ht : 0 < t) :
    newmanConstant ≤ t ↔ nonrealZeroCount t = 0 := by
  rw [← mem_realRootedTimes_iff_nonrealZeroCount_eq_zero ht, mem_realRootedTimes_iff ht.le]

/-- For `t > 0`, `newmanConstant ≤ t` iff `collisionMass s = 0` for all `s > t`. -/
theorem newmanConstant_le_iff_forall_collisionMass_eq_zero {t : ℝ} (ht : 0 < t) :
    newmanConstant ≤ t ↔ ∀ s > t, collisionMass s = 0 :=
  (newmanConstant_le_iff_nonrealZeroCount_eq_zero ht).trans
    (nonrealZeroCount_eq_zero_iff_forall_collisionMass_eq_zero ht)

/-- Above the de Bruijn–Newman constant, every collision mass vanishes. -/
theorem collisionMass_eq_zero_of_newmanConstant_lt {s : ℝ} (hs : newmanConstant < s) :
    collisionMass s = 0 := by
  have hs0 : 0 < s := lt_of_le_of_lt newmanConstant_nonneg hs
  have ht0 : 0 < (newmanConstant + s) / 2 := by linarith [newmanConstant_nonneg]
  have hΛt : newmanConstant ≤ (newmanConstant + s) / 2 := by linarith
  have hts : (newmanConstant + s) / 2 < s := by linarith
  exact (newmanConstant_le_iff_forall_collisionMass_eq_zero ht0).mp hΛt s hts

/-- **Last-collision theorem in collision-mass form.** If `0 < newmanConstant`, then
`collisionMass newmanConstant ≠ 0`. -/
theorem collisionMass_newmanConstant_ne_zero (hΛ : 0 < newmanConstant) :
    collisionMass newmanConstant ≠ 0 := by
  obtain ⟨z, hz0, hdz⟩ := exists_multiple_zero_of_newmanConstant_pos hΛ
  have hmem := (mem_realRootedTimes_iff newmanConstant_nonneg).mpr le_rfl
  have hzim : z.im = 0 := hmem.2 z hz0
  have hzre : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hzim])
  rw [← hzre] at hz0 hdz
  intro hc0
  exact (collisionMass_eq_zero_iff_simple hΛ).mp hc0 z.re hz0 hdz

/-- If `0 < newmanConstant`, the last collision has mass at least `2`. -/
theorem two_le_collisionMass_newmanConstant (hΛ : 0 < newmanConstant) :
    2 ≤ collisionMass newmanConstant :=
  two_le_collisionMass_of_ne_zero (collisionMass_newmanConstant_ne_zero hΛ)

/-- If `0 < newmanConstant`, then `newmanConstant` is the greatest positive collision time. -/
theorem isGreatest_collisionTimes_newmanConstant (hΛ : 0 < newmanConstant) :
    IsGreatest {s : ℝ | 0 < s ∧ collisionMass s ≠ 0} newmanConstant := by
  refine ⟨⟨hΛ, collisionMass_newmanConstant_ne_zero hΛ⟩, fun s hs => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hs.2 (collisionMass_eq_zero_of_newmanConstant_lt hlt)

/-- **The de Bruijn–Newman constant is the supremum of the positive collision times.** -/
theorem newmanConstant_eq_sSup_collisionTimes :
    newmanConstant = sSup {s : ℝ | 0 < s ∧ collisionMass s ≠ 0} := by
  rcases eq_or_lt_of_le newmanConstant_nonneg with h0 | hpos
  · have hemp : {s : ℝ | 0 < s ∧ collisionMass s ≠ 0} = ∅ := by
      ext s
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hs
      exact collisionMass_eq_zero_of_newmanConstant_lt (by linarith)
    rw [← h0, hemp, Real.sSup_empty]
  · exact (isGreatest_collisionTimes_newmanConstant hpos).isLUB.csSup_eq
      ⟨newmanConstant, hpos, collisionMass_newmanConstant_ne_zero hpos⟩ |>.symm

/-- For every `t > 0` with `zetaZeroWidth ^ 2 / 2 ≤ t`, `nonrealZeroCount t = 0`. -/
theorem nonrealZeroCount_eq_zero_of_half_sq_zetaZeroWidth_le {t : ℝ} (ht : 0 < t)
    (hw : zetaZeroWidth ^ 2 / 2 ≤ t) : nonrealZeroCount t = 0 :=
  (newmanConstant_le_iff_nonrealZeroCount_eq_zero ht).mp
    (le_trans (csInf_le realRootedTimes_bddBelow
      ⟨by positivity, fun _ hz => riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le le_rfl hz⟩) hw)

/-- For every `s > zetaZeroWidth ^ 2 / 2`, `collisionMass s = 0`. -/
theorem collisionMass_eq_zero_of_half_sq_zetaZeroWidth_lt {s : ℝ}
    (hs : zetaZeroWidth ^ 2 / 2 < s) : collisionMass s = 0 := by
  have hΛ : newmanConstant ≤ zetaZeroWidth ^ 2 / 2 :=
    csInf_le realRootedTimes_bddBelow
      ⟨by positivity, fun _ hz => riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le le_rfl hz⟩
  exact collisionMass_eq_zero_of_newmanConstant_lt (lt_of_le_of_lt hΛ hs)

/-- **Zero-width slice heat positivity.** Since every nontrivial zero of `ζ` (and hence every zero
of `ξ`) lies within `zetaZeroWidth` of the critical line, every heated horizontal slice coefficient
is nonnegative whenever `zetaZeroWidth ^ 2 ≤ r ^ 2 + 3 * lam`. -/
theorem xiSliceHeatTransfer_nonneg_of_zetaZeroWidth {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    (hw : zetaZeroWidth ^ 2 ≤ r ^ 2 + 3 * lam) (t : ℝ) (n : ℕ) :
    (0 : ℂ) ≤ xiSliceHeatTransfer lam r t n := by
  refine xiSliceHeatTransfer_nonneg_of_heatedHyperbola_all hlam hr (fun q => ?_) n
  have hz := xi_eq_zero_of_mem_divisor_support q.1
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hz
  have hmem : (q.1 : ℂ) ∈ Zeta23.zetaZeroConfig.carrier :=
    show Zeta23.IsNontrivialZero (q.1 : ℂ) from
      ⟨(xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hz).1, h0, h1⟩
  have hle := abs_re_sub_half_le_zetaZeroWidth hmem
  have him : |(xiSpectralPoint q).im| = |(q.1 : ℂ).re - 1 / 2| := by
    have : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
      simp [xiSpectralPoint]
    rw [this, abs_neg]
  have hsq : (xiSpectralPoint q).im ^ 2 ≤ zetaZeroWidth ^ 2 := by
    rw [← sq_abs ((xiSpectralPoint q).im), him]
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  nlinarith [sq_nonneg ((xiSpectralPoint q).re - t)]

/-- **The WD heat threshold is at most one-third the square of the zero width**
(`wdHeatThreshold ≤ zetaZeroWidth ^ 2 / 3`), sharpening the `1/2` factor of
`newmanConstant ≤ zetaZeroWidth ^ 2 / 2` to `1/3` for the slice threshold. -/
theorem wdHeatThreshold_le_third_sq_zetaZeroWidth :
    wdHeatThreshold ≤ zetaZeroWidth ^ 2 / 3 := by
  refine csInf_le wdHeatAdmissible_bddBelow (fun t n => ?_)
  exact xiSliceHeatTransfer_nonneg_of_zetaZeroWidth (by positivity) le_rfl (by linarith) t n

/-- **Vanishing of the zero width is equivalent to vanishing of the WD heat threshold.** -/
theorem zetaZeroWidth_eq_zero_iff_wdHeatThreshold_eq_zero :
    zetaZeroWidth = 0 ↔ wdHeatThreshold = 0 := by
  rw [← riemannHypothesis_iff_zetaZeroWidth_eq_zero, riemannHypothesis_iff_wdHeatThreshold_eq_zero]

/-! ## 3. Small-time (`t → 0⁺`) collision conservation and finite-exception equivalence -/

/-- **RH as emptiness of the positive collision set.** -/
theorem riemannHypothesis_iff_collisionTimes_empty :
    RiemannHypothesis ↔ {s : ℝ | 0 < s ∧ collisionMass s ≠ 0} = ∅ := by
  rw [riemannHypothesis_iff_forall_collisionMass_eq_zero]
  constructor
  · intro h
    ext s
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    exact h s
  · intro hemp s hs
    by_contra hne
    have : s ∈ ({s : ℝ | 0 < s ∧ collisionMass s ≠ 0} : Set ℝ) := ⟨hs, hne⟩
    rw [hemp] at this
    exact this

/-- If `Ξ` has finitely many nonreal zero copies, there is a positive heat time `t₁ > 0` below
which no collision occurs (`collisionMass s = 0` for all `0 < s ≤ t₁`), and at which
`nonrealZeroCount t₁` equals the total number of nonreal zero copies of `Ξ`. -/
theorem exists_pos_collision_free_below_of_finite_nonrealCopies
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    ∃ t₁ > 0, nonrealZeroCount t₁ = hfin.toFinset.card ∧
      ∀ s, 0 < s → s ≤ t₁ → collisionMass s = 0 := by
  obtain ⟨t₁, ht₁eq, ht₁⟩ :=
    ((eventually_nonrealZeroCount_eq_of_finite hfin).and self_mem_nhdsWithin).exists
  have ht₁pos : 0 < t₁ := ht₁
  refine ⟨t₁, ht₁pos, ht₁eq, fun s hs0 hst₁ => ?_⟩
  have hs2 : 0 < s / 2 := by positivity
  have hle1 : nonrealZeroCount (s / 2) ≤ hfin.toFinset.card :=
    nonrealZeroCount_le_of_finite_nonreal_zeros hfin hs2
  have hle2 : nonrealZeroCount t₁ ≤ nonrealZeroCount (s / 2) :=
    nonrealZeroCount_antitoneOn hs2 ht₁pos (by linarith)
  have heq : nonrealZeroCount (s / 2) = nonrealZeroCount t₁ := by omega
  have hsum := sum_collisionMass_Ioc_eq_sub hs2 (by linarith : s / 2 ≤ t₁)
  rw [heq, Nat.sub_self] at hsum
  by_contra hne
  have hmem : s ∈ (finite_collisionTimes hs2).toFinset.filter (fun u => u ≤ t₁) := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨by linarith, hne⟩, hst₁⟩
  have hpos := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  omega

/-- If `Ξ` has finitely many nonreal zero copies, then the set of all positive collision times
`{s > 0 | collisionMass s ≠ 0}` is finite. -/
theorem finite_all_collisionTimes_of_finite_nonrealCopies
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    {s : ℝ | 0 < s ∧ collisionMass s ≠ 0}.Finite := by
  obtain ⟨t₁, ht₁, -, hno⟩ := exists_pos_collision_free_below_of_finite_nonrealCopies hfin
  refine (finite_collisionTimes ht₁).subset fun s ⟨hs0, hsc⟩ => ⟨?_, hsc⟩
  by_contra hle
  exact hsc (hno s hs0 (not_lt.mp hle))

/-- **Global conservation of off-line zero multiplicity as collision mass.** When `Ξ` has finitely
many nonreal zero copies, the sum of `collisionMass s` over all positive collision times `s > 0`
equals the exact number of nonreal zero copies of `Ξ` (counted with multiplicity). -/
theorem sum_all_collisionMass_eq_card_nonrealCopies
    (hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    ∑ s ∈ (finite_all_collisionTimes_of_finite_nonrealCopies hfin).toFinset, collisionMass s =
      hfin.toFinset.card := by
  obtain ⟨t₁, ht₁, ht₁eq, hno⟩ := exists_pos_collision_free_below_of_finite_nonrealCopies hfin
  have hset : (finite_all_collisionTimes_of_finite_nonrealCopies hfin).toFinset =
      (finite_collisionTimes ht₁).toFinset := by
    ext s
    simp only [Set.Finite.mem_toFinset, mem_setOf_eq]
    refine ⟨fun ⟨hs0, hsc⟩ => ⟨?_, hsc⟩, fun ⟨hts, hsc⟩ => ⟨lt_trans ht₁ hts, hsc⟩⟩
    by_contra hle
    exact hsc (hno s hs0 (not_lt.mp hle))
  rw [hset, ← nonrealZeroCount_eq_sum_collisionMass ht₁, ht₁eq]

/-- **Finiteness of nonreal zeros of `Ξ` is equivalent to finiteness of positive collision times.** -/
theorem finite_nonreal_zeros_iff_finite_all_collisionTimes :
    {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Finite ↔
      {s : ℝ | 0 < s ∧ collisionMass s ≠ 0}.Finite := by
  constructor
  · intro hZ
    exact finite_all_collisionTimes_of_finite_nonrealCopies (finite_nonrealCopies_of_finite_zeros hZ)
  · intro hfin
    rw [finite_nonreal_zeros_iff_exists_nonrealZeroCount_le]
    refine ⟨∑ s ∈ hfin.toFinset, collisionMass s, fun t ht => ?_⟩
    rw [nonrealZeroCount_eq_sum_collisionMass ht]
    refine Finset.sum_le_sum_of_subset fun s hs => ?_
    rw [Set.Finite.mem_toFinset] at hs ⊢
    exact ⟨lt_trans ht hs.1, hs.2⟩

/-- When `Ξ` has infinitely many nonreal zeros, the total collision mass after time `t` diverges to
`+∞` as `t → 0⁺`. -/
theorem tendsto_collisionMassAfter_atTop_of_infinite
    (hinf : {z : ℂ | riemannHeat 0 z = 0 ∧ z.im ≠ 0}.Infinite) :
    Tendsto collisionMassAfter (𝓝[>] 0) atTop := by
  refine (tendsto_nonrealZeroCount_atTop_of_infinite hinf).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact nonrealZeroCount_eq_collisionMassAfter ht

/-! ## 4. Unconditional Weyl–Jensen small-time bounds on `nonrealZeroCount` and `collisionMass` -/

/-- **General ball zero-multiplicity bound from sphere growth.** For any entire function `f` with
`f 0 ≠ 0`, any radius `R > 0`, and any finite set `S` contained in the open ball `ball 0 R`, the
total multiplicity of `f` on `S` is bounded by `log(Mf / ‖f 0‖) / log 2`, where `Mf > 0` bounds
`‖f z‖` on the circle `‖z‖ = 3 R`. -/
theorem sum_zeroMult_ball_le_of_sphere_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {R Mf : ℝ} (hR : 0 < R) (hMf0 : 0 < Mf)
    (hMf : ∀ z : ℂ, ‖z‖ = 3 * R → ‖f z‖ ≤ Mf) (S : Finset ℂ) (hS : ∀ a ∈ S, ‖a‖ < R) :
    ((∑ a ∈ S, zeroMult f a : ℕ) : ℝ) * Real.log 2 ≤ Real.log (Mf / ‖f 0‖) := by
  classical
  have han : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hnz : ∀ a ∈ (univ : Set ℂ), ¬ ∀ᶠ z in 𝓝 a, f z = 0 := fun a _ h =>
    hf0 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ a) h (mem_univ 0))
  obtain ⟨T, m, g, hg, hTnorm, hgfree, hballR', hfac⟩ :=
    exists_zero_free_cofactor_bounds isOpen_univ hR (by linarith : R < 3 * R) (subset_univ _)
      han hnz hMf
  have hmult : ∀ a ∈ ball (0 : ℂ) R, zeroMult f a = if a ∈ T then m a else 0 :=
    fun a ha => zeroMult_of_factorization isOpen_ball T m
      (hg.differentiableOn.mono (subset_univ _))
      (fun z hz => hgfree z (ball_subset_closedBall hz))
      (fun z _ => hfac z (mem_univ z)) ha
  have hsum_le : ∑ a ∈ S, zeroMult f a ≤ ∑ a ∈ T, m a := by
    calc ∑ a ∈ S, zeroMult f a
        = ∑ a ∈ S, (if a ∈ T then m a else 0) :=
          Finset.sum_congr rfl fun a ha => hmult a (by simpa [mem_ball, dist_zero_right] using hS a ha)
      _ = ∑ a ∈ S.filter (fun a => a ∈ T), m a := (Finset.sum_filter _ _).symm
      _ ≤ ∑ a ∈ T, m a := Finset.sum_le_sum_of_subset fun a ha => (Finset.mem_filter.mp ha).2
  have hcount := sum_multiplicity_mul_log_le hR (by linarith : 2 * R < 3 * R) hMf0 hTnorm
    (hballR' 0 (by simp; linarith)) (hfac 0 (mem_univ 0)) hf0
  have hratio : (3 * R - R) / R = 2 := by field_simp; ring
  rw [hratio] at hcount
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcast : ((∑ a ∈ S, zeroMult f a : ℕ) : ℝ) ≤ ((∑ a ∈ T, m a : ℕ) : ℝ) := by
    exact_mod_cast hsum_le
  exact (mul_le_mul_of_nonneg_right hcast hlog2).trans hcount

/-- At purely imaginary arguments `I * y` (`y : ℝ`), `riemannHeat t (I * y)` is the real positive
integral `∫ x, Φ(x) e^{t x²} e^{−y x}`. -/
theorem norm_riemannHeat_mul_I_eq_integral {t : ℝ} (ht : 0 ≤ t) (y : ℝ) :
    ‖riemannHeat t (I * (y : ℂ))‖ =
      ∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp (-(y * x)) := by
  have hrew : riemannHeat t (I * (y : ℂ)) =
      ((∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2) * Real.exp (-(y * x)) : ℝ) : ℂ) := by
    unfold riemannHeat cosTransform
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    have hexp : I * (I * (y : ℂ)) * (x : ℂ) = ((-(y * x) : ℝ) : ℂ) := by
      calc I * (I * (y : ℂ)) * (x : ℂ) = (I * I) * (y : ℂ) * (x : ℂ) := by ring
        _ = ((-(y * x) : ℝ) : ℂ) := by rw [I_mul_I]; push_cast; ring
    rw [hexp, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [hrew, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact integral_nonneg fun x => by positivity [riemannKernelReal_pos x]

/-- For every `t ≥ 0`, `‖riemannHeat 0 0‖ ≤ ‖riemannHeat t 0‖`. -/
theorem norm_riemannHeat_zero_le_norm_riemannHeat_zero {t : ℝ} (ht : 0 ≤ t) :
    ‖riemannHeat 0 0‖ ≤ ‖riemannHeat t 0‖ := by
  have h0 := norm_riemannHeat_mul_I_eq_integral le_rfl 0
  have ht0 := norm_riemannHeat_mul_I_eq_integral ht 0
  simp only [Complex.ofReal_zero, mul_zero] at h0 ht0
  rw [h0, ht0]
  have hint : ∀ s : ℝ, 0 ≤ s → Integrable (fun x : ℝ =>
      riemannKernelReal x * Real.exp (s * x ^ 2) * Real.exp (-(0 * x))) := by
    intro s hs
    have h := (riemannKernel_superExp.mul_exp_sq hs).integrable_mul_exp 0
    refine h.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [zero_mul, neg_zero]
  refine integral_mono (hint 0 le_rfl) (hint t ht) fun x => ?_
  dsimp only
  rw [zero_mul, neg_zero, Real.exp_zero, mul_one, mul_one]
  exact mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity))
    (riemannKernelReal_pos x).le

/-- For `0 ≤ t ≤ 1/8` and every `z : ℂ`, `‖riemannHeat t z‖ ≤ ‖riemannHeat (1/8) (I * z.im)‖`. -/
theorem norm_riemannHeat_le_eighth_im {t : ℝ} (ht0 : 0 ≤ t) (ht8 : t ≤ 1 / 8) (z : ℂ) :
    ‖riemannHeat t z‖ ≤ ‖riemannHeat (1 / 8) (I * (z.im : ℂ))‖ := by
  rw [norm_riemannHeat_mul_I_eq_integral (by norm_num)]
  unfold riemannHeat cosTransform
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint8 : Integrable (fun x : ℝ => riemannKernelReal x * Real.exp (1 / 8 * x ^ 2) *
      Real.exp (-(z.im * x))) := by
    refine ((riemannKernel_superExp.mul_exp_sq (by norm_num : (0 : ℝ) ≤ 1 / 8)).integrable_mul_exp
      |z.im|).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact ((continuous_riemannKernelReal.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [riemannKernelReal_pos x])]
      gcongr
      · positivity [riemannKernelReal_pos x]
      · rw [← abs_mul]; exact neg_le_abs _
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint8
    (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [norm_integrand, abs_of_nonneg (by positivity [riemannKernelReal_pos x])]
  gcongr
  positivity [riemannKernelReal_pos x]

/-- **Uniform order-one envelope for `H_t` (`0 ≤ t ≤ 1/8`).** There is an absolute constant
`C ≥ 0` (independent of `t`) such that `‖riemannHeat t z‖ ≤ exp(C (1 + ‖z‖) log(2 + ‖z‖))` for all
`0 ≤ t ≤ 1/8` and `z ∈ ℂ`. -/
theorem exists_norm_riemannHeat_le_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → ∀ z : ℂ,
      ‖riemannHeat t z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨C, hC0, hbound⟩ :=
    (riemannKernel_superExp.mul_exp_sq (by norm_num : (0 : ℝ) ≤ 1 / 8)).exists_envelope
  refine ⟨C, hC0, fun t ht0 ht8 z => ?_⟩
  have h1 := norm_riemannHeat_le_eighth_im ht0 ht8 z
  have h2 := hbound (I * (z.im : ℂ))
  have hnorm : ‖I * (z.im : ℂ)‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm z
  refine h1.trans (h2.trans (Real.exp_le_exp.mpr ?_))
  have hlog : Real.log (2 + ‖I * (z.im : ℂ)‖) ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (2 + ‖I * (z.im : ℂ)‖) :=
    Real.log_nonneg (by linarith [norm_nonneg (I * (z.im : ℂ))])
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC0) hlog hlog0 (by positivity)

/-- **Uniform disk zero-count bound for `H_t` (`0 ≤ t ≤ 1/8`).** There is an absolute constant
`C₀ > 0` such that for all `0 ≤ t ≤ 1/8`, all `R ≥ 1`, and every finite set `S ⊆ ball 0 R`,
`∑_{a ∈ S} zeroMult (riemannHeat t) a ≤ C₀ * R * log(2 + 3 R)`. -/
theorem exists_sum_zeroMult_riemannHeat_ball_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → ∀ R : ℝ, 1 ≤ R →
      ∀ S : Finset ℂ, (∀ a ∈ S, ‖a‖ < R) →
        ((∑ a ∈ S, zeroMult (riemannHeat t) a : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
  obtain ⟨C, hC0, hunif⟩ := exists_norm_riemannHeat_le_uniform
  have hf0pos : 0 < ‖riemannHeat 0 0‖ := norm_pos_iff.mpr (riemannHeat_zero_ne le_rfl)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := (4 * C + |Real.log ‖riemannHeat 0 0‖| / Real.log 2 + 1) / Real.log 2
  have hKpos : 0 < K := by positivity
  refine ⟨K, hKpos, fun t ht0 ht8 R hR1 S hS => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  set Mf := Real.exp (C * (1 + 3 * R) * Real.log (2 + 3 * R))
  have hcount := sum_zeroMult_ball_le_of_sphere_bound (Mf := Mf) (differentiable_riemannHeat ht0)
    (riemannHeat_zero_ne ht0) hR0 (Real.exp_pos _)
    (fun z hz => by
      have h := hunif t ht0 ht8 z
      rwa [hz] at h) S hS
  have hf0t : ‖riemannHeat 0 0‖ ≤ ‖riemannHeat t 0‖ :=
    norm_riemannHeat_zero_le_norm_riemannHeat_zero ht0
  have hft0pos : 0 < ‖riemannHeat t 0‖ := lt_of_lt_of_le hf0pos hf0t
  rw [Real.log_div (Real.exp_pos _).ne' hft0pos.ne', Real.log_exp] at hcount
  have hlog_f0 : -Real.log ‖riemannHeat t 0‖ ≤ |Real.log ‖riemannHeat 0 0‖| := by
    have := Real.log_le_log hf0pos hf0t
    linarith [neg_le_abs (Real.log ‖riemannHeat 0 0‖)]
  have hlog3R : Real.log 2 ≤ Real.log (2 + 3 * R) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog3R_pos : 0 < Real.log (2 + 3 * R) := lt_of_lt_of_le hlog2 hlog3R
  have h1R : 1 ≤ R * (Real.log (2 + 3 * R) / Real.log 2) := by
    have : 1 ≤ Real.log (2 + 3 * R) / Real.log 2 := (one_le_div hlog2).mpr hlog3R
    nlinarith
  have h13R : 1 + 3 * R ≤ 4 * R := by linarith
  rw [← le_div_iff₀ hlog2] at hcount
  refine hcount.trans ?_
  rw [show K * R * Real.log (2 + 3 * R) =
    (4 * C + |Real.log ‖riemannHeat 0 0‖| / Real.log 2 + 1) * R * Real.log (2 + 3 * R) /
      Real.log 2 by simp only [K]; ring]
  refine div_le_div_of_nonneg_right ?_ hlog2.le
  have hC_term : C * (1 + 3 * R) * Real.log (2 + 3 * R) ≤ 4 * C * R * Real.log (2 + 3 * R) := by
    nlinarith
  have h0_term : |Real.log ‖riemannHeat 0 0‖| ≤
      (|Real.log ‖riemannHeat 0 0‖| / Real.log 2) * R * Real.log (2 + 3 * R) := by
    have hmul := mul_le_mul_of_nonneg_left h1R (abs_nonneg (Real.log ‖riemannHeat 0 0‖))
    calc |Real.log ‖riemannHeat 0 0‖| = |Real.log ‖riemannHeat 0 0‖| * 1 := by ring
      _ ≤ |Real.log ‖riemannHeat 0 0‖| * (R * (Real.log (2 + 3 * R) / Real.log 2)) := hmul
      _ = _ := by ring
  nlinarith

/-- **Weyl spatial localization of collision points.** For every `ε > 0`, there is `X₀ ≥ 1` such
that for every `t > 0` and every collision point `z ∈ realMultipleZeros t`, `z.im = 0` and
`|z.re| < max X₀ (2π e^{(3/2 + ε)/t})`. -/
theorem exists_realMultipleZeros_abs_lt_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ t : ℝ, 0 < t → ∀ z ∈ realMultipleZeros t,
      z.im = 0 ∧ |z.re| < max X₀ (2 * Real.pi * Real.exp ((3 / 2 + ε) / t)) := by
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_simple_weyl hε
  refine ⟨max X₁ 1, le_max_right _ _, fun t ht z hz => ?_⟩
  rcases le_or_gt t (1 / 8) with ht8 | ht8
  · obtain ⟨hz0, hzim, hdz⟩ := (mem_realMultipleZeros ht ht8).mp hz
    refine ⟨hzim, ?_⟩
    by_contra hge
    push Not at hge
    have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
    have h2 : 2 * Real.pi * Real.exp ((3 / 2 + ε) / t) ≤ |z.re| :=
      (le_max_right _ _).trans hge
    exact (hX₁ t ht ht8 z hz0 h1 h2).2 hdz
  · simp only [realMultipleZeros, dif_neg (not_and.mpr fun _ => not_le.mpr ht8)] at hz
    exact absurd hz (Finset.notMem_empty _)

/-- **Unconditional Weyl–Jensen small-time bound on `nonrealZeroCount t`, remaining collision mass
`∑_{s > t} collisionMass s`, and instantaneous `collisionMass t`.**
For every `ε > 0`, there exist `C₀ > 0` and `X₀ ≥ 1` such that for all `0 < t ≤ 1/8`, with
`R(t) = max X₀ (2π e^{(3/2 + ε)/t}) + 1`:
1. `nonrealZeroCount t ≤ C₀ * R(t) * log(2 + 3 R(t))`,
2. `∑_{s > t} collisionMass s ≤ C₀ * R(t) * log(2 + 3 R(t))`, and
3. `collisionMass t ≤ C₀ * R(t) * log(2 + 3 R(t))`. -/
theorem exists_nonrealZeroCount_and_collisionMass_le_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ X₀ : ℝ, 0 < C₀ ∧ 1 ≤ X₀ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 8 →
      let R := max X₀ (2 * Real.pi * Real.exp ((3 / 2 + ε) / t)) + 1
      ((nonrealZeroCount t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) ∧
      ((∑ s ∈ (finite_collisionTimes ht).toFinset, collisionMass s : ℕ) : ℝ) ≤
        C₀ * R * Real.log (2 + 3 * R) ∧
      ((collisionMass t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
  obtain ⟨C₀, hC₀, hball⟩ := exists_sum_zeroMult_riemannHeat_ball_le
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_simple_weyl hε
  set X₀ := max X₁ 1
  have hX₀1 : 1 ≤ X₀ := le_max_right _ _
  refine ⟨C₀, X₀, hC₀, hX₀1, fun t ht ht8 => ?_⟩
  intro R
  have hR1 : 1 ≤ R := by
    have : 1 ≤ max X₀ (2 * Real.pi * Real.exp ((3 / 2 + ε) / t)) :=
      hX₀1.trans (le_max_left _ _)
    linarith
  have hN : ((nonrealZeroCount t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
    rw [nonrealZeroCount_eq ht]
    refine hball t ht.le ht8 R hR1 _ fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := (riemannHeat_nonreal_zeros_finite ht).mem_toFinset.mp hz
    have hre : |z.re| < max X₀ (2 * Real.pi * Real.exp ((3 / 2 + ε) / t)) := by
      by_contra hge
      push Not at hge
      have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
      have h2 : 2 * Real.pi * Real.exp ((3 / 2 + ε) / t) ≤ |z.re| :=
        (le_max_right _ _).trans hge
      exact hzim (hX₁ t ht ht8 z hz0 h1 h2).1
    have him : |z.im| ≤ 1 / 2 := abs_im_le_half_of_riemannHeat_eq_zero ht hz0
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ < R := by simp only [R]; linarith
  have hC : ((collisionMass t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
    have hle : ((collisionMass t : ℕ) : ℝ) ≤
        ((∑ z ∈ realMultipleZeros t, zeroMult (riemannHeat t) z : ℕ) : ℝ) := by
      exact_mod_cast collisionMass_le_sum_zeroMult t
    refine hle.trans (hball t ht.le ht8 R hR1 _ fun z hz => ?_)
    obtain ⟨hz0, hzim, hdz⟩ := (mem_realMultipleZeros ht ht8).mp hz
    have hre : |z.re| < max X₀ (2 * Real.pi * Real.exp ((3 / 2 + ε) / t)) := by
      by_contra hge
      push Not at hge
      have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
      have h2 : 2 * Real.pi * Real.exp ((3 / 2 + ε) / t) ≤ |z.re| :=
        (le_max_right _ _).trans hge
      exact (hX₁ t ht ht8 z hz0 h1 h2).2 hdz
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ < R := by rw [hzim, abs_zero]; simp only [R]; linarith
  refine ⟨hN, ?_, hC⟩
  have hN' := hN
  rwa [nonrealZeroCount_eq_sum_collisionMass ht] at hN'

/-! ## 5. Critical-heat and retained finite-head coefficient positivity bridges -/

/-- Because `{t' : ℝ | XiC t' ≠ 0}` is dense in `ℝ` and `t' ↦ xiSliceHeatTransfer lam r t' n` is
continuous, nonnegativity of `xiSliceHeatTransfer lam r t' n` at nonvanishing heights `Ξ(t') ≠ 0`
implies nonnegativity at every real height `t`. -/
theorem xiSliceHeatTransfer_nonneg_of_ne_zero {lam r t : ℝ} {n : ℕ}
    (h : ∀ᶠ t' : ℝ in 𝓝 t, XiC (t' : ℂ) ≠ 0 → 0 ≤ xiSliceHeatTransfer lam r t' n) :
    0 ≤ xiSliceHeatTransfer lam r t n := by
  have hc : Continuous fun t' : ℝ => xiSliceHeatTransfer lam r t' n :=
    (continuous_xiSliceHeatTransfer_joint r n).comp
      (Continuous.prodMk continuous_const continuous_id)
  have htend : Tendsto (fun t' : ℝ => xiSliceHeatTransfer lam r t' n) (𝓝[≠] t)
      (𝓝 (xiSliceHeatTransfer lam r t n)) :=
    (hc.tendsto t).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto htend
    (((h.filter_mono nhdsWithin_le_nhds).and (eventually_XiC_ofReal_ne_zero t)).mono
      fun t' ht' => ht'.1 ht'.2)

/-- At the critical WD heat threshold `wdHeatThreshold`, every heated slice coefficient is
nonnegative at every height. -/
theorem xiSliceHeatTransfer_nonneg_at_wdHeatThreshold (t : ℝ) (n : ℕ) :
    (0 : ℂ) ≤ xiSliceHeatTransfer wdHeatThreshold 0 t n :=
  wdHeatThreshold_mem_wdHeatAdmissible t n

/-- At the de Bruijn–Newman constant `newmanConstant`, every heated slice coefficient is
nonnegative at every height. -/
theorem xiSliceHeatTransfer_nonneg_at_newmanConstant (t : ℝ) (n : ℕ) :
    (0 : ℂ) ≤ xiSliceHeatTransfer newmanConstant 0 t n := by
  rcases eq_or_lt_of_le wdHeatThreshold_le_newmanConstant with heq | hlt
  · rw [← heq]
    exact wdHeatThreshold_mem_wdHeatAdmissible t n
  · exact mem_wdHeatAdmissible_of_lt hlt t n

/-- **Retained finite-head polynomial positivity bounds `wdHeatThreshold`.** If at heat `lam ≥ 0`
there is a radius profile `R : ℝ → ℝ` with `R t ≥ 0` and `1/2 ≤ R t ^ 2 + 3 * lam` such that the
heated finite-head polynomial has nonnegative coefficients at every height `t`, then
`wdHeatThreshold ≤ lam`. -/
theorem wdHeatThreshold_le_of_finiteHead_poly_nonneg {lam : ℝ} (hlam : 0 ≤ lam)
    (R : ℝ → ℝ) (hR : ∀ t, 0 ≤ R t) (hcov : ∀ t, 1 / 2 ≤ R t ^ 2 + 3 * lam)
    (hpoly : ∀ t, CoeffNonneg (forwardPolyHeat (lam / 2)
      (Polynomial.expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t (R t)))))) :
    wdHeatThreshold ≤ lam := by
  refine csInf_le wdHeatAdmissible_bddBelow (fun t n => ?_)
  refine xiSliceHeatTransfer_nonneg_of_ne_zero (Eventually.of_forall fun t' ht' => ?_)
  exact xiSliceHeatTransfer_nonneg_of_finiteHead_poly hlam le_rfl ht' (hR t') (hcov t') (hpoly t') n

/-- **Verification-height + finite-head reduction for `wdHeatThreshold`.** If every zero of `ξ`
with `|Im ρ| ≤ H` lies on the critical line, then `wdHeatThreshold ≤ lam` as soon as the retained
finite-head polynomial has nonnegative coefficients at heat `lam ≥ 0` for heights `|t| ≥ H − 1/2`. -/
theorem wdHeatThreshold_le_of_zeros_on_line_below_and_finiteHead {H lam : ℝ} (hlam : 0 ≤ lam)
    (hRH : ∀ ρ : ℂ, xi ρ = 0 → |ρ.im| ≤ H → ρ.re = 1 / 2)
    (R : ℝ → ℝ) (hR : ∀ t, H - 1 / 2 ≤ |t| → 0 ≤ R t)
    (hcov : ∀ t, H - 1 / 2 ≤ |t| → 1 / 2 ≤ R t ^ 2 + 3 * lam)
    (hpoly : ∀ t, H - 1 / 2 ≤ |t| → CoeffNonneg (forwardPolyHeat (lam / 2)
      (Polynomial.expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t (R t)))))) :
    wdHeatThreshold ≤ lam := by
  have hlow : ∀ t : ℝ, |t| ≤ H - 1 / 2 → ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n := by
    intro t ht n
    have hcone : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).im - t| := by
      intro q
      have hz := xi_eq_zero_of_mem_divisor_support q.1
      by_cases hq : |(q.1 : ℂ).im| ≤ H
      · rw [hRH _ hz hq, sub_self, abs_zero]
        exact abs_nonneg _
      · push Not at hq
        have hstrip := xiZeroCopy_re_mem_open_unit q
        have h1 : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := by
          rw [abs_lt]; constructor <;> linarith [hstrip.1, hstrip.2]
        have h2 : 1 / 2 < |(q.1 : ℂ).im - t| := by
          have := abs_sub_abs_le_abs_sub (q.1 : ℂ).im t
          linarith
        linarith
    have hnn := nonnegTaylorAtZero_xiSliceProduct_of_cone hcone
    have hc : ∀ k : ℕ, 0 ≤ xiSliceCoeff t k := by
      intro k
      unfold xiSliceCoeff
      have hf : (0 : ℂ) ≤ (k.factorial : ℂ)⁻¹ := by
        rw [show ((k.factorial : ℂ))⁻¹ = (((k.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl]
        exact Complex.zero_le_real.mpr (by positivity)
      exact mul_nonneg hf (hnn.2 k)
    exact xiSliceHeatTransfer_nonneg_of_coeff_nonneg hlam hc n
  refine csInf_le wdHeatAdmissible_bddBelow (fun t n => ?_)
  by_cases ht : |t| ≤ H - 1 / 2
  · exact hlow t ht n
  · push Not at ht
    have hopen : IsOpen {t' : ℝ | H - 1 / 2 < |t'|} :=
      isOpen_lt continuous_const continuous_abs
    refine xiSliceHeatTransfer_nonneg_of_ne_zero ?_
    filter_upwards [hopen.mem_nhds ht] with t' ht' hne
    exact xiSliceHeatTransfer_nonneg_of_finiteHead_poly hlam le_rfl hne (hR t' ht'.le)
      (hcov t' ht'.le) (hpoly t' ht'.le) n

/-- Under the Riemann Hypothesis, every symmetric truncation polynomial `sliceTruncPoly t S` is
coefficient-nonnegative after any forward heat `s ≥ 0` at every height `t ∈ ℝ`. -/
theorem coeffNonneg_forwardPolyHeat_sliceTruncPoly_of_riemannHypothesis
    (hRH : RiemannHypothesis) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) (S : Finset XiZeroCopy) :
    CoeffNonneg (forwardPolyHeat s (Polynomial.expand ℝ 2 (sliceTruncPoly t S))) := by
  classical
  unfold sliceTruncPoly
  rw [map_mul, map_prod, map_prod]
  refine coeffNonneg_forwardPolyHeat_mul hs
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q _ =>
      coeffNonneg_forwardPolyHeat_sliceLin hs (by unfold sliceAtom; positivity))
    (coeffNonneg_forwardPolyHeat_prod hs _ fun q hq => ?_)
  exfalso
  have him_pos : 0 < (xiSpectralPoint q).im := (mem_sliceTruncUp.mp hq).2
  have hz := xi_eq_zero_of_mem_divisor_support q.1
  have hre : (q.1 : ℂ).re = 1 / 2 :=
    (riemannHypothesis_iff_xi_zeros_on_critical_line.mp hRH) _ hz
  have him0 : (xiSpectralPoint q).im = 0 := by simp [xiSpectralPoint, hre]
  linarith

/-- **All-height finite-head heat positivity criterion for RH.** For any radius `R ≥ 0` with
`1/2 ≤ R²`, the Riemann Hypothesis is equivalent to `CoeffNonneg` of the heated retained
finite-head polynomial at every height `t ∈ ℝ` and every positive heat `lam > 0`. -/
theorem riemannHypothesis_iff_forall_pos_finiteHead_poly_nonneg {R : ℝ} (hR : 0 ≤ R)
    (hR2 : 1 / 2 ≤ R ^ 2) :
    RiemannHypothesis ↔ ∀ lam > 0, ∀ t : ℝ,
      CoeffNonneg (forwardPolyHeat (lam / 2)
        (Polynomial.expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))) := by
  constructor
  · intro hRH lam hlam t
    exact coeffNonneg_forwardPolyHeat_sliceTruncPoly_of_riemannHypothesis hRH (by positivity) t _
  · intro hpoly
    rw [riemannHypothesis_iff_wdHeatThreshold_eq_zero]
    refine le_antisymm ?_ wdHeatThreshold_nonneg
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    exact wdHeatThreshold_le_of_finiteHead_poly_nonneg hε.le (fun _ => R) (fun _ => hR)
      (fun _ => by linarith) (hpoly ε hε)

/-- **Exclusion of positive-time collision mass is equivalent to all-height retained finite-head
heat positivity.** For any radius `R ≥ 0` with `1/2 ≤ R²`, `∀ t > 0, collisionMass t = 0` holds iff
the heated retained finite-head polynomial has nonnegative coefficients at every height `t ∈ ℝ` and
every positive heat `lam > 0`. -/
theorem forall_collisionMass_eq_zero_iff_forall_pos_finiteHead_poly_nonneg {R : ℝ} (hR : 0 ≤ R)
    (hR2 : 1 / 2 ≤ R ^ 2) :
    (∀ t, 0 < t → collisionMass t = 0) ↔ ∀ lam > 0, ∀ t : ℝ,
      CoeffNonneg (forwardPolyHeat (lam / 2)
        (Polynomial.expand ℝ 2 (sliceTruncPoly t (xiSliceGaussianRadiusHead t R)))) :=
  riemannHypothesis_iff_forall_collisionMass_eq_zero.symm.trans
    (riemannHypothesis_iff_forall_pos_finiteHead_poly_nonneg hR hR2)

end

end RHTower.DeBruijn
