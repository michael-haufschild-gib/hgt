import GaloisForLFunctions.TransHorizonIncidenceMechanics.LogarithmicMomentHierarchySeparatesEveryPositivePair

/-!
# The logarithmic moments are a complete receiver invariant

For a damped weight `c`, `M(c·log^k) = −Σ_d c(d) log^{k+1} d / d` is, up to sign, the `(k+1)`-st
derivative at `s = 1` of the Dirichlet series `L_c(s) = Σ c(d) d^{-s}`, which is holomorphic on
`Re s > 1 − ε`. If two damped weights have the same logarithmic moments of every order, the
difference `L_c − L_{c'}` has all derivatives of positive order zero at `s = 1`; by Taylor expansion it
is constant near `1`, by analytic continuation constant on the half-plane, and by uniqueness of
Dirichlet coefficients `c − c'` is a multiple of `δ₁` on the positive integers. The receiver does not
see `δ₁` (its prefix vanishes), so **two damped weights with equal logarithmic pronic moments have
the same receiver**: every parity pair, whatever the signs of its members, is separated by some
`M(c·log^k)`. With the positive-pair theorem this names the separating additive observables
completely: the first pronic moments of the log-power weights.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

theorem firstPronicMoment_logPowWeight_eq_tsum {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (k : ℕ) :
    firstPronicMoment (logPowWeight c k) = -∑' d : ℕ, c d * Real.log d ^ (k + 1) / d := by
  have hcl := logPowWeight_mem_dampedClass hε hc k
  have hε2 : 0 < ε / 2 := by linarith
  unfold firstPronicMoment
  rw [(hasSum_weightCenteredPrefix_div_pronic (summable_div_of_dampedClass hε2 hcl)
    (summable_abs_mul_log_div_of_dampedClass hε2 hcl)).tsum_eq]
  congr 1
  exact tsum_congr fun d => by rw [logPowWeight, pow_succ]; ring

theorem summable_mul_logPow_div {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c)
    (k : ℕ) : Summable (fun d : ℕ => c d * Real.log d ^ (k + 1) / d) := by
  have hcl := logPowWeight_mem_dampedClass hε hc k
  refine (summable_abs_mul_log_div_of_dampedClass (by linarith) hcl).of_norm_bounded fun d =>
    le_of_eq ?_
  have hl := Real.log_natCast_nonneg d
  rw [Real.norm_eq_abs, logPowWeight, abs_div, abs_mul, abs_mul, Nat.abs_cast,
    abs_of_nonneg (pow_nonneg hl (k + 1)), abs_of_nonneg (pow_nonneg hl k), pow_succ]
  ring

theorem logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]; ring

/-- The receiver does not see `δ₁`: adding `a δ₁` preserves receiver boundedness. -/
theorem receiverBounded_add_unitMass {c : ℕ → ℝ} (hs : Summable (fun d : ℕ => c d / d)) (a : ℝ) :
    ReceiverBounded (fun d => c d + a * unitMass d) ↔ ReceiverBounded c := by
  set m := ∑' k : ℕ, c k / k
  have hu : HasSum (fun d : ℕ => unitMass d / d) 1 := by
    have h := hasSum_ite_eq (1 : ℕ) (1 : ℝ)
    refine h.congr_fun fun d => ?_
    by_cases hd : d = 1 <;> simp [unitMass, hd]
  have hmean : ∑' d : ℕ, (c d + a * unitMass d) / d = m + a := by
    have h := hs.hasSum.add (hu.mul_left a)
    rw [mul_one] at h
    refine (h.congr_fun fun d => ?_).tsum_eq
    ring
  have hA : ∀ n, weightCenteredPrefix (fun d => c d + a * unitMass d) (m + a) n =
      weightCenteredPrefix c m n := fun n => by
    have hu1 : ∀ j ∈ Icc 1 n, ∑ d ∈ j.divisors, unitMass d = 1 := fun j hj => by
      have hj : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
      rw [Finset.sum_eq_single 1 (fun d _ hd => by simp [unitMass, hd]) (fun h => absurd
        (Nat.one_mem_divisors.mpr hj) h)]
      simp [unitMass]
    unfold weightCenteredPrefix
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl hu1]
    simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one]
    ring
  unfold ReceiverBounded weightPronicEnergy
  rw [hmean]
  simp only [hA]
  exact Iff.rfl

/-- **Equal logarithmic moments force equality up to `δ₁`.** -/
theorem eq_add_unitMass_of_logMoments_eq {K K' ε : ℝ} (hε : 0 < ε) {c c' : ℕ → ℝ}
    (hc : DampedClass K ε c) (hc' : DampedClass K' ε c')
    (hM : ∀ k : ℕ, firstPronicMoment (logPowWeight c k) = firstPronicMoment (logPowWeight c' k)) :
    ∀ d : ℕ, 2 ≤ d → c d = c' d := by
  have hK := nonneg_of_dampedClass hc
  have hK' := nonneg_of_dampedClass hc'
  set D : ℕ → ℂ := fun n => ((c n - c' n : ℝ) : ℂ)
  -- the Dirichlet series of the difference converges absolutely on `Re s > 1 − ε`
  have hbound : ∃ C, ∀ n : ℕ, n ≠ 0 → ‖D n‖ ≤ C * (n : ℝ) ^ (-ε) := ⟨K + K', fun n _ => by
    simp only [D, Complex.norm_real, Real.norm_eq_abs]
    calc |c n - c' n| ≤ |c n| + |c' n| := abs_sub _ _
      _ ≤ K * (n : ℝ) ^ (-ε) + K' * (n : ℝ) ^ (-ε) := add_le_add (hc n) (hc' n)
      _ = (K + K') * (n : ℝ) ^ (-ε) := by ring⟩
  have habs : LSeries.abscissaOfAbsConv D ≤ ((-ε : ℝ) : EReal) + 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow hbound
  set U : Set ℂ := {s : ℂ | 1 - ε < s.re}
  have hU : U ⊆ {s : ℂ | LSeries.abscissaOfAbsConv D < s.re} := fun s hs => by
    refine habs.trans_lt ?_
    have : (-ε : ℝ) + 1 < s.re := by simp only [U, Set.mem_setOf_eq] at hs; linarith
    exact_mod_cast this
  set L := LSeries D
  have hL : AnalyticOnNhd ℂ L U := (LSeries_analyticOnNhd D).mono hU
  have h1U : (1 : ℂ) ∈ U := by simp only [U, Set.mem_setOf_eq, one_re]; linarith
  -- all derivatives of positive order vanish at `1`
  have hderiv : ∀ k : ℕ, iteratedDeriv (k + 1) L 1 = 0 := by
    intro k
    rw [LSeries_iteratedDeriv (k + 1) (hU h1U)]
    have hdiff : ∑' d : ℕ, (c d - c' d) * Real.log d ^ (k + 1) / d = 0 := by
      have h := hM k
      rw [firstPronicMoment_logPowWeight_eq_tsum hε hc, firstPronicMoment_logPowWeight_eq_tsum hε hc',
        neg_inj] at h
      rw [show (fun d : ℕ => (c d - c' d) * Real.log d ^ (k + 1) / d) = fun d =>
          c d * Real.log d ^ (k + 1) / d - c' d * Real.log d ^ (k + 1) / d from
        funext fun d => by ring, (summable_mul_logPow_div hε hc k).tsum_sub
          (summable_mul_logPow_div hε hc' k), h, sub_self]
    have hterm : ∀ n : ℕ, LSeries.term (LSeries.logMul^[k + 1] D) 1 n =
        (((c n - c' n) * Real.log n ^ (k + 1) / n : ℝ) : ℂ) := fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      rw [LSeries.term_of_ne_zero hn, logMul_iterate_apply, cpow_one,
        show Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) by
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]]
      simp only [D]
      push_cast; ring
    rw [LSeries, tsum_congr hterm, ← Complex.ofReal_tsum, hdiff, Complex.ofReal_zero, mul_zero]
  -- Taylor: `L` is constant on a ball around `1`
  have hball : Metric.ball (1 : ℂ) ε ⊆ U := fun z hz => by
    simp only [U, Set.mem_setOf_eq]
    have h := abs_re_le_norm (z - 1)
    rw [Metric.mem_ball, dist_eq_norm] at hz
    simp only [sub_re, one_re] at h
    linarith [abs_le.mp h]
  have hconst : ∀ z ∈ Metric.ball (1 : ℂ) ε, L z = L 1 := fun z hz => by
    have hT := Complex.hasSum_taylorSeries_on_ball
      ((hL.mono hball).differentiableOn) hz
    have hz' : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (z - 1) ^ n • iteratedDeriv n L 1)
        (L 1) := by
      convert hasSum_ite_eq 0 (L 1) using 1
      funext n
      rcases n with _ | n
      · simp
      · rw [hderiv n, smul_zero, smul_zero, if_neg (Nat.succ_ne_zero n)]
    exact hT.unique hz'
  have hev : (fun s => L s - L 1) =ᶠ[𝓝 (1 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (1 : ℂ) hε] with z hz
    simp [hconst z hz]
  have hU_pre : IsPreconnected U := (convex_halfSpace_re_gt (1 - ε)).isPreconnected
  have heq := (hL.sub analyticOnNhd_const).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hU_pre h1U hev
  -- uniqueness of Dirichlet coefficients against the constant `L(1) δ₁`
  set G : ℕ → ℂ := fun n => if n = 1 then L 1 else 0
  have hG : LSeries.abscissaOfAbsConv G < ⊤ := by
    refine (LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) ⟨‖L 1‖, fun n _ => ?_⟩).trans_lt
      (by exact_mod_cast (EReal.coe_lt_top _))
    simp only [G]; split_ifs <;> simp
  have hD : LSeries.abscissaOfAbsConv D < ⊤ :=
    habs.trans_lt (by exact_mod_cast EReal.coe_lt_top _)
  have hLG : ∀ s : ℂ, LSeries G s = L 1 := fun s => by
    rw [LSeries, tsum_eq_single 1 fun n hn => by simp [LSeries.term_def, G, hn]]
    simp [G]
  have hev2 : (fun x : ℝ => LSeries D x) =ᶠ[atTop] fun x => LSeries G x := by
    filter_upwards [eventually_gt_atTop (1 - ε)] with x hx
    have h := heq (show ((x : ℂ)) ∈ U by simp [U, hx])
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
    rw [hLG]; exact h
  intro d hd
  have h := LSeries.eq_of_LSeries_eventually_eq hD hG hev2 (show d ≠ 0 by omega)
  simp only [D, G, if_neg (show d ≠ 1 by omega)] at h
  have := Complex.ofReal_eq_zero.mp h
  linarith

/-- **Every parity pair is separated by a logarithmic moment.** If two damped weights have different
receiver behaviour, some logarithmic pronic moment `M(c·log^k)` distinguishes them. -/
theorem exists_logMoment_ne {K K' ε : ℝ} (hε : 0 < ε) {c c' : ℕ → ℝ}
    (hc : DampedClass K ε c) (hc' : DampedClass K' ε c')
    (hdiff : ¬ (ReceiverBounded c ↔ ReceiverBounded c')) :
    ∃ k : ℕ, firstPronicMoment (logPowWeight c k) ≠ firstPronicMoment (logPowWeight c' k) := by
  by_contra hall
  push Not at hall
  have h2 := eq_add_unitMass_of_logMoments_eq hε hc hc' hall
  apply hdiff
  have hcongr : ∀ d, 0 < d → c d = c' d + (c 1 - c' 1) * unitMass d := fun d hd => by
    rcases eq_or_ne d 1 with rfl | hd1
    · simp [unitMass]
    · rw [h2 d (by omega)]; simp [unitMass, hd1]
  rw [receiverBounded_congr hcongr]
  exact receiverBounded_add_unitMass (summable_div_of_dampedClass hε hc') _

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
