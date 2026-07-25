import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Rigidity of finite real-exponential sums

A finite sum `sum_i B i * exp (u * J i)` with pairwise distinct **real** exponents `J i` and nonzero
complex coefficients cannot cancel: as `u -> infinity` the term with the largest exponent dominates
every other term, so the sum grows at exactly that rate.  Consequently a two-sided growth bound
`‖sum‖ <= C * exp (lam * |u|)` forces every exponent into `[-lam, lam]`.

This is what distinguishes a set of equal-height spectral points from a general almost-periodic
family: no separation or Diophantine hypothesis on the exponents is needed, only that they are real
and distinct.
-/

open Filter
open scoped BigOperators

namespace HTGeometry

/-- **One-sided rigidity.**  A growth bound `C * exp (lam * |u|)` on a finite sum of real
exponentials with distinct exponents and nonzero coefficients caps every exponent by `lam`. -/
theorem le_of_expSum_norm_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (J : ι → ℝ) (B : ι → ℂ)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, J i = J j → i = j)
    (hB : ∀ i ∈ s, B i ≠ 0) {C lam : ℝ}
    (hbound : ∀ u : ℝ, ‖∑ i ∈ s, B i * (Real.exp (u * J i) : ℂ)‖ ≤ C * Real.exp (lam * |u|)) :
    ∀ i ∈ s, J i ≤ lam := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨i₀, hi₀s, hi₀max⟩ := s.exists_max_image J hs
  suffices h : J i₀ ≤ lam by
    exact fun i hi => le_trans (hi₀max i hi) h
  by_contra hlt
  push Not at hlt
  refine (hB i₀ hi₀s) ?_
  set g : ℝ → ℂ := fun u => ∑ i ∈ s, B i * (Real.exp (u * (J i - J i₀)) : ℂ) with hg
  have hA : Tendsto g atTop (nhds (B i₀)) := by
    have hterm : ∀ i ∈ s, Tendsto (fun u : ℝ => B i * (Real.exp (u * (J i - J i₀)) : ℂ))
        atTop (nhds (if i = i₀ then B i else 0)) := by
      intro i hi
      by_cases hii : i = i₀
      · subst hii
        simp
      · have hneg : J i - J i₀ < 0 := by
          rcases lt_or_eq_of_le (hi₀max i hi) with hcase | hcase
          · linarith
          · exact absurd (hinj i hi i₀ hi₀s hcase) hii
        have h1 : Tendsto (fun u : ℝ => u * (J i - J i₀)) atTop atBot :=
          Filter.Tendsto.atTop_mul_const_of_neg hneg Filter.tendsto_id
        have h2 : Tendsto (fun u : ℝ => Real.exp (u * (J i - J i₀))) atTop (nhds 0) :=
          Real.tendsto_exp_atBot.comp h1
        have h3 : Tendsto (fun u : ℝ => ((Real.exp (u * (J i - J i₀)) : ℝ) : ℂ))
            atTop (nhds 0) := by
          have hc := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h2
          simpa only [Complex.ofReal_zero, Function.comp_def] using hc
        simpa [hii] using h3.const_mul (B i)
    have hsum := tendsto_finsetSum s hterm
    rwa [Finset.sum_ite_eq' s i₀ B, if_pos hi₀s] at hsum
  have hB0 : Tendsto (fun u => ‖g u‖) atTop (nhds 0) := by
    refine squeeze_zero' (g := fun u : ℝ => C * Real.exp (u * (lam - J i₀)))
      (Eventually.of_forall fun u => norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      have hfac : g u = (∑ i ∈ s, B i * (Real.exp (u * J i) : ℂ)) *
          ((Real.exp (-(u * J i₀)) : ℝ) : ℂ) := by
        rw [hg, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
          show u * J i + -(u * J i₀) = u * (J i - J i₀) from by ring]
      have h1 := hbound u
      rw [abs_of_nonneg hu] at h1
      rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc ‖∑ i ∈ s, B i * (Real.exp (u * J i) : ℂ)‖ * Real.exp (-(u * J i₀))
          ≤ C * Real.exp (lam * u) * Real.exp (-(u * J i₀)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = C * Real.exp (u * (lam - J i₀)) := by
            rw [mul_assoc, ← Real.exp_add,
              show lam * u + -(u * J i₀) = u * (lam - J i₀) from by ring]
    · have hneg : lam - J i₀ < 0 := by linarith
      have h1 : Tendsto (fun u : ℝ => u * (lam - J i₀)) atTop atBot :=
        Filter.Tendsto.atTop_mul_const_of_neg hneg Filter.tendsto_id
      have h2 : Tendsto (fun u : ℝ => Real.exp (u * (lam - J i₀))) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp h1
      simpa using h2.const_mul C
  exact norm_eq_zero.mp (tendsto_nhds_unique hA.norm hB0)

/-- **Two-sided rigidity.**  Under the same hypotheses every exponent lies in `[-lam, lam]`. -/
theorem abs_le_of_expSum_norm_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (J : ι → ℝ) (B : ι → ℂ)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, J i = J j → i = j)
    (hB : ∀ i ∈ s, B i ≠ 0) {C lam : ℝ}
    (hbound : ∀ u : ℝ, ‖∑ i ∈ s, B i * (Real.exp (u * J i) : ℂ)‖ ≤ C * Real.exp (lam * |u|)) :
    ∀ i ∈ s, |J i| ≤ lam := by
  have hinj' : ∀ i ∈ s, ∀ j ∈ s, (fun k => -J k) i = (fun k => -J k) j → i = j := by
    intro a ha b hb h
    exact hinj a ha b hb (by simpa using neg_injective h)
  have hbound' : ∀ u : ℝ,
      ‖∑ i ∈ s, B i * (Real.exp (u * (fun k => -J k) i) : ℂ)‖ ≤ C * Real.exp (lam * |u|) := by
    intro u
    have heq : (∑ i ∈ s, B i * (Real.exp (u * (fun k => -J k) i) : ℂ))
        = ∑ i ∈ s, B i * (Real.exp (-u * J i) : ℂ) :=
      Finset.sum_congr rfl fun i _ => by
        rw [show u * (fun k => -J k) i = -u * J i from by simp]
    rw [heq]
    simpa using hbound (-u)
  intro i hi
  have hup := le_of_expSum_norm_le s J B hinj hB hbound i hi
  have hlow := le_of_expSum_norm_le s (fun k => -J k) B hinj' hB hbound' i hi
  simp only at hlow
  rw [abs_le]
  exact ⟨by linarith, hup⟩

/-- **Phase-robust dominance.**  A finite family of real exponentials with distinct exponents and
coefficients of fixed positive moduli -- but otherwise arbitrary, possibly parameter-dependent,
phases -- cannot stay bounded unless every exponent is nonpositive.  Phases do not change moduli, so
they cannot cancel the largest exponent; no averaging, almost-periodicity, or separation hypothesis
is needed. -/
theorem le_zero_of_expSum_norm_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (J : ι → ℝ) (m : ι → ℝ) (hm : ∀ i ∈ s, 0 < m i)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, J i = J j → i = j)
    {M : ℝ} (B : ℝ → ι → ℂ) (hB : ∀ (u : ℝ), ∀ i ∈ s, ‖B u i‖ = m i)
    (hbound : ∀ u : ℝ, ‖∑ i ∈ s, B u i * (Real.exp (u * J i) : ℂ)‖ ≤ M) :
    ∀ i ∈ s, J i ≤ 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨i₀, hi₀s, hi₀max⟩ := s.exists_max_image J hs
  suffices h : J i₀ ≤ 0 by
    exact fun i hi => le_trans (hi₀max i hi) h
  by_contra hlt
  push Not at hlt
  have hlow : ∀ i ∈ s.erase i₀, J i - J i₀ < 0 := by
    intro i hi
    have hine : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    have his : i ∈ s := (Finset.mem_erase.mp hi).2
    rcases lt_or_eq_of_le (hi₀max i his) with hcase | hcase
    · linarith
    · exact absurd (hinj i his i₀ hi₀s hcase) hine
  set g : ℝ → ℂ := fun u => ∑ i ∈ s, B u i * (Real.exp (u * (J i - J i₀)) : ℂ) with hg
  have hfac : ∀ u : ℝ, g u =
      (∑ i ∈ s, B u i * (Real.exp (u * J i) : ℂ)) * ((Real.exp (-(u * J i₀)) : ℝ) : ℂ) := by
    intro u
    rw [hg, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      show u * J i + -(u * J i₀) = u * (J i - J i₀) from by ring]
  have hupper : ∀ u : ℝ, ‖g u‖ ≤ M * Real.exp (-(u * J i₀)) := by
    intro u
    rw [hfac u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hbound u) (Real.exp_pos _).le
  have hlower : ∀ u : ℝ,
      m i₀ - ∑ i ∈ s.erase i₀, m i * Real.exp (u * (J i - J i₀)) ≤ ‖g u‖ := by
    intro u
    have hsplit : g u = B u i₀ +
        ∑ i ∈ s.erase i₀, B u i * (Real.exp (u * (J i - J i₀)) : ℂ) := by
      show (∑ i ∈ s, B u i * (Real.exp (u * (J i - J i₀)) : ℂ)) = _
      rw [← Finset.add_sum_erase s (fun i => B u i * (Real.exp (u * (J i - J i₀)) : ℂ)) hi₀s]
      simp
    have htail : ‖∑ i ∈ s.erase i₀, B u i * (Real.exp (u * (J i - J i₀)) : ℂ)‖ ≤
        ∑ i ∈ s.erase i₀, m i * Real.exp (u * (J i - J i₀)) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        hB u i (Finset.mem_erase.mp hi).2]
    have h := norm_sub_norm_le (B u i₀)
      (-(∑ i ∈ s.erase i₀, B u i * (Real.exp (u * (J i - J i₀)) : ℂ)))
    rw [norm_neg, sub_neg_eq_add, ← hsplit, hB u i₀ hi₀s] at h
    linarith
  have hlimU : Filter.Tendsto (fun u : ℝ => M * Real.exp (-(u * J i₀))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun u : ℝ => u * -(J i₀)) Filter.atTop Filter.atBot :=
      Filter.Tendsto.atTop_mul_const_of_neg (by linarith) Filter.tendsto_id
    have h2 : Filter.Tendsto (fun u : ℝ => Real.exp (-(u * J i₀))) Filter.atTop (nhds 0) := by
      have := Real.tendsto_exp_atBot.comp h1
      refine this.congr fun u => ?_
      simp only [Function.comp_apply]
      congr 1
      ring
    simpa using h2.const_mul M
  have hlimL : Filter.Tendsto
      (fun u : ℝ => m i₀ - ∑ i ∈ s.erase i₀, m i * Real.exp (u * (J i - J i₀)))
      Filter.atTop (nhds (m i₀)) := by
    have hterm : ∀ i ∈ s.erase i₀,
        Filter.Tendsto (fun u : ℝ => m i * Real.exp (u * (J i - J i₀))) Filter.atTop (nhds 0) := by
      intro i hi
      have h1 : Filter.Tendsto (fun u : ℝ => u * (J i - J i₀)) Filter.atTop Filter.atBot :=
        Filter.Tendsto.atTop_mul_const_of_neg (hlow i hi) Filter.tendsto_id
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (m i)
    have hsum := tendsto_finsetSum (s.erase i₀) hterm
    simpa using tendsto_const_nhds.sub hsum
  have hfinal : m i₀ ≤ 0 :=
    le_of_tendsto_of_tendsto' hlimL hlimU (fun u => le_trans (hlower u) (hupper u))
  exact absurd (hm i₀ hi₀s) (not_lt.mpr hfinal)

end HTGeometry
