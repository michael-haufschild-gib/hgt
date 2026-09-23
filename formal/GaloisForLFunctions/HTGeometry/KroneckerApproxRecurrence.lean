import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity

/-!
# Kronecker recurrence at arbitrarily large times

The approximation theorem for a rationally independent frequency family holds with the
approximating time pushed beyond any prescribed bound.  The mechanism is unchanged: the Bohr mean
of the positive kernel product is a fixed polynomially small quantity, and a Bohr mean only sees
the tail of the line, so a pointwise exponential bound valid merely for large times already
contradicts it.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-- **Kronecker recurrence.**  A rationally independent frequency family returns arbitrarily close
to every point of the torus at arbitrarily large times. -/
theorem kronecker_approx_atTop {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ι → ℝ}
    (hind : LinearIndependent ℚ lam) (θ : ι → ℝ) {ε : ℝ} (hε : 0 < ε) (T₀ : ℝ) :
    ∃ t : ℝ, T₀ < t ∧ ∀ j : ι,
      ‖expChar (lam j) t - Complex.exp ((θ j : ℝ) * Complex.I)‖ < ε := by
  classical
  set m : ℕ := Fintype.card ι with hm
  by_contra hcon
  push Not at hcon
  set S : ℝ := max T₀ 0 with hS
  have hS0 : (0 : ℝ) ≤ S := le_max_right _ _
  have hTS : T₀ ≤ S := le_max_left _ _
  set q : ℝ := max 0 (1 - ε ^ (2 : ℕ) / 4) with hqdef
  have hq0 : 0 ≤ q := le_max_left _ _
  have hq1 : q < 1 := by
    refine max_lt one_pos ?_
    nlinarith
  -- the pointwise bound along the far part of the line
  have hpoint : ∀ (K : ℕ) (t : ℝ), T₀ < t →
      ∏ j : ι, cosKernel K (lam j * t - θ j) ≤ q ^ K := by
    intro K t htt
    obtain ⟨j₀, hj₀⟩ := hcon t htt
    have hcos : (1 + Real.cos (lam j₀ * t - θ j₀)) / 2 ≤ q := by
      have hsq := norm_expChar_sub_sq (lam j₀ * t) (θ j₀)
      have hge : ε ^ (2 : ℕ) ≤ ‖expChar (lam j₀) t - Complex.exp ((θ j₀ : ℝ) * Complex.I)‖ ^ (2 : ℕ) := by
        have hnn : (0 : ℝ) ≤ ‖expChar (lam j₀) t - Complex.exp ((θ j₀ : ℝ) * Complex.I)‖ :=
          norm_nonneg _
        nlinarith [hj₀]
      have hexpeq : expChar (lam j₀) t = Complex.exp (((lam j₀ * t : ℝ) : ℝ) * Complex.I) := rfl
      rw [hexpeq, hsq] at hge
      have : Real.cos (lam j₀ * t - θ j₀) ≤ 1 - ε ^ (2 : ℕ) / 2 := by linarith
      have hle : (1 + Real.cos (lam j₀ * t - θ j₀)) / 2 ≤ 1 - ε ^ (2 : ℕ) / 4 := by linarith
      exact hle.trans (le_max_right _ _)
    have hbad : cosKernel K (lam j₀ * t - θ j₀) ≤ q ^ K := cosKernel_le_pow hcos
    calc ∏ j : ι, cosKernel K (lam j * t - θ j)
        ≤ ∏ j : ι, (if j = j₀ then q ^ K else 1) := by
          refine Finset.prod_le_prod (fun j _ => cosKernel_nonneg K _) (fun j _ => ?_)
          by_cases hj : j = j₀
          · subst hj; simpa using hbad
          · simpa [hj] using cosKernel_le_one K (lam j * t - θ j)
      _ = q ^ K := by simp
  -- the mean of the kernel product is dominated by the bound on the tail alone
  have hmeanbound : ∀ K : ℕ, ‖((Nat.choose (2 * K) K : ℂ) / 4 ^ K) ^ m‖ ≤ q ^ K := by
    intro K
    set g : ℝ → ℂ := fun t => ((∏ j : ι, cosKernel K (lam j * t - θ j) : ℝ) : ℂ) with hg
    have hgsum : g = fun t => ∑ v ∈ Fintype.piFinset (fun _ : ι => Finset.range (2 * K + 1)),
        (∏ j : ι, ((Nat.choose (2 * K) (v j) : ℂ) / 4 ^ K) *
            Complex.exp ((-(((v j : ℝ) - K) * θ j) : ℝ) * Complex.I))
          * expChar (∑ j : ι, ((v j : ℝ) - K) * lam j) t :=
      funext fun t => ofReal_prod_cosKernel_eq_sum lam θ K t
    have hgc : Continuous g := by
      rw [hgsum]
      exact continuous_finsetSum _ fun v _ => continuous_const.mul (continuous_expChar _)
    have hga : HTGeometry.IsBohrAlmostPeriodic g := by
      rw [hgsum]
      exact isBohrAlmostPeriodic_sum _ (fun v _ => continuous_const.mul (continuous_expChar _))
        (fun v _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))
    have hgle : ∀ x : ℝ, ‖g x‖ ≤ 1 := by
      intro x
      rw [hg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.prod_nonneg fun j _ => cosKernel_nonneg K _)]
      exact Finset.prod_le_one (fun j _ => cosKernel_nonneg K _)
        (fun j _ => cosKernel_le_one K _)
    have hnorm : Tendsto (fun T => ‖windowAverage g T‖) atTop (nhds ‖bohrMean g‖) :=
      (continuous_norm.tendsto _).comp (tendsto_windowAverage_bohrMean hgc hga)
    have hrhs : Tendsto (fun T : ℝ => S / T + q ^ K) atTop (nhds (0 + q ^ K)) := by
      refine Filter.Tendsto.add ?_ tendsto_const_nhds
      exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have hbd : ‖bohrMean g‖ ≤ q ^ K := by
      have hle : ‖bohrMean g‖ ≤ 0 + q ^ K := by
        refine le_of_tendsto_of_tendsto hnorm hrhs ?_
        filter_upwards [eventually_gt_atTop (max S 1)] with T hT
        have hST : S ≤ T := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hT)
        have hT0 : (0 : ℝ) < T := lt_trans one_pos (lt_of_le_of_lt (le_max_right _ _) hT)
        have hsplit : (∫ t in (0 : ℝ)..T, g t)
            = (∫ t in (0 : ℝ)..S, g t) + ∫ t in S..T, g t :=
          (intervalIntegral.integral_add_adjacent_intervals
            (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)).symm
        have hb1 : ‖∫ t in (0 : ℝ)..S, g t‖ ≤ 1 * |S - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => hgle x
        have hb2 : ‖∫ t in S..T, g t‖ ≤ q ^ K * |T - S| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
          rw [Set.uIoc_of_le hST] at hx
          rw [hg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Finset.prod_nonneg fun j _ => cosKernel_nonneg K _)]
          exact hpoint K x (lt_of_le_of_lt hTS hx.1)
        have hb1' : ‖∫ t in (0 : ℝ)..S, g t‖ ≤ S := by
          rw [sub_zero, abs_of_nonneg hS0, one_mul] at hb1
          exact hb1
        have hb2' : ‖∫ t in S..T, g t‖ ≤ q ^ K * T := by
          have habs : |T - S| = T - S := abs_of_nonneg (by linarith)
          rw [habs] at hb2
          nlinarith [pow_nonneg hq0 K]
        simp only [windowAverage, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hT0.le)]
        rw [hsplit]
        have hsum : ‖(∫ t in (0 : ℝ)..S, g t) + ∫ t in S..T, g t‖ ≤ S + q ^ K * T :=
          le_trans (norm_add_le _ _) (by linarith)
        calc T⁻¹ * ‖(∫ t in (0 : ℝ)..S, g t) + ∫ t in S..T, g t‖
            ≤ T⁻¹ * (S + q ^ K * T) :=
              mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hT0.le)
          _ = S / T + q ^ K := by field_simp
      simpa using hle
    have hbd' := hbd
    rw [hg] at hbd'
    rw [← bohrMean_prod_cosKernel hind θ K]
    exact hbd'
  -- the central binomial lower bound
  have hlower : ∀ K : ℕ, (1 : ℝ) / (2 * (K : ℝ) + 1) ≤ (Nat.choose (2 * K) K : ℝ) / 4 ^ K := by
    intro K
    have hR : (4 : ℝ) ^ K ≤ (2 * (K : ℝ) + 1) * (Nat.choose (2 * K) K : ℝ) := by
      exact_mod_cast four_pow_le_succ_mul_centralBinom K
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hfinal : ∀ K : ℕ, (1 : ℝ) ≤ (2 * (K : ℝ) + 1) ^ m * q ^ K := by
    intro K
    have h1 := hmeanbound K
    have hnormeq : ‖((Nat.choose (2 * K) K : ℂ) / 4 ^ K) ^ m‖
        = ((Nat.choose (2 * K) K : ℝ) / 4 ^ K) ^ m := by
      rw [norm_pow]
      congr 1
      rw [norm_div]
      norm_num
    rw [hnormeq] at h1
    have h2 : ((1 : ℝ) / (2 * (K : ℝ) + 1)) ^ m ≤ ((Nat.choose (2 * K) K : ℝ) / 4 ^ K) ^ m :=
      pow_le_pow_left₀ (by positivity) (hlower K) m
    have h3 : ((1 : ℝ) / (2 * (K : ℝ) + 1)) ^ m ≤ q ^ K := le_trans h2 h1
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)] at h3
    linarith
  have hdecay : Tendsto (fun K : ℕ => (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K)) atTop (nhds 0) := by
    have habs : |q| < 1 := by rwa [abs_of_nonneg hq0]
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one m habs
    simpa using h.const_mul ((3 : ℝ) ^ m)
  have hev := Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1) hdecay
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hev
  set K : ℕ := max K0 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hsmall : (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K) < 1 := hK0 K (le_max_left _ _)
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hcmp : (2 * (K : ℝ) + 1) ^ m * q ^ K ≤ (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K) := by
    have hbase : 2 * (K : ℝ) + 1 ≤ 3 * (K : ℝ) := by linarith
    have hp : (2 * (K : ℝ) + 1) ^ m ≤ (3 * (K : ℝ)) ^ m :=
      pow_le_pow_left₀ (by positivity) hbase m
    calc (2 * (K : ℝ) + 1) ^ m * q ^ K ≤ (3 * (K : ℝ)) ^ m * q ^ K :=
          mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (3 : ℝ) ^ m * ((K : ℝ) ^ m * q ^ K) := by rw [mul_pow]; ring
  linarith [hfinal K]

end

end GaloisForLFunctions
