import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeMellinSingularity

/-!
# Exact Mellin factorization of the critical full-prime dilation

The literal Abel primitive sampled by terminal children is absolutely
Mellin-summable over all prime dilations to the right of the square-root
abscissa. Its transform is the product of the source Mellin transform and
the prime zeta function. This is the first global bridge in the boundary
singularity attack; it does not yet estimate the square-root terminal core.
-/

noncomputable section
open Filter Topology Set Complex MeasureTheory Finset
namespace RHTower

private theorem integral_rpow_abs_scaled {f : ℝ → ℝ} {σ m : ℝ} (hm0 : 0 < m) :
    (∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * |f (m * t)|)
      = m ^ (-σ) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x| := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x : ℝ => (x / m) ^ (σ - 1) * |f x|) 0 hm0
  rw [mul_zero] at h
  have hlhs : (∫ t in Ioi (0 : ℝ), ((m * t) / m) ^ (σ - 1) * |f (m * t)|)
      = ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * |f (m * t)| := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_comm m t, mul_div_assoc, div_self (ne_of_gt hm0), mul_one]
  rw [hlhs] at h
  have hrhs : (∫ x in Ioi (0 : ℝ), (x / m) ^ (σ - 1) * |f x|)
      = m ^ (-(σ - 1)) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x| := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [Real.div_rpow hx.le hm0.le, Real.rpow_neg hm0.le]
    field_simp
  rw [hrhs, smul_eq_mul] at h
  rw [h]
  have hcomb : m⁻¹ * (m ^ (-(σ - 1)) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x|)
      = m ^ (-σ) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x| := by
    have hinv : m⁻¹ = m ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]
    rw [hinv, ← mul_assoc, ← Real.rpow_add hm0]
    congr 2
    ring
  exact hcomb

private def criticalPrimeAbelTerm (p : Nat.Primes) (x : ℝ) : ℂ :=
  ((Real.sqrt (p : ℝ) : ℝ) : ℂ) *
    (criticalContinuousAbel (x / (p : ℝ)) : ℂ)

private theorem criticalPrimeAbelTerm_mellin (p : Nat.Primes) (σ : ℝ) :
    mellin (criticalPrimeAbelTerm p) (-(σ : ℂ)) =
      (((p : ℝ) ^ ((1 / 2 : ℝ) - σ) : ℝ) : ℂ) *
        mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ)) (-(σ : ℂ)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpinv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp
  have hfun : criticalPrimeAbelTerm p = fun x : ℝ =>
      (Real.sqrt (p : ℝ) : ℂ) •
        ((fun y : ℝ => (criticalContinuousAbel y : ℂ)) ((p : ℝ)⁻¹ * x)) := by
    funext x
    simp only [criticalPrimeAbelTerm, smul_eq_mul]
    congr 1
    congr 1
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun, mellin_const_smul,
    mellin_comp_mul_left (fun x : ℝ => (criticalContinuousAbel x : ℂ))
      (-(σ : ℂ)) hpinv]
  simp only [neg_neg, smul_eq_mul]
  have hpow : (((p : ℝ)⁻¹ : ℝ) : ℂ) ^ (σ : ℂ) =
      (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hpinv.le, Real.inv_rpow hp.le,
      ← Real.rpow_neg hp.le]
  rw [hpow, ← mul_assoc, ← Complex.ofReal_mul, Real.sqrt_eq_rpow,
    ← Real.rpow_add hp]
  simp only [sub_eq_add_neg]

private theorem criticalPrimeAbelTerm_convergent (p : Nat.Primes) {σ : ℝ}
    (hσ : 3 / 2 < σ) : MellinConvergent (criticalPrimeAbelTerm p) (-(σ : ℂ)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hbase := (hasMellin_criticalContinuousAbel
    (s := (σ : ℂ)) (by simpa using hσ)).1
  have hcomp := (MellinConvergent.comp_mul_left
    (f := fun x : ℝ => (criticalContinuousAbel x : ℂ))
    (s := -(σ : ℂ)) (inv_pos.mpr hp)).2 hbase
  have hsmul := hcomp.const_smul (Real.sqrt (p : ℝ) : ℂ)
  convert hsmul using 1
  funext x
  simp only [criticalPrimeAbelTerm, smul_eq_mul]
  congr 1
  congr 1
  rw [div_eq_mul_inv, mul_comm]

private theorem criticalPrimeAbelTerm_integral_norm (p : Nat.Primes) (σ : ℝ) :
    (∫ x in Ioi (0 : ℝ),
      ‖(x : ℂ) ^ (-(σ : ℂ) - 1) • criticalPrimeAbelTerm p x‖) =
      (∫ x in Ioi (0 : ℝ), x ^ (-σ - 1) * |criticalContinuousAbel x|) *
        (p : ℝ) ^ ((1 / 2 : ℝ) - σ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpinv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      ‖(x : ℂ) ^ (-(σ : ℂ) - 1) • criticalPrimeAbelTerm p x‖ =
        Real.sqrt (p : ℝ) *
          (x ^ (-σ - 1) * |criticalContinuousAbel (x / (p : ℝ))|) := by
    intro x hx
    simp only [criticalPrimeAbelTerm, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [sub_re, neg_re, ofReal_re, one_re]
    ring
  calc
    _ = Real.sqrt (p : ℝ) *
        (∫ x in Ioi (0 : ℝ),
          x ^ (-σ - 1) * |criticalContinuousAbel (x / (p : ℝ))|) := by
          rw [← integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = Real.sqrt (p : ℝ) *
        ((p : ℝ)⁻¹ ^ σ *
          ∫ x in Ioi (0 : ℝ), x ^ (-σ - 1) * |criticalContinuousAbel x|) := by
          have hscale := integral_rpow_abs_scaled
            (f := criticalContinuousAbel) (σ := -σ) (m := (p : ℝ)⁻¹) hpinv
          have harg (x : ℝ) : x / (p : ℝ) = (p : ℝ)⁻¹ * x := by ring
          simp_rw [harg]
          simpa only [neg_neg] using
            congrArg (fun t : ℝ => Real.sqrt (p : ℝ) * t) hscale
    _ = _ := by
      rw [Real.inv_rpow hp.le, ← Real.rpow_neg hp.le,
        Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hp]
      simp only [sub_eq_add_neg]
      ring

def criticalPrimeAbelHead (x : ℝ) : ℂ :=
  ∑' p : Nat.Primes, criticalPrimeAbelTerm p x

theorem mellin_criticalPrimeAbelHead (σ : ℝ) (hσ : 3 / 2 < σ) :
    mellin criticalPrimeAbelHead (-(σ : ℂ)) =
      (primeZeta (σ - 1 / 2) : ℂ) *
        mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ)) (-(σ : ℂ)) := by
  let K : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (-σ - 1) * |criticalContinuousAbel x|
  let F : Nat.Primes → ℝ → ℂ := fun p x =>
    (x : ℂ) ^ (-(σ : ℂ) - 1) • criticalPrimeAbelTerm p x
  have hweight : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ ((1 / 2 : ℝ) - σ)) := by
    have hexp : (1 / 2 : ℝ) - σ = -(σ - 1 / 2) := by ring
    simpa only [hexp] using
      (summable_primeZetaTerm (s := σ - 1 / 2) (by linarith))
  have hFint : ∀ p : Nat.Primes,
      Integrable (F p) (volume.restrict (Ioi (0 : ℝ))) := by
    intro p
    exact criticalPrimeAbelTerm_convergent p hσ
  have hFnorm (p : Nat.Primes) :
      (∫ x, ‖F p x‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
        K * (p : ℝ) ^ ((1 / 2 : ℝ) - σ) :=
    criticalPrimeAbelTerm_integral_norm p σ
  have hFsum : Summable fun p : Nat.Primes =>
      ∫ x, ‖F p x‖ ∂(volume.restrict (Ioi (0 : ℝ))) := by
    simp_rw [hFnorm]
    exact hweight.mul_left K
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  have hfun : (fun x : ℝ => (x : ℂ) ^ (-(σ : ℂ) - 1) • criticalPrimeAbelHead x) =
      fun x => ∑' p : Nat.Primes, F p x := by
    funext x
    simp only [criticalPrimeAbelHead, F, smul_eq_mul]
    rw [← tsum_mul_left]
  rw [mellin, hfun, ← hswap]
  have hterm (p : Nat.Primes) :
      (∫ x, F p x ∂(volume.restrict (Ioi (0 : ℝ)))) =
        (((p : ℝ) ^ ((1 / 2 : ℝ) - σ) : ℝ) : ℂ) *
          mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ)) (-(σ : ℂ)) := by
    simpa only [mellin, F] using criticalPrimeAbelTerm_mellin p σ
  simp_rw [hterm]
  rw [tsum_mul_right]
  have hsum : (∑' p : Nat.Primes,
      (((p : ℝ) ^ ((1 / 2 : ℝ) - σ) : ℝ) : ℂ)) =
      (primeZeta (σ - 1 / 2) : ℂ) := by
    have h := (Complex.ofRealCLM.hasSum hweight.hasSum).tsum_eq
    simpa only [primeZeta, Function.comp_def, Complex.ofRealCLM_apply,
      show (1 / 2 : ℝ) - σ = -(σ - 1 / 2) by ring] using h
  rw [hsum]

/-- The actual all-prime dilated Abel head has a finite-order logarithmic
boundary singularity with nonzero leading coefficient. -/
theorem criticalPrimeAbelHead_logJet :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun δ : ℝ =>
        mellin criticalPrimeAbelHead
          (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) /
          (δ : ℂ) ^ r /
          ((abscissaLog (1 + δ) : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  obtain ⟨r, hr, c, hc, hjet⟩ := criticalAbelPrimeMellin_logJet
  refine ⟨r, hr, c, hc, ?_⟩
  have heq : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      mellin criticalPrimeAbelHead
          (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) /
          (δ : ℂ) ^ r /
          ((abscissaLog (1 + δ) : ℝ) : ℂ) =
        (mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ))
          (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) / (δ : ℂ) ^ r) *
          ((primeZeta (1 + δ) / abscissaLog (1 + δ) : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ at hδ
    have hσ : 3 / 2 < (1 + δ + 1 / 2 : ℝ) := by linarith
    have harg : -((1 : ℂ) + (δ : ℂ) + 1 / 2) =
        -(((1 + δ + 1 / 2 : ℝ) : ℂ)) := by push_cast; ring
    rw [harg, mellin_criticalPrimeAbelHead _ hσ]
    have hp : 1 + δ + 1 / 2 - 1 / 2 = (1 + δ : ℝ) := by ring
    rw [hp]
    rw [← harg]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  refine hjet.congr' ?_
  filter_upwards [heq] with δ h
  exact h.symm

/-- The source has no mass at or below its unit onset. -/
theorem criticalContinuousAbel_eq_zero_le_one {x : ℝ} (hx : x ≤ 1) :
    criticalContinuousAbel x = 0 := by
  unfold criticalContinuousAbel
  rw [squareRootSummatoryPrimitive_eq_integral]
  simp [Set.Ioo_eq_empty_of_le hx]

theorem criticalPrimeAbelHead_eq_finite (x : ℝ) (N : ℕ)
    (hN : x ≤ N) :
    criticalPrimeAbelHead x =
      ∑ p ∈ (Finset.range N).subtype Nat.Prime,
        (Real.sqrt (p : ℝ) : ℂ) *
          (criticalContinuousAbel (x / (p : ℝ)) : ℂ) := by
  unfold criticalPrimeAbelHead
  change (∑' p : {p : ℕ // p.Prime},
      (Real.sqrt (p : ℝ) : ℂ) *
        (criticalContinuousAbel (x / (p : ℝ)) : ℂ)) = _
  refine tsum_eq_sum (s := (Finset.range N).subtype Nat.Prime) ?_
  intro p hpS
  have hpN : N ≤ (p : ℕ) := by
    by_contra h
    have hlt : (p : ℕ) < N := Nat.lt_of_not_ge h
    exact hpS (by simpa using hlt)
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hx : x / (p : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hp]
    simpa using hN.trans (by exact_mod_cast hpN)
  simp [criticalContinuousAbel_eq_zero_le_one hx]

end RHTower
