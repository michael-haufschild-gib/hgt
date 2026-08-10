import GaloisForLFunctions.RHTower.GaussComponentMagnitudeResidue
import GaloisForLFunctions.RHTower.GaussComponentVerticalPhase
import GaloisForLFunctions.HTGeometry.PositiveSequenceBounds

/-!
# Uniform bounds for the sampled Gauss-component energy

The sampled critical energy `|d_n|^{2m}` is asymptotic to `log p / (n+1)`.  Since it is strictly
positive at every index and its rescaling converges to a strictly positive limit, the asymptotic
upgrades to the uniform two-sided estimate

`c/(n+1) ≤ |d_n|^{2m} ≤ C/(n+1)`,

and hence to the shifted ratio bound `|d_{n+j}|^{2m} ≤ K |d_n|^{2m} (n+1)/(n+j+1)`, which is the
form the high-frequency tail estimate consumes.

The module also records the exact relation between the magnitude used by the residue computation
and the norm of the actual vertical Gauss component: they differ by the constant `(π/m)^{1/(2m)}`.
-/

namespace RHTower

open Filter Topology

noncomputable section

/-! ## Positivity and the magnitude/value bridge -/

theorem gaussComponentVerticalMagnitude_pos {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (t : ℝ) :
    0 < gaussComponentVerticalMagnitude k t := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hbase : (0 : ℝ) < Real.pi / (m : ℝ) := by positivity
  rw [gaussComponentVerticalMagnitude]
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (Real.exp_pos _)

theorem gaussComponentVerticalUpperArg_eq_magnitudeArg {m : ℕ} (k : Fin m) (t : ℝ) :
    gaussComponentVerticalUpperArg k (t : ℂ) =
      (gaussComponentOffset k : ℂ) + (t / (2 * (m : ℝ)) : ℂ) * Complex.I := by
  rw [gaussComponentVerticalUpperArg]
  push_cast
  ring

theorem gaussComponentVerticalLowerArg_eq_magnitudeArg {m : ℕ} (k : Fin m) (t : ℝ) :
    gaussComponentVerticalLowerArg k (t : ℂ) =
      ((gaussComponentOffset k + gaussComponentDelta m : ℝ) : ℂ) -
        (t / (2 * (m : ℝ)) : ℂ) * Complex.I := by
  rw [gaussComponentVerticalLowerArg]
  push_cast
  ring

/-- **Magnitude and value agree up to the archimedean constant.**  The magnitude used by the
residue computation is `(π/m)^{1/(2m)}` times the norm of the actual vertical Gauss component. -/
theorem gaussComponentVerticalMagnitude_eq_norm_value
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) {t : ℝ} (ht : 0 < t) :
    gaussComponentVerticalMagnitude k t =
      (Real.pi / (m : ℝ)) ^ gaussComponentDelta m *
        ‖gaussComponentVerticalValue k t‖ := by
  have hu : Complex.Gamma (gaussComponentVerticalUpperArg k (t : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero (gaussComponentVerticalUpperArg_ne_neg_nat hm k ht)
  have hv : Complex.Gamma (gaussComponentVerticalLowerArg k (t : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero (gaussComponentVerticalLowerArg_ne_neg_nat hm k ht)
  have hupos : 0 < ‖Complex.Gamma (gaussComponentVerticalUpperArg k (t : ℂ))‖ :=
    norm_pos_iff.mpr hu
  have hvpos : 0 < ‖Complex.Gamma (gaussComponentVerticalLowerArg k (t : ℂ))‖ :=
    norm_pos_iff.mpr hv
  have hnorm : ‖gaussComponentVerticalValue k t‖
      = ‖Complex.Gamma (gaussComponentVerticalUpperArg k (t : ℂ))‖ /
        ‖Complex.Gamma (gaussComponentVerticalLowerArg k (t : ℂ))‖ := by
    rw [gaussComponentVerticalValue, gaussComponentVerticalCarrier, norm_div, norm_mul,
      Complex.norm_exp]
    have hre : (-(Complex.I / (m : ℂ)) * (Real.log (Real.pi / (m : ℝ)) : ℂ) * (t : ℂ)).re = 0 := by
      have hform : (-(Complex.I / (m : ℂ)) * (Real.log (Real.pi / (m : ℝ)) : ℂ) * (t : ℂ))
          = ((-(Real.log (Real.pi / (m : ℝ)) * t / (m : ℝ)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hform]
      simp
    rw [hre, Real.exp_zero, one_mul]
  rw [gaussComponentVerticalMagnitude, hnorm, ← gaussComponentVerticalUpperArg_eq_magnitudeArg,
    ← gaussComponentVerticalLowerArg_eq_magnitudeArg, Real.exp_sub, Real.exp_log hupos,
    Real.exp_log hvpos]

/-! ## Uniform two-sided bounds on the sampled energy -/

theorem gaussComponentPrimeMagnitudeEnergy_pos {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (n : ℕ) : 0 < gaussComponentPrimeMagnitudeEnergy k p n := by
  rw [gaussComponentPrimeMagnitudeEnergy]
  exact pow_pos (gaussComponentVerticalMagnitude_pos hm k _) _

/-- **Uniform two-sided energy bound.**  The sampled critical energy is comparable to `1/(n+1)`
at every index, not only asymptotically. -/
theorem exists_gaussComponentPrimeMagnitudeEnergy_bounds
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      c / ((n : ℝ) + 1) ≤ gaussComponentPrimeMagnitudeEnergy k p n ∧
        gaussComponentPrimeMagnitudeEnergy k p n ≤ C / ((n : ℝ) + 1) := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    GaloisForLFunctions.exists_pos_bounds_of_tendsto_pos hlog
      (fun n => mul_pos (gaussComponentPrimeMagnitudeEnergy_pos hm k p n) (by positivity))
      (gaussComponentPrimeMagnitudeEnergy_mul_succ_tendsto hm k p)
  refine ⟨c, C, hc, hC, fun n => ?_⟩
  obtain ⟨h1, h2⟩ := hbounds n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact ⟨(div_le_iff₀ hn).mpr h1, (le_div_iff₀ hn).mpr h2⟩

/-- **Shifted ratio bound.**  The sampled energy at a forward shift is controlled by the energy at
the base index, with the exact harmonic factor. -/
theorem exists_gaussComponentPrimeMagnitudeEnergy_ratio_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ K : ℝ, 0 < K ∧ ∀ n j : ℕ,
      gaussComponentPrimeMagnitudeEnergy k p (n + j) ≤
        K * gaussComponentPrimeMagnitudeEnergy k p n *
          (((n : ℝ) + 1) / ((n : ℝ) + (j : ℝ) + 1)) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_gaussComponentPrimeMagnitudeEnergy_bounds hm k p
  refine ⟨C / c, div_pos hC hc, fun n j => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnj : (0 : ℝ) < (n : ℝ) + (j : ℝ) + 1 := by positivity
  have hup : gaussComponentPrimeMagnitudeEnergy k p (n + j)
      ≤ C / ((n : ℝ) + (j : ℝ) + 1) := by
    have h := (hb (n + j)).2
    push_cast at h
    convert h using 2
  have hlow : c / ((n : ℝ) + 1) ≤ gaussComponentPrimeMagnitudeEnergy k p n := (hb n).1
  have hmono : C / c * (c / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / ((n : ℝ) + (j : ℝ) + 1))
      ≤ C / c * gaussComponentPrimeMagnitudeEnergy k p n *
        (((n : ℝ) + 1) / ((n : ℝ) + (j : ℝ) + 1)) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hstep : C / c * (c / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / ((n : ℝ) + (j : ℝ) + 1))
      = C / ((n : ℝ) + (j : ℝ) + 1) := by
    field_simp
  rw [hstep] at hmono
  linarith

end

end RHTower
