import GaloisForLFunctions.RHTower.Deninger.DeningerPeriodizationMap

/-!
# A lattice partition of unity

A compactly supported smooth function lies in the source, because every exponential weight is
bounded on a compact set.  Taking a bump positive on an interval longer than the period, its
periodization is everywhere positive, so dividing by it produces a compactly supported smooth
`\chi` with `\sum_j \chi(t+jL) = 1`.

* `deningerExpSchwartz_of_hasCompactSupport` : compactly supported smooth functions are in `H_-`.
* `deningerPartitionBump` : a bump positive on `(-(|L|+2), |L|+2)`.
* `deningerPartitionDenom` : its periodization, **everywhere positive.**
-/

namespace RHTower

open SchwartzMap Metric

noncomputable section

/-- **A compactly supported Schwartz function lies in the source.** -/
theorem deningerExpSchwartz_of_hasCompactSupport {f : 𝓢(ℝ, ℂ)}
    (hf : HasCompactSupport (f : ℝ → ℂ)) : f ∈ DeningerExpSchwartz := by
  intro A n
  have hcs : HasCompactSupport (fun x : ℝ => Real.exp (A * |x|)
      * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖) := by
    refine HasCompactSupport.mul_left ?_
    exact (hf.iteratedFDeriv n).norm
  have hcont : Continuous (fun x : ℝ => Real.exp (A * |x|)
      * ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖) := by
    refine Continuous.mul ?_ ?_
    · exact Real.continuous_exp.comp (continuous_const.mul continuous_abs)
    · exact ((f.smooth (⊤ : ℕ∞)).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this

/-- A bump positive on an interval strictly longer than the period. -/
def deningerPartitionBump (L : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := |L| + 1
  rOut := |L| + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

@[simp]
theorem deningerPartitionBump_rOut (L : ℝ) : (deningerPartitionBump L).rOut = |L| + 2 := rfl

theorem deningerPartitionBump_nonneg (L : ℝ) (t : ℝ) :
    0 ≤ (deningerPartitionBump L : ℝ → ℝ) t := (deningerPartitionBump L).nonneg

theorem deningerPartitionBump_pos {L t : ℝ} (ht : |t| < |L| + 2) :
    0 < (deningerPartitionBump L : ℝ → ℝ) t := by
  refine (deningerPartitionBump L).pos_of_mem_ball ?_
  simpa [Real.dist_eq] using ht

theorem deningerPartitionBump_hasCompactSupport (L : ℝ) :
    HasCompactSupport (deningerPartitionBump L : ℝ → ℝ) :=
  (deningerPartitionBump L).hasCompactSupport

/-- The bump as a complex-valued Schwartz function. -/
def deningerPartitionSchwartz (L : ℝ) : 𝓢(ℝ, ℂ) :=
  HasCompactSupport.toSchwartzMap
    ((deningerPartitionBump_hasCompactSupport L).comp_left (g := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ))
      (by simp))
    (Complex.ofRealCLM.contDiff.comp (deningerPartitionBump L).contDiff)

theorem deningerPartitionSchwartz_apply (L t : ℝ) :
    ((deningerPartitionSchwartz L : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
      = ((deningerPartitionBump L : ℝ → ℝ) t : ℂ) := rfl

theorem deningerPartitionSchwartz_mem (L : ℝ) :
    deningerPartitionSchwartz L ∈ DeningerExpSchwartz :=
  deningerExpSchwartz_of_hasCompactSupport
    ((deningerPartitionBump_hasCompactSupport L).comp_left (g := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ))
      (by simp))

/-- The real periodization of the bump. -/
def deningerPartitionDenom (L t : ℝ) : ℝ :=
  ∑' j : ℤ, (deningerPartitionBump L : ℝ → ℝ) (t + (j : ℝ) * L)

theorem deningerPartitionDenom_summable {L : ℝ} (hL : 0 < L) (t : ℝ) :
    Summable fun j : ℤ => (deningerPartitionBump L : ℝ → ℝ) (t + (j : ℝ) * L) := by
  have hc := deningerShiftInt_summable (deningerPartitionSchwartz_mem L) hL t
  have hreal : ∀ j : ℤ, ‖(deningerPartitionBump L : ℝ → ℝ) (t + (j : ℝ) * L)‖
      = ‖((deningerPartitionSchwartz L : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (t + (j : ℝ) * L)‖ := by
    intro j
    rw [deningerPartitionSchwartz_apply, Complex.norm_real]
  exact Summable.of_norm_bounded hc.norm (fun j => le_of_eq (hreal j))

/-- The complex periodization of the bump is the real one. -/
theorem deningerPartitionDenom_coe {L : ℝ} (hL : 0 < L) (t : ℝ) :
    deningerPeriodizationSum (deningerPartitionSchwartz L) L t
      = ((deningerPartitionDenom L t : ℝ) : ℂ) := by
  have hmap := ContinuousLinearMap.map_tsum (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)
    (deningerPartitionDenom_summable hL t)
  rw [deningerPeriodizationSum, deningerPartitionDenom,
    show ((∑' j : ℤ, (deningerPartitionBump L : ℝ → ℝ) (t + (j : ℝ) * L) : ℝ) : ℂ)
      = Complex.ofRealCLM (∑' j : ℤ, (deningerPartitionBump L : ℝ → ℝ) (t + (j : ℝ) * L)) from rfl,
    hmap]
  rfl

/-- **The periodized bump is everywhere positive.**  Some lattice translate of any point lands in
the interval where the bump is positive, and all terms are nonnegative. -/
theorem deningerPartitionDenom_pos {L : ℝ} (hL : 0 < L) (t : ℝ) :
    0 < deningerPartitionDenom L t := by
  set n : ℤ := -⌊t / L⌋ with hn
  have hfr : t + (n : ℝ) * L = L * Int.fract (t / L) := by
    rw [hn, Int.fract]
    push_cast
    field_simp
    ring
  have hlt : |t + (n : ℝ) * L| < |L| + 2 := by
    have h0 : 0 ≤ Int.fract (t / L) := Int.fract_nonneg _
    have h1 : Int.fract (t / L) < 1 := Int.fract_lt_one _
    rw [hfr, abs_of_nonneg (by positivity)]
    have hlt' : L * Int.fract (t / L) < L := mul_lt_of_lt_one_right hL h1
    have hLabs : L ≤ |L| := le_abs_self L
    linarith
  refine lt_of_lt_of_le (deningerPartitionBump_pos hlt) ?_
  exact Summable.le_tsum (deningerPartitionDenom_summable hL t) n
    (fun j _ => deningerPartitionBump_nonneg L _)

/-- The denominator is `L`-periodic. -/
theorem deningerPartitionDenom_periodic {L : ℝ} (hL : 0 < L) (t : ℝ) :
    deningerPartitionDenom L (t + L) = deningerPartitionDenom L t := by
  have h := deningerPeriodizationSum_periodic (deningerPartitionSchwartz L) L t
  rw [deningerPartitionDenom_coe hL, deningerPartitionDenom_coe hL] at h
  exact_mod_cast h

/-- The denominator is smooth. -/
theorem deningerPartitionDenom_contDiff {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ (⊤ : ℕ∞) (deningerPartitionDenom L) := by
  have h := deningerPeriodizationSum_contDiff (deningerPartitionSchwartz_mem L) hL
  have heq : (fun t => Complex.reCLM
      (deningerPeriodizationSum (deningerPartitionSchwartz L) L t))
      = deningerPartitionDenom L := by
    funext t
    rw [deningerPartitionDenom_coe hL]
    simp
  rw [← heq]
  exact Complex.reCLM.contDiff.comp h

end

end RHTower
