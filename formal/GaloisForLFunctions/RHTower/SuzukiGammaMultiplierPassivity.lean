import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBound
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit

/-!
# Asymptotic passivity of the archimedean Gamma multiplier

With the pole-cleared archimedean factor

```text
γ(s) = s (s - 1) π^(-s/2) Γ(s/2) / 2
```

and `0 < ω < 1/2`, the Suzuki multiplier on the critical Mellin line is

```text
m_ω(t) = γ(1/2 - ω + i t) / γ(1/2 + ω + i t) .
```

Its supremum is computed **exactly**, with no Stirling asymptotics:

```text
M_ω = sup_t |m_ω(t)| = π^ω Γ(1/4 - ω/2) / Γ(1/4 + ω/2) ,
```

attained at `t = 0`.  Two exact cancellations do the work.  The polynomial prefactor is unimodular
on the critical line, because

```text
|1/2 - ω + it| · |-1/2 - ω + it| = |1/2 + ω + it| · |-1/2 + ω + it| ,
```

and the Gamma quotient is largest on the real axis by
`HTGeometry.norm_Gamma_mul_Gamma_le`.  Since `Γ` is continuous and positive at `1/4`, this gives
`M_ω < ∞` for every shift and `M_ω → 1` as `ω → 0+`: the multiplier is asymptotically passive
without being contractive at any fixed positive shift.

Plancherel then transports the bound to `L²`, entrywise summation transports it to the divisor
incidence curvature, and the four-unit budget of the parent clock law survives the completion in
the limit.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-! ### The archimedean factor and its multiplier -/

/-- The pole-cleared archimedean factor `γ(s) = s(s-1)π^(-s/2)Γ(s/2)/2`. -/
def suzukiArchimedeanFactor (s : ℂ) : ℂ :=
  s * (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) / 2

/-- The Suzuki Gamma multiplier on the critical Mellin line. -/
def suzukiGammaMultiplier (ω t : ℝ) : ℂ :=
  suzukiArchimedeanFactor (((1 / 2 - ω : ℝ) : ℂ) + (t : ℂ) * I) /
    suzukiArchimedeanFactor (((1 / 2 + ω : ℝ) : ℂ) + (t : ℂ) * I)

/-- The exact multiplier norm `M_ω = π^ω Γ(1/4 - ω/2)/Γ(1/4 + ω/2)`. -/
def suzukiGammaMultiplierNorm (ω : ℝ) : ℝ :=
  Real.pi ^ ω * (Real.Gamma (1 / 4 - ω / 2) / Real.Gamma (1 / 4 + ω / 2))

/-- Closed form for the modulus of the archimedean factor on a vertical line. -/
theorem norm_suzukiArchimedeanFactor (x t : ℝ) :
    ‖suzukiArchimedeanFactor ((x : ℂ) + (t : ℂ) * I)‖
      = Real.sqrt (x ^ 2 + t ^ 2) * Real.sqrt ((x - 1) ^ 2 + t ^ 2) * Real.pi ^ (-x / 2)
        * ‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ / 2 := by
  have hsub : ((x : ℂ) + (t : ℂ) * I) - 1 = ((x - 1 : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast
    ring
  have hhalf : ((x : ℂ) + (t : ℂ) * I) / 2 = ((x / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hre : (-((x : ℂ) + (t : ℂ) * I) / 2).re = -x / 2 := by
    simp only [Complex.div_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.neg_im, Complex.add_im,
      Complex.mul_im, Complex.normSq_apply]
    norm_num
    ring
  rw [suzukiArchimedeanFactor, norm_div, norm_mul, norm_mul, norm_mul, hsub, hhalf,
    HTGeometry.norm_ofReal_add_mul_I, HTGeometry.norm_ofReal_add_mul_I,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hre]
  norm_num

/-- **Exact multiplier bound.**  For every shift `0 < ω < 1/2` and every height, the Suzuki
multiplier is bounded by the closed value `M_ω`. -/
theorem norm_suzukiGammaMultiplier_le {ω : ℝ} (hω : 0 < ω) (hω' : ω < 1 / 2) (t : ℝ) :
    ‖suzukiGammaMultiplier ω t‖ ≤ suzukiGammaMultiplierNorm ω := by
  set a : ℝ := 1 / 4 - ω / 2 with ha'
  set b : ℝ := 1 / 4 + ω / 2 with hb'
  have hapos : 0 < a := by simp only [ha']; linarith
  have hab : a ≤ b := by simp only [ha', hb']; linarith
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos hapos
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos (by linarith)
  -- the Gamma quotient is maximal on the real axis
  have hkey := HTGeometry.norm_Gamma_mul_Gamma_le hapos hab (t / 2)
  -- the polynomial prefactors coincide
  have hpoly : Real.sqrt ((1 / 2 - ω) ^ 2 + t ^ 2) * Real.sqrt (((1 / 2 - ω) - 1) ^ 2 + t ^ 2)
      = Real.sqrt ((1 / 2 + ω) ^ 2 + t ^ 2) * Real.sqrt (((1 / 2 + ω) - 1) ^ 2 + t ^ 2) := by
    have h1 : ((1 / 2 - ω) - 1) ^ 2 = (1 / 2 + ω) ^ 2 := by ring
    have h2 : ((1 / 2 + ω) - 1) ^ 2 = (1 / 2 - ω) ^ 2 := by ring
    rw [h1, h2]
    ring
  have hpi : Real.pi ^ (-(1 / 2 - ω) / 2)
      = Real.pi ^ ω * Real.pi ^ (-(1 / 2 + ω) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hcastA : ((1 / 2 - ω) / 2 : ℝ) = a := by simp only [ha']; ring
  have hcastB : ((1 / 2 + ω) / 2 : ℝ) = b := by simp only [hb']; ring
  have hA := norm_suzukiArchimedeanFactor (1 / 2 - ω) t
  have hB := norm_suzukiArchimedeanFactor (1 / 2 + ω) t
  rw [hcastA] at hA
  rw [hcastB] at hB
  set P : ℝ := Real.sqrt ((1 / 2 + ω) ^ 2 + t ^ 2)
    * Real.sqrt (((1 / 2 + ω) - 1) ^ 2 + t ^ 2) with hP
  have hPnn : 0 ≤ P := by
    simp only [hP]
    positivity
  set GA : ℝ := ‖Complex.Gamma ((a : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ with hGA
  set GB : ℝ := ‖Complex.Gamma ((b : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ with hGB
  have hGAnn : 0 ≤ GA := norm_nonneg _
  have hGBnn : 0 ≤ GB := norm_nonneg _
  have hpipos : (0 : ℝ) < Real.pi ^ (-(1 / 2 + ω) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  -- the numerator is bounded by `M_ω` times the denominator
  have hmain : ‖suzukiArchimedeanFactor (((1 / 2 - ω : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ suzukiGammaMultiplierNorm ω *
        ‖suzukiArchimedeanFactor (((1 / 2 + ω : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    rw [hA, hB, hpoly, hpi, suzukiGammaMultiplierNorm, ← ha', ← hb']
    have hstep : GA * Real.Gamma b ≤ Real.Gamma a * GB := hkey
    have hGAle : GA ≤ Real.Gamma a / Real.Gamma b * GB := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hGb]
      linarith
    have hfac : (0 : ℝ) ≤ P * (Real.pi ^ ω * Real.pi ^ (-(1 / 2 + ω) / 2)) / 2 := by
      have : (0 : ℝ) < Real.pi ^ ω := Real.rpow_pos_of_pos Real.pi_pos _
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hGAle hfac]
  have hnum : ‖suzukiGammaMultiplier ω t‖
      = ‖suzukiArchimedeanFactor (((1 / 2 - ω : ℝ) : ℂ) + (t : ℂ) * I)‖ /
        ‖suzukiArchimedeanFactor (((1 / 2 + ω : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    rw [suzukiGammaMultiplier, norm_div]
  rcases eq_or_lt_of_le (norm_nonneg
      (suzukiArchimedeanFactor (((1 / 2 + ω : ℝ) : ℂ) + (t : ℂ) * I))) with hzero | hpos
  · rw [hnum, ← hzero, div_zero]
    have hM : 0 ≤ suzukiGammaMultiplierNorm ω := by
      rw [suzukiGammaMultiplierNorm]
      have : (0 : ℝ) < Real.pi ^ ω := Real.rpow_pos_of_pos Real.pi_pos _
      positivity
    exact hM
  · rw [hnum, div_le_iff₀ hpos]
    exact hmain

/-- The bound is attained on the real axis, so `M_ω` is the exact supremum of the multiplier
modulus. -/
theorem norm_suzukiGammaMultiplier_zero {ω : ℝ} (hω : 0 < ω) (hω' : ω < 1 / 2) :
    ‖suzukiGammaMultiplier ω 0‖ = suzukiGammaMultiplierNorm ω := by
  have hgamma : ∀ x : ℝ, 0 < x →
      ‖Complex.Gamma (((x : ℝ) : ℂ) + (((0 : ℝ) / 2 : ℝ) : ℂ) * I)‖ = Real.Gamma x := by
    intro x hx
    have hzero : (((0 : ℝ) / 2 : ℝ) : ℂ) * I = 0 := by norm_num
    rw [hzero, add_zero, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos hx)]
  have hsq : ∀ x : ℝ, 0 ≤ x → Real.sqrt (x ^ 2 + (0 : ℝ) ^ 2) = x := by
    intro x hx
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq hx]
  have hsqneg : ∀ x : ℝ, x ≤ 0 → Real.sqrt (x ^ 2 + (0 : ℝ) ^ 2) = -x := by
    intro x hx
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs, abs_of_nonpos hx]
  have hA := norm_suzukiArchimedeanFactor (1 / 2 - ω) 0
  have hB := norm_suzukiArchimedeanFactor (1 / 2 + ω) 0
  rw [hsq (1 / 2 - ω) (by linarith), hsqneg ((1 / 2 - ω) - 1) (by linarith),
    hgamma ((1 / 2 - ω) / 2) (by linarith)] at hA
  rw [hsq (1 / 2 + ω) (by linarith), hsqneg ((1 / 2 + ω) - 1) (by linarith),
    hgamma ((1 / 2 + ω) / 2) (by linarith)] at hB
  have hGa : 0 < Real.Gamma ((1 / 2 - ω) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hGb : 0 < Real.Gamma ((1 / 2 + ω) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpiA : (0 : ℝ) < Real.pi ^ (-(1 / 2 - ω) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hpiB : (0 : ℝ) < Real.pi ^ (-(1 / 2 + ω) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hpi : Real.pi ^ (-(1 / 2 - ω) / 2)
      = Real.pi ^ ω * Real.pi ^ (-(1 / 2 + ω) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hcastA : ((1 / 2 - ω) / 2 : ℝ) = 1 / 4 - ω / 2 := by ring
  have hcastB : ((1 / 2 + ω) / 2 : ℝ) = 1 / 4 + ω / 2 := by ring
  have hpref : (1 / 2 - ω) * -(1 / 2 - ω - 1) = (1 / 2 + ω) * -(1 / 2 + ω - 1) := by ring
  have hK : ((1 / 2 + ω) * -(1 / 2 + ω - 1) : ℝ) ≠ 0 := by
    have : ((1 / 2 + ω) * -(1 / 2 + ω - 1) : ℝ) = (1 / 2 + ω) * (1 / 2 - ω) := by ring
    rw [this]
    have h1 : (0 : ℝ) < 1 / 2 + ω := by linarith
    have h2 : (0 : ℝ) < 1 / 2 - ω := by linarith
    positivity
  have halg : ∀ K pA pB GA GB : ℝ, K ≠ 0 → pB ≠ 0 → GB ≠ 0 →
      (K * (pA * pB) * GA / 2) / (K * pB * GB / 2) = pA * (GA / GB) := by
    intro K pA pB GA GB hK hpB hGB
    field_simp
  have hGbne : Real.Gamma (1 / 4 + ω / 2) ≠ 0 := by
    rw [← hcastB]
    exact hGb.ne'
  have hpiBne : Real.pi ^ (-(1 / 2 + ω) / 2) ≠ 0 := hpiB.ne'
  rw [suzukiGammaMultiplier, norm_div, hA, hB, suzukiGammaMultiplierNorm, hcastA, hcastB, hpi,
    hpref]
  exact halg _ _ _ _ _ hK hpiBne hGbne

/-! ### The multiplier norm tends to one -/

/-- **Asymptotic passivity.**  The exact multiplier norm tends to one as the shift tends to
zero. -/
theorem tendsto_suzukiGammaMultiplierNorm :
    Tendsto suzukiGammaMultiplierNorm (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hGamma : ContinuousAt Real.Gamma (1 / 4 : ℝ) := by
    refine (Real.differentiableAt_Gamma ?_).continuousAt
    intro m hcontra
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGpos : (0 : ℝ) < Real.Gamma (1 / 4 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
  have hA : Tendsto (fun ω : ℝ => Real.Gamma (1 / 4 - ω / 2)) (nhds 0)
      (nhds (Real.Gamma (1 / 4 : ℝ))) := by
    have hinner : Tendsto (fun ω : ℝ => 1 / 4 - ω / 2) (nhds 0) (nhds (1 / 4 : ℝ)) := by
      have hcont : Continuous (fun ω : ℝ => 1 / 4 - ω / 2) := by fun_prop
      simpa using hcont.tendsto (0 : ℝ)
    exact hGamma.tendsto.comp hinner
  have hB : Tendsto (fun ω : ℝ => Real.Gamma (1 / 4 + ω / 2)) (nhds 0)
      (nhds (Real.Gamma (1 / 4 : ℝ))) := by
    have hinner : Tendsto (fun ω : ℝ => 1 / 4 + ω / 2) (nhds 0) (nhds (1 / 4 : ℝ)) := by
      have hcont : Continuous (fun ω : ℝ => 1 / 4 + ω / 2) := by fun_prop
      simpa using hcont.tendsto (0 : ℝ)
    exact hGamma.tendsto.comp hinner
  have hpi : Tendsto (fun ω : ℝ => Real.pi ^ ω) (nhds 0) (nhds 1) := by
    have := (Real.continuousAt_const_rpow (a := Real.pi) (b := 0) Real.pi_pos.ne').tendsto
    simpa using this
  have hquot : Tendsto (fun ω : ℝ =>
      Real.pi ^ ω * (Real.Gamma (1 / 4 - ω / 2) / Real.Gamma (1 / 4 + ω / 2)))
      (nhds 0) (nhds 1) := by
    have h := hpi.mul (hA.div hB hGpos.ne')
    rwa [div_self hGpos.ne', mul_one] at h
  exact (hquot.mono_left nhdsWithin_le_nhds).congr fun ω => rfl

/-! ### Plancherel transport and the entrywise energy bound -/

/-- **Plancherel multiplier bound.**  Multiplication by a symbol of norm at most `M` is bounded by
`M` in every `L^p`, in particular in `L²` where it is the Mellin multiplier bound. -/
theorem eLpNorm_mul_le_of_norm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {m f : α → ℂ} {M : ℝ} (hM : 0 ≤ M) (hm : ∀ x, ‖m x‖ ≤ M) (p : ℝ≥0∞) :
    eLpNorm (fun x => m x * f x) p μ ≤ ENNReal.ofReal M * eLpNorm f p μ := by
  have hmono : eLpNorm (fun x => m x * f x) p μ ≤ eLpNorm ((M : ℂ) • f) p μ := by
    refine eLpNorm_mono fun x => ?_
    have hsmul : ((M : ℂ) • f) x = (M : ℂ) * f x := rfl
    rw [hsmul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hm x) (norm_nonneg _)
  rw [eLpNorm_const_smul] at hmono
  refine hmono.trans (le_of_eq ?_)
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]

/-- **Entrywise energy transfer.**  If every entry norm is scaled by at most `M`, the total
relative energy is scaled by at most `M²`. -/
theorem sum_sq_le_of_norm_le {ι : Type*} (s : Finset ι) {u v : ι → ℝ} {M c : ℝ}
    (hc : 0 ≤ c) (hu : ∀ i ∈ s, 0 ≤ u i) (h : ∀ i ∈ s, u i ≤ M * v i) :
    c * ∑ i ∈ s, u i ^ 2 ≤ M ^ 2 * (c * ∑ i ∈ s, v i ^ 2) := by
  have hterm : ∀ i ∈ s, u i ^ 2 ≤ M ^ 2 * v i ^ 2 := by
    intro i hi
    nlinarith [h i hi, hu i hi]
  have hsum : ∑ i ∈ s, u i ^ 2 ≤ ∑ i ∈ s, M ^ 2 * v i ^ 2 :=
    Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hsum hc]

/-- **Contractive insertion.**  Applying any entrywise contraction — in particular an exact Sonin
orthogonal projection — after the Gamma multiplier preserves the completed energy bound. -/
theorem sum_sq_le_of_contraction {ι : Type*} (s : Finset ι) {u w v : ι → ℝ} {M c : ℝ}
    (hc : 0 ≤ c) (hu : ∀ i ∈ s, 0 ≤ u i) (hcontr : ∀ i ∈ s, u i ≤ w i)
    (h : ∀ i ∈ s, w i ≤ M * v i) :
    c * ∑ i ∈ s, u i ^ 2 ≤ M ^ 2 * (c * ∑ i ∈ s, v i ^ 2) :=
  sum_sq_le_of_norm_le s hc hu fun i hi => le_trans (hcontr i hi) (h i hi)

/-! ### The completed four-unit budget -/

/-- The Gamma-completed critical energy bound: the parent four-unit relative clock energy scaled by
the exact multiplier norm. -/
def suzukiGammaCompletedEnergyBound (ω : ℝ) : ℝ :=
  suzukiGammaMultiplierNorm ω ^ 2 * squarefreeMobiusCriticalRelativeClockEnergy (1 + 2 * ω)

/-- **Asymptotic four-unit passivity.**  The Gamma-completed energy bound of the divisor incidence
curvature tends to exactly four: the completion cannot exceed the critical four-unit budget. -/
theorem tendsto_suzukiGammaCompletedEnergyBound :
    Tendsto suzukiGammaCompletedEnergyBound (nhdsWithin 0 (Ioi 0)) (nhds 4) := by
  have hshift : Tendsto (fun ω : ℝ => 1 + 2 * ω) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin 1 (Ioi 1)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous (fun ω : ℝ => 1 + 2 * ω) := by fun_prop
      have h0 : Tendsto (fun ω : ℝ => 1 + 2 * ω) (nhds 0) (nhds 1) := by
        simpa using hcont.tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ω hω
      have : (0 : ℝ) < ω := hω
      simp only [Set.mem_Ioi]
      linarith
  have henergy := tendsto_squarefreeMobiusCriticalRelativeClockEnergy.comp hshift
  have hnorm := (tendsto_suzukiGammaMultiplierNorm.pow 2)
  have h := hnorm.mul henergy
  rw [one_pow, one_mul] at h
  exact h

end

end RHTower
