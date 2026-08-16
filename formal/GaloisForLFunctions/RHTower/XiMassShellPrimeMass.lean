import GaloisForLFunctions.RHTower.XiMassShellAsymptotic
import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO

/-!
# The prime mass of a spacelike shell

The corpus prime number theorem for `θ` with a square-root-logarithmic error gives the plain
relative form `|θ(x) − x| ≤ ε x` eventually.  Applied at the two ends of a shell

`e^{κu} < p ≤ e^{κu+L}`

it produces the lower bound

`∑_{shell} log p = θ(e^{κu+L}) − θ(e^{κu}) ≥ ½(e^L − 1) e^{κu}`

for all large heights: the shell carries a fixed positive proportion of the mass predicted by the
continuum, uniformly in the height.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- **The relative `θ`-form of the prime number theorem.** -/
theorem chebyshevTheta_eventually_relative {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, |Chebyshev.theta x - x| ≤ ε * x := by
  obtain ⟨c, hc0, hO⟩ := RHTower.Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := hO.bound
  have hdecay : Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x))) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
    have h2 : Tendsto (fun x : ℝ => -c * Real.sqrt (Real.log x)) atTop atBot := by
      have h3 := h1.const_mul_atTop hc0
      have h4 : Tendsto (fun x : ℝ => -(c * Real.sqrt (Real.log x))) atTop atBot :=
        tendsto_neg_atTop_atBot.comp h3
      simpa [neg_mul] using h4
    exact Real.tendsto_exp_atBot.comp h2
  have hsmall : ∀ᶠ x : ℝ in atTop, C * Real.exp (-c * Real.sqrt (Real.log x)) ≤ ε := by
    have hlim : Tendsto (fun x : ℝ => C * Real.exp (-c * Real.sqrt (Real.log x))) atTop
        (nhds 0) := by
      simpa using hdecay.const_mul C
    exact hlim.eventually_le_const hε
  filter_upwards [hC, hsmall, eventually_gt_atTop (0 : ℝ)] with x hx hxs hx0
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hx
  have habs : |x * Real.exp (-c * Real.sqrt (Real.log x))|
      = x * Real.exp (-c * Real.sqrt (Real.log x)) := abs_of_pos (by positivity)
  rw [habs] at hx
  have hnorm : |Chebyshev.theta x - x| ≤ C * (x * Real.exp (-c * Real.sqrt (Real.log x))) := hx
  have hstep : C * (x * Real.exp (-c * Real.sqrt (Real.log x))) ≤ ε * x := by
    have := mul_le_mul_of_nonneg_right hxs hx0.le
    nlinarith [this]
  linarith [hnorm, hstep]

/-- The shell prime mass is the difference of the two `θ` values. -/
theorem chebyshevTheta_sub_eq_shellSum {x y : ℝ} (hxy : ⌊x⌋₊ ≤ ⌊y⌋₊) :
    Chebyshev.theta y - Chebyshev.theta x
      = ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.Prime p), Real.log p := by
  classical
  have hunion : Finset.Ioc 0 ⌊x⌋₊ ∪ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ = Finset.Ioc 0 ⌊y⌋₊ :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hxy
  have hdisj : Disjoint (Finset.Ioc 0 ⌊x⌋₊) (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    have h1 := (Finset.mem_Ioc.mp hp).2
    have h2 := (Finset.mem_Ioc.mp hp').1
    omega
  have hfilterdisj : Disjoint ((Finset.Ioc 0 ⌊x⌋₊).filter (fun p => Nat.Prime p))
      ((Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.Prime p)) :=
    Finset.disjoint_filter_filter hdisj
  have hsplit : Chebyshev.theta y
      = Chebyshev.theta x + ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter (fun p => Nat.Prime p),
          Real.log p := by
    rw [Chebyshev.theta, Chebyshev.theta, ← hunion, Finset.filter_union,
      Finset.sum_union hfilterdisj]
  linarith [hsplit]

/-- **(17.21) The shell carries a fixed proportion of the continuum mass.** -/
theorem exists_shell_theta_lower {kappa L : ℝ} (hkappa : 0 < kappa) (hL : 0 < L) :
    ∃ u₀ : ℝ, 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      (1 / 2) * (Real.exp L - 1) * Real.exp (kappa * u)
        ≤ Chebyshev.theta (Real.exp (kappa * u + L))
          - Chebyshev.theta (Real.exp (kappa * u)) := by
  have hexpL : (1 : ℝ) < Real.exp L := Real.one_lt_exp_iff.mpr hL
  obtain ⟨ε, hε0, hεbound⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (Real.exp L + 1) ≤ (1 / 4) * (Real.exp L - 1) :=
    ⟨(1 / 4) * (Real.exp L - 1) / (Real.exp L + 1), by positivity, by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]⟩
  obtain ⟨X, hX⟩ := (chebyshevTheta_eventually_relative hε0).exists_forall_of_atTop
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ u : ℝ, Y ≤ u →
      Real.exp (kappa * u) ≥ max X 1 ∧ (1 : ℝ) ≤ (1 / 4) * (Real.exp L - 1)
        * Real.exp (kappa * u) := by
    have hgrow : Tendsto (fun u : ℝ => Real.exp (kappa * u)) atTop atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      exact Filter.tendsto_id.const_mul_atTop hkappa
    have h1 : ∀ᶠ u : ℝ in atTop, Real.exp (kappa * u) ≥ max X 1 :=
      hgrow.eventually_ge_atTop _
    have h2 : ∀ᶠ u : ℝ in atTop, (1 : ℝ) ≤ (1 / 4) * (Real.exp L - 1) * Real.exp (kappa * u) := by
      have hpos : (0 : ℝ) < (1 / 4) * (Real.exp L - 1) := by
        have : (0 : ℝ) < Real.exp L - 1 := by linarith
        positivity
      have := (hgrow.const_mul_atTop hpos).eventually_ge_atTop (1 : ℝ)
      exact this
    obtain ⟨Y, hYm⟩ := (h1.and h2).exists_forall_of_atTop
    exact ⟨Y, hYm⟩
  refine ⟨max Y 1, le_max_right _ _, fun u hu => ?_⟩
  have huY : Y ≤ u := le_trans (le_max_left _ _) hu
  obtain ⟨hbig, hone⟩ := hY u huY
  have hE : (0 : ℝ) < Real.exp (kappa * u) := Real.exp_pos _
  have hEL : Real.exp (kappa * u + L) = Real.exp (kappa * u) * Real.exp L := by
    rw [Real.exp_add]
  have hX1 : X ≤ Real.exp (kappa * u) := le_trans (le_max_left _ _) hbig
  have hX2 : X ≤ Real.exp (kappa * u + L) := by
    rw [hEL]
    nlinarith [hX1, hE, hexpL]
  have h1 := hX _ hX1
  have h2 := hX _ hX2
  have hlow : Chebyshev.theta (Real.exp (kappa * u + L))
      ≥ (1 - ε) * Real.exp (kappa * u + L) := by
    have := abs_le.1 h2
    linarith [this.1]
  have hup : Chebyshev.theta (Real.exp (kappa * u)) ≤ (1 + ε) * Real.exp (kappa * u) := by
    have := abs_le.1 h1
    linarith [this.2]
  have hgap : (1 - ε) * Real.exp (kappa * u + L) - (1 + ε) * Real.exp (kappa * u)
      ≥ (1 / 2) * (Real.exp L - 1) * Real.exp (kappa * u) := by
    rw [hEL]
    have hkey : Real.exp L - 1 - ε * (Real.exp L + 1) ≥ (1 / 2) * (Real.exp L - 1) := by
      linarith [hεbound]
    nlinarith [hkey, hE]
  linarith [hlow, hup, hgap]

end

end RHTower
