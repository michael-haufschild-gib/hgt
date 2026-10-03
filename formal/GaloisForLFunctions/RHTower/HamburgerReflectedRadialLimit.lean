import GaloisForLFunctions.RHTower.HamburgerTwistedRadialDefect

/-!
# The reflected boundary function has the same radial limit at every `m`

Let `f(s) = Σ a_n n^{-s}` satisfy Hamburger's hypotheses with polar coefficient `β`, boundary value
`Φ(t) = f(½ + 2it)` and reflection defect `g`, so that `Φ − g` is the boundary value of the
reflected completed function divided by `Γ_ℝ`.  Write `S(τ) = Σ_n a_n e^{−2πnτ}` and
`J_h(τ) = (1/2π) ∫ h(t) k(2t, τ) dt` for Hamburger's Laplace transform.

**Theorem** (`reflected_laplace_identity`).  `S(τ) − β/(πτ) = J_{Φ−g}(τ)` for `Re τ > 0`.

**Corollary** (`tendsto_reflected_radial`).  `ε J_{Φ−g}(ε + i m) → β/π` for every `m ≥ 1`.

*Proof.*  `S` is `i`-periodic, so `ε S(ε + im) = ε S(ε)`.  At `m = 0` the kernel decays like
`e^{−2|t|}`, so `ε J_{Φ−g}(ε) → 0`, and the identity gives `ε S(ε) → β/π`.

The twisted Hamburger theorem uses this identity through a residue comparison of
`Σ a_n t/(π(n² + t²))`.  Here no residue is needed: the identity says that the reflected boundary
function has one and the same radial limit at every `m`.  For a producer
(`PhaseLockRigidity`), `Φ − g = phiStar G = G(1 − s)/(s(s−1)Γ_ℝ(s))` on the critical line, and
the limit `β/π` is carried by the lower half-line alone (`tendsto_lower_reflected_radial`).
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

namespace HamburgerTwisted

open GaloisForLFunctions.HTGeometry HamburgerStability

noncomputable section

/-- The `i`-periodic theta series `S(τ) = Σ_{n ≥ 1} a_n e^{−2πnτ}`. -/
def thetaLaplace (a : ℕ → ℂ) (τ : ℂ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))

theorem thetaLaplace_add_nat_mul_I (a : ℕ → ℂ) (τ : ℂ) (m : ℕ) :
    thetaLaplace a (τ + (m : ℂ) * I) = thetaLaplace a τ := by
  unfold thetaLaplace
  refine tsum_congr fun n => ?_
  rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + (m : ℂ) * I)) =
    -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-(((n : ℤ) + 1) * m) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `ε J_h(ε) → 0` for every polynomially bounded `h`: on the real axis the kernel decays like
`e^{−2|t|}`. -/
theorem tendsto_mul_defectLaplace_real {h : ℝ → ℂ} {Ch : ℝ} {N : ℕ}
    (hhm : AEStronglyMeasurable h volume) (hhb : ∀ t, ‖h t‖ ≤ Ch * (1 + |t|) ^ N) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace h (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  refine squeeze_zero_norm'
    (a := fun ε : ℝ => 3 / (2 * Real.pi) * abelMass h (2 * 1) * ε ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hre : 0 < ((ε : ℂ)).re := by simpa using hε'
    have hb := norm_defectLaplace_le hhm hhb hre
    have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
    rw [hn, Complex.ofReal_re, div_self hε'.ne'] at hb
    rw [norm_mul, hn]
    have e : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hε'.le (by norm_num)]; norm_num
    calc ε * ‖defectLaplace h ε‖
        ≤ ε * (3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * abelMass h (2 * 1)) := by gcongr
      _ = 3 / (2 * Real.pi) * abelMass h (2 * 1) * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
      _ = 3 / (2 * Real.pi) * abelMass h (2 * 1) * ε ^ (1 / 2 : ℝ) := by rw [e]
  · have hr := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
    rw [Real.zero_rpow (by norm_num)] at hr
    simpa using (hr.mono_left nhdsWithin_le_nhds).const_mul
      (3 / (2 * Real.pi) * abelMass h (2 * 1))

/-- **The reflected Laplace identity** `S(τ) − β/(πτ) = J_Φ(τ) − J_g(τ)` on `Re τ > 0`. -/
theorem reflected_laplace_identity {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g Φ : ℝ → ℂ} {CB : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * coeffDirichlet a s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hΦ : ∀ t : ℝ, E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) +
      β * Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) =
        Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * Φ t)
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ CB * (1 + |t|) ^ N)
    (hΦm : Measurable Φ) (hΦb : ∀ t, ‖Φ t‖ ≤ CB * (1 + |t|) ^ N)
    {τ : ℂ} (hτ : 0 < τ.re) :
    thetaLaplace a τ - β / (Real.pi * τ) = defectLaplace Φ τ - defectLaplace g τ := by
  have hgm' := hgm.aestronglyMeasurable (μ := volume)
  have hΦm' := hΦm.aestronglyMeasurable (μ := volume)
  have hθc : ContinuousOn (coeffTheta a) (Ioi 0) := continuousOn_coeffTheta a (ha 2 (by norm_num))
  have hθm : MellinConvergent (coeffTheta a) (3 / 4) :=
    mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (coeffTheta a) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]
    exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact integrable_Gammaℝ_mul hgm' hgb
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      1 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel g x := by
    intro x hx
    have h := critical_line_even_theta_relation_defect
      (d := fun s => Complex.Gammaℝ s * g (s.im / 2)) hθc hθm hEc hEd hdecay hR' hC hdint hx
    simp only [him] at h
    unfold defectKernel
    linear_combination h
  have hL := hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta
    (fun τ hτ => (defectKernel_laplace hgm hgb hτ).1)
    (differentiableOn_defectLaplace hgm' hgb)
    (fun τ hτ => (defectKernel_laplace hgm hgb hτ).2) hτ
  have htheta0 : ∀ x : ℝ, 0 < x → coeffTheta a x =
      0 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + 0 + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel Φ x := fun x hx => by
    rw [coeffTheta_eq_defectKernel ha hEc hEd hdecay hR hΦ hx]; ring
  have hL0 := hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta0
    (fun τ hτ => (defectKernel_laplace hΦm hΦb hτ).1)
    (differentiableOn_defectLaplace hΦm' hΦb)
    (fun τ hτ => (defectKernel_laplace hΦm hΦb hτ).2) hτ
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold thetaLaplace
  have e : -β / (Real.pi * τ) = -(β / (Real.pi * τ)) := by ring
  rw [e] at hL
  simp only [zero_mul, zero_add, one_mul] at hL hL0
  linear_combination hL0 - hL

/-- **The reflected radial limit.**  Under Hamburger's hypotheses,
`ε (J_Φ − J_g)(ε + i m) → β/π` for every `m ≥ 1`. -/
theorem tendsto_reflected_radial {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g Φ : ℝ → ℂ} {CB : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * coeffDirichlet a s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hΦ : ∀ t : ℝ, E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) +
      β * Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) =
        Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * Φ t)
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ CB * (1 + |t|) ^ N)
    (hΦm : Measurable Φ) (hΦb : ∀ t, ‖Φ t‖ ≤ CB * (1 + |t|) ^ N) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * (defectLaplace Φ ((ε : ℂ) + (m : ℂ) * I) -
      defectLaplace g ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0) (𝓝 (β / Real.pi)) := by
  have hpi := Real.pi_pos
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hid := fun {τ : ℂ} (hτ : 0 < τ.re) =>
    reflected_laplace_identity ha hEc hEd hdecay hR hC hΦ hgm hgb hΦm hΦb hτ
  -- `ε S(ε) → β/π`
  have h0 : Tendsto (fun ε : ℝ => (ε : ℂ) * (defectLaplace Φ (ε : ℂ) - defectLaplace g (ε : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := tendsto_mul_defectLaplace_real hΦm.aestronglyMeasurable hΦb
    have h2 := tendsto_mul_defectLaplace_real hgm.aestronglyMeasurable hgb
    simpa [mul_sub] using h1.sub h2
  have hS : Tendsto (fun ε : ℝ => (ε : ℂ) * thetaLaplace a (ε : ℂ)) (𝓝[>] 0)
      (𝓝 (β / Real.pi)) := by
    have hc : Tendsto (fun _ : ℝ => β / (Real.pi : ℂ)) (𝓝[>] 0) (𝓝 (β / Real.pi)) :=
      tendsto_const_nhds
    have := h0.add hc
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hre : 0 < ((ε : ℂ)).re := by simpa using hε'
    have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε'.ne'
    rw [← hid hre]
    field_simp
    ring
  -- transport to `ε + i m`
  have hre : ∀ ε : ℝ, 0 < ε → 0 < ((ε : ℂ) + (m : ℂ) * I).re := fun ε hε => by simp [hε]
  have hpole : Tendsto (fun ε : ℝ => (ε : ℂ) * (β / (Real.pi * ((ε : ℂ) + (m : ℂ) * I))))
      (𝓝[>] 0) (𝓝 0) := by
    have hm0 : ((Real.pi : ℂ) * ((0 : ℂ) + (m : ℂ) * I)) ≠ 0 := by
      have : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      simp [hπ, this, Complex.I_ne_zero]
    have hcont : ContinuousAt (fun x : ℝ => (x : ℂ) * (β / (Real.pi * ((x : ℂ) + (m : ℂ) * I))))
        0 := by
      refine Complex.continuous_ofReal.continuousAt.mul (continuousAt_const.div ?_ ?_)
      · exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.add continuousAt_const)
      · simpa using hm0
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have := hS.sub hpole
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have e := hid (hre ε hε')
  rw [thetaLaplace_add_nat_mul_I a (ε : ℂ) m] at e
  show (ε : ℂ) * thetaLaplace a ε - (ε : ℂ) * (β / (Real.pi * ((ε : ℂ) + (m : ℂ) * I))) =
    (ε : ℂ) * (defectLaplace Φ ((ε : ℂ) + (m : ℂ) * I) - defectLaplace g ((ε : ℂ) + (m : ℂ) * I))
  rw [← e]; ring

end

end HamburgerTwisted

namespace PhaseLockRigidity

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  HamburgerStability HamburgerTwisted

noncomputable section

/-- The reflected boundary value `G(1 − s)/(s(s−1)Γ_ℝ(s))` at `s = ½ + 2iτ`. -/
def phiStar (G : ℂ → ℂ) (τ : ℝ) : ℂ :=
  G (1 - lineS τ) / (lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ))

theorem phiG_sub_gG (G : ℂ → ℂ) (τ : ℝ) : phiG G τ - gG G τ = phiStar G τ := by
  unfold phiG gG phiStar; ring

/-- **The lower reflected radial limit of a producer.**  For a Herglotz producer, the reflected
boundary value on the lower half-line has `ε J(ε + i m) → β/π` for every `m ≥ 1`, with
`β = G(1)/2`. -/
theorem tendsto_lower_reflected_radial {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (phiStar G))
      ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 (betaG G / Real.pi)) := by
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable (hLa σ (by simpa using hσ)).1
  obtain ⟨C, hC⟩ := exists_decay_bigEG hsl hΦre hid hGc hGd hG2
  obtain ⟨CB, N, hCB, hB⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hdE := differentiableOn_bigEG hGd
  have hrad := tendsto_reflected_radial (a := a) ha (E := bigEG G) (β := betaG G) (C := C)
    (g := gG G) (Φ := phiG G) (CB := CB) (N := N)
    (fun z hz => by
      rw [mem_verticalStrip] at hz
      exact (continuousAt_bigEG hGc hGd hz.1).continuousWithinAt)
    (hdE.mono fun z hz => by show (1 / 2 : ℝ) < z.re; exact hz.1)
    hC
    (fun s hs => by
      have h1 : 1 < s.re := by rw [hs]; norm_num
      have h0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
      have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [coeffDirichlet_eq_LSeries, (hLa s h1).2, bigEG_eq h0 hs1,
        G_eq_bigG hsl hid hGd hG2 h1]
      unfold bigG
      field_simp
      ring)
    (fun s hs => bigEG_sub_eq_gG hs)
    (fun τ => bigEG_add_eq_phiG τ)
    (continuous_gG hGc).measurable (fun t => (hB t).2)
    (continuous_phiG hGc).measurable (fun t => (hB t).1) hm
  -- `J_Φ − J_g = J_{phiStar}`
  have hsc : Continuous (phiStar G) := by
    have : phiStar G = fun τ => phiG G τ - gG G τ := by funext τ; rw [phiG_sub_gG]
    rw [this]; exact (continuous_phiG hGc).sub (continuous_gG hGc)
  have hsb : ∀ t, ‖phiStar G t‖ ≤ (2 * CB) * (1 + |t|) ^ N := by
    intro t
    rw [← phiG_sub_gG]
    calc ‖phiG G t - gG G t‖ ≤ ‖phiG G t‖ + ‖gG G t‖ := norm_sub_le _ _
      _ ≤ CB * (1 + |t|) ^ N + CB * (1 + |t|) ^ N := add_le_add (hB t).1 (hB t).2
      _ = 2 * CB * (1 + |t|) ^ N := by ring
  have hsub : ∀ τ : ℂ, 0 < τ.re →
      defectLaplace (phiG G) τ - defectLaplace (gG G) τ = defectLaplace (phiStar G) τ := by
    intro τ hτ
    have i1 := integrable_defectLaplace_integrand (continuous_phiG hGc).aestronglyMeasurable
      (fun t => (hB t).1) hτ
    have i2 := integrable_defectLaplace_integrand (continuous_gG hGc).aestronglyMeasurable
      (fun t => (hB t).2) hτ
    unfold defectLaplace
    rw [← mul_sub, ← integral_sub i1 i2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [← phiG_sub_gG]
    ring
  -- split off the upper and middle pieces
  have hsm := hsc.aestronglyMeasurable (μ := volume)
  have hup := tendsto_mul_defectLaplace_upper_radial hsm hsb (le_refl (0 : ℝ)) m
  have hmid := tendsto_mul_defectLaplace_radial (hsm.indicator measurableSet_Icc)
    (fun t => (norm_indicator_le_norm_self _ t).trans (hsb t))
    (tendsto_mul_abelMass_indicator_Icc hsm hsb 0) m
  have hall := (hrad.sub hup).sub hmid
  rw [sub_zero, sub_zero] at hall
  refine hall.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hre : 0 < ((ε : ℂ) + (m : ℂ) * I).re := by simp [show (0 : ℝ) < ε from hε]
  rw [hsub _ hre, defectLaplace_split hsm hsb (le_refl (0 : ℝ)) hre, neg_zero]
  ring

end

end PhaseLockRigidity

end RHTower
