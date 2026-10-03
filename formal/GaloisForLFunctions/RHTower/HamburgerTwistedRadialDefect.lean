import GaloisForLFunctions.RHTower.WeilHerglotzPhaseLockRigidity

/-!
# Phase locks with a radially vanishing defect

The twisted Hamburger theorem and the phase-lock rigidity theorem use the lock defect only through
Hamburger's radial limits `ε J_r(ε + i m) → 0` (`m ∈ ℕ`), where
`J_r(τ) = (1/2π) ∫ r(t) k(2t, τ) dt` is the Laplace transform of the defect kernel.  Abel
sublinearity of `r` is one sufficient condition.  This file states both theorems with the radial
limits themselves as the hypothesis.  The point is that the radial limits are *signed*: they can
vanish through cancellation in `r(t) k(2t, ε + i m)`, which oscillates like `m^{2it}`, when
`δ ∫ ‖r‖ e^{−δ|t|}` does not tend to zero.

* `HamburgerTwisted.coeff_eq_of_critical_line_twisted_radial_defect`: Hamburger's hypotheses, a
  polynomially bounded reflection defect, and `g = (1 − κ⁻¹) Φ + r'` on `t < −Y`, where `r'` has
  vanishing radial limits on `t < −Y`.  Then every coefficient equals `2κβ`.
* `PhaseLockRigidity.phase_lock_rigidity_of_radial_defect`: the Herglotz form of Weil positivity,
  `G` continuous on `Re s ≥ ½` with `G' = ΦG`, and the lock
  `G(1 − s) = κ⁻¹ G(s) + s(s−1)Γ_ℝ(s) e` on the lower critical line with a radially vanishing
  defect `e`.  Then `lam = Λ` and the Riemann hypothesis holds.

The proofs are those of `coeff_eq_of_critical_line_twisted_defect` and
`phase_lock_rigidity_of_defect`, with the Abel step replaced by the hypothesis.
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

namespace HamburgerTwisted

open GaloisForLFunctions.HTGeometry HamburgerStability

noncomputable section

/-- **The twisted Hamburger theorem with a radially vanishing remainder.**  As
`coeff_eq_of_critical_line_twisted_defect`, with the Abel condition on `r'` replaced by the radial
limits `ε J_{r' 1_{t < −Y}}(ε + i m) → 0` for every `m ∈ ℕ`. -/
theorem coeff_eq_of_critical_line_twisted_radial_defect {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g Φ r' : ℝ → ℂ} {CB : ℝ} {N : ℕ}
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
    (hr'm : Measurable r') (hr'b : ∀ t, ‖r' t‖ ≤ CB * (1 + |t|) ^ N)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hr'rad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) *
      defectLaplace ((Iio (-Y)).indicator r') ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0))
    {κ : ℂ} (hκ : κ ≠ 0)
    (hlow : ∀ t, t < -Y → g t = (1 - κ⁻¹) * Φ t + r' t)
    (n : ℕ) : a (n + 1) = 2 * κ * β := by
  have hgm' := hgm.aestronglyMeasurable (μ := volume)
  have hΦm' := hΦm.aestronglyMeasurable (μ := volume)
  have hr'm' := hr'm.aestronglyMeasurable (μ := volume)
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
  -- the defect relation and its Laplace transform
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      1 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel g x := by
    intro x hx
    have h := critical_line_even_theta_relation_defect
      (d := fun s => Complex.Gammaℝ s * g (s.im / 2)) hθc hθm hEc hEd hdecay hR' hC hdint hx
    simp only [him] at h
    unfold defectKernel
    linear_combination h
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_forall_rpow ha
    simpa using this
  set S : ℂ → ℂ := fun τ => ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ))
    with hS
  have hL : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a τ =
      1 * S τ + -β / (Real.pi * τ) + β + defectLaplace g τ := fun τ hτ =>
    hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta
      (fun τ hτ => (defectKernel_laplace hgm hgb hτ).1)
      (differentiableOn_defectLaplace hgm' hgb)
      (fun τ hτ => (defectKernel_laplace hgm hgb hτ).2) hτ
  -- the untwisted identity `L = β + J_Φ`
  have htheta0 : ∀ x : ℝ, 0 < x → coeffTheta a x =
      0 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + 0 + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel Φ x := fun x hx => by
    rw [coeffTheta_eq_defectKernel ha hEc hEd hdecay hR hΦ hx]; ring
  have hL0 : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a τ = β + defectLaplace Φ τ := by
    intro τ hτ
    have h := hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta0
      (fun τ hτ => (defectKernel_laplace hΦm hΦb hτ).1)
      (differentiableOn_defectLaplace hΦm' hΦb)
      (fun τ hτ => (defectKernel_laplace hΦm hΦb hτ).2) hτ
    rw [h]; simp
  -- the pieces
  set U : Set ℝ := Ioi Y with hU
  set Lo : Set ℝ := Iio (-Y) with hLo
  set Mi : Set ℝ := Icc (-Y) Y with hMi
  set K₀ : ℂ → ℂ := fun τ => κ * defectLaplace (U.indicator g) τ -
      (κ - 1) * (defectLaplace (U.indicator Φ) τ + defectLaplace (Mi.indicator Φ) τ) +
      κ * (defectLaplace (Lo.indicator r') τ + defectLaplace (Mi.indicator g) τ) with hK₀
  have hκinv : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  have hmain : ∀ τ : ℂ, 0 < τ.re →
      hamburgerSeries a τ = κ * S τ - κ * β / Real.pi / τ + β + K₀ τ := by
    intro τ hτ
    have eA := hL τ hτ
    have eB := hL0 τ hτ
    have eC := defectLaplace_split hgm' hgb hY hτ
    have eD := defectLaplace_split hΦm' hΦb hY hτ
    have eF := defectLaplace_indicator_eq (g := g) hΦm'
      (fun t => (hΦb t).trans (le_refl _)) hr'm' hr'b measurableSet_Iio (1 - κ⁻¹)
      (fun t ht => hlow t ht) hτ
    have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [hK₀]
    rw [show -β / (Real.pi * τ) = -(β / Real.pi / τ) by field_simp] at eA
    linear_combination κ * eA + κ * eC + κ * eF - (κ - 1) * eB - (κ - 1) * eD -
      defectLaplace (Lo.indicator Φ) τ * hκinv
  have hper : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a (τ + I) - hamburgerSeries a τ =
      -(κ * β / Real.pi) / (τ + I) - -(κ * β / Real.pi) / τ + (K₀ (τ + I) - K₀ τ) := by
    intro τ hτ
    have hτ' : 0 < (τ + I).re := by simpa using hτ
    have hexp : S (τ + I) = S τ := by
      simp only [hS]
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hmain τ hτ, hmain (τ + I) hτ', hexp]
    ring
  -- radial vanishing of every piece of `K₀`
  have hmidΦ := tendsto_mul_abelMass_indicator_Icc hΦm' hΦb Y
  have hmidg := tendsto_mul_abelMass_indicator_Icc hgm' hgb Y
  have hb : ∀ {h : ℝ → ℂ}, (∀ t, ‖h t‖ ≤ CB * (1 + |t|) ^ N) → ∀ s : Set ℝ, ∀ t,
      ‖s.indicator h t‖ ≤ CB * (1 + |t|) ^ N :=
    fun hh s t => (norm_indicator_le_norm_self _ t).trans (hh t)
  have hK₀rad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * K₀ ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
    intro m
    have t0 := tendsto_mul_defectLaplace_upper_radial hgm' hgb hY m
    have t1 := tendsto_mul_defectLaplace_upper_radial hΦm' hΦb hY m
    have t2 := tendsto_mul_defectLaplace_radial (hΦm'.indicator measurableSet_Icc)
      (hb hΦb Mi) hmidΦ m
    have t4 := hr'rad m
    have t5 := tendsto_mul_defectLaplace_radial (hgm'.indicator measurableSet_Icc)
      (hb hgb Mi) hmidg m
    have := ((t0.const_mul κ).sub ((t1.add t2).const_mul (κ - 1))).add
      ((t4.add t5).const_mul κ)
    simp only [mul_zero, sub_zero, add_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    simp only [hK₀]
    ring
  have hK : ∀ n₀ : ℕ, Tendsto (fun τ => (τ - (n₀ : ℂ) * I) * (K₀ (τ + I) - K₀ τ))
      (𝓝[{τ : ℂ | 0 < τ.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
    intro n₀
    refine tendsto_sub_mul_defect_of_radial ha2 (-(κ * β / Real.pi))
      (fun τ => K₀ (τ + I) - K₀ τ) hper n₀ ?_
    have h1 := hK₀rad (n₀ + 1)
    have h0 := hK₀rad n₀
    have := h1.sub h0
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    push_cast
    ring_nf
  have h := coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect ha2 (-(κ * β / Real.pi))
    (fun τ => K₀ (τ + I) - K₀ τ) hper hK n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end

end HamburgerTwisted

namespace PhaseLockRigidity

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity

noncomputable section

/-- **Phase-locked Herglotz producers with a radially vanishing lock defect are `Λ`, and RH
holds.**  As `phase_lock_rigidity_of_defect`, with the Abel condition on `e` replaced by the radial
limits `ε J_{e 1_{t < −Y}}(ε + i m) → 0` for every `m ∈ ℕ`. -/
theorem phase_lock_rigidity_of_radial_defect {lam : ℕ → ℝ} {Φ G : ℂ → ℂ} {e : ℝ → ℂ} {Ce : ℝ} {Nₑ : ℕ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hem : Measurable e) (heb : ∀ t, ‖e t‖ ≤ Ce * (1 + |t|) ^ Nₑ)
    {Y : ℝ} (hY : 0 ≤ Y)
    (heR : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * HamburgerStability.defectLaplace
      ((Iio (-Y)).indicator e) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0))
    {κ : ℂ} (hκ : κ ≠ 0)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) =
      κ⁻¹ * G (lineS τ) + lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) * e τ) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hid' : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable (hLa σ (by simpa using hσ)).1
  obtain ⟨C, hC⟩ := exists_decay_bigEG hsl hΦre hid' hGc hGd hG2
  obtain ⟨CB₀, N₀, hCB₀, hB₀⟩ := exists_poly_bound_lineG hsl hΦre hid' hGc hGd hG2
  have hCe : 0 ≤ Ce := by
    have := (norm_nonneg _).trans (heb 0)
    simpa using this
  set CB := max CB₀ Ce with hCB
  set N := N₀ + Nₑ with hN
  have hpow : ∀ t : ℝ, ∀ k : ℕ, k ≤ N → (1 + |t|) ^ k ≤ (1 + |t|) ^ N := fun t k hk =>
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hk
  have hbound : ∀ {h : ℝ → ℂ} {C₀ : ℝ} {k : ℕ}, k ≤ N → C₀ ≤ CB →
      (∀ t, ‖h t‖ ≤ C₀ * (1 + |t|) ^ k) → ∀ t, ‖h t‖ ≤ CB * (1 + |t|) ^ N := by
    intro h C₀ k hk hC h' t
    have h0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (by simpa using h' 0)
    calc ‖h t‖ ≤ C₀ * (1 + |t|) ^ k := h' t
      _ ≤ CB * (1 + |t|) ^ N := mul_le_mul hC (hpow t k hk) (by positivity)
          (le_trans h0 hC)
  have hdE := differentiableOn_bigEG hGd
  set β := betaG G with hβ
  have hlow : ∀ τ : ℝ, τ < -Y → gG G τ = (1 - κ⁻¹) * phiG G τ + (fun t => -e t) τ := by
    intro τ hτ
    have hD : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
        (Gammaℝ_lineS_ne_zero τ)
    unfold gG phiG
    rw [hlock τ hτ]
    set D := lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) with hDdef
    set X := G (lineS τ)
    show (X - (κ⁻¹ * X + D * e τ)) / D = (1 - κ⁻¹) * (X / D) + -e τ
    field_simp
    ring
  have hrR : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * HamburgerStability.defectLaplace
      ((Iio (-Y)).indicator fun t => -e t) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    intro m
    have h := (heR m).neg
    rw [neg_zero] at h
    refine h.congr fun ε => ?_
    have hind : ((Iio (-Y)).indicator fun t => -e t) = fun t => -((Iio (-Y)).indicator e t) :=
      Set.indicator_neg' _ _
    simp only [HamburgerStability.defectLaplace, hind, neg_mul, integral_neg, mul_neg]
  have hcoef := HamburgerTwisted.coeff_eq_of_critical_line_twisted_radial_defect
    (a := a) ha (E := bigEG G) (β := β) (C := C) (g := gG G)
    (Φ := phiG G) (r' := fun t => -e t) (CB := CB) (N := N)
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
        G_eq_bigG hsl hid' hGd hG2 h1]
      unfold bigG
      field_simp
      ring)
    (fun s hs => bigEG_sub_eq_gG hs)
    (fun τ => bigEG_add_eq_phiG τ)
    (continuous_gG hGc).measurable
    (hbound (k := N₀) (by omega) (le_max_left _ _) (fun t => (hB₀ t).2))
    (continuous_phiG hGc).measurable
    (hbound (k := N₀) (by omega) (le_max_left _ _) (fun t => (hB₀ t).1))
    hem.neg
    (hbound (k := Nₑ) (by omega) (le_max_right _ _) (fun t => by rw [norm_neg]; exact heb t))
    hY hrR hκ hlow
  -- all coefficients equal `a 1 = 1`
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have h2β : 2 * κ * β = 1 := by rw [← hcoef 0, ha1]
  have hall : ∀ {n : ℕ}, n ≠ 0 → a n = (1 : ℕ → ℂ) n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hcoef k, h2β]; rfl
  have hζ : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s := by
    intro s hs
    rw [← (hLa s hs).2, LSeries_congr hall s, LSeries_one_eq_riemannZeta hs]
  have hLam : ∀ s : ℂ, 1 < s.re →
      LSeries (lamTwo lam) s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    intro s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : riemannZeta =ᶠ[𝓝 s] zetaOf lam := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact (hζ z hz).symm
    have hd := (hasDerivAt_zetaOf hsl hs).congr_of_eventuallyEq hev
    have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hd.deriv, hζ s hs]
    field_simp
  have habs1 : LSeries.abscissaOfAbsConv (lamTwo lam) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lseriesSummable_of_le (norm_lamTwo_le lam) hsl (by simpa using hy))
      (EReal.coe_lt_top 1)
  have habs2 :
      LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
      (EReal.coe_lt_top 1)
  have hEv : (fun x : ℝ => LSeries (lamTwo lam) x) =ᶠ[atTop]
      fun x : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hLam x (by simpa using hx)
  refine ⟨fun n hn => ?_, ?_⟩
  · have h := LSeries.eq_of_LSeries_eventually_eq habs1 habs2 hEv (n := n) (by omega)
    simp only [lamTwo, if_pos hn] at h
    exact_mod_cast h
  · by_contra hRH
    obtain ⟨ρ, hρ0, hρ1, hρ2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    set Z : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta₀ s + 1 with hZ
    have hZd : Differentiable ℂ Z := by
      have := differentiable_completedZeta₀
      intro s; simp only [hZ]; fun_prop
    set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hZa : AnalyticOnNhd ℂ Z U := hZd.differentiableOn.analyticOnNhd hUo
    have hGa : AnalyticOnNhd ℂ G U := by
      have : DifferentiableOn ℂ G U := fun z hz =>
        (hGd z hz).differentiableAt.differentiableWithinAt
      exact this.analyticOnNhd hUo
    have hZΛ : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Z s = s * (s - 1) * completedRiemannZeta s := by
      intro s h0 h1
      have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
      simp only [hZ]
      rw [completedRiemannZeta_eq]
      field_simp
      ring
    have hΛζ : ∀ s : ℂ, 0 < s.re → completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      intro s hs
      have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
      rw [riemannZeta_def_of_ne_zero h0]
      field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : G =ᶠ[𝓝 (2 : ℂ)] Z := by
      filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      have hz' : 1 < z.re := hz
      have h0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
      have h1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
      rw [hZΛ z h0 h1, hΛζ z (by linarith), ← hζ z hz', G_eq_bigG hsl hid' hGd hG2 hz']
      unfold bigG; ring
    have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
    have hglob := hGa.eqOn_of_preconnected_of_eventuallyEq hZa
      (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected h2U hev hρ1
    have hρne0 : ρ ≠ 0 := by intro h; rw [h] at hρ1; simp at hρ1; linarith
    have hρne1 : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
    have hzero : G ρ = 0 := by
      rw [hglob, hZΛ ρ hρne0 hρne1, hΛζ ρ (by linarith), hρ0, mul_zero, mul_zero]
    exact G_ne_zero hΦd hGd hG2 hρ1 hzero

end

end PhaseLockRigidity

end RHTower
