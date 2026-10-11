import GaloisForLFunctions.RHTower.DegreeThreeFiniteDeficitConverse

/-!
# Every non-`ζ³` cubic datum loses `ξ` multiplicity at infinitely many points

For an odd cubic datum the Maass function `u` of `g ⋆ μ` is `1`-periodic and satisfies
`u(z) + u(−1/z) = W(z)`, where `W` is the finite polar packet produced by the deficit divisor.
Then `2u(z) = W(z) + W(z + 1) − W(z/(z + 1))`, and periodicity of `u` gives the packet identity

  `W(z + 2) − W(z) = W((z + 1)/(z + 2)) − W(z/(z + 1))`   (`oddInversion_packet_identity`).

Its boundary form is `f(x + 2) − f(x) = f((x+1)/(x+2))/(x + 2) − f(x/(x+1))/(x + 1)` for the
boundary polynomial sum `f(x) = Σ_ρ R_ρ(log x) x^{−ρ}`.  The right side is `O(x^{−2})`, so
telescoping and `f → 0` give `f(x) = O(1/x)`.  Hence `Σ_ρ R_ρ(t) e^{(1−ρ)t}` is bounded on
`t ≥ 0`, and since `0 < Re(1 − ρ)` every `R_ρ` vanishes
(`finitePoleBoundary_eq_zero_of_oddPeriod`).  An empty packet means full `ξ` divisibility, which
forces the sign `+1`.  So odd data always have infinitely many deficits
(`degreeThree_odd_infiniteDeficits`), and with the even case every cubic datum is either
`g(1)ζ³` or has infinitely many deficits (`degreeThree_eq_zetaCube_or_infiniteDeficits`).
-/

noncomputable section

open Set Complex Filter Topology Polynomial

namespace RHTower.WeilHigherDenominator

open MaassBesselSeries

/-! ## The odd packet identity in the upper half-plane -/

private lemma frac_eq_one_add_invS {z : ℂ} (_hz1 : z + 1 ≠ 0) :
    z / (z + 1) = 1 + invS (z + 1) := by
  dsimp [invS]
  field_simp
  ring

private lemma invS_frac {z : ℂ} (hz : z ≠ 0) :
    invS (z / (z + 1)) = invS z - 1 := by
  dsimp [invS]
  field_simp
  ring

private lemma frac_im {z : ℂ} (hz1 : z + 1 ≠ 0) :
    (z / (z + 1)).im = z.im / normSq (z + 1) := by
  rw [frac_eq_one_add_invS hz1, add_im, one_im, zero_add, invS_im]
  simp

private lemma add_one_ne_zero_of_im {z : ℂ} (hz : 0 < z.im) : z + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The doubled odd Maass function is an explicit combination of the packet. -/
private lemma two_mul_odd_eq {u W : ℂ → ℂ} (hper : ∀ z, u (z + 1) = u z)
    (hodd : ∀ z : ℂ, 0 < z.im → u z + u (invS z) = W z) {z : ℂ} (hz : 0 < z.im) :
    2 * u z = W z + W (z + 1) - W (z / (z + 1)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz1 := add_one_ne_zero_of_im hz
  have hz1im : 0 < (z + 1).im := by simpa using hz
  have hfim : 0 < (z / (z + 1)).im := by
    rw [frac_im hz1]
    exact div_pos hz (Complex.normSq_pos.mpr hz1)
  have h1 := hodd z hz
  have h2 := hodd (z + 1) hz1im
  have h3 := hodd (z / (z + 1)) hfim
  rw [hper] at h2
  have e1 : u (z / (z + 1)) = u (invS (z + 1)) := by
    rw [frac_eq_one_add_invS hz1, add_comm, hper]
  have e2 : u (invS (z / (z + 1))) = u (invS z) := by
    rw [invS_frac hz0, ← hper (invS z - 1), sub_add_cancel]
  rw [e1, e2] at h3
  linear_combination h1 + h2 - h3

/-- **The odd packet identity.** -/
theorem oddInversion_packet_identity {u W : ℂ → ℂ} (hper : ∀ z, u (z + 1) = u z)
    (hodd : ∀ z : ℂ, 0 < z.im → u z + u (invS z) = W z) {z : ℂ} (hz : 0 < z.im) :
    W (z + 2) - W z = W ((z + 1) / (z + 2)) - W (z / (z + 1)) := by
  have hz1im : 0 < (z + 1).im := by simpa using hz
  have ha := two_mul_odd_eq hper hodd hz
  have hb := two_mul_odd_eq hper hodd hz1im
  rw [hper] at hb
  have e : z + 1 + 1 = z + 2 := by ring
  rw [e] at hb
  linear_combination ha - hb

/-! ## The boundary identity -/

private lemma boundaryLine_tendsto' (x : ℝ) :
    Tendsto (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  have hy : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hy.mul_const I)

/-- Boundary limit of the packet along the fractional path `z ↦ (z + c)/(z + c + 1)`. -/
private lemma packet_frac_limit (Z : Finset ℂ) (R : ℂ → ℂ[X])
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1) {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) :
    Tendsto (fun y : ℝ => (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ)
        (((x : ℂ) + (y : ℂ) * I + (c : ℂ)) / ((x : ℂ) + (y : ℂ) * I + (c : ℂ) + 1))) /
        ((Real.sqrt y : ℂ) * (Real.log y : ℂ))) (𝓝[>] 0)
      (𝓝 ((-2 * finitePoleBoundary Z id R ((x + c) / (x + c + 1))) /
        ((x + c + 1 : ℝ) : ℂ))) := by
  let w : ℝ → ℂ := fun y => (x : ℂ) + (y : ℂ) * I + (c : ℂ)
  have hw : Tendsto w (𝓝[>] 0) (𝓝 ((x + c : ℝ) : ℂ)) := by
    have := (boundaryLine_tendsto' x).add_const (c : ℂ)
    simpa [w] using this
  have hxc : 0 < x + c := by linarith
  have hxc1 : 0 < x + c + 1 := by linarith
  have hxc1c : ((x + c : ℝ) : ℂ) + 1 ≠ 0 := by exact_mod_cast hxc1.ne'
  have hw1 (y : ℝ) : w y + 1 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp [w] at this
    linarith
  have hf := hw.div (hw.add_const 1) hxc1c
  have hfre : Tendsto (fun y => (w y / (w y + 1)).re) (𝓝[>] 0)
      (𝓝 ((x + c) / (x + c + 1))) := by
    convert continuous_re.continuousAt.tendsto.comp hf using 1 <;>
      simp [Function.comp_def, ← ofReal_one, ← ofReal_add, ← ofReal_div]
  have hd : Tendsto (fun y => normSq (w y + 1)) (𝓝[>] 0) (𝓝 ((x + c + 1) ^ 2)) := by
    have hh := continuous_normSq.continuousAt.tendsto.comp (hw.add_const 1)
    convert hh using 1 <;> simp [w, Function.comp_def, normSq_apply, pow_two]
  have hlim := poissonPacket_boundary_path Z R hstrip (div_pos hxc hxc1)
    (sq_pos_of_pos hxc1) hfre
    (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)) hd
    (Eventually.of_forall fun y => by rw [frac_im (hw1 y)]; simp [w])
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hxc1] at hlim
  exact hlim

/-- The odd packet identity transports to its weight-one boundary form. -/
theorem poissonPacket_boundary_oddPeriod (Z : Finset ℂ) (R : ℂ → ℂ[X])
    (hstrip : ∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1)
    (hrel : ∀ z : ℂ, 0 < z.im →
      (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z + 2)) -
          ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z =
        (∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) ((z + 1) / (z + 2))) -
          ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) (z / (z + 1))) :
    ∀ x > 0, finitePoleBoundary Z id R (x + 2) - finitePoleBoundary Z id R x =
      finitePoleBoundary Z id R ((x + 1) / (x + 2)) / ((x + 2 : ℝ) : ℂ) -
        finitePoleBoundary Z id R (x / (x + 1)) / ((x + 1 : ℝ) : ℂ) := by
  intro x hx
  set W : ℂ → ℂ := fun z => ∑ ρ ∈ Z, polynomialPolarMode ρ (R ρ) z with hW
  have hz := boundaryLine_tendsto' x
  have hpath (c : ℝ) (hc : 0 < x + c) := poissonPacket_boundary_path
    (z := fun y : ℝ => (x : ℂ) + (y : ℂ) * I + (c : ℂ))
    (d := fun _ => 1) Z R hstrip hc zero_lt_one
    (by simpa only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one,
      sub_zero, add_zero, Function.comp_def] using
      continuous_re.continuousAt.tendsto.comp (hz.add_const (c : ℂ)))
    (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝[>] 0)) tendsto_const_nhds
    (Eventually.of_forall fun y => by simp)
  have h2 := hpath 2 (by linarith)
  have h0 := hpath 0 (by linarith)
  have hf0 := packet_frac_limit Z R hstrip hx le_rfl
  have hf1 := packet_frac_limit Z R hstrip hx zero_le_one
  have hL := h2.sub h0
  have hR := hf1.sub hf0
  have hlim := tendsto_nhds_unique hL (hR.congr' (by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    have hzy : 0 < ((x : ℂ) + (y : ℂ) * I).im := by simpa using hy
    have e1 : ((x : ℂ) + (y : ℂ) * I + ((1 : ℝ) : ℂ)) /
        ((x : ℂ) + (y : ℂ) * I + ((1 : ℝ) : ℂ) + 1) =
        ((x : ℂ) + (y : ℂ) * I + 1) / ((x : ℂ) + (y : ℂ) * I + 2) := by push_cast; ring
    have e2 : (x : ℂ) + (y : ℂ) * I + ((2 : ℝ) : ℂ) = (x : ℂ) + (y : ℂ) * I + 2 := by push_cast; ring
    have e3 : (x : ℂ) + (y : ℂ) * I + ((0 : ℝ) : ℂ) = (x : ℂ) + (y : ℂ) * I := by push_cast; ring
    simp only [e1, e2, e3, id]
    rw [div_sub_div_same, div_sub_div_same, hrel _ hzy]))
  simp only [Real.sqrt_one, ofReal_one, div_one, add_zero,
    show (x + 1 + 1 : ℝ) = x + 2 by ring] at hlim
  linear_combination hlim / (-2 : ℂ)

/-! ## The real-variable rigidity -/

/-- Telescoped tail bound used in the odd period argument. -/
private lemma inv_sq_le_telescope {y : ℝ} (hy : 1 ≤ y) :
    1 / y ^ 2 ≤ 3 / 2 * (1 / y - 1 / (y + 2)) := by
  have hy0 : 0 < y := by linarith
  rw [div_sub_div _ _ hy0.ne' (by linarith : y + 2 ≠ 0), div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- **No finite polar packet satisfies the odd period identity.** -/
theorem finitePoleBoundary_eq_zero_of_oddPeriod {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (ρ : ι → ℂ) (hinj : Set.InjOn ρ ↑S)
    (hρ : ∀ i ∈ S, 0 < (ρ i).re ∧ (ρ i).re < 1) (p : ι → Polynomial ℂ)
    (hrel : ∀ x > 0, finitePoleBoundary S ρ p (x + 2) - finitePoleBoundary S ρ p x =
      finitePoleBoundary S ρ p ((x + 1) / (x + 2)) / ((x + 2 : ℝ) : ℂ) -
        finitePoleBoundary S ρ p (x / (x + 1)) / ((x + 1 : ℝ) : ℂ)) :
    ∀ i ∈ S, p i = 0 := by
  set f := finitePoleBoundary S ρ p with hfdef
  have hreg := finitePoleBoundary_contDiffOn S ρ p
  have hsub : Icc (1 / 2 : ℝ) 1 ⊆ Ioi 0 := fun t ht => by
    change 0 < t
    linarith [ht.1]
  -- bounds for `f` and `f'` on `[1/2, 1]`
  have hcont := hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.mono hsub)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hreg.continuousOn.mono hsub)
  set L := max D 0 with hL
  set M' := max M 0 with hM'
  have hL0 : 0 ≤ L := le_max_right _ _
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hdiff : ∀ t ∈ Icc (1 / 2 : ℝ) 1, DifferentiableAt ℝ f t := fun t ht =>
    ((hreg t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt
      (by decide)
  have hlip : ∀ a ∈ Icc (1 / 2 : ℝ) 1, ∀ b ∈ Icc (1 / 2 : ℝ) 1, ‖f a - f b‖ ≤ L * |a - b| :=
    fun a ha b hb => by
      have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff
        (fun t ht => (hD t ht).trans (le_max_left D 0)) (convex_Icc (1 / 2 : ℝ) 1) hb ha
      simpa [Real.norm_eq_abs] using this
  have hfM : ∀ a ∈ Icc (1 / 2 : ℝ) 1, ‖f a‖ ≤ M' := fun a ha => (hM a ha).trans (le_max_left _ _)
  -- the right side is `O(y^{-2})`
  set K := L + M' with hK
  have hR : ∀ y : ℝ, 1 ≤ y → ‖f (y + 2) - f y‖ ≤ K / y ^ 2 := by
    intro y hy
    have hy0 : 0 < y := by linarith
    rw [hrel y hy0]
    have ha : (y + 1) / (y + 2) ∈ Icc (1 / 2 : ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by linarith)]; linarith
      · rw [div_le_one (by linarith)]; linarith
    have hb : y / (y + 1) ∈ Icc (1 / 2 : ℝ) 1 := by
      constructor
      · rw [le_div_iff₀ (by linarith)]; linarith
      · rw [div_le_one (by linarith)]; linarith
    have hab : |(y + 1) / (y + 2) - y / (y + 1)| = 1 / ((y + 1) * (y + 2)) := by
      rw [div_sub_div _ _ (by linarith : y + 2 ≠ 0) (by linarith : y + 1 ≠ 0)]
      rw [abs_of_pos (by apply div_pos <;> nlinarith)]
      field_simp
      ring
    have hsplit : f ((y + 1) / (y + 2)) / ((y + 2 : ℝ) : ℂ) - f (y / (y + 1)) / ((y + 1 : ℝ) : ℂ) =
        (f ((y + 1) / (y + 2)) - f (y / (y + 1))) / ((y + 2 : ℝ) : ℂ) +
          f (y / (y + 1)) * (1 / ((y + 2 : ℝ) : ℂ) - 1 / ((y + 1 : ℝ) : ℂ)) := by
      ring
    have hr : (1 / (y + 2) - 1 / (y + 1) : ℝ) = (-1) / ((y + 1) * (y + 2)) := by
      field_simp
      ring
    have hdiffc : (1 / ((y + 2 : ℝ) : ℂ) - 1 / ((y + 1 : ℝ) : ℂ)) =
        (((-1) / ((y + 1) * (y + 2)) : ℝ) : ℂ) := by
      rw [← hr]
      push_cast
      ring
    rw [hsplit, hdiffc]
    have hy1 : 0 < y + 1 := by linarith
    have hy2 : 0 < y + 2 := by linarith
    calc ‖(f ((y + 1) / (y + 2)) - f (y / (y + 1))) / ((y + 2 : ℝ) : ℂ) +
          f (y / (y + 1)) * (((-1) / ((y + 1) * (y + 2)) : ℝ) : ℂ)‖
        ≤ ‖f ((y + 1) / (y + 2)) - f (y / (y + 1))‖ / (y + 2) +
            ‖f (y / (y + 1))‖ * (1 / ((y + 1) * (y + 2))) := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hy2, abs_div, abs_neg, abs_one,
            abs_of_pos (mul_pos hy1 hy2)]
      _ ≤ L * (1 / ((y + 1) * (y + 2))) / (y + 2) + M' * (1 / ((y + 1) * (y + 2))) := by
          gcongr
          · rw [← hab]; exact hlip _ ha _ hb
          · exact hfM _ hb
      _ ≤ K / y ^ 2 := by
          rw [hK]
          have h1 : 1 / ((y + 1) * (y + 2)) ≤ 1 / y ^ 2 := by
            apply one_div_le_one_div_of_le (by positivity); nlinarith
          have h2 : L * (1 / ((y + 1) * (y + 2))) / (y + 2) ≤ L * (1 / y ^ 2) := by
            rw [div_le_iff₀ hy2]
            calc L * (1 / ((y + 1) * (y + 2))) ≤ L * (1 / y ^ 2) :=
                  mul_le_mul_of_nonneg_left h1 hL0
              _ ≤ L * (1 / y ^ 2) * (y + 2) := by
                  have : 0 ≤ L * (1 / y ^ 2) := by positivity
                  nlinarith
          have h3 : M' * (1 / ((y + 1) * (y + 2))) ≤ M' * (1 / y ^ 2) :=
            mul_le_mul_of_nonneg_left h1 hM0
          have : (L + M') / y ^ 2 = L * (1 / y ^ 2) + M' * (1 / y ^ 2) := by ring
          linarith
  -- telescoping: `‖f x − f (x + 2N)‖ ≤ (3/2) K (1/x − 1/(x + 2N))`
  have htel : ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ,
      ‖f x - f (x + 2 * N)‖ ≤ 3 / 2 * K * (1 / x - 1 / (x + 2 * N)) := by
    intro x hx N
    induction N with
    | zero => simp
    | succ N ih =>
      have hxN : 1 ≤ x + 2 * N := by
        have : (0 : ℝ) ≤ 2 * N := by positivity
        linarith
      have hstep := hR (x + 2 * N) hxN
      have htele := inv_sq_le_telescope hxN
      have hK0 : 0 ≤ K := by positivity
      have e : x + 2 * ((N + 1 : ℕ) : ℝ) = x + 2 * N + 2 := by push_cast; ring
      rw [e]
      calc ‖f x - f (x + 2 * N + 2)‖
          ≤ ‖f x - f (x + 2 * N)‖ + ‖f (x + 2 * N + 2) - f (x + 2 * N)‖ := by
            have := norm_sub_le (f x - f (x + 2 * N)) (f (x + 2 * N + 2) - f (x + 2 * N))
            simpa using this
        _ ≤ 3 / 2 * K * (1 / x - 1 / (x + 2 * N)) + K / (x + 2 * N) ^ 2 := add_le_add ih hstep
        _ ≤ 3 / 2 * K * (1 / x - 1 / (x + 2 * N + 2)) := by
            have : K / (x + 2 * N) ^ 2 = K * (1 / (x + 2 * N) ^ 2) := by ring
            rw [this]
            have := mul_le_mul_of_nonneg_left htele hK0
            nlinarith
  -- `f x = O(1/x)`
  have hdecay := finitePoleBoundary_tendsto_zero S ρ (fun i hi => (hρ i hi).1) p
  have hbound : ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ 3 / 2 * K / x := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hseq : Tendsto (fun N : ℕ => x + 2 * (N : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ x
        (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
    have hlim : Tendsto (fun N : ℕ => ‖f (x + 2 * N)‖ + 3 / 2 * K * (1 / x)) atTop
        (𝓝 (0 + 3 / 2 * K * (1 / x))) := by
      have := (continuous_norm.tendsto 0).comp (hdecay.comp hseq)
      simpa using this.add_const (3 / 2 * K * (1 / x))
    rw [zero_add] at hlim
    rw [show 3 / 2 * K / x = 3 / 2 * K * (1 / x) by ring]
    refine ge_of_tendsto' hlim fun N => ?_
    have h1 := htel x hx N
    have h2 : 3 / 2 * K * (1 / x - 1 / (x + 2 * N)) ≤ 3 / 2 * K * (1 / x) := by
      have : 0 ≤ 1 / (x + 2 * (N : ℝ)) := by positivity
      have hK0 : 0 ≤ 3 / 2 * K := by positivity
      nlinarith
    calc ‖f x‖ ≤ ‖f (x + 2 * N)‖ + ‖f x - f (x + 2 * N)‖ := by
          have := norm_add_le (f (x + 2 * N)) (f x - f (x + 2 * N))
          simpa using this
      _ ≤ ‖f (x + 2 * N)‖ + 3 / 2 * K * (1 / x) := by linarith
  -- the shifted exponential polynomial is bounded
  have hzero := exponential_polynomial_eq_zero_of_bounded (fun i => 1 - ρ i) S
    (fun i hi j hj h => hinj hi hj (by linear_combination -h))
    (fun i hi => by simpa using (hρ i hi).2) p ⟨3 / 2 * K, fun t ht => ?_⟩
  · exact hzero
  · have hx : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
    have hb := hbound (Real.exp t) hx
    have he : ∑ i ∈ S, (p i).eval (t : ℂ) * Complex.exp ((1 - ρ i) * (t : ℂ)) =
        (Real.exp t : ℂ) * f (Real.exp t) := by
      rw [hfdef, finitePoleBoundary, Real.log_exp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ofReal_exp, sub_mul, one_mul, Complex.exp_sub,
        show -ρ i * (t : ℂ) = -(ρ i * (t : ℂ)) by ring, Complex.exp_neg, div_eq_mul_inv]
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    have hpos := Real.exp_pos t
    calc Real.exp t * ‖f (Real.exp t)‖ ≤ Real.exp t * (3 / 2 * K / Real.exp t) :=
          mul_le_mul_of_nonneg_left hb hpos.le
      _ = 3 / 2 * K := by field_simp

/-! ## The cubic consequence -/

/-- **Odd cubic data lose `ξ` multiplicity at infinitely many points.** -/
theorem degreeThree_odd_infiniteDeficits {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hodd : ∀ s, E (1 - s) = -E s) :
    (xiDeficitSupport E).Infinite := by
  classical
  rcases degreeThree_infiniteDeficits_or_spatialDefect hD hE1 with hi |
    ⟨P, H, ε, R, hm, _, he, ho, _, _, _, _, hs, hpacket⟩
  · exact hi
  · exfalso
    have hε : ε = -1 := by
      apply mul_right_cancel₀ hE1
      rw [← he 1, hodd 1]
      ring
    subst hε
    set u := maassFun (degreeTwoQuotientCoeff g) (-1 * degreeTwoEndpointNumerator E 1)
      (-1 * deriv (degreeTwoEndpointNumerator E) 1) with hu
    have hper : ∀ z, u (z + 1) = u z := fun z => maassFun_add_one _ _ z
    have hoddrel : ∀ z : ℂ, 0 < z.im →
        u z + u (invS z) = ∑ ρ ∈ P.roots.toFinset, polynomialPolarMode ρ (R ρ) z := by
      intro z hz
      have := hpacket z hz
      rw [← this]
      ring
    have hzero := finitePoleBoundary_eq_zero_of_oddPeriod P.roots.toFinset id
      (Set.injOn_id _) (fun ρ hρ => ⟨(hs ρ hρ).1, (hs ρ hρ).2.1⟩) R
      (poissonPacket_boundary_oddPeriod P.roots.toFinset R
        (fun ρ hρ => ⟨(hs ρ hρ).1, (hs ρ hρ).2.1⟩)
        (fun z hz => oddInversion_packet_identity hper hoddrel hz))
    have hp (z : ℂ) : P.eval z ≠ 0 := by
      intro hz
      have hmz : z ∈ P.roots.toFinset :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hm.ne_zero).mpr hz)
      exact (hs z hmz).2.2 (hzero z hmz)
    obtain ⟨ρ, hρ⟩ := exists_xiDeficit_of_odd hD hE1 hodd
    have hPA : AnalyticAt ℂ (fun w => P.eval w) ρ :=
      P.differentiable.differentiableOn.analyticAt Filter.univ_mem
    have hd : xiDeficit E ρ = 0 := by
      exact_mod_cast (ho ρ).symm.trans (hPA.analyticOrderAt_eq_zero.mpr (hp ρ))
    have := Nat.sub_eq_zero_iff_le.mp hd
    omega

/-- **Every cubic datum is `g(1)ζ³` or loses `ξ` multiplicity at infinitely many points.** -/
theorem degreeThree_eq_zetaCube_or_infiniteDeficits {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (∀ s : ℂ, 1 < s.re → LSeries g s = g 1 * riemannZeta s ^ 3) ∨
      (xiDeficitSupport E).Infinite := by
  rcases hD.functional_equation with heven | hodd
  · exact degreeThree_eq_zetaCube_or_infiniteDeficits_of_even hD hE1 heven
  · exact Or.inr (degreeThree_odd_infiniteDeficits hD hE1 hodd)

end RHTower.WeilHigherDenominator
