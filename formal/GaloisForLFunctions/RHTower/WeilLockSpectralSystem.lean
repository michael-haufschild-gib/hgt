import GaloisForLFunctions.RHTower.WeilLockSpectralIdentity

/-!
# The spectral system for extendable locks

This extends the spectral identity (`lock_spectral_identity`, frequency `m = 1`) to every
frequency `m ≥ 1` of Hamburger's kernel `k(2t, ε + im)`.  Let `G` be a Herglotz producer with
Dirichlet coefficients `a(n)` and lower-line lock `G(1 − s) = κ₀ e^{L(s)} G(s)`, `L` holomorphic on
the lower region with `Re L` bounded above.  For `m, n ≥ 1` put

`A_L^{(m)}(n) = lim_{ε→0⁺} ε ∫_{y ≤ −2} e^{L(3/2 + iy)} e^{y(κ_{ε+im} − i log n)} dy`.

**Theorem** (`lock_spectral_system`).  If these limits exist, then for every `m ≥ 1`

`κ₀ √m Σ_{n ≥ 1} a(n) n^{−3/2} A_L^{(m)}(n) = G(1)`.

For the trivial lock (`L = 0`) one has `A_0^{(m)}(n) = m δ_{nm}`, and the system reads
`κ₀ a(m) = G(1)` for every `m`, i.e. `a ≡ 1`: this is Hamburger's theorem in spectral form.  For a
general extendable lock the system couples the Abel spectrum of the twist at the ratios `n/m` to
the producer's coefficients.

**Proof.**  As for `m = 1`, with the kernel coefficient `c_{ε+im} → 2√m` (`tendsto_edgeCoeff_m`)
and the bounds `m ≤ ‖ε + im‖ ≤ m + 1`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### The kernel coefficient at the frequency `im` -/

theorem edgeCoeff_value_m {m : ℕ} (hm : 1 ≤ m) :
    2 * I * ((m : ℂ) * I) * cexp (-((Real.log m : ℝ) : ℂ) / 2 - ((Real.pi : ℝ) : ℂ) * I / 4 -
      3 * (Real.pi : ℂ) * I / 4) = ((2 * Real.sqrt m : ℝ) : ℂ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he : -((Real.log m : ℝ) : ℂ) / 2 - ((Real.pi : ℝ) : ℂ) * I / 4 - 3 * (Real.pi : ℂ) * I / 4 =
      ((-(Real.log m / 2) : ℝ) : ℂ) + -((Real.pi : ℂ) * I) := by push_cast; ring
  have hs : Real.exp (-(Real.log m / 2)) = 1 / Real.sqrt m := by
    rw [Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hmpos]
    rw [one_div]; congr 1; congr 1; ring
  have hexp : cexp (-((Real.log m : ℝ) : ℂ) / 2 - ((Real.pi : ℝ) : ℂ) * I / 4 -
      3 * (Real.pi : ℂ) * I / 4) = -(((1 / Real.sqrt m : ℝ)) : ℂ) := by
    rw [he, Complex.exp_add, Complex.exp_neg ((Real.pi : ℂ) * I), Complex.exp_pi_mul_I,
      ← Complex.ofReal_exp, hs]
    simp
  have h1 : (m : ℝ) * (1 / Real.sqrt m) = Real.sqrt m := by
    rw [mul_one_div, Real.div_sqrt]
  rw [hexp]
  calc 2 * I * ((m : ℂ) * I) * -(((1 / Real.sqrt m : ℝ)) : ℂ)
      = 2 * (-(I * I)) * ((((m : ℝ) * (1 / Real.sqrt m)) : ℝ) : ℂ) := by push_cast; ring
    _ = ((2 * Real.sqrt m : ℝ) : ℂ) := by rw [Complex.I_mul_I, h1]; push_cast; ring

/-- `c_{ε+im} → 2√m` as `ε → 0⁺`. -/
theorem tendsto_edgeCoeff_m {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => edgeCoeff ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0)
      (𝓝 ((2 * Real.sqrt m : ℝ) : ℂ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hτ : Tendsto (fun ε : ℝ => (ε : ℂ) + (m : ℂ) * I) (𝓝[>] 0) (𝓝 ((m : ℂ) * I)) := by
    have hc : Continuous (fun ε : ℝ => (ε : ℂ) + (m : ℂ) * I) := by fun_prop
    have h := hc.tendsto 0
    rw [show ((0 : ℝ) : ℂ) + (m : ℂ) * I = (m : ℂ) * I by simp] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hnorm : ‖(m : ℂ) * I‖ = m := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast]
  have hlog : Tendsto (fun ε : ℝ => Real.log ‖(ε : ℂ) + (m : ℂ) * I‖) (𝓝[>] 0)
      (𝓝 (Real.log m)) := by
    have hI : ‖(m : ℂ) * I‖ ≠ 0 := by rw [hnorm]; exact hmpos.ne'
    have h := ((Real.continuousAt_log hI).tendsto).comp (continuous_norm.continuousAt.tendsto.comp hτ)
    rw [hnorm] at h
    exact h
  have harg : Tendsto (fun ε : ℝ => ((Real.pi : ℂ) * ((ε : ℂ) + (m : ℂ) * I) ^ 2).arg)
      (𝓝[>] 0) (𝓝 Real.pi) := by
    have hlim : Tendsto (fun ε : ℝ => (Real.pi : ℂ) * ((ε : ℂ) + (m : ℂ) * I) ^ 2)
        (𝓝[>] 0) (𝓝 ((Real.pi : ℂ) * ((m : ℂ) * I) ^ 2)) :=
      (tendsto_const_nhds (x := (Real.pi : ℂ))).mul (hτ.pow 2)
    have hval : (Real.pi : ℂ) * ((m : ℂ) * I) ^ 2 = (((-(Real.pi * (m : ℝ) ^ 2)) : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [hval] at hlim
    have hwithin : Tendsto (fun ε : ℝ => (Real.pi : ℂ) * ((ε : ℂ) + (m : ℂ) * I) ^ 2)
        (𝓝[>] 0) (𝓝[{z : ℂ | 0 ≤ z.im}] (((-(Real.pi * (m : ℝ) ^ 2)) : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hlim, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      show 0 ≤ ((Real.pi : ℂ) * ((ε : ℂ) + (m : ℂ) * I) ^ 2).im
      simp only [sq, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
        Complex.natCast_im]
      have hpi := Real.pi_pos
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_nonneg hε'.le hm0]
    have hre : ((((-(Real.pi * (m : ℝ) ^ 2)) : ℝ) : ℂ)).re < 0 := by
      rw [Complex.ofReal_re]
      have := mul_pos Real.pi_pos (pow_pos hmpos 2)
      linarith
    exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre
      (Complex.ofReal_im _)).comp hwithin
  have hF : Continuous fun p : ℂ × ℝ × ℝ =>
      2 * I * p.1 * cexp (-((p.2.1 : ℝ) : ℂ) / 2 - ((p.2.2 : ℝ) : ℂ) * I / 4 -
        3 * (Real.pi : ℂ) * I / 4) := by fun_prop
  have h := (hF.tendsto ((m : ℂ) * I, Real.log m, Real.pi)).comp
    (hτ.prodMk_nhds (hlog.prodMk_nhds harg))
  rw [← edgeCoeff_value_m hm]
  refine h.congr fun ε => ?_
  simp [edgeCoeff, Function.comp]

/-! ### The system -/

/-- **The right edge in the limit at frequency `m`.**
`ε ∫_{y ≤ −2} (e^{L} F k_τ)(3/2 + iy) dy → 2√m Σ a(n) n^{−3/2} A_L^{(m)}(n)`, `τ = ε + im`. -/
theorem tendsto_eps_rightEdge_m {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    {Aspec : ℕ → ℂ}
    (hspec : ∀ n : ℕ, 1 ≤ n → Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      cexp (L (edgePt y) + (y : ℂ) *
        (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (Aspec n))) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      edgeIntegrand (expTwistG L G) ((ε : ℂ) + (m : ℂ) * I) (edgePt y)) (𝓝[>] 0)
      (𝓝 (((2 * Real.sqrt m : ℝ) : ℂ) *
        ∑' n, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n * Aspec n)) := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set M : ℝ := (m : ℝ) + 1 with hM
  have hM0 : 0 < M := by linarith
  set a : ℕ → ℂ := dirichletExp (lamLog lam) with ha
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hSa : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ :=
    (hLa _ (by simp; norm_num)).1.norm
  have hedge_im : ∀ y : ℝ, (edgePt y).im = y := fun y => by
    simp only [edgePt, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    ring
  have hLc' : ∀ y : ℝ, y ≤ -2 → ContinuousAt L (edgePt y) := fun y hy =>
    hLc _ (by rw [edgePt_re]; norm_num) (by rw [hedge_im]; linarith)
  have hA : ∀ y : ℝ, y ≤ -2 → (L (edgePt y)).re ≤ A := fun y hy =>
    hLs _ (by rw [edgePt_re]; norm_num) (by rw [edgePt_re]) (by rw [hedge_im]; linarith)
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  set C : ℝ := 2 * M * (eA * M) + 4 * M * eA / Real.pi with hC
  -- the terms
  set f : ℝ → ℕ → ℂ := fun ε n => (ε : ℂ) * expEdgeTerm a L ((ε : ℂ) + (m : ℂ) * I) (-2) n
    with hf
  -- facts about `τ = ε + i` for `0 < ε < 1`
  have hτfacts : ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      0 < ((ε : ℂ) + (m : ℂ) * I).re ∧ 1 ≤ ‖(ε : ℂ) + (m : ℂ) * I‖ ∧
        ‖(ε : ℂ) + (m : ℂ) * I‖ ≤ M ∧
        ε / M ≤ (edgeExp ((ε : ℂ) + (m : ℂ) * I)).re := by
    intro ε hε
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre : τ.re = ε := by simp [hτ]
    have hτre0 : 0 < τ.re := by rw [hτre]; exact hε.1
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      rw [him, abs_of_pos (by linarith)] at h; linarith
    have hτ2 : ‖τ‖ ≤ M := by
      have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
        Real.norm_eq_abs, abs_of_pos hε.1] at h
      rw [hτ]; linarith [hε.2]
    have hτpos : 0 < ‖τ‖ := by linarith
    refine ⟨hτre0, hτ1, hτ2, ?_⟩
    rw [edgeExp_re]
    have h := abs_arg_pi_mul_sq_le hτre0
    have := le_abs_self ((Real.pi : ℂ) * τ ^ 2).arg
    have hδ : ε / M ≤ τ.re / ‖τ‖ := by
      rw [hτre]; exact div_le_div_of_nonneg_left hε.1.le hτpos hτ2
    linarith
  -- the sum
  have hsum_eq : ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 →
      (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
        edgeIntegrand (expTwistG L G) ((ε : ℂ) + (m : ℂ) * I) (edgePt y) = ∑' n, f ε n := by
    intro ε hε
    obtain ⟨hτre0, hτ1, _, _⟩ := hτfacts ε hε
    have hhs := hasSum_expEdgeTerm hsl hid hGd hG2 hτre0 hτ1 (by norm_num) hLc' hA
    rw [← hhs.tsum_eq, ← tsum_mul_left]
  -- the per-term limits
  have hlim : ∀ n : ℕ, Tendsto (fun ε => f ε n) (𝓝[>] 0)
      (𝓝 (((2 * Real.sqrt m : ℝ) : ℂ) * (LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * Aspec n))) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      have h0 : ∀ ε : ℝ, f ε 0 = 0 := fun ε => by simp [hf, expEdgeTerm]
      simp only [h0, LSeries.term_zero, zero_mul, mul_zero]
      exact tendsto_const_nhds
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    set T₀ := LSeries.term a (((3 / 2 : ℝ) : ℂ)) n with hT₀
    set leadF : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ y in Iic (-2 : ℝ), cexp (L (edgePt y) + (y : ℂ) *
        (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I)) with hleadF
    set restF : ℝ → ℂ := fun ε => ∫ y in Iic (-2 : ℝ),
        cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) *
          (offKernel ((ε : ℂ) + (m : ℂ) * I) (edgePt y) -
            edgeCoeff ((ε : ℂ) + (m : ℂ) * I) * cexp ((y : ℂ) *
              edgeExp ((ε : ℂ) + (m : ℂ) * I))) with hrestF
    have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε n =
        T₀ * edgeCoeff ((ε : ℂ) + (m : ℂ) * I) * leadF ε + T₀ * ((ε : ℂ) * restF ε) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
      obtain ⟨hτre0, _, _, _⟩ := hτfacts ε hε
      have hd := (expEdgeTerm_decomp a hτre0 hn1 (by norm_num : (-2 : ℝ) ≤ -1) hLc' hA).1
      simp only [hf, hleadF, hrestF]
      rw [hd]; ring
    have hrest0 : Tendsto (fun ε : ℝ => (ε : ℂ) * restF ε) (𝓝[>] 0) (𝓝 0) := by
      have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ‖(ε : ℂ) * restF ε‖ ≤ ε * (eA * (4 * M / Real.pi)) := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
        obtain ⟨hτre0, hτ1, hτ2, _⟩ := hτfacts ε hε
        have hr := (expEdgeTerm_decomp a hτre0 hn1 (by norm_num : (-2 : ℝ) ≤ -1) hLc' hA).2
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
        have hτh : ‖(ε : ℂ) + (m : ℂ) * I‖ ^ (1 / 2 : ℝ) ≤ M := by
          calc _ ≤ ‖(ε : ℂ) + (m : ℂ) * I‖ ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
            _ = ‖(ε : ℂ) + (m : ℂ) * I‖ := Real.rpow_one _
            _ ≤ M := hτ2
        have hpe : Real.exp (Real.pi * -2) ≤ 1 := by
          rw [Real.exp_le_one_iff]; linarith
        have hr' : ‖restF ε‖ ≤ eA * (4 * M / Real.pi) := by
          refine hr.trans ?_
          have : 4 * ‖(ε : ℂ) + (m : ℂ) * I‖ ^ (1 / 2 : ℝ) *
              (Real.exp (Real.pi * -2) / Real.pi) ≤ 4 * M * (1 / Real.pi) := by gcongr
          calc Real.exp A * (4 * ‖(ε : ℂ) + (m : ℂ) * I‖ ^ (1 / 2 : ℝ) *
                (Real.exp (Real.pi * -2) / Real.pi)) ≤ eA * (4 * M * (1 / Real.pi)) :=
                mul_le_mul_of_nonneg_left this heA0.le
            _ = eA * (4 * M / Real.pi) := by ring
        exact mul_le_mul_of_nonneg_left hr' hε.1.le
      have hz : Tendsto (fun ε : ℝ => ε * (eA * (4 * M / Real.pi))) (𝓝[>] 0) (𝓝 0) := by
        have := ((tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).mul_const
          (eA * (4 * M / Real.pi))
        simpa using this
      exact squeeze_zero_norm' hb hz
    have hmain := ((tendsto_const_nhds (x := T₀)).mul (tendsto_edgeCoeff_m hm)).mul (hspec n hn1)
    have htot := hmain.add (hrest0.const_mul T₀)
    rw [mul_zero, add_zero] at htot
    refine (htot.congr' (heq.mono fun ε h => h.symm)).trans (le_of_eq ?_)
    ring_nf
  -- the uniform bound
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ n : ℕ,
      ‖f ε n‖ ≤ ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * C := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε n
    obtain ⟨hτre0, hτ1, hτ2, hκ⟩ := hτfacts ε hε
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    by_cases hn0 : n = 0
    · subst hn0
      have : f ε 0 = 0 := by simp [hf, expEdgeTerm]
      rw [this, norm_zero]; exact mul_nonneg (norm_nonneg _) (by positivity)
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    obtain ⟨hd, hr⟩ := expEdgeTerm_decomp a hτre0 hn1 (by norm_num : (-2 : ℝ) ≤ -1) hLc' hA
    have hκ0 : 0 < (edgeExp τ).re := lt_of_lt_of_le (div_pos hε.1 hM0) hκ
    have hw : (edgeExp τ - ((Real.log n : ℝ) : ℂ) * I).re = (edgeExp τ).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hl := norm_lead_le_trivial (w := edgeExp τ - ((Real.log n : ℝ) : ℂ) * I)
      (by rw [hw]; exact hκ0) hA
    rw [hw] at hl
    have hτh : ‖τ‖ ^ (1 / 2 : ℝ) ≤ M := by
      calc ‖τ‖ ^ (1 / 2 : ℝ) ≤ ‖τ‖ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
        _ = ‖τ‖ := Real.rpow_one _
        _ ≤ M := hτ2
    have hcoef : ‖edgeCoeff τ‖ ≤ 2 * M := by
      rw [norm_edgeCoeff (by intro h; rw [h] at hτre0; simp at hτre0)]; linarith
    have hlead' : ε * ‖∫ y in Iic (-2 : ℝ), cexp (L (edgePt y) + (y : ℂ) *
        (edgeExp τ - ((Real.log n : ℝ) : ℂ) * I))‖ ≤ eA * M := by
      have he1 : Real.exp ((edgeExp τ).re * -2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have hq : ε / (edgeExp τ).re ≤ M := by
        rw [div_le_iff₀ hκ0]
        have := (div_le_iff₀ hM0).mp hκ
        linarith
      calc ε * ‖_‖ ≤ ε * (Real.exp A * (Real.exp ((edgeExp τ).re * -2) / (edgeExp τ).re)) :=
            mul_le_mul_of_nonneg_left hl hε.1.le
        _ ≤ ε * (eA * (1 / (edgeExp τ).re)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right he1 hκ0.le) heA0.le) hε.1.le
        _ = eA * (ε / (edgeExp τ).re) := by ring
        _ ≤ eA * M := mul_le_mul_of_nonneg_left hq heA0.le
    have hr' : ε * ‖∫ y in Iic (-2 : ℝ), cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) *
        cexp (L (edgePt y)) * (offKernel τ (edgePt y) - edgeCoeff τ * cexp ((y : ℂ) *
          edgeExp τ))‖ ≤ 4 * M * eA / Real.pi := by
      have hpe : Real.exp (Real.pi * -2) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have h1 : Real.exp A * (4 * ‖τ‖ ^ (1 / 2 : ℝ) * (Real.exp (Real.pi * -2) / Real.pi)) ≤
          eA * (4 * M * (1 / Real.pi)) := by
        apply mul_le_mul_of_nonneg_left _ heA0.le
        gcongr
      calc ε * ‖_‖ ≤ 1 * (eA * (4 * M * (1 / Real.pi))) :=
            mul_le_mul hε.2.le (hr.trans h1) (norm_nonneg _) (by positivity)
        _ = 4 * M * eA / Real.pi := by ring
    simp only [hf]
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
    have htri := norm_add_le (LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * edgeCoeff τ *
      (∫ y in Iic (-2 : ℝ), cexp (L (edgePt y) + (y : ℂ) * (edgeExp τ - ((Real.log n : ℝ) : ℂ) * I))))
      (LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * (∫ y in Iic (-2 : ℝ),
        cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) *
          (offKernel τ (edgePt y) - edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ))))
    rw [norm_mul, norm_mul, norm_mul] at htri
    set T := ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ with hT
    have hT0 : 0 ≤ T := norm_nonneg _
    calc ε * ‖_‖ ≤ ε * (T * ‖edgeCoeff τ‖ * ‖∫ y in Iic (-2 : ℝ), cexp (L (edgePt y) +
          (y : ℂ) * (edgeExp τ - ((Real.log n : ℝ) : ℂ) * I))‖ + T * ‖∫ y in Iic (-2 : ℝ),
          cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) *
            (offKernel τ (edgePt y) - edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ))‖) :=
          mul_le_mul_of_nonneg_left htri hε.1.le
      _ = T * ‖edgeCoeff τ‖ * (ε * ‖∫ y in Iic (-2 : ℝ), cexp (L (edgePt y) +
          (y : ℂ) * (edgeExp τ - ((Real.log n : ℝ) : ℂ) * I))‖) + T * (ε * ‖∫ y in Iic (-2 : ℝ),
          cexp (-(((Real.log n : ℝ) : ℂ) * ((y : ℂ) * I))) * cexp (L (edgePt y)) *
            (offKernel τ (edgePt y) - edgeCoeff τ * cexp ((y : ℂ) * edgeExp τ))‖) := by ring
      _ ≤ T * (2 * M) * (eA * M) + T * (4 * M * eA / Real.pi) := by
          have h1 := mul_le_mul (mul_le_mul_of_nonneg_left hcoef hT0) hlead'
            (mul_nonneg hε.1.le (norm_nonneg _)) (mul_nonneg hT0 (by positivity))
          have h2 := mul_le_mul_of_nonneg_left hr' hT0
          linarith
      _ = T * C := by rw [hC]; ring
  -- Tannery
  have hT := tendsto_tsum_of_dominated_convergence (hSa.mul_right C) hlim hbound
  rw [tsum_mul_left] at hT
  refine hT.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
  exact (hsum_eq ε hε).symm


/-! ### The far part as a right edge plus a top edge -/

/-- For `0 < ε ≤ 1` and `τ = ε + im`, the far radial integral is half the right edge plus `i/2`
times the top edge at height `−2`, and the top edge is bounded independently of `ε`. -/
theorem far_eq_spectral_m {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → s.im < 0 → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    {CF₀ : ℝ} (hCF₀ : 0 ≤ CF₀)
    (hF₀ : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF₀ * (1 + |y|) ^ (1 / 2 : ℝ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (ε : ℂ) * (∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) =
      (1 / 2 : ℂ) * ((ε : ℂ) * ∫ y in Iic (-2 : ℝ),
        edgeIntegrand (expTwistG L G) ((ε : ℂ) + (m : ℂ) * I) (edgePt y)) +
      (1 / 2 : ℂ) * I * ((ε : ℂ) * ∫ x in (1 / 2 : ℝ)..(3 / 2),
        edgeIntegrand (expTwistG L G) ((ε : ℂ) + (m : ℂ) * I)
          ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)) ∧
    ‖∫ x in (1 / 2 : ℝ)..(3 / 2), edgeIntegrand (expTwistG L G) ((ε : ℂ) + (m : ℂ) * I)
        ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ ≤
      Real.exp A * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1)) := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖ with hS
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  set CF : ℝ := eA * CF₀ with hCF
  have hCF0 : 0 ≤ CF := by positivity
  set H : ℂ → ℂ := expTwistG L G with hH
  have hHc' : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → ContinuousAt H s :=
    fun s hs _ him =>
    (Complex.continuous_exp.continuousAt.comp (hLc s hs (by linarith))).mul (hGc s hs)
  have hHd' : ∀ s : ℂ, 1 / 2 < s.re → s.re < 3 / 2 → s.im < -1 → DifferentiableAt ℂ H s :=
    fun s hs _ him =>
    ((hLd s hs (by linarith)).cexp).mul (hGd s hs).differentiableAt
  have hF : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ 3 / 2 → y ≤ -2 →
      ‖prodF H ((x : ℂ) + (y : ℂ) * I)‖ ≤ CF * (1 + |y|) ^ (1 / 2 : ℝ) := by
    intro x y hx1 hx2 hy
    have hre : (1 / 2 : ℝ) ≤ ((x : ℂ) + (y : ℂ) * I).re := by simpa using hx1
    have hre2 : ((x : ℂ) + (y : ℂ) * I).re ≤ 3 / 2 := by simpa using hx2
    have him : ((x : ℂ) + (y : ℂ) * I).im ≤ -1 := by simp; linarith
    rw [hH, prodF_expTwistG, norm_mul, Complex.norm_exp, hCF]
    have h1 : Real.exp (L ((x : ℂ) + (y : ℂ) * I)).re ≤ eA :=
      Real.exp_le_exp.mpr (hLs _ hre hre2 him)
    have h3 := hF₀ x y hx1 hx2 (by rw [abs_of_neg (by linarith)]; linarith)
    calc Real.exp (L ((x : ℂ) + (y : ℂ) * I)).re * ‖prodF G ((x : ℂ) + (y : ℂ) * I)‖
        ≤ eA * (CF₀ * (1 + |y|) ^ (1 / 2 : ℝ)) :=
          mul_le_mul h1 h3 (norm_nonneg _) heA0.le
      _ = eA * CF₀ * (1 + |y|) ^ (1 / 2 : ℝ) := by ring
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : τ.re = ε := by simp [hτ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [hτ]
    rw [him, abs_of_pos (by linarith)] at h; linarith
  have hτ2 : ‖τ‖ ≤ (m : ℝ) + 1 := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    rw [hτ]; linarith
  have hτpos : 0 < ‖τ‖ := by linarith
  have hedge : ∀ y : ℝ, y ≤ -1 → ‖edgeIntegrand H τ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      (eA * Real.exp S) *
        (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(|y| * (τ.re / ‖τ‖)))) := by
    intro y hy
    rw [hH, edgeIntegrand_expTwistG, norm_mul, Complex.norm_exp]
    have hE := norm_edgeIntegrand_three_halves_le hsl hid hGd hG2 hτre0 hτ1
      (show 1 ≤ |y| by rw [abs_of_neg (by linarith)]; linarith)
    have hLe : Real.exp (L (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re ≤ eA :=
      Real.exp_le_exp.mpr (hLs _ (by norm_num) (by norm_num) (by simpa using hy))
    calc _ ≤ eA * (Real.exp S * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
          Real.exp (-(|y| * (τ.re / ‖τ‖))))) := mul_le_mul hLe hE (norm_nonneg _) heA0.le
      _ = _ := by ring
  have hfint : IntegrableOn (fun t => phiG H t * pairKernel (2 * t) τ) (Iic (-1)) := by
    have h := ((MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
      hτre0).norm.const_mul eA).integrableOn (s := Iic (-1))
    refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Iic).mpr
      (Filter.Eventually.of_forall fun t ht => ?_))
    · have hc : ContinuousOn (fun t : ℝ => cexp (L (lineS t)) * phiG G t *
          pairKernel (2 * t) τ) (Iic (-1)) := by
        intro t ht
        have ht0 : t ≤ -1 := ht
        have hl : Continuous lineS := by unfold lineS; fun_prop
        have him : (lineS t).im < 0 := by unfold lineS; simp; linarith
        have hL1 : ContinuousAt (fun t : ℝ => cexp (L (lineS t))) t :=
          Complex.continuous_exp.continuousAt.comp
            ((hLc _ (le_of_eq (lineS_re t).symm) him).comp hl.continuousAt)
        exact ((hL1.mul (continuous_phiG hGc).continuousAt).mul
          (continuous_pairKernel_two_mul hτ0).continuousAt).continuousWithinAt
      refine (hc.congr fun t _ => ?_).aestronglyMeasurable measurableSet_Iic
      simp only [hH, phiG_expTwistG]
    · have ht0 : t < 0 := lt_of_le_of_lt ht (by norm_num)
      rw [hH, phiG_expTwistG, mul_assoc, norm_mul, Complex.norm_exp]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hLl t ht0)) (norm_nonneg _)
  have hcont := setIntegral_Iic_radial_eq_of_lowerRegion hHc' hHd' hCF0 hF hτre0 hτ1 hedge le_rfl
    hfint
  have hrewrite : ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) τ) =
      ∫ t in Iic (-1 : ℝ), phiG H t * pairKernel (2 * t) τ := by
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    rw [hH, phiG_expTwistG]; ring
  refine ⟨?_, ?_⟩
  · rw [hrewrite, hcont, show (2 * (-1 : ℝ)) = -2 by norm_num]
    simp only [edgePt]
    ring
  · have h := norm_horizontalEdge_le_lower hF hτre0 hτ1 (y := 2 * (-1 : ℝ)) (by norm_num)
    refine h.trans ?_
    have habs : |2 * (-1 : ℝ)| = 2 := by norm_num
    rw [habs]
    have he : Real.exp (-(2 * (τ.re / ‖τ‖))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := div_pos hτre0 hτpos; linarith
    have h0 : 0 ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) := by positivity
    calc CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
          Real.exp (-(2 * (τ.re / ‖τ‖))))
        ≤ CF * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1) * 1) := by gcongr
      _ = _ := by rw [hCF]; ring


/-! ### The twisted radial integral and the identity -/

/-- **The twisted radial limit at frequency `m`.**  If the edge Abel transforms exist,
`ε ∫_{t<0} e^{L(½+2it)} φ(t) k(2t, ε + im) dt → √m Σ_n a(n) n^{−3/2} A_L^{(m)}(n)`. -/
theorem tendsto_twisted_spectral_m {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → s.im < 0 → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A) {Aspec : ℕ → ℂ}
    (hspec : ∀ n : ℕ, 1 ≤ n → Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      cexp (L (edgePt y) + (y : ℂ) *
        (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (Aspec n))) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iio (0 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (((Real.sqrt m : ℝ) : ℂ) *
        ∑' n, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n * Aspec n)) := by
  have hpi := Real.pi_pos
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  obtain ⟨CF₀, hCF₀, hF₀⟩ := exists_norm_prodF_le hsl hΦre hid hGc hGd hG2
  set eA : ℝ := Real.exp A with heA
  have heA0 : 0 < eA := Real.exp_pos _
  -- the near part
  have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_eps_mul_setIntegral_Ioo (h := fun t => cexp (L (lineS t)) * phiG G t)
      (B := eA * (CB * 2 ^ N)) (fun t ht => ?_) hm).congr fun ε => ?_
    · rw [norm_mul, Complex.norm_exp]
      have h1 : Real.exp (L (lineS t)).re ≤ eA := Real.exp_le_exp.mpr (hLl t ht.2)
      have h2 : ‖phiG G t‖ ≤ CB * 2 ^ N := by
        refine (hpoly t).1.trans ?_
        have hta : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        gcongr; linarith
      exact mul_le_mul h1 h2 (norm_nonneg _) heA0.le
    · simp only [mul_assoc]
  -- the far part
  set Sspec : ℂ := ∑' n, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n * Aspec n
    with hSspec
  have hedgeLim := tendsto_eps_rightEdge_m hsl hid hGd hG2 hm hLc hLs hspec
  set Ct : ℝ := Real.exp A * CF₀ * (1 + 2) ^ (1 / 2 : ℝ) * (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1))
    with hCt
  have htop : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ x in (1 / 2 : ℝ)..(3 / 2),
      edgeIntegrand (expTwistG L G) ((ε : ℂ) + (m : ℂ) * I)
        ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ‖(ε : ℂ) * ∫ x in (1 / 2 : ℝ)..(3 / 2),
        edgeIntegrand (expTwistG L G) ((ε : ℂ) + (m : ℂ) * I)
          ((x : ℂ) + ((2 * (-1 : ℝ) : ℝ) : ℂ) * I)‖ ≤ ε * Ct := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
      have h := (far_eq_spectral_m hsl hΦre hid hGc hGd hG2 hm hLc hLd hLs hLl hCF₀ hF₀ hε.1
        hε.2.le).2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
      exact mul_le_mul_of_nonneg_left h hε.1.le
    have hz : Tendsto (fun ε : ℝ => ε * Ct) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds).mul_const Ct
      simpa using this
    exact squeeze_zero_norm' hb hz
  have hfar : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (L (lineS t)) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (((Real.sqrt m : ℝ) : ℂ) * Sspec)) := by
    have h := (hedgeLim.const_mul (1 / 2 : ℂ)).add (htop.const_mul ((1 / 2 : ℂ) * I))
    rw [mul_zero, add_zero, show (1 / 2 : ℂ) * (((2 * Real.sqrt m : ℝ) : ℂ) * Sspec) =
      ((Real.sqrt m : ℝ) : ℂ) * Sspec by push_cast; ring] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
    exact ((far_eq_spectral_m hsl hΦre hid hGc hGd hG2 hm hLc hLd hLs hLl hCF₀ hF₀ hε.1
      hε.2.le).1).symm
  -- combine
  have hsum := hfar.add hnear
  rw [add_zero] at hsum
  refine hsum.congr' (eventually_nhdsWithin_of_forall fun ε hε => ?_)
  have hε' : (0 : ℝ) < ε := hε
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre : 0 < τ.re := by simp [hτ]; exact hε'
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hint : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Iio 0) := by
    have h := ((MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
      hτre).norm.const_mul eA).integrableOn (s := Iio (0 : ℝ))
    refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Iio).mpr
      (Eventually.of_forall fun t ht => ?_))
    · have hc : ContinuousOn (fun t : ℝ => cexp (L (lineS t)) * (phiG G t *
          pairKernel (2 * t) τ)) (Iio 0) := by
        intro t ht
        have ht0 : t < 0 := ht
        have hl : Continuous lineS := by unfold lineS; fun_prop
        have him : (lineS t).im < 0 := by unfold lineS; simp; linarith
        have hL1 : ContinuousAt (fun t : ℝ => cexp (L (lineS t))) t :=
          Complex.continuous_exp.continuousAt.comp
            ((hLc _ (le_of_eq (lineS_re t).symm) him).comp hl.continuousAt)
        exact (hL1.mul ((continuous_phiG hGc).continuousAt.mul
          (continuous_pairKernel_two_mul hτ0).continuousAt)).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Iio
    · have ht0 : t < 0 := ht
      rw [norm_mul, Complex.norm_exp]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hLl t ht0)) (norm_nonneg _)
  have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
    ext t
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro h
      by_cases h1 : t ≤ -1
      · exact Or.inl h1
      · exact Or.inr ⟨by linarith, h⟩
    · rintro (h | h)
      · linarith
      · exact h.2
  have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
    Set.disjoint_left.mpr fun t h1 h2 => by
      simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
  have h1 : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Iic (-1)) := hint.mono_set (by rw [hsplit]; exact subset_union_left)
  have h2 : IntegrableOn (fun t => cexp (L (lineS t)) * (phiG G t *
      pairKernel (2 * t) τ)) (Ioo (-1) 0) := hint.mono_set (by rw [hsplit]; exact subset_union_right)
  simp only
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioo h1 h2]
  ring



/-- **The spectral system.**  If the producer satisfies the lower-line lock
`G(1 − s) = κ₀ e^{L(s)} G(s)` and the edge Abel transforms `A_L^{(m)}(n)` at the frequency `m`
exist, then `κ₀ √m Σ_{n ≥ 1} a(n) n^{−3/2} A_L^{(m)}(n) = G(1)`. -/
theorem lock_spectral_identity_m {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {m : ℕ} (hm : 1 ≤ m) {L : ℂ → ℂ} (hLc : ∀ s : ℂ, 1 / 2 ≤ s.re → s.im < 0 → ContinuousAt L s)
    (hLd : ∀ s : ℂ, 1 / 2 < s.re → s.im < 0 → DifferentiableAt ℂ L s) {A : ℝ}
    (hLs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → s.im ≤ -1 → (L s).re ≤ A)
    (hLl : ∀ t : ℝ, t < 0 → (L (lineS t)).re ≤ A)
    {κ₀ : ℂ} (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = κ₀ * cexp (L (lineS τ)) * G (lineS τ))
    {Aspec : ℕ → ℂ}
    (hspec : ∀ n : ℕ, 1 ≤ n → Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      cexp (L (edgePt y) + (y : ℂ) *
        (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (Aspec n))) :
    κ₀ * (((Real.sqrt m : ℝ) : ℂ) *
      ∑' n, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n * Aspec n) = G 1 := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  have hpi := Real.pi_pos
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  set R : ℝ → ℂ := fun ε => (ε : ℂ) * ∫ t in Iio (0 : ℝ),
    phiStar G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) with hR
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
    have h := (tendsto_lower_reflected_radial hsl hΦre hidT hGc hGd hG2 hm).const_mul
      ((2 * Real.pi : ℝ) : ℂ)
    have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) = 2 * betaG G := by
      have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
      push_cast; field_simp
    rw [hval] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    simp only [hR]
    linear_combination ((ε : ℂ) * ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ) * h2pi
  have hR' : Tendsto R (𝓝[>] 0) (𝓝 (κ₀ * (((Real.sqrt m : ℝ) : ℂ) *
      ∑' n, LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n * Aspec n))) := by
    have h := (tendsto_twisted_spectral_m hsl hΦre hidT hGc hGd hG2 hm hLc hLd hLs hLl
      hspec).const_mul κ₀
    refine h.congr' (eventually_nhdsWithin_of_forall fun ε _ => ?_)
    simp only [hR]
    rw [← mul_assoc, mul_comm κ₀, mul_assoc, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
    have ht0 : t < 0 := ht
    simp only [phiStar, phiG]
    rw [hlock t ht0]
    ring
  have h := tendsto_nhds_unique hR' hRlim
  rw [h]
  unfold betaG
  ring


end

end AbelianTwist

end RHTower
