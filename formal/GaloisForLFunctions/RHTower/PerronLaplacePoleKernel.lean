import GaloisForLFunctions.RHTower.PerronVonMangoldtSwap

/-!
# The weighted Perron integral of a simple pole

For `c > 0`, `s = c + 2πiw`, `L ∈ ℝ` and `Re b < c`,

`∫ e^{sL} / (s² (s − b)) dw = ∫_0^∞ e^{bu} (L − u)⁺ du`,

and for `b ≠ 0`, `L ≥ 0` the right side is `(e^{bL} − 1 − bL)/b²`.

**Proof.**  `1/(s − b) = ∫_0^∞ e^{−(s−b)u} du`.  The double integral converges absolutely
(`e^{−(c − Re b)u} e^{cL}/|s|²`), so Fubini applies, and the inner integral is the weighted
Perron kernel `∫ e^{s(L−u)}/s² dw = (L − u)⁺` (`perron_weighted_kernel`).  The closed form is the
antiderivative `e^{bu}(L − u)/b + e^{bu}/b²` on `[0, L]`.

This evaluates, without contour shifting, the contribution of every simple pole `b` left of the
contour to a logarithmically weighted Perron integral: it is the residue sum
`e^{bL}/b² − 1/b² − L/b` at `s = b` and the double pole `s = 0`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower

namespace PerronPole

/-- The Perron contour point `c + 2πiw`. -/
def contour (c w : ℝ) : ℂ := (c : ℂ) + 2 * Real.pi * w * I

theorem contour_re (c w : ℝ) : (contour c w).re = c := by simp [contour]

theorem norm_contour_sq_ge (c w : ℝ) : c ^ 2 + (2 * Real.pi * w) ^ 2 ≤ ‖contour c w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [contour]
  nlinarith

/-- **The closed form.**  `∫_0^∞ e^{bu}(L − u)⁺ du = (e^{bL} − 1 − bL)/b²` for `b ≠ 0`, `L ≥ 0`. -/
theorem integral_cexp_mul_max_sub {b : ℂ} (hb : b ≠ 0) {L : ℝ} (hL : 0 ≤ L) :
    ∫ u in Ioi (0 : ℝ), cexp (b * u) * ((max (L - u) 0 : ℝ) : ℂ) =
      (cexp (b * L) - 1 - b * L) / b ^ 2 := by
  set f : ℝ → ℂ := fun u => cexp (b * u) * ((max (L - u) 0 : ℝ) : ℂ) with hf
  have hzero : ∀ u ∈ Ioi L, f u = 0 := fun u hu => by
    simp only [hf, mem_Ioi] at hu ⊢
    rw [max_eq_right (by linarith), Complex.ofReal_zero, mul_zero]
  have hsplit : ∫ u in Ioi (0 : ℝ), f u = ∫ u in (0 : ℝ)..L, f u := by
    rw [intervalIntegral.integral_of_le hL]
    have hU : Ioi (0 : ℝ) = Ioc 0 L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL).symm
    have hcont : Continuous f := by
      simp only [hf]; fun_prop
    rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      ((integrableOn_zero).congr_fun (fun u hu => (hzero u hu).symm) measurableSet_Ioi),
      setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero, add_zero]
  rw [hsplit]
  set F : ℝ → ℂ := fun u => cexp (b * u) * (L - u) / b + cexp (b * u) / b ^ 2 with hF
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) L, HasDerivAt F (f u) u := by
    intro u hu
    rw [uIcc_of_le hL] at hu
    have he : HasDerivAt (fun u : ℝ => cexp (b * u)) (cexp (b * u) * b) u := by
      have h := ((hasDerivAt_id (u : ℂ)).const_mul b).cexp
      simpa using h.comp_ofReal
    have hlin : HasDerivAt (fun u : ℝ => ((L - u : ℝ) : ℂ)) (-1) u := by
      have h := ((hasDerivAt_id u).const_sub L).ofReal_comp
      simpa using h
    have h1 := (he.mul hlin).div_const b
    have h2 := he.div_const (b ^ 2)
    have h := h1.add h2
    have hFeq : F = fun u : ℝ => cexp (b * u) * ((L - u : ℝ) : ℂ) / b + cexp (b * u) / b ^ 2 := by
      funext u; simp only [hF]; push_cast; ring
    rw [hFeq]
    refine h.congr_deriv ?_
    simp only [hf]
    rw [max_eq_left (by linarith [hu.2])]
    field_simp
    push_cast
    ring
  have hcont : Continuous f := by simp only [hf]; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 L)]
  simp only [hF]
  push_cast
  field_simp
  ring_nf
  simp
  ring

/-- `1/(s − b) = ∫_0^∞ e^{−(s−b)u} du` for `Re s > Re b`. -/
theorem inv_sub_eq_integral {s b : ℂ} (h : b.re < s.re) :
    1 / (s - b) = ∫ u in Ioi (0 : ℝ), cexp (-(s - b) * u) := by
  have ha : (-(s - b)).re < 0 := by simp; linarith
  rw [integral_exp_mul_complex_Ioi ha 0]
  have hne : s - b ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  field_simp
  simp

/-- **The weighted Perron integral of a simple pole.**  For `c > 0`, `Re b < c` and `L ∈ ℝ`,
`∫ e^{sL}/(s²(s − b)) dw = ∫_0^∞ e^{bu}(L − u)⁺ du` on `s = c + 2πiw`. -/
theorem integral_inv_sub_mul_perron {c : ℝ} (hc : 0 < c) (L : ℝ) {b : ℂ} (hb : b.re < c) :
    ∫ w : ℝ, 1 / (contour c w - b) * (cexp (contour c w * L) / contour c w ^ 2) =
      ∫ u in Ioi (0 : ℝ), cexp (b * u) * ((max (L - u) 0 : ℝ) : ℂ) := by
  have hre : ∀ w, b.re < (contour c w).re := fun w => by rw [contour_re]; exact hb
  set P : ℝ → ℂ := fun w => cexp (contour c w * L) / contour c w ^ 2 with hP
  have hPi : Integrable P := integrable_perron_integrand hc L
  have hPn : ∀ w, ‖P w‖ = Real.exp (c * L) / (c ^ 2 + (2 * Real.pi * w) ^ 2) :=
    fun w => norm_perron_integrand (a := c) L w
  set κ : ℝ := c - b.re with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set g : ℝ → ℝ → ℂ := fun w u => cexp (-(contour c w - b) * u) * P w with hg
  have h1 : ∀ w, 1 / (contour c w - b) * P w = ∫ u in Ioi (0 : ℝ), g w u := by
    intro w
    rw [inv_sub_eq_integral (hre w), ← integral_mul_const]
  have hnorm : ∀ w u : ℝ, ‖g w u‖ = Real.exp (-(κ * u)) * ‖P w‖ := by
    intro w u
    simp only [hg]
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [contour, hκ]
    ring
  have hexpI : IntegrableOn (fun u : ℝ => Real.exp (-(κ * u))) (Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 hκ0
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have hint : Integrable (Function.uncurry g) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hprod := hPi.norm.mul_prod (μ := volume) (ν := volume.restrict (Ioi (0 : ℝ))) hexpI
    refine hprod.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine (Continuous.aestronglyMeasurable ?_)
      have hne : ∀ p : ℝ × ℝ, ((c : ℂ) + 2 * Real.pi * p.1 * I) ^ 2 ≠ 0 := fun p =>
        pow_ne_zero 2 fun h0 => by
          have := congrArg Complex.re h0
          simp at this
          linarith
      show Continuous fun p : ℝ × ℝ => g p.1 p.2
      simp only [hg, hP, contour]
      exact Continuous.mul (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) hne)
    · show ‖g p.1 p.2‖ ≤ _
      rw [hnorm, mul_comm]
  calc ∫ w : ℝ, 1 / (contour c w - b) * P w
      = ∫ w : ℝ, ∫ u in Ioi (0 : ℝ), g w u := integral_congr_ae (Eventually.of_forall h1)
    _ = ∫ u in Ioi (0 : ℝ), ∫ w : ℝ, g w u := integral_integral_swap hint
    _ = ∫ u in Ioi (0 : ℝ), cexp (b * u) * ((max (L - u) 0 : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        have hgu : ∀ w, g w u = cexp (b * u) *
            (cexp (((c : ℂ) + 2 * Real.pi * w * I) * ((L - u : ℝ) : ℂ)) /
              ((c : ℂ) + 2 * Real.pi * w * I) ^ 2) := by
          intro w
          simp only [hg, hP, contour]
          rw [mul_div_assoc', mul_div_assoc', ← Complex.exp_add, ← Complex.exp_add]
          congr 2
          push_cast
          ring
        simp_rw [hgu]
        rw [integral_const_mul, perron_weighted_kernel hc (L - u)]

/-- The closed form of the pole integral: `(e^{bL} − 1 − bL)/b²` for `b ≠ 0`, `L ≥ 0`. -/
theorem integral_inv_sub_mul_perron_eq {c : ℝ} (hc : 0 < c) {L : ℝ} (hL : 0 ≤ L) {b : ℂ}
    (hb : b.re < c) (hb0 : b ≠ 0) :
    ∫ w : ℝ, 1 / (contour c w - b) * (cexp (contour c w * L) / contour c w ^ 2) =
      (cexp (b * L) - 1 - b * L) / b ^ 2 := by
  rw [integral_inv_sub_mul_perron hc L hb, integral_cexp_mul_max_sub hb0 hL]

/-- **The logarithmically weighted Perron formula for a Dirichlet series.**  If
`Σ f(n) n^{−(z+c)}` converges absolutely (`c > 0`), then for every `L ∈ ℝ`
`Σ_n f(n) n^{−z} (L − log n)⁺ = ∫ L(f, z + s) e^{sL}/s² dw` on `s = c + 2πiw`. -/
theorem tsum_term_mul_max_eq_integral {f : ℕ → ℂ} {z : ℂ} {c : ℝ} (hc : 0 < c)
    (hf : LSeriesSummable f (z + c)) (L : ℝ) :
    ∑' n : ℕ, LSeries.term f z n * ((max (L - Real.log n) 0 : ℝ) : ℂ) =
      ∫ w : ℝ, LSeries f (z + contour c w) * (cexp (contour c w * L) / contour c w ^ 2) := by
  set T : ℕ → ℝ → ℂ := fun n w =>
    LSeries.term f (z + contour c w) n * (cexp (contour c w * L) / contour c w ^ 2) with hT
  have hTeq : ∀ n w, T n w = LSeries.term f z n *
      (cexp (((c : ℂ) + 2 * Real.pi * w * I) * ((L - Real.log n : ℝ) : ℂ)) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 2) := by
    intro n w
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hT]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp only [hT, contour]
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
        Complex.cpow_add _ _ hnC]
      have hlog : (n : ℂ) ^ ((c : ℂ) + 2 * Real.pi * w * I) =
          cexp (((c : ℂ) + 2 * Real.pi * w * I) * (Real.log n : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
        ring_nf
      rw [hlog]
      have he : cexp (((c : ℂ) + 2 * Real.pi * w * I) * ((L - Real.log n : ℝ) : ℂ)) =
          cexp (((c : ℂ) + 2 * Real.pi * w * I) * L) /
            cexp (((c : ℂ) + 2 * Real.pi * w * I) * (Real.log n : ℂ)) := by
        rw [← Complex.exp_sub]; push_cast; ring_nf
      rw [he]
      field_simp
  have hint : ∀ n, Integrable (T n) := fun n => by
    have := (integrable_perron_integrand hc (L - Real.log n)).const_mul (LSeries.term f z n)
    exact this.congr (Eventually.of_forall fun w => (hTeq n w).symm)
  have hstep1 : ∀ n, ∫ w, T n w = LSeries.term f z n * ((max (L - Real.log n) 0 : ℝ) : ℂ) := by
    intro n
    rw [integral_congr_ae (Eventually.of_forall (hTeq n)), integral_const_mul,
      perron_weighted_kernel hc]
  have hK : Integrable fun w : ℝ => (c ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
    have := (integrable_perron_integrand hc 0).norm
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only
    rw [norm_perron_integrand (a := c) 0 w, mul_zero, Real.exp_zero, one_div]
  have hnormint : ∀ n, ∫ w, ‖T n w‖ = ‖LSeries.term f (z + c) n‖ * Real.exp (c * L) *
      ∫ w : ℝ, (c ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
    intro n
    have hpt : ∀ w, ‖T n w‖ = ‖LSeries.term f (z + c) n‖ * Real.exp (c * L) *
        (c ^ 2 + (2 * Real.pi * w) ^ 2)⁻¹ := by
      intro w
      rw [hTeq, norm_mul, norm_perron_integrand]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
          Complex.norm_natCast_cpow_of_pos hnpos, Complex.norm_natCast_cpow_of_pos hnpos]
        have hre : (z + (c : ℂ)).re = z.re + c := by simp
        rw [hre, Real.rpow_add hn0, mul_sub, Real.exp_sub,
          show Real.exp (c * Real.log n) = (n : ℝ) ^ c by
            rw [Real.rpow_def_of_pos hn0, mul_comm]]
        have h1 : 0 < (n : ℝ) ^ z.re := Real.rpow_pos_of_pos hn0 _
        have h2 : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hn0 _
        field_simp
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  have hsum : Summable fun n => ∫ w, ‖T n w‖ := by
    simp_rw [hnormint]
    exact ((summable_norm_iff.mpr hf).mul_right (Real.exp (c * L))).mul_right _
  have hstep3 : ∀ w, ∑' n, T n w =
      LSeries f (z + contour c w) * (cexp (contour c w * L) / contour c w ^ 2) := by
    intro w
    simp only [hT]
    rw [tsum_mul_right]
    rfl
  calc ∑' n : ℕ, LSeries.term f z n * ((max (L - Real.log n) 0 : ℝ) : ℂ)
      = ∑' n : ℕ, ∫ w, T n w := tsum_congr fun n => (hstep1 n).symm
    _ = ∫ w, ∑' n, T n w := integral_tsum_of_summable_integral_norm hint hsum
    _ = _ := integral_congr_ae (Eventually.of_forall hstep3)

/-! ### The order-two kernel `1/s³` -/

theorem contour_ne_zero {c : ℝ} (hc : 0 < c) (w : ℝ) : contour c w ≠ 0 := fun h => by
  have := congrArg Complex.re h
  rw [contour_re] at this
  simp at this
  linarith

theorem integrable_inv_sub_mul_perron {c : ℝ} (hc : 0 < c) (L : ℝ) {b : ℂ} (hb : b.re < c) :
    Integrable fun w : ℝ => 1 / (contour c w - b) * (cexp (contour c w * L) / contour c w ^ 2) := by
  have hP : Integrable fun w : ℝ => cexp (contour c w * L) / contour c w ^ 2 :=
    integrable_perron_integrand hc L
  refine hP.bdd_mul (c := 1 / (c - b.re)) ?_ (Eventually.of_forall fun w => ?_)
  · refine (Continuous.aestronglyMeasurable ?_)
    have hne : ∀ w : ℝ, contour c w - b ≠ 0 := fun w h0 => by
      have := congrArg Complex.re h0
      simp [contour] at this
      linarith
    simp only [contour] at hne ⊢
    exact continuous_const.div (by fun_prop) hne
  · rw [norm_div, norm_one]
    have hlow : c - b.re ≤ ‖contour c w - b‖ := by
      have h := Complex.abs_re_le_norm (contour c w - b)
      rw [Complex.sub_re, contour_re] at h
      linarith [le_abs_self (c - b.re)]
    exact one_div_le_one_div_of_le (by linarith) hlow

/-- **The order-two Perron kernel.**  `∫ e^{sL}/s³ dw = (L⁺)²/2`. -/
theorem integral_perron_cube {c : ℝ} (hc : 0 < c) (L : ℝ) :
    ∫ w : ℝ, cexp (contour c w * L) / contour c w ^ 3 = ((max L 0 ^ 2 / 2 : ℝ) : ℂ) := by
  have h := integral_inv_sub_mul_perron hc L (b := 0) (by simpa using hc)
  have hl : ∀ w : ℝ, 1 / (contour c w - 0) * (cexp (contour c w * L) / contour c w ^ 2) =
      cexp (contour c w * L) / contour c w ^ 3 := fun w => by
    rw [sub_zero]; field_simp [contour_ne_zero hc w]
  simp_rw [hl] at h
  rw [h]
  simp only [zero_mul, Complex.exp_zero, one_mul]
  rcases le_total 0 L with hL | hL
  · have h0 : ∫ u in Ioi (0 : ℝ), ((max (L - u) 0 : ℝ) : ℂ) = ∫ u in (0 : ℝ)..L, ((L - u : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_of_le hL]
      have hU : Ioi (0 : ℝ) = Ioc 0 L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL).symm
      have hz : ∀ u ∈ Ioi L, ((max (L - u) 0 : ℝ) : ℂ) = 0 := fun u hu => by
        rw [mem_Ioi] at hu; rw [max_eq_right (by linarith), Complex.ofReal_zero]
      have hcont : Continuous fun u : ℝ => ((max (L - u) 0 : ℝ) : ℂ) := by fun_prop
      rw [hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        ((integrableOn_zero).congr_fun (fun u hu => (hz u hu).symm) measurableSet_Ioi),
        setIntegral_congr_fun measurableSet_Ioi hz, integral_zero, add_zero]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      rw [max_eq_left (by linarith [hu.2])]
    rw [h0, intervalIntegral.integral_ofReal]
    congr 1
    rw [intervalIntegral.integral_sub (f := fun _ => L) (g := fun x => x)
      intervalIntegrable_const (continuous_id.intervalIntegrable 0 L)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id, max_eq_left hL]
    ring
  · have hz : ∀ u ∈ Ioi (0 : ℝ), ((max (L - u) 0 : ℝ) : ℂ) = 0 := fun u hu => by
      rw [mem_Ioi] at hu; rw [max_eq_right (by linarith), Complex.ofReal_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hz, integral_zero, max_eq_right hL]
    simp

theorem integrable_perron_cube {c : ℝ} (hc : 0 < c) (L : ℝ) :
    Integrable fun w : ℝ => cexp (contour c w * L) / contour c w ^ 3 := by
  have h := integrable_inv_sub_mul_perron hc L (b := 0) (by simpa using hc)
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only
  rw [sub_zero]; field_simp [contour_ne_zero hc w]

/-- **The order-two pole integral.**  For `Re b < c`, `b ≠ 0`, `L ≥ 0`:
`∫ e^{sL}/(s³(s − b)) dw = (e^{bL} − 1 − bL − b²L²/2)/b³`. -/
theorem integral_inv_sub_mul_perron_cube_eq {c : ℝ} (hc : 0 < c) {L : ℝ} (hL : 0 ≤ L) {b : ℂ}
    (hb : b.re < c) (hb0 : b ≠ 0) :
    ∫ w : ℝ, 1 / (contour c w - b) * (cexp (contour c w * L) / contour c w ^ 3) =
      (cexp (b * L) - 1 - b * L - b ^ 2 * L ^ 2 / 2) / b ^ 3 := by
  have hpf : ∀ w : ℝ, 1 / (contour c w - b) * (cexp (contour c w * L) / contour c w ^ 3) =
      b⁻¹ * (1 / (contour c w - b) * (cexp (contour c w * L) / contour c w ^ 2) -
        cexp (contour c w * L) / contour c w ^ 3) := by
    intro w
    have h1 := contour_ne_zero hc w
    have h2 : contour c w - b ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0
      simp [contour] at this
      linarith
    field_simp
    ring
  simp_rw [hpf]
  rw [integral_const_mul, integral_sub (integrable_inv_sub_mul_perron hc L hb)
    (integrable_perron_cube hc L), integral_inv_sub_mul_perron_eq hc hL hb hb0,
    integral_perron_cube hc L, max_eq_left hL]
  field_simp
  push_cast
  ring

theorem norm_perron_cube (c u w : ℝ) :
    ‖cexp (contour c w * u) / contour c w ^ 3‖ = Real.exp (c * u) / ‖contour c w‖ ^ 3 := by
  rw [norm_div, Complex.norm_exp, norm_pow]
  congr 2
  simp [contour]

/-- **The order-two weighted Perron formula for a Dirichlet series.**  If `Σ f(n) n^{−(z+c)}`
converges absolutely (`c > 0`), then for every `L ∈ ℝ`
`Σ_n f(n) n^{−z} ((L − log n)⁺)²/2 = ∫ L(f, z + s) e^{sL}/s³ dw` on `s = c + 2πiw`. -/
theorem tsum_term_mul_sq_eq_integral {f : ℕ → ℂ} {z : ℂ} {c : ℝ} (hc : 0 < c)
    (hf : LSeriesSummable f (z + c)) (L : ℝ) :
    ∑' n : ℕ, LSeries.term f z n * ((max (L - Real.log n) 0 ^ 2 / 2 : ℝ) : ℂ) =
      ∫ w : ℝ, LSeries f (z + contour c w) * (cexp (contour c w * L) / contour c w ^ 3) := by
  set T : ℕ → ℝ → ℂ := fun n w =>
    LSeries.term f (z + contour c w) n * (cexp (contour c w * L) / contour c w ^ 3) with hT
  have hTeq : ∀ n w, T n w = LSeries.term f z n *
      (cexp (contour c w * ((L - Real.log n : ℝ) : ℂ)) / contour c w ^ 3) := by
    intro n w
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hT]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp only [hT]
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC]
      have hlog : (n : ℂ) ^ contour c w = cexp (contour c w * (Real.log n : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
        ring_nf
      rw [hlog]
      have he : cexp (contour c w * ((L - Real.log n : ℝ) : ℂ)) =
          cexp (contour c w * L) / cexp (contour c w * (Real.log n : ℂ)) := by
        rw [← Complex.exp_sub]; push_cast; ring_nf
      rw [he]
      field_simp
  have hint : ∀ n, Integrable (T n) := fun n => by
    have := (integrable_perron_cube hc (L - Real.log n)).const_mul (LSeries.term f z n)
    exact this.congr (Eventually.of_forall fun w => (hTeq n w).symm)
  have hstep1 : ∀ n, ∫ w, T n w =
      LSeries.term f z n * ((max (L - Real.log n) 0 ^ 2 / 2 : ℝ) : ℂ) := by
    intro n
    rw [integral_congr_ae (Eventually.of_forall (hTeq n)), integral_const_mul,
      integral_perron_cube hc]
  have hK : Integrable fun w : ℝ => 1 / ‖contour c w‖ ^ 3 := by
    have := (integrable_perron_cube hc 0).norm
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only
    rw [norm_perron_cube, mul_zero, Real.exp_zero]
  have hnormint : ∀ n, ∫ w, ‖T n w‖ = ‖LSeries.term f (z + c) n‖ * Real.exp (c * L) *
      ∫ w : ℝ, 1 / ‖contour c w‖ ^ 3 := by
    intro n
    have hpt : ∀ w, ‖T n w‖ = ‖LSeries.term f (z + c) n‖ * Real.exp (c * L) *
        (1 / ‖contour c w‖ ^ 3) := by
      intro w
      rw [hTeq, norm_mul, norm_perron_cube]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
          Complex.norm_natCast_cpow_of_pos hnpos, Complex.norm_natCast_cpow_of_pos hnpos]
        have hre : (z + (c : ℂ)).re = z.re + c := by simp
        rw [hre, Real.rpow_add hn0, mul_sub, Real.exp_sub,
          show Real.exp (c * Real.log n) = (n : ℝ) ^ c by
            rw [Real.rpow_def_of_pos hn0, mul_comm]]
        have h1 : 0 < (n : ℝ) ^ z.re := Real.rpow_pos_of_pos hn0 _
        have h2 : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hn0 _
        have h3 : 0 < ‖contour c w‖ := norm_pos_iff.mpr (contour_ne_zero hc w)
        field_simp
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  have hsum : Summable fun n => ∫ w, ‖T n w‖ := by
    simp_rw [hnormint]
    exact ((summable_norm_iff.mpr hf).mul_right (Real.exp (c * L))).mul_right _
  have hstep3 : ∀ w, ∑' n, T n w =
      LSeries f (z + contour c w) * (cexp (contour c w * L) / contour c w ^ 3) := by
    intro w
    simp only [hT]
    rw [tsum_mul_right]
    rfl
  calc ∑' n : ℕ, LSeries.term f z n * ((max (L - Real.log n) 0 ^ 2 / 2 : ℝ) : ℂ)
      = ∑' n : ℕ, ∫ w, T n w := tsum_congr fun n => (hstep1 n).symm
    _ = ∫ w, ∑' n, T n w := integral_tsum_of_summable_integral_norm hint hsum
    _ = _ := integral_congr_ae (Eventually.of_forall hstep3)

/-- The weighted Perron kernel times a `3/4`-power growth is `O((1 + |w|)^{−5/4})`. -/
theorem perron_bound_mul_rpow_le {c L C w : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    Real.exp (c * L) / (c ^ 2 + (2 * π * w) ^ 2) * (C * (1 + |w|) ^ (3 / 4 : ℝ)) ≤
      C * Real.exp (c * L) * (2 / min (c ^ 2) 1) * (1 + ‖w‖) ^ (-(5 / 4 : ℝ)) := by
  rw [Real.norm_eq_abs]
  set Y : ℝ := 1 + |w| with hY
  have hY0 : 0 < Y := by rw [hY]; positivity
  set m : ℝ := min (c ^ 2) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  have hmc : m ≤ c ^ 2 := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  have hden : 0 < c ^ 2 + (2 * π * w) ^ 2 := by positivity
  have hrp : Y ^ (-(5 / 4 : ℝ)) = Y ^ (3 / 4 : ℝ) / Y ^ 2 := by
    rw [show (-(5 / 4 : ℝ)) = 3 / 4 - (2 : ℕ) by norm_num, Real.rpow_sub hY0, Real.rpow_natCast]
  rw [hrp]
  have hkey : m * Y ^ 2 ≤ 2 * (c ^ 2 + (2 * π * w) ^ 2) := by
    have h1 : Y ^ 2 ≤ 2 * (1 + w ^ 2) := by
      rw [hY]; nlinarith [sq_abs w, abs_nonneg w, sq_nonneg (1 - |w|)]
    have h2 : m * (1 + w ^ 2) ≤ c ^ 2 + (2 * π * w) ^ 2 := by
      have hpi : 1 ≤ (2 * π) ^ 2 := by nlinarith [Real.two_le_pi]
      have : m * w ^ 2 ≤ (2 * π * w) ^ 2 := by
        rw [mul_pow]; nlinarith [sq_nonneg w]
      nlinarith
    nlinarith
  have hYp : 0 ≤ Y ^ (3 / 4 : ℝ) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  have e : C * Real.exp (c * L) * (2 / m) * (Y ^ (3 / 4 : ℝ) / Y ^ 2) *
      (c ^ 2 + (2 * π * w) ^ 2) = C * Real.exp (c * L) * Y ^ (3 / 4 : ℝ) *
        (2 * (c ^ 2 + (2 * π * w) ^ 2) / (m * Y ^ 2)) := by
    field_simp
  rw [e]
  have h1 : 1 ≤ 2 * (c ^ 2 + (2 * π * w) ^ 2) / (m * Y ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h0 : 0 ≤ C * Real.exp (c * L) * Y ^ (3 / 4 : ℝ) := by positivity
  nlinarith

end PerronPole

end RHTower
