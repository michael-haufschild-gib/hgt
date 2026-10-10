import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyZeroCascade
import GaloisForLFunctions.RHTower.RayPolylogMultiplicity

/-!
# The squarefree discrepancy is not `o(x^{1/4})`

Let `E(x) = #{n ≤ x squarefree} - (6/π²) x` and let `ρ` be a zero of `ζ` on the critical line of
order `m`.

* **Graded law** (`natCast_lt_of_squarefree_littleO`). If `E(x) = o(x^{1/4} (1 + log x)^a)`, then
  `m < a + 1`.
* **Ω-result** (`not_squarefree_littleO_quarter`). Unconditionally `E(x) ≠ o(x^{1/4})`, and more
  generally `E(x) ≠ o(x^{1/4} (1 + log x)^a)` whenever `a + 1 ≤ m`
  (`not_squarefree_littleO_of_le_order`).

**Proof.** A little-`o` bound gives `E = O(x^{1/4+ε})` for every `ε`, hence RH by the halving
cascade. Under RH, `ζ(ρ/2) ≠ 0`, because `Re(ρ/2) = 1/4`. The moment `G` is holomorphic on
`Re s > 1/4` with `(s - 1) s G(s) Z(2s) = (2s - 1) Z(s) - (6/π²) s Z(2s)`, where `Z(w) = (w - 1)ζ(w)`.
The factor `Z(2s)` vanishes to order `m` at `s₀ = ρ/2`, while the right side is
`(ρ - 1)(s₀ - 1)ζ(s₀) ≠ 0` there. The Mellin tail bound gives
`‖G(s₀ + r)‖ ≤ η r^{-(a+1)} + C_η`, and the ray lemma gives `m < a + 1`.
-/

open Filter Topology MeasureTheory Set Asymptotics Complex

namespace RHTower.SquarefreeDiscrepancy

noncomputable section

/-- `E(x) = o(x^{1/4} (1 + log x)^a)`, in explicit form. -/
def LittleOQuarter (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x →
    |error x| ≤ ε * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a

/-- A little-`o` bound is a global bound `|E(x)| ≤ B x^{1/4} (1 + log x)^a` on `x ≥ 1`. -/
theorem exists_global_of_littleOQuarter {a : ℝ} (ha : 0 ≤ a) (h : LittleOQuarter a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x →
      |error x| ≤ B * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := by
  obtain ⟨T, hT1, hT⟩ := h 1 one_pos
  refine ⟨max 1 (4 * Real.sqrt T), le_max_of_le_left zero_le_one, fun x hx => ?_⟩
  have hw : 1 ≤ x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hx (by norm_num))
      (Real.one_le_rpow (by linarith [Real.log_nonneg hx]) ha)
  rcases le_or_gt T x with hTx | hxT
  · calc |error x| ≤ 1 * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := hT x hTx
      _ ≤ max 1 (4 * Real.sqrt T) * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · calc |error x| ≤ 4 * Real.sqrt x := abs_error_le hx
      _ ≤ 4 * Real.sqrt T := by gcongr
      _ ≤ max 1 (4 * Real.sqrt T) := le_max_right _ _
      _ = max 1 (4 * Real.sqrt T) * 1 := (mul_one _).symm
      _ ≤ max 1 (4 * Real.sqrt T) * (x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a) :=
          mul_le_mul_of_nonneg_left hw (le_max_of_le_left zero_le_one)
      _ = max 1 (4 * Real.sqrt T) * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := by ring

/-- A polylogarithmic bound at the exponent `1/4` is a power bound at every exponent `1/4 + δ`. -/
theorem exists_power_bound_of_littleOQuarter {a : ℝ} (ha : 0 ≤ a) (h : LittleOQuarter a)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |error x| ≤ C * x ^ (1 / 4 + δ) := by
  obtain ⟨B, hB0, hB⟩ := exists_global_of_littleOQuarter ha h
  refine ⟨B * ((2 / (2 * δ)) ^ a * polylogConst a), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl := one_add_log_rpow_le ha (by linarith : 0 < 2 * δ) (by linarith) hx
  rw [show 2 * δ / 2 = δ by ring] at hl
  have e : x ^ (1 / 4 : ℝ) * x ^ δ = x ^ (1 / 4 + δ) := by rw [← Real.rpow_add hx0]
  calc |error x| ≤ B * x ^ (1 / 4 : ℝ) * (1 + Real.log x) ^ a := hB x hx
    _ ≤ B * x ^ (1 / 4 : ℝ) * ((2 / (2 * δ)) ^ a * polylogConst a * x ^ δ) := by gcongr
    _ = B * ((2 / (2 * δ)) ^ a * polylogConst a) * (x ^ (1 / 4 : ℝ) * x ^ δ) := by ring
    _ = B * ((2 / (2 * δ)) ^ a * polylogConst a) * x ^ (1 / 4 + δ) := by rw [e]

/-- A little-`o` bound at `x^{1/4}` with any logarithmic power implies RH. -/
theorem riemannHypothesis_of_littleOQuarter {a : ℝ} (ha : 0 ≤ a) (h : LittleOQuarter a) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_squarefree_quarter_bound fun ε hε => ?_
  obtain ⟨C, hC⟩ := exists_power_bound_of_littleOQuarter ha h (δ := min ε (1 / 2))
    (lt_min hε (by norm_num)) (min_le_right _ _)
  refine ⟨|C|, fun x hx => ?_⟩
  calc |error x| ≤ C * x ^ (1 / 4 + min ε (1 / 2)) := hC x hx
    _ ≤ |C| * x ^ (1 / 4 + min ε (1 / 2)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C| * x ^ (1 / 4 + ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith [min_le_left ε (1 / 2)])) (abs_nonneg C)

/-- Under RH, `ζ` has no zero on `Re s = 1/4`. -/
theorem riemannZeta_ne_zero_of_re_quarter (hRH : RiemannHypothesis) {s : ℂ}
    (hs : s.re = 1 / 4) : riemannZeta s ≠ 0 := by
  intro hz
  have h0 : 0 < s.re := by rw [hs]; norm_num
  have h1 : s.re < 1 := by rw [hs]; norm_num
  have hz' : riemannZeta (1 - s) = 0 := (riemannZeta_one_sub_eq_zero_iff h0 h1).mpr hz
  have hre : 1 / 2 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re, hs]; norm_num
  exact (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) (1 - s) hre hz'

/-- **Graded law at the exponent `1/4`.** If `ζ(z) = (z - ρ)^m g(z)` near a critical zero `ρ` and
`E(x) = o(x^{1/4} (1 + log x)^a)`, then `m < a + 1`. -/
theorem natCast_lt_of_squarefree_littleO {a : ℝ} (ha : 0 ≤ a) (h : LittleOQuarter a)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hz : riemannZeta ρ = 0) {m : ℕ} {g : ℂ → ℂ}
    (hg : ContinuousAt g ρ) (hfac : ∀ᶠ w in 𝓝 ρ, riemannZeta w = (w - ρ) ^ m • g w) :
    (m : ℝ) < a + 1 := by
  have hRH := riemannHypothesis_of_littleOQuarter ha h
  set s₀ : ℂ := ρ / 2 with hs₀
  have hs₀re : s₀.re = 1 / 4 := by
    rw [hs₀, Complex.div_re]; simp [hρ]; ring
  have hζs₀ : riemannZeta s₀ ≠ 0 := riemannZeta_ne_zero_of_re_quarter hRH hs₀re
  have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hρ; norm_num at hρ
  have hs₀1 : s₀ ≠ 1 := by
    intro h1; rw [h1, Complex.one_re] at hs₀re; norm_num at hs₀re
  have h2s₀ : 2 * s₀ = ρ := by rw [hs₀]; ring
  -- the factorisation of `(z - 1) z Z(2z)` at `s₀`
  set P : ℂ → ℂ := fun z => (z - 1) * z * ((2 * z - 1) * (2 ^ m * g (2 * z))) with hP
  have hdouble : Tendsto (fun z : ℂ => 2 * z) (𝓝 s₀) (𝓝 ρ) := by
    have := (continuous_const_mul (2 : ℂ)).tendsto s₀
    rwa [h2s₀] at this
  have hPc : ContinuousAt P s₀ := by
    have hgc : ContinuousAt (fun z : ℂ => g (2 * z)) s₀ := by
      rw [ContinuousAt, h2s₀]; exact hg.tendsto.comp hdouble
    exact ((continuousAt_id.sub continuousAt_const).mul continuousAt_id).mul
      (((continuousAt_const.mul continuousAt_id).sub continuousAt_const).mul
        (continuousAt_const.mul hgc))
  have hEfac : ∀ᶠ z in 𝓝 s₀,
      (z - 1) * z * zetaResidueUnit (2 * z) = (z - s₀) ^ m * P z := by
    have hne : ∀ᶠ z in 𝓝 s₀, 2 * z ≠ 1 :=
      hdouble.eventually (isOpen_compl_singleton.mem_nhds hρ1)
    filter_upwards [hdouble.eventually hfac, hne] with z hz1 hz2
    rw [zetaResidueUnit, Function.update_of_ne hz2]
    rw [hz1, smul_eq_mul, hP]
    have : 2 * z - ρ = 2 * (z - s₀) := by rw [← h2s₀]; ring
    rw [this, mul_pow]
    ring
  -- the right side of the identity at `s₀`
  set H : ℂ → ℂ := fun z => (2 * z - 1) * zetaResidueUnit z -
    (Sieve.squarefreeDensity : ℂ) * z * zetaResidueUnit (2 * z) with hH
  have hHc : ContinuousAt H s₀ :=
    (((continuousAt_const.mul continuousAt_id).sub continuousAt_const).mul
      (analyticAt_zetaResidueUnit s₀).continuousAt).sub
      ((continuousAt_const.mul continuousAt_id).mul
        ((analyticAt_zetaResidueUnit (2 * s₀)).continuousAt.comp
          (continuous_const.mul continuous_id).continuousAt))
  have hHs₀ : H s₀ ≠ 0 := by
    have hZρ : zetaResidueUnit (2 * s₀) = 0 := by
      rw [h2s₀, zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
    simp only [hH, hZρ, mul_zero, sub_zero]
    rw [zetaResidueUnit, Function.update_of_ne hs₀1, h2s₀]
    exact mul_ne_zero (sub_ne_zero.mpr hρ1) (mul_ne_zero (sub_ne_zero.mpr hs₀1) hζs₀)
  -- the identity along the ray
  have hray_re : ∀ r : ℝ, (s₀ + (r : ℂ) * 1).re = 1 / 4 + r := fun r => by simp [hs₀re]
  have hFE : ∀ᶠ r : ℝ in 𝓝[>] 0,
      moment (s₀ + r * 1) * ((s₀ + r * 1 - 1) * (s₀ + r * 1) * zetaResidueUnit (2 * (s₀ + r * 1)))
        = H (s₀ + r * 1) := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr hrI
    have hr0 : (0 : ℝ) < r := hr
    obtain ⟨C, hC⟩ := exists_power_bound_of_littleOQuarter ha h (δ := r / 2) (by linarith)
      (by linarith [hrI.2])
    have hid := moment_identity_of_bound (α := 1 / 4 + r / 2) (by linarith [hrI.2]) hC
      (s := s₀ + r * 1) (by rw [hray_re]; linarith)
    rw [hH]
    linear_combination hid
  -- the Mellin tail bound
  obtain ⟨B, hB0, hB⟩ := exists_global_of_littleOQuarter ha h
  have htail := norm_integral_Ioi_one_cpow_mul_le (f := fun t => (error t : ℂ))
    (c := 1 / 4) (a := a) (B := B) ha
    (fun t ht => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hB t ht.le)
    (fun ε hε => by
      obtain ⟨T, hT1, hT⟩ := h ε hε
      exact ⟨T, hT1, fun t ht => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hT t ht⟩)
  have hF : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ‖moment (s₀ + r * 1)‖ ≤ η * r ^ (-(a + 1)) + C := by
    intro η hη
    obtain ⟨C, hC⟩ := htail η hη
    refine ⟨C, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hrI
    have hb := hC (s₀ + r * 1) (by rw [hray_re]; linarith [hrI.1])
      (by rw [hray_re]; linarith [hrI.2])
    rw [hray_re, show (1 / 4 + r - 1 / 4 : ℝ) = r by ring] at hb
    rw [moment_eq_integral]
    have hcongr : (∫ x in Ioi (1 : ℝ), (error x : ℂ) * (x : ℂ) ^ (-(s₀ + r * 1 + 1))) =
        ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(s₀ + r * 1) - 1) * (error t : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [mul_comm, show -(s₀ + r * 1 + 1) = -(s₀ + r * 1) - 1 by ring]
    rw [hcongr]
    exact hb
  exact natCast_lt_of_ray_littleO (E := fun z => (z - 1) * z * zetaResidueUnit (2 * z))
    (F := moment) (H := H) (p := P) (v := 1) ha hPc hEfac hHc hHs₀ hFE hF

/-- **Graded Ω at the exponent `1/4`.** If a critical zero has order `m`, then
`E(x) ≠ o(x^{1/4} (1 + log x)^a)` for every `0 ≤ a` with `a + 1 ≤ m`. -/
theorem not_squarefree_littleO_of_le_order {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hz : riemannZeta ρ = 0)
    {a : ℝ} (ha : 0 ≤ a) (hm : a + 1 ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) :
    ¬ LittleOQuarter a := by
  intro h
  have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hρ; norm_num at hρ
  have hρpos : 0 < ρ.re := by rw [hρ]; norm_num
  have hρlt : ρ.re < 1 := by rw [hρ]; norm_num
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρlt⟩]
    exact xi_orderAt_ne_top ρ
  have hcoe : (((analyticOrderAt riemannZeta ρ).toNat : ℕ) : ℕ∞) = analyticOrderAt riemannZeta ρ :=
    ENat.coe_toNat hfin
  obtain ⟨g, hg, _, hfac⟩ :=
    ((analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_natCast).mp hcoe.symm
  have hlt := natCast_lt_of_squarefree_littleO ha h hρ hz hg.continuousAt hfac
  linarith

/-- **`E(x) ≠ o(x^{1/4})`**, unconditionally. -/
theorem not_squarefree_littleO_quarter : ¬ LittleOQuarter 0 := by
  obtain ⟨ρ, hρ, hz⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
  have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hρ; norm_num at hρ
  have hρpos : 0 < ρ.re := by rw [hρ]; norm_num
  have hρlt : ρ.re < 1 := by rw [hρ]; norm_num
  have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρlt⟩]
    exact xi_orderAt_ne_top ρ
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    rintro (h | h)
    exacts [h (analyticOn_riemannZeta ρ hρ1), h hz]
  have h1 : 1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    exact hne ((ENat.toNat_eq_zero.mp h).resolve_right hfin)
  exact not_squarefree_littleO_of_le_order hρ hz le_rfl
    (by simpa using (show (1 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) by
      exact_mod_cast h1))

end

end RHTower.SquarefreeDiscrepancy
