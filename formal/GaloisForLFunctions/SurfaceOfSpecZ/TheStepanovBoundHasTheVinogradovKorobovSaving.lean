import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovBoundHasTheClassicalSaving
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovZeroFree

/-!
# The Stepanov bound has the Vinogradov–Korobov saving

With the Vinogradov–Korobov zero-free region `β ≤ 1 − (log t)^{−2/3}(log log t)^{−5/3}/10⁸`
(`RHTower.Sieve.riemannZeta_ne_zero_vinogradovKorobov`) in place of de la Vallée Poussin's, the spline
traces of `ζ` satisfy, unconditionally,

  `‖S(u)‖ ≤ C e^{u/2 − u^{3/5}/(10⁸ log u)}`   (`exists_norm_lagStructure_le_vk`, `u ≥ e`),

so the smoothed prime count in the window of `n` is its archimedean-plus-pole prediction up to
`O(√n exp(−(log n)^{3/5}/(10⁸ log log n)))` (`exists_abs_primeWindow_sub_archPoleWindow_le_vk`).

A zero `ρ = β + it` above height `t₀` costs `(1 + |t|)^{−6} e^{(β−½)u} ≤ e^{u/2 − (6L + u w(L))}`,
`L = log |t|`, `w(L) = L^{−2/3}(log L)^{−5/3}/10⁸`, and `6L + u w(L) ≥ u^{3/5}/(10⁸ log u)`
(`vk_budget`): for `L ≥ u^{3/5}/log u` the first term pays, below it `L ≤ u` and the width pays. The
finitely many lower zeros have `β ≤ 1 − δ` and `u^{3/5} ≤ δu + δ^{−3/2}` (`rpow_three_fifths_le`).
The saving `u^{3/5}` is the exponent of the zero-free region; any power saving in `e^{u/2}` itself
is a zero-free strip (`TheWidthLawAtEveryGapSet`).
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### The zeros of `ζ` -/

/-- **The Vinogradov–Korobov region** for the zeros of the configuration of `ζ`. -/
theorem exists_re_le_vk : ∃ t₀ : ℝ, Real.exp (Real.exp 1) ≤ t₀ ∧
    ∀ ρ ∈ zetaZeroConfig.carrier, t₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - Real.log |ρ.im| ^ (-(2 : ℝ) / 3) * Real.log (Real.log |ρ.im|) ^ (-(5 : ℝ) / 3) /
        10 ^ 8 := by
  obtain ⟨γ₀, hγ₀⟩ := _root_.RHTower.Sieve.riemannZeta_ne_zero_vinogradovKorobov
  refine ⟨max γ₀ (Real.exp (Real.exp 1)), le_max_right _ _, fun ρ hρ ht => ?_⟩
  have hγ : γ₀ ≤ |ρ.im| := le_trans (le_max_left _ _) ht
  have hxi :=
    (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
      hρ).1
  have hζ := (_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1
  by_contra hlt
  push Not at hlt
  rcases le_or_gt 0 ρ.im with h0 | h0
  · rw [abs_of_nonneg h0] at hγ hlt
    refine hγ₀ ρ.re ρ.im hγ hlt ?_
    rw [Complex.re_add_im]; exact hζ
  · rw [abs_of_neg h0] at hγ hlt
    refine hγ₀ ρ.re (-ρ.im) hγ hlt ?_
    have hc := riemannZeta_conj ρ
    rw [hζ, map_zero] at hc
    have e : (starRingEnd ℂ) ρ = (ρ.re : ℂ) + ((-ρ.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [← e]; exact hc

/-- **The low zeros.** The finitely many zeros below height `T₀` lie left of `1 − δ`. -/
theorem exists_low_margin_below (T₀ : ℝ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| < T₀ → ρ.re ≤ 1 - δ := by
  have hfin := zetaZeroConfig.finite_window (-T₀) T₀
  set S := zetaZeroConfig.carrier ∩ {ρ : ℂ | -T₀ < ρ.im ∧ ρ.im ≤ T₀} with hS
  have hmem : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| < T₀ → ρ ∈ S := fun ρ hρ h =>
    ⟨hρ, by have := abs_lt.mp h; exact ⟨this.1, this.2.le⟩⟩
  by_cases hne : S.Nonempty
  · obtain ⟨ρ₁, hρ₁, hmax⟩ := Set.exists_max_image S Complex.re hfin hne
    have h1 : ρ₁.re < 1 :=
      (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
        hρ₁.1).2.2
    refine ⟨1 - ρ₁.re, by linarith, fun ρ hρ him => ?_⟩
    have := hmax ρ (hmem ρ hρ him)
    linarith
  · exact ⟨1, one_pos, fun ρ hρ him => absurd ⟨ρ, hmem ρ hρ him⟩ hne⟩

/-! ### The optimization -/

/-- `u · (u^{3/5}/log u)^{−2/3} · (log u)^{−5/3} = u^{3/5}/log u`. -/
theorem mul_rpow_budget_eq {u : ℝ} (hu : 1 < u) :
    u * ((u ^ ((3 : ℝ) / 5) / Real.log u) ^ (-(2 : ℝ) / 3) * Real.log u ^ (-(5 : ℝ) / 3)) =
      u ^ ((3 : ℝ) / 5) / Real.log u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos hu
  rw [Real.div_rpow (by positivity) hl.le, ← Real.rpow_mul hu0.le]
  have e1 : u * (u ^ ((3 : ℝ) / 5 * (-(2 : ℝ) / 3))) = u ^ ((3 : ℝ) / 5) := by
    rw [show (3 : ℝ) / 5 * (-(2 : ℝ) / 3) = -(2 : ℝ) / 5 by norm_num]
    calc u * u ^ (-(2 : ℝ) / 5) = u ^ (1 : ℝ) * u ^ (-(2 : ℝ) / 5) := by rw [Real.rpow_one]
      _ = u ^ ((1 : ℝ) + -(2 : ℝ) / 5) := (Real.rpow_add hu0 _ _).symm
      _ = u ^ ((3 : ℝ) / 5) := by norm_num
  have e2 : Real.log u ^ (-(5 : ℝ) / 3) / Real.log u ^ (-(2 : ℝ) / 3) = 1 / Real.log u := by
    rw [← Real.rpow_sub hl, show -(5 : ℝ) / 3 - -(2 : ℝ) / 3 = -1 by norm_num, Real.rpow_neg_one,
      one_div]
  have hpos : 0 < Real.log u ^ (-(2 : ℝ) / 3) := Real.rpow_pos_of_pos hl _
  calc u * (u ^ ((3 : ℝ) / 5 * (-(2 : ℝ) / 3)) / Real.log u ^ (-(2 : ℝ) / 3) *
        Real.log u ^ (-(5 : ℝ) / 3))
      = (u * u ^ ((3 : ℝ) / 5 * (-(2 : ℝ) / 3))) *
          (Real.log u ^ (-(5 : ℝ) / 3) / Real.log u ^ (-(2 : ℝ) / 3)) := by
        field_simp
    _ = u ^ ((3 : ℝ) / 5) / Real.log u := by rw [e1, e2]; ring

/-- **The budget of a zero above `t₀`.** For `u ≥ e` and `L ≥ e`:
`u^{3/5}/(10⁸ log u) ≤ 6L + u L^{−2/3}(log L)^{−5/3}/10⁸`. -/
theorem vk_budget {u L : ℝ} (hu : Real.exp 1 ≤ u) (hL : Real.exp 1 ≤ L) :
    u ^ ((3 : ℝ) / 5) / (10 ^ 8 * Real.log u) ≤
      6 * L + u * (L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3) / 10 ^ 8) := by
  have he : (1 : ℝ) < Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hu1 : 1 < u := lt_of_lt_of_le he hu
  have hL1 : 1 < L := lt_of_lt_of_le he hL
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < L := by linarith
  have hlu : 1 ≤ Real.log u := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hu
  have hlL : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hL
  set X : ℝ := u ^ ((3 : ℝ) / 5) / Real.log u with hX
  have hX0 : 0 < X := by positivity
  have hsec : 0 ≤ u * (L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3) / 10 ^ 8) := by positivity
  have hgoal : u ^ ((3 : ℝ) / 5) / (10 ^ 8 * Real.log u) = X / 10 ^ 8 := by
    rw [hX]; field_simp
  rw [hgoal]
  rcases le_or_gt X L with hXL | hXL
  · nlinarith
  · -- `L < X ≤ u`, so the width pays
    have hXu : X ≤ u := by
      have h35 : u ^ ((3 : ℝ) / 5) ≤ u := by
        calc u ^ ((3 : ℝ) / 5) ≤ u ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hu1.le (by norm_num)
          _ = u := Real.rpow_one u
      rw [hX, div_le_iff₀ (by linarith)]; nlinarith
    have hLu : L ≤ u := hXL.le.trans hXu
    have h1 : X ^ (-(2 : ℝ) / 3) ≤ L ^ (-(2 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_nonpos hL0 hXL.le (by norm_num)
    have h2 : Real.log u ^ (-(5 : ℝ) / 3) ≤ Real.log L ^ (-(5 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (Real.log_le_log hL0 hLu) (by norm_num)
    have h3 : u * (X ^ (-(2 : ℝ) / 3) * Real.log u ^ (-(5 : ℝ) / 3)) ≤
        u * (L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) hu0.le
    rw [hX, mul_rpow_budget_eq hu1] at h3
    have h4 : u * (L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3) / 10 ^ 8) =
        u * (L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3)) / 10 ^ 8 := by ring
    rw [h4, hX]
    have h5 : 0 ≤ 6 * L := by positivity
    have h6 : u ^ ((3 : ℝ) / 5) / Real.log u / 10 ^ 8 ≤
        u * (L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3)) / 10 ^ 8 :=
      div_le_div_of_nonneg_right h3 (by norm_num)
    linarith

/-- `u^{3/5} ≤ δu + δ^{−3/2}` for `u ≥ 0`, `δ > 0`. -/
theorem rpow_three_fifths_le {u δ : ℝ} (hu : 0 ≤ u) (hδ : 0 < δ) :
    u ^ ((3 : ℝ) / 5) ≤ δ * u + δ ^ (-(3 : ℝ) / 2) := by
  have hδ0 : 0 ≤ δ ^ (-(3 : ℝ) / 2) := by positivity
  set c : ℝ := δ ^ (-(5 : ℝ) / 2) with hc
  have hc0 : 0 < c := by positivity
  rcases le_or_gt c u with hcu | hcu
  · -- `u^{−2/5} ≤ c^{−2/5} = δ`
    have hu0 : 0 < u := lt_of_lt_of_le hc0 hcu
    have h1 : u ^ (-(2 : ℝ) / 5) ≤ c ^ (-(2 : ℝ) / 5) :=
      Real.rpow_le_rpow_of_nonpos hc0 hcu (by norm_num)
    have h2 : c ^ (-(2 : ℝ) / 5) = δ := by
      rw [hc, ← Real.rpow_mul hδ.le]; norm_num
    have h3 : u ^ ((3 : ℝ) / 5) = u * u ^ (-(2 : ℝ) / 5) := by
      calc u ^ ((3 : ℝ) / 5) = u ^ ((1 : ℝ) + -(2 : ℝ) / 5) := by norm_num
        _ = u ^ (1 : ℝ) * u ^ (-(2 : ℝ) / 5) := Real.rpow_add hu0 _ _
        _ = u * u ^ (-(2 : ℝ) / 5) := by rw [Real.rpow_one]
    rw [h3]
    have := mul_le_mul_of_nonneg_left (h1.trans h2.le) hu
    linarith
  · have h1 : u ^ ((3 : ℝ) / 5) ≤ c ^ ((3 : ℝ) / 5) :=
      Real.rpow_le_rpow hu hcu.le (by norm_num)
    have h2 : c ^ ((3 : ℝ) / 5) = δ ^ (-(3 : ℝ) / 2) := by
      rw [hc, ← Real.rpow_mul hδ.le]; norm_num
    have := mul_nonneg hδ.le hu
    linarith

/-- The saving `c(u) = u^{3/5}/(10⁸ log u)`. -/
def vkSaving (u : ℝ) : ℝ := u ^ ((3 : ℝ) / 5) / (10 ^ 8 * Real.log u)

/-- **The weight of one zero.** For `u ≥ e`: `(1 + |t|)^{−6} e^{(β − ½)u} ≤ K e^{u/2 − c(u)}`. -/
theorem pow_mul_exp_le_vk {t₀ δ : ℝ} (ht₀ : Real.exp (Real.exp 1) ≤ t₀) (hδ : 0 < δ)
    (hvk : ∀ ρ ∈ zetaZeroConfig.carrier, t₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - Real.log |ρ.im| ^ (-(2 : ℝ) / 3) * Real.log (Real.log |ρ.im|) ^ (-(5 : ℝ) / 3) /
        10 ^ 8)
    (hlow : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| < t₀ → ρ.re ≤ 1 - δ) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) {u : ℝ} (hu : Real.exp 1 ≤ u) :
    1 / (1 + |ρ.im|) ^ 6 * Real.exp ((ρ.re - 1 / 2) * u) ≤
      Real.exp (δ ^ (-(3 : ℝ) / 2)) * Real.exp (u / 2 - vkSaving u) := by
  have he1 : (1 : ℝ) < Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hu1 : 1 < u := lt_of_lt_of_le he1 hu
  have hu0 : 0 ≤ u := by linarith
  have hlu : 1 ≤ Real.log u := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hu
  have hK1 : 1 ≤ Real.exp (δ ^ (-(3 : ℝ) / 2)) := Real.one_le_exp (by positivity)
  -- the saving is at most `u^{3/5}`
  have hcu : vkSaving u ≤ u ^ ((3 : ℝ) / 5) := by
    unfold vkSaving
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ u ^ ((3 : ℝ) / 5) := by positivity
    nlinarith
  rcases lt_or_ge |ρ.im| t₀ with hlo | hhi
  · have hβ := hlow ρ hρ hlo
    have h1 : 1 / (1 + |ρ.im|) ^ 6 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by linarith [abs_nonneg ρ.im])
    have h2 : Real.exp ((ρ.re - 1 / 2) * u) ≤
        Real.exp (δ ^ (-(3 : ℝ) / 2)) * Real.exp (u / 2 - vkSaving u) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h3 := rpow_three_fifths_le hu0 hδ
      have h4 : (ρ.re - 1 / 2) * u ≤ (1 / 2 - δ) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu0
      nlinarith
    calc 1 / (1 + |ρ.im|) ^ 6 * Real.exp ((ρ.re - 1 / 2) * u)
        ≤ 1 * Real.exp ((ρ.re - 1 / 2) * u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := by rw [one_mul]; exact h2
  · have hβ := hvk ρ hρ hhi
    set t := |ρ.im| with htdef
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht₀ |>.trans_le hhi
    set L := Real.log t with hLdef
    have hL : Real.exp 1 ≤ L := by
      rw [hLdef, ← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) (ht₀.trans hhi)
    have h1 : 1 / (1 + t) ^ 6 ≤ Real.exp (-(6 * L)) := by
      have : Real.exp (-(6 * L)) = 1 / t ^ 6 := by
        rw [Real.exp_neg, show 6 * L = ((6 : ℕ) : ℝ) * L by norm_num, Real.exp_nat_mul, hLdef,
          Real.exp_log ht0, one_div]
      rw [this]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ht0.le (by linarith) 6)
    set w : ℝ := L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3) / 10 ^ 8 with hw
    have h2 : (ρ.re - 1 / 2) * u ≤ u / 2 - u * w := by
      have : ρ.re - 1 / 2 ≤ 1 / 2 - w := by rw [hw]; linarith
      have := mul_le_mul_of_nonneg_right this hu0
      linarith
    have h3 := vk_budget hu hL
    calc 1 / (1 + t) ^ 6 * Real.exp ((ρ.re - 1 / 2) * u)
        ≤ Real.exp (-(6 * L)) * Real.exp (u / 2 - u * w) :=
          mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (u / 2 - (6 * L + u * w)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (u / 2 - vkSaving u) := by
          refine Real.exp_le_exp.mpr ?_
          rw [← hw] at h3
          unfold vkSaving; linarith
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le hK1

/-! ### The saving -/

/-- **Summation over the zeros.** A uniform bound `W` on `(1 + |t|)^{−6} e^{(β − ½)u}` gives
`‖S(u)‖ ≤ 2A² W Σ m/(1 + |γ|²)`, `A = 2⁴ e²`. -/
theorem norm_lagStructure_le_of_weight {u W : ℝ}
    (hW : ∀ ρ ∈ zetaZeroConfig.carrier, 1 / (1 + |ρ.im|) ^ 6 * Real.exp ((ρ.re - 1 / 2) * u) ≤ W) :
    ‖lagStructure zetaZeroConfig (boxSpline 1 3) u‖ ≤
      2 * (2 ^ (3 + 1) * Real.exp ((3 + 1) / 2)) ^ 2 * W *
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := by
  set A : ℝ := 2 ^ (3 + 1) * Real.exp ((3 + 1) / 2)
  have hT := temperedConfig_zetaZeroConfig
  unfold TemperedConfig at hT
  set f : zetaZeroConfig.carrier → ℂ := fun ρ => (zetaZeroConfig.mult ρ : ℂ) *
    paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) (gammaOf ρ) * cexp (I * gammaOf ρ * u)
  have hb := (contDiff_boxSpline (r := 1) one_pos 2).continuous
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  have hterm : ∀ ρ : zetaZeroConfig.carrier, ‖f ρ‖ ≤
      2 * A ^ 2 * W * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hρ := ρ.2
    have hstrip :=
      (_root_.RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp
        hρ).2
    set w := gammaOf (ρ : ℂ)
    set t := (ρ : ℂ).im
    have hwre : w.re = t := gammaOf_re _
    have hwim : w.im = 1 / 2 - (ρ : ℂ).re := gammaOf_im _
    have hwim2 : |w.im| ≤ 1 / 2 := by rw [hwim, abs_le]; constructor <;> linarith
    have hty : |t| ≤ ‖w‖ := by rw [← hwre]; exact Complex.abs_re_le_norm w
    have hB1 := norm_paperFT_boxSpline_le' 3 hwim2 (abs_nonneg t) hty
    have hcim : |(conj w).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hwim2
    have hcn : |t| ≤ ‖conj w‖ := by rw [Complex.norm_conj]; exact hty
    have hB2 := norm_paperFT_boxSpline_le' 3 hcim (abs_nonneg t) hcn
    have hF : ‖paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) w‖ ≤ A ^ 2 / (1 + |t|) ^ 8 := by
      rw [EF.paperFT_weilTest hb hb hbc hbc, norm_mul, Complex.norm_conj]
      calc ‖paperFT (boxSpline 1 3) w‖ * ‖paperFT (boxSpline 1 3) (conj w)‖
          ≤ (A / (1 + |t|) ^ (3 + 1)) * (A / (1 + |t|) ^ (3 + 1)) :=
            mul_le_mul hB1 hB2 (norm_nonneg _) (by positivity)
        _ = A ^ 2 / (1 + |t|) ^ 8 := by field_simp; ring
    have hE : ‖cexp (I * w * u)‖ = Real.exp (((ρ : ℂ).re - 1 / 2) * u) := by
      rw [Complex.norm_exp]
      congr 1
      have : I * w * u = ((ρ : ℂ) - 1 / 2) * u := by
        simp only [w, gammaOf]; field_simp
      rw [this]; simp
    have hWρ := hW (ρ : ℂ) hρ
    have hnorm : 1 + Complex.normSq w ≤ 2 * (1 + |t|) ^ 2 := by
      rw [Complex.normSq_apply, hwre, hwim]
      have h1 : ((1 / 2 - (ρ : ℂ).re) * (1 / 2 - (ρ : ℂ).re)) ≤ 1 := by nlinarith
      nlinarith [abs_nonneg t, sq_abs t]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hpos : 0 < 1 + Complex.normSq w := by have := Complex.normSq_nonneg w; linarith
    simp only [f]
    rw [norm_mul, norm_mul, Complex.norm_natCast, hE]
    have key : A ^ 2 / (1 + |t|) ^ 8 * Real.exp (((ρ : ℂ).re - 1 / 2) * u) ≤
        2 * A ^ 2 * W * (1 / (1 + Complex.normSq w)) := by
      have h6 : A ^ 2 / (1 + |t|) ^ 8 * Real.exp (((ρ : ℂ).re - 1 / 2) * u) =
          A ^ 2 * (1 / (1 + |t|) ^ 2) *
            (1 / (1 + |t|) ^ 6 * Real.exp (((ρ : ℂ).re - 1 / 2) * u)) := by
        field_simp
      have h7 : 1 / (1 + |t|) ^ 2 ≤ 2 * (1 / (1 + Complex.normSq w)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
        linarith
      rw [h6]
      calc A ^ 2 * (1 / (1 + |t|) ^ 2) *
            (1 / (1 + |t|) ^ 6 * Real.exp (((ρ : ℂ).re - 1 / 2) * u))
          ≤ A ^ 2 * (2 * (1 / (1 + Complex.normSq w))) * W :=
            mul_le_mul (mul_le_mul_of_nonneg_left h7 (by positivity)) hWρ (by positivity)
              (by positivity)
        _ = _ := by ring
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (EF.weilTest (boxSpline 1 3) (boxSpline 1 3)) w‖ *
          Real.exp (((ρ : ℂ).re - 1 / 2) * u)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (A ^ 2 / (1 + |t|) ^ 8) *
            Real.exp (((ρ : ℂ).re - 1 / 2) * u) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hm) (Real.exp_pos _).le
      _ = (zetaZeroConfig.mult ρ : ℝ) * (A ^ 2 / (1 + |t|) ^ 8 *
            Real.exp (((ρ : ℂ).re - 1 / 2) * u)) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (2 * A ^ 2 * W * (1 / (1 + Complex.normSq w))) :=
          mul_le_mul_of_nonneg_left key hm
      _ = _ := by ring
  have hsum : Summable fun ρ : zetaZeroConfig.carrier => ‖f ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hT.mul_left _)
  calc ‖lagStructure zetaZeroConfig (boxSpline 1 3) u‖ = ‖∑' ρ, f ρ‖ := rfl
    _ ≤ ∑' ρ, ‖f ρ‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' ρ : zetaZeroConfig.carrier, 2 * A ^ 2 * W *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) :=
        Summable.tsum_le_tsum hterm hsum (hT.mul_left _)
    _ = _ := by rw [tsum_mul_left]

/-- **The Vinogradov–Korobov saving.** Unconditionally, `‖S(u)‖ ≤ C e^{u/2 − u^{3/5}/(10⁸ log u)}`
for `u ≥ e`. -/
theorem exists_norm_lagStructure_le_vk : ∃ C : ℝ, ∀ u : ℝ, Real.exp 1 ≤ u →
    ‖lagStructure zetaZeroConfig (boxSpline 1 3) u‖ ≤ C * Real.exp (u / 2 - vkSaving u) := by
  obtain ⟨t₀, ht₀, hvk⟩ := exists_re_le_vk
  obtain ⟨δ, hδ, hlow⟩ := exists_low_margin_below t₀
  set A : ℝ := 2 ^ (3 + 1) * Real.exp ((3 + 1) / 2)
  set Sw := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
  refine ⟨2 * A ^ 2 * Real.exp (δ ^ (-(3 : ℝ) / 2)) * Sw, fun u hu => ?_⟩
  have h := norm_lagStructure_le_of_weight (u := u)
    (fun ρ hρ => pow_mul_exp_le_vk ht₀ hδ hvk hlow hρ hu)
  calc ‖lagStructure zetaZeroConfig (boxSpline 1 3) u‖
      ≤ 2 * A ^ 2 * (Real.exp (δ ^ (-(3 : ℝ) / 2)) * Real.exp (u / 2 - vkSaving u)) * Sw := h
    _ = 2 * A ^ 2 * Real.exp (δ ^ (-(3 : ℝ) / 2)) * Sw * Real.exp (u / 2 - vkSaving u) := by ring

/-- **The prime number theorem in every window, with the Vinogradov–Korobov error.** -/
theorem exists_abs_primeWindow_sub_archPoleWindow_le_vk : ∃ C : ℝ, ∀ n : ℕ,
    Real.exp (Real.exp 1) ≤ n →
    |primeWindow n - archPoleWindow n| ≤
      C * Real.sqrt n *
        Real.exp (-(Real.log n ^ ((3 : ℝ) / 5) / (10 ^ 8 * Real.log (Real.log n)))) := by
  obtain ⟨C, hC⟩ := exists_norm_lagStructure_le_vk
  refine ⟨C, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have hlog : Real.exp 1 ≤ Real.log n := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hn
  have h := hC _ hlog
  have he : Real.exp (Real.log n / 2 - vkSaving (Real.log n)) =
      Real.sqrt n * Real.exp (-(Real.log n ^ ((3 : ℝ) / 5) / (10 ^ 8 * Real.log (Real.log n)))) := by
    have e1 : Real.exp (Real.log n / 2) = Real.sqrt n := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0]; ring_nf
    rw [sub_eq_add_neg, Real.exp_add, e1, vkSaving]
  have hid : primeWindow n - archPoleWindow n =
      -(lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)).re := by
    rw [← orbitCorr_eq_re_lagStructure_spline, orbitCorr_log_eq_archPoleWindow_sub_primeWindow]
    ring
  rw [hid, abs_neg]
  calc |(lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)).re|
      ≤ ‖lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)‖ := Complex.abs_re_le_norm _
    _ ≤ C * Real.exp (Real.log n / 2 - vkSaving (Real.log n)) := h
    _ = _ := by rw [he]; ring

end GaloisForLFunctions.SurfaceOfSpecZ
