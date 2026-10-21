import GaloisForLFunctions.SquareRootThreshold.ZetaAttainedTopIsVisibleAtAnExplicitLag

/-!
# Twins are exponentially tight unless tripled

The twin law places a second zero within `O_w((1 + log log γ)/V)` of a hidden near-top record. A
twin can hide the record only by cancelling it, and the cancellation is fragile under a change of
the Fejér order: by the recursion
`(x² + β²) K_{k+1}(x) = c K_k(x)`, `β = (2k+2)π/V`, `c = (2k+2)(2k+1)(π/V)²`, the two windows of orders
`k` and `k + 1` give two linear forms in the two coefficients, and one combination eliminates the
twin exactly (`dipole_elimination`):
`(x₂² + β²) A_{k+1} − c A_k = D₁ (x₂ − x₁)(x₂ + x₁) K_{k+1}(x₁)`, `A_j = D₁ K_j(x₁) + D₂ K_j(x₂)`.

* **Cluster law** (`norm_sum_evenCoeff_mul_fejerPowWin_le`, `zeta_powCluster_le`). For any finite set
  `S` of exponents, `|Σ_{z ∈ S} D(z) K_j(z − s)|` is bounded by the potential of the exponents
  outside `S`; for `ζ`, with every exponent outside `S` at distance `≥ r` from `s`, by
  `(2j)!(π/V)^{2j} n_j` with the explicit bracket `n_j` (`clusterBracket`,
  `clusterBracket_le`: `n_j ≤ (4/3)^j (4|M| + 4W + 3840 L |D(z*)| e^κ)/r^{2j+1}`).
* **Dipole law** (`zeta_dipole_law`). If the record `z*` and one companion `z₂` are the only
  exponents within `r` of `s = z* − κ/V` and `|(z* − s) + (z₂ − s)| ≥ κ/V`, then
  `|D(z*)| |z₂ − z*| (e^κ − 1) V^{2k+2} ≤ (κ² + 4π²(k+1)²)^{k+1} ((5/4) r² n_{k+1} + n_k)`.
* **Mirror points** (`mirror_alternative`). The side condition fails only near the mirror point
  `z* − 2κ/V`; it holds at depth `κ` or at depth `4κ`.
* **Isolated twins** (`zeta_isolated_twin_tight`). If a companion within `r/2` of the record is
  the only other exponent within `2r`, then
  `|z₂ − z*| V^{2k+2} r^{2k+1} ≤ (8/3)(4/3)^k (16κ² + 4π²(k+1)²)^{k+1} (4(|M| + W)/((e − 1)ε₀) + 6144L)`.
* **Near-top twins of `ζ`** (`zeta_near_top_twin_tight_or_triple`). For a near-top zero above
  `T_w`, positivity of the modulated difference tests on `[0, V]`, `V ≥ V_w(z₀)`,
  `Vr ≥ 2(R_w + κ_w)` and `Vr ≥ 2(4 + 2π(k + 1))`: the record has two other zeros within `2r`, or
  a twin within `(4/3) A_w log(180(Γ + 6))(4 + 2π(k + 1))/(3^k V)` (`twinTightConstant`).

With `k + 1 ≍ Vr/(4π)` the twin distance is `≤ C_w log γ₀ · r e^{−c Vr}`, `c = log 3/(4π)`: an isolated
twin must sit exponentially close to its record. Hiding at a near-top zero therefore needs a cluster
of at least three zeros within `2r`, or a pair at distance `e^{−cVr}`; the elimination generalizes to
`n` orders and `n` cluster members through the Vandermonde structure of `1/(x² + β_j²)`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The record-potential law for a cluster -/

/-- **Cluster record-potential law.** If the difference tests are Weil nonnegative on `[0, V]`, then
for every finite set `S` of exponents and `s = σ + it`:
`|Σ_{z ∈ S} D(z) K_k(z − s)| ≤ |M|(|K_k(−σ)| + |K_k(−s)|) + Σ_z |D(z)||K_k(z − σ)|
  + Σ_{z ∉ S} |D(z)||K_k(z − s)|`. -/
theorem norm_sum_evenCoeff_mul_fejerPowWin_le (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V)
    (k : ℕ) (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    (S : Finset ℂ) (σ t : ℝ) :
    ‖∑ z ∈ S, evenCoeff Z b z * fejerPowWin k V (z - (σ + t * I))‖ ≤
      |2 * (lagStructure Z b 0).re| *
          (‖fejerPowWin k V (-σ)‖ + ‖fejerPowWin k V (-(σ + t * I))‖) +
      ∑' z : ℂ, ‖evenCoeff Z b z‖ * ‖fejerPowWin k V (z - σ)‖ +
      ∑' z : ℂ, (if z ∈ S then 0 else
        ‖evenCoeff Z b z‖ * ‖fejerPowWin k V (z - (σ + t * I))‖) := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  have hg : ∀ u ∈ Icc (0 : ℝ) V,
      0 ≤ Real.sin (π * u / V) ^ (2 * k) * (M - 2 * (lagStructure Z b u).re) := fun u hu => by
    have := hm u hu
    rw [re_W_lag_eq Z hZ hb hbs u] at this
    exact mul_nonneg (sin_pow_nonneg _ k) this
  have hG := integral_fejerPowWindow_eq Z hZ hb hbs hV k
  have hsumL : ∀ s : ℂ, Summable fun z : ℂ => ‖D z‖ * ‖fejerPowWin k V (z - s)‖ := fun s =>
    summable_norm_evenCoeff_mul Z hZ hb hbs (C := V * Real.exp ((1 / 2 + |s.re|) * V))
      (fun _ => norm_nonneg _) fun z hz => (norm_fejerPowWin_le_const hV k _).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by
          rw [Complex.sub_re]
          exact (abs_sub _ _).trans (by linarith [abs_re_le_of_evenCoeff_ne_zero hz]))
          hV)) hV)
  have hsumC : ∀ s : ℂ, Summable fun z : ℂ => D z * fejerPowWin k V (z - s) := fun s =>
    (hsumL s).of_norm_bounded fun z => (norm_mul _ _).le
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hpos := norm_integral_cexp_mul_le hV hg s
  rw [hsre] at hpos
  have hGs := hG s
  have hGσ := hG σ
  -- split off the cluster
  have hsplit : ∑' z : ℂ, D z * fejerPowWin k V (z - s) =
      ∑ z ∈ S, D z * fejerPowWin k V (z - s) +
        ∑' z : ℂ, (if z ∈ S then 0 else D z * fejerPowWin k V (z - s)) := by
    have h2 := tsum_subtype ((↑S)ᶜ : Set ℂ) (fun z => D z * fejerPowWin k V (z - s))
    rw [← (hsumC s).sum_add_tsum_compl (s := S), h2]
    congr 1
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_notMem (by simpa using hz), if_pos hz]
    · rw [Set.indicator_of_mem (by simpa using hz), if_neg hz]
  have hrest : ‖∑' z : ℂ, (if z ∈ S then 0 else D z * fejerPowWin k V (z - s))‖ ≤
      ∑' z : ℂ, (if z ∈ S then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) := by
    have hn : ∀ z : ℂ, ‖(if z ∈ S then 0 else D z * fejerPowWin k V (z - s))‖ =
        (if z ∈ S then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) := fun z => by
      split_ifs <;> simp
    have hs' : Summable fun z : ℂ => (if z ∈ S then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) :=
      (hsumL s).of_nonneg_of_le (fun z => by split_ifs <;> positivity)
        fun z => by split_ifs <;> first | positivity | exact le_rfl
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hn)
    simp_rw [hn]
    exact hs'
  have hGre : ((M : ℂ) * fejerPowWin k V (-(σ : ℂ)) - ∑' z : ℂ, D z * fejerPowWin k V (z - σ)).re ≤
      |M| * ‖fejerPowWin k V (-σ)‖ + ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ := by
    rw [Complex.sub_re]
    have h1 : ((M : ℂ) * fejerPowWin k V (-(σ : ℂ))).re ≤ |M| * ‖fejerPowWin k V (-σ)‖ := by
      refine (Complex.re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : -(∑' z : ℂ, D z * fejerPowWin k V (z - σ)).re ≤
        ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ := by
      refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
      refine (norm_tsum_le_tsum_norm (hsumC σ).norm).trans_eq ?_
      simp
    linarith
  set Gs := ∫ u in (0 : ℝ)..V, cexp (-s * u) *
    ((Real.sin (π * u / V) ^ (2 * k) * (M - 2 * (lagStructure Z b u).re) : ℝ) : ℂ) with hGsdef
  set R := ∑' z : ℂ, (if z ∈ S then 0 else D z * fejerPowWin k V (z - s)) with hRdef
  have hkey : ∑ z ∈ S, D z * fejerPowWin k V (z - s) = M * fejerPowWin k V (-s) - Gs - R := by
    rw [hGs, hsplit]; ring
  rw [hkey]
  have htri : ‖(M : ℂ) * fejerPowWin k V (-s) - Gs - R‖ ≤
      ‖(M : ℂ) * fejerPowWin k V (-s)‖ + ‖Gs‖ + ‖R‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_sub_le ((M : ℂ) * fejerPowWin k V (-s)) Gs])
  have hMn : ‖(M : ℂ) * fejerPowWin k V (-s)‖ = |M| * ‖fejerPowWin k V (-s)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hGb : ‖Gs‖ ≤ |M| * ‖fejerPowWin k V (-σ)‖ +
      ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ := by
    refine hpos.trans ?_
    rw [hGσ]
    exact hGre
  have hs1 : (-s : ℂ) = -(σ + t * I) := by rw [hs]
  rw [← hs1]
  linarith

/-- **Noise of an isolated cluster for `ζ`.** Let `z*` be the Legendre record at lag `V`, `j ≥ 1`,
`V ≥ πj`, `σ = Re z* − κ/V > 0`, `s = σ + i Im z*`, `0 < r ≤ 4`, `Vr ≥ 4πj`, and let every exponent
outside a finite set `S` keep distance `r` from `s`. If the difference tests are Weil nonnegative on
`[0, V]`, then
`|Σ_{z ∈ S} D(z) K_j(z − s)| ≤ (2j)!(π/V)^{2j} (|M|(2/σ^{2j+1} + 2(4/3)^j/4^{2j+1})
  + (4/3)^j (|D(z*)| e^κ Π/r^{2j−2} + 2W(1/4^{2j+1} + 1/r^{2j+1})))`, `Π = twinPotential r (Im z*)`. -/
theorem zeta_powCluster_le {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {j : ℕ} (hj : 1 ≤ j) {V : ℝ} (hV : π * j ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hσ : 0 < z₁.re - κ / V) (hr : 0 < r) (hr4 : r ≤ 4)
    (hVr : 4 * π * j ≤ V * r) (S : Finset ℂ)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖) :
    ‖∑ z ∈ S, evenCoeff zetaZeroConfig b z *
        fejerPowWin j V (z - ((z₁.re - κ / V : ℝ) + z₁.im * I))‖ ≤
      (2 * j).factorial * (π / V) ^ (2 * j) *
        (|2 * (lagStructure zetaZeroConfig b 0).re| *
            (2 / (z₁.re - κ / V) ^ (2 * j + 1) + 2 * (4 / 3) ^ j / 4 ^ (2 * j + 1)) +
          (4 / 3) ^ j * (‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp κ *
              (twinPotential r z₁.im / r ^ (2 * j - 2)) +
            2 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) *
              (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1)))) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set σ : ℝ := z₁.re - κ / V with hσdef
  have hk0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hθV : κ / V * V = κ := by field_simp
  set s : ℂ := (σ : ℂ) + z₁.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = z₁.im := by simp [hs]
  set ck : ℝ := (4 / 3) ^ j with hck
  set uk : ℝ := (2 * j).factorial * (π / V) ^ (2 * j) with huk
  have hck0 : 0 < ck := by positivity
  have huk0 : 0 < uk := by positivity
  have hcore := norm_sum_evenCoeff_mul_fejerPowWin_le zetaZeroConfig temperedConfig_zetaZeroConfig
    hb hbs hV0.le j hm S σ z₁.im
  rw [← hs] at hcore
  -- the loudness of every exponent, relative to the record
  have hloud : ∀ z, D z ≠ 0 → ‖D z‖ * Real.exp ((z.re - σ) * V) ≤ ‖D z₁‖ * Real.exp κ + ‖D z‖ :=
    fun z hz => by
      by_cases hre : 0 < z.re
      · have h := hrec z hz hre
        have e1 : ‖D z‖ * Real.exp ((z.re - σ) * V) =
            ‖D z‖ * Real.exp (z.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        have e2 : ‖D z₁‖ * Real.exp κ = ‖D z₁‖ * Real.exp (z₁.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hσdef]; linarith [hθV]
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-σ * V)).le
        linarith [norm_nonneg (D z)]
      · push Not at hre
        have : Real.exp ((z.re - σ) * V) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hV0.le)
        have := mul_le_mul_of_nonneg_left this (norm_nonneg (D z))
        have := mul_nonneg (norm_nonneg (D z₁)) (Real.exp_pos κ).le
        linarith
  -- potential kernels
  have hkern : ∀ {z u : ℂ} {d : ℝ}, 0 < d → 4 * π * j ≤ V * d → u.re = σ → D z ≠ 0 →
      d ≤ ‖z - u‖ → ‖D z‖ * ‖fejerPowWin j V (z - u)‖ ≤
        ck * uk * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3 / d ^ (2 * j - 2)) +
          2 * ‖D z‖ / d ^ (2 * j + 1)) := by
    intro z u d hd hVd hu hz hgap
    have hzu : 0 < ‖z - u‖ := lt_of_lt_of_le hd hgap
    have h4 : 4 * π * j ≤ V * ‖z - u‖ := hVd.trans (mul_le_mul_of_nonneg_left hgap hV0.le)
    have hdec := norm_fejerPowWin_le_decay hV0 j (norm_pos_iff.mp hzu) h4
    rw [Complex.sub_re, hu] at hdec
    have hp1 := one_div_pow_le_cube hd hgap hj
    have hp2 : 1 / ‖z - u‖ ^ (2 * j + 1) ≤ 1 / d ^ (2 * j + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hd.le hgap _)
    have hl := hloud z hz
    calc ‖D z‖ * ‖fejerPowWin j V (z - u)‖
        ≤ ‖D z‖ * ((4 / 3) ^ j * (2 * j).factorial * (π / V) ^ (2 * j) *
            (Real.exp ((z.re - σ) * V) + 1) / ‖z - u‖ ^ (2 * j + 1)) :=
          mul_le_mul_of_nonneg_left hdec (norm_nonneg _)
      _ = ck * uk * ((‖D z‖ * Real.exp ((z.re - σ) * V) + ‖D z‖) *
            (1 / ‖z - u‖ ^ (2 * j + 1))) := by rw [hck, huk]; field_simp
      _ ≤ ck * uk * ((‖D z₁‖ * Real.exp κ + 2 * ‖D z‖) * (1 / ‖z - u‖ ^ (2 * j + 1))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          linarith
      _ ≤ ck * uk * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3 / d ^ (2 * j - 2)) +
            2 * ‖D z‖ / d ^ (2 * j + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [add_mul, show 2 * ‖D z‖ / d ^ (2 * j + 1) = 2 * ‖D z‖ * (1 / d ^ (2 * j + 1)) by
            ring]
          exact add_le_add (mul_le_mul_of_nonneg_left hp1 (by positivity))
            (mul_le_mul_of_nonneg_left hp2 (by positivity))
  -- the potential sums
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
  obtain ⟨hs0, hP0b⟩ := tsum_inv_cube_le (b := b) (s := (σ : ℂ)) (r := 4) (by norm_num)
    (fun z => D z ≠ 0) fun z hz => ⟨hz, (four_le_abs_im_of_evenCoeff_zeta hz).trans (by
      have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this)⟩
  obtain ⟨hs1, hP1b⟩ := tsum_inv_cube_le (b := b) (s := s) hr
    (fun z => D z ≠ 0 ∧ z ∉ S) fun z hz => ⟨hz.1, hiso z hz.2 hz.1⟩
  rw [show (|((σ : ℂ)).im| : ℝ) = 0 by simp, zero_add] at hP0b
  rw [hsim] at hP1b
  set P0 : ℝ := ∑' z : ℂ, (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) with hP0
  set P1 : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ z ∉ S then 1 / ‖z - s‖ ^ 3 else 0) with hP1
  have hV4 : 4 * π * j ≤ V * 4 := by linarith
  have hP0 : ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin j V (z - σ)‖ ≤
      ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2)) + 2 * W / 4 ^ (2 * j + 1)) := by
    have hle : ∀ z : ℂ, ‖D z‖ * ‖fejerPowWin j V (z - σ)‖ ≤ ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) / 4 ^ (2 * j - 2)) +
          2 * ‖D z‖ / 4 ^ (2 * j + 1)) := fun z => by
      by_cases hz : D z = 0
      · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, if_false, zero_div,
          mul_zero, zero_add]
        positivity
      · rw [if_pos hz]
        exact hkern (by norm_num) hV4 (by simp) hz
          ((four_le_abs_im_of_evenCoeff_zeta hz).trans (by
            have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
    have hR : Summable fun z : ℂ => ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) / 4 ^ (2 * j - 2)) +
          2 * ‖D z‖ / 4 ^ (2 * j + 1)) :=
      (((hs0.div_const _).mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le (fun _ => by positivity) hle) hR).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add ((hs0.div_const _).mul_left _)
      ((hsD.mul_left 2).div_const _), tsum_mul_left, tsum_div_const, tsum_div_const, tsum_mul_left]
  have hP1 : ∑' z : ℂ, (if z ∈ S then 0 else ‖D z‖ * ‖fejerPowWin j V (z - s)‖) ≤
      ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * j - 2)) + 2 * W / r ^ (2 * j + 1)) := by
    have hle : ∀ z : ℂ, (if z ∈ S then 0 else ‖D z‖ * ‖fejerPowWin j V (z - s)‖) ≤ ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 ∧ z ∉ S then 1 / ‖z - s‖ ^ 3 else 0) /
          r ^ (2 * j - 2)) + 2 * ‖D z‖ / r ^ (2 * j + 1)) := fun z => by
      have hc0' : 0 ≤ ck * uk := by positivity
      by_cases hzS : z ∈ S
      · rw [if_pos hzS]; split_ifs <;> positivity
      · rw [if_neg hzS]
        by_cases hz : D z = 0
        · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, false_and, if_false,
            zero_div, mul_zero, zero_add]
          positivity
        · rw [if_pos ⟨hz, hzS⟩]
          exact hkern hr hVr hsre hz (hiso z hzS hz)
    have hR : Summable fun z : ℂ => ck * uk *
        (‖D z₁‖ * Real.exp κ * ((if D z ≠ 0 ∧ z ∉ S then 1 / ‖z - s‖ ^ 3 else 0) /
          r ^ (2 * j - 2)) + 2 * ‖D z‖ / r ^ (2 * j + 1)) :=
      (((hs1.div_const _).mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le
      (fun z => by positivity) hle) hR).trans (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add ((hs1.div_const _).mul_left _)
      ((hsD.mul_left 2).div_const _), tsum_mul_left, tsum_div_const, tsum_div_const, tsum_mul_left]
  -- the archimedean-pole kernels
  have hE1 : ‖fejerPowWin j V (-(σ : ℂ))‖ ≤ uk * (2 / σ ^ (2 * j + 1)) := by
    have := norm_fejerPowWin_neg_le hV0 j hσ
    rw [huk]; refine this.trans (le_of_eq ?_); ring
  have hE2 : ‖fejerPowWin j V (-s)‖ ≤ uk * (2 * ck / 4 ^ (2 * j + 1)) := by
    have h4 : (4 : ℝ) ≤ ‖s‖ := (four_le_abs_im_of_evenCoeff_zeta hz₁).trans (by
      rw [← hsim]; exact Complex.abs_im_le_norm s)
    have hs0' : -s ≠ 0 := fun h => by
      rw [neg_eq_zero] at h; rw [h, norm_zero] at h4; norm_num at h4
    have hdec := norm_fejerPowWin_le_decay hV0 j hs0' (by
      rw [norm_neg]; exact hV4.trans (mul_le_mul_of_nonneg_left h4 hV0.le))
    rw [norm_neg, Complex.neg_re, hsre] at hdec
    refine hdec.trans ?_
    have he : Real.exp (-σ * V) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) hV0.le)
    have hpow : (4 : ℝ) ^ (2 * j + 1) ≤ ‖s‖ ^ (2 * j + 1) := pow_le_pow_left₀ (by norm_num) h4 _
    calc (4 / 3) ^ j * ((2 * j).factorial : ℝ) * (π / V) ^ (2 * j) * (Real.exp (-σ * V) + 1) /
          ‖s‖ ^ (2 * j + 1)
        ≤ (4 / 3) ^ j * ((2 * j).factorial : ℝ) * (π / V) ^ (2 * j) * 2 / 4 ^ (2 * j + 1) := by
          gcongr; linarith
      _ = uk * (2 * ck / 4 ^ (2 * j + 1)) := by rw [huk, hck]; ring
  -- assemble
  set Pb : ℝ := twinPotential r z₁.im with hPb
  have hPle : P0 + P1 ≤ Pb := by
    have h0 : P0 ≤ 480 * Real.log 1080 * (1 / 64 + 3) := by
      refine hP0b.trans (le_of_eq ?_); norm_num
    rw [hPb, twinPotential]; linarith [hP1b]
  have hP0' : 0 ≤ P0 := tsum_nonneg fun z => by split_ifs <;> positivity
  have hP1' : 0 ≤ P1 := tsum_nonneg fun z => by split_ifs <;> positivity
  have hr4' : 1 / (4 : ℝ) ^ (2 * j - 2) ≤ 1 / r ^ (2 * j - 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le hr4 _)
  have hPr : P0 / 4 ^ (2 * j - 2) + P1 / r ^ (2 * j - 2) ≤ Pb / r ^ (2 * j - 2) := by
    have h1 : P0 / 4 ^ (2 * j - 2) ≤ P0 / r ^ (2 * j - 2) := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div P0]
      exact mul_le_mul_of_nonneg_left hr4' hP0'
    calc P0 / 4 ^ (2 * j - 2) + P1 / r ^ (2 * j - 2) ≤ P0 / r ^ (2 * j - 2) + P1 / r ^ (2 * j - 2) := by
          linarith
      _ = (P0 + P1) / r ^ (2 * j - 2) := by rw [add_div]
      _ ≤ Pb / r ^ (2 * j - 2) := div_le_div_of_nonneg_right hPle (by positivity)
  have hDe : 0 ≤ ‖D z₁‖ * Real.exp κ := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine hcore.trans ?_
  have h1 : |M| * (‖fejerPowWin j V (-(σ : ℂ))‖ + ‖fejerPowWin j V (-s)‖) ≤
      uk * (|M| * (2 / σ ^ (2 * j + 1) + 2 * ck / 4 ^ (2 * j + 1))) := by
    calc |M| * (‖fejerPowWin j V (-(σ : ℂ))‖ + ‖fejerPowWin j V (-s)‖) ≤
          |M| * (uk * (2 / σ ^ (2 * j + 1)) + uk * (2 * ck / 4 ^ (2 * j + 1))) :=
          mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) (abs_nonneg M)
      _ = _ := by ring
  have h2 : ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2)) + 2 * W / 4 ^ (2 * j + 1)) +
      ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * j - 2)) + 2 * W / r ^ (2 * j + 1)) ≤
      uk * (ck * (‖D z₁‖ * Real.exp κ * (Pb / r ^ (2 * j - 2)) +
        2 * W * (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1)))) := by
    have := mul_le_mul_of_nonneg_left hPr hDe
    have e : ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2)) + 2 * W / 4 ^ (2 * j + 1)) +
        ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * j - 2)) + 2 * W / r ^ (2 * j + 1)) =
        uk * (ck * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2) + P1 / r ^ (2 * j - 2)) +
          2 * W * (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1)))) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ huk0.le
    have := mul_le_mul_of_nonneg_left this hck0.le
    linarith
  linarith

/-! ### The dipole law -/

/-- The cluster bracket `n_j = |M|(2/σ^{2j+1} + 2(4/3)^j/4^{2j+1})
  + (4/3)^j(|D(z*)|e^κ Π/r^{2j−2} + 2W(1/4^{2j+1} + 1/r^{2j+1}))`. -/
def clusterBracket (j : ℕ) (M W D σ κ r Pb : ℝ) : ℝ :=
  |M| * (2 / σ ^ (2 * j + 1) + 2 * (4 / 3) ^ j / 4 ^ (2 * j + 1)) +
    (4 / 3) ^ j * (D * Real.exp κ * (Pb / r ^ (2 * j - 2)) +
      2 * W * (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1)))

/-- **Elimination of the twin.** Two consecutive Fejér powers see a pair of exponents through
`(x₂² + β²) A_{k+1} − c A_k = D₁ (x₂² − x₁²) K_{k+1}(x₁)`, `A_j = D₁ K_j(x₁) + D₂ K_j(x₂)`,
`β = (2k+2)π/V`, `c = (2k+2)(2k+1)(π/V)²`. -/
theorem dipole_elimination {V : ℝ} (hV : 0 < V) (k : ℕ) (D₁ D₂ x₁ x₂ : ℂ) :
    (x₂ ^ 2 + (((2 * k + 2) * π / V : ℝ) : ℂ) ^ 2) *
        (D₁ * fejerPowWin (k + 1) V x₁ + D₂ * fejerPowWin (k + 1) V x₂) -
      (((2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 : ℝ) : ℂ) *
        (D₁ * fejerPowWin k V x₁ + D₂ * fejerPowWin k V x₂) =
      D₁ * (x₂ - x₁) * (x₂ + x₁) * fejerPowWin (k + 1) V x₁ := by
  have h1 := fejerPowWin_succ hV k x₁
  have h2 := fejerPowWin_succ hV k x₂
  linear_combination D₁ * h1 + D₂ * h2

/-- **Dipole law for `ζ`.** Under the hypotheses of `zeta_powCluster_le` at the orders `k` and `k + 1`
(`k ≥ 1`, `V ≥ π(k + 1)`, `0 < r ≤ 4`, `Vr ≥ 4π(k + 1)`), let `z₂ ≠ z*` be an exponent with
`|z₂ − s| ≤ r` and `|(z* − s) + (z₂ − s)| ≥ κ/V`, and let every other exponent keep distance `r` from
`s`. Then
`|D(z*)| |z₂ − z*| (e^κ − 1) V^{2k+2} ≤ (κ² + 4π²(k+1)²)^{k+1} ((5/4) r² n_{k+1} + n_k)`. -/
theorem zeta_dipole_law {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {k : ℕ} (hk : 1 ≤ k) {V : ℝ} (hV : π * (k + 1) ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hσ : 0 < z₁.re - κ / V) (hr : 0 < r) (hr4 : r ≤ 4)
    (hVr : 4 * π * (k + 1) ≤ V * r) {z₂ : ℂ} (hz₂ : z₂ ≠ z₁)
    (hz₂r : ‖z₂ - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ ≤ r)
    (hsum : κ / V ≤ ‖(z₁ - ((z₁.re - κ / V : ℝ) + z₁.im * I)) +
      (z₂ - ((z₁.re - κ / V : ℝ) + z₁.im * I))‖)
    (hiso : ∀ z, z ≠ z₁ → z ≠ z₂ → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖) :
    ‖evenCoeff zetaZeroConfig b z₁‖ * ‖z₂ - z₁‖ * (Real.exp κ - 1) * V ^ (2 * k + 2) ≤
      (κ ^ 2 + 4 * π ^ 2 * (k + 1 : ℕ) ^ 2) ^ (k + 1) *
        (5 / 4 * r ^ 2 * clusterBracket (k + 1) (2 * (lagStructure zetaZeroConfig b 0).re)
            (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) ‖evenCoeff zetaZeroConfig b z₁‖
            (z₁.re - κ / V) κ r (twinPotential r z₁.im) +
          clusterBracket k (2 * (lagStructure zetaZeroConfig b 0).re)
            (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) ‖evenCoeff zetaZeroConfig b z₁‖
            (z₁.re - κ / V) κ r (twinPotential r z₁.im)) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  set S : Finset ℂ := {z₁, z₂} with hS
  have hisoS : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    exact hiso z hz.1 hz.2 hDz
  have hsumS : ∀ j : ℕ, ∑ z ∈ S, D z * fejerPowWin j V (z - s) =
      D z₁ * fejerPowWin j V (z₁ - s) + D z₂ * fejerPowWin j V (z₂ - s) := fun j => by
    rw [hS, Finset.sum_pair hz₂.symm]
  -- the two cluster bounds
  have hA1 := zeta_powCluster_le hb hbs (j := k + 1) (by omega) (by push_cast; linarith) hm hz₁ hrec
    hκ hσ hr hr4 (by push_cast; linarith) S hisoS
  have hA0 := zeta_powCluster_le hb hbs (j := k) hk (by nlinarith [Real.pi_pos]) hm hz₁ hrec
    hκ hσ hr hr4 (by nlinarith [Real.pi_pos]) S hisoS
  rw [hsumS] at hA1 hA0
  set n1 := clusterBracket (k + 1) (2 * (lagStructure zetaZeroConfig b 0).re)
    (∑' z : ℂ, ‖D z‖) ‖D z₁‖ (z₁.re - κ / V) κ r (twinPotential r z₁.im) with hn1
  set n0 := clusterBracket k (2 * (lagStructure zetaZeroConfig b 0).re)
    (∑' z : ℂ, ‖D z‖) ‖D z₁‖ (z₁.re - κ / V) κ r (twinPotential r z₁.im) with hn0
  set u1 : ℝ := (2 * (k + 1)).factorial * (π / V) ^ (2 * (k + 1)) with hu1
  set u0 : ℝ := (2 * k).factorial * (π / V) ^ (2 * k) with hu0
  have hA1' : ‖D z₁ * fejerPowWin (k + 1) V (z₁ - s) + D z₂ * fejerPowWin (k + 1) V (z₂ - s)‖ ≤
      u1 * n1 := by rw [hu1, hn1, clusterBracket]; exact hA1
  have hA0' : ‖D z₁ * fejerPowWin k V (z₁ - s) + D z₂ * fejerPowWin k V (z₂ - s)‖ ≤ u0 * n0 := by
    rw [hu0, hn0, clusterBracket]; exact hA0
  -- elimination
  set c : ℝ := (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 with hc
  set β : ℝ := (2 * k + 2) * π / V with hβ
  have hcu : c * u0 = u1 := by
    rw [hc, hu0, hu1, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, show (2 * k + 1) + 1 = 2 * k + 2 by ring, pow_add]
    push_cast; ring
  have hid := dipole_elimination hV0 k (D z₁) (D z₂) (z₁ - s) (z₂ - s)
  rw [← hβ, ← hc, show z₂ - s - (z₁ - s) = z₂ - z₁ by ring] at hid
  have hβr : 2 * β ≤ r := by
    rw [hβ, show 2 * ((2 * k + 2) * π / V) = 4 * π * (k + 1) / V by ring, div_le_iff₀ hV0]
    linarith
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hq : ‖(z₂ - s) ^ 2 + ((β : ℝ) : ℂ) ^ 2‖ ≤ 5 / 4 * r ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
    have := pow_le_pow_left₀ (norm_nonneg _) hz₂r 2
    nlinarith
  have hnorm := congrArg norm hid
  rw [norm_mul, norm_mul, norm_mul] at hnorm
  have hle : ‖D z₁‖ * ‖z₂ - z₁‖ * ‖(z₂ - s) + (z₁ - s)‖ * ‖fejerPowWin (k + 1) V (z₁ - s)‖ ≤
      5 / 4 * r ^ 2 * (u1 * n1) + c * (u0 * n0) := by
    rw [← hnorm]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by rw [hc]; positivity)]
    exact add_le_add (mul_le_mul hq hA1' (norm_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_left hA0' (by rw [hc]; positivity))
  -- the record kernel at depth `κ/V`
  have hx₁ : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  have hθ0 : 0 < κ / V := div_pos hκ hV0
  have hlow := norm_fejerPowWin_ofReal_ge hV0 (k + 1) hθ0
  rw [← hx₁] at hlow
  set Q : ℝ := (κ ^ 2 + 4 * π ^ 2 * (k + 1 : ℕ) ^ 2) ^ (k + 1) with hQ
  have hQ0 : 0 < Q := by positivity
  have hlow' : u1 * (Real.exp κ - 1) * V ^ (2 * k + 3) / (κ * Q) ≤
      ‖fejerPowWin (k + 1) V (z₁ - s)‖ := by
    refine le_trans (le_of_eq ?_) hlow
    have hVne : V ≠ 0 := hV0.ne'
    have hκne : κ ≠ 0 := hκ.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + 1 : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * (k + 1 : ℕ) ^ 2) / V ^ 2 := by field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu1, hQ, div_pow, div_pow, ← pow_mul V 2 (k + 1),
      show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 3 = (2 * k + 2) + 1 by ring, pow_succ]
    field_simp
    ring
  have hsum' : κ / V ≤ ‖(z₂ - s) + (z₁ - s)‖ := by rw [add_comm]; exact hsum
  have hu10 : 0 < u1 := by rw [hu1]; positivity
  have hD0 : 0 ≤ ‖D z₁‖ * ‖z₂ - z₁‖ := by positivity
  have hexp : 0 ≤ Real.exp κ - 1 := by linarith [Real.one_le_exp hκ.le]
  have hchain : ‖D z₁‖ * ‖z₂ - z₁‖ * (κ / V) * (u1 * (Real.exp κ - 1) * V ^ (2 * k + 3) / (κ * Q)) ≤
      5 / 4 * r ^ 2 * (u1 * n1) + u1 * n0 := by
    refine le_trans ?_ (hle.trans (le_of_eq (by rw [← hcu]; ring)))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsum' hD0) hlow' (by positivity) (by positivity)
  have e2 : ‖D z₁‖ * ‖z₂ - z₁‖ * (κ / V) * (u1 * (Real.exp κ - 1) * V ^ (2 * k + 3) / (κ * Q)) =
      u1 * (‖D z₁‖ * ‖z₂ - z₁‖ * (Real.exp κ - 1) * V ^ (2 * k + 2) / Q) := by
    have hVne : V ≠ 0 := hV0.ne'
    have hκne : κ ≠ 0 := hκ.ne'
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by ring, pow_succ]
    field_simp
  rw [e2, show 5 / 4 * r ^ 2 * (u1 * n1) + u1 * n0 = u1 * (5 / 4 * r ^ 2 * n1 + n0) by ring]
    at hchain
  have hfin := le_of_mul_le_mul_left hchain hu10
  rw [div_le_iff₀ hQ0] at hfin
  linarith

/-- `n_j ≤ (4/3)^j (4|M| + 4W + 3840 L |D| e^κ)/r^{2j+1}` for `j ≥ 1`, `0 < r ≤ min(1, σ)`,
`L = log(180(|γ| + 6))`. -/
theorem clusterBracket_le {j : ℕ} (hj : 1 ≤ j) {M W D σ κ r : ℝ} (γ : ℝ) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ σ) :
    clusterBracket j M W D σ κ r (twinPotential r γ) ≤
      (4 / 3) ^ j * (4 * |M| + 4 * W + 3840 * Real.log (180 * (|γ| + 6)) * D * Real.exp κ) /
        r ^ (2 * j + 1) := by
  unfold clusterBracket
  set t : ℝ := 1 / r ^ (2 * j + 1) with ht
  have ht0 : 0 < t := by positivity
  set cj : ℝ := (4 / 3) ^ j with hcj
  have hcj1 : 1 ≤ cj := one_le_pow₀ (by norm_num)
  have hσ0 : 0 < σ := lt_of_lt_of_le hr hrσ
  have h1 : 2 / σ ^ (2 * j + 1) ≤ 2 * t := by
    rw [ht, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le hrσ _)
  have h4 : 1 / (4 : ℝ) ^ (2 * j + 1) ≤ t :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le (by linarith) _)
  obtain ⟨-, hPu⟩ := twinPotential_bounds hr hr1 γ
  set L := Real.log (180 * (|γ| + 6))
  have hPr : twinPotential r γ / r ^ (2 * j - 2) ≤ 3840 * L * t := by
    rw [div_le_iff₀ (by positivity), ht]
    refine hPu.trans (le_of_eq ?_)
    rw [show 2 * j + 1 = 3 + (2 * j - 2) by omega, pow_add]
    field_simp
  have hDe : 0 ≤ D * Real.exp κ := mul_nonneg hD (Real.exp_pos _).le
  have hM1 : |M| * (2 / σ ^ (2 * j + 1) + 2 * cj / 4 ^ (2 * j + 1)) ≤ |M| * (4 * cj * t) := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg M)
    have h5 : 2 * cj / (4 : ℝ) ^ (2 * j + 1) ≤ 2 * cj * t := by
      rw [show 2 * cj / (4 : ℝ) ^ (2 * j + 1) = 2 * cj * (1 / 4 ^ (2 * j + 1)) by ring]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : 2 * t ≤ 2 * cj * t := by nlinarith
    linarith
  have hD1 : cj * (D * Real.exp κ * (twinPotential r γ / r ^ (2 * j - 2))) ≤
      cj * (D * Real.exp κ * (3840 * L * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPr hDe) (by positivity)
  have hW1 : cj * (2 * W * (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1))) ≤ cj * (2 * W * (2 * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by rw [← ht]; linarith) (by positivity))
      (by positivity)
  have e : cj * (4 * |M| + 4 * W + 3840 * L * D * Real.exp κ) / r ^ (2 * j + 1) =
      |M| * (4 * cj * t) + cj * (D * Real.exp κ * (3840 * L * t)) + cj * (2 * W * (2 * t)) := by
    rw [ht]; ring
  rw [e, mul_add]
  linarith

/-- **Mirror points.** For `θ > 0` and every `e ∈ ℂ`, `|2θ + e| ≥ θ` or `|8θ + e| ≥ 4θ`. -/
theorem mirror_alternative {θ : ℝ} (hθ : 0 < θ) (e : ℂ) :
    θ ≤ ‖(2 * θ : ℂ) + e‖ ∨ 4 * θ ≤ ‖(8 * θ : ℂ) + e‖ := by
  by_contra h
  push Not at h
  have h1 := (Complex.abs_re_le_norm ((2 * θ : ℂ) + e)).trans_lt h.1
  have h2 := (Complex.abs_re_le_norm ((8 * θ : ℂ) + e)).trans_lt h.2
  have r1 : ((2 * θ : ℂ) + e).re = 2 * θ + e.re := by simp
  have r2 : ((8 * θ : ℂ) + e).re = 8 * θ + e.re := by simp
  rw [r1, abs_lt] at h1
  rw [r2, abs_lt] at h2
  linarith [h1.1, h2.2]

/-- **Isolated twins are exponentially tight.** Let the difference tests of a `C²` bump be Weil
nonnegative on `[0, V]`, `z*` the Legendre record at lag `V` with `|D(z*)| ≥ ε₀ > 0`, `k ≥ 1`,
`V ≥ π(k + 1)`, `κ ≥ 1`, `0 < r ≤ 1`, `Vr ≥ 4π(k + 1)`, `8κ/V ≤ r` and `4κ/V + r ≤ Re z*`. Let
`z₂ ≠ z*` be an exponent with `|z₂ − z*| ≤ r/2`, and let every other exponent keep distance `2r` from
`z*`. Then, with `L = log(180(|Im z*| + 6))`,
`|z₂ − z*| V^{2k+2} r^{2k+1} ≤ (8/3)(4/3)^k (16κ² + 4π²(k+1)²)^{k+1}
  (4(|M| + W)/((e − 1)ε₀) + 6144 L)`. -/
theorem zeta_isolated_twin_tight {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {k : ℕ} (hk : 1 ≤ k) {V : ℝ} (hV : π * (k + 1) ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hD₁ : ε₀ ≤ ‖evenCoeff zetaZeroConfig b z₁‖)
    {κ r : ℝ} (hκ : 1 ≤ κ) (hr : 0 < r) (hr1 : r ≤ 1) (hVr : 4 * π * (k + 1) ≤ V * r)
    (hκr : 8 * κ / V ≤ r) (hrz : 4 * κ / V + r ≤ z₁.re) {z₂ : ℂ} (hz₂ : z₂ ≠ z₁)
    (hz₂r : ‖z₂ - z₁‖ ≤ r / 2)
    (hiso : ∀ z, z ≠ z₁ → z ≠ z₂ → evenCoeff zetaZeroConfig b z ≠ 0 → 2 * r ≤ ‖z - z₁‖) :
    ‖z₂ - z₁‖ * V ^ (2 * k + 2) * r ^ (2 * k + 1) ≤
      8 / 3 * (4 / 3) ^ k * (16 * κ ^ 2 + 4 * π ^ 2 * (k + 1 : ℕ) ^ 2) ^ (k + 1) *
        (4 * (|2 * (lagStructure zetaZeroConfig b 0).re| +
            ∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) / ((Real.exp 1 - 1) * ε₀) +
          6144 * Real.log (180 * (|z₁.im| + 6))) := by
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set L : ℝ := Real.log (180 * (|z₁.im| + 6)) with hL
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [abs_nonneg z₁.im])
  have hκ0 : 0 < κ := by linarith
  have hθ0 : 0 < κ / V := div_pos hκ0 hV0
  have h4κ : 4 * κ / V ≤ r / 2 := by
    have : 8 * κ / V = 2 * (4 * κ / V) := by ring
    linarith
  -- choose the evaluation depth `κ'` with no mirror twin
  obtain ⟨κ', hκ'1, hκ'4, hsum⟩ : ∃ κ' : ℝ, κ ≤ κ' ∧ κ' ≤ 4 * κ ∧
      κ' / V ≤ ‖(z₁ - ((z₁.re - κ' / V : ℝ) + z₁.im * I)) +
        (z₂ - ((z₁.re - κ' / V : ℝ) + z₁.im * I))‖ := by
    have hx : ∀ κ' : ℝ, (z₁ - ((z₁.re - κ' / V : ℝ) + z₁.im * I)) +
        (z₂ - ((z₁.re - κ' / V : ℝ) + z₁.im * I)) = ((2 * (κ' / V) : ℝ) : ℂ) + (z₂ - z₁) := by
      intro κ'
      apply Complex.ext
      · simp; ring
      · simp
    rcases mirror_alternative hθ0 (z₂ - z₁) with h | h
    · refine ⟨κ, le_rfl, by linarith, ?_⟩
      rw [hx]; push_cast at h ⊢; exact h
    · refine ⟨4 * κ, by linarith, le_rfl, ?_⟩
      rw [hx]; push_cast at h ⊢
      rw [show (4 * κ / V : ℝ) = 4 * (κ / V) by ring, show (2 * (4 * (κ : ℂ) / V)) = 8 * (κ / V) by
        ring]
      exact h
  have hκ'0 : 0 < κ' := by linarith
  have hκ'V : κ' / V ≤ 4 * κ / V := div_le_div_of_nonneg_right hκ'4 hV0.le
  set s : ℂ := ((z₁.re - κ' / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ' / V := by
    have : z₁ - s = ((κ' / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ'0 hV0)]
  have hσ : 0 < z₁.re - κ' / V := by linarith
  have hrσ : r ≤ z₁.re - κ' / V := by linarith
  have hz₂s : ‖z₂ - s‖ ≤ r := by
    calc ‖z₂ - s‖ ≤ ‖z₂ - z₁‖ + ‖z₁ - s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r := by rw [hz₁s]; linarith
  have hiso' : ∀ z, z ≠ z₁ → z ≠ z₂ → D z ≠ 0 → r ≤ ‖z - s‖ := fun z h1 h2 h3 => by
    have h4 := hiso z h1 h2 h3
    have h5 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h5
    linarith
  have hlaw := zeta_dipole_law hb hbs hk hV hm hz₁ hrec hκ'0 hσ hr (by linarith) hVr hz₂ hz₂s
    hsum hiso'
  -- the brackets in units `1/r^{2k+1}`
  set Ξ : ℝ := 4 * |M| + 4 * W + 3840 * L * ‖D z₁‖ * Real.exp κ' with hΞ
  have hb1 := clusterBracket_le (j := k + 1) (by omega) (M := M) (W := W) (D := ‖D z₁‖)
    (κ := κ') z₁.im hW0 (norm_nonneg _) hr hr1 hrσ
  have hb0 := clusterBracket_le (j := k) hk (M := M) (W := W) (D := ‖D z₁‖)
    (κ := κ') z₁.im hW0 (norm_nonneg _) hr hr1 hrσ
  rw [← hL] at hb1 hb0
  have hbr : 5 / 4 * r ^ 2 * clusterBracket (k + 1) M W ‖D z₁‖ (z₁.re - κ' / V) κ' r
        (twinPotential r z₁.im) + clusterBracket k M W ‖D z₁‖ (z₁.re - κ' / V) κ' r
        (twinPotential r z₁.im) ≤ 8 / 3 * (4 / 3) ^ k * Ξ / r ^ (2 * k + 1) := by
    have hΞ' : (4 / 3) ^ (k + 1) * Ξ / r ^ (2 * (k + 1) + 1) =
        4 / 3 * ((4 / 3) ^ k * Ξ / r ^ (2 * k + 1)) / r ^ 2 := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add, pow_succ]; field_simp; ring
    have hb1' : 5 / 4 * r ^ 2 * clusterBracket (k + 1) M W ‖D z₁‖ (z₁.re - κ' / V) κ' r
        (twinPotential r z₁.im) ≤ 5 / 3 * ((4 / 3) ^ k * Ξ / r ^ (2 * k + 1)) := by
      have := mul_le_mul_of_nonneg_left hb1 (show 0 ≤ 5 / 4 * r ^ 2 by positivity)
      refine this.trans (le_of_eq ?_)
      rw [hΞ]; rw [hΞ] at hΞ'; rw [hΞ']; field_simp
    have e : 8 / 3 * (4 / 3) ^ k * Ξ / r ^ (2 * k + 1) =
        5 / 3 * ((4 / 3) ^ k * Ξ / r ^ (2 * k + 1)) + (4 / 3) ^ k * Ξ / r ^ (2 * k + 1) := by ring
    rw [e]
    exact add_le_add hb1' (by rw [hΞ]; exact hb0)
  -- the record's own size
  set Q : ℝ := (κ' ^ 2 + 4 * π ^ 2 * (k + 1 : ℕ) ^ 2) ^ (k + 1) with hQ
  set Q₄ : ℝ := (16 * κ ^ 2 + 4 * π ^ 2 * (k + 1 : ℕ) ^ 2) ^ (k + 1) with hQ₄
  have hQQ : Q ≤ Q₄ := by
    rw [hQ, hQ₄]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : κ' ^ 2 ≤ 16 * κ ^ 2 := by nlinarith
    linarith
  have hQ0 : 0 < Q := by positivity
  have hE1 : Real.exp 1 - 1 ≤ Real.exp κ' - 1 := by linarith [Real.exp_le_exp.mpr (show 1 ≤ κ' by linarith)]
  have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  have hratio : Real.exp κ' / (Real.exp κ' - 1) ≤ 8 / 5 := by
    rw [div_le_iff₀ (by linarith)]
    have : (8 : ℝ) / 3 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  have hΞle : Ξ / (‖D z₁‖ * (Real.exp κ' - 1)) ≤
      4 * (|M| + W) / ((Real.exp 1 - 1) * ε₀) + 6144 * L := by
    have hD0 : 0 < ‖D z₁‖ := lt_of_lt_of_le hε₀ hD₁
    have hden : 0 < ‖D z₁‖ * (Real.exp κ' - 1) := mul_pos hD0 (by linarith)
    have h1 : (4 * |M| + 4 * W) / (‖D z₁‖ * (Real.exp κ' - 1)) ≤
        4 * (|M| + W) / ((Real.exp 1 - 1) * ε₀) := by
      rw [show 4 * |M| + 4 * W = 4 * (|M| + W) by ring]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      rw [mul_comm]; exact mul_le_mul hD₁ hE1 he1.le (norm_nonneg _)
    have h2 : 3840 * L * ‖D z₁‖ * Real.exp κ' / (‖D z₁‖ * (Real.exp κ' - 1)) ≤ 6144 * L := by
      rw [show 3840 * L * ‖D z₁‖ * Real.exp κ' / (‖D z₁‖ * (Real.exp κ' - 1)) =
        3840 * L * (Real.exp κ' / (Real.exp κ' - 1)) by field_simp]
      have := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 3840 * L by positivity)
      linarith
    rw [hΞ, add_div]
    linarith
  -- assemble
  have hmain : ‖D z₁‖ * ‖z₂ - z₁‖ * (Real.exp κ' - 1) * V ^ (2 * k + 2) ≤
      Q * (8 / 3 * (4 / 3) ^ k * Ξ / r ^ (2 * k + 1)) := hlaw.trans
    (mul_le_mul_of_nonneg_left hbr hQ0.le)
  have hD0 : 0 < ‖D z₁‖ := lt_of_lt_of_le hε₀ hD₁
  have hden : 0 < ‖D z₁‖ * (Real.exp κ' - 1) := mul_pos hD0 (by linarith)
  have hr0 : 0 < r ^ (2 * k + 1) := by positivity
  have hEne : Real.exp κ' - 1 ≠ 0 := by linarith
  calc ‖z₂ - z₁‖ * V ^ (2 * k + 2) * r ^ (2 * k + 1)
      = ‖D z₁‖ * ‖z₂ - z₁‖ * (Real.exp κ' - 1) * V ^ (2 * k + 2) * r ^ (2 * k + 1) /
          (‖D z₁‖ * (Real.exp κ' - 1)) := by field_simp
    _ ≤ Q * (8 / 3 * (4 / 3) ^ k * Ξ / r ^ (2 * k + 1)) * r ^ (2 * k + 1) /
          (‖D z₁‖ * (Real.exp κ' - 1)) := by gcongr
    _ = 8 / 3 * (4 / 3) ^ k * Q * (Ξ / (‖D z₁‖ * (Real.exp κ' - 1))) := by field_simp
    _ ≤ 8 / 3 * (4 / 3) ^ k * Q₄ * (4 * (|M| + W) / ((Real.exp 1 - 1) * ε₀) + 6144 * L) := by
        have hΞ0 : 0 ≤ Ξ / (‖D z₁‖ * (Real.exp κ' - 1)) := by rw [hΞ]; positivity
        gcongr
    _ = _ := by ring

/-- The arithmetic of the tightness bound: `d V^{2k+2} r^{2k+1} ≤ (8/3)(4/3)^k B^{2k+2} A L` and
`Vr ≥ 2B` give `d ≤ (4/3) A L B/(3^k V)`. -/
theorem twin_tight_arith {d V r B A L L' : ℝ} (k : ℕ) (hd : 0 ≤ d) (hV : 0 < V)
    (hB : 0 < B) (hA : 0 ≤ A) (hLL : L ≤ L') (hVk : 2 * B ≤ V * r)
    (h : d * V ^ (2 * k + 2) * r ^ (2 * k + 1) ≤ 8 / 3 * (4 / 3) ^ k * B ^ (2 * k + 2) * (A * L)) :
    d ≤ 4 / 3 * A * L' * B / (3 ^ k * V) := by
  have hVr2 : (2 * B) ^ (2 * k + 1) ≤ (V * r) ^ (2 * k + 1) := pow_le_pow_left₀ (by positivity) hVk _
  have hden : V * (2 * B) ^ (2 * k + 1) ≤ V ^ (2 * k + 2) * r ^ (2 * k + 1) := by
    rw [show V ^ (2 * k + 2) * r ^ (2 * k + 1) = V * (V * r) ^ (2 * k + 1) by ring]
    exact mul_le_mul_of_nonneg_left hVr2 hV.le
  have h1 : d * (V * (2 * B) ^ (2 * k + 1)) ≤ 8 / 3 * (4 / 3) ^ k * B ^ (2 * k + 2) * (A * L) :=
    le_trans (mul_le_mul_of_nonneg_left hden hd) (by rw [← mul_assoc]; exact h)
  have key : (4 / 3 : ℝ) ^ k * 3 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
  have e1 : (2 * B) ^ (2 * k + 1) = 2 * 4 ^ k * B ^ (2 * k + 1) := by
    rw [mul_pow, pow_succ, pow_mul]; ring
  have hP : 0 < 2 * 4 ^ k * B ^ (2 * k + 1) := by positivity
  have h2 : (d * (3 ^ k * V)) * (2 * 4 ^ k * B ^ (2 * k + 1)) ≤
      (4 / 3 * A * L * B) * (2 * 4 ^ k * B ^ (2 * k + 1)) := by
    have h3 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ 3 ^ k by positivity)
    calc (d * (3 ^ k * V)) * (2 * 4 ^ k * B ^ (2 * k + 1))
        = d * (V * (2 * B) ^ (2 * k + 1)) * 3 ^ k := by rw [e1]; ring
      _ ≤ 8 / 3 * (4 / 3) ^ k * B ^ (2 * k + 2) * (A * L) * 3 ^ k := h3
      _ = (4 / 3 * A * L * B) * (2 * 4 ^ k * B ^ (2 * k + 1)) := by
          rw [pow_succ B (2 * k + 1)]
          linear_combination (8 / 3 * B ^ (2 * k + 1) * B * (A * L)) * key
  have h4 := le_of_mul_le_mul_right h2 hP
  rw [le_div_iff₀ (by positivity)]
  calc d * (3 ^ k * V) ≤ 4 / 3 * A * L * B := h4
    _ ≤ 4 / 3 * A * L' * B := by gcongr

/-! ### Near-top twins of `ζ` -/

/-- The tightness constant `A_w = 256e(e^{w/2}B_w)²(C + 1)/((e − 1)a_w²) + 6144`. -/
def twinTightConstant (w : ℝ) : ℝ :=
  256 * Real.exp 1 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 * (xiLineTwoLogDerivConstant + 1) /
    ((Real.exp 1 - 1) * centerAmplitude w ^ 2) + 6144

theorem twinTightConstant_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ twinTightConstant w := by
  unfold twinTightConstant
  have hC := xiLineTwoLogDerivConstant_nonneg
  have he : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have ha := centerAmplitude_pos hw
  exact add_nonneg (div_nonneg (by positivity) (mul_pos he (pow_pos ha 2)).le) (by norm_num)

/-- **Near-top twins are exponentially tight or tripled.** Let `½ + z₀` be a zero right of the line at
height `γ₀ ≥ T_w`, `1/V`-near the top, `V ≥ V_w(z₀)`, and let the difference tests of the bump modulated
to `γ₀` be Weil nonnegative on `[0, V]`. Let `k ≥ 1`, `0 < r ≤ 1`, `r + 4/V ≤ Re z₀/2`,
`Vr ≥ 2(R_w(γ₀) + κ_w)` and `Vr ≥ 2(4 + 2π(k + 1))`. Then the Legendre record `z*` at lag `V` has
either two other zeros within `2r`, or a twin within
`(4/3) A_w log(180(Γ + 6)) (4 + 2π(k + 1))/(3^k V)`, `Γ = recordHeightEnvelope w γ₀`. -/
theorem zeta_near_top_twin_tight_or_triple {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re)
    (hVlag : hidingLag w z₀ ≤ V) {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hrδ : r + 4 / V ≤ z₀.re / 2)
    (hVR : 2 * (twinRadiusNumerator w z₀.im + uniformTwinDepth w) ≤ V * r)
    (hVk : 2 * (4 + 2 * π * (k + 1)) ≤ V * r) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      ((∃ z z', z ≠ z₁ ∧ z' ≠ z₁ ∧ z ≠ z' ∧
          evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z' ≠ 0 ∧
          ‖z - z₁‖ < 2 * r ∧ ‖z' - z₁‖ < 2 * r) ∨
        ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          ‖z - z₁‖ ≤ 4 / 3 * twinTightConstant w *
            Real.log (180 * (recordHeightEnvelope w z₀.im + 6)) * (4 + 2 * π * (k + 1)) /
              (3 ^ k * V)) := by
  classical
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set R := twinRadiusNumerator w z₀.im with hR
  set κw := uniformTwinDepth w with hκw
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set a := centerAmplitude w with ha
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hK0 : 0 ≤ K₀ := by positivity
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  obtain ⟨hΓ, hsmall⟩ := nearTopHeight_conditions hw hTw
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have := htop _ h
      have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      linarith
    · have := htop _ h
      have e : (1 / 2 + conj z).re = 1 / 2 + z.re := by simp
      linarith
  have hV1 : R * max 1 (4 / z₀.re) ≤ V := (le_max_left _ _).trans hVlag
  have hV2 : 2 * Real.log (160 * Real.log (180 * Γ) * K₀ / a ^ 2) ≤ z₀.re * V := by
    have := (le_max_right _ _).trans hVlag
    rw [div_le_iff₀ hre₀] at this; linarith
  obtain ⟨z₁, hz₁, hre₁, hlow, hup, hD₁, hrec, z, hz, hDz, hdist⟩ :=
    zeta_uniform_twin_radius hw hV hz₀ hre₀ hpos₀ hΓ hsmall htop' hm hV1 hV2
  refine ⟨z₁, hz₁, hre₁, ?_⟩
  -- the twin of the uniform law is within `r/2` of the record
  have hκ0 : 0 < κw := by
    rw [hκw, uniformTwinDepth]
    refine Real.log_pos ?_
    have : 0 ≤ Real.exp 1 * (32 * K₀ * (xiLineTwoLogDerivConstant + 1)) / (60 * a ^ 2) := by
      have := xiLineTwoLogDerivConstant_nonneg
      positivity
    linarith
  set s : ℂ := ((z₁.re - κw / V : ℝ) : ℂ) + z₁.im * I with hs
  have hs1 : ‖s - z₁‖ = κw / V := by
    have : s - z₁ = ((-(κw / V) : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos hκ0 hV)]
  have hdist' : ‖z - s‖ < R / V := by rw [hR, twinRadiusNumerator]; exact hdist
  have hzr : ‖z - z₁‖ ≤ r / 2 := by
    have h1 : ‖z - z₁‖ ≤ ‖z - s‖ + ‖s - z₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : (R + κw) / V ≤ r / 2 := by
      rw [div_le_iff₀ hV]; linarith
    rw [hs1] at h1
    have : R / V + κw / V = (R + κw) / V := by ring
    linarith
  -- a third zero, or isolation
  by_cases h3 : ∃ z', z' ≠ z₁ ∧ z' ≠ z ∧ D z' ≠ 0 ∧ ‖z' - z₁‖ < 2 * r
  · obtain ⟨z', h1, h2, h3, h4⟩ := h3
    exact Or.inl ⟨z, z', hz, h1, fun h => h2 h.symm, hDz, h3, by linarith, h4⟩
  push Not at h3
  refine Or.inr ⟨z, hz, hDz, ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB : 0 < 4 + 2 * π * (k + 1) := by positivity
  have hVr0 : 0 < V * r := by positivity
  have hπk : 0 ≤ π * (k + 1) := mul_nonneg Real.pi_pos.le (by positivity)
  have hVrV : V * r ≤ V := mul_le_of_le_one_right hV.le hr1
  have hVπ : π * (k + 1) ≤ V := by linarith
  have h4π : 4 * π * (k + 1) ≤ V * r := by linarith
  have h8 : 8 * 1 / V ≤ r := by rw [div_le_iff₀ hV]; linarith [mul_comm V r]
  have htight := zeta_isolated_twin_tight (contDiff_modScaledBump_two w _)
    (modScaledBump_support hw _) hk hVπ hm hz₁ hrec (by positivity) hD₁ (κ := 1) le_rfl hr hr1
    h4π h8 (by linarith) hz hzr (fun z' h1 h2 h3' => h3 z' h1 h2 h3')
  -- the mass terms are logarithmic
  set L := Real.log (180 * (|z₁.im| + 6)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith [abs_nonneg z₁.im]
  have hcL : Real.log (|z₀.im| + 4) ≤ L := by
    rw [abs_of_pos hpos₀]
    exact Real.log_le_log (by positivity) (by linarith)
  have hW := tsum_norm_evenCoeff_modScaledBump_le hw z₀.im
  have hMW := abs_two_re_lagStructure_zero_le zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w z₀.im) (modScaledBump_support hw z₀.im)
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hWdef
  set C := xiLineTwoLogDerivConstant with hC
  have hC0 : 0 ≤ C := xiLineTwoLogDerivConstant_nonneg
  have hMW2 : |M| + W ≤ 32 * K₀ * (C + 1) * L := by
    have h1 : 16 * K₀ * (C + Real.log (|z₀.im| + 4)) ≤ 16 * K₀ * (C + L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : C + L ≤ (C + 1) * L := by
      have := mul_le_mul_of_nonneg_left hL1 hC0; linarith
    have h3 : 16 * K₀ * (C + L) ≤ 16 * K₀ * ((C + 1) * L) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  have hbr : 4 * (|M| + W) / ((Real.exp 1 - 1) * (a ^ 2 / (2 * Real.exp 1))) + 6144 * L ≤
      twinTightConstant w * L := by
    rw [twinTightConstant, ← hK₀, ← ha, ← hC]
    have hden : 0 < (Real.exp 1 - 1) * (a ^ 2 / (2 * Real.exp 1)) := by positivity
    have h1 : 4 * (|M| + W) / ((Real.exp 1 - 1) * (a ^ 2 / (2 * Real.exp 1))) ≤
        4 * (32 * K₀ * (C + 1) * L) / ((Real.exp 1 - 1) * (a ^ 2 / (2 * Real.exp 1))) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    have e : 4 * (32 * K₀ * (C + 1) * L) / ((Real.exp 1 - 1) * (a ^ 2 / (2 * Real.exp 1))) =
        256 * Real.exp 1 * K₀ * (C + 1) / ((Real.exp 1 - 1) * a ^ 2) * L := by
      field_simp; ring
    rw [add_mul]; linarith
  -- assemble: `(16 + 4π²(k+1)²)^{k+1} ≤ B^{2k+2}` and `Vr ≥ 2B`
  set B : ℝ := 4 + 2 * π * (k + 1) with hBdef
  have hQ : (16 * 1 ^ 2 + 4 * π ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2) ^ (k + 1) ≤ B ^ (2 * k + 2) := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [hBdef]; push_cast
    have e : (4 + 2 * π * ((k : ℝ) + 1)) ^ 2 =
        16 + 16 * (π * (k + 1)) + 4 * π ^ 2 * ((k : ℝ) + 1) ^ 2 := by ring
    rw [e]; linarith
  have hY0 : 0 ≤ 4 * (|M| + W) / ((Real.exp 1 - 1) * (a ^ 2 / (2 * Real.exp 1))) + 6144 * L := by
    have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
    have hL0 : 0 ≤ L := by linarith
    have hd : 0 < (Real.exp 1 - 1) * (a ^ 2 / (2 * Real.exp 1)) :=
      mul_pos he1 (div_pos (pow_pos ha0 2) (mul_pos two_pos (Real.exp_pos 1)))
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) hW0)) hd.le)
      (mul_nonneg (by norm_num) hL0)
  have hc0 : (0 : ℝ) ≤ 8 / 3 * (4 / 3) ^ k := by positivity
  have hB0 : (0 : ℝ) ≤ 8 / 3 * (4 / 3) ^ k * B ^ (2 * k + 2) := by positivity
  have hX := mul_le_mul (mul_le_mul_of_nonneg_left hQ hc0) hbr hY0 hB0
  have hmain : ‖z - z₁‖ * V ^ (2 * k + 2) * r ^ (2 * k + 1) ≤
      8 / 3 * (4 / 3) ^ k * B ^ (2 * k + 2) * (twinTightConstant w * L) := htight.trans hX
  have hA0 : 0 ≤ twinTightConstant w := twinTightConstant_nonneg hw
  have hLΓ : L ≤ Real.log (180 * (Γ + 6)) := by
    rw [hL]
    exact Real.log_le_log (by positivity) (by linarith only [hup])
  exact twin_tight_arith k (norm_nonneg _) hV hB hA0 hLΓ (by linarith only [hVk]) hmain

end GaloisForLFunctions.SquareRootThreshold
