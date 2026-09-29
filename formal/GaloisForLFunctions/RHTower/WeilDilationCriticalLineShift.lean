import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality
import Zeta23.WeilEF.FullLine
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.RiemannKernelWeilRadical
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction

/-!
# Dilated von Mangoldt weights: the shift to the critical line

For a finite set `S` of positive integers and real `b`, the *dilated* perturbation
`w(n) = Σ_{m ∈ S, m ∣ n} b(m) Λ(n/m)` has Dirichlet series `−B(s) ζ'/ζ(s)`, with
`B(s) = Σ_{m ∈ S} b(m) m^{-s}` (`dilationPoly`).  It has a pole at every zero of `ζ`, so the
regular rigidity theorems do not apply to it.  This module moves its Weil pairing onto the
critical line.

* `dilated_prime_side_line`: for `k ∈ C_c²` and `1 < c ≤ 3/2`,
  `Σ_n w(n) n^{-1/2} k(log n) = (1/2π) ∫ B(c+it) H_k(c+it) (−ζ'/ζ)(c+it) dt`.
  This is the one-sided prime sum of the translates `k(· + log m)`.
* `riemannPhiTransform_mul_logDeriv_zeta`: with `ξ = riemannPhiTransform`,
  `ξ ζ'/ζ = ξ' − ξ (1/s + 1/(s−1) + Γℝ'/Γℝ)`.  Hence `dilationShiftIntegrand`, which equals
  `B ξ³ ξ̄³ H_k (−ζ'/ζ)` off the zeros (`dilationShiftIntegrand_eq`), is analytic on `Re s > 0`
  whenever `H_k(1) = 0`: the transform of Riemann's kernel vanishes at every zero, and the pole at
  `s = 1` is removed by `dslope`.
* `integral_dilationShiftIntegrand_eq`: its integrals over `Re s = c` and `Re s = 1/2` agree.
  Its size on the strip is controlled by the kernel representation of `ξ` (bounded on vertical
  strips), Cauchy estimates for `ξ'`, digamma growth, and the decay of `H_k`.
* `Hfn_weilTest_twistTest` and `exists_norm_integral_dilation_error_le`: the spread radical test
  `twistTest 0 τ₀ R S` has transform `(Φ̂_R(z) conj Φ̂_R(z̄))³ H_G`, where `G = dilationProbe`.
  Replacing the truncated kernel by the full `ξ³ ξ̄³` on `Re s = c` costs at most the tail mass of
  Riemann's kernel beyond `R`, times tilted probe masses (Plancherel).
* `dilationShiftIntegrand_dilationProbe_critical`: on the critical line the probe factors out,
  as `|q̂_S(t)|²` times the integrand of the bump cube.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 Zeta23.WeilEF

/-- The dilation Dirichlet polynomial `B(s) = Σ_{m ∈ S} b(m) m^{-s}`. -/
def dilationPoly (S : Finset ℕ) (b : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ S, (b m : ℂ) * (m : ℂ) ^ (-s)

/-- The dilated von Mangoldt perturbation `Σ_{m ∈ S, m ∣ n} b(m) Λ(n/m)`. -/
def dilatedVonMangoldt (S : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ S, if m ∣ n then b m * Λ (n / m) else 0

theorem Hfn_translate (k : ℝ → ℂ) (y : ℝ) (s : ℂ) :
    Hfn (fun u => k (u + y)) s = Complex.exp (-(s - 1 / 2) * y) * Hfn k s := by
  unfold Hfn paperFT
  have := integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => k v * Complex.exp (I * ((s - 1 / 2) / I) * ((v - y : ℝ) : ℂ))) y
  simp only [add_sub_cancel_right] at this
  rw [this, ← integral_const_mul]
  congr 1; funext v
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have : I * ((s - 1 / 2) / I) = s - 1 / 2 := by field_simp
  rw [this]
  push_cast
  rw [show (s - 1 / 2) * ((v : ℂ) - y) = -(s - 1 / 2) * y + (s - 1 / 2) * v by ring,
    Complex.exp_add]
  ring

/-- The one-sided prime sum of a translate: `Σ_j Λ(j) j^{-1/2} k(log j + log m)` as a line
integral of `m^{1/2-s} H_k(s) (-ζ'/ζ)(s)` on `Re s = c`. -/
theorem prime_side_line_translate {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) (m : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Complex.exp (-((c : ℂ) + t * I - 1 / 2) * Real.log m) *
        Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n + Real.log m) := by
  have hkm : ContDiff ℝ 2 (fun u => k (u + Real.log m)) := hk.comp (contDiff_id.add contDiff_const)
  have hkmc : HasCompactSupport (fun u => k (u + Real.log m)) :=
    hkc.comp_homeomorph (Homeomorph.addRight (Real.log m))
  have h := prime_side_line hkm hkmc hc1 hc2
  rw [← h]
  congr 2; funext t
  rw [Hfn_translate]

theorem natCast_cpow_neg_eq_sqrt_mul_exp {m : ℕ} (hm : 1 ≤ m) (s : ℂ) :
    (m : ℂ) ^ (-s) = (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * Complex.exp (-(s - 1 / 2) * Real.log m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hmC]
  have hlog : Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hm0.le]; push_cast; rfl
  have hsq : (Real.sqrt m)⁻¹ = Real.exp (-(1 / 2) * Real.log m) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0, ← Real.exp_neg]; ring_nf
  rw [hlog, hsq, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring_nf

theorem tsum_dvd_reindex {m : ℕ} (hm : 1 ≤ m) (f : ℕ → ℂ) :
    ∑' n : ℕ, (if m ∣ n then f (n / m) else 0) = ∑' j : ℕ, f j := by
  have hinj : Function.Injective (fun j : ℕ => m * j) := fun a b h => by
    simpa [Nat.mul_left_cancel_iff (by omega : 0 < m)] using h
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun j => ?_
    simp [Nat.mul_div_cancel_left j (by omega : 0 < m)]
  · intro n hn
    by_cases h : m ∣ n
    · obtain ⟨j, rfl⟩ := h; exact ⟨j, rfl⟩
    · exact absurd (by simp [h]) hn

/-- **The dilated prime sum on a vertical line.**  For `k ∈ C_c²`, `1 < c ≤ 3/2`, and a finite set
`S` of positive integers,
`Σ_n (Σ_{m ∈ S, m ∣ n} b(m) Λ(n/m)) n^{-1/2} k(log n) = (1/2π) ∫ B(c+it) H_k(c+it) (-ζ'/ζ)(c+it) dt`
with `B(s) = Σ_{m ∈ S} b(m) m^{-s}`. -/
theorem dilated_prime_side_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, dilationPoly S b (c + t * I) * Hfn k (c + t * I) *
        (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, ((dilatedVonMangoldt S b n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  -- finite support in `n`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ u, L < |u| → k u = 0 := by
    obtain ⟨L, hL⟩ := hkc.isCompact.isBounded.subset_closedBall 0
    refine ⟨L, fun u hu => ?_⟩
    by_contra h
    have := hL (subset_tsupport _ h)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith
  have hfin : ∀ (g : ℕ → ℂ), Summable fun n : ℕ => g n * k (Real.log n) := by
    intro g
    apply summable_of_hasFiniteSupport
    refine (Set.finite_Iic ⌈Real.exp L⌉₊).subset fun n hn => ?_
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Set.mem_Iic]
    by_contra hlt
    push Not at hlt
    have hn1 : Real.exp L < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hlt)
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn1
    have : L < |Real.log n| := by
      rw [abs_of_nonneg (Real.log_nonneg (by
        have : (1 : ℝ) ≤ n := by
          have h1 : (1 : ℕ) ≤ n := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · subst h0; simp at hnpos
            · exact h0
          exact_mod_cast h1
        exact this))]
      exact (Real.lt_log_iff_exp_lt hnpos).mpr hn1
    exact hn (by rw [hL _ this, mul_zero])
  -- the right side as a finite sum of translated prime sums
  have hR : ∑' n : ℕ, ((dilatedVonMangoldt S b n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) =
      ∑ m ∈ S, ((b m : ℂ) * (((Real.sqrt m)⁻¹ : ℝ) : ℂ)) *
        ∑' j : ℕ, ((Λ j / Real.sqrt j : ℝ) : ℂ) * k (Real.log j + Real.log m) := by
    have hsplit : ∀ n : ℕ, ((dilatedVonMangoldt S b n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) =
        ∑ m ∈ S, (if m ∣ n then ((b m * Λ (n / m) / Real.sqrt n : ℝ) : ℂ) * k (Real.log n)
          else 0) := by
      intro n
      unfold dilatedVonMangoldt
      rw [Finset.sum_div, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    rw [tsum_congr hsplit, Summable.tsum_finsetSum]
    · refine Finset.sum_congr rfl fun m hmS => ?_
      have hm := hS m hmS
      set f : ℕ → ℂ := fun j => ((b m * Λ j / Real.sqrt (m * j : ℕ) : ℝ) : ℂ) *
          k (Real.log (m * j : ℕ)) with hfdef
      have hpt : ∀ n : ℕ, (if m ∣ n then ((b m * Λ (n / m) / Real.sqrt n : ℝ) : ℂ) *
          k (Real.log n) else 0) = (if m ∣ n then f (n / m) else 0) := by
        intro n
        split_ifs with h
        · obtain ⟨j, rfl⟩ := h
          simp [hfdef, Nat.mul_div_cancel_left j (by omega : 0 < m)]
        · rfl
      rw [tsum_congr hpt, tsum_dvd_reindex hm f]
      · rw [← tsum_mul_left]
        refine tsum_congr fun j => ?_
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp [hfdef]
        · simp only [hfdef]
          have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
          have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
          have hlog : Real.log ((m * j : ℕ) : ℝ) = Real.log j + Real.log m := by
            push_cast; rw [Real.log_mul hm0.ne' hj0.ne']; ring
          have hsq : Real.sqrt ((m * j : ℕ) : ℝ) = Real.sqrt m * Real.sqrt j := by
            push_cast; exact Real.sqrt_mul hm0.le _
          rw [hlog, hsq]
          have : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm0).ne'
          have : Real.sqrt j ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
          push_cast
          field_simp
    · intro m _
      have := hfin (fun n => if m ∣ n then ((b m * Λ (n / m) / Real.sqrt n : ℝ) : ℂ) else 0)
      refine this.congr fun n => ?_
      split_ifs <;> simp
  rw [hR]
  -- the left side, term by term
  have hint : ∀ m ∈ S, Integrable (fun t : ℝ => (b m : ℂ) * (m : ℂ) ^ (-((c : ℂ) + t * I)) *
      Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))) := by
    intro m hmS
    have hm := hS m hmS
    have hkm : ContDiff ℝ 2 (fun u => k (u + Real.log m)) :=
      hk.comp (contDiff_id.add contDiff_const)
    have hkmc : HasCompactSupport (fun u => k (u + Real.log m)) :=
      hkc.comp_homeomorph (Homeomorph.addRight (Real.log m))
    have hI := (integrable_Hfn_mul_logDeriv_zeta hkm hkmc hc1 hc2).neg.const_mul
      ((b m : ℂ) * (((Real.sqrt m)⁻¹ : ℝ) : ℂ))
    refine hI.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, Hfn_translate, natCast_cpow_neg_eq_sqrt_mul_exp hm]
    ring
  have hL : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, dilationPoly S b (c + t * I) * Hfn k (c + t * I) *
        (-logDeriv riemannZeta (c + t * I)) =
      ∑ m ∈ S, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (b m : ℂ) * (m : ℂ) ^ (-((c : ℂ) + t * I)) *
        Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I)) := by
    rw [← Finset.mul_sum, ← integral_finsetSum _ hint]
    congr 2; funext t
    unfold dilationPoly
    rw [Finset.sum_mul, Finset.sum_mul]
  rw [hL]
  refine Finset.sum_congr rfl fun m hmS => ?_
  have hm := hS m hmS
  rw [← prime_side_line_translate hk hkc hc1 hc2 m]
  have : ∀ t : ℝ, (b m : ℂ) * (m : ℂ) ^ (-((c : ℂ) + t * I)) * Hfn k (c + t * I) *
      (-logDeriv riemannZeta (c + t * I)) = ((b m : ℂ) * (((Real.sqrt m)⁻¹ : ℝ) : ℂ)) *
      (Complex.exp (-((c : ℂ) + t * I - 1 / 2) * Real.log m) * Hfn k (c + t * I) *
        (-logDeriv riemannZeta (c + t * I))) := by
    intro t; rw [natCast_cpow_neg_eq_sqrt_mul_exp hm]; ring
  simp_rw [this, integral_const_mul]
  ring


/-! ### The completed kernel and the logarithmic derivative of `ζ` -/

theorem riemannPhiTransform_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannPhiTransform s = s * (s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [riemannPhiTransform_eq hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- `ξ · ζ'/ζ = ξ' − ξ (1/s + 1/(s−1) + Γℝ'/Γℝ)` on `Re s > 0`, `s ≠ 1`, `ζ(s) ≠ 0`, with
`ξ = riemannPhiTransform`. -/
theorem riemannPhiTransform_mul_logDeriv_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    riemannPhiTransform s * logDeriv riemannZeta s =
      deriv riemannPhiTransform s - riemannPhiTransform s *
        (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  -- local agreement with the product
  have hev : riemannPhiTransform =ᶠ[𝓝 s]
      fun w => w * (w - 1) / 2 * (Complex.Gammaℝ w * riemannZeta w) := by
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w ≠ 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    filter_upwards [hopen.mem_nhds ⟨hs, hs1⟩] with w hw
    exact riemannPhiTransform_eq_zeta hw.1 hw.2
  have hGd := hasDerivAt_Gammaℝ_of_re_pos hs
  have hζd := (differentiableAt_riemannZeta hs1).hasDerivAt
  have hpoly : HasDerivAt (fun w : ℂ => w * (w - 1) / 2) ((2 * s - 1) / 2) s := by
    have h1 : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
      (hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)
    exact (h1.div_const 2).congr_deriv (by ring)
  have hprod : HasDerivAt (fun w : ℂ => w * (w - 1) / 2 * (Complex.Gammaℝ w * riemannZeta w))
      ((2 * s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) +
        s * (s - 1) / 2 * (Complex.Gammaℝ s * (Complex.digamma (s / 2) / 2 -
          (Real.log Real.pi : ℂ) / 2) * riemannZeta s + Complex.Gammaℝ s * deriv riemannZeta s)) s :=
    hpoly.mul (hGd.mul hζd)
  have hderiv : deriv riemannPhiTransform s = (2 * s - 1) / 2 * (Complex.Gammaℝ s * riemannZeta s) +
      s * (s - 1) / 2 * (Complex.Gammaℝ s * (Complex.digamma (s / 2) / 2 -
        (Real.log Real.pi : ℂ) / 2) * riemannZeta s + Complex.Gammaℝ s * deriv riemannZeta s) := by
    rw [hev.deriv_eq, hprod.deriv]
  have hlogG : logDeriv Complex.Gammaℝ s = Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_apply, hGd.deriv]; field_simp
  rw [logDeriv_apply riemannZeta, hderiv, hlogG, riemannPhiTransform_eq_zeta hs hs1]
  field_simp
  ring


/-! ### The analytic shift integrand -/

/-- `ξ̄(s) = conj ξ(conj s)`, entire. -/
def xiConj (s : ℂ) : ℂ := starRingEnd ℂ (riemannPhiTransform (starRingEnd ℂ s))

theorem differentiable_xiConj : Differentiable ℂ xiConj := by
  intro s
  have h := (differentiable_riemannPhiTransform (starRingEnd ℂ s)).conj_conj
  rw [Complex.conj_conj] at h
  exact h

/-- The logarithmic derivative `ψ(s/2)/2 − (log π)/2` of `Γℝ`. -/
def gammaRLogDeriv (s : ℂ) : ℂ := Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2

theorem logDeriv_Gammaℝ_eq_gammaRLogDeriv {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = gammaRLogDeriv s := by
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [logDeriv_apply, (hasDerivAt_Gammaℝ_of_re_pos hs).deriv, gammaRLogDeriv]
  field_simp

theorem differentiableOn_digamma_half :
    DifferentiableOn ℂ (fun s : ℂ => Complex.digamma (s / 2)) {s | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓ : DifferentiableOn ℂ Complex.Gamma {s | 0 < s.re} := fun s hs =>
    (Complex.differentiableAt_Gamma s fun m hm => by
      have : s.re = -(m : ℝ) := by rw [hm]; simp
      have hs' : 0 < s.re := hs
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith).differentiableWithinAt
  have hΓ' := hΓ.deriv hU
  have hdig : DifferentiableOn ℂ Complex.digamma {s | 0 < s.re} := by
    intro s hs
    have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
    have h1 := (hΓ' s hs).differentiableAt (hU.mem_nhds hs)
    have h2 := (hΓ s hs).differentiableAt (hU.mem_nhds hs)
    have : Complex.digamma =ᶠ[𝓝 s] fun w => deriv Complex.Gamma w / Complex.Gamma w := by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
    exact ((h1.div h2 hne).congr_of_eventuallyEq this).differentiableWithinAt
  intro s hs
  have hs2 : (s / 2) ∈ {s : ℂ | 0 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.div_re]
    have hs' : 0 < s.re := hs
    norm_num; positivity
  exact ((hdig _ hs2).differentiableAt (hU.mem_nhds hs2)).comp s
    (differentiableAt_id.div_const 2) |>.differentiableWithinAt

/-- The analytic integrand of the critical-line shift:
`−B(s) ξ(s)² ξ̄(s)³ (H_k(s) ξ'(s) − H_k(s) ξ(s)(1/s + Γℝ'/Γℝ(s)) − ξ(s) (H_k(s) − H_k(1))/(s−1))`. -/
def dilationShiftIntegrand (S : Finset ℕ) (b : ℕ → ℝ) (k : ℝ → ℂ) (s : ℂ) : ℂ :=
  -(dilationPoly S b s * riemannPhiTransform s ^ 2 * xiConj s ^ 3 *
    (Hfn k s * deriv riemannPhiTransform s -
      Hfn k s * riemannPhiTransform s * (1 / s + gammaRLogDeriv s) -
      riemannPhiTransform s * dslope (Hfn k) 1 s))

theorem dilationShiftIntegrand_eq {S : Finset ℕ} {b : ℕ → ℝ} {k : ℝ → ℂ} (hk1 : Hfn k 1 = 0)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    dilationShiftIntegrand S b k s = dilationPoly S b s * riemannPhiTransform s ^ 3 *
      xiConj s ^ 3 * Hfn k s * (-logDeriv riemannZeta s) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have key := riemannPhiTransform_mul_logDeriv_zeta hs hs1 hζ
  rw [logDeriv_Gammaℝ_eq_gammaRLogDeriv hs] at key
  have hds : dslope (Hfn k) 1 s = Hfn k s / (s - 1) := by
    rw [dslope_of_ne _ hs1, slope_def_field, hk1, sub_zero]
  unfold dilationShiftIntegrand
  rw [hds]
  linear_combination (dilationPoly S b s * riemannPhiTransform s ^ 2 * xiConj s ^ 3 * Hfn k s) * key

theorem differentiableOn_dilationShiftIntegrand (S : Finset ℕ) (b : ℕ → ℝ) {k : ℝ → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    DifferentiableOn ℂ (dilationShiftIntegrand S b k) {s | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hX : Differentiable ℂ riemannPhiTransform := differentiable_riemannPhiTransform
  have hX' : Differentiable ℂ (deriv riemannPhiTransform) := fun s =>
    ((hX.differentiableOn.deriv isOpen_univ) s (Set.mem_univ s)).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ s))
  have hH : Differentiable ℂ (Hfn k) := by
    have h := differentiable_paperFT hk hkc
    intro s
    unfold Hfn
    exact (h _).comp s ((differentiableAt_id.sub_const _).div_const _)
  have hds : Differentiable ℂ (dslope (Hfn k) 1) := fun s =>
    (((Complex.differentiableOn_dslope Filter.univ_mem).mpr hH.differentiableOn) s
      (Set.mem_univ s)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ s))
  intro s hs
  have hs' : 0 < s.re := hs
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs'; simp at hs'
  have hB : DifferentiableAt ℂ (dilationPoly S b) s := by
    unfold dilationPoly
    refine DifferentiableAt.fun_sum fun m _ => (differentiableAt_const _).mul ?_
    exact (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.mpr hs0))
  have hG : DifferentiableAt ℂ gammaRLogDeriv s := by
    unfold gammaRLogDeriv
    exact (((differentiableOn_digamma_half s hs).differentiableAt (hU.mem_nhds hs)).div_const
      _).sub_const _
  have hinv : DifferentiableAt ℂ (fun w : ℂ => 1 / w) s :=
    (differentiableAt_const _).div differentiableAt_id hs0
  unfold dilationShiftIntegrand
  refine (DifferentiableAt.neg ?_).differentiableWithinAt
  refine ((hB.mul ((hX s).pow 2)).mul ((differentiable_xiConj s).pow 3)).mul ?_
  exact (((hH s).mul (hX' s)).sub (((hH s).mul (hX s)).mul (hinv.add hG))).sub
    ((hX s).mul (hds s))


/-! ### Bounds on vertical strips -/

theorem norm_riemannPhiTransform_le {b : ℝ} (hb : 0 ≤ b) {s : ℂ} (hs : |s.re - 1 / 2| ≤ b) :
    ‖riemannPhiTransform s‖ ≤ ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (b * |u|) := by
  unfold riemannPhiTransform
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) (integrable_norm_riemannPhiKernel_mul_exp hb)
    (Eventually.of_forall fun u => ?_))
  simp only
  rw [norm_mul, Complex.norm_exp, mul_comm]
  gcongr
  have : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by simp
  rw [this]
  calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
    _ = |s.re - 1 / 2| * |u| := abs_mul _ _
    _ ≤ b * |u| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)

theorem norm_xiConj_le {b : ℝ} (hb : 0 ≤ b) {s : ℂ} (hs : |s.re - 1 / 2| ≤ b) :
    ‖xiConj s‖ ≤ ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (b * |u|) := by
  unfold xiConj
  rw [Complex.norm_conj]
  exact norm_riemannPhiTransform_le hb (by simpa using hs)

theorem norm_deriv_riemannPhiTransform_le {b : ℝ} (hb : 0 ≤ b) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ b) :
    ‖deriv riemannPhiTransform s‖ ≤
      4 * ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp ((b + 1 / 4) * |u|) := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := 1 / 4)
    (C := ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp ((b + 1 / 4) * |u|)) (by norm_num)
    (differentiable_riemannPhiTransform.diffContOnCl) (fun w hw => by
      refine norm_riemannPhiTransform_le (by linarith) ?_
      have hd : ‖w - s‖ = 1 / 4 := by rw [← dist_eq_norm]; exact hw
      have hre : |w.re - s.re| ≤ 1 / 4 := by
        have := Complex.abs_re_le_norm (w - s)
        rw [Complex.sub_re] at this; linarith
      calc |w.re - 1 / 2| = |(w.re - s.re) + (s.re - 1 / 2)| := by ring_nf
        _ ≤ |w.re - s.re| + |s.re - 1 / 2| := abs_add_le _ _
        _ ≤ b + 1 / 4 := by linarith)
  calc ‖deriv riemannPhiTransform s‖ ≤ _ / (1 / 4) := h
    _ = _ := by ring

theorem norm_dilationPoly_le {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m) (b : ℕ → ℝ) {s : ℂ}
    (hs : 0 ≤ s.re) : ‖dilationPoly S b s‖ ≤ ∑ m ∈ S, |b m| := by
  unfold dilationPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hm1 := hS m hm
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_real, Real.norm_eq_abs]
  have : (m : ℝ) ^ (-s).re ≤ 1 := by
    rw [Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1) (by linarith)
  calc |b m| * (m : ℝ) ^ (-s).re ≤ |b m| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |b m| := mul_one _

theorem exists_norm_dslope_Hfn_le {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hk1 : Hfn k 1 = 0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖dslope (Hfn k) 1 ((σ : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨CK, hCK0, hCK⟩ := norm_Hfn_le hk hkc
  have hH : Differentiable ℂ (Hfn k) := by
    have h := differentiable_paperFT hk.continuous hkc
    intro s; unfold Hfn
    exact (h _).comp s ((differentiableAt_id.sub_const _).div_const _)
  have hds : Continuous (dslope (Hfn k) 1) := by
    have hd : DifferentiableOn ℂ (dslope (Hfn k) 1) Set.univ :=
      (Complex.differentiableOn_dslope Filter.univ_mem).mpr hH.differentiableOn
    exact continuousOn_univ.mp hd.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    hds.continuousOn
  refine ⟨max CK (2 * max M 0), by positivity, fun σ t hσ1 hσ2 => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hq : 0 < 1 + t ^ 2 := by positivity
  by_cases hball : dist s 1 ≤ 1
  · have h1 := hM s (Metric.mem_closedBall.mpr hball)
    have ht : |t| ≤ 1 := by
      have : |s.im - (1 : ℂ).im| ≤ dist s 1 := by
        rw [dist_eq_norm]
        have := Complex.abs_im_le_norm (s - 1)
        simpa using this
      simpa [hsdef] using this.trans hball
    have ht2 : 1 + t ^ 2 ≤ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    rw [le_div_iff₀ hq]
    calc ‖dslope (Hfn k) 1 s‖ * (1 + t ^ 2) ≤ max M 0 * 2 :=
          mul_le_mul (h1.trans (le_max_left _ _)) ht2 hq.le (le_max_right _ _)
      _ ≤ max CK (2 * max M 0) := by rw [mul_comm]; exact le_max_right _ _
  · push Not at hball
    have hs1 : s ≠ 1 := fun h => by rw [h, dist_self] at hball; linarith
    rw [dslope_of_ne _ hs1, slope_def_field, hk1, sub_zero, norm_div]
    have hden : 1 ≤ ‖s - 1‖ := by rw [← dist_eq_norm]; exact hball.le
    calc ‖Hfn k s‖ / ‖s - 1‖ ≤ ‖Hfn k s‖ := div_le_self (norm_nonneg _) hden
      _ ≤ CK / (1 + t ^ 2) := hCK σ t (by linarith) (by linarith)
      _ ≤ max CK (2 * max M 0) / (1 + t ^ 2) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hq.le


theorem norm_gammaRLogDeriv_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
    ‖gammaRLogDeriv ((σ : ℂ) + t * I)‖ ≤ A * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
  obtain ⟨Cψ, hCψ, hψ⟩ := digamma_growth_strip
  have hπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨Real.log Real.pi / 2 + 5 * (Cψ / 2), by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have hw1 : 1 / 4 ≤ (((σ : ℂ) + t * I) / 2).re := by simp; linarith
  have hw2 : (((σ : ℂ) + t * I) / 2).re ≤ 1 := by simp; linarith
  have hψb := hψ _ hw1 hw2
  have him : |(((σ : ℂ) + t * I) / 2).im| = |t| / 2 := by simp [abs_div]
  rw [him] at hψb
  have hlog : Real.log (2 + |t| / 2) ≤ 5 * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    have hlt : Real.log (2 + |t| / 2) ≤ Real.log (2 + |t|) :=
      Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
    have h2 := log_two_add_le (abs_nonneg t)
    rw [sq_abs] at h2
    linarith
  have hr1 : 1 ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
  unfold gammaRLogDeriv
  calc ‖Complex.digamma (((σ : ℂ) + t * I) / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖
      ≤ ‖Complex.digamma (((σ : ℂ) + t * I) / 2)‖ / 2 + Real.log Real.pi / 2 := by
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hπ]; norm_num
    _ ≤ Cψ * (5 * (1 + t ^ 2) ^ (1 / 4 : ℝ)) / 2 + Real.log Real.pi / 2 := by
        gcongr; exact hψb.trans (mul_le_mul_of_nonneg_left hlog hCψ.le)
    _ ≤ (Real.log Real.pi / 2 + 5 * (Cψ / 2)) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
        nlinarith

theorem exists_norm_dilationShiftIntegrand_le {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hk1 : Hfn k 1 = 0) : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖dilationShiftIntegrand S b k ((σ : ℂ) + t * I)‖ ≤
        K * (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
  obtain ⟨CK, hCK0, hCK⟩ := norm_Hfn_le hk hkc
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_dslope_Hfn_le hk hkc hk1
  obtain ⟨A, hA0, hA⟩ := norm_gammaRLogDeriv_le
  set CB := ∑ m ∈ S, |b m| with hCB
  set CX := ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (1 * |u|) with hCX
  set CX' := 4 * ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp ((1 + 1 / 4) * |u|) with hCX'
  have hCB0 : 0 ≤ CB := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCX0 : 0 ≤ CX := integral_nonneg fun _ => by positivity
  have hCX'0 : 0 ≤ CX' := mul_nonneg (by norm_num) (integral_nonneg fun _ => by positivity)
  refine ⟨CB * CX ^ 5 * (CK * CX' + CK * CX * (2 + A) + CX * Cd), by positivity,
    fun σ t hσ1 hσ2 => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hstrip : |s.re - 1 / 2| ≤ 1 := by rw [hsre, abs_le]; constructor <;> linarith
  have hq : 0 < 1 + t ^ 2 := by positivity
  have hr1 : 1 ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by nlinarith) (by norm_num)
  have hB := norm_dilationPoly_le hS b (s := s) (by rw [hsre]; linarith)
  have hX := norm_riemannPhiTransform_le (by norm_num : (0 : ℝ) ≤ 1) hstrip
  have hY := norm_xiConj_le (by norm_num : (0 : ℝ) ≤ 1) hstrip
  have hX' := norm_deriv_riemannPhiTransform_le (by norm_num : (0 : ℝ) ≤ 1) hstrip
  have hK := hCK σ t (by linarith) (by linarith)
  have hD := hCd σ t hσ1 hσ2
  have hG := hA σ t hσ1 hσ2
  have hinv : ‖1 / s‖ ≤ 2 := by
    have hn : 1 / 2 ≤ ‖s‖ := by
      have := Complex.re_le_norm s; rw [hsre] at this; linarith
    rw [norm_div, norm_one]
    rw [div_le_iff₀ (by linarith)]; linarith
  have hexp : (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) = (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) := by
    rw [Real.norm_eq_abs, sq_abs, show (-(3 / 2 : ℝ) / 2) = 1 / 4 - 1 by norm_num,
      Real.rpow_sub hq, Real.rpow_one]
  rw [hexp]
  set r := (1 + t ^ 2) ^ (1 / 4 : ℝ) with hr
  set q := 1 + t ^ 2 with hqdef
  -- the bracket
  have hbr : ‖Hfn k s * deriv riemannPhiTransform s - Hfn k s * riemannPhiTransform s *
      (1 / s + gammaRLogDeriv s) - riemannPhiTransform s * dslope (Hfn k) 1 s‖ ≤
      (CK * CX' + CK * CX * (2 + A) + CX * Cd) * (r / q) := by
    have e1 : ‖Hfn k s * deriv riemannPhiTransform s‖ ≤ CK * CX' * (r / q) := by
      rw [norm_mul]
      calc ‖Hfn k s‖ * ‖deriv riemannPhiTransform s‖ ≤ CK / q * CX' :=
            mul_le_mul hK hX' (norm_nonneg _) (by positivity)
        _ ≤ CK * CX' * (r / q) := by
            rw [show CK / q * CX' = CK * CX' * (1 / q) by ring]
            gcongr
    have e2 : ‖Hfn k s * riemannPhiTransform s * (1 / s + gammaRLogDeriv s)‖ ≤
        CK * CX * (2 + A) * (r / q) := by
      rw [norm_mul, norm_mul]
      have hg : ‖1 / s + gammaRLogDeriv s‖ ≤ (2 + A) * r :=
        (norm_add_le _ _).trans (by nlinarith)
      calc ‖Hfn k s‖ * ‖riemannPhiTransform s‖ * ‖1 / s + gammaRLogDeriv s‖
          ≤ CK / q * CX * ((2 + A) * r) := by gcongr
        _ = CK * CX * (2 + A) * (r / q) := by ring
    have e3 : ‖riemannPhiTransform s * dslope (Hfn k) 1 s‖ ≤ CX * Cd * (r / q) := by
      rw [norm_mul]
      calc ‖riemannPhiTransform s‖ * ‖dslope (Hfn k) 1 s‖ ≤ CX * (Cd / q) := by gcongr
        _ ≤ CX * Cd * (r / q) := by
            rw [show CX * (Cd / q) = CX * Cd * (1 / q) by ring]
            gcongr
    calc _ ≤ ‖Hfn k s * deriv riemannPhiTransform s - Hfn k s * riemannPhiTransform s *
          (1 / s + gammaRLogDeriv s)‖ + ‖riemannPhiTransform s * dslope (Hfn k) 1 s‖ :=
          norm_sub_le _ _
      _ ≤ (‖Hfn k s * deriv riemannPhiTransform s‖ + ‖Hfn k s * riemannPhiTransform s *
          (1 / s + gammaRLogDeriv s)‖) + ‖riemannPhiTransform s * dslope (Hfn k) 1 s‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ _ := by nlinarith
  unfold dilationShiftIntegrand
  rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
  calc ‖dilationPoly S b s‖ * ‖riemannPhiTransform s‖ ^ 2 * ‖xiConj s‖ ^ 3 * ‖_‖
      ≤ CB * CX ^ 2 * CX ^ 3 * ((CK * CX' + CK * CX * (2 + A) + CX * Cd) * (r / q)) := by
        gcongr
    _ = CB * CX ^ 5 * (CK * CX' + CK * CX * (2 + A) + CX * Cd) * (r / q) := by ring


theorem tendsto_one_add_norm_sq_rpow_neg {l : Filter ℝ} (hl : Tendsto (fun t : ℝ => ‖t‖) l atTop)
    (K : ℝ) : Tendsto (fun t : ℝ => K * (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) l (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => 1 + ‖t‖ ^ 2) l atTop :=
    tendsto_atTop_add_const_left _ _ ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hl)
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2 / 2)).comp h1
  have h3 : (fun t : ℝ => K * (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) =
      fun t => K * ((fun x : ℝ => x ^ (-(3 / 2 / 2 : ℝ))) ∘ fun t : ℝ => 1 + ‖t‖ ^ 2) t := by
    funext t; simp only [Function.comp]; congr 2; ring
  rw [h3]
  simpa using h2.const_mul K

/-- **The critical-line shift.**  The integral of the analytic shift integrand over the line
`Re s = c` equals its integral over the critical line, for `1/2 ≤ c ≤ 3/2`. -/
theorem integral_dilationShiftIntegrand_eq {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m) (b : ℕ → ℝ)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (hk1 : Hfn k 1 = 0)
    {c : ℝ} (hc1 : 1 / 2 ≤ c) (hc2 : c ≤ 3 / 2) :
    ∫ t : ℝ, dilationShiftIntegrand S b k ((c : ℂ) + t * I) =
      ∫ t : ℝ, dilationShiftIntegrand S b k (((1 / 2 : ℝ) : ℂ) + t * I) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_dilationShiftIntegrand_le hS b hk hkc hk1
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff := differentiableOn_dilationShiftIntegrand S b hk.continuous hkc
  refine vertical_line_shift hc1 (fun s hs1 _ => (hdiff s (show 0 < s.re by
      linarith)).differentiableAt (hU.mem_nhds (show 0 < s.re by linarith)))
    (φ := fun t => K * (1 + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2))
    ((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul K)
    (fun σ t h1 h2 => hK σ t h1 (by linarith))
    (tendsto_one_add_norm_sq_rpow_neg tendsto_norm_atTop_atTop K)
    (tendsto_one_add_norm_sq_rpow_neg (tendsto_abs_atBot_atTop.congr
      (fun t => (Real.norm_eq_abs t).symm)) K)


/-! ### The functional equation of the kernel transform and the critical line -/

theorem riemannPhiTransform_one_sub (w : ℂ) :
    riemannPhiTransform (1 - w) = riemannPhiTransform w := by
  unfold riemannPhiTransform
  rw [← integral_neg_eq_self]
  congr 1; funext x
  rw [riemannPhiKernel_neg]
  congr 1; push_cast; ring_nf

theorem xiConj_critical (t : ℝ) :
    xiConj ((1 / 2 : ℂ) + t * I) = starRingEnd ℂ (riemannPhiTransform ((1 / 2 : ℂ) + t * I)) := by
  unfold xiConj
  congr 1
  rw [← riemannPhiTransform_one_sub]
  congr 1
  apply Complex.ext <;> simp; norm_num

theorem riemannPhiTransform_mul_xiConj_critical (t : ℝ) :
    riemannPhiTransform ((1 / 2 : ℂ) + t * I) ^ 3 * xiConj ((1 / 2 : ℂ) + t * I) ^ 3 =
      ((‖riemannPhiTransform ((1 / 2 : ℂ) + t * I)‖ ^ 6 : ℝ) : ℂ) := by
  rw [xiConj_critical, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring_nf

theorem weilTest_self_neg (f : ℝ → ℂ) (y : ℝ) :
    EF.weilTest f f (-y) = starRingEnd ℂ (EF.weilTest f f y) := by
  rw [weilTest_apply, weilTest_apply, ← integral_conj]
  rw [← integral_sub_right_eq_self (μ := volume) _ y]
  congr 1; funext t
  simp only [map_mul, Complex.conj_conj]
  rw [mul_comm]; congr 2; ring_nf


/-! ### The probe part of the spread radical test -/

/-- The triple polar-free bump `β ⋆ β ⋆ β`. -/
def bumpCube : ℝ → ℂ :=
  convolution (convolution weilBumpPolarFree weilBumpPolarFree (ContinuousLinearMap.mul ℝ ℂ) volume)
    weilBumpPolarFree (ContinuousLinearMap.mul ℝ ℂ) volume

theorem hasCompactSupport_bumpCube : HasCompactSupport bumpCube :=
  (hasCompactSupport_weilBumpPolarFree.convolution _ hasCompactSupport_weilBumpPolarFree).convolution
    _ hasCompactSupport_weilBumpPolarFree

theorem contDiff_bumpCube : ContDiff ℝ 2 bumpCube := by
  have h2 : HasCompactSupport (convolution weilBumpPolarFree weilBumpPolarFree
      (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    hasCompactSupport_weilBumpPolarFree.convolution _ hasCompactSupport_weilBumpPolarFree
  have hc2 : ContDiff ℝ 2 (convolution weilBumpPolarFree weilBumpPolarFree
      (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    hasCompactSupport_weilBumpPolarFree.contDiff_convolution_left _ contDiff_weilBumpPolarFree
      contDiff_weilBumpPolarFree.continuous.locallyIntegrable
  exact h2.contDiff_convolution_left _ hc2 contDiff_weilBumpPolarFree.continuous.locallyIntegrable

theorem paperFT_bumpCube (z : ℂ) :
    paperFT bumpCube z = paperFT weilBumpPolarFree z ^ 3 := by
  have h2 : HasCompactSupport (convolution weilBumpPolarFree weilBumpPolarFree
      (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    hasCompactSupport_weilBumpPolarFree.convolution _ hasCompactSupport_weilBumpPolarFree
  have hc2 : ContDiff ℝ 2 (convolution weilBumpPolarFree weilBumpPolarFree
      (ContinuousLinearMap.mul ℝ ℂ) volume) :=
    hasCompactSupport_weilBumpPolarFree.contDiff_convolution_left _ contDiff_weilBumpPolarFree
      contDiff_weilBumpPolarFree.continuous.locallyIntegrable
  unfold bumpCube
  rw [paperFT_convolution (integrable_mul_cexp_of_continuous hc2.continuous h2 z)
    (integrable_weilBumpPolarFree_mul_exp z),
    paperFT_convolution (integrable_weilBumpPolarFree_mul_exp z)
      (integrable_weilBumpPolarFree_mul_exp z)]
  ring

/-- The probe part `β ⋆ β ⋆ β ⋆ q_S` of the spread radical test. -/
def dilationProbe (τ₀ S : ℝ) : ℝ → ℂ :=
  convolution bumpCube (twistProbe τ₀ S) (ContinuousLinearMap.mul ℝ ℂ) volume

theorem hasCompactSupport_twistProbe' {τ₀ S : ℝ} (hS : 0 < S) :
    HasCompactSupport (twistProbe τ₀ S) :=
  hasCompactSupport_of_abs_gt (a := S) fun _ h => twistProbe_eq_zero hS h

theorem hasCompactSupport_dilationProbe {τ₀ S : ℝ} (hS : 0 < S) :
    HasCompactSupport (dilationProbe τ₀ S) :=
  hasCompactSupport_bumpCube.convolution _ (hasCompactSupport_twistProbe' hS)

theorem contDiff_dilationProbe (τ₀ S : ℝ) : ContDiff ℝ 2 (dilationProbe τ₀ S) :=
  hasCompactSupport_bumpCube.contDiff_convolution_left _ contDiff_bumpCube
    (continuous_twistProbe τ₀ S).locallyIntegrable

theorem paperFT_dilationProbe {τ₀ S : ℝ} (hS : 0 < S) (z : ℂ) :
    paperFT (dilationProbe τ₀ S) z =
      paperFT weilBumpPolarFree z ^ 3 * paperFT (twistProbe τ₀ S) z := by
  unfold dilationProbe
  rw [paperFT_convolution (integrable_mul_cexp_of_continuous contDiff_bumpCube.continuous
    hasCompactSupport_bumpCube z)
    (integrable_mul_cexp_of_continuous (continuous_twistProbe τ₀ S)
      (hasCompactSupport_twistProbe' hS) z), paperFT_bumpCube]

/-- **Factorization of the spread radical test.**  With `z = (s − 1/2)/i`, the transform of the
autocorrelation of `twistTest 0 τ₀ R S` is the cube of the truncated kernel factor
`Φ̂_R(z) conj Φ̂_R(conj z)` times the transform of the autocorrelation of the probe part. -/
theorem Hfn_weilTest_twistTest {τ₀ R S : ℝ} (hS : 0 < S) (s : ℂ) :
    Hfn (EF.weilTest (twistTest 0 τ₀ R S) (twistTest 0 τ₀ R S)) s =
      (paperFT (riemannPhiCore R) ((s - 1 / 2) / I) *
        starRingEnd ℂ (paperFT (riemannPhiCore R) (starRingEnd ℂ ((s - 1 / 2) / I)))) ^ 3 *
      Hfn (EF.weilTest (dilationProbe τ₀ S) (dilationProbe τ₀ S)) s := by
  have hFc : Continuous (twistTest 0 τ₀ R S) := (contDiff_twistTest 0 τ₀ R S).continuous
  have hFs : HasCompactSupport (twistTest 0 τ₀ R S) :=
    hasCompactSupport_of_abs_gt (a := 3 * R + S) fun _ h => twistTest_eq_zero hS h
  have hGc : Continuous (dilationProbe τ₀ S) := (contDiff_dilationProbe τ₀ S).continuous
  have hGs := hasCompactSupport_dilationProbe (τ₀ := τ₀) hS
  unfold Hfn
  set z := (s - 1 / 2) / I
  rw [EF.paperFT_weilTest hFc hFc hFs hFs, EF.paperFT_weilTest hGc hGc hGs hGs,
    paperFT_twistTest_factor hS, paperFT_twistTest_factor hS, paperFT_dilationProbe hS,
    paperFT_dilationProbe hS]
  simp only [Complex.ofReal_zero, add_zero, neg_zero, paperFT_weilRadicalTest, map_mul, map_pow]
  ring


/-! ### Plancherel with a tilt -/

theorem integral_norm_paperFT_sq {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 = 2 * π * ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have h := integral_normSq_paperFT_mul_cos_eq hf hfs 0
  simp only [mul_zero, Real.cos_zero, mul_one, neg_zero] at h
  rw [h, weilTest_apply]
  have : (fun t : ℝ => f t * starRingEnd ℂ (f (t - 0))) = fun t => ((‖f t‖ ^ 2 : ℝ) : ℂ) := by
    funext t; rw [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [this, integral_complex_ofReal, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

theorem tsupport_tilt_subset (k : ℝ → ℂ) (b : ℝ) : tsupport (tilt k b) ⊆ tsupport k := by
  apply closure_mono
  intro u hu
  simp only [Function.mem_support, tilt, ne_eq, mul_eq_zero, not_or] at hu
  exact hu.1

theorem integral_norm_paperFT_tilt_sq {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (y : ℝ) :
    ∫ τ : ℝ, ‖paperFT (tilt f y) τ‖ ^ 2 = 2 * π * ∫ x : ℝ, ‖f x‖ ^ 2 * Real.exp (2 * y * x) := by
  rw [integral_norm_paperFT_sq (tilt_contDiff hf y) ((tsupport_tilt_subset f y).trans hfs)]
  congr 2; funext x
  simp only [tilt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow]
  rw [← Real.exp_nat_mul]; congr 2; push_cast; ring

theorem norm_Hfn_weilTest_line_le {f : ℝ → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (c t : ℝ) :
    ‖Hfn (EF.weilTest f f) ((c : ℂ) + t * I)‖ ≤
      (‖paperFT (tilt f (c - 1 / 2)) t‖ ^ 2 + ‖paperFT (tilt f (1 / 2 - c)) t‖ ^ 2) / 2 := by
  have h1 : Hfn (EF.weilTest f f) ((c : ℂ) + t * I) =
      Hfn f ((c : ℂ) + t * I) * starRingEnd ℂ (Hfn f (((1 - c : ℝ) : ℂ) + t * I)) := by
    unfold Hfn
    rw [EF.paperFT_weilTest hfc hfc hfs hfs]
    congr 3
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    apply Complex.ext
    · simp
    · simp; ring
  rw [h1, norm_mul, Complex.norm_conj, Hfn_line, Hfn_line]
  rw [show (1 - c : ℝ) - 1 / 2 = 1 / 2 - c by ring]
  nlinarith [sq_nonneg (‖paperFT (tilt f (c - 1 / 2)) t‖ - ‖paperFT (tilt f (1 / 2 - c)) t‖)]


/-! ### The truncation error on the line `Re s = c` -/

theorem norm_cube_prod_sub_le {a b e f : ℂ} {M ε : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M)
    (he : ‖e‖ ≤ ε) (hf : ‖f‖ ≤ ε) :
    ‖((a - e) * (b - f)) ^ 3 - (a * b) ^ 3‖ ≤ (2 * M * ε + ε ^ 2) * (3 * (M + ε) ^ 4) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans ha
  have hε : 0 ≤ ε := (norm_nonneg _).trans he
  set u := (a - e) * (b - f)
  set v := a * b
  have huv : ‖u - v‖ ≤ 2 * M * ε + ε ^ 2 := by
    have : u - v = -(a * f) - e * b + e * f := by simp only [u, v]; ring
    rw [this]
    calc ‖-(a * f) - e * b + e * f‖ ≤ ‖a * f‖ + ‖e * b‖ + ‖e * f‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact (norm_sub_le _ _).trans (by rw [norm_neg])
      _ ≤ M * ε + ε * M + ε * ε := by
          rw [norm_mul, norm_mul, norm_mul]; gcongr
      _ = 2 * M * ε + ε ^ 2 := by ring
  have hu : ‖u‖ ≤ (M + ε) ^ 2 := by
    simp only [u]; rw [norm_mul, sq]
    exact mul_le_mul ((norm_sub_le _ _).trans (by linarith)) ((norm_sub_le _ _).trans
      (by linarith)) (norm_nonneg _) (by positivity)
  have hv : ‖v‖ ≤ (M + ε) ^ 2 := by
    simp only [v]; rw [norm_mul, sq]
    exact mul_le_mul (ha.trans (by linarith)) (hb.trans (by linarith)) (norm_nonneg _)
      (by positivity)
  have hfac : u ^ 3 - v ^ 3 = (u - v) * (u ^ 2 + u * v + v ^ 2) := by ring
  rw [hfac, norm_mul]
  have hq : ‖u ^ 2 + u * v + v ^ 2‖ ≤ 3 * (M + ε) ^ 4 := by
    have h1 : ‖u ^ 2‖ ≤ (M + ε) ^ 4 := by
      rw [norm_pow]; calc ‖u‖ ^ 2 ≤ ((M + ε) ^ 2) ^ 2 := by gcongr
        _ = (M + ε) ^ 4 := by ring
    have h2 : ‖u * v‖ ≤ (M + ε) ^ 4 := by
      rw [norm_mul]; calc ‖u‖ * ‖v‖ ≤ (M + ε) ^ 2 * (M + ε) ^ 2 := by gcongr
        _ = (M + ε) ^ 4 := by ring
    have h3 : ‖v ^ 2‖ ≤ (M + ε) ^ 4 := by
      rw [norm_pow]; calc ‖v‖ ^ 2 ≤ ((M + ε) ^ 2) ^ 2 := by gcongr
        _ = (M + ε) ^ 4 := by ring
    calc ‖u ^ 2 + u * v + v ^ 2‖ ≤ ‖u ^ 2‖ + ‖u * v‖ + ‖v ^ 2‖ := by
          refine (norm_add_le _ _).trans ?_; gcongr; exact norm_add_le _ _
      _ ≤ 3 * (M + ε) ^ 4 := by linarith
  exact mul_le_mul huv hq (norm_nonneg _) (by positivity)

theorem exists_tsupport_subset_Icc {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ a : ℝ, tsupport f ⊆ Icc (-a) a := by
  obtain ⟨L, hL⟩ := hf.isCompact.isBounded.subset_closedBall 0
  exact ⟨L, hL.trans (by rw [Real.closedBall_eq_Icc, zero_sub, zero_add])⟩

/-- **The truncation error on `Re s = c`.**  Replacing the truncated kernel factor of the spread
radical test by the full `ξ(s)³ ξ̄(s)³` changes the line integral against `B (−ζ'/ζ)` by at most
the tail mass `ε_R` of Riemann's kernel times tilted probe masses. -/
theorem exists_norm_integral_dilation_error_le {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m)
    (b : ℕ → ℝ) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    ∃ Mζ : ℝ, 0 ≤ Mζ ∧ ∀ τ₀ R Sp : ℝ, 0 < Sp →
      ‖∫ t : ℝ, dilationPoly S b ((c : ℂ) + t * I) *
          (Hfn (EF.weilTest (twistTest 0 τ₀ R Sp) (twistTest 0 τ₀ R Sp)) ((c : ℂ) + t * I) -
            riemannPhiTransform ((c : ℂ) + t * I) ^ 3 * xiConj ((c : ℂ) + t * I) ^ 3 *
              Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp)) ((c : ℂ) + t * I)) *
          (-logDeriv riemannZeta ((c : ℂ) + t * I))‖ ≤
        (∑ m ∈ S, |b m|) * Mζ *
          ((2 * (∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (1 * |u|)) *
              (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 * |u|)) +
            (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 * |u|)) ^ 2) *
            (3 * ((∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (1 * |u|)) +
              (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 * |u|))) ^ 4)) *
          (π * ((∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (c - 1 / 2) * x)) +
            ∫ x : ℝ, ‖dilationProbe τ₀ Sp x‖ ^ 2 * Real.exp (2 * (1 / 2 - c) * x))) := by
  obtain ⟨Mζ, hMζ0, hMζ⟩ := norm_logDeriv_zeta_le_of_one_lt_re hc1
  refine ⟨Mζ, hMζ0, fun τ₀ R Sp hSp => ?_⟩
  set CX := ∫ u : ℝ, ‖riemannPhiKernel u‖ * Real.exp (1 * |u|) with hCX
  set ε := ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 * |u|) with hε
  set G := dilationProbe τ₀ Sp with hG
  have hGc : ContDiff ℝ 2 G := contDiff_dilationProbe τ₀ Sp
  have hGs : HasCompactSupport G := hasCompactSupport_dilationProbe hSp
  obtain ⟨aG, haG⟩ := exists_tsupport_subset_Icc hGs
  set CB := ∑ m ∈ S, |b m| with hCB
  set Δ := (2 * CX * ε + ε ^ 2) * (3 * (CX + ε) ^ 4) with hΔ
  have hCB0 : 0 ≤ CB := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΔ0 : 0 ≤ Δ := by
    have : 0 ≤ CX := integral_nonneg fun _ => by positivity
    have : 0 ≤ ε := integral_nonneg fun _ => by positivity
    positivity
  set g : ℝ → ℝ := fun t => CB * Mζ * Δ *
    ((‖paperFT (tilt G (c - 1 / 2)) t‖ ^ 2 + ‖paperFT (tilt G (1 / 2 - c)) t‖ ^ 2) / 2) with hgdef
  have hgi : Integrable g := by
    have h1 := integrable_normSq_paperFT (tilt_contDiff hGc (c - 1 / 2))
      ((tsupport_tilt_subset G _).trans haG)
    have h2 := integrable_normSq_paperFT (tilt_contDiff hGc (1 / 2 - c))
      ((tsupport_tilt_subset G _).trans haG)
    exact ((h1.add h2).div_const 2).const_mul _
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
  · set s : ℂ := (c : ℂ) + t * I with hsdef
    set z : ℂ := (s - 1 / 2) / I with hzdef
    have hz1 : 1 / 2 + I * z = s := by
      rw [hzdef]; field_simp; ring
    have hz2 : 1 / 2 + I * starRingEnd ℂ z = 1 - starRingEnd ℂ s := by
      rw [hzdef, map_div₀, Complex.conj_I, map_sub]
      field_simp
      have h12 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
        rw [map_div₀, map_one, map_ofNat]
      rw [h12]; ring
    have hzim : |z.im| ≤ 1 := by
      rw [hzdef, hsdef]; simp; rw [abs_le]; constructor <;> linarith
    have hzim' : |(starRingEnd ℂ z).im| ≤ 1 := by rw [Complex.conj_im, abs_neg]; exact hzim
    have hsre : |s.re - 1 / 2| ≤ 1 := by
      rw [hsdef]; simp; rw [abs_le]; constructor <;> linarith
    have hfac := Hfn_weilTest_twistTest (τ₀ := τ₀) (R := R) hSp s
    rw [paperFT_riemannPhiCore_eq, paperFT_riemannPhiCore_eq, hz1, hz2,
      riemannPhiTransform_one_sub] at hfac
    have hY : starRingEnd ℂ (riemannPhiTransform (starRingEnd ℂ s)) = xiConj s := rfl
    rw [map_sub, hY] at hfac
    have hdiff : Hfn (EF.weilTest (twistTest 0 τ₀ R Sp) (twistTest 0 τ₀ R Sp)) s -
        riemannPhiTransform s ^ 3 * xiConj s ^ 3 * Hfn (EF.weilTest G G) s =
        (((riemannPhiTransform s - paperFT (riemannPhiTail R) z) *
          (xiConj s - starRingEnd ℂ (paperFT (riemannPhiTail R) (starRingEnd ℂ z)))) ^ 3 -
          (riemannPhiTransform s * xiConj s) ^ 3) * Hfn (EF.weilTest G G) s := by
      rw [hfac]; ring
    have hcube := norm_cube_prod_sub_le (M := CX) (ε := ε)
      (norm_riemannPhiTransform_le (by norm_num) hsre) (norm_xiConj_le (by norm_num) hsre)
      (norm_paperFT_riemannPhiTail_le (L := R) (by norm_num) hzim)
      (by rw [Complex.norm_conj]; exact norm_paperFT_riemannPhiTail_le (L := R) (by norm_num) hzim')
    have hK := norm_Hfn_weilTest_line_le hGc.continuous hGs c t
    rw [hdiff, norm_mul, norm_mul, norm_mul, norm_neg]
    calc ‖dilationPoly S b s‖ * (‖_‖ * ‖Hfn (EF.weilTest G G) s‖) * ‖logDeriv riemannZeta s‖
        ≤ CB * (Δ * ((‖paperFT (tilt G (c - 1 / 2)) t‖ ^ 2 +
            ‖paperFT (tilt G (1 / 2 - c)) t‖ ^ 2) / 2)) * Mζ := by
          gcongr
          · exact norm_dilationPoly_le hS b (by rw [hsdef]; simp; linarith)
          · exact hMζ t
      _ = g t := by simp only [hgdef]; ring
  · simp only [hgdef]
    rw [integral_const_mul, integral_div, integral_add
      (integrable_normSq_paperFT (tilt_contDiff hGc _) ((tsupport_tilt_subset G _).trans haG))
      (integrable_normSq_paperFT (tilt_contDiff hGc _) ((tsupport_tilt_subset G _).trans haG)),
      integral_norm_paperFT_tilt_sq hGc haG, integral_norm_paperFT_tilt_sq hGc haG]
    ring


/-! ### The critical line: the probe factors out -/

theorem Hfn_weilTest_dilationProbe {τ₀ Sp : ℝ} (hSp : 0 < Sp) (s : ℂ) :
    Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp)) s =
      Hfn (EF.weilTest bumpCube bumpCube) s *
        (paperFT (twistProbe τ₀ Sp) ((s - 1 / 2) / I) *
          starRingEnd ℂ (paperFT (twistProbe τ₀ Sp) (starRingEnd ℂ ((s - 1 / 2) / I)))) := by
  have hGc : Continuous (dilationProbe τ₀ Sp) := (contDiff_dilationProbe τ₀ Sp).continuous
  have hGs := hasCompactSupport_dilationProbe (τ₀ := τ₀) hSp
  have hHc : Continuous bumpCube := contDiff_bumpCube.continuous
  unfold Hfn
  rw [EF.paperFT_weilTest hGc hGc hGs hGs, EF.paperFT_weilTest hHc hHc hasCompactSupport_bumpCube
    hasCompactSupport_bumpCube, paperFT_dilationProbe hSp, paperFT_dilationProbe hSp,
    paperFT_bumpCube, paperFT_bumpCube]
  simp only [map_mul, map_pow]
  ring

theorem Hfn_weilTest_bumpCube_one : Hfn (EF.weilTest bumpCube bumpCube) 1 = 0 := by
  have hHc : Continuous bumpCube := contDiff_bumpCube.continuous
  unfold Hfn
  rw [EF.paperFT_weilTest hHc hHc hasCompactSupport_bumpCube hasCompactSupport_bumpCube,
    paperFT_bumpCube]
  have : ((1 : ℂ) - 1 / 2) / I = -(I / 2) := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [this, paperFT_weilBumpPolarFree_neg_half_I]
  ring

theorem Hfn_weilTest_dilationProbe_one {τ₀ Sp : ℝ} (hSp : 0 < Sp) :
    Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp)) 1 = 0 := by
  rw [Hfn_weilTest_dilationProbe hSp, Hfn_weilTest_bumpCube_one, zero_mul]

/-- On the critical line the shift integrand of the spread test is the bump-cube integrand times
`|q̂_S(t)|²`. -/
theorem dilationShiftIntegrand_dilationProbe_critical {S : Finset ℕ} (b : ℕ → ℝ) {τ₀ Sp : ℝ}
    (hSp : 0 < Sp) (t : ℝ) :
    dilationShiftIntegrand S b (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp))
        (((1 / 2 : ℝ) : ℂ) + t * I) =
      dilationShiftIntegrand S b (EF.weilTest bumpCube bumpCube) (((1 / 2 : ℝ) : ℂ) + t * I) *
        ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ) := by
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I with hsdef
  have hz : (s - 1 / 2) / I = (t : ℂ) := by
    rw [hsdef]; have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp; push_cast; ring
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsdef] at this; simp at this
  have hP : paperFT (twistProbe τ₀ Sp) ((s - 1 / 2) / I) *
      starRingEnd ℂ (paperFT (twistProbe τ₀ Sp) (starRingEnd ℂ ((s - 1 / 2) / I))) =
      ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ) := by
    rw [hz, Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hK := Hfn_weilTest_dilationProbe (τ₀ := τ₀) hSp s
  rw [hP] at hK
  have hD : dslope (Hfn (EF.weilTest (dilationProbe τ₀ Sp) (dilationProbe τ₀ Sp))) 1 s =
      dslope (Hfn (EF.weilTest bumpCube bumpCube)) 1 s *
        ((‖paperFT (twistProbe τ₀ Sp) t‖ ^ 2 : ℝ) : ℂ) := by
    rw [dslope_of_ne _ hs1, dslope_of_ne _ hs1, slope_def_field, slope_def_field,
      Hfn_weilTest_dilationProbe_one hSp, Hfn_weilTest_bumpCube_one, hK]
    ring
  unfold dilationShiftIntegrand
  rw [hK, hD]
  ring

end RHTower
