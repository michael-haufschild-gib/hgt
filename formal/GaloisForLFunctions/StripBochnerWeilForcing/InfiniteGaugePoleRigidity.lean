import GaloisForLFunctions.RHTower.EntireAutomorphism
import GaloisForLFunctions.RHTower.TwinRigidityPoleOrder
import GaloisForLFunctions.RHTower.OneSignTailImpossible
import GaloisForLFunctions.RHTower.LandauAbscissaWitnesses
import GaloisForLFunctions.RHTower.LaplaceAbscissaExists
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing
import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount

/-!
# Whole-Strip Pole-Budget Rigidity: Infinite Gauge Collapse and Simple-Pole Refund Obstruction

Across the full critical strip `0 < Re s < 1`, the pole budget `κ` enforces two global structural
laws on multiplicative deformations:

1. **Infinite multiplicative gauge collapse (`exists_monic_poly_of_completed_gauge`,
   `exists_monic_poly_of_laplace_exp_gauge`):** Let `G` be bounded on a right half-plane `Re s ≥ σ₀`
   with `G(σ) → 1` along `+∞` (in particular `G(s) = exp(∫_{(0,∞)} f(u) e^{-su} dμ(u))` for any
   measure `μ` and finite-abscissa profile `f`). If `E(s) = (s(s − 1))^κ G(s)` extends to an entire
   function of finite order satisfying `E(1 − s) = ε E(s)` (`‖ε‖ = 1`), then `ε = 1` and `E`
   collapses to a **monic polynomial of exact degree `2 κ`**. Consequently, the total zero
   multiplicity of `E` across all of `ℂ` is at most `2 κ`, and when `E(s̄) = conj(E(s))`, the total
   multiplicity of complex off-critical orbits `{ρ, ρ̄, 1 − ρ, 1 − ρ̄}` (`Re ρ ≠ 1/2`, `Im ρ > 0`) is
   at most `⌊κ / 2⌋`.

2. **Simple-pole critical-refund rigidity (`simple_pole_nonneg_laplace_refund_rigidity`):** At pole
   order two (`κ = 2`), cancelling a critical zero pair of `ξ` refunds one unit of pole budget and
   permits genuinely complex off-critical quartets with a nonnegative logarithmic deformation
   (`RefundedComplexStray`). At simple pole order (`κ = 1`), no critical-zero refund is possible:
   if `ν` is any nonnegative Borel measure on `(0, ∞)` and `E` is any nonzero entire function with
   `E(1 − s) = ε E(s)` (`ε ≠ 0`) satisfying `−(E'/E)(σ) + (ξ'/ξ)(σ) = ∫_{(0,∞)} e^{−σu} dν(u)` on a
   right ray `σ > σ₁`, then `ν|_{(0,∞)} = 0` and `E(s) = (E(1)/ξ(1)) ξ(s)` on all of `ℂ`. No
   finite-order growth assumption on `E` is needed.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory Asymptotics Polynomial
open scoped ENNReal
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa
  complexLaplace_ofReal hasDerivAt_complexLaplace differentiableOn_complexLaplace
  integrable_cexp_of_gt_abscissa integrableOn_exp_neg_of_gt_abscissa
  isAbscissa_volume_zero exists_isAbscissa false_of_analyticAt_abscissa)
open GaloisForLFunctions.HTGeometry (analyticOrderAt_eval_eq_rootMultiplicity)

namespace GaloisForLFunctions.StripBochnerWeilForcing

/-! ### 1. Polynomial degree and monicity from asymptotic scaling -/

private theorem tendsto_eval_div_pow_natDegree (P : ℂ[X]) :
    Tendsto (fun σ : ℝ => P.eval (σ : ℂ) / (σ : ℂ) ^ P.natDegree)
      atTop (𝓝 P.leadingCoeff) := by
  have hsum : ∀ σ : ℝ, 0 < σ →
      P.eval (σ : ℂ) / (σ : ℂ) ^ P.natDegree =
        ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * ((σ : ℂ)⁻¹) ^ (P.natDegree - i) := by
    intro σ hσ
    have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
    rw [Polynomial.eval_eq_sum_range, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpow : (σ : ℂ) ^ P.natDegree = (σ : ℂ) ^ i * (σ : ℂ) ^ (P.natDegree - i) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    rw [hpow, inv_pow]
    field_simp [pow_ne_zero i hσ0, pow_ne_zero (P.natDegree - i) hσ0]
  have hinv : Tendsto (fun σ : ℝ => ((σ : ℂ))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => ((σ⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa using h1
  have hlim : Tendsto
      (fun σ : ℝ => ∑ i ∈ Finset.range (P.natDegree + 1),
        P.coeff i * ((σ : ℂ)⁻¹) ^ (P.natDegree - i))
      atTop
      (𝓝 (∑ i ∈ Finset.range (P.natDegree + 1),
        if i = P.natDegree then P.coeff i else 0)) := by
    refine tendsto_finset_sum _ fun i hi => ?_
    have hle : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases heq : i = P.natDegree
    · subst heq
      simp only [Nat.sub_self, pow_zero, mul_one, ↓reduceIte]
      exact tendsto_const_nhds
    · have hpos : 0 < P.natDegree - i := Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      simp only [heq, ↓reduceIte]
      have hp : Tendsto (fun σ : ℝ => ((σ : ℂ)⁻¹) ^ (P.natDegree - i)) atTop (𝓝 0) := by
        simpa [ zero_pow hpos.ne' ] using hinv.pow (P.natDegree - i)
      simpa using hp.const_mul (P.coeff i)
  have heval_sum :
      (∑ i ∈ Finset.range (P.natDegree + 1),
        if i = P.natDegree then P.coeff i else 0) = P.leadingCoeff := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (Nat.lt_succ_self _)),
      Polynomial.leadingCoeff]
  rw [← heval_sum]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
  exact (hsum σ hσ).symm

/-- A complex polynomial satisfying `P(σ) / σ^d → 1` as `σ → +∞` is monic of exact degree `d`. -/
theorem monic_and_natDegree_of_tendsto_eval_div_pow {P : ℂ[X]} {d : ℕ}
    (hlim : Tendsto (fun σ : ℝ => P.eval (σ : ℂ) / (σ : ℂ) ^ d) atTop (𝓝 1)) :
    P.Monic ∧ P.natDegree = d := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp only [Polynomial.eval_zero, zero_div] at hlim
    exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hlim)
  have hlead := tendsto_eval_div_pow_natDegree P
  have hinv : Tendsto (fun σ : ℝ => ((σ : ℂ))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => ((σ⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa using h1
  have hdeg : P.natDegree = d := by
    rcases lt_trichotomy P.natDegree d with hlt | heq | hgt
    · exfalso
      have hpos : 0 < d - P.natDegree := Nat.sub_pos_of_lt hlt
      have hp : Tendsto (fun σ : ℝ => ((σ : ℂ)⁻¹) ^ (d - P.natDegree)) atTop (𝓝 0) := by
        simpa [zero_pow hpos.ne'] using hinv.pow (d - P.natDegree)
      have hprod : Tendsto
          (fun σ : ℝ => (P.eval (σ : ℂ) / (σ : ℂ) ^ P.natDegree) *
            ((σ : ℂ)⁻¹) ^ (d - P.natDegree))
          atTop (𝓝 (P.leadingCoeff * 0)) := hlead.mul hp
      have heq_fn : (fun σ : ℝ => P.eval (σ : ℂ) / (σ : ℂ) ^ d) =ᶠ[atTop]
          fun σ : ℝ => (P.eval (σ : ℂ) / (σ : ℂ) ^ P.natDegree) *
            ((σ : ℂ)⁻¹) ^ (d - P.natDegree) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
        have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
        have hpow : (σ : ℂ) ^ d = (σ : ℂ) ^ P.natDegree * (σ : ℂ) ^ (d - P.natDegree) := by
          rw [← pow_add, Nat.add_sub_of_le hlt.le]
        rw [hpow, inv_pow]
        field_simp [pow_ne_zero P.natDegree hσ0, pow_ne_zero (d - P.natDegree) hσ0]
      have h01 := tendsto_nhds_unique hlim (hprod.congr' heq_fn.symm)
      simp at h01
    · exact heq
    · exfalso
      have hpos : 0 < P.natDegree - d := Nat.sub_pos_of_lt hgt
      have hp : Tendsto (fun σ : ℝ => ((σ : ℂ)⁻¹) ^ (P.natDegree - d)) atTop (𝓝 0) := by
        simpa [zero_pow hpos.ne'] using hinv.pow (P.natDegree - d)
      have hprod : Tendsto
          (fun σ : ℝ => (P.eval (σ : ℂ) / (σ : ℂ) ^ d) * ((σ : ℂ)⁻¹) ^ (P.natDegree - d))
          atTop (𝓝 (1 * 0)) := hlim.mul hp
      have heq_fn : (fun σ : ℝ => P.eval (σ : ℂ) / (σ : ℂ) ^ P.natDegree) =ᶠ[atTop]
          fun σ : ℝ => (P.eval (σ : ℂ) / (σ : ℂ) ^ d) * ((σ : ℂ)⁻¹) ^ (P.natDegree - d) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
        have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
        have hpow : (σ : ℂ) ^ P.natDegree = (σ : ℂ) ^ d * (σ : ℂ) ^ (P.natDegree - d) := by
          rw [← pow_add, Nat.add_sub_of_le hgt.le]
        rw [hpow, inv_pow]
        field_simp [pow_ne_zero d hσ0, pow_ne_zero (P.natDegree - d) hσ0]
      have hc0 := tendsto_nhds_unique hlead (hprod.congr' heq_fn.symm)
      simp only [mul_zero] at hc0
      exact Polynomial.leadingCoeff_ne_zero.mpr hP0 hc0
  refine ⟨?_, hdeg⟩
  rw [Polynomial.Monic]
  rw [hdeg] at hlead
  exact tendsto_nhds_unique hlead hlim

/-! ### 2. Infinite multiplicative gauge collapse across `ℂ` -/

/-- **Infinite multiplicative gauge collapse law.** Any holomorphic factor `G` bounded on a right
half-plane `Re s ≥ σ₀` with `G(σ) → 1` along `+∞` whose pole-cleared completion
`E(s) = (s(s − 1))^κ G(s)` extends to an entire function of finite order satisfying
`E(1 − s) = ε E(s)` (`‖ε‖ = 1`) forces `ε = 1` and collapses `E` to a monic polynomial of exact
degree `2 κ`. -/
theorem exists_monic_poly_of_completed_gauge {κ : ℕ} {σ₀ S : ℝ} {G E : ℂ → ℂ} {ε : ℂ}
    (hS : 0 ≤ S)
    (hG : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ S)
    (hGlim : Tendsto (fun σ : ℝ => G (σ : ℂ)) atTop (𝓝 1))
    (hE : Differentiable ℂ E)
    (hfin : ∃ ρ C₀ : ℝ, ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ))
    (hε : ‖ε‖ = 1)
    (hsym : ∀ s, E (1 - s) = ε * E s)
    (hcomp : ∀ s : ℂ, σ₀ < s.re → E s = (s * (s - 1)) ^ κ * G s) :
    ε = 1 ∧ ∃ P : ℂ[X], P.Monic ∧ P.natDegree = 2 * κ ∧ ∀ s : ℂ, E s = P.eval s := by
  obtain ⟨ρ, C₀, hfin⟩ := hfin
  set N : ℝ := max (max σ₀ 2) 0 + 1 with hNdef
  have hN0 : 0 ≤ N := by
    have : (0 : ℝ) ≤ max (max σ₀ 2) 0 := le_max_right _ _
    linarith
  have hN1 : 1 ≤ N := by
    have h2 : (2 : ℝ) ≤ max σ₀ 2 := le_max_right _ _
    have h3 : max σ₀ 2 ≤ max (max σ₀ 2) 0 := le_max_left _ _
    linarith
  have hσN : σ₀ < N := by
    have h1 : σ₀ ≤ max σ₀ 2 := le_max_left _ _
    have h2 : max σ₀ 2 ≤ max (max σ₀ 2) 0 := le_max_left _ _
    linarith
  have hflip : ∀ s, ‖E s‖ = ‖E (1 - s)‖ := by
    intro s
    have h := hsym (1 - s)
    rw [sub_sub_cancel] at h
    rw [h, norm_mul, hε, one_mul]
  have hright : ∀ s : ℂ, N ≤ s.re → ‖E s‖ ≤ S * (‖s‖ + 1) ^ (2 * κ) := by
    intro s hs
    rw [hcomp s (hσN.trans_le hs), norm_mul, norm_pow, norm_mul]
    have h1 : ‖s‖ ≤ ‖s‖ + 1 := by linarith
    have h2 : ‖s - 1‖ ≤ ‖s‖ + 1 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by simp
    have hGs : ‖G s‖ ≤ S := hG s (hσN.le.trans hs)
    calc (‖s‖ * ‖s - 1‖) ^ κ * ‖G s‖
        ≤ ((‖s‖ + 1) * (‖s‖ + 1)) ^ κ * S := by gcongr
      _ = S * (‖s‖ + 1) ^ (2 * κ) := by rw [← pow_two, ← pow_mul]; ring
  have hleft : ∀ s : ℂ, s.re ≤ 1 - N →
      ‖E s‖ ≤ S * 2 ^ (2 * κ) * (‖s‖ + 1) ^ (2 * κ) := by
    intro s hs
    rw [hflip s]
    have hre : N ≤ (1 - s).re := by simp; linarith
    have hn : ‖1 - s‖ + 1 ≤ 2 * (‖s‖ + 1) := by
      have : ‖1 - s‖ ≤ 1 + ‖s‖ := by
        calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ := by simp
      linarith [norm_nonneg s]
    calc ‖E (1 - s)‖ ≤ S * (‖1 - s‖ + 1) ^ (2 * κ) := hright (1 - s) hre
      _ ≤ S * (2 * (‖s‖ + 1)) ^ (2 * κ) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hn _) hS
      _ = S * 2 ^ (2 * κ) * (‖s‖ + 1) ^ (2 * κ) := by rw [mul_pow]; ring
  -- Apply Phragmén–Lindelöf to `w(z) = E(z) / (z + (N + 1))^{2κ}` on `1 - N ≤ Re z ≤ N`.
  set a : ℂ := ((N + 1 : ℝ) : ℂ) with hadef
  set Q : ℂ → ℂ := fun z => (z + a) ^ (2 * κ) with hQdef
  set w : ℂ → ℂ := fun z => E z / Q z with hwdef
  have hza_ge : ∀ z : ℂ, 1 - N ≤ z.re → 2 ≤ ‖z + a‖ := by
    intro z hz
    have hre : 2 ≤ (z + a).re := by
      rw [Complex.add_re, hadef, Complex.ofReal_re]
      linarith
    exact hre.trans (Complex.re_le_norm _)
  have hQ1 : ∀ z : ℂ, 1 - N ≤ z.re → 1 ≤ ‖Q z‖ := by
    intro z hz
    rw [hQdef, norm_pow]
    exact one_le_pow₀ ((by norm_num : (1 : ℝ) ≤ 2).trans (hza_ge z hz))
  have hw_diff : DiffContOnCl ℂ w (Complex.re ⁻¹' Ioo (1 - N) N) := by
    have hopen : IsOpen {z : ℂ | -N < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hsub : closure (Complex.re ⁻¹' Ioo (1 - N) N) ⊆ {z : ℂ | -N < z.re} := by
      have hcl : IsClosed {z : ℂ | 1 - N ≤ z.re} :=
        isClosed_le continuous_const Complex.continuous_re
      have h1 : closure (Complex.re ⁻¹' Ioo (1 - N) N) ⊆ {z : ℂ | 1 - N ≤ z.re} :=
        hcl.closure_subset_iff.mpr fun z hz => hz.1.le
      exact fun z hz => by have := h1 hz; change -N < z.re; linarith
    have hdOn : DifferentiableOn ℂ w {z : ℂ | -N < z.re} := by
      intro z hz
      change -N < z.re at hz
      have hQa : Q z ≠ 0 := by
        rw [hQdef]
        refine pow_ne_zero _ (fun h0 => ?_)
        have hre := congrArg Complex.re h0
        simp only [Complex.add_re, hadef, Complex.ofReal_re, Complex.zero_re] at hre
        linarith
      exact ((hE z).div ((differentiableAt_id.add_const a).pow _) hQa).differentiableWithinAt
    exact ⟨hdOn.mono ( subset_closure.trans hsub ), hdOn.continuousOn.mono hsub⟩
  obtain ⟨c, hc, B, hEO⟩ := RHTower.CompletionGrowth.isBigO_strip_of_finiteOrder_at hfin hN1
  have hwO : w =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (1 - N) N)]
      fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩).trans hEO
    have hre : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo (1 - N) N), z.re ∈ Ioo (1 - N) N :=
      Eventually.filter_mono inf_le_right (eventually_principal.mpr fun z hz => hz)
    filter_upwards [hre] with z hz
    rw [one_mul, hwdef, norm_div]
    exact div_le_self (norm_nonneg _) (hQ1 z hz.1.le)
  set B₀ : ℝ := S * 2 ^ (2 * κ) * (N + 3) ^ (2 * κ) with hB₀def
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hnorm_le_za : ∀ z : ℂ, 1 - N ≤ z.re →
      (‖z‖ + 1) ^ (2 * κ) ≤ (N + 3) ^ (2 * κ) * ‖Q z‖ := by
    intro z hz
    have h2 := hza_ge z hz
    have h1 : 1 ≤ ‖z + a‖ := by linarith
    have htri : ‖z‖ ≤ ‖z + a‖ + (N + 1) := by
      calc ‖z‖ = ‖(z + a) - a‖ := by ring_nf
        _ ≤ ‖z + a‖ + ‖a‖ := norm_sub_le _ _
        _ = ‖z + a‖ + (N + 1) := by
            rw [hadef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hlin : ‖z‖ + 1 ≤ (N + 3) * ‖z + a‖ := by nlinarith
    rw [hQdef, norm_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlin _
  have hw_left : ∀ z : ℂ, z.re = 1 - N → ‖w z‖ ≤ B₀ := by
    intro z hz
    have hQpos : 0 < ‖Q z‖ := lt_of_lt_of_le zero_lt_one (hQ1 z hz.ge)
    rw [hwdef, norm_div, div_le_iff₀ hQpos]
    calc ‖E z‖ ≤ S * 2 ^ (2 * κ) * (‖z‖ + 1) ^ (2 * κ) := hleft z hz.le
      _ ≤ S * 2 ^ (2 * κ) * ((N + 3) ^ (2 * κ) * ‖Q z‖) :=
          mul_le_mul_of_nonneg_left (hnorm_le_za z hz.ge) (by positivity)
      _ = B₀ * ‖Q z‖ := by rw [hB₀def]; ring
  have hw_right : ∀ z : ℂ, z.re = N → ‖w z‖ ≤ B₀ := by
    intro z hz
    have hz1 : 1 - N ≤ z.re := by linarith
    have hQpos : 0 < ‖Q z‖ := lt_of_lt_of_le zero_lt_one (hQ1 z hz1)
    have hpow2 : (1 : ℝ) ≤ 2 ^ (2 * κ) := one_le_pow₀ (by norm_num)
    rw [hwdef, norm_div, div_le_iff₀ hQpos]
    calc ‖E z‖ ≤ S * (‖z‖ + 1) ^ (2 * κ) := hright z hz.ge
      _ ≤ S * 2 ^ (2 * κ) * (‖z‖ + 1) ^ (2 * κ) := by
          nlinarith [pow_nonneg (by positivity : 0 ≤ ‖z‖ + 1) (2 * κ)]
      _ ≤ S * 2 ^ (2 * κ) * ((N + 3) ^ (2 * κ) * ‖Q z‖) :=
          mul_le_mul_of_nonneg_left (hnorm_le_za z hz1) (by positivity)
      _ = B₀ * ‖Q z‖ := by rw [hB₀def]; ring
  have hstrip : ∀ z : ℂ, 1 - N ≤ z.re → z.re ≤ N →
      ‖E z‖ ≤ B₀ * (N + 2) ^ (2 * κ) * (‖z‖ + 1) ^ (2 * κ) := by
    intro z h1 h2
    have hwz : ‖w z‖ ≤ B₀ :=
      PhragmenLindelof.vertical_strip hw_diff hwO hw_left hw_right h1 h2
    have hQpos : 0 < ‖Q z‖ := lt_of_lt_of_le zero_lt_one (hQ1 z h1)
    have hEw : ‖E z‖ ≤ B₀ * ‖Q z‖ := by
      rw [hwdef, norm_div, div_le_iff₀ hQpos] at hwz
      exact hwz
    have hQub : ‖Q z‖ ≤ (N + 2) ^ (2 * κ) * (‖z‖ + 1) ^ (2 * κ) := by
      have hza_ub : ‖z + a‖ ≤ (N + 2) * (‖z‖ + 1) := by
        calc ‖z + a‖ ≤ ‖z‖ + ‖a‖ := norm_add_le _ _
          _ = ‖z‖ + (N + 1) := by
              rw [hadef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          _ ≤ (N + 2) * (‖z‖ + 1) := by nlinarith [norm_nonneg z]
      rw [hQdef, norm_pow, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hza_ub _
    calc ‖E z‖ ≤ B₀ * ‖Q z‖ := hEw
      _ ≤ B₀ * ((N + 2) ^ (2 * κ) * (‖z‖ + 1) ^ (2 * κ)) :=
          mul_le_mul_of_nonneg_left hQub hB₀0
      _ = B₀ * (N + 2) ^ (2 * κ) * (‖z‖ + 1) ^ (2 * κ) := by ring
  -- Uniform polynomial bound across all of `ℂ`.
  set M₀ : ℝ := S * 2 ^ (2 * κ) + B₀ * (N + 2) ^ (2 * κ) with hM₀def
  have hgrow : ∀ z : ℂ, ‖E z‖ ≤ M₀ * (‖z‖ + 1) ^ (2 * κ) := by
    intro z
    have hp0 : 0 ≤ (‖z‖ + 1) ^ (2 * κ) := by positivity
    rcases le_or_gt N z.re with h2 | h2
    · have hr := hright z h2
      have hpow2 : (1 : ℝ) ≤ 2 ^ (2 * κ) := one_le_pow₀ (by norm_num)
      have hb : 0 ≤ B₀ * (N + 2) ^ (2 * κ) := by positivity
      rw [hM₀def]
      nlinarith
    rcases le_or_gt (1 - N) z.re with h1 | h1
    · have hs := hstrip z h1 h2.le
      have ha0 : 0 ≤ S * 2 ^ (2 * κ) := by positivity
      rw [hM₀def]
      nlinarith
    · have hl := hleft z h1.le
      have hb : 0 ≤ B₀ * (N + 2) ^ (2 * κ) := by positivity
      rw [hM₀def]
      nlinarith
  obtain ⟨P, hP⟩ := RHTower.exists_polynomial_of_polyGrowth hE hgrow
  -- Asymptotic `P(σ) / σ^{2κ} → 1` along `+∞`.
  have hinv : Tendsto (fun σ : ℝ => ((σ : ℂ))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => ((σ⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa using h1
  have hrat : Tendsto (fun σ : ℝ => (1 - ((σ : ℂ))⁻¹) ^ κ * G (σ : ℂ)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun σ : ℝ => (1 - ((σ : ℂ))⁻¹) ^ κ) atTop (𝓝 ((1 - (0 : ℂ)) ^ κ)) :=
      (tendsto_const_nhds.sub hinv).pow κ
    simpa using h1.mul hGlim
  have hPlim : Tendsto (fun σ : ℝ => P.eval (σ : ℂ) / (σ : ℂ) ^ (2 * κ)) atTop (𝓝 1) := by
    refine hrat.congr' ?_
    filter_upwards [eventually_gt_atTop (max σ₀ 1)] with σ hσ
    have hσ0 : σ₀ < σ := (le_max_left _ _).trans_lt hσ
    have hσ1 : 0 < σ := zero_lt_one.trans ((le_max_right _ _).trans_lt hσ)
    have hσc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ1.ne'
    rw [← hP (σ : ℂ), hcomp (σ : ℂ) (by simpa using hσ0)]
    have hpow : (((σ : ℂ) * ((σ : ℂ) - 1)) ^ κ) / (σ : ℂ) ^ (2 * κ) =
        (1 - ((σ : ℂ))⁻¹) ^ κ := by
      have h2k : (σ : ℂ) ^ (2 * κ) = ((σ : ℂ) * (σ : ℂ)) ^ κ := by
        rw [← pow_two, pow_mul]
      rw [h2k, ← div_pow]
      congr 1
      field_simp [hσc]
    rw [mul_div_right_comm, hpow]
  obtain ⟨hMonic, hDeg⟩ := monic_and_natDegree_of_tendsto_eval_div_pow hPlim
  -- Extract `ε = 1` from `E(1 - (-σ)) = ε E(-σ)`, i.e., `E(1 + σ) = ε E(-σ)` along `+∞`.
  have hε1 : ε = 1 := by
    have hshift : Tendsto (fun σ : ℝ => E ((1 + σ : ℝ) : ℂ) / (σ : ℂ) ^ (2 * κ))
        atTop (𝓝 1) := by
      have h1 : Tendsto (fun σ : ℝ => P.eval ((1 + σ : ℝ) : ℂ) / ((1 + σ : ℝ) : ℂ) ^ (2 * κ))
          atTop (𝓝 1) := hPlim.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
      have h2 : Tendsto (fun σ : ℝ => (((1 + σ : ℝ) : ℂ) / (σ : ℂ)) ^ (2 * κ))
          atTop (𝓝 1) := by
        have hq : Tendsto (fun σ : ℝ => (1 : ℂ) + ((σ : ℂ))⁻¹) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add hinv
        have hqp : Tendsto (fun σ : ℝ => ((1 : ℂ) + ((σ : ℂ))⁻¹) ^ (2 * κ)) atTop (𝓝 1) := by
          simpa using hq.pow (2 * κ)
        refine hqp.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
        have hσc : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
        congr 1
        push_cast
        field_simp [hσc]
      refine (by simpa using h1.mul h2 : Tendsto _ atTop (𝓝 (1 : ℂ))).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
      have hs1 : ((1 + σ : ℝ) : ℂ) ^ (2 * κ) ≠ 0 :=
        pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (by linarith))
      rw [← hP]
      field_simp [hs1]
    have hneg : Tendsto (fun σ : ℝ => E (-(σ : ℂ)) / (σ : ℂ) ^ (2 * κ)) atTop (𝓝 1) := by
      have hlead := tendsto_eval_div_pow_natDegree (P.comp (-Polynomial.X))
      have hnd : (P.comp (-Polynomial.X)).natDegree = 2 * κ := by
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_neg, Polynomial.natDegree_X,
          mul_one, hDeg]
      have hlc : (P.comp (-Polynomial.X)).leadingCoeff = 1 := by
        rw [Polynomial.leadingCoeff_comp (by simp), hMonic.leadingCoeff,
          Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X, hDeg, pow_mul,
          neg_one_sq, one_pow, one_mul]
      rw [hnd, hlc] at hlead
      refine hlead.congr' ?_
      filter_upwards with σ
      rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, ← hP]
    have hε_lim : Tendsto (fun σ : ℝ => E ((1 + σ : ℝ) : ℂ) / (σ : ℂ) ^ (2 * κ))
        atTop (𝓝 ε) := by
      refine (by simpa using hneg.const_mul ε : Tendsto _ atTop (𝓝 ε)).congr' ?_
      filter_upwards with σ
      have he : ((1 + σ : ℝ) : ℂ) = 1 - (-(σ : ℂ)) := by push_cast; ring
      rw [he, hsym (-(σ : ℂ)), mul_div_assoc]
    exact (tendsto_nhds_unique hε_lim hshift)
  exact ⟨hε1, P, hMonic, hDeg, hP⟩

/-- **Infinite Borel exponential-gauge collapse.** For any measure `μ` on `ℝ` and profile
`f : ℝ → ℂ` with `∫_{(0,∞)} ‖f(u)‖ e^{−σ₀ u} dμ < ∞`, if
`G(s) = exp(∫_{(0,∞)} f(u) e^{−su} dμ(u))` has an entire finite-order completion
`E(s) = (s(s − 1))^κ G(s)` satisfying `E(1 − s) = ε E(s)` (`‖ε‖ = 1`), then `ε = 1` and `E`
collapses to a monic polynomial of exact degree `2 κ`. -/
theorem exists_monic_poly_of_laplace_exp_gauge {κ : ℕ} {σ₀ : ℝ} {μ : Measure ℝ}
    {f : ℝ → ℂ} {E : ℂ → ℂ} {ε : ℂ}
    (hf_meas : AEStronglyMeasurable f (μ.restrict (Ioi (0 : ℝ))))
    (hf_int : Integrable (fun u : ℝ => ‖f u‖ * Real.exp (-σ₀ * u)) (μ.restrict (Ioi (0 : ℝ))))
    (hE : Differentiable ℂ E)
    (hfin : ∃ ρ C₀ : ℝ, ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ))
    (hε : ‖ε‖ = 1)
    (hsym : ∀ s, E (1 - s) = ε * E s)
    (hcomp : ∀ s : ℂ, σ₀ < s.re →
      E s = (s * (s - 1)) ^ κ *
        Complex.exp (∫ u in Ioi (0 : ℝ), f u * Complex.exp (-s * (u : ℂ)) ∂μ)) :
    ε = 1 ∧ ∃ P : ℂ[X], P.Monic ∧ P.natDegree = 2 * κ ∧ ∀ s : ℂ, E s = P.eval s := by
  set G : ℂ → ℂ := fun s =>
    Complex.exp (∫ u in Ioi (0 : ℝ), f u * Complex.exp (-s * (u : ℂ)) ∂μ) with hGdef
  set I₀ : ℝ := ∫ u in Ioi (0 : ℝ), ‖f u‖ * Real.exp (-σ₀ * u) ∂μ with hI₀def
  have hG_bound : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ Real.exp I₀ := by
    intro s hs
    rw [hGdef, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    calc (∫ u in Ioi (0 : ℝ), f u * Complex.exp (-s * (u : ℂ)) ∂μ).re
        ≤ ‖∫ u in Ioi (0 : ℝ), f u * Complex.exp (-s * (u : ℂ)) ∂μ‖ := Complex.re_le_norm _
      _ ≤ ∫ u in Ioi (0 : ℝ), ‖f u * Complex.exp (-s * (u : ℂ))‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ I₀ := by
          refine integral_mono_ae ?_ hf_int ?_
          · refine hf_int.mono' ?_ ?_
            · exact (hf_meas.mul (Complex.continuous_exp.comp
                (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable).norm
            · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
              have hu0 : 0 ≤ u := le_of_lt hu
              rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_exp]
              have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
              rw [hre]
              exact mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (by nlinarith)) (norm_nonneg _)
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            have hu0 : 0 ≤ u := le_of_lt hu
            rw [norm_mul, Complex.norm_exp]
            have hre : (-s * (u : ℂ)).re = -s.re * u := by simp
            rw [hre]
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by nlinarith)) (norm_nonneg _)
  have hG_lim : Tendsto (fun σ : ℝ => G (σ : ℂ)) atTop (𝓝 1) := by
    have hint0 : Tendsto
        (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), f u * Complex.exp (-(σ : ℂ) * (u : ℂ)) ∂μ)
        atTop (𝓝 0) := by
      have hzero : (0 : ℂ) = ∫ _ in Ioi (0 : ℝ), (0 : ℂ) ∂μ := by simp
      rw [hzero]
      refine tendsto_integral_filter_of_dominated_convergence
        (fun u => ‖f u‖ * Real.exp (-σ₀ * u)) ?_ ?_ hf_int ?_
      · refine Eventually.of_forall fun σ => hf_meas.mul ?_
        exact (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
      · filter_upwards [eventually_ge_atTop σ₀] with σ hσ
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 ≤ u := le_of_lt hu
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(σ : ℂ) * (u : ℂ)).re = -σ * u := by simp
        rw [hre]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (norm_nonneg _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := hu
        have hexp : Tendsto (fun σ : ℝ => Complex.exp (-(σ : ℂ) * (u : ℂ))) atTop (𝓝 0) := by
          have h1 : Tendsto (fun σ : ℝ => ((Real.exp (-σ * u) : ℝ) : ℂ))
              atTop (𝓝 ((0 : ℝ) : ℂ)) := by
            refine (Complex.continuous_ofReal.tendsto 0).comp ?_
            refine Real.tendsto_exp_atBot.comp ?_
            have : Tendsto (fun σ : ℝ => σ * u) atTop atTop :=
              Tendsto.atTop_mul_const hu0 tendsto_id
            simpa only [neg_mul] using tendsto_neg_atTop_atBot.comp this
          refine (by simpa using h1 : Tendsto _ atTop (𝓝 0)).congr fun σ => ?_
          rw [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
        simpa using hexp.const_mul (f u)
    simpa [hGdef] using (Complex.continuous_exp.tendsto 0).comp hint0
  exact exists_monic_poly_of_completed_gauge (Real.exp_pos I₀).le hG_bound hG_lim hE hfin hε
    hsym hcomp

/-! ### 3. Whole-strip zero-multiplicity and off-critical quartet budgets -/

/-- For a nonzero polynomial `P : ℂ[X]`, the sum of root multiplicities over any finite subset of
`ℂ` is bounded by `P.natDegree`. -/
theorem sum_rootMultiplicity_le_natDegree {P : ℂ[X]} (hP : P ≠ 0) (S : Finset ℂ) :
    ∑ z ∈ S, P.rootMultiplicity z ≤ P.natDegree := by
  let M : Multiset ℂ := S.val.bind (fun z => Multiset.replicate (P.roots.count z) z)
  have hle : M ≤ P.roots := by
    rw [Multiset.le_iff_count]
    intro w
    have hcount : M.count w = ∑ z ∈ S, (Multiset.replicate (P.roots.count z) z).count w := by
      simp only [M, Finset.sum, Multiset.count_bind]
    rw [hcount]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w]
      · simp
      · intro z _ hzw
        rw [Multiset.count_replicate, if_neg (Ne.symm hzw)]
      · intro hnot
        exact absurd hw hnot
    · have h0 : ∑ z ∈ S, (Multiset.replicate (P.roots.count z) z).count w = 0 := by
        refine Finset.sum_eq_zero fun z hz => ?_
        have hzw : w ≠ z := fun h => hw (h ▸ hz)
        rw [Multiset.count_replicate, if_neg hzw]
      rw [h0]
      exact Nat.zero_le _
  have hcard : M.card = ∑ z ∈ S, P.rootMultiplicity z := by
    simp only [M, Finset.sum, Multiset.card_bind, Multiset.card_replicate]
    refine Multiset.map_congr rfl fun z _ => ?_
    exact Polynomial.count_roots P
  calc ∑ z ∈ S, P.rootMultiplicity z = M.card := hcard.symm
    _ ≤ P.roots.card := Multiset.card_le_card hle
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- **Global zero-multiplicity and off-critical quartet budget of a collapsed gauge.** Suppose
`E(s) = P.eval s` for a monic polynomial `P` of degree `2 κ`. Then:
1. Over any finite set `S ⊂ ℂ`, `∑_{z ∈ S} (analyticOrderAt E z).toNat ≤ 2 κ`.
2. When `E(s̄) = conj(E(s))` and `E(1 − s) = E(s)`, for any `q` upper-half-plane off-critical zeros
   `ρ₁, …, ρ_q` with pairwise distinct positive ordinates `Im ρ_ℓ > 0`, `Re ρ_ℓ ≠ 1/2`, and
   multiplicities `m_ℓ ≤ (analyticOrderAt E ρ_ℓ).toNat`, the total quartet multiplicity satisfies
   `2 * ∑_ℓ m_ℓ ≤ κ` (hence `∑_ℓ m_ℓ ≤ κ / 2`). -/
theorem completed_gauge_zero_and_quartet_budget {κ : ℕ} {E : ℂ → ℂ} {P : ℂ[X]}
    (hMonic : P.Monic) (hDeg : P.natDegree = 2 * κ) (hEP : ∀ s : ℂ, E s = P.eval s) :
    (∀ S : Finset ℂ, ∑ z ∈ S, (analyticOrderAt E z).toNat ≤ 2 * κ) ∧
    ((∀ s, E (starRingEnd ℂ s) = starRingEnd ℂ (E s)) →
      (∀ s, E (1 - s) = E s) →
      ∀ {q : ℕ} (ρ : Fin q → ℂ) (m : Fin q → ℕ),
        (∀ i, 0 < (ρ i).im) →
        (∀ i j, i ≠ j → (ρ i).im ≠ (ρ j).im) →
        (∀ i, (ρ i).re ≠ 1 / 2) →
        (∀ i, m i ≤ (analyticOrderAt E (ρ i)).toNat) →
        2 * ∑ i, m i ≤ κ) := by
  have hP0 : P ≠ 0 := hMonic.ne_zero
  have hord : ∀ z : ℂ, (analyticOrderAt E z).toNat = P.rootMultiplicity z := by
    intro z
    have hfn : E = fun y : ℂ => P.eval y := funext hEP
    rw [hfn, analyticOrderAt_eval_eq_rootMultiplicity hP0 z, ENat.toNat_coe]
  have hpart1 : ∀ S : Finset ℂ, ∑ z ∈ S, (analyticOrderAt E z).toNat ≤ 2 * κ := by
    intro S
    simp_rw [hord]
    exact (sum_rootMultiplicity_le_natDegree hP0 S).trans hDeg.le
  refine ⟨hpart1, fun hconj hsym q ρ m him hdist hre hm => ?_⟩
  classical
  have hEdiff : Differentiable ℂ E := by
    rw [show E = fun y => P.eval y from funext hEP]
    exact Polynomial.differentiable P
  have hEan : AnalyticOnNhd ℂ E univ := hEdiff.differentiableOn.analyticOnNhd isOpen_univ
  -- Symmetries preserve analytic order.
  have hord_reflect : ∀ z : ℂ, analyticOrderAt E (1 - z) = analyticOrderAt E z := by
    intro z
    have h := RHTower.CompletionZeroPairs.divisor_reflect hEan one_ne_zero
      (c := 1) (fun w => by rw [hsym w, one_mul]) z
    rw [GaloisForLFunctions.EntireZeroDivisor.divisor_univ_eq_analyticOrder hEan,
      GaloisForLFunctions.EntireZeroDivisor.divisor_univ_eq_analyticOrder hEan] at h
    rw [show E = fun y => P.eval y from funext hEP] at h ⊢
    rw [analyticOrderAt_eval_eq_rootMultiplicity hP0,
      analyticOrderAt_eval_eq_rootMultiplicity hP0] at h ⊢
    simp only [ENat.map_coe, Int.ofNat_eq_coe, WithTop.untop₀_coe, Nat.cast_inj] at h
    exact congrArg Nat.cast h
  have hord_conj : ∀ z : ℂ,
      (analyticOrderAt E (starRingEnd ℂ z)).toNat = (analyticOrderAt E z).toNat := by
    intro z
    obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt E z = n :=
      ⟨P.rootMultiplicity z, by
        rw [show E = fun y => P.eval y from funext hEP,
          analyticOrderAt_eval_eq_rootMultiplicity hP0]⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt E (starRingEnd ℂ z) = k :=
      ⟨P.rootMultiplicity (starRingEnd ℂ z), by
        rw [show E = fun y => P.eval y from funext hEP,
          analyticOrderAt_eval_eq_rootMultiplicity hP0]⟩
    have hle : ∀ w : ℂ, ∀ r : ℕ, analyticOrderAt E w = r →
        (r : ℕ∞) ≤ analyticOrderAt E (starRingEnd ℂ w) := by
      intro w r hr
      obtain ⟨g, hgan, _, hwg⟩ := (hEan w (mem_univ w)).analyticOrderAt_eq_natCast.mp hr
      refine (hEan _ (mem_univ _)).le_analyticOrderAt (g := fun y => starRingEnd ℂ (g (starRingEnd ℂ y))) ?_ ?_
      · have hgd : DifferentiableOn ℂ (fun y => starRingEnd ℂ (g (starRingEnd ℂ y)))
            {y | AnalyticAt ℂ g (starRingEnd ℂ y)} := by
          intro y hy
          have h := (hy.differentiableAt).conj_conj
          simpa [Function.comp_def] using h.differentiableWithinAt
        have hopen : IsOpen {y : ℂ | AnalyticAt ℂ g (starRingEnd ℂ y)} :=
          isOpen_analyticAt ℂ g |>.preimage Complex.continuous_conj
        exact hgd.analyticAt (hopen.mem_nhds (by simpa using hgan))
      · have hopen_nhds : ∀ᶠ y in 𝓝 (starRingEnd ℂ w),
            E (starRingEnd ℂ y) = (starRingEnd ℂ y - w) ^ r * g (starRingEnd ℂ y) :=
          Complex.continuous_conj.continuousAt.eventually hwg
        filter_upwards [hopen_nhds] with y hy
        have hc := congrArg (starRingEnd ℂ) hy
        rw [← hconj, Complex.conj_conj, map_mul, map_pow, map_sub] at hc
        exact hc
    have h1 := hle z n hn
    have h2 := hle (starRingEnd ℂ z) k hk
    rw [Complex.conj_conj, hn] at h2
    rw [hk] at h1
    have hnk : k = n := le_antisymm (ENat.coe_le_coe.mp h2) (ENat.coe_le_coe.mp h1)
    rw [hn, hk, hnk]
  -- Build the four-element orbit Finset for each `i : Fin q`.
  let orb : Fin q → Finset ℂ := fun i =>
    {ρ i, starRingEnd ℂ (ρ i), 1 - ρ i, 1 - starRingEnd ℂ (ρ i)}
  have horb_abs_im : ∀ i z, z ∈ orb i → |z.im| = (ρ i).im := by
    intro i z hz
    have hi : 0 < (ρ i).im := him i
    simp only [orb, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact abs_of_pos hi
    · simp [abs_of_pos hi]
    · simp [abs_of_pos hi]
    · simp [abs_of_pos hi]
  have horb_disj : Pairwise (fun i j => Disjoint (orb i) (orb j)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    exact hdist i j hij ((horb_abs_im i z hzi).symm.trans (horb_abs_im j z hzj))
  have horb_sum : ∀ i, 4 * m i ≤ ∑ z ∈ orb i, (analyticOrderAt E z).toNat := by
    intro i
    have hi : 0 < (ρ i).im := him i
    have hri : (ρ i).re ≠ 1 / 2 := hre i
    have hne12 : ρ i ≠ starRingEnd ℂ (ρ i) := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hne13 : ρ i ≠ 1 - ρ i := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hne14 : ρ i ≠ 1 - starRingEnd ℂ (ρ i) := fun h => by
      have := congrArg Complex.re h; simp at this; apply hri; linarith
    have hne23 : starRingEnd ℂ (ρ i) ≠ 1 - ρ i := fun h => by
      have := congrArg Complex.re h; simp at this; apply hri; linarith
    have hne24 : starRingEnd ℂ (ρ i) ≠ 1 - starRingEnd ℂ (ρ i) := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hne34 : 1 - ρ i ≠ 1 - starRingEnd ℂ (ρ i) := fun h =>
      hne12 (sub_left_inj.mp h)
    have hmem1 : ρ i ∉ ({starRingEnd ℂ (ρ i), 1 - ρ i, 1 - starRingEnd ℂ (ρ i)} : Finset ℂ) := by
      simp [hne12, hne13, hne14]
    have hmem2 : starRingEnd ℂ (ρ i) ∉ ({1 - ρ i, 1 - starRingEnd ℂ (ρ i)} : Finset ℂ) := by
      simp [hne23, hne24]
    have hmem3 : 1 - ρ i ∉ ({1 - starRingEnd ℂ (ρ i)} : Finset ℂ) := by
      simp [hne34]
    simp only [orb]
    rw [Finset.sum_insert hmem1, Finset.sum_insert hmem2, Finset.sum_insert hmem3,
      Finset.sum_singleton]
    have o2 : (analyticOrderAt E (starRingEnd ℂ (ρ i))).toNat = (analyticOrderAt E (ρ i)).toNat :=
      hord_conj (ρ i)
    have o3 : (analyticOrderAt E (1 - ρ i)).toNat = (analyticOrderAt E (ρ i)).toNat := by
      rw [hord_reflect]
    have o4 : (analyticOrderAt E (1 - starRingEnd ℂ (ρ i))).toNat =
        (analyticOrderAt E (ρ i)).toNat := by
      rw [hord_reflect, hord_conj]
    rw [o2, o3, o4]
    have hmi := hm i
    omega
  have hbiU := hpart1 (Finset.univ.biUnion orb)
  rw [Finset.sum_biUnion (fun i _ j _ hij => horb_disj hij)] at hbiU
  have h4 : 4 * ∑ i, m i ≤ ∑ i : Fin q, ∑ z ∈ orb i, (analyticOrderAt E z).toNat := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => horb_sum i
  omega

/-! ### 4. Simple-pole (`κ = 1`) critical-refund rigidity via Landau's real-axis theorem -/

private theorem ne_zero_of_entire_linear_ode {E W : ℂ → ℂ} {t₀ : ℝ}
    (hE : Differentiable ℂ E) (hE_nz : ∃ z₀, E z₀ ≠ 0)
    (hW : AnalyticAt ℂ W (t₀ : ℂ))
    (heq : ∀ᶠ t : ℝ in 𝓝[≠] t₀, deriv E (t : ℂ) = W (t : ℂ) * E (t : ℂ)) :
    E (t₀ : ℂ) ≠ 0 := by
  intro h0
  set z₀ : ℂ := (t₀ : ℂ) with hz₀
  have hEan : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z₁, hz₁⟩ := hE_nz
  have hntop : analyticOrderAt E z₀ ≠ ⊤ :=
    hEan.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₁) (mem_univ z₀)
      (by rw [(hEan z₁ (mem_univ z₁)).analyticOrderAt_eq_zero.mpr hz₁]; exact ENat.zero_ne_top)
  have hne0 : analyticOrderAt E z₀ ≠ 0 := fun hz =>
    ((hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_zero.mp hz) h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hntop
  have hm_pos : 1 ≤ m := by
    rcases eq_or_ne m 0 with rfl | hm0
    · exact absurd hm.symm hne0
    · omega
  obtain ⟨g, hgan, hg0, hEg⟩ := (hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_natCast.mp hm.symm
  -- Transfer `deriv E = W * E` from the punctured real ray to `𝓝 z₀`.
  have hdE_an : AnalyticAt ℂ (deriv E) z₀ := (hEan z₀ (mem_univ z₀)).deriv
  have hWE_an : AnalyticAt ℂ (fun z => W z * E z) z₀ := hW.mul (hEan z₀ (mem_univ z₀))
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] z₀, deriv E z = W z * E z := by
    have hnb : (𝓝[≠] t₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by simp)
    have htend := RHTower.tendsto_ofReal_nhdsNE t₀
    exact (heq.frequently).map htend
  have hEqC : deriv E =ᶠ[𝓝 z₀] fun z => W z * E z :=
    hdE_an.eventually_eq_of_frequently_eq hWE_an hfreq
  -- Compare vanishing orders of `deriv E` and `W * E` at `z₀`.
  have hderiv_g : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hgan.eventually_analyticAt
  have hd_local : ∀ᶠ z in 𝓝 z₀,
      deriv E z = (z - z₀) ^ (m - 1) * ((m : ℂ) * g z + (z - z₀) * deriv g z) := by
    obtain ⟨U, hU_sub, hU_open, hz₀U⟩ := eventually_iff_exists_mem.mp (hEg.and hderiv_g)
    filter_upwards [hU_open.mem_nhds hz₀U] with z hzU
    have hev : E =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * g w := by
      filter_upwards [hU_open.mem_nhds hzU] with w hwU
      exact (hU_sub hwU).1
    have hgz : DifferentiableAt ℂ g z := (hU_sub hzU).2.differentiableAt
    have hd1 : HasDerivAt (fun w : ℂ => (w - z₀) ^ m)
        ((m : ℂ) * (z - z₀) ^ (m - 1)) z := by
      simpa using ((hasDerivAt_id z).sub_const z₀).pow m
    have hd2 : HasDerivAt (fun w : ℂ => (w - z₀) ^ m * g w)
        ((m : ℂ) * (z - z₀) ^ (m - 1) * g z + (z - z₀) ^ m * deriv g z) z :=
      hd1.mul hgz.hasDerivAt
    rw [hev.deriv_eq, hd2.deriv]
    have hpow : (z - z₀) ^ m = (z - z₀) ^ (m - 1) * (z - z₀) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ]
    rw [hpow]
    ring
  have hcancel : ∀ᶠ z in 𝓝[≠] z₀,
      (m : ℂ) * g z + (z - z₀) * deriv g z = (z - z₀) * W z * g z := by
    filter_upwards [nhdsWithin_le_nhds (hEqC.and (hd_local.and hEg)),
      self_mem_nhdsWithin] with z ⟨h1, h2, h3⟩ hz
    have hsub0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hpow : (z - z₀) ^ m = (z - z₀) ^ (m - 1) * (z - z₀) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm_pos, pow_succ]
    rw [h2, h3, hpow] at h1
    have h1' : (z - z₀) ^ (m - 1) * ((m : ℂ) * g z + (z - z₀) * deriv g z) =
        (z - z₀) ^ (m - 1) * ((z - z₀) * W z * g z) := by linear_combination h1
    exact mul_left_cancel₀ (pow_ne_zero _ hsub0) h1'
  have hlhs : Tendsto (fun z => (m : ℂ) * g z + (z - z₀) * deriv g z)
      (𝓝[≠] z₀) (𝓝 ((m : ℂ) * g z₀)) := by
    have hc : ContinuousAt (fun z => (m : ℂ) * g z + (z - z₀) * deriv g z) z₀ :=
      (continuousAt_const.mul hgan.continuousAt).add
        ((continuousAt_id.sub continuousAt_const).mul hgan.deriv.continuousAt)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hrhs : Tendsto (fun z => (z - z₀) * W z * g z) (𝓝[≠] z₀) (𝓝 0) := by
    have hc : ContinuousAt (fun z => (z - z₀) * W z * g z) z₀ :=
      ((continuousAt_id.sub continuousAt_const).mul hW.continuousAt).mul hgan.continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hnb : (𝓝[≠] z₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  have hm0 := tendsto_nhds_unique (hlhs.congr' hcancel) hrhs
  have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero hm_ne hg0 hm0

private theorem ne_zero_at_endpoint_of_nonneg_logDeriv_diff {E : ℂ → ℂ} {c : ℝ}
    (hE : Differentiable ℂ E) (hE_nz : ∃ z₀, E z₀ ≠ 0)
    (hnonneg : ∀ᶠ t : ℝ in 𝓝[>] c,
      0 ≤ (-logDeriv E (t : ℂ) + logDeriv RHTower.xi (t : ℂ)).re) :
    E (c : ℂ) ≠ 0 := by
  intro h0
  set z₀ : ℂ := (c : ℂ) with hz₀
  have hEan : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z₁, hz₁⟩ := hE_nz
  have hntop : analyticOrderAt E z₀ ≠ ⊤ :=
    hEan.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ z₁) (mem_univ z₀)
      (by rw [(hEan z₁ (mem_univ z₁)).analyticOrderAt_eq_zero.mpr hz₁]; exact ENat.zero_ne_top)
  have hne0 : analyticOrderAt E z₀ ≠ 0 := fun hz =>
    ((hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_zero.mp hz) h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hntop
  have hm_pos : 1 ≤ m := by
    rcases eq_or_ne m 0 with rfl | hm0
    · exact absurd hm.symm hne0
    · omega
  obtain ⟨g, hgan, hg0, hEg⟩ := (hEan z₀ (mem_univ z₀)).analyticOrderAt_eq_natCast.mp hm.symm
  have hlog : ∀ᶠ z in 𝓝[≠] z₀,
      logDeriv E z = (m : ℂ) / (z - z₀) + logDeriv g z := by
    have hgnz : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hgan.continuousAt.eventually_ne hg0
    have hgan' : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hgan.eventually_analyticAt
    obtain ⟨U, hU_sub, hU_open, hz₀U⟩ := eventually_iff_exists_mem.mp (hEg.and (hgnz.and hgan'))
    filter_upwards [nhdsWithin_le_nhds (hU_open.mem_nhds hz₀U), self_mem_nhdsWithin] with z hzU hz
    have hev : E =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * g w := by
      filter_upwards [hU_open.mem_nhds hzU] with w hwU
      exact (hU_sub hwU).1
    have hsub0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hgz0 : g z ≠ 0 := (hU_sub hzU).2.1
    have hgd : DifferentiableAt ℂ g z := (hU_sub hzU).2.2.differentiableAt
    have hpd : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ m) z :=
      ((differentiableAt_id.sub_const z₀).pow m)
    have hle1 : logDeriv E z = logDeriv (fun w => (w - z₀) ^ m * g w) z := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    rw [hle1, logDeriv_mul z (pow_ne_zero _ hsub0) hgz0 hpd hgd,
      logDeriv_fun_pow (differentiableAt_id.sub_const z₀) m]
    congr 1
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div, div_eq_mul_inv]
  have hxian : AnalyticAt ℂ (logDeriv RHTower.xi) z₀ := by
    have hd := (RHTower.xi_analyticOnNhd_univ z₀ (mem_univ z₀)).deriv
    exact hd.div (RHTower.xi_analyticOnNhd_univ z₀ (mem_univ z₀))
      (RHTower.xi_ne_zero_of_ofReal c)
  have hgan_ld : AnalyticAt ℂ (logDeriv g) z₀ := hgan.deriv.div hgan hg0
  -- Along `t ↓ c⁺`, `(t - c) * Re (-logDeriv E t + logDeriv xi t) → -m`.
  have ht_ne : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] c) (𝓝[≠] z₀) := by
    refine (RHTower.tendsto_ofReal_nhdsNE c).mono_left ?_
    exact nhdsWithin_mono c fun t (ht : c < t) => ne_of_gt ht
  have hlim : Tendsto
      (fun t : ℝ => (t - c) * (-logDeriv E (t : ℂ) + logDeriv RHTower.xi (t : ℂ)).re)
      (𝓝[>] c) (𝓝 (-(m : ℝ))) := by
    have hrem_cont : ContinuousAt
        (fun t : ℝ => (-logDeriv g (t : ℂ) + logDeriv RHTower.xi (t : ℂ)).re) c :=
      Complex.continuous_re.continuousAt.comp
        (((hgan_ld.neg.add hxian).continuousAt).comp Complex.continuous_ofReal.continuousAt)
    have hsub0 : Tendsto (fun t : ℝ => t - c) (𝓝[>] c) (𝓝 0) := by
      simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).sub_const c
    have hprod : Tendsto
        (fun t : ℝ => -(m : ℝ) +
          (t - c) * (-logDeriv g (t : ℂ) + logDeriv RHTower.xi (t : ℂ)).re)
        (𝓝[>] c) (𝓝 (-(m : ℝ) + 0 * (-logDeriv g z₀ + logDeriv RHTower.xi z₀).re)) :=
      tendsto_const_nhds.add (hsub0.mul (hrem_cont.tendsto.mono_left nhdsWithin_le_nhds))
    simp only [zero_mul, add_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [ht_ne.eventually hlog, self_mem_nhdsWithin] with t ht htc
    change c < t at htc
    have htc0 : t - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt htc)
    have hcast : ((m : ℂ) / ((t : ℂ) - z₀)).re = (m : ℝ) / (t - c) := by
      have he : (t : ℂ) - z₀ = ((t - c : ℝ) : ℂ) := by rw [hz₀]; push_cast; ring
      have hd : (m : ℂ) / (((t - c : ℝ) : ℂ)) = (((m : ℝ) / (t - c) : ℝ) : ℂ) := by push_cast; rfl
      rw [he, hd, Complex.ofReal_re]
    rw [ht]
    have hre : (-((m : ℂ) / ((t : ℂ) - z₀) + logDeriv g (t : ℂ)) + logDeriv RHTower.xi (t : ℂ)).re =
        -((m : ℝ) / (t - c)) + (-logDeriv g (t : ℂ) + logDeriv RHTower.xi (t : ℂ)).re := by
      rw [neg_add, add_assoc, Complex.add_re, Complex.neg_re, hcast]
    rw [hre, mul_add]
    congr 1
    field_simp [htc0]
  have hge0 : ∀ᶠ t : ℝ in 𝓝[>] c,
      0 ≤ (t - c) * (-logDeriv E (t : ℂ) + logDeriv RHTower.xi (t : ℂ)).re := by
    filter_upwards [hnonneg, self_mem_nhdsWithin] with t ht htc
    change c < t at htc
    exact mul_nonneg (by linarith) ht
  have hnb : (𝓝[>] c).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hle0 : (0 : ℝ) ≤ -(m : ℝ) := ge_of_tendsto hlim hge0
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
  linarith

private theorem isAbscissa_add_volume_zero {ν : Measure ℝ}
    (hfin : ∀ σ : ℝ, laplaceMass ν σ ≠ ⊤) :
    IsAbscissa (ν + volume) 0 := by
  have hmass : ∀ σ : ℝ, laplaceMass (ν + volume) σ = laplaceMass ν σ + laplaceMass volume σ := by
    intro σ
    unfold laplaceMass
    rw [Measure.restrict_add, lintegral_add_measure]
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · rw [hmass σ]
    exact ENNReal.add_ne_top.mpr ⟨hfin σ, isAbscissa_volume_zero.1 σ hσ⟩
  · rw [hmass σ, isAbscissa_volume_zero.2 σ hσ, add_top]

/-- **Simple-pole (`κ = 1`) critical-refund rigidity law.** Let `ν` be any nonnegative Borel
measure on `ℝ` with `laplaceMass ν σ₁ ≠ ⊤`, and let `E : ℂ → ℂ` be a nonzero entire function
satisfying `E(1 − s) = ε E(s)` (`ε ≠ 0`) such that on `σ > σ₁`, `E(σ) ≠ 0` and
`−logDeriv E(σ) + logDeriv ξ(σ) = laplaceReal ν σ` (so `E / (2 ξ)` may cancel any subset of
nonreal or critical zeros of `ξ`, without any finite-order assumption on `E`). Then
`ν.restrict (Ioi 0) = 0`, `ε = 1`, and `E(s) = (E(1) / ξ(1)) ξ(s)` for all `s ∈ ℂ`. -/
theorem simple_pole_nonneg_laplace_refund_rigidity {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv₁ : laplaceMass ν σ₁ ≠ ⊤)
    {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hE_nz : ∃ z₀, E z₀ ≠ 0)
    {ε : ℂ} (hε : ε ≠ 0) (hsym : ∀ s, E (1 - s) = ε * E s)
    (hE_ray : ∀ σ : ℝ, σ₁ < σ → E (σ : ℂ) ≠ 0)
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv E (σ : ℂ) + logDeriv RHTower.xi (σ : ℂ) = ((laplaceReal ν σ : ℝ) : ℂ)) :
    ν.restrict (Ioi (0 : ℝ)) = 0 ∧ ε = 1 ∧
      ∀ s : ℂ, E s = (E 1 / RHTower.xi 1) * RHTower.xi s := by
  have hEan : AnalyticOnNhd ℂ E univ := hE.differentiableOn.analyticOnNhd isOpen_univ
  -- Reusable propagation along any open ray `(c, ∞)` on which `complexLaplace ν` is holomorphic.
  have hpropagate : ∀ c : ℝ,
      DifferentiableOn ℂ (complexLaplace ν) {z : ℂ | c < z.re} →
      ∀ t : ℝ, c < t →
        E (t : ℂ) ≠ 0 ∧
          -logDeriv E (t : ℂ) + logDeriv RHTower.xi (t : ℂ) = ((laplaceReal ν t : ℝ) : ℂ) := by
    intro c hCLdiff
    set W : ℂ → ℂ := fun z => logDeriv RHTower.xi z - complexLaplace ν z with hWdef
    have hWan : ∀ t : ℝ, c < t → AnalyticAt ℂ W (t : ℂ) := by
      intro t ht
      have hopen : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hCL : AnalyticAt ℂ (complexLaplace ν) (t : ℂ) :=
        hCLdiff.analyticAt (hopen.mem_nhds (by simpa using ht))
      have hxi : AnalyticAt ℂ (logDeriv RHTower.xi) (t : ℂ) :=
        (RHTower.xi_analyticOnNhd_univ (t : ℂ) (mem_univ _)).deriv.div
          (RHTower.xi_analyticOnNhd_univ (t : ℂ) (mem_univ _))
          (RHTower.xi_ne_zero_of_ofReal t)
      exact hxi.sub hCL
    -- Real-analyticity of `deriv E - W * E` on `Ioi c`.
    have hode_all : ∀ t : ℝ, c < t → deriv E (t : ℂ) = W (t : ℂ) * E (t : ℂ) := by
      have h1 : AnalyticOnNhd ℝ (fun t : ℝ => deriv E (t : ℂ)) (Ioi c) :=
        fun t ht => RHTower.analyticAt_ofReal_comp (hEan (t : ℂ) (mem_univ _)).deriv
      have h2 : AnalyticOnNhd ℝ (fun t : ℝ => W (t : ℂ) * E (t : ℂ)) (Ioi c) :=
        fun t ht => RHTower.analyticAt_ofReal_comp ((hWan t ht).mul (hEan (t : ℂ) (mem_univ _)))
      set t₁ : ℝ := max c σ₁ + 1 with ht₁def
      have ht₁c : c < t₁ := by rw [ht₁def]; linarith [le_max_left c σ₁]
      have ht₁s : σ₁ < t₁ := by rw [ht₁def]; linarith [le_max_right c σ₁]
      have hev : (fun t : ℝ => deriv E (t : ℂ)) =ᶠ[𝓝 t₁]
          fun t : ℝ => W (t : ℂ) * E (t : ℂ) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht₁s] with t ht
        change σ₁ < t at ht
        have hEt0 : E (t : ℂ) ≠ 0 := hE_ray t ht
        have hag := hagree t ht
        rw [← complexLaplace_ofReal] at hag
        have hld : logDeriv E (t : ℂ) = W (t : ℂ) := by
          rw [hWdef]; linear_combination -hag
        rw [logDeriv_apply] at hld
        exact (div_eq_iff hEt0).mp hld
      exact fun t ht => h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_Ioi ht₁c hev ht
    intro t ht
    have hEt0 : E (t : ℂ) ≠ 0 := by
      refine ne_zero_of_entire_linear_ode hE hE_nz (hWan t ht) ?_
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ht)] with y hy
      exact hode_all y hy
    refine ⟨hEt0, ?_⟩
    have hode := hode_all t ht
    have hld : logDeriv E (t : ℂ) = W (t : ℂ) := by
      rw [logDeriv_apply, div_eq_iff hEt0]
      exact hode
    rw [hld, hWdef, complexLaplace_ofReal]
    ring
  -- Step A: `laplaceMass ν σ ≠ ⊤` for every real `σ`.
  have hfin_all : ∀ σ : ℝ, laplaceMass ν σ ≠ ⊤ := by
    intro σ₀
    by_contra htop
    obtain ⟨c, hc⟩ := exists_isAbscissa ⟨σ₁, hconv₁⟩ ⟨σ₀, htop⟩
    have hray := hpropagate c (differentiableOn_complexLaplace hc)
    have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] c,
        0 ≤ (-logDeriv E (t : ℂ) + logDeriv RHTower.xi (t : ℂ)).re := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change c < t at ht
      rw [(hray t ht).2, Complex.ofReal_re]
      exact integral_nonneg fun u => (Real.exp_pos _).le
    have hEc : E (c : ℂ) ≠ 0 := ne_zero_at_endpoint_of_nonneg_logDeriv_diff hE hE_nz hnonneg
    set Φ : ℂ → ℂ := fun z => -logDeriv E z + logDeriv RHTower.xi z with hΦdef
    have hΦan : AnalyticAt ℂ Φ (c : ℂ) := by
      have h1 : AnalyticAt ℂ (logDeriv E) (c : ℂ) :=
        (hEan (c : ℂ) (mem_univ _)).deriv.div (hEan (c : ℂ) (mem_univ _)) hEc
      have h2 : AnalyticAt ℂ (logDeriv RHTower.xi) (c : ℂ) :=
        (RHTower.xi_analyticOnNhd_univ (c : ℂ) (mem_univ _)).deriv.div
          (RHTower.xi_analyticOnNhd_univ (c : ℂ) (mem_univ _))
          (RHTower.xi_ne_zero_of_ofReal c)
      exact h1.neg.add h2
    obtain ⟨δ, hδ, hball⟩ := hΦan.exists_ball_analyticOnNhd
    exact false_of_analyticAt_abscissa hc hδ hball (fun σ hσ _ => (hray σ hσ).2)
  -- Step B: Holomorphy of `complexLaplace ν` on `Re z > 0` via `ν + volume`.
  have hc_sum : IsAbscissa (ν + volume) 0 := isAbscissa_add_volume_zero hfin_all
  have hCL_pos : DifferentiableOn ℂ (complexLaplace ν) {z : ℂ | 0 < z.re} := by
    have hdiff_sum := differentiableOn_complexLaplace hc_sum
    have hdiff_vol := differentiableOn_complexLaplace isAbscissa_volume_zero
    refine (hdiff_sum.sub hdiff_vol).congr fun z hz => ?_
    change 0 < z.re at hz
    have hi_sum := integrable_cexp_of_gt_abscissa hc_sum hz
    rw [Measure.restrict_add] at hi_sum
    have hi_nu : Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ)))
        (ν.restrict (Ioi (0 : ℝ))) := hi_sum.left_of_add_measure
    have hi_vol := integrable_cexp_of_gt_abscissa isAbscissa_volume_zero hz
    unfold complexLaplace
    rw [Measure.restrict_add, integral_add_measure hi_nu hi_vol]
    ring
  have hray0 := hpropagate 0 hCL_pos
  -- Evaluate reflection antisymmetry at `t = 3/4` and `1 - t = 1/4`.
  have hlogE_odd := RHTower.CompletionZeroPairs.logDeriv_one_sub hE hε hsym
  have hlogXi_odd := RHTower.CompletionZeroPairs.logDeriv_one_sub RHTower.xi_differentiable
    one_ne_zero (fun s => by rw [RHTower.xi_one_sub, one_mul])
  have h34 := (hray0 (3 / 4) (by norm_num)).2
  have h14 := (hray0 (1 / 4) (by norm_num)).2
  have hrefl_sum : laplaceReal ν (3 / 4) + laplaceReal ν (1 / 4) = 0 := by
    have hc_eq : (((laplaceReal ν (3 / 4) + laplaceReal ν (1 / 4) : ℝ) : ℂ)) = 0 := by
      push_cast
      rw [← h34, ← h14]
      have hsub : ((1 / 4 : ℝ) : ℂ) = 1 - ((3 / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub, hlogE_odd, hlogXi_odd]
      ring
    exact Complex.ofReal_eq_zero.mp hc_eq
  have hl34_nn : 0 ≤ laplaceReal ν (3 / 4) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hl14_nn : 0 ≤ laplaceReal ν (1 / 4) := integral_nonneg fun _ => (Real.exp_pos _).le
  have hl14_zero : laplaceReal ν (1 / 4) = 0 := by linarith
  -- Force `ν.restrict (Ioi 0) = 0` from vanishing of `∫_{(0,∞)} e^{-u/4} dν`.
  have hnu_zero : ν.restrict (Ioi (0 : ℝ)) = 0 := by
    have hint14 : Integrable (fun u : ℝ => Real.exp (-(1 / 4 : ℝ) * u))
        (ν.restrict (Ioi (0 : ℝ))) := by
      have hi_sum := integrableOn_exp_neg_of_gt_abscissa hc_sum (σ := 1 / 4) (by norm_num)
      rw [IntegrableOn, Measure.restrict_add] at hi_sum
      exact hi_sum.left_of_add_measure
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun u => (Real.exp_pos _).le) hint14).mp hl14_zero
    have hnull : (ν.restrict (Ioi (0 : ℝ))) univ = 0 := by
      rw [← ae_iff]
      filter_upwards [hae] with u hu
      exact absurd hu (Real.exp_pos _).ne'
    exact Measure.measure_univ_eq_zero.mp hnull
  -- Deduce `E(s) = (E(1) / ξ(1)) ξ(s)` on all of `ℂ` and `ε = 1`.
  have hExi : ∀ s : ℂ, E s = (E 1 / RHTower.xi 1) * RHTower.xi s := by
    have hxi1 : RHTower.xi 1 ≠ 0 := by rw [RHTower.xi_one]; norm_num
    -- On `Ioi 0`, `logDeriv E = logDeriv xi`, so `deriv (E / xi) = 0` near `1`, hence `E = c₀ xi`.
    set q : ℂ → ℂ := fun z => E z / RHTower.xi z with hqdef
    have hq_const : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), q (t : ℂ) = q 1 := by
      have hopen : IsOpen {z : ℂ | RHTower.xi z ≠ 0} :=
        isOpen_compl_singleton.preimage RHTower.xi_differentiable.continuous
      obtain ⟨r, hr0, hr_sub⟩ := Metric.isOpen_iff.mp hopen 1 hxi1
      -- On `(max 0 (1 - r/2), 1 + r/2)`, the real derivative of `t ↦ q (t : ℂ)` vanishes.
      set δ : ℝ := min (1 / 2) (r / 2) with hδdef
      have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
      have hderiv0 : ∀ t ∈ Ioo (1 - δ) (1 + δ), HasDerivAt (fun y : ℝ => q (y : ℂ)) 0 t := by
        intro t ht
        have ht_pos : 0 < t := by
          have : δ ≤ 1 / 2 := min_le_left _ _
          linarith [ht.1]
        have hxit : RHTower.xi (t : ℂ) ≠ 0 := RHTower.xi_ne_zero_of_ofReal t
        have hEt : E (t : ℂ) ≠ 0 := (hray0 t ht_pos).1
        have hld_eq : logDeriv E (t : ℂ) = logDeriv RHTower.xi (t : ℂ) := by
          have h := (hray0 t ht_pos).2
          unfold laplaceReal at h
          rw [hnu_zero, integral_zero_measure, Complex.ofReal_zero] at h
          linear_combination -h
        have hnum : deriv E (t : ℂ) * RHTower.xi (t : ℂ) -
            E (t : ℂ) * deriv RHTower.xi (t : ℂ) = 0 := by
          rw [logDeriv_apply, logDeriv_apply, div_eq_div_iff hEt hxit] at hld_eq
          exact sub_eq_zero.mpr hld_eq
        have hdC : HasDerivAt q 0 (t : ℂ) := by
          have hdq := (hE (t : ℂ)).hasDerivAt.div
            (RHTower.xi_differentiable (t : ℂ)).hasDerivAt hxit
          rw [hnum, zero_div] at hdq
          exact hdq
        simpa using hdC.comp_ofReal
      filter_upwards [Ioo_mem_nhds (by linarith : 1 - δ < 1) (by linarith : 1 < 1 + δ)] with t ht
      have hconv : Convex ℝ (Ioo (1 - δ) (1 + δ)) := convex_Ioo _ _
      have hdOn : DifferentiableOn ℝ (fun y : ℝ => q (y : ℂ)) (Ioo (1 - δ) (1 + δ)) :=
        fun y hy => (hderiv0 y hy).differentiableAt.differentiableWithinAt
      exact hconv.is_const_of_fderivWithin_eq_zero hdOn
        (fun y hy => by
          rw [fderivWithin_eq_fderiv (isOpen_Ioo.uniqueDiffWithinAt hy),
            (hderiv0 y hy).hasFDerivAt.fderiv]
          ext; simp)
        ht ⟨by linarith, by linarith⟩
    have hE_eq_ray : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ),
        E (t : ℂ) = (E 1 / RHTower.xi 1) * RHTower.xi (t : ℂ) := by
      filter_upwards [hq_const] with t ht
      have hxit : RHTower.xi (t : ℂ) ≠ 0 := RHTower.xi_ne_zero_of_ofReal t
      have ht' : E (t : ℂ) / RHTower.xi (t : ℂ) = E 1 / RHTower.xi 1 := by
        simpa [hqdef] using ht
      exact (div_eq_iff hxit).mp ht'
    have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (1 : ℂ),
        E z = (E 1 / RHTower.xi 1) * RHTower.xi z := by
      have hnb : (𝓝[≠] (1 : ℝ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by simp)
      have hev' : ∀ᶠ t : ℝ in 𝓝[≠] (1 : ℝ),
          E (t : ℂ) = (E 1 / RHTower.xi 1) * RHTower.xi (t : ℂ) :=
        nhdsWithin_le_nhds hE_eq_ray
      exact hev'.frequently.map (RHTower.tendsto_ofReal_nhdsNE 1)
    have hRHS_an : AnalyticOnNhd ℂ (fun z => (E 1 / RHTower.xi 1) * RHTower.xi z) univ :=
      fun z _ => analyticAt_const.mul (RHTower.xi_analyticOnNhd_univ z (mem_univ z))
    have hloc := (hEan 1 (mem_univ 1)).eventually_eq_of_frequently_eq (hRHS_an 1 (mem_univ 1)) hfreq
    exact fun s => hEan.eqOn_of_preconnected_of_eventuallyEq hRHS_an isPreconnected_univ
      (mem_univ 1) hloc (mem_univ s)
  have hε1 : ε = 1 := by
    obtain ⟨z₀, hz₀⟩ := hE_nz
    have h1 := hsym z₀
    rw [hExi (1 - z₀), hExi z₀, RHTower.xi_one_sub] at h1
    have h2 : ε * E z₀ = 1 * E z₀ := by rw [← hExi z₀] at h1; exact h1.symm
    exact mul_right_cancel₀ hz₀ h2
  exact ⟨hnu_zero, hε1, hExi⟩

end GaloisForLFunctions.StripBochnerWeilForcing
