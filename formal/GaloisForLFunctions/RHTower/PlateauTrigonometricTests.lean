import GaloisForLFunctions.RHTower.BoxConvolutionPlateau
import GaloisForLFunctions.RHTower.ZetaZeroCountUpperBound

/-!
# Plateau trigonometric tests

For a plateau `b` (equal to `1` on `[-ℓ, ℓ]`) and the frequencies `τ_j = (j - k₀)π/ℓ`,
`0 ≤ j ≤ 2k₀`, the tests `f_c(u) = b(u) Σ_j c_j e^{iτ_j u}` satisfy

* `f̂_c(z) = Σ_j c_j b̂(z + τ_j)` (`paperFT_trigTest`);
* `∫ |f_c|² ≥ 2ℓ Σ_j |c_j|²`, by orthogonality of the `e^{iτ_j u}` on `[-ℓ, ℓ]`
  (`two_mul_sum_le_integral_trigTest`); in particular `c ↦ f_c` is injective.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## Orthogonality on `[-ℓ, ℓ]` -/

theorem integral_Icc_cexp_int_mul {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℤ) :
    ∫ u in Icc (-ℓ) ℓ, Complex.exp (I * ((k * π / ℓ : ℝ) : ℂ) * u) =
      if k = 0 then ((2 * ℓ : ℝ) : ℂ) else 0 := by
  split_ifs with hk
  · subst hk
    simp only [Int.cast_zero, zero_mul, zero_div, Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero]
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), Complex.real_smul,
      mul_one]
    push_cast; ring
  · have hc : I * ((k * π / ℓ : ℝ) : ℂ) ≠ 0 := by
      refine mul_ne_zero I_ne_zero ?_
      exact_mod_cast div_ne_zero (mul_ne_zero (by exact_mod_cast hk) Real.pi_ne_zero) hℓ.ne'
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      integral_exp_mul_complex hc]
    have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
    have e1 : I * ((k * π / ℓ : ℝ) : ℂ) * (ℓ : ℂ) = (k : ℂ) * (π * I) := by
      push_cast; field_simp
    have e2 : I * ((k * π / ℓ : ℝ) : ℂ) * ((-ℓ : ℝ) : ℂ) = -((k : ℂ) * (π * I)) := by
      push_cast; field_simp
    rw [e1, e2]
    have h2 : Complex.exp ((k : ℂ) * (π * I)) = Complex.exp (-((k : ℂ) * (π * I))) := by
      have := Complex.exp_int_mul_two_pi_mul_I k
      rw [show (k : ℂ) * (2 * ↑π * I) = (k : ℂ) * (π * I) - (-((k : ℂ) * (π * I))) by ring,
        Complex.exp_sub, div_eq_one_iff_eq (Complex.exp_ne_zero _)] at this
      exact this
    rw [h2, sub_self, zero_div]

/-! ## Trigonometric polynomials on the plateau -/

/-- The frequencies `τ_j = (j - k₀)π/ℓ`, `j ≤ 2k₀`. -/
def trigFreq (ℓ : ℝ) (k₀ : ℕ) (j : Fin (2 * k₀ + 1)) : ℝ := ((j : ℝ) - k₀) * π / ℓ

theorem trigFreq_sub (ℓ : ℝ) (k₀ : ℕ) (j m : Fin (2 * k₀ + 1)) :
    trigFreq ℓ k₀ j - trigFreq ℓ k₀ m = ((((j : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) : ℝ) * π / ℓ := by
  unfold trigFreq; push_cast; ring

theorem abs_trigFreq_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k₀ : ℕ) (j : Fin (2 * k₀ + 1)) :
    |trigFreq ℓ k₀ j| ≤ k₀ * π / ℓ := by
  unfold trigFreq
  have hj : (j : ℝ) ≤ 2 * k₀ := by
    have := j.isLt; exact_mod_cast (by omega : (j : ℕ) ≤ 2 * k₀)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hℓ]
  apply div_le_div_of_nonneg_right _ hℓ.le
  apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
  rw [abs_le]; constructor <;> linarith

/-- `p_c(u) = Σ_j c_j e^{iτ_j u}`. -/
def bandTrigPoly (ℓ : ℝ) (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) (u : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (I * (trigFreq ℓ k₀ j : ℂ) * u)

theorem continuous_bandTrigPoly (ℓ : ℝ) (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) :
    Continuous (bandTrigPoly ℓ k₀ c) := by
  unfold bandTrigPoly; fun_prop

theorem contDiff_bandTrigPoly (ℓ : ℝ) (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) {n : ℕ∞} :
    ContDiff ℝ n (bandTrigPoly ℓ k₀ c) := by
  unfold bandTrigPoly
  refine ContDiff.sum fun j _ => contDiff_const.mul ?_
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- **Parseval on the plateau.** `∫_{-ℓ}^{ℓ} |p_c|² = 2ℓ Σ |c_j|²`. -/
theorem integral_Icc_norm_bandTrigPoly_sq {ℓ : ℝ} (hℓ : 0 < ℓ) (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) :
    ∫ u in Icc (-ℓ) ℓ, ‖bandTrigPoly ℓ k₀ c u‖ ^ 2 = 2 * ℓ * ∑ j, ‖c j‖ ^ 2 := by
  have hexp : ∀ u : ℝ, bandTrigPoly ℓ k₀ c u * (starRingEnd ℂ) (bandTrigPoly ℓ k₀ c u) =
      ∑ j, ∑ m, c j * (starRingEnd ℂ) (c m) *
        Complex.exp (I * (((trigFreq ℓ k₀ j - trigFreq ℓ k₀ m : ℝ)) : ℂ) * u) := by
    intro u
    unfold bandTrigPoly
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    have e : (starRingEnd ℂ) (I * (trigFreq ℓ k₀ m : ℂ) * (u : ℂ)) =
        -(I * (trigFreq ℓ k₀ m : ℂ) * (u : ℂ)) := by
      simp [Complex.conj_ofReal]
    rw [e]
    have e2 : Complex.exp (I * (trigFreq ℓ k₀ j : ℂ) * u) *
        Complex.exp (-(I * (trigFreq ℓ k₀ m : ℂ) * (u : ℂ))) =
        Complex.exp (I * (((trigFreq ℓ k₀ j - trigFreq ℓ k₀ m : ℝ)) : ℂ) * u) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← e2]; ring
  have hint : ∀ (j m : Fin (2 * k₀ + 1)), IntegrableOn (fun u : ℝ => c j * (starRingEnd ℂ) (c m) *
      Complex.exp (I * (((trigFreq ℓ k₀ j - trigFreq ℓ k₀ m : ℝ)) : ℂ) * u)) (Icc (-ℓ) ℓ) :=
    fun j m => (by fun_prop : Continuous fun u : ℝ => c j * (starRingEnd ℂ) (c m) *
      Complex.exp (I * (((trigFreq ℓ k₀ j - trigFreq ℓ k₀ m : ℝ)) : ℂ) * u)).integrableOn_Icc
  have hC : ∫ u in Icc (-ℓ) ℓ, bandTrigPoly ℓ k₀ c u * (starRingEnd ℂ) (bandTrigPoly ℓ k₀ c u) =
      ((2 * ℓ * ∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun m _ => hint j m]
    rw [Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun m _ => hint j m]
    simp_rw [integral_const_mul, trigFreq_sub]
    have hI : ∀ j m : Fin (2 * k₀ + 1),
        ∫ u in Icc (-ℓ) ℓ, Complex.exp (I * ((((((j : ℕ) : ℤ) - ((m : ℕ) : ℤ) : ℤ) : ℝ) * π / ℓ :
          ℝ) : ℂ) * u) = if m = j then ((2 * ℓ : ℝ) : ℂ) else 0 := by
      intro j m
      rw [integral_Icc_cexp_int_mul hℓ]
      by_cases hmj : m = j
      · rw [if_pos hmj, if_pos (by rw [hmj]; simp)]
      · rw [if_neg hmj, if_neg (fun h => hmj (Fin.ext (by omega)))]
    simp only [hI, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hR : ∀ u : ℝ, ((‖bandTrigPoly ℓ k₀ c u‖ ^ 2 : ℝ) : ℂ) =
      bandTrigPoly ℓ k₀ c u * (starRingEnd ℂ) (bandTrigPoly ℓ k₀ c u) := by
    intro u; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h := hC
  simp_rw [← hR] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-! ## The tests `f_c = b · p_c` -/

/-- `f_c(u) = b(u) Σ_j c_j e^{iτ_j u}`. -/
def trigTest (b : ℝ → ℂ) (ℓ : ℝ) (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) : ℝ → ℂ :=
  fun u => b u * bandTrigPoly ℓ k₀ c u

theorem paperFT_trigTest {b : ℝ → ℂ} {U : ℝ} (hb : Integrable b) (hbs : ∀ u, U < |u| → b u = 0)
    (ℓ : ℝ) (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) (z : ℂ) :
    paperFT (trigTest b ℓ k₀ c) z = ∑ j, c j * paperFT b (z + trigFreq ℓ k₀ j) := by
  unfold paperFT trigTest bandTrigPoly
  have e : ∀ u : ℝ, b u * (∑ j, c j * Complex.exp (I * (trigFreq ℓ k₀ j : ℂ) * u)) *
      Complex.exp (I * z * u) =
      ∑ j, c j * (b u * Complex.exp (I * (z + trigFreq ℓ k₀ j) * u)) := by
    intro u
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Complex.exp (I * (trigFreq ℓ k₀ j : ℂ) * u) * Complex.exp (I * z * u) =
        Complex.exp (I * (z + trigFreq ℓ k₀ j) * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← this]; ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ =>
    (integrable_mul_cexp_of_support hb hbs (z + trigFreq ℓ k₀ j)).const_mul (c j)]
  simp_rw [integral_const_mul]

theorem contDiff_trigTest {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) (ℓ : ℝ) (k₀ : ℕ)
    (c : Fin (2 * k₀ + 1) → ℂ) : ContDiff ℝ 2 (trigTest b ℓ k₀ c) :=
  hb.mul (contDiff_bandTrigPoly ℓ k₀ c)

theorem tsupport_trigTest {b : ℝ → ℂ} {U : ℝ} (hbs : ∀ u, U ≤ |u| → b u = 0) (ℓ : ℝ) (k₀ : ℕ)
    (c : Fin (2 * k₀ + 1) → ℂ) : tsupport (trigTest b ℓ k₀ c) ⊆ Icc (-U) U := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ U ≤ |x| := fun h => hx (by simp [trigTest, hbs x h])
  push Not at h
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

/-- **Bulk lower bound.** If `b = 1` on `[-ℓ, ℓ]`, then `∫ |f_c|² ≥ 2ℓ Σ |c_j|²`. -/
theorem two_mul_sum_le_integral_trigTest {b : ℝ → ℂ} {U ℓ : ℝ} (hℓ : 0 < ℓ)
    (hbc : Continuous b) (hbs : ∀ u, U < |u| → b u = 0) (hb1 : ∀ u, |u| ≤ ℓ → b u = 1)
    (k₀ : ℕ) (c : Fin (2 * k₀ + 1) → ℂ) :
    2 * ℓ * ∑ j, ‖c j‖ ^ 2 ≤ ∫ u, ‖trigTest b ℓ k₀ c u‖ ^ 2 := by
  have hcont : Continuous fun u => ‖trigTest b ℓ k₀ c u‖ ^ 2 :=
    ((hbc.mul (continuous_bandTrigPoly ℓ k₀ c)).norm.pow 2)
  have hcs : HasCompactSupport fun u => ‖trigTest b ℓ k₀ c u‖ ^ 2 :=
    hasCompactSupport_of_support_subset_abs (Λ := U) fun u hu => by
      by_contra h; push Not at h
      exact hu (by simp [trigTest, hbs u h])
  have hint : Integrable fun u => ‖trigTest b ℓ k₀ c u‖ ^ 2 :=
    hcont.integrable_of_hasCompactSupport hcs
  rw [← integral_Icc_norm_bandTrigPoly_sq hℓ k₀ c]
  have heq : ∫ u in Icc (-ℓ) ℓ, ‖bandTrigPoly ℓ k₀ c u‖ ^ 2 =
      ∫ u in Icc (-ℓ) ℓ, ‖trigTest b ℓ k₀ c u‖ ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    simp only [trigTest]
    rw [hb1 u (abs_le.mpr ⟨hu.1, hu.2⟩), one_mul]
  rw [heq]
  exact setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)

/-- `c ↦ f_c` as a linear map. -/
def trigTestMap (b : ℝ → ℂ) (ℓ : ℝ) (k₀ : ℕ) : (Fin (2 * k₀ + 1) → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun c := trigTest b ℓ k₀ c
  map_add' c d := by
    funext u; simp only [trigTest, bandTrigPoly, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      mul_add]
  map_smul' a c := by
    funext u
    simp only [trigTest, bandTrigPoly, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

theorem trigTestMap_injective {b : ℝ → ℂ} {U ℓ : ℝ} (hℓ : 0 < ℓ) (hbc : Continuous b)
    (hbs : ∀ u, U < |u| → b u = 0) (hb1 : ∀ u, |u| ≤ ℓ → b u = 1) (k₀ : ℕ) :
    Function.Injective (trigTestMap b ℓ k₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have h0 : trigTest b ℓ k₀ c = 0 := hc
  have hle := two_mul_sum_le_integral_trigTest hℓ hbc hbs hb1 k₀ c
  rw [h0] at hle
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, integral_zero] at hle
  have hsum : ∑ j, ‖c j‖ ^ 2 = 0 := by
    have hs0 : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    nlinarith
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hsum j
    (Finset.mem_univ _)
  simpa using this

/-! ## The Weil energy of a test vanishing at the low zeros -/

/-- Far from the frequency band the transform of `f_c` is small: if `|b̂(w)| ≤ B/(Re w)²` for
`|Re w| ≥ Δ` in the strip, then `|f̂_c(x)| ≤ (Σ|c_j|) B/(1 + |Re x| - T)²` for `|Re x| > T`,
where `k₀π/ℓ + Δ ≤ T`. -/
theorem norm_paperFT_trigTest_far_le {b : ℝ → ℂ} {U ℓ T Δ B : ℝ} (hb : Integrable b)
    (hbs : ∀ u, U < |u| → b u = 0) (hℓ : 0 < ℓ) {k₀ : ℕ} (hΩ : k₀ * π / ℓ + Δ ≤ T)
    (hΔ : 1 ≤ Δ) (hB : 0 ≤ B)
    (hdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 → Δ ≤ |w.re| → ‖paperFT b w‖ ≤ B / w.re ^ 2)
    (c : Fin (2 * k₀ + 1) → ℂ) {x : ℂ} (hx : |x.im| ≤ 1 / 2) (hT : T < |x.re|) :
    ‖paperFT (trigTest b ℓ k₀ c) x‖ ≤ (∑ j, ‖c j‖) * B / (1 + (|x.re| - T)) ^ 2 := by
  rw [paperFT_trigTest hb hbs, Finset.sum_mul, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  have hτ := abs_trigFreq_le hℓ k₀ j
  set w := x + (trigFreq ℓ k₀ j : ℂ) with hw
  have hwre : w.re = x.re + trigFreq ℓ k₀ j := by simp [hw]
  have hwim : w.im = x.im := by simp [hw]
  have hD : 1 + (|x.re| - T) ≤ |w.re| := by
    rw [hwre]
    have := abs_sub_abs_le_abs_sub x.re (-trigFreq ℓ k₀ j)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hΔw : Δ ≤ |w.re| := by
    rw [hwre]
    have := abs_sub_abs_le_abs_sub x.re (-trigFreq ℓ k₀ j)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have h := hdec w (by rw [hwim]; exact hx) hΔw
  have hD1 : 0 < 1 + (|x.re| - T) := by linarith
  have hsq : (1 + (|x.re| - T)) ^ 2 ≤ w.re ^ 2 := by
    rw [← sq_abs w.re]; exact pow_le_pow_left₀ hD1.le hD 2
  have hB' : B / w.re ^ 2 ≤ B / (1 + (|x.re| - T)) ^ 2 :=
    div_le_div_of_nonneg_left hB (by positivity) hsq
  calc ‖c j‖ * ‖paperFT b w‖ ≤ ‖c j‖ * (B / (1 + (|x.re| - T)) ^ 2) :=
        mul_le_mul_of_nonneg_left (h.trans hB') (norm_nonneg _)
    _ = ‖c j‖ * B / (1 + (|x.re| - T)) ^ 2 := by ring

/-- **Weil energy of a constrained plateau test.** If `f̂_c` vanishes at `γ_ρ` for every zero with
`|Im ρ| ≤ T`, then `‖W(f_c, f_c)‖ ≤ ((Σ|c_j|) B)² · 48 A₀ log(T + 3)`. -/
theorem norm_W_trigTest_le {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {b : ℝ → ℂ} {U ℓ T Δ B : ℝ} (hb : Integrable b) (hbs : ∀ u, U < |u| → b u = 0) (hℓ : 0 < ℓ)
    {k₀ : ℕ} (hΩ : k₀ * π / ℓ + Δ ≤ T) (hΔ : 1 ≤ Δ) (hB : 0 ≤ B)
    (hdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 → Δ ≤ |w.re| → ‖paperFT b w‖ ≤ B / w.re ^ 2)
    (c : Fin (2 * k₀ + 1) → ℂ)
    (hc : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T →
      paperFT (trigTest b ℓ k₀ c) (gammaOf ρ) = 0) :
    ‖zetaZeroConfig.W (trigTest b ℓ k₀ c) (trigTest b ℓ k₀ c)‖ ≤
      ((∑ j, ‖c j‖) * B) ^ 2 * (48 * A₀ * Real.log (T + 3)) := by
  have hT0 : 0 ≤ T := by
    have : 0 ≤ (k₀ : ℝ) * π / ℓ := by positivity
    linarith
  set f := trigTest b ℓ k₀ c with hf
  set K := ((∑ j, ‖c j‖) * B) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨hs₁, hle₁⟩ := window_tsum_le zetaZeroConfig hA₀ hloc T
  obtain ⟨hs₂, hle₂⟩ := window_tsum_le zetaZeroConfig hA₀ hloc (-T)
  set g : zetaZeroConfig.carrier → ℝ := fun ρ =>
    K * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - T|) ^ 3 +
      (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - -T|) ^ 3) with hg
  have hgs : Summable g := (hs₁.add hs₂).mul_left K
  have hpt : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand f f ρ‖ ≤ g ρ := by
    intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hg0 : 0 ≤ g ρ := by simp only [hg]; positivity
    by_cases hlow : |(ρ : ℂ).im| ≤ T
    · unfold ZeroConfig.Wsummand
      rw [hc _ hmem hlow, mul_zero, zero_mul, norm_zero]; exact hg0
    · push Not at hlow
      have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
      have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
        rw [Complex.conj_im, abs_neg]; exact hIm
      have hre1 : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
      have hre2 : ((starRingEnd ℂ) (gammaOf (ρ : ℂ))).re = (ρ : ℂ).im := by
        rw [Complex.conj_re, WeilEF.gammaOf_re]
      have hv1 := norm_paperFT_trigTest_far_le hb hbs hℓ hΩ hΔ hB hdec c hIm
        (by rw [hre1]; exact hlow)
      have hv2 := norm_paperFT_trigTest_far_le hb hbs hℓ hΩ hΔ hB hdec c hIm'
        (by rw [hre2]; exact hlow)
      rw [hre1] at hv1; rw [hre2] at hv2
      unfold ZeroConfig.Wsummand
      rw [norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
      set D := 1 + (|(ρ : ℂ).im| - T) with hD
      have hD1 : 1 ≤ D := by rw [hD]; linarith
      have hprod : ‖paperFT f (gammaOf (ρ : ℂ))‖ *
          ‖paperFT f ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖ ≤ K / D ^ 3 := by
        calc ‖paperFT f (gammaOf (ρ : ℂ))‖ * ‖paperFT f ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖
            ≤ ((∑ j, ‖c j‖) * B / D ^ 2) * ((∑ j, ‖c j‖) * B / D ^ 2) :=
              mul_le_mul hv1 hv2 (norm_nonneg _) (by positivity)
          _ = K / D ^ 4 := by rw [hK, div_mul_div_comm]; congr 1 <;> ring
          _ ≤ K / D ^ 3 := by
              apply div_le_div_of_nonneg_left hK0 (by positivity)
              calc D ^ 3 = D ^ 3 * 1 := by ring
                _ ≤ D ^ 3 * D := by gcongr
                _ = D ^ 4 := by ring
      have hDsplit : 1 / D ^ 3 ≤ 1 / (1 + |(ρ : ℂ).im - T|) ^ 3 +
          1 / (1 + |(ρ : ℂ).im - -T|) ^ 3 := by
        rcases lt_or_gt_of_ne (show (ρ : ℂ).im ≠ 0 by
          intro h; rw [h, abs_zero] at hlow; linarith) with hneg | hpos
        · have e : D = 1 + |(ρ : ℂ).im - -T| := by
            rw [hD, abs_of_neg hneg, sub_neg_eq_add, abs_of_nonpos (by
              rw [abs_of_neg hneg] at hlow; linarith)]; ring
          rw [e]
          have : 0 ≤ 1 / (1 + |(ρ : ℂ).im - T|) ^ 3 := by positivity
          linarith
        · have e : D = 1 + |(ρ : ℂ).im - T| := by
            rw [hD, abs_of_pos hpos, abs_of_nonneg (by rw [abs_of_pos hpos] at hlow; linarith)]
          rw [e]
          have : 0 ≤ 1 / (1 + |(ρ : ℂ).im - -T|) ^ 3 := by positivity
          linarith
      calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f (gammaOf (ρ : ℂ))‖ *
            ‖paperFT f ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖
          = (zetaZeroConfig.mult ρ : ℝ) * (‖paperFT f (gammaOf (ρ : ℂ))‖ *
            ‖paperFT f ((starRingEnd ℂ) (gammaOf (ρ : ℂ)))‖) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (K / D ^ 3) := mul_le_mul_of_nonneg_left hprod hm
        _ = K * ((zetaZeroConfig.mult ρ : ℝ) * (1 / D ^ 3)) := by ring
        _ ≤ K * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3 +
              1 / (1 + |(ρ : ℂ).im - -T|) ^ 3)) := by gcongr
        _ = g ρ := by simp only [hg]; ring
  have hsum' : Summable fun ρ : zetaZeroConfig.carrier => ‖zetaZeroConfig.Wsummand f f ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hgs
  unfold ZeroConfig.W
  refine (norm_tsum_le_tsum_norm hsum').trans ((Summable.tsum_le_tsum hpt hsum' hgs).trans ?_)
  rw [hg, tsum_mul_left, Summable.tsum_add hs₁ hs₂]
  rw [abs_neg, abs_of_nonneg hT0] at hle₂
  rw [abs_of_nonneg hT0] at hle₁
  calc K * (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) /
        (1 + |(ρ : ℂ).im - T|) ^ 3 + ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - -T|) ^ 3)
      ≤ K * (24 * A₀ * Real.log (T + 3) + 24 * A₀ * Real.log (T + 3)) :=
        mul_le_mul_of_nonneg_left (add_le_add hle₁ hle₂) hK0
    _ = K * (48 * A₀ * Real.log (T + 3)) := by ring

end

end RHTower
