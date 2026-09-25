import GaloisForLFunctions.RHTower.SelbergModalFrobenius
import GaloisForLFunctions.RHTower.SarnakXueCuspTail
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.MaassCongruenceL2

open Set Filter Topology UpperHalfPlane

/-!
# Energy rigidity of Maass Fourier modes below `1/4`

For `a'' = (k² - λ/y²) a` on `y > 0` the energy `F = Re(ā a') - |a|²/(2y)` has
`F' = |a' - a/(2y)|² + (k² + (1/4 - λ)/y²)|a|²` (`hasDerivAt_energyF`). For `λ < 1/4` it is nondecreasing, so
`F → 0` at `0⁺` gives `F ≥ 0`, whence `(|a|²)' = 2F + |a|²/y ≥ 0`; with `a → 0` at `∞` the mode vanishes
(`eq_zero_of_energy`). If `a = O(y^{s₀})` and `y a' = O(y^{s₀})` with `s₀ > 1/2`, then `F = O(y^{2s₀-1}) → 0`
(`energy_tendsto_zero`).

For a `Γ(N+1)` Maass cusp form with `λ = s₀(1 - s₀)`, `1/2 < s₀ < 1`, every Fourier coefficient satisfies
`a(y) = α y^{1-s₀} + O(y^{s₀})` as `y → 0⁺`, and `α = 0` forces the coefficient to vanish identically
(`maassCoefficient_leading`).
-/

namespace GaloisForLFunctions.RHTower.SelbergModalEnergy

open SarnakXueCuspTail

variable {a a' a'' : ℝ → ℂ} {k lam : ℝ}

/-- The energy `F(y) = Re(ā a') - |a|²/(2y)`. -/
noncomputable def energyF (a a' : ℝ → ℂ) (y : ℝ) : ℝ :=
  (a y).re * (a' y).re + (a y).im * (a' y).im - ((a y).re ^ 2 + (a y).im ^ 2) / (2 * y)

/-- Its derivative is a sum of squares plus `(k² + (1/4 - λ)/y²)|a|²`. -/
theorem hasDerivAt_energyF {y : ℝ} (hy : 0 < y) (ha : HasDerivAt a (a' y) y)
    (ha' : HasDerivAt a' (a'' y) y) (hode : a'' y = ((k ^ 2 - lam / y ^ 2 : ℝ) : ℂ) * a y) :
    HasDerivAt (energyF a a')
      (((a' y).re - (a y).re / (2 * y)) ^ 2 + ((a' y).im - (a y).im / (2 * y)) ^ 2 +
        (k ^ 2 + (1 / 4 - lam) / y ^ 2) * ((a y).re ^ 2 + (a y).im ^ 2)) y := by
  have hr := hasDerivAt_re ha
  have hi := hasDerivAt_im ha
  have hr' := hasDerivAt_re ha'
  have hi' := hasDerivAt_im ha'
  have hyinv : HasDerivAt (fun t : ℝ => 2 * t) 2 y := by simpa using (hasDerivAt_id y).const_mul 2
  have h := ((hr.mul hr').add (hi.mul hi')).sub (((hr.pow 2).add (hi.pow 2)).div hyinv (by positivity))
  unfold energyF
  refine h.congr_deriv ?_
  have hre : (a'' y).re = (k ^ 2 - lam / y ^ 2) * (a y).re := by rw [hode, Complex.re_ofReal_mul]
  have him : (a'' y).im = (k ^ 2 - lam / y ^ 2) * (a y).im := by rw [hode, Complex.im_ofReal_mul]
  rw [hre, him]
  simp only [Pi.add_apply, Pi.pow_apply]
  norm_num
  field_simp
  ring


/-- **Vanishing from the energy.** If `λ < 1/4`, the energy tends to `0` at `0⁺` and `a → 0` at `∞`,
then `a ≡ 0` on `y > 0`. -/
theorem eq_zero_of_energy (hlam : lam < 1 / 4)
    (ha : ∀ y, 0 < y → HasDerivAt a (a' y) y) (ha' : ∀ y, 0 < y → HasDerivAt a' (a'' y) y)
    (hode : ∀ y, 0 < y → a'' y = ((k ^ 2 - lam / y ^ 2 : ℝ) : ℂ) * a y)
    (h0 : Tendsto (energyF a a') (𝓝[>] 0) (𝓝 0)) (hinf : Tendsto a atTop (𝓝 0)) :
    ∀ y, 0 < y → a y = 0 := by
  set F := energyF a a'
  have hd : ∀ y, 0 < y → HasDerivAt F (((a' y).re - (a y).re / (2 * y)) ^ 2 +
      ((a' y).im - (a y).im / (2 * y)) ^ 2 + (k ^ 2 + (1 / 4 - lam) / y ^ 2) * ((a y).re ^ 2 + (a y).im ^ 2)) y :=
    fun y hy => hasDerivAt_energyF hy (ha y hy) (ha' y hy) (hode y hy)
  have hmono : MonotoneOn F (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ioi] at hy; exact (hd y hy).differentiableAt.differentiableWithinAt
    · intro y hy; rw [interior_Ioi] at hy; rw [(hd y hy).deriv]
      have : 0 ≤ (1 / 4 - lam) / y ^ 2 := div_nonneg (by linarith) (by positivity)
      positivity
  have hFnn : ∀ y, 0 < y → 0 ≤ F y := by
    intro y hy
    apply le_of_tendsto h0
    filter_upwards [Ioo_mem_nhdsGT hy] with t ht
    exact hmono ht.1 hy ht.2.le
  set G : ℝ → ℝ := fun y => (a y).re ^ 2 + (a y).im ^ 2
  have hGd : ∀ y, 0 < y → HasDerivAt G (2 * F y + G y / y) y := by
    intro y hy
    have h := ((hasDerivAt_re (ha y hy)).pow 2).add ((hasDerivAt_im (ha y hy)).pow 2)
    refine h.congr_deriv ?_
    simp only [F, G, energyF]
    field_simp
    ring
  have hGmono : MonotoneOn G (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun y hy => (hGd y hy).continuousAt.continuousWithinAt
    · intro y hy; rw [interior_Ioi] at hy; exact (hGd y hy).differentiableAt.differentiableWithinAt
    · intro y hy; rw [interior_Ioi] at hy; rw [(hGd y hy).deriv]
      have := hFnn y hy
      have : 0 ≤ G y / y := div_nonneg (by positivity) hy.le
      linarith
  have hGlim : Tendsto G atTop (𝓝 0) := by
    have : Tendsto (fun y => Complex.normSq (a y)) atTop (𝓝 (Complex.normSq 0)) :=
      (Complex.continuous_normSq.tendsto 0).comp hinf
    simpa [G, Complex.normSq_apply, pow_two] using this
  intro y hy
  have hG0 : G y ≤ 0 := by
    apply ge_of_tendsto hGlim
    filter_upwards [eventually_ge_atTop y] with t ht
    exact hGmono hy (hy.trans_le ht) ht
  apply Complex.ext <;> simp <;> nlinarith [sq_nonneg (a y).re, sq_nonneg (a y).im]

/-- **The energy vanishes at `0⁺` for a subdominant mode.** If `‖a y‖ ≤ C y^{s₀}` and `‖y a'(y)‖ ≤ C y^{s₀}` on
`(0, 1]` with `s₀ > 1/2`, then `F(y) → 0` as `y → 0⁺`. -/
theorem energy_tendsto_zero {s₀ C : ℝ} (hs : 1 / 2 < s₀)
    (hA : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y‖ ≤ C * y ^ s₀) (hB : ∀ y ∈ Ioc (0 : ℝ) 1, ‖(y : ℂ) * a' y‖ ≤ C * y ^ s₀) :
    Tendsto (energyF a a') (𝓝[>] 0) (𝓝 0) := by
  have hr : Tendsto (fun y : ℝ => 2 * C ^ 2 * y ^ (2 * s₀ - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (Real.continuousAt_rpow_const 0 (2 * s₀ - 1) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at hc
    simpa using (hc.const_mul (2 * C ^ 2)).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hr
  filter_upwards [Ioc_mem_nhdsGT one_pos] with y hy
  have hy0 := hy.1
  have hyy : y ^ s₀ * y ^ s₀ = y * y ^ (2 * s₀ - 1) := by
    rw [← Real.rpow_add hy0, show s₀ + s₀ = 1 + (2 * s₀ - 1) by ring, Real.rpow_add hy0, Real.rpow_one]
  have ha1 := hA y hy
  have hb1 := hB y hy
  have hC : 0 ≤ C * y ^ s₀ := (norm_nonneg _).trans ha1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0] at hb1
  have hinner : |(a y).re * (a' y).re + (a y).im * (a' y).im| ≤ ‖a y‖ * ‖a' y‖ := by
    have : (a y).re * (a' y).re + (a y).im * (a' y).im = (starRingEnd ℂ (a y) * a' y).re := by
      simp [Complex.mul_re]
    rw [this]
    exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  have hsq : (a y).re ^ 2 + (a y).im ^ 2 = ‖a y‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  unfold energyF
  rw [Real.norm_eq_abs, hsq]
  have h1 : ‖a y‖ * ‖a' y‖ ≤ C ^ 2 * y ^ (2 * s₀ - 1) := by
    have : y * (‖a y‖ * ‖a' y‖) ≤ y * (C ^ 2 * y ^ (2 * s₀ - 1)) := by
      calc y * (‖a y‖ * ‖a' y‖) = ‖a y‖ * (y * ‖a' y‖) := by ring
        _ ≤ (C * y ^ s₀) * (C * y ^ s₀) := mul_le_mul ha1 hb1 (by positivity) hC
        _ = y * (C ^ 2 * y ^ (2 * s₀ - 1)) := by rw [mul_mul_mul_comm, hyy]; ring
    exact le_of_mul_le_mul_left this hy0
  have h2 : ‖a y‖ ^ 2 / (2 * y) ≤ C ^ 2 * y ^ (2 * s₀ - 1) := by
    rw [div_le_iff₀ (by positivity)]
    have : ‖a y‖ ^ 2 ≤ (C * y ^ s₀) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha1 2
    have hp : 0 ≤ C ^ 2 * y ^ (2 * s₀ - 1) * y := by positivity
    nlinarith [hyy]
  have h3 : 0 ≤ ‖a y‖ ^ 2 / (2 * y) := by positivity
  rw [abs_le] at hinner ⊢
  constructor <;> nlinarith

section Maass

open SelbergMaassFourier SelbergMaassMean _root_.RHTower

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

theorem maassCoefficient_bounded : ∃ M : ℝ, ∀ n : ℤ, ∀ y : ℝ, 0 < y → ‖maassCoefficient N f n y‖ ≤ M := by
  obtain ⟨M, hM⟩ := MaassCongruenceL2.source_bounded N f
  refine ⟨M, fun n y hy => ?_⟩
  have hb : ∀ x ∈ uIoc (0 : ℝ) (N + 1 : ℕ), ‖(f.1.1 ∘ ofComplex) (point x y)‖ ≤ M := by
    intro x _
    have hp : 0 < (point x y).im := by simpa [point] using hy
    simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hp] using hM ⟨point x y, hp⟩
  simpa only [maassCoefficient, coefficient] using
    deningerFourierCoeff_norm_le (by positivity : (0 : ℝ) < (N + 1 : ℕ)) hb n

/-- **Leading-coefficient rigidity.** For `λ = s₀(1 - s₀)` with `1/2 < s₀ < 1`, each Fourier coefficient of a
`Γ(N+1)` Maass cusp form is `α y^{1-s₀} + O(y^{s₀})` as `y → 0⁺`, and it vanishes identically when `α = 0`. -/
theorem maassCoefficient_leading {s₀ : ℝ} (hs1 : 1 / 2 < s₀) (hs2 : s₀ < 1) (hlam : lam = s₀ * (1 - s₀))
    (n : ℤ) : ∃ α : ℂ, ∃ C : ℝ,
      (∀ y ∈ Ioc (0 : ℝ) 1, ‖maassCoefficient N f n y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀) ∧
      (α = 0 → ∀ y, 0 < y → maassCoefficient N f n y = 0) := by
  set a := maassCoefficient N f n
  set k := signedFrequency (N + 1 : ℕ) n
  have h1 : ∀ y, 0 < y → HasDerivAt a (deriv a y) y := fun y hy => maassCoefficient_hasDerivAt N f n hy
  have h2 : ∀ y, 0 < y → HasDerivAt (deriv a) (deriv (deriv a) y) y :=
    fun y hy => maassCoefficient_second_hasDerivAt N f n hy
  have hode : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv a) y = ((k ^ 2 * y ^ 2 - lam : ℝ) : ℂ) * a y := by
    intro y hy
    have := maassCoefficient_modal_equation N f n hy
    push_cast
    linear_combination -this
  obtain ⟨M, hM⟩ := maassCoefficient_bounded N f
  obtain ⟨α, C, hC⟩ := SelbergModalFrobenius.frobenius_asymptotics (a := a) (a' := deriv a)
    (a'' := deriv (deriv a)) (k := k) hs1 hs2.le (M := M) (fun y hy => h1 y hy.1) (fun y hy => h2 y hy.1)
    (fun y hy => by rw [hode y hy.1, hlam]) (fun y hy => hM n y hy.1)
  refine ⟨α, C, fun y hy => (hC y hy).1, fun hα => ?_⟩
  apply eq_zero_of_energy (lam := lam) (k := k) (by rw [hlam]; nlinarith) h1 h2
  · intro y hy
    have hy2 : (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hy 2).ne'
    have := hode y hy
    rw [mul_comm, ← eq_div_iff hy2] at this
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [this]; push_cast; field_simp
  · apply energy_tendsto_zero (C := C + s₀ * C) hs1
    · intro y hy
      have := (hC y hy).1
      rw [hα, zero_mul, sub_zero] at this
      have hs : 0 ≤ s₀ * (C * y ^ s₀) := mul_nonneg (by linarith) ((norm_nonneg _).trans this)
      nlinarith
    · intro y hy
      have hA := (hC y hy).1
      have hB := (hC y hy).2
      rw [hα, zero_mul, sub_zero] at hA
      rw [hα, mul_zero, zero_mul, sub_zero] at hB
      calc ‖(y : ℂ) * deriv a y‖ = ‖((y : ℂ) * deriv a y - s₀ * a y) + s₀ * a y‖ := by ring_nf
        _ ≤ ‖(y : ℂ) * deriv a y - s₀ * a y‖ + ‖(s₀ : ℂ) * a y‖ := norm_add_le _ _
        _ ≤ C * y ^ s₀ + s₀ * (C * y ^ s₀) := by
            gcongr
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
            gcongr
        _ = (C + s₀ * C) * y ^ s₀ := by ring
  · exact maassCoefficient_decay N f n

end Maass

end GaloisForLFunctions.RHTower.SelbergModalEnergy
