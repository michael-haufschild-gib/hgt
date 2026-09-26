import GaloisForLFunctions.RHTower.ThetaChiEightSeries

/-!
# The theta series of the quadratic character modulo `12`

For the even primitive character `χ₁₂` (`χ₁₂(n) = 1` for `n ≡ ±1`, `-1` for `n ≡ ±5 (mod 12)`,
`0` otherwise) put `ϑ₁₂(τ) = ∑_{n ∈ ℤ} χ₁₂(n) e^{πiτn²/12}`.  Then

* `ϑ₁₂(τ + 1) = e^{πi/12} ϑ₁₂(τ)`, because `n² ≡ 1 (mod 24)` on the support of `χ₁₂`;
* `ϑ₁₂(-1/τ) = (-iτ)^{1/2} ϑ₁₂(τ)`.

The inversion law is Poisson summation over residue classes: splitting `n = 12m + r` writes `ϑ₁₂` as
`∑_r χ₁₂(r) e^{πiτr²/12} θ(rτ, 12τ)`; the Jacobi inversion of each `θ(rτ, 12τ)` cancels the Gaussian
prefactor and produces `∑_r χ₁₂(r) θ(r/12, -1/(12τ))`, whose Fourier coefficients are the Gauss sums
`∑_r χ₁₂(r) e^{2πimr/12} = √12 · χ₁₂(m)`.
-/

open Complex
open scoped Real

namespace RHTower

noncomputable section

/-! ## The character -/

/-- `χ₁₂` on the integers. -/
def chiTwelve (k : ℤ) : ℝ :=
  if k % 12 = 1 ∨ k % 12 = 11 then 1 else if k % 12 = 5 ∨ k % 12 = 7 then -1 else 0

theorem chiTwelve_add_twelve_mul (q k : ℤ) : chiTwelve (12 * q + k) = chiTwelve k := by
  unfold chiTwelve
  split_ifs <;> first | rfl | (exfalso; omega)

theorem chiTwelve_neg (k : ℤ) : chiTwelve (-k) = chiTwelve k := by
  unfold chiTwelve
  split_ifs <;> first | rfl | (exfalso; omega)

theorem abs_chiTwelve_le (k : ℤ) : |chiTwelve k| ≤ 1 := by
  unfold chiTwelve; split_ifs <;> norm_num

theorem chiTwelve_zero : chiTwelve 0 = 0 := by unfold chiTwelve; norm_num

/-- On the support of `χ₁₂`, `n² ≡ 1 (mod 24)`. -/
theorem sq_eq_one_add_of_chiTwelve_ne_zero {n : ℤ} (h : chiTwelve n ≠ 0) :
    ∃ K : ℤ, n ^ 2 = 1 + 24 * K := by
  obtain ⟨q, r, hr0, hr12, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 12 ∧ n = 12 * q + r :=
    ⟨n / 12, n % 12, by omega, by omega, by omega⟩
  rw [chiTwelve_add_twelve_mul] at h
  have hr : r = 1 ∨ r = 5 ∨ r = 7 ∨ r = 11 := by
    by_contra hc
    apply h
    unfold chiTwelve
    split_ifs <;> first | rfl | (exfalso; omega)
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨6 * q ^ 2 + q, by ring⟩
  · exact ⟨6 * q ^ 2 + 5 * q + 1, by ring⟩
  · exact ⟨6 * q ^ 2 + 7 * q + 2, by ring⟩
  · exact ⟨6 * q ^ 2 + 11 * q + 5, by ring⟩

/-! ## The theta series -/

/-- `ϑ₁₂(τ) = ∑_{n ∈ ℤ} χ₁₂(n) e^{πiτn²/12}`. -/
def thetaChiTwelve (τ : ℂ) : ℂ :=
  ∑' n : ℤ, (chiTwelve n : ℂ) * Complex.exp (π * I * τ * ((n : ℂ) ^ 2 / 12))

theorem norm_thetaChiTwelve_term_le (τ : ℂ) (k : ℤ) :
    ‖(chiTwelve k : ℂ) * Complex.exp (π * I * τ * ((k : ℂ) ^ 2 / 12))‖ ≤
      Real.exp (-(π * (τ.im / 12) * (k : ℝ) ^ 2)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := norm_cexp_pi_I_mul τ ((k : ℝ) ^ 2 / 12)
  have e : ((((k : ℝ) ^ 2 / 12 : ℝ)) : ℂ) = (k : ℂ) ^ 2 / 12 := by push_cast; ring
  rw [e] at h
  rw [h]
  have := abs_chiTwelve_le k
  have e2 : -(π * τ.im * ((k : ℝ) ^ 2 / 12)) = -(π * (τ.im / 12) * (k : ℝ) ^ 2) := by ring
  rw [e2]
  calc |chiTwelve k| * Real.exp (-(π * (τ.im / 12) * (k : ℝ) ^ 2))
      ≤ 1 * Real.exp (-(π * (τ.im / 12) * (k : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = _ := one_mul _

theorem summable_thetaChiTwelve_norm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable (fun k : ℤ => ‖(chiTwelve k : ℂ) * Complex.exp (π * I * τ * ((k : ℂ) ^ 2 / 12))‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaChiTwelve_term_le τ)
    (summable_gauss_int (by positivity))

/-! ## Translation -/

theorem thetaChiTwelve_add_one (τ : ℂ) :
    thetaChiTwelve (τ + 1) = Complex.exp (π * I / 12) * thetaChiTwelve τ := by
  unfold thetaChiTwelve
  rw [← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  by_cases h : chiTwelve n = 0
  · simp [h]
  obtain ⟨K, hK⟩ := sq_eq_one_add_of_chiTwelve_ne_zero h
  have hKc : ((n : ℂ)) ^ 2 = 1 + 24 * (K : ℂ) := by exact_mod_cast hK
  have e : (π : ℂ) * I * (τ + 1) * ((n : ℂ) ^ 2 / 12) =
      π * I / 12 + π * I * τ * ((n : ℂ) ^ 2 / 12) + (K : ℂ) * (2 * π * I) := by
    rw [hKc]; ring
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring

/-! ## Residue classes modulo `12` -/

/-- `ℤ ≃ Fin 12 × ℤ` by residue and quotient. -/
def residueTwelveEquiv : Fin 12 × ℤ ≃ ℤ where
  toFun p := 12 * p.2 + (p.1 : ℤ)
  invFun n := (⟨(n % 12).toNat, by omega⟩, n / 12)
  left_inv p := by
    obtain ⟨⟨r, hr⟩, m⟩ := p
    ext
    · simp only; omega
    · simp only; omega
  right_inv n := by simp only; omega

theorem tsum_int_eq_sum_residue_twelve {f : ℤ → ℂ} (hf : Summable f) :
    ∑' n : ℤ, f n = ∑ r : Fin 12, ∑' m : ℤ, f (12 * m + r) := by
  have h1 : HasSum (fun p : Fin 12 × ℤ => f (residueTwelveEquiv p)) (∑' n, f n) :=
    (residueTwelveEquiv.hasSum_iff).mpr hf.hasSum
  have hfib : ∀ r : Fin 12, HasSum (fun m : ℤ => f (residueTwelveEquiv (r, m)))
      (∑' m : ℤ, f (12 * m + r)) := by
    intro r
    have hinj : Function.Injective (fun m : ℤ => residueTwelveEquiv (r, m)) := by
      intro a b h; simpa using residueTwelveEquiv.injective h
    exact (hf.comp_injective hinj).hasSum
  have h2 := h1.prod_fiberwise hfib
  exact h2.unique (hasSum_fintype _)

/-- `ϑ₁₂(τ) = ∑_r χ₁₂(r) e^{πiτr²/12} θ(rτ, 12τ)`. -/
theorem thetaChiTwelve_eq_sum {τ : ℂ} (hτ : 0 < τ.im) :
    thetaChiTwelve τ = ∑ r : Fin 12, (chiTwelve r : ℂ) *
      Complex.exp (π * I * τ * (((r : ℤ) : ℂ) ^ 2 / 12)) *
        jacobiTheta₂ (((r : ℤ) : ℂ) * τ) (12 * τ) := by
  unfold thetaChiTwelve
  rw [tsum_int_eq_sum_residue_twelve (summable_thetaChiTwelve_norm hτ).of_norm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [chiTwelve_add_twelve_mul, jacobiTheta₂_term]
  rw [show (chiTwelve r : ℂ) * Complex.exp (π * I * τ * (((r : ℤ) : ℂ) ^ 2 / 12)) *
      Complex.exp (2 * π * I * m * (((r : ℤ) : ℂ) * τ) + π * I * m ^ 2 * (12 * τ)) =
      (chiTwelve r : ℂ) * (Complex.exp (π * I * τ * (((r : ℤ) : ℂ) ^ 2 / 12)) *
      Complex.exp (2 * π * I * m * (((r : ℤ) : ℂ) * τ) + π * I * m ^ 2 * (12 * τ))) by ring,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ## Gauss sums -/

theorem sum_fin_twelve_chiTwelve (g : ℤ → ℂ) :
    ∑ r : Fin 12, (chiTwelve r : ℂ) * g r = g 1 - g 5 - g 7 + g 11 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [chiTwelve]
  ring

theorem cos_pi_mul_div_six_of_odd {m : ℤ} (hm : m % 2 = 1) :
    Real.cos (π * m / 6) = Real.sqrt 3 / 2 * chiTwelve m := by
  obtain ⟨q, r, hr0, hr12, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < 12 ∧ m = 12 * q + r :=
    ⟨m / 12, m % 12, by omega, by omega, by omega⟩
  rw [chiTwelve_add_twelve_mul]
  have e : π * ((12 * q + r : ℤ) : ℝ) / 6 = π * r / 6 + q * (2 * π) := by push_cast; ring
  rw [e, Real.cos_add_int_mul_two_pi]
  interval_cases r
  all_goals first
    | (exfalso; omega)
    | skip
  · rw [show π * ((1 : ℤ) : ℝ) / 6 = π / 6 by push_cast; ring, Real.cos_pi_div_six]
    unfold chiTwelve; norm_num
  · rw [show π * ((3 : ℤ) : ℝ) / 6 = π / 2 by push_cast; ring, Real.cos_pi_div_two]
    unfold chiTwelve; norm_num
  · rw [show π * ((5 : ℤ) : ℝ) / 6 = π - π / 6 by push_cast; ring, Real.cos_pi_sub,
      Real.cos_pi_div_six]
    unfold chiTwelve; norm_num
  · rw [show π * ((7 : ℤ) : ℝ) / 6 = π / 6 + π by push_cast; ring, Real.cos_add_pi,
      Real.cos_pi_div_six]
    unfold chiTwelve; norm_num
  · rw [show π * ((9 : ℤ) : ℝ) / 6 = π / 2 + π by push_cast; ring, Real.cos_add_pi,
      Real.cos_pi_div_two]
    unfold chiTwelve; norm_num
  · rw [show π * ((11 : ℤ) : ℝ) / 6 = 2 * π - π / 6 by push_cast; ring, Real.cos_two_pi_sub,
      Real.cos_pi_div_six]
    unfold chiTwelve; norm_num

theorem chiTwelve_of_even {m : ℤ} (hm : m % 2 = 0) : chiTwelve m = 0 := by
  unfold chiTwelve; split_ifs <;> first | rfl | (exfalso; omega)

/-- **The Gauss sums of `χ₁₂`.** -/
theorem gaussSum_chiTwelve (m : ℤ) :
    ∑ r : Fin 12, (chiTwelve r : ℂ) * Complex.exp (2 * π * I * m * ((r : ℤ) : ℂ) / 12) =
      (Real.sqrt 12 : ℂ) * chiTwelve m := by
  rw [sum_fin_twelve_chiTwelve (fun r => Complex.exp (2 * π * I * m * (r : ℂ) / 12))]
  set ζ : ℂ := Complex.exp (π * I * m / 6) with hζ
  have hpow : ∀ k : ℕ, Complex.exp (2 * π * I * m * ((k : ℤ) : ℂ) / 12) = ζ ^ k := by
    intro k; rw [hζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h1 := hpow 1; have h5 := hpow 5; have h7 := hpow 7; have h11 := hpow 11
  push_cast at h1 h5 h7 h11
  simp only [Int.cast_one, Int.cast_ofNat]
  rw [h1, h5, h7, h11]
  have h6 : ζ ^ 6 = Complex.exp (m * (π * I)) := by
    rw [hζ, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I] at h6
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · have he : Even m := Int.even_iff.mpr hm
    rw [he.neg_one_zpow] at h6
    rw [chiTwelve_of_even hm]
    have : ζ ^ 1 - ζ ^ 5 - ζ ^ 7 + ζ ^ 11 = (ζ - ζ ^ 5) * (1 - ζ ^ 6) := by ring
    rw [this, h6]; simp
  · have ho : Odd m := Int.odd_iff.mpr hm
    rw [ho.neg_one_zpow] at h6
    have hinv : ζ * Complex.exp (-(π * I * m / 6)) = 1 := by
      rw [hζ, ← Complex.exp_add]; simp
    have h5' : ζ ^ 5 = -Complex.exp (-(π * I * m / 6)) := by
      linear_combination (-ζ ^ 5) * hinv + Complex.exp (-(π * I * m / 6)) * h6
    have hsum : ζ ^ 1 - ζ ^ 5 - ζ ^ 7 + ζ ^ 11 =
        2 * (Complex.exp (π * m / 6 * I) + Complex.exp (-(π * m / 6) * I)) := by
      have e7 : ζ ^ 7 = ζ ^ 6 * ζ := by ring
      have e11 : ζ ^ 11 = ζ ^ 6 * ζ ^ 5 := by ring
      rw [e7, e11, h6, h5', hζ]
      have ea : Complex.exp (π * I * m / 6) = Complex.exp (π * m / 6 * I) := by congr 1; ring
      have eb : Complex.exp (-(π * I * m / 6)) = Complex.exp (-(π * m / 6) * I) := by
        congr 1; ring
      rw [ea, eb]; ring
    rw [hsum, ← Complex.two_cos]
    rw [show ((π : ℂ) * m / 6) = ((π * m / 6 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      cos_pi_mul_div_six_of_odd hm]
    have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    rw [h12]; push_cast; ring

/-! ## Inversion -/

theorem cpow_half_twelve_mul {x : ℂ} (hx : x ≠ 0) :
    ((12 : ℝ) * x : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 12 : ℂ) * x ^ (1 / 2 : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by norm_num) hx),
    Complex.log_ofReal_mul (by norm_num) hx, Complex.cpow_def_of_ne_zero hx, add_mul,
    Complex.exp_add]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), Complex.ofReal_exp]
  push_cast
  ring_nf

/-- **The inversion law of `ϑ₁₂`.** -/
theorem thetaChiTwelve_S {τ : ℂ} (hτ : 0 < τ.im) :
    thetaChiTwelve (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaChiTwelve τ := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hIτ : -I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0
  set σ : ℂ := -1 / (12 * τ) with hσ
  have hσim : 0 < σ.im := by
    have : σ = -1 / τ / 12 := by rw [hσ]; field_simp
    rw [this]
    have := neg_one_div_im_pos hτ
    simp only [Complex.div_ofNat_im]; linarith
  -- inversion of every residue class
  have hres : thetaChiTwelve τ = 1 / (-I * (12 * τ)) ^ (1 / 2 : ℂ) *
      ∑ r : Fin 12, (chiTwelve r : ℂ) * jacobiTheta₂ (((r : ℤ) : ℂ) / 12) σ := by
    rw [thetaChiTwelve_eq_sum hτ, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [jacobiTheta₂_functional_equation]
    have e1 : ((r : ℤ) : ℂ) * τ / (12 * τ) = ((r : ℤ) : ℂ) / 12 := by field_simp
    have e2 : -1 / (12 * τ) = σ := rfl
    rw [e1, e2]
    have e3 : Complex.exp (π * I * τ * (((r : ℤ) : ℂ) ^ 2 / 12)) *
        Complex.exp (-π * I * (((r : ℤ) : ℂ) * τ) ^ 2 / (12 * τ)) = 1 := by
      rw [← Complex.exp_add]
      have : (π : ℂ) * I * τ * (((r : ℤ) : ℂ) ^ 2 / 12) +
          -π * I * (((r : ℤ) : ℂ) * τ) ^ 2 / (12 * τ) = 0 := by field_simp; ring
      rw [this, Complex.exp_zero]
    linear_combination (1 / (-I * (12 * τ)) ^ (1 / 2 : ℂ) * (chiTwelve r : ℂ) *
      jacobiTheta₂ (((r : ℤ) : ℂ) / 12) σ) * e3
  -- Fourier expansion of the character combination
  have hfour : ∑ r : Fin 12, (chiTwelve r : ℂ) * jacobiTheta₂ (((r : ℤ) : ℂ) / 12) σ =
      (Real.sqrt 12 : ℂ) * thetaChiTwelve (-1 / τ) := by
    simp only [jacobiTheta₂]
    have hs : ∀ r ∈ (Finset.univ : Finset (Fin 12)),
        Summable (fun m : ℤ => (chiTwelve r : ℂ) * jacobiTheta₂_term m (((r : ℤ) : ℂ) / 12) σ) :=
      fun r _ => ((summable_jacobiTheta₂_term_iff _ σ).mpr hσim).mul_left _
    simp only [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hs]
    unfold thetaChiTwelve
    rw [← tsum_mul_left]
    refine tsum_congr (fun m => ?_)
    have hterm : ∀ r : Fin 12, (chiTwelve r : ℂ) * jacobiTheta₂_term m (((r : ℤ) : ℂ) / 12) σ =
        (chiTwelve r : ℂ) * Complex.exp (2 * π * I * m * ((r : ℤ) : ℂ) / 12) *
          Complex.exp (π * I * m ^ 2 * σ) := by
      intro r
      rw [jacobiTheta₂_term, Complex.exp_add]
      rw [show 2 * π * I * (m : ℂ) * (((r : ℤ) : ℂ) / 12) = 2 * π * I * m * ((r : ℤ) : ℂ) / 12 by
        ring]
      ring
    simp only [hterm]
    rw [← Finset.sum_mul, gaussSum_chiTwelve]
    rw [hσ]
    have e : (π : ℂ) * I * (m : ℂ) ^ 2 * (-1 / (12 * τ)) = π * I * (-1 / τ) * ((m : ℂ) ^ 2 / 12) := by
      field_simp
    rw [e]
    ring
  have hsplit : (-I * (12 * τ)) ^ (1 / 2 : ℂ) = (Real.sqrt 12 : ℂ) * (-I * τ) ^ (1 / 2 : ℂ) := by
    rw [show -I * (12 * τ) = ((12 : ℝ) : ℂ) * (-I * τ) by push_cast; ring]
    exact cpow_half_twelve_mul hIτ
  rw [hfour, hsplit] at hres
  have hs12 : (Real.sqrt 12 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 12 := by positivity
    exact_mod_cast this.ne'
  have hP : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [hres]
  field_simp

/-! ## Holomorphy -/

theorem differentiableAt_thetaChiTwelve {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ thetaChiTwelve τ := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have heq : thetaChiTwelve =ᶠ[nhds τ] fun z => ∑ r : Fin 12, (chiTwelve r : ℂ) *
      Complex.exp (π * I * z * (((r : ℤ) : ℂ) ^ 2 / 12)) *
        jacobiTheta₂ (((r : ℤ) : ℂ) * z) (12 * z) :=
    Filter.eventually_of_mem (hopen.mem_nhds hτ) (fun z hz => thetaChiTwelve_eq_sum hz)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  refine DifferentiableAt.fun_sum (fun r _ => ?_)
  have h12 : 0 < (12 * τ).im := by simp; linarith
  have hJ : DifferentiableAt ℂ (fun z : ℂ => jacobiTheta₂ (((r : ℤ) : ℂ) * z) (12 * z)) τ := by
    have hg : DifferentiableAt ℂ (fun z : ℂ => ((((r : ℤ) : ℂ) * z), 12 * z)) τ :=
      (differentiableAt_const _ |>.mul differentiableAt_id).prodMk
        ((differentiableAt_const _).mul differentiableAt_id)
    exact (hasFDerivAt_jacobiTheta₂ _ h12).differentiableAt.comp τ hg
  exact ((differentiableAt_const _).mul (by fun_prop)).mul hJ

end

end RHTower
