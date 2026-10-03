import GaloisForLFunctions.RHTower.WeilConeSettledLockRigidity
import GaloisForLFunctions.RHTower.RiemannHypothesisLittlewoodBound
import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction

/-!
# Soundararajan's moment bounds from RH, through the Weil cone

**Theorem** (`exists_setIntegral_norm_riemannZeta_criticalLine_rpow_le`).  Assume RH.  For every
`k > 0` and `ε > 0` there are `C`, `T₀` with

`∫_T^{2T} |ζ(½ + it)|^{2k} dt ≤ C T (log T)^{k² + ε}`  for `T ≥ T₀`.

This is Soundararajan's theorem (Ann. of Math. 2009).  Here it is the instance `lam = Λ` of the
Weil-cone moment theorem `exists_setIntegral_exp_mul_le`: RH puts `Λ` in the full Weil cone, and
`Λ` is supported on prime powers with `|Λ(n)| ≤ log n`, so its rest weight
`Σ_{n = p^k, k ≥ 3} 1/(k p^{k/2})` is finite (`summable_restWeight_vonMangoldt`).  The producer
`G = 2ξ` carries the bound from `½ + 1/log T` to the line
(`exists_setIntegral_norm_phiG_rpow_le`).  Just right of the line the statement is
`exists_setIntegral_norm_riemannZeta_rpow_le`.

In particular the hypotheses of the Weil-cone moment and settled-lock theorems are satisfiable
under RH, by `Λ` and `G = 2ξ` with `w ≡ 1`.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz WeilConeMoments IntegerMassRigidity FractionalMassRigidity

/-! ### The rest weight of `Λ` -/

theorem sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  rw [show x ^ n = (Real.sqrt x ^ n) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]]
  exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) n)

/-- `Σ_{n = p^k, k ≥ 3} Λ(n)/(√n log n) < ∞`. -/
theorem summable_restWeight_vonMangoldt : Summable (restWeight vonMangoldtReal) := by
  set φ : Nat.Primes × ℕ → ℕ := fun x => (x.1 : ℕ) ^ (x.2 + 3) with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨⟨p, hp⟩, j⟩ ⟨⟨q, hq⟩, i⟩ h
    have h' : p ^ ((j + 2) + 1) = q ^ ((i + 2) + 1) := h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hp hq h'
    subst h1
    simp only [Prod.mk.injEq, true_and]
    omega
  have hsupp : ∀ n ∉ Set.range φ, restWeight vonMangoldtReal n = 0 := by
    intro n hn
    unfold restWeight
    split_ifs with hc
    · by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
      · simp [vonMangoldtReal, hΛ]
      · exfalso
        obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp
          (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
        rcases Nat.lt_or_ge k 3 with hk3 | hk3
        · interval_cases k
          · rw [pow_one] at hpk; subst hpk; exact hc.2.1 hp
          · subst hpk; exact hc.2.2 (isPrimeSq_sq hp)
        · exact hn ⟨(⟨p, hp⟩, k - 3), by simp only [hφ]; rw [Nat.sub_add_cancel hk3]; exact hpk⟩
    · rfl
  rw [← hinj.summable_iff hsupp]
  have hs2 : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by positivity
  have hs2' : (Real.sqrt 2)⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity)]
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hP : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hG : Summable fun j : ℕ => (Real.sqrt 2)⁻¹ ^ j := summable_geometric_of_lt_one hs2 hs2'
  refine Summable.of_nonneg_of_le (fun x => restWeight_nonneg _ _) (fun x => ?_)
    (hP.mul_of_nonneg hG (fun p => by positivity) (fun j => by positivity))
  obtain ⟨⟨p, hp⟩, j⟩ := x
  simp only [Function.comp, hφ]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  unfold restWeight
  split_ifs with hc
  · rw [vonMangoldtReal, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp, abs_of_pos hlogp]
    push_cast
    rw [Real.log_pow, sqrt_pow_eq hp0.le]
    have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have hk : (1 : ℝ) ≤ ((j + 3 : ℕ) : ℝ) := by norm_cast; omega
    have hden : Real.sqrt p ^ (j + 3) * Real.log p ≤
        Real.sqrt p ^ (j + 3) * (((j + 3 : ℕ) : ℝ) * Real.log p) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith
    calc Real.log p / (Real.sqrt p ^ (j + 3) * (((j + 3 : ℕ) : ℝ) * Real.log p))
        ≤ Real.log p / (Real.sqrt p ^ (j + 3) * Real.log p) :=
          div_le_div_of_nonneg_left hlogp.le (by positivity) hden
      _ = (Real.sqrt p)⁻¹ ^ (j + 3) := by rw [inv_pow]; field_simp
      _ = (Real.sqrt p)⁻¹ ^ 3 * (Real.sqrt p)⁻¹ ^ j := by ring
      _ ≤ ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (Real.sqrt 2)⁻¹ ^ j := by
          refine mul_le_mul (le_of_eq ?_) (pow_le_pow_left₀ (by positivity) ?_ j)
            (by positivity) (by positivity)
          · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_natCast,
              ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le]
            norm_num
          · exact inv_anti₀ (by positivity) (Real.sqrt_le_sqrt hp2)
  · positivity

/-! ### The moments -/

/-- **RH ⇒ moments just right of the line.**  For `k > 0`, `ε > 0`:
`∫_T^{2T} |ζ(½ + 1/log T + it)|^{2k} dt ≤ C T (log T)^{k² + ε}` for large `T`. -/
theorem exists_setIntegral_norm_riemannZeta_rpow_le (hRH : RiemannHypothesis) {k : ℝ}
    (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in Ioc T (2 * T),
          ‖riemannZeta (((1 / 2 + 1 / Real.log T : ℝ) : ℂ) + t * I)‖ ^ (2 * k) ≤
        C * T * Real.log T ^ (k ^ 2 + ε) := by
  have hW : WeilPositiveFull vonMangoldtReal :=
    RHTower.weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
  have hlam : ∀ n : ℕ, 2 ≤ n → |vonMangoldtReal n| ≤ 1 * Real.log n := fun n _ => by
    rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log
  obtain ⟨ε', hε', hε8, hlt⟩ := exists_eps_exponent_lt (k ^ 2) 1 hε
  simp only [one_pow, mul_one] at hlt
  obtain ⟨C, T₀, hC⟩ := exists_setIntegral_exp_mul_le hW summable_restWeight_vonMangoldt
    zero_le_one hlam hk hε' hε8
  refine ⟨max C 0, max T₀ 3, fun T hT => ?_⟩
  have hT3 : 3 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have := Real.exp_one_lt_d9; linarith
  have hσ : 1 / 2 < 1 / 2 + 1 / Real.log T := by
    have : 0 < 1 / Real.log T := by positivity
    linarith
  have h := hC T ((le_max_left _ _).trans hT)
  simp only [one_pow, mul_one] at h
  have heq : ∀ t ∈ Ioc T (2 * T),
      ‖riemannZeta (((1 / 2 + 1 / Real.log T : ℝ) : ℂ) + t * I)‖ ^ (2 * k) =
        Real.exp (2 * k * (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re) := by
    intro t ht
    have ht0 : t ≠ 0 := (hT0.trans ht.1).ne'
    rw [riemannZeta_eq_cexp_producerLogZeta hRH hW hσ ht0, Complex.norm_exp,
      ← Real.exp_mul]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioc heq]
  have hmono : Real.log T ^ (k ^ 2 * (Real.exp ε' / (1 - 4 * ε') ^ 2) + ε') ≤
      Real.log T ^ (k ^ 2 + ε) := Real.rpow_le_rpow_of_exponent_le hlogT hlt.le
  refine h.trans ?_
  calc C * T * Real.log T ^ (k ^ 2 * (Real.exp ε' / (1 - 4 * ε') ^ 2) + ε')
      ≤ max C 0 * T * Real.log T ^ (k ^ 2 * (Real.exp ε' / (1 - 4 * ε') ^ 2) + ε') := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * T * Real.log T ^ (k ^ 2 + ε) := by gcongr

/-- `2ξ` is a producer for `Λ` under RH. -/
theorem two_mul_xi_producer (hRH : RiemannHypothesis) :
    let hW : WeilPositiveFull vonMangoldtReal :=
      RHTower.weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
    (∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt (fun z => 2 * xi z) s) ∧
    (∀ s : ℂ, 1 / 2 < s.re →
      HasDerivAt (fun z => 2 * xi z) (weilContinuation hW s * (2 * xi s)) s) ∧
    2 * xi 2 = bigG vonMangoldtReal 2 := by
  intro hW
  refine ⟨fun s _ => (xi_differentiable s).continuousAt.const_mul 2, fun s hs => ?_, ?_⟩
  · have hxi : xi s ≠ 0 := by
      intro h0
      have := xi_zero_re_eq_half_of_RH hRH h0
      linarith
    rw [weilContinuation_vonMangoldt_eq hW hs, logDeriv_apply]
    have hd := (xi_differentiable s).hasDerivAt.const_mul (2 : ℂ)
    refine hd.congr_deriv ?_
    rw [mul_comm (2 : ℂ) (xi s), ← mul_assoc, div_mul_cancel₀ _ hxi, mul_comm]
  · have h2 := xi_eq_mul_Gammaℝ_mul_riemannZeta (s := 2) (by norm_num) (by norm_num) (by norm_num)
    have hz : riemannZeta 2 = zetaOf vonMangoldtReal 2 := by
      unfold zetaOf
      rw [lamLog_eq_lamLogC, lamLogC_vonMangoldt]
      exact (exp_canonicalEulerLogZeta_eq_riemannZeta (by norm_num)).symm
    rw [h2, bigG, ← hz]
    ring

/-- **Soundararajan's theorem from RH.**  For `k > 0`, `ε > 0`:
`∫_T^{2T} |ζ(½ + it)|^{2k} dt ≤ C T (log T)^{k² + ε}` for large `T`. -/
theorem exists_setIntegral_norm_riemannZeta_criticalLine_rpow_le (hRH : RiemannHypothesis)
    {k : ℝ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in Ioc T (2 * T), ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ (2 * k) ≤
        C * T * Real.log T ^ (k ^ 2 + ε) := by
  set hW : WeilPositiveFull vonMangoldtReal :=
    RHTower.weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH with hWdef
  obtain ⟨hGc, hGd, hG2⟩ := two_mul_xi_producer hRH
  have hlam : ∀ n : ℕ, 2 ≤ n → |vonMangoldtReal n| ≤ 1 * Real.log n := fun n _ => by
    rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log
  obtain ⟨ε', hε', hε8, hlt⟩ := exists_eps_exponent_lt (k ^ 2) 1 hε
  simp only [one_pow, mul_one] at hlt
  obtain ⟨C, T₀, hC0, hC⟩ := exists_setIntegral_norm_phiG_rpow_le hW
    summable_restWeight_vonMangoldt zero_le_one hlam hGc hGd hG2 hk hε' hε8
  simp only [one_pow, mul_one] at hC
  set β : ℝ := k ^ 2 * (Real.exp ε' / (1 - 4 * ε') ^ 2) + ε' with hβ
  have hβ0 : 0 ≤ β := by positivity
  -- `φ_{2ξ}(τ) = ζ(½ + 2iτ)`
  have hphi : ∀ τ : ℝ, PhaseLockRigidity.phiG (fun z => 2 * xi z) τ = riemannZeta (lineS τ) := by
    intro τ
    unfold PhaseLockRigidity.phiG
    beta_reduce
    have h0 := lineS_ne_zero τ
    have h1 := lineS_ne_one τ
    rw [xi_eq_mul_Gammaℝ_mul_riemannZeta h0 h1 (by rw [lineS_re]; norm_num)]
    have hG := Gammaℝ_lineS_ne_zero τ
    have h1' : lineS τ - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
  refine ⟨max C 0 * 2 * 2 ^ β, 2 * max T₀ 3, fun T hT => ?_⟩
  have hT3 : 3 ≤ T / 2 := by
    have := (le_max_right T₀ 3); linarith
  have hT0 : 0 < T := by linarith
  have hTh : T₀ ≤ T / 2 := by have := le_max_left T₀ 3; linarith
  have h := hC (T / 2) hTh
  simp only [hphi] at h
  -- change of variables `t = 2τ`
  set f : ℝ → ℝ := fun t => ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ^ (2 * k) with hf
  have hfeq : ∀ τ : ℝ, ‖riemannZeta (lineS τ)‖ ^ (2 * k) = f (2 * τ) := by
    intro τ
    simp only [hf, lineS_eq]
    try push_cast
    try ring_nf
  simp only [hfeq] at h
  have hchange : ∫ τ in Ioc (T / 2) (2 * (T / 2)), f (2 * τ) =
      2⁻¹ * ∫ t in Ioc T (2 * T), f t := by
    rw [← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
    congr 2 <;> ring
  rw [hchange] at h
  have hlogT : 1 ≤ Real.log (T / 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith
  have hlogle : Real.log (T / 2) ≤ Real.log T := Real.log_le_log (by positivity) (by linarith)
  have hpow1 : Real.log (T / 2) ^ β ≤ Real.log T ^ β :=
    Real.rpow_le_rpow (by linarith) hlogle hβ0
  have hlogT' : 1 ≤ Real.log T := hlogT.trans hlogle
  have hpow2 : Real.log T ^ β ≤ Real.log T ^ (k ^ 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hlogT' hlt.le
  have hI : ∫ t in Ioc T (2 * T), f t ≤ 2 * (max C 0 * (T / 2) * Real.log (T / 2) ^ β) := by
    have h' : 2⁻¹ * ∫ t in Ioc T (2 * T), f t ≤ max C 0 * (T / 2) * Real.log (T / 2) ^ β :=
      h.trans (by gcongr; exact le_max_left _ _)
    linarith
  calc ∫ t in Ioc T (2 * T), f t ≤ 2 * (max C 0 * (T / 2) * Real.log (T / 2) ^ β) := hI
    _ ≤ 2 * (max C 0 * (T / 2) * Real.log T ^ (k ^ 2 + ε)) := by
        gcongr; exact hpow1.trans hpow2
    _ ≤ max C 0 * 2 * 2 ^ β * T * Real.log T ^ (k ^ 2 + ε) := by
        have h2β : (1 : ℝ) ≤ 2 ^ β := Real.one_le_rpow (by norm_num) hβ0
        have hX : 0 ≤ max C 0 * T * Real.log T ^ (k ^ 2 + ε) := by positivity
        nlinarith

end RHTower.WeilSpectral
