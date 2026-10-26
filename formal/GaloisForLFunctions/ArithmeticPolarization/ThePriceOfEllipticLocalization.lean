import Zeta23.WeilEF.Main
import GaloisForLFunctions.«arithmetic-positivity-theory».SingleHeightPhaseSelectiveApertureAndPowerSaving
import GaloisForLFunctions.ArithmeticPolarization.TwistedSectorsCollideQuartets

/-!
# The price of elliptic localization

What the elliptic localizer `σ_γ` costs on the arithmetic side. Since its sectors are twists
(`TwistedSectorsCollideQuartets`), the price is read from the explicit formula of a twisted test.

* **Twists and autocorrelations.** The twist commutes with autocorrelation,
  `(e^{−iγu} f) ⋆ (e^{−iγu} g)~ = e^{−iγx} (f ⋆ g̃)` (`weilTest_twist`), shifts the transform
  (`paperFT_twist`), and is the corpus height shift at `ξ = −γ/2π` (`twist_eq_heightShift`).
* **The twisted explicit formula** (`literatureRHS_twist`, `twisted_explicit_formula`): for every
  zero configuration with the explicit formula, the zero sum of the shifted configuration `Z − iγ`
  equals: the pole terms at the **shifted poles** (transform points `±i/2 − γ`, i.e. spectral
  points `−iγ` and `1 − iγ`), minus the prime sum with **phased weights**
  `Λ(n) n^{−1/2}(n^{−iγ} k(log n) + n^{iγ} k(−log n))`, plus the archimedean integral against the
  **shifted digamma density** `Re ψ(¼ + i(r + γ)/2) − log π`.
* **Charge** (`twisted_atoms_of_real_even`, `exists_vonMangoldt_pos_cos_neg`): on real even kernels
  the phased atoms are `2 cos(γ log n) K(log n)`, and for every `γ ≠ 0` some prime power `n` has
  `cos(γ log n) < 0`: every elliptic localizer off the real axis is gauge charged.
* **The conductor horizon** (`elliptic_sector_nonneg_below_conductor_horizon`): the shifted digamma
  density grows like `log γ` and pays the whole prime sum of a test of aperture `a` once
  `(4 + ε) e^a ≲ log γ`; below this horizon positivity of `ζ`'s form on twisted tests is a theorem,
  and it is source-blind (the bound uses only `|Λ|`). The single-height laws of
  `SingleHeightPhaseSelectiveApertureAndPowerSaving` show that the coefficient `4` cannot be
  lowered eventually in height. Localizing a pair at ordinate `γ` needs aperture `≍ log γ`, far
  beyond the horizon `a ≈ log log γ`.
-/

open Complex MeasureTheory
open scoped ComplexConjugate ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-! ### 1. Twists, transforms and autocorrelations -/

theorem paperFT_twist (γ : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    paperFT (twist γ f) z = paperFT f (z - γ) := by
  rw [paperFT, paperFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [twist]
  rw [mul_comm (Complex.exp _) (f u), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The twist is the corpus height shift at `ξ = −γ/2π`. -/
theorem twist_eq_heightShift (γ : ℝ) (f : ℝ → ℂ) :
    twist γ f = SquareRootThreshold.heightShift (-γ / (2 * Real.pi)) f := by
  funext u
  simp only [twist, SquareRootThreshold.heightShift]
  congr 2
  push_cast
  field_simp

/-- **The twist commutes with autocorrelation.** -/
theorem weilTest_twist (γ : ℝ) (f g : ℝ → ℂ) :
    EF.weilTest (twist γ f) (twist γ g) = twist γ (EF.weilTest f g) := by
  funext x
  simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', twist, EF.tilde]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_ofReal]
  have e : Complex.exp (-(γ * I * t)) * Complex.exp (-(γ * -I * ((-(x - t) : ℝ) : ℂ))) =
      Complex.exp (-(γ * I * x)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [← e]; ring

theorem contDiff_twist {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (γ : ℝ) : ContDiff ℝ 2 (twist γ f) := by
  rw [twist_eq_heightShift]; exact SquareRootThreshold.heightShift_contDiff hf _

theorem hasCompactSupport_twist {f : ℝ → ℂ} (hf : HasCompactSupport f) (γ : ℝ) :
    HasCompactSupport (twist γ f) := hf.mul_left

/-! ### 2. The twisted explicit formula -/

/-- **The twisted right-hand side.** Shifted poles, phased prime weights, shifted digamma
density. -/
theorem literatureRHS_twist (γ : ℝ) (k : ℝ → ℂ) :
    EF.literatureRHS (twist γ k) =
      paperFT k (I / 2 - γ) + paperFT k (-I / 2 - γ)
      - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
          * (Complex.exp (-(γ * I * Real.log n)) * k (Real.log n) +
              Complex.exp (γ * I * Real.log n) * k (-Real.log n))
      + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket (r + γ) : ℂ) := by
  have hsum : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (twist γ k (Real.log n) + twist γ k (-Real.log n))) =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (Complex.exp (-(γ * I * Real.log n)) * k (Real.log n) +
            Complex.exp (γ * I * Real.log n) * k (-Real.log n)) := by
    refine tsum_congr fun n => ?_
    simp only [twist, Complex.ofReal_neg]
    ring_nf
  have hint : (∫ r : ℝ, paperFT (twist γ k) r * (EF.gammaBracket r : ℂ)) =
      ∫ r : ℝ, paperFT k r * (EF.gammaBracket (r + γ) : ℂ) := by
    rw [← integral_add_right_eq_self (fun r : ℝ => paperFT (twist γ k) r *
      (EF.gammaBracket r : ℂ)) γ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [paperFT_twist]
    push_cast
    ring_nf
  rw [EF.literatureRHS, paperFT_twist, paperFT_twist, hsum, hint]

/-- **The twisted explicit formula.** For a configuration with the explicit formula, the zero sum
of the shifted configuration `Z − iγ` is the twisted right-hand side: the explicit formula of the
archimedean twist, with its shifted poles, phased primes and shifted Gamma factor. -/
theorem twisted_explicit_formula {Z : Zeta23.ZeroConfig} (hZ : EF.EF_lit Z) (γ : ℝ)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun z : (shiftConfig Z γ).carrier => ((shiftConfig Z γ).mult z : ℂ) * tr k z) ∧
    ∑' z : (shiftConfig Z γ).carrier, ((shiftConfig Z γ).mult z : ℂ) * tr k z =
      EF.literatureRHS (twist γ k) := by
  obtain ⟨hs, he⟩ := hZ (twist γ k) (contDiff_twist hk γ) (hasCompactSupport_twist hkc γ)
  have hterm : ∀ ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (twist γ k) (gammaOf ρ) =
      ((shiftConfig Z γ).mult (shiftEquiv Z γ ρ) : ℂ) * tr k (shiftEquiv Z γ ρ) := by
    intro ρ
    change _ = ((Z.mult (ρ.1 - γ * I + γ * I)) : ℂ) * tr k (ρ.1 - γ * I)
    rw [sub_add_cancel, ← tr, tr_twist]
  refine ⟨?_, ?_⟩
  · rw [← (shiftEquiv Z γ).summable_iff]
    exact hs.congr hterm
  · rw [← (shiftEquiv Z γ).tsum_eq, ← he]
    exact (tsum_congr hterm).symm

/-! ### 3. The charge of a twist -/

/-- **Phased atoms of a real even kernel**: `n^{−iγ} K(log n) + n^{iγ} K(−log n) = 2 cos(γ log n) K(log n)`. -/
theorem twisted_atoms_of_real_even {K : ℝ → ℝ} (hK : ∀ t, K (-t) = K t) (γ t : ℝ) :
    Complex.exp (-(γ * I * t)) * (K t : ℂ) + Complex.exp (γ * I * t) * (K (-t) : ℂ) =
      ((2 * Real.cos (γ * t) * K t : ℝ) : ℂ) := by
  rw [hK]
  have e1 : Complex.exp (-(γ * I * t)) = Complex.exp (-((γ * t : ℝ) * I)) := by
    congr 1; push_cast; ring
  have e2 : Complex.exp (γ * I * t) = Complex.exp ((γ * t : ℝ) * I) := by
    congr 1; push_cast; ring
  have h1 : Complex.exp (-(γ * I * t)) + Complex.exp (γ * I * t) = 2 * (Real.cos (γ * t) : ℂ) := by
    rw [e1, e2, Complex.ofReal_cos, Complex.cos]; ring_nf
  have h2 : ((2 * Real.cos (γ * t) * K t : ℝ) : ℂ) = 2 * (Real.cos (γ * t) : ℂ) * (K t : ℂ) := by
    norm_cast
  rw [h2]
  linear_combination (K t : ℂ) * h1

/-- The first nonnegative multiple of an angle off `2πℤ` with negative cosine. -/
theorem exists_cos_nsmul_neg {θ : ℝ} (hθ : ∀ m : ℤ, θ ≠ 2 * Real.pi * m) :
    ∃ k : ℕ, 1 ≤ k ∧ Real.cos (k * θ) < 0 := by
  -- reduce `θ` to `θ' ∈ (−π, π]`, `θ' ≠ 0`
  set θ' := toIocMod Real.two_pi_pos (-Real.pi) θ with hθ'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, θ = θ' + m * (2 * Real.pi) :=
    ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, by
      rw [hθ', toIocMod]; simp⟩
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) θ
  rw [← hθ'] at hmem
  have hpi := Real.pi_pos
  have hlo : -Real.pi < θ' := hmem.1
  have hhi : θ' ≤ Real.pi := by linarith [hmem.2]
  have hne : θ' ≠ 0 := by
    intro h0; apply hθ m; rw [hm, h0]; ring
  have habs : 0 < |θ'| := abs_pos.mpr hne
  have habs' : |θ'| ≤ Real.pi := abs_le.mpr ⟨by linarith, hhi⟩
  set k : ℕ := ⌊Real.pi / 2 / |θ'|⌋₊ + 1
  have hk1 : 1 ≤ k := Nat.le_add_left 1 _
  have hfl := Nat.lt_floor_add_one (Real.pi / 2 / |θ'|)
  have hfl' := Nat.floor_le (div_nonneg (by positivity) habs.le : 0 ≤ Real.pi / 2 / |θ'|)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hlow : Real.pi / 2 < k * |θ'| := by
    have : Real.pi / 2 / |θ'| < k := by push_cast [k]; exact hfl
    rwa [div_lt_iff₀ habs] at this
  have hup : (k : ℝ) * |θ'| ≤ Real.pi / 2 + |θ'| := by
    have : ((k : ℝ) - 1) * |θ'| ≤ Real.pi / 2 := by
      have h2 : (k : ℝ) - 1 = ⌊Real.pi / 2 / |θ'|⌋₊ := by push_cast [k]; ring
      rw [h2]; rwa [le_div_iff₀ habs] at hfl'
    linarith
  have hstrict : (k : ℝ) * |θ'| < 3 * Real.pi / 2 := by
    rcases lt_or_eq_of_le habs' with hlt | heq
    · linarith
    · -- `|θ'| = π`: then `k = 1` and `k|θ'| = π`
      have hk : k = 1 := by
        have : Real.pi / 2 / |θ'| = 1 / 2 := by rw [heq]; field_simp
        simp only [k, this]
        norm_num
      rw [hk, heq]; push_cast; linarith
  refine ⟨k, hk1, ?_⟩
  have hcos : Real.cos (k * θ) = Real.cos (k * |θ'|) := by
    rw [hm, mul_add, show (k : ℝ) * (m * (2 * Real.pi)) = ((k * m : ℤ) : ℝ) * (2 * Real.pi) by
      push_cast; ring, Real.cos_add_int_mul_two_pi]
    rcases abs_choice θ' with h | h <;> rw [h]
    · rw [mul_neg, Real.cos_neg]
  rw [hcos]
  apply Real.cos_neg_of_pi_div_two_lt_of_lt hlow
  linarith

/-- `2^b ≠ 3^a` for positive exponents: `log 3 / log 2` is irrational. -/
theorem two_pow_ne_three_pow {a b : ℕ} (ha : 1 ≤ a) : (2 : ℝ) ^ b ≠ 3 ^ a := by
  intro h
  have h' : (2 : ℕ) ^ b = 3 ^ a := by exact_mod_cast h
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h'
    have : 3 ≤ 3 ^ a := Nat.le_self_pow (by omega) 3
    omega
  have h2 : 2 ∣ 3 ^ a := h' ▸ dvd_pow_self 2 hb
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
  omega

/-- **Every elliptic localizer off the real axis is gauge charged.** For `γ ≠ 0` some prime power
`n` (a power of `2` or of `3`) has `Λ(n) > 0` and `cos(γ log n) < 0`. -/
theorem exists_vonMangoldt_pos_cos_neg {γ : ℝ} (hγ : γ ≠ 0) :
    ∃ n : ℕ, 0 < ArithmeticFunction.vonMangoldt n ∧ Real.cos (γ * Real.log n) < 0 := by
  have hpp : ∀ (p k : ℕ), p.Prime → 1 ≤ k →
      ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p ∧ 0 < Real.log p := by
    intro p k hp hk
    refine ⟨ArithmeticFunction.vonMangoldt_apply_pow (by omega) |>.trans
      (ArithmeticFunction.vonMangoldt_apply_prime hp), Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  have hlog : ∀ (p k : ℕ), Real.log ((p ^ k : ℕ) : ℝ) = k * Real.log p := by
    intro p k; push_cast; exact Real.log_pow (p : ℝ) k
  by_cases h2 : ∀ m : ℤ, γ * Real.log 2 ≠ 2 * Real.pi * m
  · obtain ⟨k, hk, hc⟩ := exists_cos_nsmul_neg h2
    obtain ⟨hv, hl⟩ := hpp 2 k Nat.prime_two hk
    refine ⟨2 ^ k, hv ▸ hl, ?_⟩
    rw [hlog]; push_cast; rwa [show γ * (k * Real.log 2) = k * (γ * Real.log 2) by ring]
  · simp only [not_forall, not_not] at h2
    obtain ⟨m, hm⟩ := h2
    have h3 : ∀ m' : ℤ, γ * Real.log 3 ≠ 2 * Real.pi * m' := by
      intro m' hm'
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hm0 : m ≠ 0 := by
        rintro rfl; simp at hm; rcases hm with h | h
        · exact hγ h
        · linarith
      -- `m' log 2 = m log 3`, so `2^{|m'|} = 3^{|m|}`
      have hrel : (m' : ℝ) * Real.log 2 = m * Real.log 3 := by
        have : γ * Real.log 2 * Real.log 3 = γ * Real.log 3 * Real.log 2 := by ring
        rw [hm, hm'] at this
        have hpi : (2 * Real.pi) ≠ 0 := by positivity
        have := mul_left_cancel₀ hpi (by linarith : 2 * Real.pi * (m * Real.log 3) =
          2 * Real.pi * (m' * Real.log 2))
        linarith
      have hsgn : (0 < m ∧ 0 < m') ∨ (m < 0 ∧ m' < 0) := by
        rcases lt_or_gt_of_ne hm0 with hneg | hpos
        · right; refine ⟨hneg, ?_⟩
          have : (m : ℝ) * Real.log 3 < 0 :=
            mul_neg_of_neg_of_pos (by exact_mod_cast hneg) hl3
          have : (m' : ℝ) < 0 := by nlinarith
          exact_mod_cast this
        · left; refine ⟨hpos, ?_⟩
          have : 0 < (m : ℝ) * Real.log 3 := mul_pos (by exact_mod_cast hpos) hl3
          have : (0 : ℝ) < m' := by nlinarith
          exact_mod_cast this
      have habs : ((m'.natAbs : ℕ) : ℝ) * Real.log 2 = ((m.natAbs : ℕ) : ℝ) * Real.log 3 := by
        rcases hsgn with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
        · rw [Nat.cast_natAbs, Nat.cast_natAbs, abs_of_pos (by exact_mod_cast h1'),
            abs_of_pos (by exact_mod_cast h1)]
          linarith
        · rw [Nat.cast_natAbs, Nat.cast_natAbs, abs_of_neg (by exact_mod_cast h1'),
            abs_of_neg (by exact_mod_cast h1)]
          push_cast; linarith
      have hpow : (2 : ℝ) ^ m'.natAbs = 3 ^ m.natAbs := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ m'.natAbs),
          ← Real.exp_log (by positivity : (0 : ℝ) < 3 ^ m.natAbs), Real.log_pow, Real.log_pow,
          habs]
      exact two_pow_ne_three_pow (Int.natAbs_pos.mpr hm0) hpow
    obtain ⟨k, hk, hc⟩ := exists_cos_nsmul_neg h3
    obtain ⟨hv, hl⟩ := hpp 3 k Nat.prime_three hk
    refine ⟨3 ^ k, hv ▸ hl, ?_⟩
    rw [hlog]; push_cast; rwa [show γ * (k * Real.log 3) = k * (γ * Real.log 3) by ring]

/-! ### 4. The conductor horizon -/

/-- **Below the conductor horizon the twisted form of `ζ` is positive.** For every `ε > 0` there is
`C` such that `Re W_ζ(e^{−iγu} f, e^{−iγu} f) ≥ 0` for every `C²` test `f` of aperture `a` once
`C + (4 + ε) e^a + 2 ≤ log(1 + |γ|/8)` and the two high-height tail terms are below `‖f‖₂²`. -/
theorem elliptic_sector_nonneg_below_conductor_horizon {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 0 ≤ a → ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f →
      tsupport f ⊆ Set.Icc (-a) a → ∀ γ : ℝ,
        C + (4 + ε) * Real.exp a + 2 ≤ Real.log (1 + |γ| / 8) →
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + |γ| / 2)) ≤
          ∫ t, ‖f t‖ ^ 2 →
        2 * Real.exp a * (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (1 + |γ|) ^ 4 ≤
          ∫ t, ‖f t‖ ^ 2 →
        0 ≤ (zetaZeroConfig.W (twist γ f) (twist γ f)).re := by
  obtain ⟨C, hC0, hC⟩ :=
    ArithmeticPositivityTheory.zetaZeroConfig_re_W_heightShift_nonneg_of_sharp_horizon hε
  refine ⟨C, hC0, fun {a} ha {f} hf hfs γ hlog htail hpole => ?_⟩
  have hξ : Real.pi * |(-γ / (2 * Real.pi))| = |γ| / 2 := by
    rw [abs_div, abs_neg, abs_of_pos Real.two_pi_pos]; field_simp
  rw [twist_eq_heightShift]
  refine hC ha hf hfs _ ?_ ?_ ?_
  · rwa [show Real.pi * |(-γ / (2 * Real.pi))| / 4 = |γ| / 8 by rw [hξ]; ring]
  · rwa [hξ]
  · rwa [show 2 * Real.pi * |(-γ / (2 * Real.pi))| = |γ| by rw [mul_assoc, hξ]; ring]

end GaloisForLFunctions.ArithmeticPolarization
