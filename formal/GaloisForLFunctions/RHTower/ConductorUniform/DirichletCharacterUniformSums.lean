import GaloisForLFunctions.RHTower.ConductorUniform.DirichletCharacterUniformPowerLog
import GaloisForLFunctions.RHTower.PrimeProgressionPowerLog
import GaloisForLFunctions.RHTower.PrimePowerSumBound
import GaloisForLFunctions.RHTower.ZetaZeroDensityExponentLemmas

/-!
# Actual character sums with a growing conductor range

Signed unsmoothing preserves a common rate for all moduli bounded by a power
of the logarithm. Its short-interval defect is paid by the ordinary positive
von Mangoldt mass. Removing proper prime powers preserves the uniformity.
-/

noncomputable section

set_option autoImplicit false

namespace RHTower

open ArithmeticFunction
open _root_.Complex

/-- One common power-log rate controls the actual unsmoothed nonprincipal
character sums throughout a growing conductor family. -/
theorem exists_conductor_uniform_characterPsi_power_log {A : ℝ} (hA : 0 ≤ A) :
    ∃ rho C x₀ : ℝ, 0 < rho ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterChebyshevPsi χ ⌊x⌋₊‖ ≤
            C * x * Real.exp (-(rho * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨κ, C, X, hκ, hC, hX3, htent⟩ := exists_conductor_uniform_character_tent_power_log hA
  obtain ⟨κψ, Cψ, Xψ, hκψ, hCψ, hXψ3, hpsi⟩ := exists_chebyshevPsi_power_log
  let rho := min (κ / 2) κψ
  have hrho : 0 < rho := lt_min (by positivity) hκψ
  have hrhoκ : rho ≤ κ / 2 := min_le_left _ _
  have hrhoψ : rho ≤ κψ := min_le_right _ _
  refine ⟨rho, 6 * C + 1 + 3 * Cψ, max X Xψ, hrho, by positivity,
    hX3.trans (le_max_left _ _), fun x hx q _ hq χ hχ => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxXψ : Xψ ≤ x := (le_max_right _ _).trans hx
  have hx3 : 3 ≤ x := hX3.trans hxX
  have hx0 : 0 < x := by linarith only [hx3]
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith only [hx3])
  let u := Real.log x ^ ((1 : ℝ) / 10)
  let ε := Real.exp (-(rho * u))
  let y := (1 + ε) * x
  let h := Real.log (1 + ε)
  have hu : 0 < u := Real.rpow_pos_of_pos hlogx _
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hrho.le hu.le))
  have hxy : x ≤ y := by dsimp only [y]; nlinarith only [hε, hx0]
  have hy0 : 0 < y := hx0.trans_le hxy
  have hy2 : y ≤ 2 * x := by dsimp only [y]; nlinarith only [hε1, hx0]
  have hlogy : u ≤ Real.log y ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow hlogx.le (Real.log_le_log hx0 hxy) (by positivity)
  have hhyx : Real.log (y / x) = h := by
    dsimp only [y, h]
    congr 1
    field_simp
  have hhε : ε / 2 ≤ h := by
    calc
      ε / 2 = 2 * ε / 4 := by ring
      _ ≤ 2 * ε / (ε + 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hε1])
      _ ≤ h := Real.le_log_one_add_of_nonneg hε.le
  have hh : 0 < h := (div_pos hε (by norm_num)).trans_le hhε
  have hdecay (b : ℝ) (hb : 0 ≤ b) :
      Real.exp (-(b * Real.log y ^ ((1 : ℝ) / 10))) ≤ Real.exp (-(b * u)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hlogy hb))
  have ht (z : ℝ) (hz : X ≤ z) (hxz : x ≤ z) : ‖characterPerronTentSum χ z‖ ≤
      C * z * Real.exp (-(κ * Real.log z ^ ((1 : ℝ) / 10))) := by
    have hqz : (q : ℝ) ≤ Real.log z ^ A := hq.trans
      (Real.rpow_le_rpow hlogx.le (Real.log_le_log hx0 hxz) hA)
    simpa only [characterPerronTentSum, Complex.ofReal_mul, mul_assoc] using htent z hz q hqz χ hχ
  have htx : ‖characterPerronTentSum χ x‖ ≤ C * x * Real.exp (-(κ * u)) := ht x hxX le_rfl
  have hty : ‖characterPerronTentSum χ y‖ ≤ 2 * C * x * Real.exp (-(κ * u)) := by
    apply (ht y (hxX.trans hxy) hxy).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hy2 hC) (hdecay κ hκ.le)
      (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
  have hdef := norm_characterPerron_unsmoothing_defect χ hx0 hxy
  rw [hhyx] at hdef
  let P := characterChebyshevPsi χ ⌊x⌋₊
  let S := characterPerronTentSum χ y - characterPerronTentSum χ x
  have htriangle : h * ‖P‖ ≤ ‖characterPerronTentSum χ y‖ + ‖characterPerronTentSum χ x‖ +
      ‖S - (h : ℂ) * P‖ := by
    calc
      h * ‖P‖ = ‖(h : ℂ) * P‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      _ = ‖S - (S - (h : ℂ) * P)‖ := by congr 1; ring
      _ ≤ ‖S‖ + ‖S - (h : ℂ) * P‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add
        (norm_sub_le (characterPerronTentSum χ y) (characterPerronTentSum χ x)) le_rfl
  have hw : h * ‖P‖ ≤ 3 * C * x * Real.exp (-(κ * u)) +
      h * (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊) := by
    change ‖S - (h : ℂ) * P‖ ≤ h * (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊) at hdef
    linarith only [htriangle, htx, hty, hdef]
  have hrecover : ‖P‖ ≤ (3 * C * x * Real.exp (-(κ * u))) / h +
      (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊) := by
    calc
      ‖P‖ = (h * ‖P‖) / h := by field_simp
      _ ≤ (3 * C * x * Real.exp (-(κ * u)) + h *
          (chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊)) / h := div_le_div_of_nonneg_right hw hh.le
      _ = _ := by field_simp
  have hfast : Real.exp (-(κ * u)) ≤ ε ^ (2 : ℕ) := by
    dsimp only [ε]
    rw [pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hκrho : 2 * rho ≤ κ := by linarith only [hrhoκ]
    have hm := mul_le_mul_of_nonneg_right hκrho hu.le
    linarith only [hm]
  have hrate : (3 * C * x * Real.exp (-(κ * u))) / h ≤ 6 * C * x * ε := by
    calc
      _ ≤ (3 * C * x * ε ^ (2 : ℕ)) / h :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfast (by positivity)) hh.le
      _ ≤ (3 * C * x * ε ^ (2 : ℕ)) / (ε / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hhε
      _ = _ := by field_simp; ring
  have hslow : Real.exp (-(κψ * u)) ≤ ε :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hrhoψ hu.le))
  have hpx : |chebyshevPsi ⌊x⌋₊ - x| ≤ Cψ * x * ε :=
    (hpsi x hxXψ).trans (mul_le_mul_of_nonneg_left hslow (by positivity))
  have hpy : |chebyshevPsi ⌊y⌋₊ - y| ≤ 2 * Cψ * x * ε := by
    apply (hpsi y (hxXψ.trans hxy)).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hy2 hCψ) ((hdecay κψ hκψ.le).trans hslow)
      (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
  have hshort : chebyshevPsi ⌊y⌋₊ - chebyshevPsi ⌊x⌋₊ ≤ (1 + 3 * Cψ) * x * ε := by
    have hupper := (abs_le.mp hpy).2
    have hlower := (abs_le.mp hpx).1
    have hgap : y - x = x * ε := by dsimp only [y]; ring
    linarith only [hupper, hlower, hgap]
  change ‖P‖ ≤ (6 * C + 1 + 3 * Cψ) * x * ε
  linarith only [hrecover, hrate, hshort]

/-- Proper prime powers have a scalar bound independent of the character and
modulus, so the same growing family has uniform prime cancellation. -/
theorem exists_conductor_uniform_characterTheta_power_log {A : ℝ} (hA : 0 ≤ A) :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterChebyshevTheta χ x‖ ≤
            C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, C, X, hc, hC, hX, hpsi⟩ := exists_conductor_uniform_characterPsi_power_log hA
  obtain ⟨Y, hY, hdecay⟩ := sqrt_log_le_power_log_decay hc
  refine ⟨c, C + 1, max X Y, hc, by positivity, hX.trans (le_max_left _ _), fun x hx q _ hq χ hχ => ?_⟩
  have hxX := (le_max_left X Y).trans hx
  have hxY := (le_max_right X Y).trans hx
  have hx1 : 1 ≤ x := by linarith only [hX, hxX]
  have hdef := (norm_characterChebyshevPsi_sub_theta χ x).trans
    ((Chebyshev.psi_sub_theta_le hx1).trans (hdecay x hxY))
  have htri := norm_sub_norm_le (characterChebyshevTheta χ x) (characterChebyshevPsi χ ⌊x⌋₊)
  rw [norm_sub_rev] at htri
  have hp := hpsi x hxX q hq χ hχ
  linarith only [hdef, htri, hp]


#print axioms exists_conductor_uniform_characterPsi_power_log
#print axioms exists_conductor_uniform_characterTheta_power_log

/-- Every fixed real power of the logarithm is absorbed by the physical
power-log error beyond a common scalar horizon. -/
theorem exists_log_rpow_le_power_log_decay (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ X : ℝ, 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      Real.log x ^ A ≤ x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨k : ℕ, hk⟩ := exists_nat_ge A
  obtain ⟨Y, hY, hproper⟩ := sqrt_log_le_power_log_decay hc
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 3 ≤ x ∧
      Real.log x ^ A ≤ x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
    filter_upwards [eventually_const_mul_polylog_le_rpow k
      (c := (1 : ℝ) / 2) (by norm_num) 1,
      Filter.eventually_ge_atTop Y, Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with x hpoly hx hlog
    have hlog0 : 0 ≤ Real.log x := zero_le_one.trans hlog
    refine ⟨hY.trans hx, ?_⟩
    calc
      _ ≤ Real.log x ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hlog hk
      _ = Real.log x ^ k := Real.rpow_natCast _ _
      _ ≤ (1 + Real.log x) ^ k := pow_le_pow_left₀ hlog0 (by linarith) k
      _ ≤ Real.sqrt x := by simpa only [one_mul, Real.sqrt_eq_rpow] using hpoly
      _ ≤ 2 * Real.sqrt x * Real.log x := by
        have hm := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
        nlinarith only [hm, Real.sqrt_nonneg x]
      _ ≤ _ := hproper x hx
  obtain ⟨X, hX⟩ := hev.exists_forall_of_atTop
  exact ⟨max 3 X, le_max_left _ _, fun x hx =>
    (hX x ((le_max_right _ _).trans hx)).2⟩

/-- Prime divisors of every allowed modulus have one common physical error
bound; this pays the principal-character and nonunit-class corrections. -/
theorem exists_conductor_theta_power_log (A : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ C X : ℝ, 0 < C ∧ 3 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
        Chebyshev.theta q ≤ C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨C, hC, htheta⟩ := exists_chebyshevTheta_le_linear
  obtain ⟨X, hX, hpoly⟩ := exists_log_rpow_le_power_log_decay A hc
  refine ⟨C, X, hC, hX, ?_⟩
  intro x hx q _ hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  calc
    _ ≤ C * q := htheta q hq1
    _ ≤ C * Real.log x ^ A := mul_le_mul_of_nonneg_left hq hC.le
    _ ≤ C * (x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10)))) :=
      mul_le_mul_of_nonneg_left (hpoly x hx) hC.le
    _ = _ := by ring

/-- Principal and nonprincipal characters share one actual prime main-term
estimate throughout a growing conductor family. -/
theorem exists_conductor_uniform_characterTheta_main_power_log {A : ℝ} (hA : 0 ≤ A) :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
        ∀ χ : DirichletCharacter ℂ q,
          ‖characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
            C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  classical
  obtain ⟨c₁, C₁, X₁, hc₁, hC₁, hX₁, hnonprincipal⟩ :=
    exists_conductor_uniform_characterTheta_power_log hA
  obtain ⟨c₂, C₂, X₂, hc₂, hC₂, hX₂, hscalar⟩ := exists_chebyshev_theta_power_log
  let c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  obtain ⟨D, Y, hD, hY, hmodulus⟩ := exists_conductor_theta_power_log A hc
  refine ⟨c, C₁ + C₂ + D, max X₁ (max X₂ Y), hc, by positivity,
    hX₁.trans (le_max_left _ _), ?_⟩
  intro x hx q _ hq χ
  have hx₁ := (le_max_left X₁ (max X₂ Y)).trans hx
  have hx₂ := (le_max_left X₂ Y).trans ((le_max_right X₁ _).trans hx)
  have hxY := (le_max_right X₂ Y).trans ((le_max_right X₁ _).trans hx)
  have hx3 : 3 ≤ x := hX₁.trans hx₁
  have hx0 : 0 ≤ x := by linarith only [hx3]
  have hu : 0 ≤ Real.log x ^ ((1 : ℝ) / 10) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith only [hx3])) _
  let R := x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10)))
  have hR : 0 ≤ R := mul_nonneg hx0 (Real.exp_nonneg _)
  have hscale (b C : ℝ) (hb : c ≤ b) (hC : 0 ≤ C) :
      C * x * Real.exp (-(b * Real.log x ^ ((1 : ℝ) / 10))) ≤ C * R := by
    have hdecay := Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_right hb hu))
    simpa only [R, mul_assoc] using
      mul_le_mul_of_nonneg_left hdecay (mul_nonneg hC hx0)
  by_cases hχ : χ = 1
  · subst χ
    simp only [↓reduceIte]
    have hprime :
        ‖characterChebyshevTheta (1 : DirichletCharacter ℂ q) x - (Chebyshev.theta x : ℂ)‖ ≤
          D * R := by
      simpa only [R, mul_assoc] using
        (norm_characterChebyshevTheta_principal_sub_theta (Q := q) x).trans
          (hmodulus x hxY q hq)
    have hs := (hscalar x hx₂).trans (hscale c₂ C₂ (min_le_right _ _) hC₂)
    have htri := norm_add_le
      (characterChebyshevTheta (1 : DirichletCharacter ℂ q) x - (Chebyshev.theta x : ℂ))
      ((Chebyshev.theta x : ℂ) - (x : ℂ))
    rw [sub_add_sub_cancel, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htri
    have hC₁R := mul_nonneg hC₁ hR
    have hfinal : ‖characterChebyshevTheta (1 : DirichletCharacter ℂ q) x - (x : ℂ)‖ ≤
        (C₁ + C₂ + D) * R := by
      nlinarith only [hprime, hs, htri, hC₁R]
    simpa only [R, mul_assoc] using hfinal
  · simp only [hχ, ↓reduceIte, sub_zero]
    have hs := (hnonprincipal x hx₁ q hq χ hχ).trans
      (hscale c₁ C₁ (min_le_left _ _) hC₁)
    have hmore := mul_le_mul_of_nonneg_right
      (show C₁ ≤ C₁ + C₂ + D by linarith only [hC₂, hD]) hR
    exact hs.trans (by simpa only [R, mul_assoc] using hmore)

#print axioms exists_conductor_theta_power_log
#print axioms exists_conductor_uniform_characterTheta_main_power_log

/-- Finite-character recovery preserves the common rate on all reduced classes
of every allowed modulus; the character count cancels the totient normalization. -/
theorem exists_conductor_uniform_primeProgressionTheta_power_log {A : ℝ} (hA : 0 ≤ A) :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ X ∧
      ∀ x : ℝ, X ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
        ∀ a : ZMod q, IsUnit a →
          |primeProgressionTheta q a x - x / q.totient| ≤
            C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  classical
  obtain ⟨c, C, X, hc, hC, hX, hb⟩ := exists_conductor_uniform_characterTheta_main_power_log hA
  refine ⟨c, C, X, hc, hC, hX, ?_⟩
  intro x hx q _ hq a ha
  have hmain : (∑ χ : DirichletCharacter ℂ q,
      χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0)) = (x : ℂ) := by
    have hunit : (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := by
      obtain ⟨u, rfl⟩ := ha
      simp
    simp [mul_ite, hunit]
  have hidentity : ((primeProgressionTheta q a x - x / q.totient : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * (characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
      primeProgressionTheta_eq_character_sum ha]
    simp only [mul_sub, Finset.sum_sub_distrib, hmain]
    ring
  have hterm (χ : DirichletCharacter ℂ q) :
      ‖χ a⁻¹ * (characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0))‖ ≤
        C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hb x hx q hq χ)
  calc
    _ = ‖((primeProgressionTheta q a x - x / q.totient : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(q.totient : ℂ)⁻¹‖ * ‖∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹ * (characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0))‖ := by
      rw [hidentity, norm_mul]
    _ ≤ ‖(q.totient : ℂ)⁻¹‖ * ∑ χ : DirichletCharacter ℂ q,
        (C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10)))) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun χ _ => hterm χ)) (norm_nonneg _)
    _ = C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have htot : (q.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
        norm_inv, Complex.norm_natCast]
      rw [← mul_assoc, inv_mul_cancel₀ htot, one_mul]

#print axioms exists_conductor_uniform_primeProgressionTheta_power_log

end RHTower
