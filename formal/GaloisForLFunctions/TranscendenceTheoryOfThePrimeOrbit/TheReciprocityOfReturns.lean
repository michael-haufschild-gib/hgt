import Zeta23.Final
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.SurvivalAtADeepReturn

/-!
# The reciprocity of returns

Weil's explicit formula is Poisson summation for the primes. Modulating a test `φ ∈ C²_c(0, ∞)` by
`e^{−itu}` turns it into an exact identity at height `t` (`orbit_reciprocity`):

`P_φ(t) = Σ_n Λ(n) n^{−½−it} φ(log n) = π_φ(t) + Γ_φ(t) − Z_φ(t)`,

with the pole term `π_φ(t) = φ̂(i/2 − t) + φ̂(−i/2 − t)`, the Gamma term
`Γ_φ(t) = ∫ φ̂(τ − t) μ(τ) dτ` and the zero side `Z_φ(t) = Σ_ρ m_ρ φ̂(γ_ρ − t)`,
`φ̂(z) = ∫ φ(u) e^{izu} du`, `γ_ρ = (ρ − ½)/i`. The left side is the orbit polynomial of the primes
at height `t`; the right side involves the zeros through `φ̂(γ_ρ − t)` only. Reciprocity exchanges the
orbit at height `t` with the zeros near height `t`; it does not move heights.

* **Localization** (`norm_paperFT_sub_le`). For `φ` supported in `[−a, a]`, a zero of depth
  `|Re ρ − ½|` at ordinate `γ` contributes at most `e^{a|Re ρ − ½|}·C_φ/(1 + |γ − t|)²`: with
  `a = log y`, a zero of depth `h` weighs `y^h`, and a finite layer leaves a footprint `O(t^{−2})` on
  the orbit at height `t` (`tendsto_finiteLayer_footprint`). The pole term decays like `t^{−2}`
  (`norm_poleTerm_le`) and the Gamma term grows like `log t` (`exists_norm_gammaTerm_le`).
* **Pole imitation** (`norm_zeroSide_add_orbitPoly_zero_le`). At a `δ`-return `t` of the primes
  `≤ e^a`, `‖Z_φ(t) + P_φ(0)‖ ≤ ‖π_φ(t)‖ + ‖Γ_φ(t)‖ + 2πδ(a/log 2)M_φ`, `M_φ = Σ Λ(n)n^{−½}|φ(log n)|`.
  The orbit at `t = 0` carries the pole, `P_φ(0) ≈ ∫ φ(u)e^{u/2}du ≍ √y`; a return copies it to
  height `t`, and reciprocity says the zeros near `t` must reproduce it.

So a heavy return of length `y` at height `t` is a configuration of zeros near `t` that imitates the
pole: `Σ_ρ y^{|Re ρ−½|}/(1 + |γ_ρ − t|)² ≫ √y/C_φ` up to `log t`. Under RH each zero weighs `O(1)` and
a unit window holds `O(log t)` zeros, which gives `log t ≫ √y/C_φ`; unconditionally a return asks
for zeros of depth near `½` or for clusters near `t`. The main conjecture B97 is the statement that
no zero configuration below height `exp(y^c)` imitates the pole at length `y`.
-/

open Complex MeasureTheory Real Finset
open scoped Real

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open Zeta23
open PrimeTorusTheory (dist01)

/-! ## The modulated test -/

/-- The test `φ` modulated to height `t`: `u ↦ φ(u) e^{−itu}`. -/
def modTest (φ : ℝ → ℂ) (t : ℝ) : ℝ → ℂ := fun u => φ u * Complex.exp (-((t * u : ℝ) : ℂ) * I)

theorem paperFT_modTest (φ : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    paperFT (modTest φ t) z = paperFT φ (z - t) := by
  unfold paperFT modTest
  congr 1; funext u
  rw [mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

theorem contDiff_modTest {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (t : ℝ) : ContDiff ℝ 2 (modTest φ t) := by
  unfold modTest
  refine hφ.mul (Complex.contDiff_exp.comp ?_)
  refine ContDiff.mul ?_ contDiff_const
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).neg

theorem hasCompactSupport_modTest {φ : ℝ → ℂ} (hφc : HasCompactSupport φ) (t : ℝ) :
    HasCompactSupport (modTest φ t) := hφc.mul_right

/-! ## The four terms of the reciprocity -/

/-- The orbit polynomial `P_φ(t) = Σ_n Λ(n) n^{−½−it} φ(log n)`. -/
def orbitPoly (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * φ (Real.log n) *
    Complex.exp (-((t * Real.log n : ℝ) : ℂ) * I)

/-- The pole term `φ̂(i/2 − t) + φ̂(−i/2 − t)`. -/
def poleTerm (φ : ℝ → ℂ) (t : ℝ) : ℂ := paperFT φ (I / 2 - t) + paperFT φ (-I / 2 - t)

/-- The Gamma term `∫ φ̂(τ − t) μ(τ) dτ`. -/
def gammaTerm (φ : ℝ → ℂ) (t : ℝ) : ℂ := ∫ τ : ℝ, paperFT φ ((τ : ℂ) - t) * (mu τ : ℂ)

/-- The zero side `Σ_ρ m_ρ φ̂(γ_ρ − t)`. -/
def zeroSide (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT φ (gammaOf ρ - t)

/-- **The reciprocity of returns.** For `φ ∈ C²_c` vanishing on `(−∞, 0]`,
`P_φ(t) = π_φ(t) + Γ_φ(t) − Z_φ(t)` at every height `t`. -/
theorem orbit_reciprocity {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ u ≤ 0, φ u = 0) (t : ℝ) :
    orbitPoly φ t = poleTerm φ t + gammaTerm φ t - zeroSide φ t := by
  have hEF := (WeilEF.EF_lit_zetaZeroConfig (modTest φ t) (contDiff_modTest hφ t)
    (hasCompactSupport_modTest hφc t)).2
  rw [EF.literatureRHS, EF.gamma_term] at hEF
  simp only [paperFT_modTest] at hEF
  have hprime : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (modTest φ t (Real.log n) + modTest φ t (-Real.log n))) = orbitPoly φ t := by
    unfold orbitPoly
    refine tsum_congr fun n => ?_
    have h0 : modTest φ t (-Real.log n) = 0 := by
      unfold modTest; rw [hφ0 _ (neg_nonpos.mpr (Real.log_natCast_nonneg n)), zero_mul]
    rw [h0, add_zero, modTest, mul_assoc]
  rw [hprime] at hEF
  unfold zeroSide poleTerm gammaTerm
  rw [hEF]
  ring

/-! ## Localization -/

/-- The `C²` size `4(‖φ‖₁ + ‖φ″‖₁)` of the decay bound. -/
def decayMass (φ : ℝ → ℂ) : ℝ := 4 * ((∫ u, ‖φ u‖) + ∫ u, ‖deriv (deriv φ) u‖)

theorem decayMass_nonneg (φ : ℝ → ℂ) : 0 ≤ decayMass φ := by
  unfold decayMass
  have h1 : 0 ≤ ∫ u, ‖φ u‖ := integral_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ ∫ u, ‖deriv (deriv φ) u‖ := integral_nonneg fun _ => norm_nonneg _
  positivity

/-- **Localization of the transform.** `‖φ̂(z − t)‖ ≤ e^{a|Im z|} C_φ/(1 + |Re z − t|)²`. -/
theorem norm_paperFT_sub_le {φ : ℝ → ℂ} {a : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) (z : ℂ) (t : ℝ) :
    ‖paperFT φ (z - t)‖ ≤ Real.exp (|z.im| * a) * decayMass φ / (1 + |z.re - t|) ^ 2 := by
  have h := RHTower.norm_paperFT_le_decay hφ hsupp (z - t)
  simpa [decayMass, Complex.sub_re, Complex.sub_im, mul_div_assoc] using h

/-- The weight of a zero: depth `|Re ρ − ½|` and ordinate `Im ρ` enter as
`e^{a|Re ρ − ½|}/(1 + |Im ρ − t|)²`. -/
theorem norm_paperFT_gammaOf_sub_le {φ : ℝ → ℂ} {a : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) (ρ : ℂ) (t : ℝ) :
    ‖paperFT φ (gammaOf ρ - t)‖ ≤
      Real.exp (|ρ.re - 1 / 2| * a) * decayMass φ / (1 + |ρ.im - t|) ^ 2 := by
  have h := norm_paperFT_sub_le hφ hsupp (gammaOf ρ) t
  have hre : (gammaOf ρ).re = ρ.im := by simp [gammaOf]
  have him : (gammaOf ρ).im = -(ρ.re - 1 / 2) := by simp [gammaOf]
  rwa [hre, him, abs_neg] at h

/-- **The pole term decays like `t^{−2}`.** -/
theorem norm_poleTerm_le {φ : ℝ → ℂ} {a : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) (t : ℝ) :
    ‖poleTerm φ t‖ ≤ 2 * (Real.exp (a / 2) * decayMass φ / (1 + |t|) ^ 2) := by
  unfold poleTerm
  have h1 := norm_paperFT_sub_le hφ hsupp (I / 2) t
  have h2 := norm_paperFT_sub_le hφ hsupp (-I / 2) t
  simp only [Complex.div_im, Complex.I_im, Complex.div_re, Complex.I_re, Complex.neg_im,
    Complex.neg_re] at h1 h2
  norm_num at h1 h2
  have e : |t| = |-t| := (abs_neg t).symm
  refine (norm_add_le _ _).trans ?_
  rw [two_mul]
  refine add_le_add (h1.trans_eq ?_) (h2.trans_eq ?_) <;>
    · congr 2; ring_nf

/-- **A finite layer leaves a vanishing footprint.** The contribution of finitely many zeros to the
orbit at height `t` tends to `0` as `t → ∞`. -/
theorem tendsto_finiteLayer_footprint {φ : ℝ → ℂ} {a : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) (F : Finset ℂ) (c : ℂ → ℂ) :
    Filter.Tendsto (fun t : ℝ => ∑ ρ ∈ F, c ρ * paperFT φ (gammaOf ρ - t)) Filter.atTop (nhds 0) := by
  rw [show (0 : ℂ) = ∑ ρ ∈ F, c ρ * 0 by simp]
  refine tendsto_finsetSum _ fun ρ _ => (tendsto_const_nhds).mul ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound := fun t => norm_paperFT_gammaOf_sub_le hφ hsupp ρ t
  have hlim : Filter.Tendsto (fun t : ℝ =>
      Real.exp (|ρ.re - 1 / 2| * a) * decayMass φ / (1 + |ρ.im - t|) ^ 2) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (1 + |ρ.im - t|) ^ 2) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_pow_atTop (by norm_num) |>.comp ?_
      refine Filter.tendsto_atTop_add_const_left _ 1 ?_
      have : Filter.Tendsto (fun t : ℝ => t - ρ.im) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
      exact (Filter.tendsto_abs_atTop_atTop.comp this).congr fun t => by
        simp [abs_sub_comm]
    exact h1.const_div_atTop _
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hlim

/-! ## The Gamma term -/

/-- `|μ(τ)| ≤ A + log(2 + |τ|)`. -/
theorem exists_abs_mu_le' : ∃ A : ℝ, ∀ τ : ℝ, |mu τ| ≤ A + Real.log (2 + |τ|) := by
  obtain ⟨C, hC⟩ := gammaFacts.stirling
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    gammaFacts.smooth.continuous.continuousOn
  refine ⟨max (|C| + Real.log (2 * π)) B, fun τ => ?_⟩
  have hlog0 : 0 ≤ Real.log (2 + |τ|) := Real.log_nonneg (by linarith [abs_nonneg τ])
  rcases le_or_gt |τ| 1 with h | h
  · have hτ : τ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    have := hB τ hτ
    rw [Real.norm_eq_abs] at this
    linarith [le_max_right (|C| + Real.log (2 * π)) B]
  · have h1 : 1 ≤ |τ| := h.le
    have hs := hC τ h1
    have hτ2 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith [sq_abs τ]
    have hCτ : C / τ ^ 2 ≤ |C| := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [le_abs_self C, abs_nonneg C]
    have hpi : 0 < 2 * π := by positivity
    have hlogτ : 0 ≤ Real.log |τ| := Real.log_nonneg h1
    have hlogpi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have habs : |Real.log (|τ| / (2 * π))| ≤ Real.log (2 + |τ|) + Real.log (2 * π) := by
      rw [Real.log_div (by linarith) hpi.ne']
      have : Real.log |τ| ≤ Real.log (2 + |τ|) := Real.log_le_log (by linarith) (by linarith)
      rw [abs_le]; constructor <;> linarith
    have hfac : |(1 / (2 * π)) * Real.log (|τ| / (2 * π))| ≤ |Real.log (|τ| / (2 * π))| := by
      rw [abs_mul, abs_of_pos (by positivity)]
      have : 1 / (2 * π) ≤ 1 := by rw [div_le_one hpi]; linarith [Real.pi_gt_three]
      nlinarith [abs_nonneg (Real.log (|τ| / (2 * π)))]
    have := abs_sub_abs_le_abs_sub (mu τ) ((1 / (2 * π)) * Real.log (|τ| / (2 * π)))
    linarith [le_max_left (|C| + Real.log (2 * π)) B]


/-- **The Gamma term grows at most like `log t`**, with a constant `C_φ K` uniform in `φ`. -/
theorem exists_norm_gammaTerm_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (φ : ℝ → ℂ) (a : ℝ), ContDiff ℝ 2 φ → (∀ u, φ u ≠ 0 → |u| ≤ a) →
      ∀ t : ℝ, ‖gammaTerm φ t‖ ≤ decayMass φ * K * (1 + Real.log (2 + |t|)) := by
  obtain ⟨A, hA⟩ := exists_abs_mu_le'
  set A' := max A 0
  have hInt : Integrable (fun v : ℝ => (1 + |v|) ^ (-(3 / 2 : ℝ))) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  set K₀ := ∫ v : ℝ, (1 + |v|) ^ (-(3 / 2 : ℝ))
  have hK₀ : 0 ≤ K₀ := integral_nonneg fun v => by positivity
  have hA0' : 0 ≤ A' := le_max_right _ _
  refine ⟨K₀ * (A' + 2), by positivity, fun φ a hφ hsupp t => ?_⟩
  set C := decayMass φ
  have hC := decayMass_nonneg φ
  set L := Real.log (2 + |t|)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [abs_nonneg t])
  -- the majorant
  set g : ℝ → ℝ := fun τ => C * (A' + L + 2) * (1 + |τ - t|) ^ (-(3 / 2 : ℝ))
  have hg : Integrable g := (hInt.comp_sub_right t).const_mul _
  have hpt : ∀ τ : ℝ, ‖paperFT φ ((τ : ℂ) - t) * (mu τ : ℂ)‖ ≤ g τ := fun τ => by
    set w := 1 + |τ - t|
    have hw : 1 ≤ w := by linarith [abs_nonneg (τ - t)]
    have hw0 : 0 < w := by linarith
    have h1 := norm_paperFT_sub_le hφ hsupp (τ : ℂ) t
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
      Complex.ofReal_re] at h1
    have hmu : |mu τ| ≤ A' + L + Real.log w := by
      have h2 := hA τ
      have hsplit : 2 + |τ| ≤ (2 + |t|) * w := by
        have := abs_sub_abs_le_abs_sub τ t
        nlinarith [abs_nonneg t, abs_nonneg (τ - t)]
      have hlog : Real.log (2 + |τ|) ≤ L + Real.log w := by
        rw [← Real.log_mul (by positivity) hw0.ne']
        exact Real.log_le_log (by positivity) hsplit
      have : A ≤ A' := le_max_left _ _
      linarith
    have hlogw : Real.log w ≤ 2 * w ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div hw0.le (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    have hw32 : w ^ (-(3 / 2 : ℝ)) = w ^ (1 / 2 : ℝ) / w ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hw0]; norm_num
    have hinv : 1 / w ^ 2 ≤ w ^ (-(3 / 2 : ℝ)) := by
      rw [hw32]
      exact div_le_div_of_nonneg_right (Real.one_le_rpow hw (by norm_num)) (by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA0 : 0 ≤ A' := le_max_right _ _
    calc ‖paperFT φ ((τ : ℂ) - t)‖ * |mu τ| ≤ C / w ^ 2 * (A' + L + Real.log w) :=
          mul_le_mul h1 hmu (abs_nonneg _) (by positivity)
      _ = C * ((A' + L) * (1 / w ^ 2) + Real.log w / w ^ 2) := by ring
      _ ≤ C * ((A' + L) * w ^ (-(3 / 2 : ℝ)) + 2 * w ^ (-(3 / 2 : ℝ))) := by
          gcongr
          rw [hw32, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right hlogw (by positivity)
      _ = g τ := by simp only [g, w]; ring
  have hnorm := norm_integral_le_integral_norm (μ := volume)
    (fun τ : ℝ => paperFT φ ((τ : ℂ) - t) * (mu τ : ℂ))
  have hmono : ∫ τ : ℝ, ‖paperFT φ ((τ : ℂ) - t) * (mu τ : ℂ)‖ ≤ ∫ τ, g τ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hg
      (Filter.Eventually.of_forall hpt)
  have hgint : ∫ τ, g τ = C * (A' + L + 2) * K₀ := by
    simp only [g]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun v : ℝ => (1 + |v|) ^ (-(3 / 2 : ℝ))) t
  unfold gammaTerm
  calc ‖∫ τ : ℝ, paperFT φ ((τ : ℂ) - t) * (mu τ : ℂ)‖ ≤ C * (A' + L + 2) * K₀ :=
        hnorm.trans (hmono.trans hgint.le)
    _ ≤ C * (K₀ * (A' + 2)) * (1 + L) := by
        have hA0 : 0 ≤ A' := le_max_right _ _
        have e : C * (K₀ * (A' + 2)) * (1 + L) - C * (A' + L + 2) * K₀ = C * K₀ * (A' + 1) * L := by
          ring
        have : 0 ≤ C * K₀ * (A' + 1) * L := by positivity
        linarith

/-! ## Pole imitation at a return -/

/-- The orbit mass `M_φ = Σ_n Λ(n) n^{−½} |φ(log n)|`. -/
def orbitMass (φ : ℝ → ℂ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / Real.sqrt n * ‖φ (Real.log n)‖

/-- At a `δ`-return of the primes `≤ e^a`, the orbit polynomial at height `t` is the orbit
polynomial at `0` up to `2πδ(a/log 2)M_φ`. -/
theorem norm_orbitPoly_sub_le {φ : ℝ → ℂ} {a : ℝ}
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) {δ t : ℝ} (hδ : 0 ≤ δ)
    (hret : ∀ p : ℕ, p.Prime → Real.log p ≤ a → dist01 (t * Real.log p / (2 * π)) ≤ δ) :
    ‖orbitPoly φ t - orbitPoly φ 0‖ ≤ 2 * π * δ * (a / Real.log 2) * orbitMass φ := by
  set N := ⌊Real.exp a⌋₊ + 1
  have hvan : ∀ n ∉ Finset.range N, φ (Real.log n) = 0 := fun n hn => by
    by_contra h
    have hle := hsupp _ h
    have hn' : Real.exp a < n := by
      have : N ≤ n := by simpa using hn
      have h1 : Real.exp a < (N : ℝ) := by
        simp only [N]; push_cast; exact Nat.lt_floor_add_one _
      exact h1.trans_le (by exact_mod_cast this)
    have hpos : (0 : ℝ) < n := (Real.exp_pos a).trans hn'
    have : a < Real.log n := by rw [← Real.log_exp a]; exact Real.log_lt_log (Real.exp_pos a) hn'
    have : a < |Real.log n| := this.trans_le (le_abs_self _)
    linarith
  have hsum : ∀ s : ℝ, orbitPoly φ s = ∑ n ∈ Finset.range N,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * φ (Real.log n) *
        Complex.exp (-((s * Real.log n : ℝ) : ℂ) * I) := fun s =>
    tsum_eq_sum fun n hn => by rw [hvan n hn]; simp
  have hmass : orbitMass φ = ∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * ‖φ (Real.log n)‖ :=
    tsum_eq_sum fun n hn => by rw [hvan n hn]; simp
  rw [hsum t, hsum 0, hmass, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  simp only [zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one]
  rw [← mul_sub_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [abs_of_nonneg hΛ0]
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp [hΛ]
  by_cases hφn : φ (Real.log n) = 0
  · simp [hφn]
  obtain ⟨p, k, hp, hk, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have hlogp : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp'.two_le)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log ((p ^ k : ℕ) : ℝ) = k * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hka : (k : ℝ) * Real.log p ≤ a := by
    have := hsupp _ hφn
    rw [hlogn] at this
    exact (le_abs_self _).trans this
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpa : Real.log p ≤ a := by nlinarith
  have hkla : (k : ℝ) ≤ a / Real.log 2 := by
    rw [le_div_iff₀ hl2]; nlinarith
  have hd : dist01 (t * Real.log ((p ^ k : ℕ) : ℝ) / (2 * π)) ≤ k * δ := by
    have e : t * Real.log ((p ^ k : ℕ) : ℝ) / (2 * π) = ((k : ℤ) : ℝ) * (t * Real.log p / (2 * π)) := by
      rw [hlogn]; push_cast; ring
    rw [e]
    refine (dist01_intCast_mul_le _ _).trans ?_
    have : |((k : ℤ) : ℝ)| = k := by push_cast; exact abs_of_nonneg (Nat.cast_nonneg k)
    rw [this]
    exact mul_le_mul_of_nonneg_left (hret p hp' hpa) (Nat.cast_nonneg k)
  have hexp := norm_exp_neg_sub_one_le (t * Real.log ((p ^ k : ℕ) : ℝ))
  have hbound : ‖Complex.exp (-((t * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * I) - 1‖ ≤
      2 * π * δ * (a / Real.log 2) := by
    calc _ ≤ 2 * π * dist01 (t * Real.log ((p ^ k : ℕ) : ℝ) / (2 * π)) := hexp
      _ ≤ 2 * π * (k * δ) := by gcongr
      _ ≤ 2 * π * ((a / Real.log 2) * δ) := by gcongr
      _ = 2 * π * δ * (a / Real.log 2) := by ring
  calc ArithmeticFunction.vonMangoldt (p ^ k) / Real.sqrt ((p ^ k : ℕ) : ℝ) *
        ‖φ (Real.log ((p ^ k : ℕ) : ℝ))‖ *
        ‖Complex.exp (-((t * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * I) - 1‖
      ≤ ArithmeticFunction.vonMangoldt (p ^ k) / Real.sqrt ((p ^ k : ℕ) : ℝ) *
        ‖φ (Real.log ((p ^ k : ℕ) : ℝ))‖ * (2 * π * δ * (a / Real.log 2)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- **Pole imitation.** At a `δ`-return of the primes `≤ e^a`, the zeros near height `t` reproduce
the orbit at `0`: `‖Z_φ(t) + P_φ(0)‖ ≤ ‖π_φ(t)‖ + ‖Γ_φ(t)‖ + 2πδ(a/log 2)M_φ`. -/
theorem norm_zeroSide_add_orbitPoly_zero_le {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ u ≤ 0, φ u = 0) {a : ℝ}
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) {δ t : ℝ} (hδ : 0 ≤ δ)
    (hret : ∀ p : ℕ, p.Prime → Real.log p ≤ a → dist01 (t * Real.log p / (2 * π)) ≤ δ) :
    ‖zeroSide φ t + orbitPoly φ 0‖ ≤
      ‖poleTerm φ t‖ + ‖gammaTerm φ t‖ + 2 * π * δ * (a / Real.log 2) * orbitMass φ := by
  have hrec := orbit_reciprocity hφ hφc hφ0 t
  have hdiff := norm_orbitPoly_sub_le hsupp hδ hret
  have e : zeroSide φ t + orbitPoly φ 0 =
      poleTerm φ t + gammaTerm φ t - (orbitPoly φ t - orbitPoly φ 0) := by
    rw [hrec]; ring
  rw [e]
  calc ‖poleTerm φ t + gammaTerm φ t - (orbitPoly φ t - orbitPoly φ 0)‖
      ≤ ‖poleTerm φ t + gammaTerm φ t‖ + ‖orbitPoly φ t - orbitPoly φ 0‖ := norm_sub_le _ _
    _ ≤ ‖poleTerm φ t‖ + ‖gammaTerm φ t‖ + ‖orbitPoly φ t - orbitPoly φ 0‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
