import GaloisForLFunctions.EulerFETransportTheory.PolynomialStripContinuationsLieInTheHamburgerClass
import GaloisForLFunctions.EulerFETransportTheory.MissingResonancesCostLogarithmicDefectEnergy
import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakesHavePositiveDensity
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Real-weighted fakes on the integers

Let `Z(s) = Σ a_n n^{-s}` (`a_1 = 1`, coefficients of any real-weighted system with integer
norms) continue to the critical line in the Hamburger strip class with defect `g`.

* **Theorem II.2(a)** (`fake_abelMass_floor`).  If `(s - 1) Z(s)` continues holomorphically to
  `Re s > 1/2` with a zero `ρ₀` that `ζ` lacks, some coefficient `a_m ≠ 1`, and
  `liminf δ ∫ ‖g‖ e^{-δ|t|} ≥ ‖a_m - 1‖/(3(m + 1)) > 0`: `g` is not Abel-sublinear, does not tend
  to zero, and is not `O((1 + |t|)^{-α})`.  If every `a_m = 1`, then `Z = ζ` and the continuation is
  `(s - 1) ζ(s)`, which does not vanish at `ρ₀`.
* **Theorem II.2(b)** (`signedPoly_*`).  For `ρ₀ = 3/4 + iγ₀` the three-term Dirichlet polynomial
  `F₀(s) = (1 - 2^{ρ₀ - s})(1 - 2^{ρ̄₀ - s})` is the zeta function of a real-weighted system on the
  powers of `2`: `F₀(s) = exp(Σ_r w̃_r 2^{-rs})` with
  `w̃_r = -(2/r) 2^{3r/4} cos(r γ₀ log 2)` (`signedPoly_eq_exp`).  Its count is bounded
  (density `0`), it vanishes at `ρ₀`, and it lies in the Hamburger strip class with `β = 0` and a
  **bounded** defect `‖g(t)‖ ≤ 2(1 + 2^{1/4})²` (`signedPoly_hamburgerStripDefect`).
  Möbius inversion turns the prime-power weights into Euler weights on the norms `2^m`:
  `w_m = (1/m) Σ_{de = m} μ(d) e w̃_e`, `|w_m| ≤ 2 · 2^{3m/4}`, and
  `F₀(s) = Π_m (1 - 2^{-ms})^{-w_m}` on `Re s > 3/4` (`hasProd_signedPoly`).
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower.HamburgerStability

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory

/-! ## (a) Abel floor of a real-weighted fake -/

/-- `Σ a_n n^{-s} = ζ(s)` on `Re s > 1` when every `a_n = 1`. -/
theorem coeffDirichlet_eq_riemannZeta_of_forall_eq_one {a : ℕ → ℂ}
    (h1 : ∀ m : ℕ, 1 ≤ m → a m = 1) {s : ℂ} (hs : 1 < s.re) :
    coeffDirichlet a s = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, coeffDirichlet]
  refine tsum_congr fun n => ?_
  rw [h1 (n + 1) (Nat.succ_pos n)]
  push_cast
  rfl

/-- **A fake has a coefficient different from `1`.**  If `(s - 1) Z(s)` continues to `Re s > 1/2`
and vanishes at `ρ₀` where `ζ(ρ₀) ≠ 0`, then `a_m ≠ 1` for some `m ≥ 1`. -/
theorem exists_coeff_ne_one_of_fakeZero {a : ℕ → ℂ} {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * coeffDirichlet a s)
    {ρ₀ : ℂ} (hρ : 1 / 2 < ρ₀.re) (hρ1 : ρ₀ ≠ 1) (hG0 : G ρ₀ = 0)
    (hζ : riemannZeta ρ₀ ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ a m ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hZd : DifferentiableOn ℂ RHTower.zetaResidueUnit {s : ℂ | 1 / 2 < s.re} := fun s _ =>
    (RHTower.analyticAt_zetaResidueUnit s).differentiableAt.differentiableWithinAt
  have heq : ∀ s : ℂ, 1 < s.re → G s = RHTower.zetaResidueUnit s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
    rw [hGeq s hs, coeffDirichlet_eq_riemannZeta_of_forall_eq_one hcon hs,
      RHTower.zetaResidueUnit, Function.update_of_ne hs1]
  have hid := SumProductArithmeticOfTheLogarithm.eqOn_halfPlane_of_eq_on_one hGd hZd heq hρ
  rw [hG0, RHTower.zetaResidueUnit, Function.update_of_ne hρ1] at hid
  exact mul_ne_zero (sub_ne_zero.mpr hρ1) hζ hid.symm

/-- **Theorem II.2(a).**  A real-weighted fake on the integers (`a_1 = 1`, a continuation of
`(s - 1) Z(s)` to `Re s > 1/2` with a zero `ζ` lacks) in the Hamburger strip class has a
coefficient `a_m ≠ 1` and Abel floor `‖a_m - 1‖/(3(m + 1)) > 0`; its defect is neither
Abel-sublinear, nor `o(1)`, nor `O((1 + |t|)^{-α})` for any `α > 0`. -/
theorem fake_abelMass_floor {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (ha1 : a 1 = 1) {β : ℂ} {g : ℝ → ℂ} (hH : HamburgerStripDefect (coeffDirichlet a) β g)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * coeffDirichlet a s)
    {ρ₀ : ℂ} (hρ : 1 / 2 < ρ₀.re) (hρ1 : ρ₀ ≠ 1) (hG0 : G ρ₀ = 0)
    (hζ : riemannZeta ρ₀ ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ a m ≠ 1 ∧
      (∀ c : ℝ, c < ‖a m - 1‖ / (3 * ((m : ℝ) + 1)) → ∀ᶠ δ in 𝓝[>] 0, c ≤ δ * abelMass g δ) ∧
      ¬ Tendsto (fun δ => δ * abelMass g δ) (𝓝[>] 0) (𝓝 0) ∧
      (¬ ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R ≤ |t| → ‖g t‖ ≤ ε) ∧
      ∀ α : ℝ, 0 < α → ∀ C₁ : ℝ, ¬ ∀ t : ℝ, ‖g t‖ ≤ C₁ * (1 + |t|) ^ (-α) := by
  obtain ⟨m, hm, hne⟩ := exists_coeff_ne_one_of_fakeZero hGd hGeq hρ hρ1 hG0 hζ
  have hne' : a 1 ≠ a m := by rw [ha1]; exact fun h => hne h.symm
  refine ⟨m, hm, hne, fun c hc => ?_, not_tendsto_mul_abelMass_of_coeff_ne ha hH le_rfl hm hne',
    not_tendsto_zero_of_coeff_ne ha hH le_rfl hm hne',
    fun α hα C₁ => not_le_rpow_neg_of_coeff_ne ha hH le_rfl hm hne' hα C₁⟩
  exact eventually_le_mul_abelMass_of_coeff_ne ha hH le_rfl hm (by rwa [ha1])

/-! ## (b) A signed system on the powers of `2` with a bounded defect -/

/-- The fake zero `ρ₀ = 3/4 + iγ₀`. -/
def signedZero (γ₀ : ℝ) : ℂ := 3 / 4 + γ₀ * I

/-- `F₀(s) = (1 - 2^{ρ₀ - s})(1 - 2^{ρ̄₀ - s})`. -/
def signedPoly (γ₀ : ℝ) (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (signedZero γ₀ - s)) * (1 - (2 : ℂ) ^ ((starRingEnd ℂ) (signedZero γ₀) - s))

/-- The Dirichlet coefficients of `F₀`: `a_1 = 1`, `a_2 = -(2^{ρ₀} + 2^{ρ̄₀})`,
`a_4 = 2^{ρ₀ + ρ̄₀}`, all others `0`. -/
def signedCoeff (γ₀ : ℝ) (n : ℕ) : ℂ :=
  if n = 1 then 1
  else if n = 2 then -((2 : ℂ) ^ signedZero γ₀ + (2 : ℂ) ^ (starRingEnd ℂ) (signedZero γ₀))
  else if n = 4 then (2 : ℂ) ^ (signedZero γ₀ + (starRingEnd ℂ) (signedZero γ₀))
  else 0

/-- The real prime-power weights `w̃_r = -(2/r) 2^{3r/4} cos(r γ₀ log 2)` at `2^r`. -/
def signedWeight (γ₀ : ℝ) (r : ℕ) : ℝ :=
  -(2 / r) * (2 : ℝ) ^ (3 * r / 4 : ℝ) * Real.cos (r * γ₀ * Real.log 2)

theorem two_cpow_eq (z : ℂ) : (2 : ℂ) ^ z = cexp (z * Real.log 2) := by
  rw [Complex.cpow_def_of_ne_zero two_ne_zero, mul_comm]
  congr 2
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.ofReal_log (by norm_num)]

theorem norm_two_cpow (z : ℂ) : ‖(2 : ℂ) ^ z‖ = (2 : ℝ) ^ z.re := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem signedPoly_signedZero (γ₀ : ℝ) : signedPoly γ₀ (signedZero γ₀) = 0 := by
  simp [signedPoly]

theorem signedPoly_conj_signedZero (γ₀ : ℝ) :
    signedPoly γ₀ ((starRingEnd ℂ) (signedZero γ₀)) = 0 := by
  simp [signedPoly]

theorem signedZero_re (γ₀ : ℝ) : (signedZero γ₀).re = 3 / 4 := by
  simp [signedZero]

theorem conj_signedZero (γ₀ : ℝ) : (starRingEnd ℂ) (signedZero γ₀) = 3 / 4 - (γ₀ : ℂ) * I := by
  rw [signedZero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_ofNat,
    map_ofNat]
  ring

/-- `F₀` is the Dirichlet polynomial of `signedCoeff`. -/
theorem coeffDirichlet_signedCoeff (γ₀ : ℝ) (s : ℂ) :
    coeffDirichlet (signedCoeff γ₀) s = signedPoly γ₀ s := by
  set ρ := signedZero γ₀
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [coeffDirichlet, tsum_eq_sum (s := {0, 1, 3}) fun n hn => ?_]
  · simp only [signedCoeff]
    norm_num
    have h4 : (4 : ℂ) ^ s = (2 : ℂ) ^ s * (2 : ℂ) ^ s := by
      rw [← Complex.cpow_add _ _ h2, Complex.cpow_def_of_ne_zero (by norm_num : (4 : ℂ) ≠ 0),
        Complex.cpow_def_of_ne_zero h2]
      congr 1
      have hl : Complex.log 4 = 2 * Complex.log 2 := by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
          ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_log (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
      rw [hl]; ring
    have hs0 : (2 : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl h2)
    rw [h4]
    unfold signedPoly
    rw [Complex.cpow_sub _ _ h2, Complex.cpow_sub _ _ h2, Complex.cpow_add _ _ h2]
    field_simp
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp only [signedCoeff]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), zero_div]

/-- `F₀(s) = exp(Σ_{r ≥ 1} w̃_r 2^{-rs})` on `Re s > 3/4`: the zeta function of the real weights
`w̃_r` at `2^r`. -/
theorem signedPoly_eq_exp (γ₀ : ℝ) {s : ℂ} (hs : 3 / 4 < s.re) :
    signedPoly γ₀ s = cexp (∑' r : ℕ, (signedWeight γ₀ (r + 1) : ℂ) *
      (2 : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s))) := by
  set ρ := signedZero γ₀ with hρ
  set z₁ : ℂ := (2 : ℂ) ^ (ρ - s) with hz₁
  set z₂ : ℂ := (2 : ℂ) ^ ((starRingEnd ℂ) ρ - s) with hz₂
  have hz₁n : ‖z₁‖ < 1 := by
    rw [hz₁, norm_two_cpow]
    have : (ρ - s).re < 0 := by simp [hρ, signedZero_re]; linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) this
  have hz₂n : ‖z₂‖ < 1 := by
    rw [hz₂, norm_two_cpow]
    have : ((starRingEnd ℂ) ρ - s).re < 0 := by simp [hρ, signedZero_re]; linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) this
  have hs1 := Complex.hasSum_taylorSeries_neg_log hz₁n
  have hs2 := Complex.hasSum_taylorSeries_neg_log hz₂n
  -- the weights reproduce `-(z₁^r + z₂^r)/r`
  have hterm : ∀ r : ℕ, (signedWeight γ₀ (r + 1) : ℂ) * (2 : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s)) =
      -(z₁ ^ (r + 1) / ((r + 1 : ℕ) : ℂ) + z₂ ^ (r + 1) / ((r + 1 : ℕ) : ℂ)) := by
    intro r
    set k : ℕ := r + 1 with hk
    have hk0 : (k : ℂ) ≠ 0 := by rw [hk]; exact_mod_cast Nat.succ_ne_zero r
    -- `z₁^k = 2^{kρ} 2^{-ks}` and `2^{kρ} + 2^{kρ̄} = 2 · 2^{3k/4} cos(kγ₀ log 2)`
    have hz₁k : z₁ ^ k = cexp ((k : ℂ) * (ρ - s) * Real.log 2) := by
      rw [hz₁, ← Complex.cpow_nat_mul, two_cpow_eq]
    have hz₂k : z₂ ^ k = cexp ((k : ℂ) * ((starRingEnd ℂ) ρ - s) * Real.log 2) := by
      rw [hz₂, ← Complex.cpow_nat_mul, two_cpow_eq]
    have hsum : z₁ ^ k + z₂ ^ k = ((2 * (2 : ℝ) ^ (3 * k / 4 : ℝ) *
        Real.cos (k * γ₀ * Real.log 2) : ℝ) : ℂ) * cexp (-((k : ℂ) * s) * Real.log 2) := by
      rw [hz₁k, hz₂k]
      have e1 : (k : ℂ) * (ρ - s) * Real.log 2 = ((3 * k / 4 * Real.log 2 : ℝ) : ℂ) +
          ((k * γ₀ * Real.log 2 : ℝ) : ℂ) * I + (-((k : ℂ) * s) * Real.log 2) := by
        rw [hρ, signedZero]; push_cast; ring
      have e2 : (k : ℂ) * ((starRingEnd ℂ) ρ - s) * Real.log 2 =
          ((3 * k / 4 * Real.log 2 : ℝ) : ℂ) + ((-(k * γ₀ * Real.log 2) : ℝ) : ℂ) * I +
            (-((k : ℂ) * s) * Real.log 2) := by
        rw [hρ, conj_signedZero]; push_cast; ring
      rw [e1, e2, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
        Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp]
      have hrp : Real.exp (3 * k / 4 * Real.log 2) = (2 : ℝ) ^ (3 * k / 4 : ℝ) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; ring_nf
      rw [hrp, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    have hpow : (2 : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s)) = cexp (-((k : ℂ) * s) * Real.log 2) := by
      rw [two_cpow_eq]
    rw [hpow, signedWeight]
    rw [show -(z₁ ^ k / (k : ℂ) + z₂ ^ k / (k : ℂ)) = -(z₁ ^ k + z₂ ^ k) / (k : ℂ) by ring, hsum]
    push_cast
    field_simp
  -- sum the two logarithm series
  have hsum := (hs1.add hs2)
  have hsum' : HasSum (fun r : ℕ => (signedWeight γ₀ (r + 1) : ℂ) *
      (2 : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s))) (Complex.log (1 - z₁) + Complex.log (1 - z₂)) := by
    have h := ((hasSum_nat_add_iff' 1).mpr hsum).neg
    have hv : -((-Complex.log (1 - z₁) + -Complex.log (1 - z₂)) -
        ∑ i ∈ Finset.range 1, (z₁ ^ i / (i : ℂ) + z₂ ^ i / (i : ℂ))) =
        Complex.log (1 - z₁) + Complex.log (1 - z₂) := by
      rw [Finset.sum_range_one]; simp; ring
    rw [hv] at h
    exact h.congr_fun fun r => hterm r
  rw [hsum'.tsum_eq, Complex.exp_add,
    Complex.exp_log (sub_ne_zero.mpr fun h => by rw [← h, norm_one] at hz₁n; exact lt_irrefl _ hz₁n),
    Complex.exp_log (sub_ne_zero.mpr fun h => by rw [← h, norm_one] at hz₂n; exact lt_irrefl _ hz₂n)]
  rfl

/-- On `Re s ≥ 1/2`, `‖F₀(s)‖ ≤ (1 + 2^{1/4})²`. -/
theorem norm_signedPoly_le (γ₀ : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖signedPoly γ₀ s‖ ≤ (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
  have hb : ∀ w : ℂ, w.re ≤ 1 / 4 → ‖1 - (2 : ℂ) ^ w‖ ≤ 1 + (2 : ℝ) ^ (1 / 4 : ℝ) := by
    intro w hw
    calc ‖1 - (2 : ℂ) ^ w‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ w‖ := norm_sub_le _ _
      _ = 1 + (2 : ℝ) ^ w.re := by rw [norm_one, norm_two_cpow]
      _ ≤ 1 + (2 : ℝ) ^ (1 / 4 : ℝ) :=
          add_le_add_right (Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hw) 1
  rw [signedPoly, norm_mul, sq]
  exact mul_le_mul (hb _ (by simp [signedZero_re]; linarith))
    (hb _ (by simp [signedZero_re]; linarith)) (norm_nonneg _) (by positivity)

/-- The count of the signed system is bounded: density `0`. -/
theorem norm_coeffSum_signedCoeff_le (γ₀ : ℝ) (n : ℕ) :
    ‖EulerFETransportTheory.coeffSum (signedCoeff γ₀) n‖ ≤
      ‖signedCoeff γ₀ 1‖ + ‖signedCoeff γ₀ 2‖ + ‖signedCoeff γ₀ 4‖ := by
  have hz : ∀ k : ℕ, k ∉ ({0, 1, 3} : Finset ℕ) → signedCoeff γ₀ (k + 1) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    simp only [signedCoeff]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  unfold EulerFETransportTheory.coeffSum
  have e : ∑ k ∈ Finset.range n, signedCoeff γ₀ (k + 1) =
      ∑ k ∈ Finset.range n ∩ {0, 1, 3}, signedCoeff γ₀ (k + 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range n) (· ∈ ({0, 1, 3} : Finset ℕ))]
    rw [Finset.sum_eq_zero (s := Finset.filter (fun k => k ∉ ({0, 1, 3} : Finset ℕ)) _)
      fun k hk => hz k (Finset.mem_filter.mp hk).2, add_zero]
    rfl
  rw [e]
  calc ‖∑ k ∈ Finset.range n ∩ {0, 1, 3}, signedCoeff γ₀ (k + 1)‖
      ≤ ∑ k ∈ Finset.range n ∩ {0, 1, 3}, ‖signedCoeff γ₀ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ ({0, 1, 3} : Finset ℕ), ‖signedCoeff γ₀ (k + 1)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          fun _ _ _ => norm_nonneg _
    _ = _ := by simp [Finset.sum_insert, add_assoc]

/-- **Theorem II.2(b).**  The signed system is in the Hamburger strip class with `β = 0` and a
bounded defect `‖g(t)‖ ≤ 2(1 + 2^{1/4})²`. -/
theorem signedPoly_hamburgerStripDefect (γ₀ : ℝ) :
    HamburgerStripDefect (coeffDirichlet (signedCoeff γ₀)) 0
      (stripDefect fun s => (s - 1) * signedPoly γ₀ s) ∧
    ∀ t : ℝ, ‖stripDefect (fun s => (s - 1) * signedPoly γ₀ s) t‖ ≤
      2 * (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
  set G : ℂ → ℂ := fun s => (s - 1) * signedPoly γ₀ s with hG
  have hGdiff : Differentiable ℂ G := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    intro s
    unfold G signedPoly
    fun_prop (disch := exact Or.inl h2)
  have hstrip : ∀ s ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2), 1 / 2 ≤ s.re := fun s hs => by
    rw [HTGeometry.mem_verticalStrip] at hs; exact hs.1
  have hH := hamburgerStripDefect_of_stripContinuation (Z := coeffDirichlet (signedCoeff γ₀))
    (G := G) hGdiff.continuous.continuousOn hGdiff.differentiableOn
    (fun s _ => by rw [hG, coeffDirichlet_signedCoeff])
    (C₀ := (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * 2) (N₀ := 1) fun s hs => by
      have hre := hstrip s hs
      have hs' := hs
      rw [HTGeometry.mem_verticalStrip] at hs'
      have h1 : ‖s - 1‖ ≤ 2 * (1 + |s.im|) := by
        have := Complex.norm_le_abs_re_add_abs_im (s - 1)
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
          sub_zero] at this
        have : |s.re - 1| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
        linarith [abs_nonneg s.im]
      rw [hG, norm_mul, pow_one]
      calc ‖s - 1‖ * ‖signedPoly γ₀ s‖ ≤ 2 * (1 + |s.im|) * (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
            mul_le_mul h1 (norm_signedPoly_le γ₀ hre) (norm_nonneg _) (by positivity)
        _ = _ := by ring
  have hG1 : G 1 / 2 = 0 := by simp [hG]
  rw [hG1] at hH
  refine ⟨hH, fun t => ?_⟩
  set s : ℂ := (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * I with hsdef
  have hsre : s.re = 1 / 2 := by simp [hsdef]
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hsre] at this; norm_num at this
  have hs2 : 1 - s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hsre] at this
  have hχ : ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖ = 1 := by
    rw [norm_div, norm_Gammaℝ_one_sub_of_re_eq_half hsre,
      div_self (norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)))]
  have e : stripDefect G t = signedPoly γ₀ s -
      Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * signedPoly γ₀ (1 - s) := by
    show G s / (s - 1) - Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * (G (1 - s) / (1 - s - 1)) = _
    rw [hG]
    simp only
    rw [mul_div_cancel_left₀ _ hs1, mul_div_cancel_left₀ _ hs2]
  rw [e]
  calc ‖signedPoly γ₀ s - Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * signedPoly γ₀ (1 - s)‖
      ≤ ‖signedPoly γ₀ s‖ + 1 * ‖signedPoly γ₀ (1 - s)‖ := by
        have := norm_sub_le (signedPoly γ₀ s)
          (Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s * signedPoly γ₀ (1 - s))
        rwa [norm_mul, hχ] at this
    _ ≤ (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 + 1 * (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
        gcongr
        · exact norm_signedPoly_le γ₀ hsre.ge
        · exact norm_signedPoly_le γ₀ (by simp [hsre]; norm_num)
    _ = 2 * (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by ring

/-- **The signed fake.**  For `γ₀ = 1` the signed system has a fake zero `ρ₀ = 3/4 + i`
(`ζ(ρ₀) ≠ 0`), density `0`, a bounded defect, and a positive Abel floor
`liminf δ ∫ ‖g‖ e^{-δ|t|} ≥ 1/12`. -/
theorem signedPoly_fake :
    signedPoly 1 (signedZero 1) = 0 ∧ riemannZeta (signedZero 1) ≠ 0 ∧
      (∀ n : ℕ, ‖EulerFETransportTheory.coeffSum (signedCoeff 1) n‖ ≤
        ‖signedCoeff 1 1‖ + ‖signedCoeff 1 2‖ + ‖signedCoeff 1 4‖) ∧
      (∀ t : ℝ, ‖stripDefect (fun s => (s - 1) * signedPoly 1 s) t‖ ≤
        2 * (1 + (2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2) ∧
      ∀ c : ℝ, c < 1 / 12 → ∀ᶠ δ in 𝓝[>] 0,
        c ≤ δ * abelMass (stripDefect fun s => (s - 1) * signedPoly 1 s) δ := by
  obtain ⟨hH, hb⟩ := signedPoly_hamburgerStripDefect 1
  refine ⟨signedPoly_signedZero 1, ?_, norm_coeffSum_signedCoeff_le 1, hb, fun c hc => ?_⟩
  · exact RHTower.riemannZeta_ne_zero_of_abs_im_lt_four (by rw [signedZero_re]; norm_num)
      (by rw [signedZero_re]; norm_num) (by simp [signedZero])
  · -- `a_1 = 1`, `a_3 = 0`
    have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ =>
        ‖signedCoeff 1 (n + 1)‖ / ((n : ℝ) + 1) ^ σ := by
      intro σ _
      refine summable_of_ne_finset_zero (s := {0, 1, 3}) fun n hn => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      simp only [signedCoeff]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), norm_zero, zero_div]
    have h3 : signedCoeff 1 3 = 0 := by simp [signedCoeff]
    have h1 : signedCoeff 1 1 = 1 := by simp [signedCoeff]
    refine eventually_le_mul_abelMass_of_coeff_ne ha hH (m₁ := 1) (m₂ := 3) le_rfl
      (by norm_num) ?_
    rw [h3, h1, zero_sub, norm_neg, norm_one]
    norm_num
    linarith

/-! ## (b) Euler weights by Möbius inversion -/

/-- The Möbius-inverted Euler weights `w_m = (1/m) Σ_{d e = m} μ(d) e W_e` of prime-power
weights `W`. -/
def eulerWeight (W : ℕ → ℝ) (m : ℕ) : ℝ :=
  (∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * (x.2 * W x.2)) / m

/-- **Möbius inversion**: `Σ_{m ∣ r} m w_m = r W_r`. -/
theorem sum_divisors_mul_eulerWeight (W : ℕ → ℝ) {r : ℕ} (hr : 0 < r) :
    ∑ m ∈ r.divisors, (m : ℝ) * eulerWeight W m = r * W r :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun m => (m : ℝ) * eulerWeight W m) (g := fun r => (r : ℝ) * W r)).mpr
    (fun n hn => by
      simp only [eulerWeight]
      rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]) r hr

/-- Exponentially bounded weights `|r W_r| ≤ C a^r` give `|w_m| ≤ C a^m`. -/
theorem abs_eulerWeight_le {W : ℕ → ℝ} {C a : ℝ} (ha : 1 ≤ a)
    (hW : ∀ r : ℕ, |(r : ℝ) * W r| ≤ C * a ^ r) (m : ℕ) : |eulerWeight W m| ≤ C * a ^ m := by
  have hC : 0 ≤ C := by simpa using hW 0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [eulerWeight, Nat.divisorsAntidiagonal_zero, Finset.sum_empty, zero_div, abs_zero]
    positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [eulerWeight, abs_div, Nat.abs_cast, div_le_iff₀ hm']
  have hcard : ((m.divisorsAntidiagonal.card : ℕ) : ℝ) ≤ m := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
    exact_mod_cast Nat.card_divisors_le_self m
  calc |∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * (x.2 * W x.2)|
      ≤ ∑ x ∈ m.divisorsAntidiagonal, C * a ^ m := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
        rw [abs_mul]
        have hμ : |(ArithmeticFunction.moebius x.1 : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hx2 : x.2 ≤ m := Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
        calc |(ArithmeticFunction.moebius x.1 : ℝ)| * |(x.2 : ℝ) * W x.2| ≤ 1 * (C * a ^ x.2) :=
              mul_le_mul hμ (hW x.2) (abs_nonneg _) zero_le_one
          _ ≤ C * a ^ m := by rw [one_mul]; gcongr
    _ = (m.divisorsAntidiagonal.card : ℝ) * (C * a ^ m) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * a ^ m * m := by rw [mul_comm]; gcongr

/-- Divisor regrouping of a summable double series vanishing on the axes. -/
theorem hasSum_divisorsAntidiagonal_regroupC {f : ℕ × ℕ → ℂ} (hf : Summable f)
    (h0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → f p = 0) :
    HasSum (fun N : ℕ => ∑ p ∈ N.divisorsAntidiagonal, f p) (∑' p, f p) := by
  refine (hf.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)).congr_fun fun N => ?_
  rw [tsum_subtype]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
    have hz : ∀ p : ℕ × ℕ, ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}).indicator f p = 0 := by
      intro p
      by_cases hp : p ∈ (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}
      · rw [Set.indicator_of_mem hp]; exact h0 p (mul_eq_zero.mp hp)
      · rw [Set.indicator_of_notMem hp]
    simp only [hz, tsum_zero]
  · rw [tsum_eq_sum (s := N.divisorsAntidiagonal)]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Set.indicator_of_mem]
      exact (Nat.mem_divisorsAntidiagonal.mp hp).1
    · intro p hp
      rw [Set.indicator_of_notMem]
      intro h
      exact hp (Nat.mem_divisorsAntidiagonal.mpr ⟨h, hN.ne'⟩)

/-- **The Euler product of Möbius-inverted weights**: if `W_0 = 0`, `|r W_r| ≤ C a^r` and
`a ‖z‖ < 1`, then `Σ_m w_m (-log(1 - z^m)) = Σ_r W_r z^r`. -/
theorem hasSum_eulerWeight_neg_log {W : ℕ → ℝ} (hW0 : W 0 = 0) {C a : ℝ} (ha : 1 ≤ a)
    (hW : ∀ r : ℕ, |(r : ℝ) * W r| ≤ C * a ^ r) {z : ℂ} (hz : a * ‖z‖ < 1) :
    HasSum (fun m : ℕ => (eulerWeight W m : ℂ) * -Complex.log (1 - z ^ m))
      (∑' r : ℕ, (W r : ℂ) * z ^ r) := by
  have hC : 0 ≤ C := by simpa using hW 0
  have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  set q : ℝ := a * ‖z‖ with hq
  have hq0 : 0 ≤ q := by positivity
  have hzq : ‖z‖ ≤ q := by rw [hq]; nlinarith [norm_nonneg z]
  have hw0 : eulerWeight W 0 = 0 := by simp [eulerWeight]
  set f : ℕ × ℕ → ℂ := fun p => (eulerWeight W p.1 : ℂ) * ((z ^ p.1) ^ p.2 / (p.2 : ℂ)) with hf
  have hf0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → f p = 0 := by
    rintro ⟨m, k⟩ h
    rcases h with h | h
    · simp only [hf] at h ⊢; rw [h, hw0]; simp
    · simp only [hf] at h ⊢; rw [h]; simp
  -- absolute convergence: `‖f(m,k)‖ ≤ C q^m q^{k-1}`
  have hbound : ∀ p : ℕ × ℕ, ‖f p‖ ≤ C * q ^ p.1 * q ^ (p.2 - 1) := by
    rintro ⟨m, k⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hf0 _ (Or.inl rfl), norm_zero]; positivity
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hf0 _ (Or.inr rfl), norm_zero]; positivity
    simp only [hf, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hzk : (‖z‖ ^ m) ^ k ≤ ‖z‖ ^ m * q ^ (k - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ, Nat.add_sub_cancel, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (‖z‖ ^ m) ^ j ≤ ‖z‖ ^ j :=
            pow_le_pow_left₀ (by positivity) (pow_le_of_le_one (norm_nonneg z) hz1.le hm.ne') j
        _ ≤ q ^ j := pow_le_pow_left₀ (norm_nonneg z) hzq j
    have ham : a ^ m * ‖z‖ ^ m = q ^ m := by rw [hq, mul_pow]
    calc |eulerWeight W m| * ((‖z‖ ^ m) ^ k / k) ≤ C * a ^ m * (‖z‖ ^ m * q ^ (k - 1)) := by
          gcongr
          · exact abs_eulerWeight_le ha hW m
          · exact (div_le_self (by positivity) hk1).trans hzk
      _ = C * q ^ m * q ^ (k - 1) := by rw [← ham]; ring
  have hgeo : Summable fun k : ℕ => q ^ (k - 1) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using summable_geometric_of_lt_one hq0 hz
  have hsum : Summable f := Summable.of_norm_bounded
    (((summable_geometric_of_lt_one hq0 hz).mul_left C).mul_of_nonneg hgeo
      (fun m => by positivity) (fun k => by positivity)) hbound
  -- rows: `Σ_k f(m,k) = w_m (-log(1 - z^m))`
  have hrow : ∀ m : ℕ, HasSum (fun k => f (m, k))
      ((eulerWeight W m : ℂ) * -Complex.log (1 - z ^ m)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [hf, hw0, Complex.ofReal_zero, zero_mul]; exact hasSum_zero
    have hzm : ‖z ^ m‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hz1 hm.ne'
    exact (Complex.hasSum_taylorSeries_neg_log hzm).mul_left _
  -- fibres: `Σ_{m k = r} w_m z^r / k = W_r z^r`
  have hfib : ∀ r : ℕ, ∑ p ∈ r.divisorsAntidiagonal, f p = (W r : ℂ) * z ^ r := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [hW0]
    have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
    have hterm : ∀ p ∈ r.divisorsAntidiagonal,
        f p = z ^ r / r * ((p.1 : ℂ) * (eulerWeight W p.1 : ℂ)) := by
      intro p hp
      have hpr := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hp2 : (p.2 : ℂ) ≠ 0 := by
        refine Nat.cast_ne_zero.mpr fun h => ?_
        rw [h, mul_zero] at hpr; omega
      have hp1 : (p.1 : ℂ) ≠ 0 := by
        refine Nat.cast_ne_zero.mpr fun h => ?_
        rw [h, zero_mul] at hpr; omega
      simp only [hf]
      rw [← pow_mul, hpr]
      have : (r : ℂ) = p.1 * p.2 := by rw [← hpr]; push_cast; ring
      rw [this]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      Nat.sum_divisorsAntidiagonal (f := fun i _ => (i : ℂ) * (eulerWeight W i : ℂ))]
    have hm := sum_divisors_mul_eulerWeight W hr
    have hmC : ∑ i ∈ r.divisors, (i : ℂ) * (eulerWeight W i : ℂ) = (r : ℂ) * (W r : ℂ) := by
      exact_mod_cast hm
    rw [hmC]
    field_simp
  have hcol := (hasSum_divisorsAntidiagonal_regroupC hsum hf0).congr_fun fun r => (hfib r).symm
  rw [hcol.tsum_eq]
  exact hsum.hasSum.prod_fiberwise hrow

theorem abs_mul_signedWeight_le (γ₀ : ℝ) (r : ℕ) :
    |(r : ℝ) * signedWeight γ₀ r| ≤ 2 * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have e : (r : ℝ) * signedWeight γ₀ r = -2 * (2 : ℝ) ^ (3 * r / 4 : ℝ) *
      Real.cos (r * γ₀ * Real.log 2) := by
    rw [signedWeight]; field_simp
  have hp : (2 : ℝ) ^ (3 * r / 4 : ℝ) = ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
  rw [e, abs_mul, abs_mul, hp, abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ r)]
  have := Real.abs_cos_le_one (r * γ₀ * Real.log 2)
  norm_num
  nlinarith [pow_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (3 / 4 : ℝ)) r]

/-- **II.2(b) with Euler weights.**  On `Re s > 3/4`,
`F₀(s) = Π_{m} (1 - 2^{-ms})^{-w_m}` with the real Euler weights `w_m` of `w̃`, and
`|w_m| ≤ 2 · 2^{3m/4}`. -/
theorem hasProd_signedPoly (γ₀ : ℝ) {s : ℂ} (hs : 3 / 4 < s.re) :
    HasProd (fun m : ℕ => (1 - (2 : ℂ) ^ (-((m : ℂ) * s))) ^
      (-(eulerWeight (signedWeight γ₀) m : ℂ))) (signedPoly γ₀ s) := by
  set a : ℝ := (2 : ℝ) ^ (3 / 4 : ℝ) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow (by norm_num) (by norm_num)
  set z : ℂ := (2 : ℂ) ^ (-s) with hz
  have hzn : ‖z‖ = (2 : ℝ) ^ (-s.re) := by rw [hz, norm_two_cpow, Complex.neg_re]
  have hq : a * ‖z‖ < 1 := by
    rw [hzn, ha, ← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hW0 : signedWeight γ₀ 0 = 0 := by simp [signedWeight]
  have hS := hasSum_eulerWeight_neg_log hW0 ha1 (abs_mul_signedWeight_le γ₀) hq
  have hpow : ∀ m : ℕ, z ^ m = (2 : ℂ) ^ (-((m : ℂ) * s)) := by
    intro m; rw [hz, ← Complex.cpow_nat_mul]; ring_nf
  -- the prime-power series of `F₀`
  have hser : ∑' r : ℕ, (signedWeight γ₀ r : ℂ) * z ^ r = ∑' r : ℕ, (signedWeight γ₀ (r + 1) : ℂ) *
      (2 : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s)) := by
    have hsm : Summable fun r : ℕ => (signedWeight γ₀ r : ℂ) * z ^ r := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity) hq).mul_left 2)
        fun r => ?_
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp [hW0]
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, mul_pow]
      have h := abs_mul_signedWeight_le γ₀ r
      rw [abs_mul, Nat.abs_cast] at h
      have : |signedWeight γ₀ r| ≤ 2 * a ^ r := le_trans (le_mul_of_one_le_left (abs_nonneg _) hr1) h
      calc |signedWeight γ₀ r| * ‖z‖ ^ r ≤ 2 * a ^ r * ‖z‖ ^ r := by gcongr
        _ = 2 * (a ^ r * ‖z‖ ^ r) := by ring
    rw [hsm.tsum_eq_zero_add]
    simp only [hW0, Complex.ofReal_zero, zero_mul, zero_add]
    exact tsum_congr fun r => by rw [hpow]
  have hexp := hS.cexp
  rw [hser, ← signedPoly_eq_exp γ₀ hs] at hexp
  refine hexp.congr_fun fun m => ?_
  simp only [Function.comp_apply]
  rw [← hpow]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [eulerWeight]
  have hne : 1 - z ^ m ≠ 0 := by
    intro h
    have h1 : ‖z ^ m‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_pow] at h1
    have hz1 : ‖z‖ < 1 := by nlinarith [norm_nonneg z]
    exact absurd h1 (pow_lt_one₀ (norm_nonneg z) hz1 hm.ne').ne
  rw [Complex.cpow_def_of_ne_zero hne]
  ring_nf

end GaloisForLFunctions.EulerFETransportTheory
