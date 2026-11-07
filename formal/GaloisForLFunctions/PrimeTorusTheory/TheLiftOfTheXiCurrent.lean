import GaloisForLFunctions.PrimeTorusTheory.CertificatesOnTheOrbit
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiRealAxisCompletedLog
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivThreeFourOne

/-!
# The lift of the Ξ-current

The Ξ-current at `s = σ + it` is `J(s) = 2 Re(ξ'(s) conj ξ(s)) = ∂_σ |ξ(σ + it)|²`. For `σ > 1` it is the restriction to the orbit of a function on `X = ℝ × 𝔻^∞`:

`𝒥_σ(t, ω) = 2|ξ(σ + it)|² (B(σ + it) − Σ_n Λ(n) n^{−σ} Re ω(n))`,

with the archimedean base `B(s) = Re(1/s + 1/(s − 1) − ½ log π + ½ ψ(s/2))`. At the orbit point `ω(n) = n^{−it}` it is the current (`xiCurrent_eq_xiLift`).

**The worst point of every fibre is the pole.** For `‖ω(n)‖ ≤ 1` the column is at most its value at the start of the orbit, `ω = 1`, which is `−ζ'/ζ(σ)` (`lamColumn_le_pole`, `lamColumn_pole_eq`). So the lift is nonnegative on the whole fibre over `t` if and only if the base pays the size, `−ζ'/ζ(σ) ≤ B(σ + it)` (`xiLift_nonneg_iff`), and then the current is nonnegative at height `t` (`xiCurrent_nonneg_of_size_le`).

This answers the fourth question of the field for the actual current: a frozen sum-of-squares certificate of `𝒥_σ` exists exactly above the size curve, and its extremal point is the pole. Below the curve a certificate frozen on a window past the Kronecker time still costs size (`frozen_certificate_costs_size`), and one whose coefficients vary freely with `t` is the tautological graph lift (`graph_lift`).
-/

open Complex ArithmeticFunction

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The Ξ-current `2 Re(ξ'(s) conj ξ(s))`. -/
def xiCurrent (s : ℂ) : ℝ :=
  2 * (deriv RiemannGaussian.riemannXi s * starRingEnd ℂ (RiemannGaussian.riemannXi s)).re

/-- The archimedean base `Re(1/s + 1/(s − 1) − ½ log π + ½ ψ(s/2))`. -/
def xiBase (s : ℂ) : ℝ :=
  (1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 + Complex.digamma (s / 2) / 2).re

/-- The von Mangoldt column `Σ_n Λ(n) n^{−σ} Re ω(n)` of a point of the polydisc. -/
def lamColumn (σ : ℝ) (ω : ℕ → ℂ) : ℝ := ∑' n, (Λ n : ℝ) * (n : ℝ) ^ (-σ) * (ω n).re

/-- The lift of the Ξ-current to `X`. -/
def xiLift (σ t : ℝ) (ω : ℕ → ℂ) : ℝ :=
  2 * ‖RiemannGaussian.riemannXi ⟨σ, t⟩‖ ^ 2 * (xiBase ⟨σ, t⟩ - lamColumn σ ω)

theorem summable_vonMangoldt_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => (Λ n : ℝ) * (n : ℝ) ^ (-σ) := by
  have h := LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  have h2 : Summable fun n => ‖LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) (σ : ℂ) n‖ :=
    summable_norm_iff.mpr h
  refine h2.congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem summable_lamColumn {σ : ℝ} (hσ : 1 < σ) {ω : ℕ → ℂ} (hω : ∀ n, ‖ω n‖ ≤ 1) :
    Summable fun n : ℕ => (Λ n : ℝ) * (n : ℝ) ^ (-σ) * (ω n).re := by
  refine Summable.of_norm_bounded (summable_vonMangoldt_rpow hσ) fun n => ?_
  have h0 : 0 ≤ (Λ n : ℝ) * (n : ℝ) ^ (-σ) := mul_nonneg vonMangoldt_nonneg (by positivity)
  rw [norm_mul, Real.norm_of_nonneg h0]
  have h1 : ‖(ω n).re‖ ≤ 1 := (Complex.abs_re_le_norm _).trans (hω n)
  nlinarith [norm_nonneg (ω n).re]

/-- **The worst point of every fibre is the pole.** -/
theorem lamColumn_le_pole {σ : ℝ} (hσ : 1 < σ) {ω : ℕ → ℂ} (hω : ∀ n, ‖ω n‖ ≤ 1) :
    lamColumn σ ω ≤ lamColumn σ fun _ => 1 := by
  refine hasSum_le (fun n => ?_) (summable_lamColumn hσ hω).hasSum
    (summable_lamColumn hσ fun _ => by simp).hasSum
  have h0 : 0 ≤ (Λ n : ℝ) * (n : ℝ) ^ (-σ) := mul_nonneg vonMangoldt_nonneg (by positivity)
  have h1 : (ω n).re ≤ 1 := (Complex.re_le_norm _).trans (hω n)
  simpa using mul_le_mul_of_nonneg_left h1 h0

/-- The real part of `n^{−it}` is `cos(t log n)`. -/
theorem re_orbitPoint {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (orbitPoint t n).re = Real.cos (Real.log n * t) := by
  have h1 : orbitPoint t n = (n : ℂ) ^ (-((t : ℂ) * I)) := if_neg hn
  rw [h1, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [show (Real.log n : ℂ) * -((t : ℂ) * I) = ((-(Real.log n * t) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- On `Re s > 1` the real part of `Σ Λ(n) n^{−s}` is the column at the orbit point. -/
theorem re_LSeries_vonMangoldt {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (LSeries (fun n => ((Λ n : ℝ) : ℂ)) ⟨σ, t⟩).re = lamColumn σ (orbitPoint t) := by
  have hs : 1 < (⟨σ, t⟩ : ℂ).re := hσ
  rw [LSeries, Complex.re_tsum (LSeriesSummable_vonMangoldt hs)]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [RHTower.Sieve.re_lseries_term_vonMangoldt hn, re_orbitPoint hn t,
      Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
    show (Λ n : ℝ) * (Real.exp (-Real.log n * σ) * Real.cos (Real.log n * t)) = _
    rw [show Real.log n * -σ = -Real.log n * σ by ring]
    ring

theorem riemannXi_ne_zero {s : ℂ} (hs : 1 < s.re) : RiemannGaussian.riemannXi s ≠ 0 := by
  rw [RiemannGaussian.riemannXi_eq_mul_Gammaℝ_riemannZeta_of_one_lt_re hs]
  have h0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have h1 : 1 - s ≠ 0 := fun h => by
    have : s = 1 := by linear_combination -h
    rw [this] at hs
    simp at hs
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)))
    (riemannZeta_ne_zero_of_one_lt_re hs)

/-- **The current is the restriction of its lift.** For `σ > 1`, `J(σ + it) = 𝒥_σ(t, n^{−it})`. -/
theorem xiCurrent_eq_xiLift {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    xiCurrent ⟨σ, t⟩ = xiLift σ t (orbitPoint t) := by
  set s : ℂ := ⟨σ, t⟩ with hsdef
  have hs : 1 < s.re := hσ
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hξ := riemannXi_ne_zero hs
  have hlog := RiemannGaussian.logDeriv_riemannXi_of_re_pos_of_riemannZeta_ne_zero
    (by linarith : 0 < s.re) hs1 hζ
  have hζlog : logDeriv riemannZeta s = -LSeries (fun n => ((Λ n : ℝ) : ℂ)) s := by
    rw [logDeriv_apply, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div, neg_neg]
  -- `ξ' conj ξ = (ξ'/ξ) |ξ|²`.
  have hcur : xiCurrent s = 2 * ‖RiemannGaussian.riemannXi s‖ ^ 2 *
      (logDeriv RiemannGaussian.riemannXi s).re := by
    unfold xiCurrent
    have e : deriv RiemannGaussian.riemannXi s * starRingEnd ℂ (RiemannGaussian.riemannXi s) =
        logDeriv RiemannGaussian.riemannXi s * ((‖RiemannGaussian.riemannXi s‖ ^ 2 : ℝ) : ℂ) := by
      rw [logDeriv_apply, Complex.ofReal_pow, ← Complex.mul_conj', div_mul_eq_mul_div, mul_assoc,
        mul_div_assoc, mul_div_cancel_left₀ _ hξ]
    rw [e, Complex.re_mul_ofReal]
    ring
  rw [hcur, hlog, hζlog]
  unfold xiLift
  rw [← re_LSeries_vonMangoldt hσ t]
  unfold xiBase
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, ← hsdef]
  ring

/-- The value of the column at the pole is `−ζ'/ζ(σ)`. -/
theorem lamColumn_pole_eq {σ : ℝ} (hσ : 1 < σ) :
    lamColumn σ (fun _ => 1) = -(deriv riemannZeta σ / riemannZeta σ).re := by
  have h := re_LSeries_vonMangoldt hσ 0
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have e1 : (⟨σ, 0⟩ : ℂ) = (σ : ℂ) := Complex.ext rfl rfl
  rw [e1, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div, Complex.neg_re] at h
  rw [h]
  unfold lamColumn
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [re_orbitPoint hn, mul_zero, Real.cos_zero]
    simp

/-- **Torus positivity of the lift is size.** The lift is nonnegative on the whole fibre over `t` iff the base pays the column at the pole. -/
theorem xiLift_nonneg_iff {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∀ ω : ℕ → ℂ, (∀ n, ‖ω n‖ ≤ 1) → 0 ≤ xiLift σ t ω) ↔
      lamColumn σ (fun _ => 1) ≤ xiBase ⟨σ, t⟩ := by
  have hpos : 0 < 2 * ‖RiemannGaussian.riemannXi ⟨σ, t⟩‖ ^ 2 := by
    have := riemannXi_ne_zero (s := ⟨σ, t⟩) hσ
    positivity
  constructor
  · intro h
    have h1 := h (fun _ => 1) fun _ => by simp
    unfold xiLift at h1
    have := (mul_nonneg_iff_of_pos_left hpos).mp h1
    linarith
  · intro h ω hω
    unfold xiLift
    have := lamColumn_le_pole hσ hω
    exact mul_nonneg hpos.le (by linarith)

/-- Above the size curve the current is nonnegative. -/
theorem xiCurrent_nonneg_of_size_le {σ : ℝ} (hσ : 1 < σ) {t : ℝ}
    (h : -(deriv riemannZeta σ / riemannZeta σ).re ≤ xiBase ⟨σ, t⟩) : 0 ≤ xiCurrent ⟨σ, t⟩ := by
  rw [xiCurrent_eq_xiLift hσ t]
  rw [← lamColumn_pole_eq hσ] at h
  exact (xiLift_nonneg_iff hσ t).mpr h (orbitPoint t) (norm_orbitPoint_le t)

end

end GaloisForLFunctions.PrimeTorusTheory
