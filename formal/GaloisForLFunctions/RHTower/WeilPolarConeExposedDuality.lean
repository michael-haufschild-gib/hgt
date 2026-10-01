import GaloisForLFunctions.RHTower.WeilPositivityLinearDuality
import GaloisForLFunctions.RHTower.WeilPolarConeExposedPoint

/-!
# RH as Weil positivity on one exposing ray beyond the prime-blind tests

Let `K_c = P_c P_c (Φ ⋆ Φ̃)` be the polar exposing kernels of Riemann's kernel and
`w(n) = Σ_k 2^{−k} (K_{1/(k+1)}(log n) + K_{1/(k+1)}(−log n))` the exposing weight
(`exposingWeight`). The exposing functional of the polar Weil cone is
`ℓ̄(v) = Σ_{n ≥ 2} v(n) n^{−1/2} w(n)` (`polarExposingFunctional_eq_tsum`).

**Theorem** (`riemannHypothesis_iff_forall_weilDualBound_exposing`). RH holds iff for every
cutoff `N` and every level `A` with `N ≤ e^{2A}`, every finite family of polar tests at levels
`≤ A`, with weights `α ≥ 0`, whose prime-atom coefficients equal `t · w(n)` for `n ≤ N` and vanish
for `N < n ≤ e^{2A}` (`t ≥ 0`), has archimedean energy at least `t (ℓ̄(Λ) − τ_N)`. Here
`τ_N = Σ_{n > N} (log n + C₀)|w(n)|` is the box tail (`exposingTail`), which tends to `0`.

The case `t = 0` is positivity of the archimedean energy on prime-blind families, which by linear
duality is equivalent to the existence of a Weil-positive weight system. The theorem says that
one further ray of prime traces, the exposing weight `w`, upgrades existence to RH.

* `⇒`: RH makes `Λ` Weil-positive, and weak duality applies to `Λ`.
**Prime-free form** (`riemannHypothesis_iff_forall_weilDualBound_archimedean`). The threshold
`ℓ̄(Λ)` equals `E = Σ_k 2^{−k} lim_L A(P_{c_k}(Φχ_L))/(2π)`, a limit of archimedean energies of
explicit Riemann-kernel tests (`archimedeanExposingThreshold_eq`). The energy split
`A(f) = 2π W(f,f) + 2π T_Λ(f)` holds on polar tests, and the zero side of `P_c(Φχ_L)` tends to `0`.
So RH is an inequality family among archimedean energies, Riemann's kernel and the values of tests
at `log n`; no prime and no zero occurs in its statement.

* `⇐`: linear duality at every cutoff gives Weil-positive `lam_N` with
  `ℓ̄(lam_N) ≥ ℓ̄(Λ) − 2τ_N`. The level-wise box `|lam(n)| ≤ √n (log n + C₀)` puts all of them in
  a compact product; a pointwise limit `lam` is Weil-positive and has `ℓ̄(lam) ≥ ℓ̄(Λ)` by
  dominated convergence. Exposedness of `Λ` then gives `lam = Λ`, hence RH.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## The exposing weight -/

/-- The exposing weight `w(n) = Σ_k 2^{−k} (K_k(log n) + K_k(−log n))`, `K_k = P_c P_c (Φ ⋆ Φ̃)`
at `c = 1/(k+1)`. -/
def exposingWeight (n : ℕ) : ℝ :=
  ∑' k : ℕ, (1 / 2 : ℝ) ^ k * (polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n) +
    polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n))

/-- A uniform exponential decay bound for the polar exposing kernels. -/
theorem exists_abs_polarExposingKernel_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (k : ℕ) (y : ℝ),
      |polarExposingKernel (1 / ((k : ℝ) + 1)) y| ≤ D * Real.exp (-(2 * |y|)) := by
  obtain ⟨-, C₂, -, hC₂, -, hK⟩ := exists_riemannKernelAutocorr_decay
  refine ⟨C₂ * (1 + Real.exp 2) ^ 2, by positivity, fun k y => ?_⟩
  have hc : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
  have hc1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hm : (1 + 2 * polarWeight (1 / ((k : ℝ) + 1)) * Real.exp (2 * (1 / ((k : ℝ) + 1)))) ^ 2 ≤
      (1 + Real.exp 2) ^ 2 := by
    have h1 := polarWeight_le_half (1 / ((k : ℝ) + 1))
    have h2 : Real.exp (2 * (1 / ((k : ℝ) + 1))) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (by linarith)
    have h3 := polarWeight_pos (1 / ((k : ℝ) + 1))
    have h4 : 0 ≤ 2 * polarWeight (1 / ((k : ℝ) + 1)) * Real.exp (2 * (1 / ((k : ℝ) + 1))) := by
      positivity
    have h5 : 2 * polarWeight (1 / ((k : ℝ) + 1)) * Real.exp (2 * (1 / ((k : ℝ) + 1))) ≤
        Real.exp 2 := by nlinarith [Real.exp_pos (2 * (1 / ((k : ℝ) + 1)))]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  refine (abs_polarShift_polarShift_le hc hK y).trans ?_
  gcongr

/-- `e^{−2|log n|} = n^{−2}` for `n ≥ 1`. -/
theorem exp_neg_two_abs_log_eq {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(2 * |Real.log n|)) = 1 / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [abs_of_nonneg hlog, Real.exp_neg, show 2 * Real.log n = Real.log ((n : ℝ) ^ 2) by
    rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]

/-- The terms of the exposing weight are dominated by `2D n^{−2} 2^{−k}`. -/
theorem abs_exposingWeight_term_le {D : ℝ}
    (hD : ∀ (k : ℕ) (y : ℝ), |polarExposingKernel (1 / ((k : ℝ) + 1)) y| ≤ D * Real.exp (-(2 * |y|)))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    |(1 / 2 : ℝ) ^ k * (polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n) +
      polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n))| ≤
      (1 / 2 : ℝ) ^ k * (2 * D / (n : ℝ) ^ 2) := by
  rw [abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 := hD k (Real.log n)
  have h2 := hD k (-Real.log n)
  rw [abs_neg, exp_neg_two_abs_log_eq hn] at h2
  rw [exp_neg_two_abs_log_eq hn] at h1
  calc _ ≤ |polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n)| +
        |polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n)| := abs_add_le _ _
    _ ≤ D * (1 / (n : ℝ) ^ 2) + D * (1 / (n : ℝ) ^ 2) := add_le_add h1 h2
    _ = 2 * D / (n : ℝ) ^ 2 := by ring

theorem summable_exposingWeight_term (n : ℕ) :
    Summable fun k : ℕ => (1 / 2 : ℝ) ^ k * (polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n) +
      polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n)) := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_polarExposingKernel_le
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).mul_right (2 * D)) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 := hD k (Real.log n)
  have h2 := hD k (-Real.log n)
  have he : Real.exp (-(2 * |Real.log n|)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := abs_nonneg (Real.log n); linarith)
  rw [abs_neg] at h2
  calc _ ≤ |polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n)| +
        |polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n)| := abs_add_le _ _
    _ ≤ D * Real.exp (-(2 * |Real.log n|)) + D * Real.exp (-(2 * |Real.log n|)) := add_le_add h1 h2
    _ ≤ D * 1 + D * 1 := by gcongr
    _ = 2 * D := by ring

/-- `|w(n)| ≤ 4D n^{−2}` for `n ≥ 1`. -/
theorem exists_abs_exposingWeight_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n → |exposingWeight n| ≤ 4 * D / (n : ℝ) ^ 2 := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_polarExposingKernel_le
  refine ⟨D, hD0, fun n hn => ?_⟩
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hb : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k * (2 * D / (n : ℝ) ^ 2) := hg.mul_right _
  unfold exposingWeight
  calc |∑' k : ℕ, _| ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k * (2 * D / (n : ℝ) ^ 2) := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded hb.hasSum fun k => by
          rw [Real.norm_eq_abs]; exact abs_exposingWeight_term_le hD hn k
    _ = 4 * D / (n : ℝ) ^ 2 := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

/-! ## The exposing functional as a weighted prime sum -/

/-- The atom coefficient `v(n) n^{−1/2}` on `n ≥ 2`. -/
def atomCoeffOf (v : ℕ → ℝ) (n : ℕ) : ℝ := if 2 ≤ n then v n / Real.sqrt n else 0

/-- **The exposing functional is a weighted prime sum:** `ℓ̄(v) = Σ_n v(n) n^{−1/2} w(n)`. -/
theorem polarExposingFunctional_eq_tsum {v : ℕ → ℝ}
    (hv2 : Summable fun n : ℕ => |v n| / (n : ℝ) ^ 2) :
    polarExposingFunctional v = ∑' n : ℕ, atomCoeffOf v n * exposingWeight n := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_polarExposingKernel_le
  set g : ℕ → ℕ → ℝ := fun k n => (1 / 2 : ℝ) ^ k *
    (atomCoeffOf v n * (polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n) +
      polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n))) with hg
  have hgeo := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hbound : ∀ k n, |g k n| ≤ (1 / 2 : ℝ) ^ k * (2 * D * (|v n| / (n : ℝ) ^ 2)) := by
    intro k n
    simp only [hg, atomCoeffOf]
    split_ifs with h2
    · have hn1 : 1 ≤ n := by omega
      have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
      have hterm := abs_exposingWeight_term_le hD hn1 k
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k), abs_mul]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k)] at hterm
      have hk : |polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n) +
          polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n)| ≤ 2 * D / (n : ℝ) ^ 2 :=
        le_of_mul_le_mul_left hterm (by positivity)
      have hdiv : |v n / Real.sqrt n| ≤ |v n| := by
        rw [abs_div, abs_of_pos (show 0 < Real.sqrt n by linarith)]
        exact div_le_self (abs_nonneg _) hsq
      calc (1 / 2 : ℝ) ^ k * (|v n / Real.sqrt n| *
            |polarExposingKernel (1 / ((k : ℝ) + 1)) (Real.log n) +
              polarExposingKernel (1 / ((k : ℝ) + 1)) (-Real.log n)|)
          ≤ (1 / 2 : ℝ) ^ k * (|v n| * (2 * D / (n : ℝ) ^ 2)) := by gcongr
        _ = (1 / 2 : ℝ) ^ k * (2 * D * (|v n| / (n : ℝ) ^ 2)) := by ring
    · simp only [zero_mul, mul_zero, abs_zero]; positivity
  have hprod : Summable fun p : ℕ × ℕ => (1 / 2 : ℝ) ^ p.1 * (2 * D * (|v p.2| / (p.2 : ℝ) ^ 2)) :=
    hgeo.mul_of_nonneg (hv2.mul_left (2 * D)) (fun _ => by positivity) (fun _ => by positivity)
  have hunc : Summable (Function.uncurry g) :=
    Summable.of_norm_bounded hprod fun p => by
      rw [Real.norm_eq_abs]; exact hbound p.1 p.2
  have hrow : ∀ k : ℕ, (1 / 2 : ℝ) ^ k * atomPairing v (polarExposingKernel (1 / ((k : ℝ) + 1))) =
      ∑' n : ℕ, g k n := by
    intro k
    simp only [hg, atomPairing, atomCoeffOf]
    rw [tsum_mul_left]
  have hcol : ∀ n : ℕ, ∑' k : ℕ, g k n = atomCoeffOf v n * exposingWeight n := by
    intro n
    simp only [hg, exposingWeight]
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  unfold polarExposingFunctional
  rw [tsum_congr hrow, ← hunc.tsum_comm]
  exact tsum_congr hcol

/-! ## The box and its tail -/

theorem boxConst_nonneg : 0 ≤ boxConst := by
  unfold boxConst
  have := ResonatorProfile.profileRatio_nonneg
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  positivity

/-- Weil-positive weights lie in the box at every `n ≥ 2`. -/
theorem abs_le_boxWidth_of_weilPositive {lam : ℕ → ℝ} (hW : WeilPositive lam) {n : ℕ}
    (hn : 2 ≤ n) : |lam n| ≤ boxWidth n :=
  abs_le_boxWidth_of_weilPositiveUpTo (A := atomLevel n)
    (fun a ha _ f hf hfs hp hm => hW a ha f hf hfs hp hm) hn le_rfl

/-- The von Mangoldt weights lie in the box. -/
theorem vonMangoldt_le_boxWidth {n : ℕ} (hn : 2 ≤ n) :
    |(ArithmeticFunction.vonMangoldt n : ℝ)| ≤ boxWidth n := by
  have hn1 : 1 ≤ n := by omega
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have h1 : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h2 := boxWidth_div_sqrt hn
  have hs0 : 0 < Real.sqrt n := by linarith
  rw [div_eq_iff hs0.ne'] at h2
  rw [h2]
  have := boxConst_nonneg
  nlinarith

/-- The box majorant `b(n) = (log n + C₀) |w(n)|` of the exposing terms, on `n ≥ 2`. -/
def exposingMajorant (n : ℕ) : ℝ := if 2 ≤ n then (Real.log n + boxConst) * |exposingWeight n| else 0

theorem exposingMajorant_nonneg (n : ℕ) : 0 ≤ exposingMajorant n := by
  unfold exposingMajorant
  split_ifs with h
  · have := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
    have := boxConst_nonneg
    positivity
  · exact le_rfl

theorem summable_exposingMajorant : Summable exposingMajorant := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_exposingWeight_le
  have hp : Summable fun n : ℕ => (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  refine Summable.of_nonneg_of_le exposingMajorant_nonneg (fun n => ?_)
    (hp.mul_left (4 * D * (2 + boxConst)))
  unfold exposingMajorant
  split_ifs with h2
  · have hn1 : 1 ≤ n := by omega
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≤ 2 * Real.sqrt n := by
      have h := Real.log_le_rpow_div (x := (n : ℝ)) (ε := 1 / 2) hn0.le (by norm_num)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    have hsq1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
    have hC := boxConst_nonneg
    have hpow : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    have hw := hD n hn1
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hA : Real.log n + boxConst ≤ (2 + boxConst) * Real.sqrt n := by nlinarith
    rw [hpow]
    calc (Real.log n + boxConst) * |exposingWeight n|
        ≤ ((2 + boxConst) * Real.sqrt n) * (4 * D / (n : ℝ) ^ 2) := by
          gcongr
      _ = 4 * D * (2 + boxConst) * (Real.sqrt n / (n : ℝ) ^ 2) := by ring
      _ = 4 * D * (2 + boxConst) * ((n : ℝ) * Real.sqrt n)⁻¹ := by
          congr 1
          have hs0 : 0 < Real.sqrt n := by linarith
          field_simp
          exact Real.sq_sqrt hn0.le
  · have : 0 ≤ (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by positivity
    have := hD0
    have := boxConst_nonneg
    positivity

/-- Box-bounded weights have exposing terms dominated by the majorant. -/
theorem abs_atomCoeffOf_mul_le {lam : ℕ → ℝ} (hbox : ∀ n, 2 ≤ n → |lam n| ≤ boxWidth n) (n : ℕ) :
    |atomCoeffOf lam n * exposingWeight n| ≤ exposingMajorant n := by
  unfold atomCoeffOf exposingMajorant
  split_ifs with h2
  · have hn1 : 1 ≤ n := by omega
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    rw [abs_mul, abs_div, abs_of_pos hs0, ← boxWidth_div_sqrt h2]
    gcongr
    exact hbox n h2
  · simp

theorem summable_atomCoeffOf_mul {lam : ℕ → ℝ} (hbox : ∀ n, 2 ≤ n → |lam n| ≤ boxWidth n) :
    Summable fun n => atomCoeffOf lam n * exposingWeight n :=
  Summable.of_norm_bounded summable_exposingMajorant fun n => by
    rw [Real.norm_eq_abs]; exact abs_atomCoeffOf_mul_le hbox n

/-- The exposing value `ℓ̄(lam) = Σ_n lam(n) n^{−1/2} w(n)`. -/
def exposingValue (lam : ℕ → ℝ) : ℝ := ∑' n : ℕ, atomCoeffOf lam n * exposingWeight n

/-- The box tail `τ_N = Σ_{n > N} (log n + C₀)|w(n)|`. -/
def exposingTail (N : ℕ) : ℝ := ∑' n : ℕ, if N < n then exposingMajorant n else 0

/-- The truncated exposing weight `w · 1_{n ≤ N}`. -/
def exposingWeightTrunc (N : ℕ) (n : ℕ) : ℝ := if n ≤ N then exposingWeight n else 0

theorem exposingWeightTrunc_eq_zero {N n : ℕ} (h : N < n) : exposingWeightTrunc N n = 0 := by
  unfold exposingWeightTrunc; rw [if_neg (by omega)]

theorem summable_exposingTail_terms (N : ℕ) :
    Summable fun n : ℕ => if N < n then exposingMajorant n else 0 :=
  Summable.of_nonneg_of_le (fun n => by split_ifs <;> [exact exposingMajorant_nonneg n; exact le_rfl])
    (fun n => by split_ifs <;> [exact le_rfl; exact exposingMajorant_nonneg n]) summable_exposingMajorant

/-- The box tail tends to `0`. -/
theorem tendsto_exposingTail : Tendsto exposingTail atTop (𝓝 0) := by
  have hsplit : ∀ N : ℕ, exposingTail N =
      (∑' n : ℕ, exposingMajorant n) - ∑ n ∈ Finset.range (N + 1), exposingMajorant n := by
    intro N
    have hfin : ∑' n : ℕ, (if n ≤ N then exposingMajorant n else 0) =
        ∑ n ∈ Finset.range (N + 1), exposingMajorant n := by
      rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
        rw [Finset.mem_range, not_lt] at hn; rw [if_neg (by omega)])]
      exact Finset.sum_congr rfl fun n hn => by
        rw [if_pos (by rw [Finset.mem_range] at hn; omega)]
    have hs1 : Summable fun n : ℕ => if n ≤ N then exposingMajorant n else 0 :=
      summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => by
        rw [Finset.mem_range, not_lt] at hn; rw [if_neg (by omega)]
    have hadd := hs1.tsum_add (summable_exposingTail_terms N)
    have heq : (fun n : ℕ => (if n ≤ N then exposingMajorant n else 0) +
        (if N < n then exposingMajorant n else 0)) = exposingMajorant := by
      funext n
      by_cases h : n ≤ N
      · rw [if_pos h, if_neg (by omega), add_zero]
      · rw [if_neg h, if_pos (by omega), zero_add]
    rw [heq, hfin] at hadd
    unfold exposingTail
    linarith
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), exposingMajorant n) atTop
      (𝓝 (∑' n : ℕ, exposingMajorant n)) :=
    summable_exposingMajorant.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have := (tendsto_const_nhds (x := ∑' n : ℕ, exposingMajorant n)).sub hlim
  rw [sub_self] at this
  exact this.congr fun N => (hsplit N).symm

/-- **Truncation error.** For box-bounded weights, the cutoff-`N` exposing sum differs from
`ℓ̄(lam)` by at most the tail `τ_N`. -/
theorem abs_exposingValue_sub_linearWeightSum_le {lam : ℕ → ℝ}
    (hbox : ∀ n, 2 ≤ n → |lam n| ≤ boxWidth n) (N : ℕ) :
    |exposingValue lam - linearWeightSum N (exposingWeightTrunc N) lam| ≤ exposingTail N := by
  set f : ℕ → ℝ := fun n => atomCoeffOf lam n * exposingWeight n with hf
  have hfs : Summable f := summable_atomCoeffOf_mul hbox
  have hlin : linearWeightSum N (exposingWeightTrunc N) lam = ∑ n ∈ Finset.range (N + 1), f n := by
    unfold linearWeightSum
    have h1 : ∑ n ∈ Finset.range (N + 1), f n = ∑ n ∈ Finset.Icc 2 N, f n := by
      symm
      refine Finset.sum_subset (fun n hn => by
        rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega) fun n hn hn' => ?_
      simp only [hf, atomCoeffOf]
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Icc] at hn'
      rw [if_neg (by omega), zero_mul]
    rw [h1]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp only [hf, atomCoeffOf, exposingWeightTrunc]
    rw [if_pos hn.1, if_pos hn.2]
  have hs1 : Summable fun n : ℕ => if n ≤ N then f n else 0 :=
    summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => by
      rw [Finset.mem_range, not_lt] at hn; rw [if_neg (by omega)]
  have hs2 : Summable fun n : ℕ => if N < n then f n else 0 :=
    Summable.of_norm_bounded (summable_exposingTail_terms N) fun n => by
      rw [Real.norm_eq_abs]
      split_ifs
      · exact abs_atomCoeffOf_mul_le hbox n
      · simp
  have hfin : ∑' n : ℕ, (if n ≤ N then f n else 0) = ∑ n ∈ Finset.range (N + 1), f n := by
    rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
      rw [Finset.mem_range, not_lt] at hn; rw [if_neg (by omega)])]
    exact Finset.sum_congr rfl fun n hn => by
      rw [if_pos (by rw [Finset.mem_range] at hn; omega)]
  have hadd := hs1.tsum_add hs2
  have heq : (fun n : ℕ => (if n ≤ N then f n else 0) + (if N < n then f n else 0)) = f := by
    funext n
    by_cases h : n ≤ N
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [heq, hfin] at hadd
  have hdiff : exposingValue lam - linearWeightSum N (exposingWeightTrunc N) lam =
      ∑' n : ℕ, (if N < n then f n else 0) := by
    unfold exposingValue
    rw [hlin]
    change ∑' n, f n - _ = _
    linarith
  rw [hdiff, ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (summable_exposingTail_terms N).hasSum fun n => ?_
  rw [Real.norm_eq_abs]
  split_ifs
  · exact abs_atomCoeffOf_mul_le hbox n
  · simp

/-! ## Closedness of the Weil cone -/

/-- **The polar Weil cone is closed under pointwise limits on `n ≥ 2`.** -/
theorem weilPositive_of_tendsto {l : ℕ → ℕ → ℝ} {lam₀ : ℕ → ℝ} (hW : ∀ j, WeilPositive (l j))
    (hlim : ∀ n, 2 ≤ n → Tendsto (fun j => l j n) atTop (𝓝 (lam₀ n))) : WeilPositive lam₀ := by
  intro a ha f hf hfs hp hm
  set M := ⌊Real.exp (2 * a)⌋₊ with hM
  set c : ℕ → ℝ := fun n => (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re
  set E : (ℕ → ℝ) → ℝ := fun l =>
    (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) -
      2 * π * ∑ n ∈ Finset.Icc 2 M, l n / Real.sqrt n * c n with hE
  have hEq : ∀ l, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol l M (τ / (2 * π)) = E l :=
    fun l => integral_weilAtomSymbol_eq_affine hf hfs l
  have hElim : Tendsto (fun j => E (l j)) atTop (𝓝 (E lam₀)) := by
    simp only [hE]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ (tendsto_finsetSum _ fun n hn => ?_))
    exact ((hlim n (Finset.mem_Icc.mp hn).1).div_const _).mul_const _
  rw [hEq]
  refine ge_of_tendsto' hElim fun j => ?_
  rw [← hEq]
  exact hW j a ha f hf hfs hp hm

/-! ## The dual criterion -/

/-- **The converse with any slack multiple.** If for every cutoff `N` and level `A` with
`N ≤ e^{2A}` the dual bound holds with threshold `ℓ̄(Λ) − c τ_N`, then RH holds. -/
theorem riemannHypothesis_of_forall_weilDualBound_exposing_mul {c : ℝ}
    (hD : ∀ (N : ℕ) (A : ℝ), N ≤ ⌊Real.exp (2 * A)⌋₊ →
      WeilDualBound A (exposingWeightTrunc N)
        (exposingValue (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) - c * exposingTail N)) :
    RiemannHypothesis := by
  set Λv : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) with hΛv
  have hΛbox : ∀ n, 2 ≤ n → |Λv n| ≤ boxWidth n := fun n hn => vonMangoldt_le_boxWidth hn
  have hex : ∀ N : ℕ, ∃ lam : ℕ → ℝ, WeilPositive lam ∧
      exposingValue Λv - c * exposingTail N ≤ linearWeightSum N (exposingWeightTrunc N) lam :=
    fun N => (exists_weilPositive_ge_iff_forall_weilDualBound
      (fun n hn => exposingWeightTrunc_eq_zero hn)).mpr fun A hA => hD N A hA
  choose l hl hβ using hex
  have hbox : ∀ N n, 2 ≤ n → |l N n| ≤ boxWidth n := fun N n hn =>
    abs_le_boxWidth_of_weilPositive (hl N) hn
  have hval : ∀ N, exposingValue Λv - (c + 1) * exposingTail N ≤ exposingValue (l N) := by
    intro N
    have h1 := abs_le.mp (abs_exposingValue_sub_linearWeightSum_le (hbox N) N)
    linarith [hβ N, h1.1]
  -- compactness in the box
  set clamp : ℕ → ℕ → ℝ := fun k n => max (-boxWidth n) (min (boxWidth n) (l k n)) with hclamp
  have hK : IsCompact (Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n)) :=
    isCompact_univ_pi fun n => isCompact_Icc
  have hmem : ∀ k, clamp k ∈ Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n) := by
    intro k n _
    have h0 : 0 ≤ boxWidth n := abs_nonneg _
    simp only [hclamp, mem_Icc]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  obtain ⟨lam₀, hlam₀, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hcoord : ∀ n, Tendsto (fun j => clamp (φ j) n) atTop (𝓝 (lam₀ n)) :=
    fun n => tendsto_pi_nhds.mp hlim n
  have hagree : ∀ k n, 2 ≤ n → clamp k n = l k n := by
    intro k n hn
    have hb := abs_le.mp (hbox k n hn)
    simp only [hclamp]
    rw [min_eq_right hb.2, max_eq_right hb.1]
  have hcoord' : ∀ n, 2 ≤ n → Tendsto (fun j => l (φ j) n) atTop (𝓝 (lam₀ n)) := fun n hn =>
    (hcoord n).congr fun j => hagree (φ j) n hn
  have hW₀ : WeilPositive lam₀ := weilPositive_of_tendsto (fun j => hl (φ j)) hcoord'
  have hbox₀ : ∀ n, 2 ≤ n → |lam₀ n| ≤ boxWidth n := fun n _ => abs_le.mpr (hlam₀ n trivial)
  -- dominated convergence of the exposing values
  have hconv : Tendsto (fun j => exposingValue (l (φ j))) atTop (𝓝 (exposingValue lam₀)) := by
    unfold exposingValue
    refine tendsto_tsum_of_dominated_convergence summable_exposingMajorant (fun n => ?_)
      (Eventually.of_forall fun j n => by
        rw [Real.norm_eq_abs]; exact abs_atomCoeffOf_mul_le (hbox (φ j)) n)
    unfold atomCoeffOf
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn]
      exact (((hcoord' n hn).div_const _).mul_const _)
    · simp only [if_neg hn, zero_mul]
      exact tendsto_const_nhds
  have htail : Tendsto (fun j => exposingTail (φ j)) atTop (𝓝 0) :=
    tendsto_exposingTail.comp hφ.tendsto_atTop
  have hge : exposingValue Λv ≤ exposingValue lam₀ := by
    have hsum := hconv.add (htail.const_mul (c + 1))
    rw [mul_zero, add_zero] at hsum
    exact ge_of_tendsto' hsum fun j => by linarith [hval (φ j)]
  -- exposedness
  have hw2 := summable_sub_vonMangoldt_div_sq_of_weilPositive hW₀
  have hexp : polarExposingFunctional (fun n => lam₀ n - ArithmeticFunction.vonMangoldt n) =
      exposingValue lam₀ - exposingValue Λv := by
    rw [polarExposingFunctional_eq_tsum hw2]
    unfold exposingValue
    rw [← (summable_atomCoeffOf_mul hbox₀).tsum_sub (summable_atomCoeffOf_mul hΛbox)]
    refine tsum_congr fun n => ?_
    simp only [atomCoeffOf, hΛv]
    split_ifs
    · ring
    · ring
  exact riemannHypothesis_iff_exists_weilPositive_polarExposing_nonneg.mpr
    ⟨lam₀, hW₀, by rw [hexp]; linarith⟩


/-- **RH is Weil positivity on one exposing ray.** RH holds iff for every cutoff `N` and level `A`
with `N ≤ e^{2A}`, every family of polar tests at levels `≤ A` whose prime-atom coefficients are a
nonnegative multiple `t` of the truncated exposing weight `w · 1_{n ≤ N}` has archimedean energy at
least `t (ℓ̄(Λ) − τ_N)`. -/
theorem riemannHypothesis_iff_forall_weilDualBound_exposing :
    RiemannHypothesis ↔ ∀ (N : ℕ) (A : ℝ), N ≤ ⌊Real.exp (2 * A)⌋₊ →
      WeilDualBound A (exposingWeightTrunc N)
        (exposingValue (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) - exposingTail N) := by
  set Λv : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) with hΛv
  have hΛbox : ∀ n, 2 ≤ n → |Λv n| ≤ boxWidth n := fun n hn => vonMangoldt_le_boxWidth hn
  constructor
  · intro hRH N A hA
    have hΛ := riemannHypothesis_iff_weilPositive_vonMangoldt.mp hRH
    have hβ : exposingValue Λv - exposingTail N ≤ linearWeightSum N (exposingWeightTrunc N) Λv := by
      have := abs_le.mp (abs_exposingValue_sub_linearWeightSum_le hΛbox N)
      linarith [this.2]
    exact (exists_weilPositive_ge_iff_forall_weilDualBound
      (fun n hn => exposingWeightTrunc_eq_zero hn)).mp ⟨Λv, hΛ, hβ⟩ A hA
  intro hD
  exact riemannHypothesis_of_forall_weilDualBound_exposing_mul (c := 1) fun N A hA => by
    simpa only [one_mul] using hD N A hA

/-! ## The threshold is archimedean -/

/-- The polar second difference of the truncated kernel as a test: its data at some level. -/
theorem exists_polarRiemannDifference_data (L : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∃ a : ℝ, 0 ≤ a ∧ ContDiff ℝ 2 (fun u => (polarRiemannDifferenceReal L c u : ℂ)) ∧
      tsupport (fun u => (polarRiemannDifferenceReal L c u : ℂ)) ⊆ Icc (-a) a ∧
      paperFT (fun u => (polarRiemannDifferenceReal L c u : ℂ)) (I / 2) = 0 ∧
      paperFT (fun u => (polarRiemannDifferenceReal L c u : ℂ)) (-(I / 2)) = 0 := by
  obtain ⟨a, ha, h1, h2, h3, h4⟩ := exists_polarPerturbed_test_data L hc 0 (H := fun _ => 0)
    contDiff_const HasCompactSupport.zero (by simp [paperFT]) (by simp [paperFT])
  simp only [zero_mul, add_zero] at h1 h2 h3 h4
  exact ⟨a, ha, h1, h2, h3, h4⟩

/-- **Energy split of the polar Riemann difference.** Its archimedean energy is `2π` times its
zero-side energy plus `2π` times its von Mangoldt atom pairing. -/
theorem archEnergy_polarRiemannDifference_eq (L : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    archEnergy (fun u => (polarRiemannDifferenceReal L c u : ℂ)) =
      2 * π * (zetaZeroConfig.W (fun u => (polarRiemannDifferenceReal L c u : ℂ))
        (fun u => (polarRiemannDifferenceReal L c u : ℂ))).re +
      2 * π * atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c)) := by
  obtain ⟨a, -, hF, hFs, hp1, hp2⟩ := exists_polarRiemannDifference_data L hc
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hF hFs hp1 hp2
  have h2 := integral_weilAtomSymbol_eq_archEnergy_sub hF hFs
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) le_rfl
  have hsum := atomPairing_eq_sum_of_support (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hF hFs
  have hre : (zetaZeroConfig.W (fun u => (polarRiemannDifferenceReal L c u : ℂ))
      (fun u => (polarRiemannDifferenceReal L c u : ℂ))).re =
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (fun u => (polarRiemannDifferenceReal L c u : ℂ)) τ‖ ^ 2 *
        weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊
          (τ / (2 * π)) := by
    rw [hWf, Complex.ofReal_re]
  have hatom : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        atomCoeff (fun u => (polarRiemannDifferenceReal L c u : ℂ)) n =
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c)) := hsum
  rw [hre, h2, hatom]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The archimedean energies of the polar Riemann differences converge to the von Mangoldt
exposing pairing:** `A(P_c(Φχ_L))/(2π) → ℓ_c(Λ)` as `L → ∞`. -/
theorem tendsto_archEnergy_polarRiemannDifference {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun L : ℝ => archEnergy (fun u => (polarRiemannDifferenceReal L c u : ℂ)) / (2 * π))
      atTop (𝓝 (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (polarExposingKernel c))) := by
  have hw2 : Summable fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ 2 := by
    refine summable_vonMangoldt_div_sq.congr fun n => ?_
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  obtain ⟨K, -, hK⟩ := exists_abs_atomPairing_polarAutocorr_sub_le hw2 hc
  have hatom := tendsto_of_abs_sub_le hK
  obtain ⟨Λd, -, hΛd⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hW : Tendsto (fun L : ℝ => (zetaZeroConfig.W (fun u => (polarRiemannDifferenceReal L c u : ℂ))
      (fun u => (polarRiemannDifferenceReal L c u : ℂ))).re) atTop (𝓝 0) := by
    have hb : Tendsto (fun L : ℝ => 9 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2))
        atTop (𝓝 0) := by simpa using tendsto_nearRadicalEnergy.const_mul 9
    refine squeeze_zero_norm (fun L => ?_) hb
    have h := norm_W_polarRiemannDifference_le L hc hΛd
    rw [polarRiemannDifference_eq] at h
    exact (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm _).trans h
  have hsum := hW.add hatom
  rw [zero_add] at hsum
  refine hsum.congr fun L => ?_
  rw [archEnergy_polarRiemannDifference_eq L hc]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

/-- The archimedean threshold `E = Σ_k 2^{−k} lim_L A(P_{c_k}(Φχ_L))/(2π)`, `c_k = 1/(k+1)`. Only
Riemann's kernel and the archimedean Weil symbol enter. -/
def archimedeanExposingThreshold : ℝ :=
  ∑' k : ℕ, (1 / 2 : ℝ) ^ k * limUnder atTop (fun L : ℝ =>
    archEnergy (fun u => (polarRiemannDifferenceReal L (1 / ((k : ℝ) + 1)) u : ℂ)) / (2 * π))

/-- The archimedean threshold equals the exposing value of the von Mangoldt weights. -/
theorem archimedeanExposingThreshold_eq :
    archimedeanExposingThreshold = exposingValue fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hw2 : Summable fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ 2 := by
    refine summable_vonMangoldt_div_sq.congr fun n => ?_
    rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  unfold exposingValue
  rw [← polarExposingFunctional_eq_tsum hw2]
  unfold archimedeanExposingThreshold polarExposingFunctional
  refine tsum_congr fun k => ?_
  rw [(tendsto_archEnergy_polarRiemannDifference (c := 1 / ((k : ℝ) + 1)) (by positivity)).limUnder_eq]

/-- **A prime-free form of RH.** RH holds iff for every cutoff `N` and level `A` with `N ≤ e^{2A}`,
every finite family of polar tests at levels `≤ A` whose atom coefficients are `t · w(n)` for
`n ≤ N` and vanish for `N < n ≤ e^{2A}` has archimedean energy at least `t (E − τ_N)`. Every
ingredient is prime-free:
* `w(n)` are values of Riemann-kernel autocorrelations at `±log n`;
* `E` is the archimedean energy limit of explicit Riemann-kernel tests;
* `τ_N` is an explicit box tail;
* the dual bound itself involves only archimedean energies and test values at `log n`. -/
theorem riemannHypothesis_iff_forall_weilDualBound_archimedean :
    RiemannHypothesis ↔ ∀ (N : ℕ) (A : ℝ), N ≤ ⌊Real.exp (2 * A)⌋₊ →
      WeilDualBound A (exposingWeightTrunc N) (archimedeanExposingThreshold - exposingTail N) := by
  rw [archimedeanExposingThreshold_eq]
  exact riemannHypothesis_iff_forall_weilDualBound_exposing

/-! ## Weil's criterion restricted to the exposing ray -/

/-- **Energy split of a polar test.** For a polar `C²` test at level `a` and any `M ≥ ⌊e^{2a}⌋`,
`A(f) = 2π Re W(f, f) + 2π Σ_{2 ≤ n ≤ M} Λ(n) n^{−1/2} c_n(f)`. -/
theorem archEnergy_eq_W_add_atoms {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0)
    {M : ℕ} (hM : ⌊Real.exp (2 * a)⌋₊ ≤ M) :
    archEnergy f = 2 * π * (zetaZeroConfig.W f f).re +
      2 * π * ∑ n ∈ Finset.Icc 2 M,
        (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * atomCoeff f n := by
  have hWf := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  have h2 := integral_weilAtomSymbol_eq_archEnergy_sub hf hfs
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) hM
  rw [hWf, Complex.ofReal_re, h2]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The restricted Weil bound.** Every family of polar tests at levels `≤ A` whose prime-atom
coefficients are `t · w` (`t ≥ 0`, weights `α ≥ 0`) has zero-side energy at least `−t s`. -/
def RestrictedWeilBound (A : ℝ) (w : ℕ → ℝ) (s : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℝ) (f : ι → ℝ → ℂ) (α : ι → ℝ) (t : ℝ),
    (∀ i, a i ≤ A) → (∀ i, IsPolarTest (a i) (f i)) → (∀ i, 0 ≤ α i) → 0 ≤ t →
    (∀ n : ℕ, 2 ≤ n → 2 * π * ∑ i, α i * atomCoeff (f i) n = t * w n) →
    -(t * s) ≤ 2 * π * ∑ i, α i * (zetaZeroConfig.W (f i) (f i)).re

/-- On a family matched to `t · w_N`, the archimedean energy is the zero-side energy plus
`t L_N(Λ)`. -/
theorem sum_archEnergy_eq_of_matched {A : ℝ} {N : ℕ} (hNA : N ≤ ⌊Real.exp (2 * A)⌋₊)
    {ι : Type} [Fintype ι] {a : ι → ℝ} {f : ι → ℝ → ℂ} {α : ι → ℝ} {t : ℝ}
    (ha : ∀ i, a i ≤ A) (hf : ∀ i, IsPolarTest (a i) (f i))
    (hmatch : ∀ n : ℕ, 2 ≤ n →
      2 * π * ∑ i, α i * atomCoeff (f i) n = t * exposingWeightTrunc N n) :
    ∑ i, α i * archEnergy (f i) =
      2 * π * ∑ i, α i * (zetaZeroConfig.W (f i) (f i)).re +
        t * linearWeightSum N (exposingWeightTrunc N)
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  set M := ⌊Real.exp (2 * A)⌋₊ with hMdef
  have hsplit : ∀ i, archEnergy (f i) = 2 * π * (zetaZeroConfig.W (f i) (f i)).re +
      2 * π * ∑ n ∈ Finset.Icc 2 M,
        (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * atomCoeff (f i) n := by
    intro i
    obtain ⟨-, hf2, hfs, hp, hm⟩ := hf i
    exact archEnergy_eq_W_add_atoms hf2 hfs hp hm
      (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith [ha i])))
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  · rw [← linearWeightSum_eq_of_le hNA (fun n hn => exposingWeightTrunc_eq_zero hn)]
    unfold linearWeightSum
    rw [Finset.mul_sum]
    have hsw : ∑ i, α i * (2 * π * ∑ n ∈ Finset.Icc 2 M,
          (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n * atomCoeff (f i) n) =
        ∑ n ∈ Finset.Icc 2 M, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
          (2 * π * ∑ i, α i * atomCoeff (f i) n) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hsw]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hmatch n (Finset.mem_Icc.mp hn).1]
    ring

/-- **Weil's criterion on one ray.** RH holds iff, for every cutoff `N` and level `A` with
`N ≤ e^{2A}`, every family of polar tests at levels `≤ A` whose prime-atom coefficients are
`t · w(n)` for `n ≤ N` and vanish for `N < n ≤ e^{2A}` has zero-side energy
`2π Σ α_i Re W(f_i, f_i) ≥ −2tτ_N`. Weil's criterion asks this for all tests. Here the prime traces
are confined to the prime-blind subspace plus one ray. -/
theorem riemannHypothesis_iff_forall_restrictedWeilBound :
    RiemannHypothesis ↔ ∀ (N : ℕ) (A : ℝ), N ≤ ⌊Real.exp (2 * A)⌋₊ →
      RestrictedWeilBound A (exposingWeightTrunc N) (2 * exposingTail N) := by
  have hτ0 : ∀ N, 0 ≤ exposingTail N := fun N =>
    tsum_nonneg fun n => by split_ifs <;> [exact exposingMajorant_nonneg n; exact le_rfl]
  constructor
  · intro hRH N A _ ι _ a f α t _ hf hα ht _
    have hΛ := riemannHypothesis_iff_weilPositive_vonMangoldt.mp hRH
    have hW : ∀ i, 0 ≤ (zetaZeroConfig.W (f i) (f i)).re := by
      intro i
      obtain ⟨ha0, hf2, hfs, hp, hm⟩ := hf i
      have h := hΛ (a i) ha0 (f i) hf2 hfs hp hm
      rw [zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf2 hfs hp hm, Complex.ofReal_re]
      exact mul_nonneg (by positivity) h
    have hsum : 0 ≤ ∑ i, α i * (zetaZeroConfig.W (f i) (f i)).re :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hα i) (hW i)
    have := hτ0 N
    nlinarith [mul_nonneg ht (by linarith : 0 ≤ 2 * exposingTail N), Real.pi_pos]
  intro hR
  refine riemannHypothesis_of_forall_weilDualBound_exposing_mul (c := 3) fun N A hNA => ?_
  intro ι _ a f α t ha hf hα ht hmatch
  have hid := sum_archEnergy_eq_of_matched hNA ha hf hmatch
  have hz := hR N A hNA ι a f α t ha hf hα ht hmatch
  have hL := abs_le.mp (abs_exposingValue_sub_linearWeightSum_le
    (fun n hn => vonMangoldt_le_boxWidth hn) N)
  rw [hid]
  have h1 : t * (exposingValue (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) -
      exposingTail N) ≤ t * linearWeightSum N (exposingWeightTrunc N)
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith [hL.2]) ht
  nlinarith

end

end RHTower
