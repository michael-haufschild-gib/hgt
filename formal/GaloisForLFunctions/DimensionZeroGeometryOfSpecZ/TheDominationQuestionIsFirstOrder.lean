import GaloisForLFunctions.WindowTowerOfSpecZ.TheJetsOfTheTateFamily
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTangentPrincipleOfTheTateFamily

/-!
# The domination question is first order

On a window `W_A` Weil's form is the 1-jet at dimension zero of the Tate function
`τ_H(k) = ⟨ρ_A(J_k)H, H⟩` (WTZ):

`Q(H) = D(H) − 2⟨ρ_A(Λ)H, H⟩`, `D(H) = Ω(0)‖H‖² + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩²` (`archPolar`).

The *domination question* asks for a form `A_k(H)` with `A_0 = 0` and `∂_kA_k|₀ = D(H)` dominating the
window point counts, `A_k(H) ≥ 2(τ_H(k) − ‖H‖²)` for small `k > 0`. This module settles the question
in its bare form.

* **Descent** (`weilQuad_nonneg_of_dominates`): domination on any interval `(0, k₀]` gives `Q(H) ≥ 0`:
  the defect `A_k − 2(τ_H(k) − ‖H‖²)` vanishes at `0` and has derivative `Q(H)` there.
* **The Taylor remainder of the counts is prime-blind** (`abs_tateFunction_sub_tangent_le`): for
  `k ≥ 0`, `0 ≤ J_k(n) − [n = 1] − kΛ(n) ≤ n^k − 1 − k log n` (`jordanTotient_sub_tangent_le`, from
  `Σ_{d∣n} J_k(d) = n^k`, the tangent principle and `Σ_{d∣n} Λ(d) = log n`), so
  `|τ_H(k) − ‖H‖² − k⟨ρ_A(Λ)H, H⟩| ≤ R_A(k)‖H‖²` with `R_A(k) = Σ_{n≤e^A}(n^k − 1 − k log n)n^{−1/2}`.
* **Collapse** (`canonicalArch_dominates_iff`, `exists_dominating_iff`): the family
  `A_k = k D(H) + 2R_A(k)‖H‖²` — built from the Gamma factor, the pole and the integers `n ≤ e^A`,
  with no prime in it — satisfies `A_k − 2(τ_H(k) − ‖H‖²) ≥ k Q(H)` for all `k ≥ 0`. Hence a dominating
  family with the right 1-jet exists iff `Q(H) ≥ 0`, iff this explicit one dominates for every `k ≥ 0`.
  RH is equivalent to its domination on every window (`riemannHypothesis_iff_canonicalArch_dominates`).
  The bare domination question is a reformulation of Weil positivity: positive dimension carries
  information only through structure imposed on the archimedean family, never through existence.
* **Jet constraint on null tests** (`two_mul_selbergPairing_le_of_null`): if `Q(H) = 0` and a
  twice differentiable family dominates near `0`, its second jet pays Selberg's form:
  `∂²_kA_k|₀ ≥ 2⟨ρ_A(Λ₂)H, H⟩`, `Λ₂ = Λ log + Λ * Λ`. On null directions the first Taylor coefficient
  (parity-blind `Λ`) is exhausted and domination becomes a statement about the second
  (sieve-accessible `Λ₂`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open WindowTowerOfSpecZ CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
open RHTower.WeilMarkovPole ArithmeticDegenerationTheory

/-! ### The pieces of Weil's window form -/

/-- The autocorrelation `c_H(t) = ∫ H(u) H(u + t) du`. -/
def corr (H : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u, H u * H (u + t)

/-- The archimedean–polar part `D(H) = Ω(0)‖H‖² + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩²` of Weil's form. -/
def archPolar (H : ℝ → ℝ) : ℝ :=
  EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H + (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2)

/-- The `j`-th jet pairing `Σ_{n ≤ e^A} Λ_j(n) n^{−1/2} c_H(log n) = ⟨ρ_A(Λ_j)H, H⟩`. -/
def jetPairing (j : ℕ) (A : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (windowLevel A), genVonMangoldt j n / Real.sqrt n * corr H (Real.log n)

/-- The jet functions of the Tate function, `k ↦ Σ_{n ≤ e^A} ∂^j_kJ_k(n) n^{−1/2} c_H(log n)`. -/
def tateJetFunction (j : ℕ) (A : ℝ) (H : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (windowLevel A), tateJet j n k / Real.sqrt n * corr H (Real.log n)

theorem hasDerivAt_tateJetFunction (j : ℕ) (A : ℝ) (H : ℝ → ℝ) (k : ℝ) :
    HasDerivAt (tateJetFunction j A H) (tateJetFunction (j + 1) A H k) k :=
  HasDerivAt.fun_sum fun n _ => ((hasDerivAt_tateJet j n k).div_const _).mul_const _

theorem tateJetFunction_zero_dim (j : ℕ) (A : ℝ) (H : ℝ → ℝ) :
    tateJetFunction j A H 0 = jetPairing j A H := by
  simp only [tateJetFunction, jetPairing, tateJet_zero_dim]

theorem tateFunction_eq_tateJetFunction {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    tateFunction A H = tateJetFunction 0 A H := by
  funext k
  rw [tateFunction_eq hH, tateJetFunction]
  simp only [tateJet_zero, corr]

theorem jetPairing_one (A : ℝ) (H : ℝ → ℝ) :
    jetPairing 1 A H = ∑ n ∈ Finset.Icc 1 (windowLevel A),
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * corr H (Real.log n) := by
  simp only [jetPairing, genVonMangoldt_one]

/-- `τ_H′(0) = ⟨ρ_A(Λ)H, H⟩`. -/
theorem hasDerivAt_tateFunction_zero {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    HasDerivAt (tateFunction A H) (jetPairing 1 A H) 0 := by
  rw [tateFunction_eq_tateJetFunction hH, ← tateJetFunction_zero_dim]
  exact hasDerivAt_tateJetFunction 0 A H 0

/-- **Weil's window form**: `Q(H) = D(H) − 2⟨ρ_A(Λ)H, H⟩`. -/
theorem weilQuad_eq_archPolar_sub {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    weilQuad H = archPolar H - 2 * jetPairing 1 A H := by
  rw [weilQuad_eq_tateJet hH, tateFunction_zero hH, (hasDerivAt_tateFunction_zero hH).deriv,
    archPolar]
  ring

/-! ### The prime-blind Taylor remainder of the counts -/

/-- `Σ_{d∣n} J_k(d) = n^k`: the Jordan counts of the divisors fill `(ℤ/n)^k`. -/
theorem sum_divisors_jordanTotient (k : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, jordanTotient k d = (n : ℝ) ^ k := by
  have h : jordanFun k * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      tateTwist (-k) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    rw [jordanFun_eq, mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  have hn' := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  simp only [ArithmeticFunction.coe_mul_zeta_apply, tateTwist_apply,
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn, Nat.cast_one, one_mul,
    neg_neg, jordanFun_apply] at hn'
  exact hn'

/-- **The Taylor remainder of a Jordan count is bounded by that of `n^k`**: for `k ≥ 0` and `n ≥ 1`,
`J_k(n) − [n = 1] − kΛ(n) ≤ n^k − 1 − k log n`. The bound sees `n`, not its prime factors. -/
theorem jordanTotient_sub_tangent_le {k : ℝ} (hk : 0 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    jordanTotient k n - ((if n = 1 then 1 else 0) + k * ArithmeticFunction.vonMangoldt n) ≤
      (n : ℝ) ^ k - 1 - k * Real.log n := by
  rcases eq_or_lt_of_le hn with rfl | hn2
  · simp [jordanTotient_one_eq]
  have hn0 : n ≠ 0 := by omega
  have hsum := sum_divisors_jordanTotient k hn0
  have hlog : ∑ i ∈ n.divisors, ArithmeticFunction.vonMangoldt i = Real.log n :=
    ArithmeticFunction.vonMangoldt_sum
  rw [← Nat.insert_self_properDivisors hn0,
    Finset.sum_insert Nat.self_notMem_properDivisors] at hsum hlog
  have hone : (1 : ℕ) ∈ n.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hn2
  have hlow : ∑ d ∈ n.properDivisors,
      ((if d = 1 then (1 : ℝ) else 0) + k * ArithmeticFunction.vonMangoldt d) ≤
        ∑ d ∈ n.properDivisors, jordanTotient k d :=
    Finset.sum_le_sum fun d _ => jordanTotient_ge_tangent hk d
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ _ (fun _ => (1 : ℝ)), if_pos hone,
    ← Finset.mul_sum] at hlow
  have hΛ : ∑ d ∈ n.properDivisors, ArithmeticFunction.vonMangoldt d =
      Real.log n - ArithmeticFunction.vonMangoldt n := by linarith
  rw [hΛ, mul_sub] at hlow
  rw [if_neg (by omega)]
  linarith

/-- `|J_k(n) − [n = 1] − kΛ(n)| ≤ n^k − 1 − k log n` for `k ≥ 0`, `n ≥ 1`. -/
theorem abs_jordanTotient_sub_tangent_le {k : ℝ} (hk : 0 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    |jordanTotient k n - ((if n = 1 then 1 else 0) + k * ArithmeticFunction.vonMangoldt n)| ≤
      (n : ℝ) ^ k - 1 - k * Real.log n :=
  abs_le.mpr ⟨by linarith [jordanTotient_ge_tangent hk n, jordanTotient_sub_tangent_le hk hn],
    jordanTotient_sub_tangent_le hk hn⟩

/-- An autocorrelation is bounded by the energy: `|c_H(t)| ≤ ‖H‖²`. -/
theorem abs_corr_le {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) (t : ℝ) :
    |corr H t| ≤ ∫ u, H u ^ 2 := by
  have h1 := integrable_sq hH.continuous hH.hasCompactSupport
  have h2 : Integrable fun u => H (u + t) ^ 2 := h1.comp_add_right t
  have h := abs_integral_mul_le h1 h2 (integrable_mul_shift hH.continuous hH.hasCompactSupport t)
  rwa [integral_add_right_eq_self (fun u => H u ^ 2) t,
    Real.mul_self_sqrt (integral_nonneg fun u => sq_nonneg _)] at h

theorem corr_zero (H : ℝ → ℝ) : corr H 0 = ∫ u, H u ^ 2 := by
  simp only [corr, add_zero, sq]

/-- The prime-blind Taylor remainder `R_A(k) = Σ_{n ≤ e^A} (n^k − 1 − k log n) n^{−1/2}`. -/
def tateRemainder (A k : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (windowLevel A), ((n : ℝ) ^ k - 1 - k * Real.log n) / Real.sqrt n

theorem tateRemainder_zero (A : ℝ) : tateRemainder A 0 = 0 := by
  simp [tateRemainder]

/-- `R_A` is flat at dimension zero. -/
theorem hasDerivAt_tateRemainder (A : ℝ) : HasDerivAt (tateRemainder A) 0 0 := by
  have h : HasDerivAt (tateRemainder A) (∑ n ∈ Finset.Icc 1 (windowLevel A),
      ((n : ℝ) ^ (0 : ℝ) * Real.log n - Real.log n) / Real.sqrt n) 0 := by
    refine HasDerivAt.fun_sum fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact ((((Real.hasStrictDerivAt_const_rpow hn0 0).hasDerivAt).sub_const 1).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log n))).div_const _ |>.congr_deriv (by simp)
  simpa using h

/-- **The Taylor remainder of the Tate function is prime-blind**: for `k ≥ 0`,
`|τ_H(k) − ‖H‖² − k⟨ρ_A(Λ)H, H⟩| ≤ R_A(k)‖H‖²`. -/
theorem abs_tateFunction_sub_tangent_le {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {k : ℝ} (hk : 0 ≤ k) :
    |tateFunction A H k - (∫ u, H u ^ 2) - k * jetPairing 1 A H| ≤
      tateRemainder A k * ∫ u, H u ^ 2 := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 (windowLevel A) := Finset.mem_Icc.mpr ⟨le_rfl, by
    rw [windowLevel, Nat.le_floor_iff (Real.exp_pos A).le]
    simpa only [Nat.cast_one] using Real.one_le_exp_iff.mpr hA⟩
  have hnorm : (∫ u, H u ^ 2) = ∑ n ∈ Finset.Icc 1 (windowLevel A),
      (if n = 1 then (1 : ℝ) else 0) / Real.sqrt n * corr H (Real.log n) := by
    rw [Finset.sum_eq_single_of_mem 1 h1 fun n _ hn => by rw [if_neg hn, zero_div, zero_mul]]
    simp [corr_zero]
  have hexp : tateFunction A H k - (∫ u, H u ^ 2) - k * jetPairing 1 A H =
      ∑ n ∈ Finset.Icc 1 (windowLevel A),
        (jordanTotient k n - ((if n = 1 then 1 else 0) + k * ArithmeticFunction.vonMangoldt n)) /
          Real.sqrt n * corr H (Real.log n) := by
    rw [tateFunction_eq hH, hnorm, jetPairing_one, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [corr]
    ring
  rw [hexp, tateRemainder, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have hJ := abs_jordanTotient_sub_tangent_le hk hn1
  have hR : 0 ≤ (n : ℝ) ^ k - 1 - k * Real.log n := (abs_nonneg _).trans hJ
  rw [abs_mul, abs_div, abs_of_pos hsq, div_mul_eq_mul_div, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (mul_le_mul hJ (abs_corr_le hH _) (abs_nonneg _) hR) hsq.le

/-! ### Descent and collapse -/

/-- **Descent**: a function vanishing at `0`, nonnegative on `(0, k₀]`, has nonnegative derivative
at `0`. -/
theorem nonneg_of_hasDerivAt_of_nonneg {f : ℝ → ℝ} {d k₀ : ℝ} (hf : HasDerivAt f d 0)
    (h0 : f 0 = 0) (hk₀ : 0 < k₀) (hpos : ∀ k ∈ Ioc 0 k₀, 0 ≤ f k) : 0 ≤ d := by
  refine ge_of_tendsto hf.tendsto_slope_zero_right ?_
  filter_upwards [Ioo_mem_nhdsGT hk₀] with t ht
  simp only [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (hpos t ⟨ht.1, ht.2.le⟩)

/-- **Domination near dimension zero gives Weil positivity.** If `A_0 = 0`, `∂_kA_k|₀ = D(H)` and
`A_k ≥ 2(τ_H(k) − ‖H‖²)` on `(0, k₀]`, then `Q(H) ≥ 0`. -/
theorem weilQuad_nonneg_of_dominates {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {a : ℝ → ℝ} (ha0 : a 0 = 0) (ha : HasDerivAt a (archPolar H) 0) {k₀ : ℝ} (hk₀ : 0 < k₀)
    (hdom : ∀ k ∈ Ioc 0 k₀, 2 * (tateFunction A H k - ∫ u, H u ^ 2) ≤ a k) :
    0 ≤ weilQuad H := by
  have hd : HasDerivAt (fun k => a k - 2 * (tateFunction A H k - ∫ u, H u ^ 2))
      (weilQuad H) 0 := by
    rw [weilQuad_eq_archPolar_sub hH]
    exact ha.sub (((hasDerivAt_tateFunction_zero hH).sub_const _).const_mul 2)
  exact nonneg_of_hasDerivAt_of_nonneg hd (by simp [ha0, tateFunction_zero hH]) hk₀
    fun k hk => sub_nonneg.mpr (hdom k hk)

/-- **The canonical prime-blind family** `A_k(H) = k D(H) + 2R_A(k)‖H‖²`: Gamma factor, pole and the
integers `n ≤ e^A`; no prime enters. -/
def canonicalArch (A : ℝ) (H : ℝ → ℝ) (k : ℝ) : ℝ :=
  k * archPolar H + 2 * tateRemainder A k * ∫ u, H u ^ 2

theorem canonicalArch_zero (A : ℝ) (H : ℝ → ℝ) : canonicalArch A H 0 = 0 := by
  simp [canonicalArch, tateRemainder_zero]

theorem hasDerivAt_canonicalArch (A : ℝ) (H : ℝ → ℝ) :
    HasDerivAt (canonicalArch A H) (archPolar H) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (archPolar H)).add
    (((hasDerivAt_tateRemainder A).const_mul 2).mul_const (∫ u, H u ^ 2))
  have e : canonicalArch A H =
      (fun y => id y * archPolar H) + fun y => 2 * tateRemainder A y * ∫ u, H u ^ 2 := by
    funext y; simp [canonicalArch]
  rw [e]
  simpa using h

/-- **The defect of the canonical family dominates `k Q(H)`**: for `k ≥ 0`,
`k Q(H) ≤ A_k(H) − 2(τ_H(k) − ‖H‖²)`. -/
theorem mul_weilQuad_le_canonicalArch_sub {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hH : IsWindowTest A H) {k : ℝ} (hk : 0 ≤ k) :
    k * weilQuad H ≤ canonicalArch A H k - 2 * (tateFunction A H k - ∫ u, H u ^ 2) := by
  have h := (abs_le.mp (abs_tateFunction_sub_tangent_le hA hH hk)).2
  rw [weilQuad_eq_archPolar_sub hH, canonicalArch]
  linarith

/-- **Collapse**: the canonical prime-blind family dominates the counts in every dimension `k ≥ 0`
iff Weil's form is nonnegative on the test. -/
theorem canonicalArch_dominates_iff {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    (∀ k, 0 ≤ k → 2 * (tateFunction A H k - ∫ u, H u ^ 2) ≤ canonicalArch A H k) ↔
      0 ≤ weilQuad H := by
  constructor
  · intro h
    exact weilQuad_nonneg_of_dominates hH (canonicalArch_zero A H) (hasDerivAt_canonicalArch A H)
      one_pos fun k hk => h k hk.1.le
  · intro hQ k hk
    have := mul_weilQuad_le_canonicalArch_sub hA hH hk
    nlinarith [mul_nonneg hk hQ]

/-- **The bare domination question is Weil positivity**: some family with `A_0 = 0` and
`∂_kA_k|₀ = D(H)` dominates the counts near dimension zero iff `Q(H) ≥ 0`. -/
theorem exists_dominating_iff {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    (∃ a : ℝ → ℝ, a 0 = 0 ∧ HasDerivAt a (archPolar H) 0 ∧
      ∃ k₀ > 0, ∀ k ∈ Ioc 0 k₀, 2 * (tateFunction A H k - ∫ u, H u ^ 2) ≤ a k) ↔
      0 ≤ weilQuad H := by
  constructor
  · rintro ⟨a, ha0, ha, k₀, hk₀, hdom⟩
    exact weilQuad_nonneg_of_dominates hH ha0 ha hk₀ hdom
  · intro hQ
    exact ⟨canonicalArch A H, canonicalArch_zero A H, hasDerivAt_canonicalArch A H, 1, one_pos,
      fun k hk => (canonicalArch_dominates_iff hA hH).mpr hQ k hk.1.le⟩

/-- **RH ⇔ the canonical prime-blind family dominates the window counts in every dimension**
(an RH-equivalence: it shows the bare question carries no information beyond Weil positivity). -/
theorem riemannHypothesis_iff_canonicalArch_dominates :
    RiemannHypothesis ↔ ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
      ∀ k, 0 ≤ k → 2 * (tateFunction A H k - ∫ u, H u ^ 2) ≤ canonicalArch A H k := by
  rw [riemannHypothesis_iff_windowForm_nonneg]
  exact forall_congr' fun A => forall_congr' fun hA => forall_congr' fun H =>
    forall_congr' fun hH => (canonicalArch_dominates_iff hA hH).symm

/-! ### The jet constraint on null tests -/

/-- **Second-order descent**: if `f(0) = f′(0) = 0`, `f ≥ 0` on `(0, k₀]` and `f′` is differentiable
at `0`, then `f″(0) ≥ 0`. -/
theorem nonneg_of_hasDerivAt_deriv {f f' : ℝ → ℝ} {s k₀ : ℝ} (hf : ∀ k, HasDerivAt f (f' k) k)
    (hf' : HasDerivAt f' s 0) (h0 : f 0 = 0) (h0' : f' 0 = 0) (hk₀ : 0 < k₀)
    (hpos : ∀ k ∈ Ioc 0 k₀, 0 ≤ f k) : 0 ≤ s := by
  by_contra hs'
  have hs : s < 0 := not_le.mp hs'
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f' (0 + t) - f' 0) < 0 :=
    hf'.tendsto_slope_zero_right.eventually (gt_mem_nhds hs)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hev.and (Ioo_mem_nhdsGT hk₀))
  set t := min δ k₀ / 2 with ht
  have ht0 : 0 < t := by rw [ht]; exact half_pos (lt_min hδ hk₀)
  have htδ : t < δ := by rw [ht]; linarith [min_le_left δ k₀, half_lt_self (lt_min hδ hk₀)]
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' ht0
    (fun x _ => (hf x).continuousAt.continuousWithinAt) fun x _ => hf x
  have hcneg : f' c < 0 := by
    have := (hsub ⟨hc.1, hc.2.trans htδ⟩).1
    simp only [zero_add, h0', sub_zero, smul_eq_mul] at this
    exact (mul_neg_iff.mp this).elim (fun h => h.2) fun h => absurd h.1 (not_lt.mpr
      (inv_nonneg.mpr hc.1.le))
  have htk : t ≤ k₀ := by rw [ht]; linarith [min_le_right δ k₀, half_le_self (lt_min hδ hk₀).le]
  have hft := hpos t ⟨ht0, htk⟩
  rw [h0, sub_zero, sub_zero] at hcs
  have : f t / t < 0 := hcs ▸ hcneg
  exact absurd (div_nonneg hft ht0.le) (not_le.mpr this)

/-- **On a null test the second jet of a dominating family pays Selberg's form.** If `Q(H) = 0` and
a twice differentiable family `A_k` with `A_0 = 0`, `∂_kA_k|₀ = D(H)`, `∂²_kA_k|₀ = B` dominates the
counts on `(0, k₀]`, then `B ≥ 2⟨ρ_A(Λ₂)H, H⟩`. -/
theorem two_mul_selbergPairing_le_of_null {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (hQ : weilQuad H = 0) {a a' : ℝ → ℝ} {B : ℝ} (ha : ∀ k, HasDerivAt a (a' k) k)
    (ha0 : a 0 = 0) (ha'0 : a' 0 = archPolar H) (hB : HasDerivAt a' B 0) {k₀ : ℝ} (hk₀ : 0 < k₀)
    (hdom : ∀ k ∈ Ioc 0 k₀, 2 * (tateFunction A H k - ∫ u, H u ^ 2) ≤ a k) :
    2 * jetPairing 2 A H ≤ B := by
  have hτ := tateFunction_eq_tateJetFunction hH
  have hs := nonneg_of_hasDerivAt_deriv
    (f := fun k => a k - 2 * (tateJetFunction 0 A H k - ∫ u, H u ^ 2))
    (f' := fun k => a' k - 2 * tateJetFunction 1 A H k)
    (fun k => (ha k).sub (((hasDerivAt_tateJetFunction 0 A H k).sub_const _).const_mul 2))
    (hB.sub ((hasDerivAt_tateJetFunction 1 A H 0).const_mul 2))
    (by
      show a 0 - 2 * (tateJetFunction 0 A H 0 - ∫ u, H u ^ 2) = 0
      rw [ha0, ← hτ, tateFunction_zero hH]; ring)
    (by
      show a' 0 - 2 * tateJetFunction 1 A H 0 = 0
      rw [ha'0, tateJetFunction_zero_dim]
      linarith [weilQuad_eq_archPolar_sub hH])
    hk₀ fun k hk => by
      show 0 ≤ a k - 2 * (tateJetFunction 0 A H k - ∫ u, H u ^ 2)
      rw [← hτ]; exact sub_nonneg.mpr (hdom k hk)
  rw [tateJetFunction_zero_dim] at hs
  linarith

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
