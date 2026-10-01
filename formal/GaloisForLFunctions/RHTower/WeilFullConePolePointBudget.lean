import GaloisForLFunctions.RHTower.WeilFullConeCCMBridge
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleTracePositivity
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimePoleMatrix
import GaloisForLFunctions.RHTower.SelbergTruncatedVonMangoldtKreinCompletion
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The pole-point budget of a Weil-positive weight system

For real weights `lam` put

`B_lam(x) = Σ_{2≤n≤x} lam(n)/n − log x − (1/x) Σ_{2≤n≤x} lam(n)`.

**Theorem** (`eventually_polePointBudget_le`).  If `lam` is full-cone Weil-positive for the
archimedean datum of `ζ`, then for every `ε > 0`, eventually

`B_lam(x) ≤ −(γ + log 4π)/2 + ε`.

No growth, density or regularity hypothesis on `lam` is used.  For `Λ` the budget tends to
`−γ − 1` (`tendsto_polePointBudget_vonMangoldt`), and the bound exceeds this limit by
`(2 + γ − log 4π)/2 = Σ_ρ 1/ρ = 0.0231…` (`polePointBudgetConstant_eq`).  For weights of mean
density one, `B_lam(x) + 1` is the Mertens constant of `lam`, so the theorem reads
`C_lam ≤ 1 − (γ + log 4π)/2`: the Weil functional evaluated at the pole point `s = 1`.

**Proof.**  Test the restricted Weil form of aperture `a` with weights `lam` on the positive
exponential pole vector `e^{x/2} 1_{[−a,a]}`.  Full-cone positivity reaches this vector
(`ccmRestrictedWeilSourceQuadraticWith_nonneg_of_weilPositiveFull`).  Each visible atom pairs
with the pole vector as `2(e^a/n − e^{−a})`, so the weighted entry is the entry for `Λ` plus
`2e^a Σ(Λ − lam)(n)/n − 2e^{−a} Σ(Λ − lam)(n)` (`with_pole_eq`).  The entry for `Λ` divided by
`e^a` tends to `2 + γ − log 4π` (`tendsto_poleDiagonalExplicit_div_exp`); Mertens with Euler's
constant and the prime number theorem handle the `Λ` sums.

**Corollary** (`not_weilPositiveFull_primeGapWeight`).  The prime-gap weights
`lam(p) = p⁺ − p` (`p⁺` the next prime; zero off the primes) are not Weil-positive.  Their
Dirichlet series continues past the critical line, yet their budget is eventually
`≥ log(p⁺/x) − p⁺/x − log 2 + K ≥ −1.33`.  Here `K ≥ 23/84 + 1/10` collects
`u − log(1+u)`, `u = (p⁺−p)/p`, at `p = 2, 3, 5, 7`, and `p⁺ < (1.01)x` by the prime number
theorem.  The budget bound is `≤ −1.433`.
-/

open Complex Filter Topology
open ArithmeticFunction (vonMangoldt)

namespace RHTower
namespace PolePointBudget

noncomputable section

/-- The pole-point budget `B(x) = Σ_{2≤n≤x} lam(n)/n − log x − (1/x) Σ_{2≤n≤x} lam(n)`. -/
def polePointBudget (lam : ℕ → ℝ) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, lam n / n) - Real.log x - (∑ n ∈ Finset.Icc 2 ⌊x⌋₊, lam n) / x

/-- The budget constant `−(γ + log 4π)/2`. -/
def polePointBudgetConstant : ℝ :=
  -(Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) / 2

/-- The budget constant is `Λ`'s limit `−γ − 1` plus half the archimedean genus
`2 + γ − log 4π`. -/
theorem polePointBudgetConstant_eq :
    polePointBudgetConstant = (-Real.eulerMascheroniConstant - 1) + poleSharpConstant / 2 := by
  unfold polePointBudgetConstant poleSharpConstant
  ring

theorem log_le_of_mem_Icc {a : SuzukiPositiveAperture} {n : ℕ}
    (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊) : Real.log n ≤ 2 * a.1 := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega)
  exact (Real.log_le_iff_le_exp hnR).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp hn).2)

theorem psi_eq_sum_Icc_two (X : ℝ) :
    Chebyshev.psi X = ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, (vonMangoldt n : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc]
  symm
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hn).2⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn hnot
    have hsmall : n = 0 ∨ n = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp

/-- **A visible atom against the positive pole vector.** -/
theorem pole_atom_pairing (a : SuzukiPositiveAperture) {n : ℕ} (hn : 2 ≤ n)
    (hvis : Real.log n ≤ 2 * a.1) :
    1 / Real.sqrt n *
        (inner ℂ (logTranslationCLM (Real.log n) (ccmPolarApertureVector a (1 / 2)).1)
            (ccmPolarApertureVector a (1 / 2)).1 +
          inner ℂ (logTranslationCLM (-Real.log n) (ccmPolarApertureVector a (1 / 2)).1)
            (ccmPolarApertureVector a (1 / 2)).1).re =
      2 * (Real.exp a.1 / n - Real.exp (-a.1)) := by
  have h := inner_ccmPrimeTransportOperator a n (ccmPolarApertureVector a (1 / 2))
    (ccmPolarApertureVector a (1 / 2))
  rw [ccmPrimeTransport_polar_self a hn hvis] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre
  exact hre.symm

/-- **The weighted entry at the positive pole.**  It is the entry for `Λ` plus the explicit
arithmetic difference. -/
theorem with_pole_eq (a : SuzukiPositiveAperture) (lam : ℕ → ℝ) :
    ccmRestrictedWeilSourceQuadraticWith a lam ⌊Real.exp (2 * a.1)⌋₊
        (ccmPolarFormVector a (1 / 2)) =
      ccmWeilPoleDiagonal a +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          ((vonMangoldt n : ℝ) - lam n) * (2 * (Real.exp a.1 / n - Real.exp (-a.1))) := by
  unfold ccmRestrictedWeilSourceQuadraticWith ccmWeilPoleDiagonal ccmRestrictedWeilSourceQuadratic
  dsimp only
  simp only [ccmArchimedeanFormToAperture_polar]
  have hterm : ∀ w : ℕ → ℝ, ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      w n * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n) (ccmPolarApertureVector a (1 / 2)).1)
              (ccmPolarApertureVector a (1 / 2)).1 +
            inner ℂ (logTranslationCLM (-Real.log n) (ccmPolarApertureVector a (1 / 2)).1)
              (ccmPolarApertureVector a (1 / 2)).1).re =
        w n * (2 * (Real.exp a.1 / n - Real.exp (-a.1))) := by
    intro w n hn
    rw [mul_assoc, pole_atom_pairing a (Finset.mem_Icc.mp hn).1 (log_le_of_mem_Icc hn)]
  rw [Finset.sum_congr rfl (hterm lam),
    Finset.sum_congr rfl (hterm fun n => (vonMangoldt n : ℝ))]
  have hdiff : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((vonMangoldt n : ℝ) - lam n) * (2 * (Real.exp a.1 / n - Real.exp (-a.1))) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          (vonMangoldt n : ℝ) * (2 * (Real.exp a.1 / n - Real.exp (-a.1))) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
          lam n * (2 * (Real.exp a.1 / n - Real.exp (-a.1))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hdiff]
  ring

/-- **Positivity at the pole point.** -/
theorem polePoint_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (a : SuzukiPositiveAperture) :
    0 ≤ ccmWeilPoleDiagonal a +
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((vonMangoldt n : ℝ) - lam n) * (2 * (Real.exp a.1 / n - Real.exp (-a.1))) := by
  rw [← with_pole_eq]
  exact ccmRestrictedWeilSourceQuadraticWith_nonneg_of_weilPositiveFull hW a _

/-- The arithmetic difference in closed form. -/
theorem sum_diff_eq (a : SuzukiPositiveAperture) (lam : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
        ((vonMangoldt n : ℝ) - lam n) * (2 * (Real.exp a.1 / n - Real.exp (-a.1))) =
      2 * Real.exp a.1 * (reciprocalMangoldtCumulative (Real.exp (2 * a.1)) -
          ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, lam n / n) -
        2 * Real.exp (-a.1) * (Chebyshev.psi (Real.exp (2 * a.1)) -
          ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, lam n) := by
  rw [reciprocalMangoldtCumulative, psi_eq_sum_Icc_two, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **The budget at a single aperture.**  With `x = e^{2a}`, the budget is bounded by the
`Λ`-side quantity `A(a)/(2e^a) + E_M(2a) − ψ(x)/x`. -/
theorem polePointBudget_le_at {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a : SuzukiPositiveAperture) :
    polePointBudget lam (Real.exp (2 * a.1)) ≤
      poleDiagonalExplicit a.1 / (2 * Real.exp a.1) + reciprocalMangoldtError (2 * a.1) -
        Chebyshev.psi (Real.exp (2 * a.1)) / Real.exp (2 * a.1) := by
  have h := polePoint_nonneg hW a
  rw [sum_diff_eq, ccmWeilPoleDiagonal_eq_poleDiagonalExplicit] at h
  set S₁ := ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, lam n / n
  set S₀ := ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊, lam n
  set R := reciprocalMangoldtCumulative (Real.exp (2 * a.1))
  set P := Chebyshev.psi (Real.exp (2 * a.1))
  set D := poleDiagonalExplicit a.1
  have hea : 0 < Real.exp a.1 := Real.exp_pos _
  have h2a : Real.exp (2 * a.1) = Real.exp a.1 * Real.exp a.1 := by
    rw [← Real.exp_add]; ring_nf
  have hma : Real.exp (-a.1) * Real.exp a.1 = 1 := by
    rw [← Real.exp_add]; simp
  unfold polePointBudget
  rw [Real.log_exp, reciprocalMangoldtError]
  change S₁ - 2 * a.1 - S₀ / Real.exp (2 * a.1) ≤ D / (2 * Real.exp a.1) + (R - 2 * a.1) -
    P / Real.exp (2 * a.1)
  have hkey : 0 ≤ D / (2 * Real.exp a.1) + (R - S₁) - (P - S₀) / Real.exp (2 * a.1) := by
    have hpos : 0 < 2 * Real.exp a.1 := by positivity
    have hdiv := div_nonneg h hpos.le
    have hexpand : (D + (2 * Real.exp a.1 * (R - S₁) - 2 * Real.exp (-a.1) * (P - S₀))) /
        (2 * Real.exp a.1) =
        D / (2 * Real.exp a.1) + (R - S₁) - (P - S₀) / Real.exp (2 * a.1) := by
      rw [h2a]
      have hinv : Real.exp (-a.1) = 1 / Real.exp a.1 := by
        rw [Real.exp_neg, one_div]
      rw [hinv]
      field_simp
      ring
    rw [hexpand] at hdiv
    exact hdiv
  have hsplit : (P - S₀) / Real.exp (2 * a.1) = P / Real.exp (2 * a.1) - S₀ / Real.exp (2 * a.1) :=
    sub_div _ _ _
  rw [hsplit] at hkey
  linarith

/-- The `Λ`-side quantity tends to the budget constant. -/
theorem tendsto_polePoint_majorant :
    Tendsto (fun a : ℝ => poleDiagonalExplicit a / (2 * Real.exp a) +
        reciprocalMangoldtError (2 * a) - Chebyshev.psi (Real.exp (2 * a)) / Real.exp (2 * a))
      atTop (𝓝 polePointBudgetConstant) := by
  have h2a : Tendsto (fun a : ℝ => 2 * a) atTop atTop := tendsto_id.const_mul_atTop two_pos
  have hD : Tendsto (fun a : ℝ => poleDiagonalExplicit a / (2 * Real.exp a)) atTop
      (𝓝 (poleSharpConstant / 2)) := by
    have := tendsto_poleDiagonalExplicit_div_exp.div_const 2
    refine this.congr fun a => ?_
    rw [div_div, mul_comm]
  have hE : Tendsto (fun a : ℝ => reciprocalMangoldtError (2 * a)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := tendsto_reciprocalMangoldtError.comp h2a
  have hP : Tendsto (fun a : ℝ => Chebyshev.psi (Real.exp (2 * a)) / Real.exp (2 * a)) atTop
      (𝓝 1) := by
    have h := (tendsto_chebyshevError_div.comp (Real.tendsto_exp_atTop.comp h2a)).const_add 1
    rw [add_zero] at h
    refine h.congr fun a => ?_
    simp only [Function.comp_def, chebyshevError]
    have hx : Real.exp (2 * a) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring
  have hsum := (hD.add hE).sub hP
  rw [polePointBudgetConstant_eq]
  convert hsum using 2
  ring

/-- **The pole-point budget law.**  A full-cone Weil-positive weight system satisfies, for every
`ε > 0` and all large `x`,
`Σ_{2≤n≤x} lam(n)/n − log x − (1/x) Σ_{2≤n≤x} lam(n) ≤ −(γ + log 4π)/2 + ε`. -/
theorem eventually_polePointBudget_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, polePointBudget lam x ≤ polePointBudgetConstant + ε := by
  have hmaj := (tendsto_order.mp tendsto_polePoint_majorant).2 _
    (lt_add_of_pos_right polePointBudgetConstant hε)
  have hlog : Tendsto (fun x : ℝ => Real.log x / 2) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const two_pos
  filter_upwards [hlog.eventually hmaj, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hpos : 0 < Real.log x / 2 := by
    have := Real.log_pos hx1
    positivity
  have hxe : Real.exp (2 * (Real.log x / 2)) = x := by
    rw [show 2 * (Real.log x / 2) = Real.log x by ring, Real.exp_log (by linarith)]
  have h := polePointBudget_le_at hW ⟨Real.log x / 2, hpos⟩
  have hx' := hx.le
  simp only [hxe] at h hx'
  exact h.trans hx'

/-- **`Λ` sits `Σ_ρ 1/ρ` below the budget.**  Its budget tends to `−γ − 1`. -/
theorem tendsto_polePointBudget_vonMangoldt :
    Tendsto (polePointBudget fun n => (vonMangoldt n : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant - 1)) := by
  have hE : Tendsto (fun x : ℝ => reciprocalMangoldtError (Real.log x)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) :=
    tendsto_reciprocalMangoldtError.comp Real.tendsto_log_atTop
  have hP : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
    have h := tendsto_chebyshevError_div.const_add 1
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [chebyshevError]
    field_simp
    ring
  refine (hE.sub hP).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold polePointBudget reciprocalMangoldtError reciprocalMangoldtCumulative
  rw [Real.exp_log hx, psi_eq_sum_Icc_two]

/-! ## The prime-gap weights -/

/-- The least prime exceeding `n`. -/
def primeAfter (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))

theorem primeAfter_spec (n : ℕ) : n + 1 ≤ primeAfter n ∧ (primeAfter n).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (n + 1))

theorem lt_primeAfter (n : ℕ) : n < primeAfter n := (primeAfter_spec n).1

theorem primeAfter_le {n p : ℕ} (hp : p.Prime) (hnp : n < p) : primeAfter n ≤ p :=
  Nat.find_min' _ ⟨hnp, hp⟩

theorem primeAfter_of_succ_prime {n : ℕ} (h : (n + 1).Prime) : primeAfter n = n + 1 :=
  le_antisymm (primeAfter_le h (Nat.lt_succ_self n)) (primeAfter_spec n).1

theorem primeAfter_succ_of_not_prime {n : ℕ} (h : ¬ (n + 1).Prime) :
    primeAfter (n + 1) = primeAfter n := by
  apply le_antisymm
  · refine primeAfter_le (primeAfter_spec n).2 ?_
    have h1 := (primeAfter_spec n).1
    rcases Nat.lt_or_ge (n + 1) (primeAfter n) with hlt | hge
    · exact hlt
    · exfalso
      have : primeAfter n = n + 1 := le_antisymm hge h1
      exact h (this ▸ (primeAfter_spec n).2)
  · exact primeAfter_le (primeAfter_spec (n + 1)).2
      (Nat.lt_of_succ_lt (lt_primeAfter (n + 1)))

/-- Prime-gap weights: `p⁺ − p` at each prime `p`, zero elsewhere. -/
def primeGapWeight (n : ℕ) : ℝ := if n.Prime then ((primeAfter n : ℕ) : ℝ) - n else 0

/-- The logarithmic telescoping term, `log p⁺ − log p` at primes. -/
def primeGapLog (n : ℕ) : ℝ :=
  if n.Prime then Real.log (primeAfter n) - Real.log n else 0

theorem sum_primeGapWeight (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, primeGapWeight n = (primeAfter N : ℝ) - 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h : primeAfter 1 = 2 := primeAfter_of_succ_prime Nat.prime_two
    simp [h]
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    by_cases hp : (N + 1).Prime
    · rw [primeAfter_of_succ_prime hp, primeGapWeight, if_pos hp]
      push_cast
      ring
    · rw [primeAfter_succ_of_not_prime hp, primeGapWeight, if_neg hp]
      ring

theorem sum_primeGapLog (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, primeGapLog n = Real.log (primeAfter N) - Real.log 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h : primeAfter 1 = 2 := primeAfter_of_succ_prime Nat.prime_two
    simp [h]
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    by_cases hp : (N + 1).Prime
    · rw [primeAfter_of_succ_prime hp, primeGapLog, if_pos hp]
      push_cast
      ring
    · rw [primeAfter_succ_of_not_prime hp, primeGapLog, if_neg hp]
      ring

/-- Each prime term `u − log(1+u)`, `u = (p⁺ − p)/p`, is nonnegative. -/
theorem primeGapLog_le (n : ℕ) : primeGapLog n ≤ primeGapWeight n / n := by
  unfold primeGapLog primeGapWeight
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp]
    have hn : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have hq : (0 : ℝ) < primeAfter n := by exact_mod_cast (primeAfter_spec n).2.pos
    rw [← Real.log_div hq.ne' hn.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hq hn)
    have he : (primeAfter n : ℝ) / n - 1 = ((primeAfter n : ℝ) - n) / n := by
      field_simp
    linarith
  · rw [if_neg hp, if_neg hp]
    simp

theorem primeAfter_two : primeAfter 2 = 3 := primeAfter_of_succ_prime Nat.prime_three

theorem primeAfter_three : primeAfter 3 = 5 := by
  rw [← primeAfter_succ_of_not_prime (n := 3) (by norm_num)]
  exact primeAfter_of_succ_prime (n := 4) Nat.prime_five

theorem primeAfter_five : primeAfter 5 = 7 := by
  rw [← primeAfter_succ_of_not_prime (n := 5) (by norm_num)]
  exact primeAfter_of_succ_prime (n := 6) (by norm_num)

theorem primeAfter_seven : primeAfter 7 = 11 := by
  rw [← primeAfter_succ_of_not_prime (n := 7) (by norm_num),
    ← primeAfter_succ_of_not_prime (n := 8) (by norm_num),
    ← primeAfter_succ_of_not_prime (n := 9) (by norm_num)]
  exact primeAfter_of_succ_prime (n := 10) (by norm_num)

/-- `log q ≤ y` from `q ≤ 1 + y + y²/2`. -/
theorem log_le_of_le_quadratic {q y : ℝ} (hq : 0 < q) (hy : 0 ≤ y) (h : q ≤ 1 + y + y ^ 2 / 2) :
    Real.log q ≤ y :=
  (Real.log_le_iff_le_exp hq).mpr (h.trans (Real.quadratic_le_exp_of_nonneg hy))

/-- The explicit gap mass of the first four primes. -/
theorem gap_mass_first_primes :
    23 / 84 + 1 / 10 ≤ (primeGapWeight 2 / 2 - primeGapLog 2) + (primeGapWeight 3 / 3 - primeGapLog 3) +
      (primeGapWeight 5 / 5 - primeGapLog 5) + (primeGapWeight 7 / 7 - primeGapLog 7) := by
  have e2 : primeGapWeight 2 / 2 - primeGapLog 2 = 1 / 2 - Real.log (3 / 2) := by
    rw [primeGapWeight, primeGapLog, if_pos Nat.prime_two, if_pos Nat.prime_two, primeAfter_two,
      Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  have e3 : primeGapWeight 3 / 3 - primeGapLog 3 = 2 / 3 - Real.log (5 / 3) := by
    rw [primeGapWeight, primeGapLog, if_pos Nat.prime_three, if_pos Nat.prime_three,
      primeAfter_three, Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  have e5 : primeGapWeight 5 / 5 - primeGapLog 5 = 2 / 5 - Real.log (7 / 5) := by
    rw [primeGapWeight, primeGapLog, if_pos Nat.prime_five, if_pos Nat.prime_five,
      primeAfter_five, Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  have e7 : primeGapWeight 7 / 7 - primeGapLog 7 = 4 / 7 - Real.log (11 / 7) := by
    have hp7 : Nat.Prime 7 := by norm_num
    rw [primeGapWeight, primeGapLog, if_pos hp7, if_pos hp7, primeAfter_seven,
      Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  have l2 : Real.log (3 / 2) ≤ 5 / 12 := log_le_of_le_quadratic (by norm_num) (by norm_num)
    (by norm_num)
  have l3 : Real.log (5 / 3) ≤ 8 / 15 := log_le_of_le_quadratic (by norm_num) (by norm_num)
    (by norm_num)
  have l5 : Real.log (7 / 5) ≤ 12 / 35 := log_le_of_le_quadratic (by norm_num) (by norm_num)
    (by norm_num)
  have l7 : Real.log (11 / 7) ≤ 33 / 70 := log_le_of_le_quadratic (by norm_num) (by norm_num)
    (by norm_num)
  rw [e2, e3, e5, e7]
  linarith

/-- The reciprocal gap sum exceeds its telescoping logarithm by at least `23/84 + 1/10`. -/
theorem sum_primeGapWeight_div_ge (N : ℕ) (hN : 7 ≤ N) :
    Real.log (primeAfter N) - Real.log 2 + (23 / 84 + 1 / 10) ≤
      ∑ n ∈ Finset.Icc 2 N, primeGapWeight n / n := by
  rw [← sum_primeGapLog N (by omega)]
  have hsub : ({2, 3, 5, 7} : Finset ℕ) ⊆ Finset.Icc 2 N := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [Finset.mem_Icc]
    omega
  have hnn : ∀ n ∈ Finset.Icc 2 N, n ∉ ({2, 3, 5, 7} : Finset ℕ) →
      0 ≤ primeGapWeight n / n - primeGapLog n := fun n _ _ => sub_nonneg.mpr (primeGapLog_le n)
  have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hfour : ∑ n ∈ ({2, 3, 5, 7} : Finset ℕ), (primeGapWeight n / n - primeGapLog n) =
      (primeGapWeight 2 / 2 - primeGapLog 2) + (primeGapWeight 3 / 3 - primeGapLog 3) +
        (primeGapWeight 5 / 5 - primeGapLog 5) + (primeGapWeight 7 / 7 - primeGapLog 7) := by
    simp [Finset.sum_insert]
    ring
  rw [hfour] at hmono
  have hsplit : ∑ n ∈ Finset.Icc 2 N, (primeGapWeight n / n - primeGapLog n) =
      ∑ n ∈ Finset.Icc 2 N, primeGapWeight n / n - ∑ n ∈ Finset.Icc 2 N, primeGapLog n :=
    Finset.sum_sub_distrib _ _
  rw [hsplit] at hmono
  linarith [gap_mass_first_primes]

/-- The budget constant is below `−1.44`. -/
theorem polePointBudgetConstant_lt : polePointBudgetConstant < -(144 / 100) := by
  unfold polePointBudgetConstant
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlog2 := Real.log_two_gt_d9
  have hpi : 1 < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    have := Real.exp_one_lt_d9
    have := Real.pi_gt_d2
    linarith
  have h4pi : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  rw [h4pi]
  norm_num at hlog2
  linarith

/-- **The prime-gap weights are not Weil-positive.** -/
theorem not_weilPositiveFull_primeGapWeight : ¬ WeilPositiveFull primeGapWeight := by
  intro hW
  have hb := eventually_polePointBudget_le hW (ε := 1 / 100) (by norm_num)
  have hpb := prime_between (ε := 1 / 100) (by norm_num)
  obtain ⟨x, hxb, hxp, hx8⟩ := (hb.and (hpb.and (eventually_ge_atTop (8 : ℝ)))).exists
  obtain ⟨p, hp, hxp1, hxp2⟩ := hxp
  set N := ⌊x⌋₊ with hNdef
  have hx0 : 0 < x := by linarith
  have hN7 : 7 ≤ N := Nat.le_floor (by norm_num; linarith)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hNp : N < p := by exact_mod_cast (lt_of_le_of_lt hNx hxp1)
  -- the next prime after `N` lies in `(x, 1.01 x)`
  have hq_le : (primeAfter N : ℝ) ≤ p := by exact_mod_cast primeAfter_le hp hNp
  have hq_gt : x < (primeAfter N : ℝ) := by
    have : N + 1 ≤ primeAfter N := (primeAfter_spec N).1
    have h' : ((N : ℝ) + 1) ≤ (primeAfter N : ℝ) := by exact_mod_cast this
    linarith
  have hq0 : (0 : ℝ) < primeAfter N := by linarith
  -- lower bound for the budget
  have hS₁ := sum_primeGapWeight_div_ge N hN7
  have hS₀ := sum_primeGapWeight N (by omega)
  have hbudget : polePointBudget primeGapWeight x =
      (∑ n ∈ Finset.Icc 2 N, primeGapWeight n / n) - Real.log x -
        ((primeAfter N : ℝ) - 2) / x := by
    unfold polePointBudget
    rw [← hNdef, hS₀]
  have hlogq : Real.log x < Real.log (primeAfter N) := Real.log_lt_log hx0 hq_gt
  have hratio : ((primeAfter N : ℝ) - 2) / x < 101 / 100 := by
    rw [div_lt_iff₀ hx0]
    linarith
  have hlow : -(1 + 1 / 100) - Real.log 2 + (23 / 84 + 1 / 10) < polePointBudget primeGapWeight x := by
    rw [hbudget]
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hconst := polePointBudgetConstant_lt
  norm_num at hlog2
  linarith

end

end PolePointBudget

end RHTower
