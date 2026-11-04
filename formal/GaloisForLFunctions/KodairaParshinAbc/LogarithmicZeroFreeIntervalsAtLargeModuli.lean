import GaloisForLFunctions.RHTower.SiegelZeroFree
import GaloisForLFunctions.RHTower.SiegelRealAxis

/-!
# Logarithmic zero-free intervals are decided at large moduli

The exclusion of exceptional zeros is the statement that for some `c > 0` no nontrivial quadratic
Dirichlet `L`-function modulo `N` has a real zero `σ > 1 - c / log(N + 3)`.  Its derivation from a
class-number lower bound only controls large moduli; the remaining finitely many moduli are
absorbed by shrinking `c` to an infimum over the exceptions.

This module makes that absorption unconditional, using Siegel's theorem in the zero-free form
`σ > 1 - c N^{-ε}` (`RHTower.siegel_zero_free`):

* for every bound `N₀` some `c > 0` excludes real zeros beyond `1 - c / log(N + 3)` for all
  `N < N₀` (`exists_logZeroFree_below`);
* hence a logarithmic zero-free interval valid for all large moduli extends to all moduli
  (`logZeroFree_iff_eventually`);
* on such an interval `L(σ, χ)` is positive (`LFunction_re_pos_of_logZeroFree`).

It also records the class-number step: a bound `exp(π √d / h) ≤ C d^e` on the modular invariant
gives `h ≥ π √d / (log C + e log d)`, and so `h ≥ (π / (e + η)) √d / log d` once `log C ≤ η log d`.
-/

open DirichletCharacter Complex

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

/-- No nontrivial quadratic `L(s, χ)` modulo `N ≥ N₀` vanishes at a real `σ > 1 - c / log(N+3)`. -/
def LogZeroFreeFrom (c : ℝ) (N₀ : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ χ : DirichletCharacter ℂ N, χ ^ 2 = 1 → χ ≠ 1 →
    ∀ σ : ℝ, 1 - c / Real.log ((N : ℝ) + 3) < σ → LFunction χ σ ≠ 0

/-- **Finitely many moduli carry a logarithmic zero-free interval.**  For every `N₀` there is
`c > 0` such that for all `N < N₀` no nontrivial quadratic `L(s, χ)` modulo `N` vanishes at a real
`σ > 1 - c / log(N+3)`. -/
theorem exists_logZeroFree_below (N₀ : ℕ) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N], N < N₀ → ∀ χ : DirichletCharacter ℂ N, χ ^ 2 = 1 →
      χ ≠ 1 → ∀ σ : ℝ, 1 - c / Real.log ((N : ℝ) + 3) < σ → LFunction χ σ ≠ 0 := by
  obtain ⟨c₁, hc₁, hS⟩ := RHTower.siegel_zero_free (ε := 1) one_pos
  refine ⟨c₁ / ((N₀ : ℝ) + 1), by positivity, ?_⟩
  intro N _ hN χ hq hχ σ hσ
  refine hS N χ hq hχ σ (lt_of_le_of_lt ?_ hσ)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hNle : (N : ℝ) ≤ (N₀ : ℝ) + 1 := by
    have : N ≤ N₀ + 1 := by omega
    exact_mod_cast this
  have hlog : 1 < Real.log ((N : ℝ) + 3) := RHTower.one_lt_log_add_three N
  have h1 : c₁ / ((N₀ : ℝ) + 1) / Real.log ((N : ℝ) + 3) ≤ c₁ / ((N₀ : ℝ) + 1) :=
    div_le_self (by positivity) hlog.le
  have h2 : c₁ / ((N₀ : ℝ) + 1) ≤ c₁ * (N : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hc₁.le (by positivity) hNle
  linarith

/-- **Absorbing the exceptional moduli.**  A logarithmic zero-free interval for all moduli
`N ≥ N₀` yields one, with a smaller constant, for all moduli. -/
theorem logZeroFree_of_from {c : ℝ} (hc : 0 < c) {N₀ : ℕ} (h : LogZeroFreeFrom c N₀) :
    ∃ c' > 0, c' ≤ c ∧ LogZeroFreeFrom c' 0 := by
  obtain ⟨c₂, hc₂, hbelow⟩ := exists_logZeroFree_below N₀
  refine ⟨min c c₂, lt_min hc hc₂, min_le_left _ _, ?_⟩
  intro N _ _ χ hq hχ σ hσ
  have hlog : 0 < Real.log ((N : ℝ) + 3) := lt_trans one_pos (RHTower.one_lt_log_add_three N)
  rcases lt_or_ge N N₀ with hN | hN
  · refine hbelow N hN χ hq hχ σ (lt_of_le_of_lt ?_ hσ)
    have := div_le_div_of_nonneg_right (min_le_right c c₂) hlog.le
    linarith
  · refine h N hN χ hq hχ σ (lt_of_le_of_lt ?_ hσ)
    have := div_le_div_of_nonneg_right (min_le_left c c₂) hlog.le
    linarith

/-- **A logarithmic zero-free interval is decided at large moduli.** -/
theorem logZeroFree_iff_eventually :
    (∃ c > 0, ∃ N₀ : ℕ, LogZeroFreeFrom c N₀) ↔ ∃ c > 0, LogZeroFreeFrom c 0 := by
  constructor
  · rintro ⟨c, hc, N₀, h⟩
    obtain ⟨c', hc', -, h'⟩ := logZeroFree_of_from hc h
    exact ⟨c', hc', h'⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, 0, h⟩

/-- On a logarithmic zero-free interval the quadratic `L`-function is positive. -/
theorem LFunction_re_pos_of_logZeroFree {c : ℝ} {N₀ : ℕ} (h : LogZeroFreeFrom c N₀)
    {N : ℕ} [NeZero N] (hN : N₀ ≤ N) {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ : 1 - c / Real.log ((N : ℝ) + 3) < σ) (hσ2 : σ ≤ 2) :
    0 < (LFunction χ σ).re :=
  RHTower.LFunction_re_pos_of_no_zero hq hχ hσ0
    (fun t ht _ => h N hN χ hq hχ t (lt_of_lt_of_le hσ ht)) le_rfl hσ2

/-! ## The class-number step -/

/-- **From a height bound to a class-number bound.**  If `exp(π √d / h) ≤ C d^e` with `h > 0`
and `log C + e log d > 0`, then `h ≥ π √d / (log C + e log d)`. -/
theorem classNumber_ge_of_exp_le {d h C e : ℝ} (hd : 0 < d) (hh : 0 < h) (hC : 0 < C)
    (hpos : 0 < Real.log C + e * Real.log d)
    (hb : Real.exp (Real.pi * Real.sqrt d / h) ≤ C * d ^ e) :
    Real.pi * Real.sqrt d / (Real.log C + e * Real.log d) ≤ h := by
  have hlog := Real.log_le_log (Real.exp_pos _) hb
  rw [Real.log_exp, Real.log_mul hC.ne' (Real.rpow_pos_of_pos hd e).ne',
    Real.log_rpow hd] at hlog
  rw [div_le_iff₀ hpos]
  rw [div_le_iff₀ hh] at hlog
  linarith

/-- **The `√d / log d` lower bound.**  Under `exp(π √d / h) ≤ C d^e` with `e ≥ 0`, as soon as
`0 < log C ≤ η log d` (with `d > 1`) one has `h ≥ (π / (e + η)) √d / log d`. -/
theorem classNumber_ge_sqrt_div_log {d h C e η : ℝ} (hd : 1 < d) (hh : 0 < h) (hC : 1 < C)
    (he : 0 ≤ e) (hCd : Real.log C ≤ η * Real.log d)
    (hb : Real.exp (Real.pi * Real.sqrt d / h) ≤ C * d ^ e) :
    Real.pi / (e + η) * (Real.sqrt d / Real.log d) ≤ h := by
  have hlogd : 0 < Real.log d := Real.log_pos hd
  have hlogC : 0 < Real.log C := Real.log_pos hC
  have hpos : 0 < Real.log C + e * Real.log d := by positivity
  have h1 := classNumber_ge_of_exp_le (by linarith) hh (by linarith) hpos hb
  refine le_trans ?_ h1
  rw [div_mul_div_comm]
  apply div_le_div_of_nonneg_left (by positivity) hpos
  nlinarith

end GaloisForLFunctions.KodairaParshinAbc
