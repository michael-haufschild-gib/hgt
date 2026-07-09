/-
# Gelfond–Schneider and the transcendence of prime-rate ratios

The weld couples the archimedean generator `∂_s` to the prime shifts `{σ_p}`; the rate of `σ_p`
is `log p`, and the founding `𝓜⁺` weld is spanned by the rate group `⟨log p⟩`.  The one-exponential
Hermite/Lindemann engine already in this tree (`exp_algInt_ne`, `transcendental_log_rat`) shows every
single rate `log p` is transcendental — a statement about one point of the spectrum.  The *ratio* of
two rates, `log q / log p`, is a statement about the **relation** between two spectral points, and it
lies strictly beyond the one-exponential method: it is Hilbert's seventh problem (Gelfond–Schneider,
1934).

`Real.rpow` writes the bridge cleanly: with `ξ = log q / log p` and `p, q` prime,
`p ^ ξ = exp(ξ · log p) = exp(log q) = q`.  If `ξ` were algebraic it would be irrational (the
`ℤ`-independence of `log p, log q`, `two_prime_log_indep`), so Gelfond–Schneider would force `p ^ ξ`
transcendental — contradicting `p ^ ξ = q ∈ ℤ`.  Hence `ξ` is transcendental: **no two prime rates
of the weld are algebraically commensurable.**

The reduction (`log_ratio_transcendental`) is unconditional, resting only on the `ℤ`-independence of
`log p, log q` (`two_prime_log_indep`).  The one genuinely-hard analytic input — the Gelfond–Schneider
theorem itself, whose proof is the two-variable auxiliary-function / small-value / zero-estimate
method — is carried as the single explicit interface `GelfondSchneider` (complex, principal-branch
`cpow` form).  The real form used by the reduction is derived from it
(`gelfondSchneiderReal_of_complex`).
-/

import Mathlib
import GaloisForLFunctions.RHTower.WeldClassTable

open scoped Classical

namespace GaloisForLFunctions.RHTower

/-! ### §1 The Gelfond–Schneider interface (the analytic residual) -/

/-- **Gelfond–Schneider (Hilbert's seventh problem), complex principal-branch form.**  For a complex
algebraic base `α ∉ {0, 1}` and a complex algebraic exponent `β` that is not rational, the power
`α ^ β = exp (β · Complex.log α)` (principal branch `Complex.cpow`) is transcendental over `ℚ`.

This is the single hard analytic input, not proved here: its proof is Schneider's two-variable
auxiliary-function method (Siegel's lemma to build the auxiliary polynomial, a maximum-modulus
small-value estimate, and a zero estimate forcing an algebraic integer of norm `< 1` to vanish).
Mathlib supplies the ingredients (`Int.Matrix.exists_ne_zero_int_vec_norm_le`, `NumberField.house`)
but not the assembled argument. -/
def GelfondSchneider : Prop :=
  ∀ (α β : ℂ), IsAlgebraic ℤ α → α ≠ 0 → α ≠ 1 → IsAlgebraic ℤ β →
    (¬ ∃ r : ℚ, β = (r : ℂ)) → Transcendental ℚ (α ^ β)

/-- **Gelfond–Schneider, real form.**  For a positive real algebraic base `a ≠ 1` and a real
algebraic *irrational* exponent `β`, the real power `a ^ β` (`Real.rpow`) is transcendental.  Derived
from the complex form. -/
def GelfondSchneiderReal : Prop :=
  ∀ (a β : ℝ), 0 < a → a ≠ 1 → IsAlgebraic ℤ a → IsAlgebraic ℤ β → Irrational β →
    Transcendental ℚ (a ^ β)

/-- The target-shape restatement of the interface: under `GelfondSchneider`, a complex algebraic
`α ∉ {0,1}` raised to a complex algebraic non-rational `β` is transcendental. -/
theorem gelfond_schneider (hGS : GelfondSchneider) {α β : ℂ} (hα : IsAlgebraic ℤ α)
    (hα0 : α ≠ 0) (hα1 : α ≠ 1) (hβ : IsAlgebraic ℤ β) (hβirr : ¬ ∃ r : ℚ, β = (r : ℂ)) :
    Transcendental ℚ (α ^ β) :=
  hGS α β hα hα0 hα1 hβ hβirr

/-! ### §2 The real ↔ complex transfer, and the real form of Gelfond–Schneider -/

/-- A real number algebraic over `ℤ` remains algebraic over `ℤ` after the embedding `ℝ ↪ ℂ`. -/
private lemma isAlgebraic_ofReal {x : ℝ} (h : IsAlgebraic ℤ x) : IsAlgebraic ℤ (x : ℂ) := by
  have h2 := h.algHom (IsScalarTower.toAlgHom ℤ ℝ ℂ)
  have hx : (IsScalarTower.toAlgHom ℤ ℝ ℂ) x = (x : ℂ) := by
    simp [Complex.coe_algebraMap]
  rwa [hx] at h2

/-- Transcendence transfers back along `ℝ ↪ ℂ`: if the complex embedding of a real number is
transcendental over `ℚ`, so is the real number. -/
private lemma transcendental_ofReal {x : ℝ} (h : Transcendental ℚ (x : ℂ)) :
    Transcendental ℚ x := by
  intro hx
  apply h
  have h2 := hx.algHom (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  have hx2 : (IsScalarTower.toAlgHom ℚ ℝ ℂ) x = (x : ℂ) := by
    simp [Complex.coe_algebraMap]
  rwa [hx2] at h2

/-- **The real Gelfond–Schneider follows from the complex one.**  For a positive real base the
principal-branch complex power `(a : ℂ) ^ (β : ℂ)` equals the real power `↑(a ^ β)`
(`Complex.ofReal_cpow`), so transcendence transfers between the two forms. -/
theorem gelfondSchneiderReal_of_complex (h : GelfondSchneider) : GelfondSchneiderReal := by
  intro a β ha ha1 haAlg hβAlg hβirr
  have hac : IsAlgebraic ℤ (a : ℂ) := isAlgebraic_ofReal haAlg
  have hbc : IsAlgebraic ℤ (β : ℂ) := isAlgebraic_ofReal hβAlg
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have ha1c : (a : ℂ) ≠ 1 := by
    rw [Ne, ← Complex.ofReal_one, Complex.ofReal_inj]; exact ha1
  have hβnr : ¬ ∃ r : ℚ, (β : ℂ) = (r : ℂ) := by
    rintro ⟨r, hr⟩
    apply hβirr
    refine ⟨r, ?_⟩
    have hβr : (β : ℂ) = ((r : ℝ) : ℂ) := by rw [hr]; norm_cast
    exact (Complex.ofReal_inj.mp hβr).symm
  have hcpx : Transcendental ℚ ((a : ℂ) ^ (β : ℂ)) := h (a : ℂ) (β : ℂ) hac ha0 ha1c hbc hβnr
  have hcast : (a : ℂ) ^ (β : ℂ) = ((a ^ β : ℝ) : ℂ) := (Complex.ofReal_cpow ha.le β).symm
  rw [hcast] at hcpx
  exact transcendental_ofReal hcpx

/-! ### §3 The native weld corollary -/

/-- **The ratio of two distinct prime rates is irrational.**  For distinct primes `p, q`,
`log q / log p ∉ ℚ`.  A rational value `a/b` gives `b · log q − a · log p = 0`, a nontrivial
`ℤ`-relation among `log p, log q`, contradicting their unique-factorization independence
(`two_prime_log_indep`). -/
theorem irrational_log_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.log q / Real.log p) := by
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [irrational_iff_ne_rational]
  rintro a b hb hEq
  have hlogq : Real.log q / Real.log p = (a : ℝ) / (b : ℝ) := hEq
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hrel : ((-a : ℤ) : ℝ) * Real.log p + ((b : ℤ) : ℝ) * Real.log q = 0 := by
    have hmul : Real.log q * (b : ℝ) = (a : ℝ) * Real.log p := by
      rw [div_eq_div_iff hlogp_pos.ne' hbR] at hlogq
      linarith [hlogq]
    push_cast
    linarith [hmul]
  have hzero := two_prime_log_indep hp hq hpq (-a) b hrel
  exact hb (by exact_mod_cast hzero.2)

/-- **The ratio of two distinct prime rates is transcendental.**  For distinct primes `p, q`,
`log q / log p` is transcendental over `ℚ`.  The archimedean–difference weld therefore meets the
algebraic numbers only trivially not merely point-by-point (`weld_spectrum_transcendental`) but in
the *commensurability* structure of its spectrum: no two prime rates `log p, log q` are related by an
algebraic factor.  Reduction of Gelfond–Schneider: were the ratio algebraic it would be irrational
(`irrational_log_ratio`), and `p ^ (log q / log p) = q` would then be a transcendental rational
integer. -/
theorem log_ratio_transcendental (hGS : GelfondSchneider) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (Real.log q / Real.log p) := by
  have hGSr : GelfondSchneiderReal := gelfondSchneiderReal_of_complex hGS
  set ξ : ℝ := Real.log q / Real.log p with hξ
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  -- `p ^ ξ = q`.
  have hbridge : (p : ℝ) ^ ξ = (q : ℝ) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hp.pos)]
    have hcancel : Real.log p * ξ = Real.log q := by
      rw [hξ]; field_simp
    rw [hcancel, Real.exp_log (by exact_mod_cast hq.pos)]
  -- The exponent's irrationality is unconditional.
  have hξirr : Irrational ξ := irrational_log_ratio hp hq hpq
  -- Prove transcendence by contradiction with algebraicity.
  intro hξalg
  have hξZ : IsAlgebraic ℤ ξ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hξalg
  have hbase_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hbase_ne_one : (p : ℝ) ≠ 1 := by exact_mod_cast hp.one_lt.ne'
  have hbase_alg : IsAlgebraic ℤ (p : ℝ) := isAlgebraic_nat p
  have hGSapp : Transcendental ℚ ((p : ℝ) ^ ξ) :=
    hGSr (p : ℝ) ξ hbase_pos hbase_ne_one hbase_alg hξZ hξirr
  rw [hbridge] at hGSapp
  exact hGSapp ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp (isAlgebraic_nat q))

end GaloisForLFunctions.RHTower
