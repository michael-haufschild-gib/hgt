import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity

/-!
# The parity twin is geometric only in the Bohr closure

Over `𝔽_q` the twist tower completes the upper count because the parity twin is **geometric**: the
quadratic twist of a base change is a vertical shift `s ↦ s + iπ/log q` of its zeta function, so a
producer of upper counts applies to it. The question here is whether the Liouville twin over `ℤ` is
geometric in the same sense: is it a vertical shift `u ↦ u^{iτ}` (`shiftChar`), which moves every
zero by `iτ`?

**Over `𝔽_q` the shift is the degree parity** (`shift_pow_eq_neg_one_pow`). All norms are powers of
`q`, so `u ↦ u^{iπ/log q}` is `(−1)^{deg}` at every place: `−1` at every place of odd degree.

**On one prime tower the twin is geometric** (`shiftChar_primeElt_zpow`). The shift by `π / log p` is
`(−1)^n` on `p^n`, which is the Liouville twin on `⟨p⟩`.

**On two primes it is not** (`shiftChar_eq_neg_one_subsingleton`). A shift is `−1` at `p` only if
`τ log p` is an odd multiple of `π`; at two primes this gives `p^{2b+1} = q^{2a+1}` up to sign of the
exponents, impossible by unique factorization. Every geometric twin over `ℤ` is `−1` at **at most one
prime**, against a positive proportion of places over `𝔽_q`. Two-prime lattices carry the whole index
(`negIndex_orbitKernel_eq_iSup_twoPrime_towers`), so no vertical shift realizes the twin where the
index lives.

**In the Bohr closure it is** (`exists_shiftChar_near_neg_one`). The logarithms of the primes are
linearly independent over `ℚ`, so by Kronecker some shift is within `ε` of `−1` at every prime
`p ≤ N`. The Liouville twin is a limit of vertical shifts on every finite set of primes and equal to
none: a geometric parity twin over `ℤ` must live in the Bohr compactification of the shifts, not
among them.
-/

open Complex
open scoped Real
open GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- The vertical shift `u ↦ u^{iτ}` on `ℚ_{>0}`; on kernels it moves every zero by `iτ`. -/
def shiftChar (τ : ℝ) : HeckeLattice →* ℂ := logChar heckeLogScale (τ * I)

theorem shiftChar_primeElt (τ : ℝ) {p : ℕ} (hp : p.Prime) :
    shiftChar τ (primeElt hp) = cexp (((τ * Real.log p : ℝ) : ℂ) * I) := by
  rw [shiftChar, logChar_apply, scale_primeElt]
  push_cast
  ring_nf

/-- **Over `𝔽_q` the shift is the degree parity.** `(q^d)^{iπ/log q} = (−1)^d`. -/
theorem shift_pow_eq_neg_one_pow {q : ℝ} (hq : 1 < q) (d : ℕ) :
    cexp ((((π / Real.log q) * Real.log (q ^ d) : ℝ) : ℂ) * I) = (-1) ^ d := by
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq).ne'
  rw [Real.log_pow, show π / Real.log q * (d * Real.log q) = d * π by field_simp, ← exp_pi_mul_I,
    ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- **On one prime tower the parity twin is geometric.** The shift by `π / log p` is `(−1)^n` on
`p^n`. -/
theorem shiftChar_primeElt_zpow {p : ℕ} (hp : p.Prime) (n : ℤ) :
    shiftChar (π / Real.log p) (primeElt hp ^ n) = (-1) ^ n := by
  have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [map_zpow, shiftChar_primeElt, div_mul_cancel₀ _ hlog, exp_pi_mul_I]

/-- A vertical shift is `−1` at `p` only if `τ log p` is an odd multiple of `π`. -/
theorem exists_odd_of_shiftChar_eq_neg_one {τ : ℝ} {p : ℕ} (hp : p.Prime)
    (h : shiftChar τ (primeElt hp) = -1) : ∃ a : ℤ, τ * Real.log p = (2 * a + 1) * π := by
  rw [shiftChar_primeElt, ← exp_pi_mul_I, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  have him := congrArg Complex.im ha
  simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, add_im,
    intCast_re, intCast_im, re_ofNat, im_ofNat, mul_re, zero_mul, sub_zero, add_zero] at him
  linear_combination him

/-- **On two primes the parity twin is not geometric.** No vertical shift is `−1` at two distinct
primes. -/
theorem shiftChar_eq_neg_one_subsingleton (τ : ℝ) :
    {p : Nat.Primes | shiftChar τ (primeElt p.2) = -1}.Subsingleton := by
  intro p hp q hq
  by_contra hne
  obtain ⟨a, ha⟩ := exists_odd_of_shiftChar_eq_neg_one p.2 hp
  obtain ⟨b, hb⟩ := exists_odd_of_shiftChar_eq_neg_one q.2 hq
  have hlp : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hlq : 0 < Real.log (q : ℕ) := Real.log_pos (by exact_mod_cast q.2.one_lt)
  have hτ : τ ≠ 0 := by
    rintro rfl
    have h0 : ((2 * a + 1 : ℤ) : ℝ) = 0 := by
      push_cast
      nlinarith [Real.pi_pos]
    have : (2 * a + 1 : ℤ) = 0 := by exact_mod_cast h0
    omega
  -- `(2b+1) log p = (2a+1) log q`
  have key : ((2 * b + 1 : ℤ) : ℝ) * Real.log (p : ℕ) = ((2 * a + 1 : ℤ) : ℝ) * Real.log (q : ℕ) := by
    apply mul_left_cancel₀ hτ
    push_cast
    linear_combination (2 * (b : ℝ) + 1) * ha - (2 * (a : ℝ) + 1) * hb
  -- take absolute values and exponentiate: `p^k = q^l`
  have habs := congrArg abs key
  rw [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq, ← Int.cast_abs, ← Int.cast_abs,
    Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.cast_natCast, Int.cast_natCast, ← Real.log_pow,
    ← Real.log_pow] at habs
  have hpow : ((p : ℕ) : ℝ) ^ (2 * b + 1).natAbs = ((q : ℕ) : ℝ) ^ (2 * a + 1).natAbs :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by have := p.2.pos; positivity))
      (Set.mem_Ioi.mpr (by have := q.2.pos; positivity)) habs
  have hpowN : (p : ℕ) ^ (2 * b + 1).natAbs = (q : ℕ) ^ (2 * a + 1).natAbs := by exact_mod_cast hpow
  have hk : (2 * b + 1).natAbs ≠ 0 := by omega
  have hdvd : (p : ℕ) ∣ (q : ℕ) ^ (2 * a + 1).natAbs :=
    hpowN ▸ dvd_pow_self _ hk
  exact hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp (p.2.dvd_of_dvd_pow hdvd)))

/-- **In the Bohr closure the parity twin is geometric.** For every `N` and `ε > 0` some vertical
shift is within `ε` of `−1` at every prime `p ≤ N`. -/
theorem exists_shiftChar_near_neg_one (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, ∀ p : Nat.Primes, (p : ℕ) ≤ N → ‖shiftChar τ (primeElt p.2) + 1‖ < ε := by
  obtain ⟨t, ht⟩ := primeTorus_kronecker_dense N (fun _ => π) hε
  refine ⟨t, fun p hpN => ?_⟩
  have h := ht ⟨p, (mem_primesLE N p).mpr hpN⟩
  unfold GaloisForLFunctions.expChar at h
  rw [shiftChar_primeElt, mul_comm t, ← sub_neg_eq_add, ← exp_pi_mul_I]
  exact h

end GaloisForLFunctions.ArithmeticKreinLangerTheory
