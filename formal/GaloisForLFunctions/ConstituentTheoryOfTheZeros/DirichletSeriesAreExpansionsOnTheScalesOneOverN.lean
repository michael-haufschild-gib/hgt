import GaloisForLFunctions.ConstituentTheoryOfTheZeros.WienersLemmaOnAStrip
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Dirichlet series are expansions on the scales `1/n`

A Dirichlet series `Σ a(n) n^{−s}` is the expansion `Σ_q c(q) q^s` whose coefficients sit on the
scales `q = 1/n` (`dirichletCoeff`). If the series converges absolutely at a real point `x`, the
expansion converges absolutely on every closed strip right of `x`
(`wsummable_dirichletCoeff`) and equals the L-series there (`expansion_dirichletCoeff`).
-/

open LSeries

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

variable {σ₁ σ₂ : ℝ}

/-- The scale `1/(n + 1)`. -/
def invNat (n : ℕ) : Scale := (Scale.ofNat (n + 1))⁻¹

theorem toReal_invNat (n : ℕ) : (invNat n).toReal = (((n + 1 : ℕ) : ℝ))⁻¹ := by
  unfold invNat
  rw [Scale.toReal_inv, Scale.toReal_ofNat n.succ_pos]

theorem invNat_injective : Function.Injective invNat := fun m n h => by
  have h' := congrArg Scale.toReal h
  rw [toReal_invNat, toReal_invNat, inv_inj] at h'
  have h'' : m + 1 = n + 1 := by exact_mod_cast h'
  omega

/-- `(1/(n+1))^s = 1/(n+1)^s`. -/
theorem invNat_cpow (n : ℕ) (s : ℂ) : (invNat n).cpow s = (((n + 1 : ℕ) : ℂ) ^ s)⁻¹ := by
  unfold Scale.cpow
  rw [toReal_invNat, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow]
  rw [Complex.natCast_arg]
  exact Real.pi_pos.ne

/-- On the scale `1/(n+1)` the weight of a strip is `(n+1)^{−σ₁}`. -/
theorem stripWeight_invNat (h12 : σ₁ ≤ σ₂) (n : ℕ) :
    stripWeight σ₁ σ₂ (invNat n) = ((n + 1 : ℕ) : ℝ) ^ (-σ₁) := by
  have h0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast n.succ_pos
  unfold stripWeight
  rw [toReal_invNat, Real.inv_rpow h0, Real.inv_rpow h0, ← Real.rpow_neg h0, ← Real.rpow_neg h0]
  exact max_eq_left (Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg h12))

/-- The coefficients of the Dirichlet series `Σ a(n) n^{−s}`, on the scales `1/n`. -/
def dirichletCoeff (a : ℕ → ℂ) : Scale → ℂ := Function.extend invNat (fun n => a (n + 1)) 0

theorem dirichletCoeff_invNat (a : ℕ → ℂ) (n : ℕ) : dirichletCoeff a (invNat n) = a (n + 1) :=
  invNat_injective.extend_apply _ _ n

theorem dirichletCoeff_of_notMem_range (a : ℕ → ℂ) {q : Scale} (hq : q ∉ Set.range invNat) :
    dirichletCoeff a q = 0 :=
  Function.extend_apply' _ _ _ fun ⟨n, hn⟩ => hq ⟨n, hn⟩

theorem dirichletCoeff_ne_zero {a : ℕ → ℂ} {n : ℕ} (hn : a (n + 1) ≠ 0) : dirichletCoeff a ≠ 0 :=
  fun h => hn (by rw [← dirichletCoeff_invNat a n, h, Pi.zero_apply])

/-- A Dirichlet series absolutely convergent at `x` converges absolutely, as an expansion, on
every closed strip right of `x`. -/
theorem wsummable_dirichletCoeff {a : ℕ → ℂ} {x : ℝ} (hsum : LSeriesSummable a x) (h1 : x ≤ σ₁)
    (h12 : σ₁ ≤ σ₂) : WSummable σ₁ σ₂ (dirichletCoeff a) := by
  unfold WSummable
  rw [← invNat_injective.summable_iff fun q hq => by
    rw [dirichletCoeff_of_notMem_range a hq, norm_zero, zero_mul]]
  have h := (summable_nat_add_iff 1).mpr hsum.norm
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (stripWeight_pos σ₁ σ₂ _).le) (fun n => ?_) h
  have h1' : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast n.succ_pos
  show ‖dirichletCoeff a (invNat n)‖ * stripWeight σ₁ σ₂ (invNat n) ≤ ‖term a x (n + 1)‖
  rw [dirichletCoeff_invNat, stripWeight_invNat h12, LSeries.norm_term_eq, if_neg n.succ_ne_zero,
    Complex.ofReal_re, div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1' (neg_le_neg h1))
    (norm_nonneg _)

/-- Right of a point of absolute convergence the expansion is the L-series. -/
theorem expansion_dirichletCoeff {a : ℕ → ℂ} {x : ℝ} (hsum : LSeriesSummable a x) {s : ℂ}
    (hs : x ≤ s.re) : expansion (dirichletCoeff a) s = LSeries a s := by
  have hs' : LSeriesSummable a s := hsum.of_re_le_re (by rwa [Complex.ofReal_re])
  have hsupp : Function.support (fun q : Scale => dirichletCoeff a q * q.cpow s) ⊆
      Set.range invNat := fun q hq => by
    by_contra h
    exact hq (by
      show dirichletCoeff a q * q.cpow s = 0
      rw [dirichletCoeff_of_notMem_range a h, zero_mul])
  unfold expansion LSeries
  rw [hs'.tsum_eq_zero_add, LSeries.term_zero, zero_add, ← invNat_injective.tsum_eq hsupp]
  refine tsum_congr fun n => ?_
  rw [dirichletCoeff_invNat, invNat_cpow, LSeries.term_of_ne_zero n.succ_ne_zero, div_eq_mul_inv]

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
