import GaloisForLFunctions.RHTower.PrimePolarHLHolomorphic
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone
import GaloisForLFunctions.RHTower.PrimePolarWeightedError

/-!
# Meromorphic continuation of the moving-tent series

The continuation identity `(20)` of `prime-polar-moving-tent-divisor-tomography` §4.  For `Re s > 3/2`
the `Λ(k)/√k`-weighted moving-tent source series equals

`∑_k (Λ(k)/√k)·(∑_{j} τ_L(log(j/k))·j^{-s}) = I_L(s)·(-ζ'/ζ)(s-½) + H_L(s)`,

where `I_L(s) = A_L(s-1)²`.  This is the meromorphic continuation to `Re s > 1`: the only poles come
from the `ζ`-logarithmic-derivative factor, and `H_L` is holomorphic (`HL_differentiableOn`).

The identity is pure `tsum` linearity — no Fubini is needed in this direction.  Each summand splits as
`(Λ(k)/√k)·(E_{k,L}(s) + k^{1-s}·I_L(s))`; the `E_{k,L}` part sums to `H_L` (definition), and the
`k^{1-s}` part factors `I_L(s)` out of the shifted von Mangoldt Dirichlet series
`∑_k (Λ(k)/√k)·k^{1-s} = ∑_k Λ(k)·k^{-(s-½)} = -ζ'/ζ(s-½)` (`vonMangoldt_shifted_logDeriv`).  Both
pieces are absolutely summable (`weighted_E_summable` and `LSeriesSummable_vonMangoldt`).
-/

open ArithmeticFunction

namespace RHTower


theorem weighted_pow_term (s : ℂ) (k : ℕ) :
    (Λ k / Real.sqrt k) • (k : ℂ) ^ (1 - s) = LSeries.term (fun n => (Λ n : ℂ)) (s - 1 / 2) k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0; simp [LSeries.term_zero]
  · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    rw [LSeries.term_of_ne_zero hk.ne', Complex.real_smul]
    have hsqrt : (Real.sqrt k : ℂ) = (k : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, ← Complex.ofReal_natCast, Complex.ofReal_cpow hkR.le]; norm_num
    rw [Complex.ofReal_div, hsqrt, div_mul_eq_mul_div, mul_div_assoc,
      ← Complex.cpow_sub _ _ hkc, div_eq_mul_inv ((Λ k : ℂ)) _, ← Complex.cpow_neg]
    congr 2; ring

theorem movingTent_continuation (L : ℝ) (hL : 0 ≤ L) (s : ℂ) (hs32 : 3 / 2 < s.re) :
    (∑' k : ℕ, (Λ k / Real.sqrt k) • (∑ j ∈ Finset.range (Nof L k),
        (tentPos L (Real.log ((j : ℝ) / (k : ℝ))) : ℂ) * (j : ℂ) ^ (-s)))
      = (rectangularWindowAmplitude L (s - 1)) ^ 2
          * (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2)) + HL L s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs32; norm_num at hs32
  have hσ : 1 / 2 < s.re := by linarith
  set A2 := (rectangularWindowAmplitude L (s - 1)) ^ 2 with hA2
  have hnorm_eq : ∀ k : ℕ, ‖(Λ k / Real.sqrt k) • Eterm L k s‖
      = (Λ k / Real.sqrt k) * ‖Eterm L k s‖ := fun k => by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _))]
  have hsumE : Summable (fun k : ℕ => (Λ k / Real.sqrt k) • Eterm L k s) := by
    apply Summable.of_norm
    simp only [hnorm_eq]
    exact weighted_E_summable L hL s hs1 hσ
  have hLSsum : Summable (fun k : ℕ => (Λ k / Real.sqrt k) • (k : ℂ) ^ (1 - s)) := by
    have hsum := LSeriesSummable_vonMangoldt (s := s - 1 / 2)
      (by rw [Complex.sub_re]; simp; linarith)
    refine hsum.congr (fun k => (weighted_pow_term s k).symm)
  have hterm : ∀ k, (Λ k / Real.sqrt k) • (∑ j ∈ Finset.range (Nof L k),
        (tentPos L (Real.log ((j : ℝ) / (k : ℝ))) : ℂ) * (j : ℂ) ^ (-s))
      = (Λ k / Real.sqrt k) • Eterm L k s + (Λ k / Real.sqrt k) • (k : ℂ) ^ (1 - s) * A2 := by
    intro k
    have he : (∑ j ∈ Finset.range (Nof L k),
        (tentPos L (Real.log ((j : ℝ) / (k : ℝ))) : ℂ) * (j : ℂ) ^ (-s))
        = Eterm L k s + (k : ℂ) ^ (1 - s) * A2 := by rw [Eterm, hA2]; ring
    rw [he, smul_add, smul_mul_assoc]
  rw [tsum_congr hterm, Summable.tsum_add hsumE (hLSsum.mul_right A2), tsum_mul_right,
    tsum_congr (weighted_pow_term s)]
  rw [show (∑' k, LSeries.term (fun n => (Λ n : ℂ)) (s - 1 / 2) k)
      = LSeries (fun n => (Λ n : ℂ)) (s - 1 / 2) from rfl, vonMangoldt_shifted_logDeriv s hs32]
  rw [show (∑' k, (Λ k / Real.sqrt k) • Eterm L k s) = HL L s from rfl]
  ring
