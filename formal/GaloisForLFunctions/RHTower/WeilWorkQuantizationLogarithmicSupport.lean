import GaloisForLFunctions.HTGeometry.OperatorTailDirichletMatroid
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardCoefficients
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Numerator-power support of the actual logarithmic deviation

The finite Dirichlet-convolution derivation transfers a power-supported zeta
quotient to the same support for the source weight deviation. Every logarithmic
identity used for the actual source is supplied by full Weil positivity.
-/

open Finset
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilSpectral

def quantizationVonMangoldtC : ArithmeticFunction ℂ where
  toFun n := (ArithmeticFunction.vonMangoldt n : ℂ)
  map_zero' := by simp

theorem quantization_logWeight_zeta :
    logWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) =
      quantizationVonMangoldtC * ArithmeticFunction.zeta := by
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [quantizationVonMangoldtC, ArithmeticFunction.coe_mk, ← Complex.ofReal_sum,
    ArithmeticFunction.vonMangoldt_sum, logWeight_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply]
  by_cases hn : n = 0 <;> simp [hn]

/-- A divisor quotient supported on numerator powers forces the logarithmic
weight deviation to have the same support. -/
theorem quantization_logarithmic_support {u : ℕ} {L a b : ArithmeticFunction ℂ}
    (hb1 : b 1 = 1) (hb : ∀ n : ℕ, (¬∃ j : ℕ, n = u ^ j) → b n = 0)
    (ha : a = ArithmeticFunction.zeta * b) (hL : L * a = logWeight a) :
    ∀ n : ℕ, (¬∃ j : ℕ, n = u ^ j) → L n = ArithmeticFunction.vonMangoldt n := by
  let δ : ArithmeticFunction ℂ := L - quantizationVonMangoldtC
  have hid : (δ * b) * ArithmeticFunction.zeta = logWeight b * ArithmeticFunction.zeta := by
    calc
      (δ * b) * ArithmeticFunction.zeta =
          L * (ArithmeticFunction.zeta * b) -
            (quantizationVonMangoldtC * ArithmeticFunction.zeta) * b := by dsimp [δ]; ring
      _ = logWeight (ArithmeticFunction.zeta * b) -
          logWeight (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * b := by
        rw [← ha, hL, quantization_logWeight_zeta]
      _ = logWeight b * ArithmeticFunction.zeta := by rw [logWeight_leibniz]; ring
  have heq : δ * b = logWeight b := by
    have h := congrArg (fun f : ArithmeticFunction ℂ =>
      f * (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) hid
    simpa only [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] using h
  have hs : ∀ n : ℕ, (¬∃ j : ℕ, n = u ^ j) → δ n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      have he := congrArg (fun f : ArithmeticFunction ℂ => f n) heq
      rw [ArithmeticFunction.mul_apply, logWeight_apply, hb n hn, mul_zero] at he
      have hsum : (∑ p ∈ n.divisorsAntidiagonal, δ p.1 * b p.2) = δ n := by
        rw [sum_eq_single (n,1)]
        · simp [hb1]
        · intro p hp hpne
          obtain ⟨hpn, hnz⟩ := Nat.mem_divisorsAntidiagonal.mp hp
          by_cases hp2 : ∃ j : ℕ, p.2 = u ^ j
          · obtain ⟨j, hj⟩ := hp2
            have hp1 : ¬∃ i : ℕ, p.1 = u ^ i := by
              rintro ⟨i, hi⟩
              apply hn
              refine ⟨i+j, ?_⟩
              rw [← hpn, hi, hj, pow_add]
            have hplt : p.1 < n := by
              have hp1pos : 0 < p.1 := by nlinarith
              have hp2pos : 0 < p.2 := by nlinarith
              have hp2ne : p.2 ≠ 1 := by
                intro he2
                apply hpne
                apply Prod.ext
                · simpa [he2] using hpn
                · exact he2
              have hp2ge : 2 ≤ p.2 := by omega
              nlinarith
            rw [ih p.1 hplt hp1, zero_mul]
          · rw [hb p.2 hp2, mul_zero]
        · intro hnmem
          exact False.elim (hnmem (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn0.ne'⟩))
      rwa [hsum] at he
  intro n hn
  have h := hs n hn
  change L n - (ArithmeticFunction.vonMangoldt n : ℂ) = 0 at h
  exact sub_eq_zero.mp h

theorem quantization_source_logarithmic_support {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {u : ℕ} {b : ArithmeticFunction ℂ} (hb1 : b 1 = 1)
    (hb : ∀ n : ℕ, (¬∃ j : ℕ, n = u ^ j) → b n = 0)
    (ha : ∀ n : ℕ, (ArithmeticFunction.zeta * b) n = WeilSingularArithmetic.forwardCoeff lam n) :
    ∀ n : ℕ, 2 ≤ n → (¬∃ j : ℕ, n = u ^ j) → lam n = ArithmeticFunction.vonMangoldt n := by
  let L : ArithmeticFunction ℂ := ⟨WeilHerglotz.lamC lam, by simp [WeilHerglotz.lamC]⟩
  let a : ArithmeticFunction ℂ := ⟨WeilSingularArithmetic.forwardCoeff lam, by simp⟩
  have he : a = ArithmeticFunction.zeta * b := by ext n; exact (ha n).symm
  have hd : L * a = logWeight a := by
    ext n
    have h := WeilSingularArithmetic.forwardCoeff_log_convolution hW n
    rw [← ArithmeticFunction.coe_mul, logWeight_apply]
    convert h using 1 <;> rfl
  intro n hn hnp
  have h := quantization_logarithmic_support hb1 hb he hd n hnp
  change ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ) = _ at h
  rw [if_pos hn] at h
  exact_mod_cast h

end RHTower.WeilSpectral
