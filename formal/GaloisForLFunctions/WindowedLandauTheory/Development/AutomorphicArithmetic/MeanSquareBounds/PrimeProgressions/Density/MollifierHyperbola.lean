import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.SpacedMollifierDetection
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticHarmonicConvolution
import GaloisForLFunctions.RHTower.Mollifier

/-! Dirichlet hyperbola expansion of the truncated Möbius detector. -/

open Complex Finset ArithmeticFunction

namespace QH.PrimeProgressions

private theorem sum_initial_mollifier (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℂ) :
    ∑ n ∈ Ioc 0 (Q ^ 3), mollifierCoeff Q n * f n = f 1 := by
  have hD : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
  rw [sum_eq_single 1]
  · rw [mollifierCoeff_eq hQ, Nat.divisors_one, Finset.filter_singleton, if_pos hD, Finset.sum_singleton]
    simp
  · intro n hn hn1
    rw [mollifierCoeff_eq hQ, filter_true_of_mem (fun _ hd =>
      (Nat.divisor_le hd).trans (mem_Ioc.mp hn).2), ← Int.cast_sum, RHTower.sum_moebius_divisors,
      if_neg hn1]
    simp
  · exact fun h => absurd (mem_Ioc.mpr ⟨zero_lt_one, hD⟩) h

/-- The complete multiplicativity of the character power gives the exact hyperbola expansion. -/
theorem mollifierTail_eq_hyperbola {q Q : ℕ} (hQ : 0 < Q)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    let f := fun n : ℕ => χ (n : ZMod q) * (n : ℂ) ^ (-s)
    mollifierTail Q χ s =
      (∑ d ∈ Icc 1 (Q ^ 3), (moebius d : ℂ) * f d * ∑ m ∈ Icc 1 (Q ^ 6 / d), f m) - 1 := by
  let f (n : ℕ) := χ (n : ZMod q) * (n : ℂ) ^ (-s)
  let D := Q ^ 3
  let X := Q ^ 6
  have hDX : D ≤ X := Nat.pow_le_pow_right hQ (by omega)
  have hsplit := sum_Ioc_consecutive (fun n => mollifierCoeff Q n * f n) (Nat.zero_le D) hDX
  have hinit : ∑ n ∈ Ioc 0 D, mollifierCoeff Q n * f n = 1 := by
    rw [sum_initial_mollifier Q hQ]
    simp [f]
  let G (p : ℕ × ℕ) : ℂ :=
    (if p.1 ≤ D then (moebius p.1 : ℂ) else 0) * (f p.1 * f p.2)
  have hmul (d m : ℕ) : f (d * m) = f d * f m := by
    simp only [f, Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hmain : ∑ n ∈ Ioc 0 X, mollifierCoeff Q n * f n =
      ∑ d ∈ Icc 1 D, (moebius d : ℂ) * f d * ∑ m ∈ Icc 1 (X / d), f m := by
    have hset : Ioc 0 X = Icc 1 X := by
      ext n
      simp only [mem_Ioc, mem_Icc, Nat.succ_le_iff]
    rw [hset]
    calc
      _ = ∑ n ∈ Icc 1 X, ∑ p ∈ n.divisorsAntidiagonal, G p := by
        refine sum_congr rfl fun n hn => ?_
        have hterm (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal) :
            G p = (if p.1 ≤ D then (moebius p.1 : ℂ) else 0) * f n := by
          dsimp only [G]
          rw [← hmul, (Nat.mem_divisorsAntidiagonal.mp hp).1]
        rw [sum_congr rfl hterm, ← sum_mul,
          Nat.sum_divisorsAntidiagonal (fun d _ => if d ≤ D then (moebius d : ℂ) else 0),
          mollifierCoeff_eq hQ]
        rw [sum_filter]
      _ = ∑ d ∈ Icc 1 X, ∑ m ∈ Icc 1 (X / d), G (d, m) :=
        RHTower.WeilSingularArithmetic.sum_divisors_hyperbola G X
      _ = _ := by
        have hsub : Icc 1 D ⊆ Icc 1 X := Icc_subset_Icc_right hDX
        rw [← sum_subset hsub (fun d hd hd' => by
          have h : ¬d ≤ D := fun h => hd' (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, h⟩)
          simp [G, h])]
        refine sum_congr rfl fun d hd => ?_
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by simp [G, (mem_Icc.mp hd).2, mul_assoc]
  change mollifierTail Q χ s = _
  rw [← hsplit, hinit] at hmain
  have htail : mollifierTail Q χ s = ∑ n ∈ Ioc D X, mollifierCoeff Q n * f n :=
    sum_congr rfl fun _ _ => mul_assoc _ _ _
  rw [htail, ← hmain]
  ring

end QH.PrimeProgressions
