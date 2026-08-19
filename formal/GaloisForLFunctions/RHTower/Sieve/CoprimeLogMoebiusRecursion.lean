import GaloisForLFunctions.RHTower.Sieve.MoebiusPrimePeeling
import GaloisForLFunctions.RHTower.Sieve.LogMoebiusBounded

/-!
# The coprime logarithmic Möbius sum and its prime recursion

For a modulus `e` and a real cutoff `Y` set

`T_e(Y) = ∑_{j ≤ Y, (e,j) = 1} μ(j) log(Y/j) / j`.

Feeding the Möbius prime-peeling recursion the weight `log(Y/j)/j` turns the peeled correction into
the *same* functional at the divided cutoff:

`T_e(Y) = T_{pe}(Y) − (1/p) · T_{pe}(Y/p)`,

because `log(Y/(pj))/(pj) = (1/p) · log((Y/p)/j)/j`.  This is a genuine contraction — the cutoff
shrinks by the factor `p` — and it is the mechanism that produces the Euler factor
`(1 − 1/p)^{-1}` for each prime of the modulus.

The modulus-one case is bounded by an absolute constant, and the passage from an integer cutoff to
a real one costs at most one extra unit.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- The coprime logarithmic Möbius sum `T_e(Y) = ∑_{j ≤ Y, (e,j)=1} μ(j) log(Y/j)/j`. -/
noncomputable def coprimeLogMoebius (e : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun j => Nat.Coprime e j),
    ((μ j : ℤ) : ℝ) / (j : ℝ) * Real.log (Y / (j : ℝ))

/-- Below the first integer the sum is empty. -/
theorem coprimeLogMoebius_of_lt_one (e : ℕ) {Y : ℝ} (hY : Y < 1) :
    coprimeLogMoebius e Y = 0 := by
  have h0 : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr hY
  rw [coprimeLogMoebius, h0, Finset.Icc_eq_empty (by norm_num), Finset.filter_empty,
    Finset.sum_empty]

/-- **The contraction recursion.**  Removing one prime `p` from the modulus reproduces the same
functional at the cutoff `Y/p`, with the weight `1/p`. -/
theorem coprimeLogMoebius_recursion {p e : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e) (Y : ℝ) :
    coprimeLogMoebius e Y
      = coprimeLogMoebius (p * e) Y
        - (1 / (p : ℝ)) * coprimeLogMoebius (p * e) (Y / (p : ℝ)) := by
  classical
  have hpeel := sum_moebius_peel (p := p) (e := e) (y := ⌊Y⌋₊) hp hpe
    (fun j => Real.log (Y / (j : ℝ)) / (j : ℝ))
  have hA : coprimeLogMoebius e Y
      = ∑ j ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun j => Nat.Coprime e j),
          ((μ j : ℤ) : ℝ) * (Real.log (Y / (j : ℝ)) / (j : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hB : coprimeLogMoebius (p * e) Y
      = ∑ j ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun j => Nat.Coprime (p * e) j),
          ((μ j : ℤ) : ℝ) * (Real.log (Y / (j : ℝ)) / (j : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfloor : ⌊Y / (p : ℝ)⌋₊ = ⌊Y⌋₊ / p := Nat.floor_div_natCast Y p
  have hC : (1 / (p : ℝ)) * coprimeLogMoebius (p * e) (Y / (p : ℝ))
      = ∑ j ∈ (Finset.Icc 1 (⌊Y⌋₊ / p)).filter (fun j => Nat.Coprime (p * e) j),
          ((μ j : ℤ) : ℝ) * (Real.log (Y / ((p * j : ℕ) : ℝ)) / ((p * j : ℕ) : ℝ)) := by
    rw [coprimeLogMoebius, hfloor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcast : ((p * j : ℕ) : ℝ) = (p : ℝ) * (j : ℝ) := by push_cast; ring
    have harg : Y / ((p : ℝ) * (j : ℝ)) = Y / (p : ℝ) / (j : ℝ) := (div_div Y (p : ℝ) (j : ℝ)).symm
    rw [hcast, harg]
    ring
  rw [hA, hB, hC]
  exact hpeel

/-- At modulus one the sum is bounded by an absolute constant, uniformly in the real cutoff. -/
theorem abs_coprimeLogMoebius_one_le (Y : ℝ) :
    |coprimeLogMoebius 1 Y| ≤ 6 + |Real.eulerMascheroniConstant| := by
  classical
  rcases lt_or_ge Y 1 with hY | hY
  · rw [coprimeLogMoebius_of_lt_one 1 hY, abs_zero]
    have := abs_nonneg (Real.eulerMascheroniConstant)
    linarith
  · set N : ℕ := ⌊Y⌋₊ with hN
    have hN1 : 1 ≤ N := Nat.one_le_floor_iff Y |>.mpr hY
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
    have hYlt : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
    have hfil : (Finset.Icc 1 N).filter (fun j => Nat.Coprime 1 j) = Finset.Icc 1 N := by
      refine Finset.filter_true_of_mem fun j _ => ?_
      exact Nat.coprime_one_left j
    have hsplit : coprimeLogMoebius 1 Y
        = (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) * Real.log ((N : ℝ) / (d : ℝ)))
          + Real.log (Y / (N : ℝ)) * ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) := by
      rw [coprimeLogMoebius, ← hN, hfil, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hlog : Real.log (Y / (d : ℝ))
          = Real.log ((N : ℝ) / (d : ℝ)) + Real.log (Y / (N : ℝ)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      rw [hlog]
      ring
    have hmain := abs_sum_moebius_log_div_le N hN1
    have hmoeb := RHTower.abs_sum_moebius_div_le_one N hN1
    have hlogle : |Real.log (Y / (N : ℝ))| ≤ 1 := by
      have h1 : (1 : ℝ) ≤ Y / (N : ℝ) := (one_le_div hNR).mpr hNle
      have h2 : Y / (N : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hNR]
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
        linarith
      have hpos : (0 : ℝ) < Y / (N : ℝ) := by linarith
      have hupper : Real.log (Y / (N : ℝ)) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos hpos
        linarith
      have hlower : (0 : ℝ) ≤ Real.log (Y / (N : ℝ)) := Real.log_nonneg h1
      rw [abs_of_nonneg hlower]
      exact hupper
    rw [hsplit]
    have hprod : |Real.log (Y / (N : ℝ)) * ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)| ≤ 1 := by
      rw [abs_mul]
      calc |Real.log (Y / (N : ℝ))| * |∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)|
          ≤ 1 * 1 := mul_le_mul hlogle hmoeb (abs_nonneg _) zero_le_one
        _ = 1 := by norm_num
    calc |(∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) * Real.log ((N : ℝ) / (d : ℝ)))
            + Real.log (Y / (N : ℝ)) * ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)|
        ≤ _ := abs_add_le _ _
      _ ≤ 6 + |Real.eulerMascheroniConstant| := by linarith

end RHTower.Sieve
