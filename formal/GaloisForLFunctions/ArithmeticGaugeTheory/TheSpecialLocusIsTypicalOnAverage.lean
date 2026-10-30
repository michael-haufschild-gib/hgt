import GaloisForLFunctions.ArithmeticGaugeTheory.TheSpecialLocusReadsGRH
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant

/-!
# The special locus is typical on average

At a single primitive Dirichlet point the Möbius exponent is `Θ_χ`, and its typicality is GRH for `χ`
(`dirichletGRH_iff_dirichletGauge_typical`). On average over the special locus typicality holds
unconditionally, at every scale.

* **Mean square over the special locus** (`largeSieve_coprimeMoebius_dirichletGauge`). The coprime
  Möbius gauge sums `C_q(N)` at the primitive Dirichlet points of conductor at most `R`, weighted by
  `q/φ(q)`, have total mean square at most `(N + R²)(N + 1)`. With `R² ≤ N + 1` this is `2(N + 1)²`,
  spread over about `R²` points: square-root size on average, as at a Haar-random point.
* **Few atypical special points** (`card_atypical_dirichletGauge_le`). At scale `N`, at most
  `(N + R²)(N + 1)/V` primitive Dirichlet points of conductor at most `R` have `|C_q(N)|² > V`. For
  `R² ≤ N + 1` and `V = (N + 1)^{1 + 2ε}` this is at most `2 (N + 1)^{1 − 2ε}`, while there are about
  `N` such points (`card_atypical_dirichletGauge_le_rpow`).

The exceptions may change with `N`, so this is not an exponent statement for any fixed point; the
exponent of a fixed point is decided by the zeros of its `L`-function.
-/

open Finset
open scoped ComplexConjugate ArithmeticFunction.Moebius LSeries.notation

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- The coprime Möbius gauge sum at a Dirichlet point, as a twisted Mertens sum. -/
theorem norm_coprimeMoebiusSet_dirichletGauge {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (N : ℕ) :
    ‖coprimeMoebiusSet q.primeFactors (dirichletGauge ψ) N‖ =
      ‖∑ n ∈ range (N + 1), ((μ n : ℤ) : ℂ) * conj (ψ n)‖ := by
  rw [coprimeMoebiusSet_primeFactors_dirichletGauge, RHTower.partialSumSeq, ← Complex.norm_conj,
    map_sum]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  simp only [Pi.mul_apply, map_mul, map_intCast]
  ring

open Classical in
/-- **Mean square over the special locus.** -/
theorem largeSieve_coprimeMoebius_dirichletGauge (N R : ℕ) (hR : 2 ≤ R) :
    ∑ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2 ≤
      ((N : ℝ) + R ^ 2) * ((N : ℝ) + 1) := by
  have hsieve := BezoutValuationIncidence.multiplicative_largeSieve_sharp (N + 1) R hR
    (fun n => ((μ n : ℤ) : ℂ))
  have hmass : ∑ n ∈ range (N + 1), ‖((μ n : ℤ) : ℂ)‖ ^ 2 ≤ (N : ℝ) + 1 := by
    calc ∑ n ∈ range (N + 1), ‖((μ n : ℤ) : ℂ)‖ ^ 2 ≤ ∑ _n ∈ range (N + 1), (1 : ℝ) := by
          refine sum_le_sum fun n _ => ?_
          have h := norm_moebiusSource_le n
          rw [moebiusSource] at h
          nlinarith [norm_nonneg ((μ n : ℤ) : ℂ)]
      _ = (N : ℝ) + 1 := by simp
  simp_rw [norm_coprimeMoebiusSet_dirichletGauge]
  refine hsieve.trans ?_
  have hR0 : (0 : ℝ) ≤ (R : ℝ) ^ 2 := by positivity
  calc (((N + 1 : ℕ) : ℝ) + (R : ℝ) ^ 2 - 1) * ∑ n ∈ range (N + 1), ‖((μ n : ℤ) : ℂ)‖ ^ 2
      = ((N : ℝ) + R ^ 2) * ∑ n ∈ range (N + 1), ‖((μ n : ℤ) : ℂ)‖ ^ 2 := by push_cast; ring
    _ ≤ ((N : ℝ) + R ^ 2) * ((N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)

open Classical in
/-- The primitive Dirichlet points of conductor at most `R` at which the coprime Möbius gauge sum
of length `N` exceeds `V` in square norm. -/
def atypicalDirichletPoints (N R : ℕ) (V : ℝ) : Finset (Σ r : ℕ, DirichletCharacter ℂ (r + 1)) :=
  (range R).sigma fun r =>
    ((univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive)).filter
      fun ψ => V < ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2

/-- **Few atypical special points.** -/
theorem card_atypical_dirichletGauge_le (N R : ℕ) (hR : 2 ≤ R) {V : ℝ} (hV : 0 < V) :
    (#(atypicalDirichletPoints N R V) : ℝ) ≤ ((N : ℝ) + R ^ 2) * ((N : ℝ) + 1) / V := by
  classical
  rw [le_div_iff₀ hV]
  have hw : ∀ r : ℕ, (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / (r + 1).totient := by
    intro r
    have hpos : (0 : ℝ) < (r + 1).totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    rw [le_div_iff₀ hpos, one_mul]
    exact_mod_cast Nat.totient_le (r + 1)
  -- Each atypical point carries weight at least one and square norm above `V`.
  calc (#(atypicalDirichletPoints N R V) : ℝ) * V
      = ∑ r ∈ range R, ∑ _ψ ∈ ((univ : Finset (DirichletCharacter ℂ (r + 1))).filter
          (fun ψ => ψ.IsPrimitive)).filter
          (fun ψ => V < ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2), V := by
        rw [atypicalDirichletPoints, card_sigma, Nat.cast_sum, sum_mul]
        refine sum_congr rfl fun r _ => ?_
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
          ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
            ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2 := by
        refine sum_le_sum fun r _ => ?_
        calc ∑ _ψ ∈ ((univ : Finset (DirichletCharacter ℂ (r + 1))).filter
              (fun ψ => ψ.IsPrimitive)).filter
              (fun ψ => V < ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2), V
            ≤ ∑ ψ ∈ ((univ : Finset (DirichletCharacter ℂ (r + 1))).filter
              (fun ψ => ψ.IsPrimitive)).filter
              (fun ψ => V < ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2),
                ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2 :=
              sum_le_sum fun ψ hψ => (mem_filter.mp hψ).2.le
          _ ≤ ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
                ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2 :=
              sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
          _ ≤ ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
                ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter
                  (fun ψ => ψ.IsPrimitive),
                ‖coprimeMoebiusSet (r + 1).primeFactors (dirichletGauge ψ) N‖ ^ 2 :=
              le_mul_of_one_le_left (sum_nonneg fun _ _ => by positivity) (hw r)
    _ ≤ ((N : ℝ) + R ^ 2) * ((N : ℝ) + 1) := largeSieve_coprimeMoebius_dirichletGauge N R hR

/-- **At conductor `√N`, all but `2 (N + 1)^{1 − 2ε}` special points are square-root typical.** -/
theorem card_atypical_dirichletGauge_le_rpow (N R : ℕ) (hR : 2 ≤ R)
    (hRN : (R : ℝ) ^ 2 ≤ (N : ℝ) + 1) (ε : ℝ) :
    (#(atypicalDirichletPoints N R (((N : ℝ) + 1) ^ (1 + 2 * ε))) : ℝ) ≤
      2 * ((N : ℝ) + 1) ^ (1 - 2 * ε) := by
  have hX : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine (card_atypical_dirichletGauge_le N R hR (Real.rpow_pos_of_pos hX _)).trans ?_
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hX _), mul_assoc, ← Real.rpow_add hX,
    show 1 - 2 * ε + (1 + 2 * ε) = (2 : ℝ) by ring, Real.rpow_two]
  nlinarith

end GaloisForLFunctions.ArithmeticGaugeTheory
