import GaloisForLFunctions.RHTower.RoutePJuliaKreinHistoryPort
import GaloisForLFunctions.RHTower.PrimeGammaCauchyCubicSignedEulerianCurvature
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePActiveQuantileCellPort

/-!
# Zero-clock density of the literal Route-P Julia--Krein history port

At zero ordinate clock, every primitive P-G186 incidence entry is a strictly
positive real Cauchy-cubic edge, even after the literal prime-log conjugation.
Consequently every two-step child/pivot history coordinate is nonzero, whereas
the reverse chronology remains zero.  The existing history port is therefore
an all-path, ordered incidence carrier, not an edgewise two-atom carrier.

This supplies a finite source-support port for every pair of active SP-E
prime-power atoms.  It does not identify the source plaquette coefficient with
the target square-history coefficient, control the full strict-cross debt, or
assemble a cofinal graph-closed transport.
-/

open Complex Matrix
open scoped BigOperators Kronecker

namespace RHTower

noncomputable section

private theorem primeGammaCauchyCubicEdge_pos {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    0 < GaloisForLFunctions.HTGeometry.primeGammaCauchyCubicEdge x y := by
  unfold GaloisForLFunctions.HTGeometry.primeGammaCauchyCubicEdge
  exact div_pos (by norm_num) (pow_pos (add_pos hx hy) _)

private theorem primitive_window_entry_zero_is_pos_real
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (i j : Fin N) :
    ∃ x : ℝ, 0 < x ∧
      routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0) i j = (x : ℂ) := by
  let ai : ℝ := Real.sqrt (ArithmeticFunction.vonMangoldt
    (xiGammaEulerValuationNat (pe i)) / xiGammaEulerValuationNat (pe i))
  let aj : ℝ := Real.sqrt (ArithmeticFunction.vonMangoldt
    (xiGammaEulerValuationNat (pe j)) / xiGammaEulerValuationNat (pe j))
  let e : ℝ := GaloisForLFunctions.HTGeometry.primeGammaCauchyCubicEdge
    (xiGammaEulerPrimitiveLogFrequency (pe i))
    (xiGammaEulerPrimitiveLogFrequency (pe j))
  refine ⟨ai * e * aj, mul_pos (mul_pos ?_ ?_) ?_, ?_⟩
  · rw [show ai = Real.sqrt (ArithmeticFunction.vonMangoldt
        (xiGammaEulerValuationNat (pe i)) / xiGammaEulerValuationNat (pe i)) by rfl]
    exact Real.sqrt_pos.2 (by
      apply div_pos
      · rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log (pe i)]
        exact Real.log_pos (by exact_mod_cast (pe i).1.property.one_lt)
      · exact_mod_cast pow_pos (pe i).1.property.pos ((pe i).2 + 1))
  · exact primeGammaCauchyCubicEdge_pos
      (xiGammaEulerPrimitiveLogFrequency_pos (pe i))
      (xiGammaEulerPrimitiveLogFrequency_pos (pe j))
  · rw [show aj = Real.sqrt (ArithmeticFunction.vonMangoldt
        (xiGammaEulerValuationNat (pe j)) / xiGammaEulerValuationNat (pe j)) by rfl]
    exact Real.sqrt_pos.2 (by
      apply div_pos
      · rw [xiGammaEulerValuationNat, vonMangoldt_prime_pow_succ_eq_log (pe j)]
        exact Real.log_pos (by exact_mod_cast (pe j).1.property.one_lt)
      · exact_mod_cast pow_pos (pe j).1.property.pos ((pe j).2 + 1))
  · rw [routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy,
      routePPrimitiveBaseCauchyCubicKernelMatrix_apply,
      show (0 : ℝ) - 0 = 0 by ring,
      GaloisForLFunctions.HTGeometry.routePBaseCauchyCubicKernel_one_zero_eq_primeGammaCauchyCubicEdge]
    simp only [finiteVonMangoldtDepthOneAmplitude]
    push_cast
    rw [Complex.star_def, Complex.conj_ofReal]

private theorem matrix_sq_entry_ne_zero_of_pos_real
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : ∀ i j, ∃ x : ℝ, 0 < x ∧ H i j = (x : ℂ))
    (i j : Fin N) :
    (H * H) i j ≠ 0 := by
  choose h hpos hval using hH
  rw [Matrix.mul_apply]
  have hrewrite : (fun k : Fin N => H i k * H k j) =
      fun k => ((h i k * h k j : ℝ) : ℂ) := by
    funext k
    rw [hval i k, hval k j]
    push_cast
    rfl
  rw [hrewrite, ← Complex.ofReal_sum]
  exact Complex.ofReal_ne_zero.mpr
    (Finset.sum_pos (fun k _ => mul_pos (hpos i k) (hpos k j))
      ⟨i, Finset.mem_univ _⟩).ne'

private theorem primitive_primeLog_window_entry_zero_is_pos_real
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (i j : Fin N) :
    ∃ x : ℝ, 0 < x ∧
      routePPrimitiveJointDepthPrimeLogConjugate pe
        (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0)) i j = (x : ℂ) := by
  obtain ⟨x, hx, hentry⟩ := primitive_window_entry_zero_is_pos_real pe i j
  refine ⟨Real.log (pe i).1 * x * Real.log (pe j).1,
    mul_pos (mul_pos (Real.log_pos (by exact_mod_cast (pe i).1.property.one_lt)) hx)
      (Real.log_pos (by exact_mod_cast (pe j).1.property.one_lt)), ?_⟩
  rw [routePPrimitiveJointDepthPrimeLogConjugate_apply, hentry]
  push_cast
  rfl

private theorem primitive_primeLog_window_square_zero_entry_ne_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (i j : Fin N) :
    (routePPrimitiveJointDepthPrimeLogConjugate pe
        (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0)) *
      routePPrimitiveJointDepthPrimeLogConjugate pe
        (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0))) i j ≠ 0 := by
  apply matrix_sq_entry_ne_zero_of_pos_real
  exact primitive_primeLog_window_entry_zero_is_pos_real pe

/-- Every literal zero-clock P-G186 child/pivot history coordinate is nonzero in the forward
chronology.  Thus the forward history acts through all two-step primitive paths, not just one
chosen source pair. -/
theorem routePPrimitiveBurnolGammaJulia_zero_history_forward_ne_zero
    {N : ℕ} (pe : Fin N → Nat.Primes × ℕ) (i j : Fin N) :
    (routePJuliaKreinIncidenceChildHistoryStep
        (routePPrimitiveJointDepthPrimeLogConjugate pe
          (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0))) *
      routePJuliaKreinIncidenceNegativePivotHistoryStep
        (routePPrimitiveJointDepthPrimeLogConjugate pe
          (routePPrimitiveBurnolWindowGramMatrix pe (fun _ => 0)))) (0, i) (0, j) ≠ 0 := by
  rw [(routePPrimitiveBurnolGammaJulia_history_ordered_coordinate_asymmetry
    pe (fun _ => 0) i j).1]
  exact mul_ne_zero (by norm_num) (primitive_primeLog_window_square_zero_entry_ne_zero pe i j)

/-- Every active SP-E prime-power pair has a literal P-G186 two-label packet with a nonzero
forward child/pivot history coordinate and vanishing reversed coordinate.  This is a support
port only: matching its coefficient to the SP-E plaquette remains the open graph problem. -/
theorem isPrimePow_pair_exists_routePPrimitiveBurnol_zero_history_support_port
    (m n : ℕ) (hm : IsPrimePow m) (hn : IsPrimePow n) :
    ∃ pe tau : Nat.Primes × ℕ,
      xiGammaEulerValuationNat pe = m ∧
      xiGammaEulerValuationNat tau = n ∧
      (routePJuliaKreinIncidenceChildHistoryStep
          (routePPrimitiveJointDepthPrimeLogConjugate ![pe, tau]
            (routePPrimitiveBurnolWindowGramMatrix ![pe, tau] (fun _ => 0))) *
        routePJuliaKreinIncidenceNegativePivotHistoryStep
          (routePPrimitiveJointDepthPrimeLogConjugate ![pe, tau]
            (routePPrimitiveBurnolWindowGramMatrix ![pe, tau] (fun _ => 0)))) (0, 0) (0, 1) ≠ 0 ∧
      (routePJuliaKreinIncidenceNegativePivotHistoryStep
          (routePPrimitiveJointDepthPrimeLogConjugate ![pe, tau]
            (routePPrimitiveBurnolWindowGramMatrix ![pe, tau] (fun _ => 0))) *
        routePJuliaKreinIncidenceChildHistoryStep
          (routePPrimitiveJointDepthPrimeLogConjugate ![pe, tau]
            (routePPrimitiveBurnolWindowGramMatrix ![pe, tau] (fun _ => 0)))) (0, 0) (0, 1) = 0 := by
  obtain ⟨pe, hpe, _, _⟩ := isPrimePow_exists_routePPrimitiveBurnolZeroClockRay m hm
  obtain ⟨tau, htau, _, _⟩ := isPrimePow_exists_routePPrimitiveBurnolZeroClockRay n hn
  refine ⟨pe, tau, hpe, htau,
    routePPrimitiveBurnolGammaJulia_zero_history_forward_ne_zero ![pe, tau] 0 1,
    (routePPrimitiveBurnolGammaJulia_history_ordered_coordinate_asymmetry
      ![pe, tau] (fun _ => 0) 0 1).2⟩

end

end RHTower
