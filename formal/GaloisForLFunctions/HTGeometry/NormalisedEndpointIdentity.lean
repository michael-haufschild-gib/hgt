import GaloisForLFunctions.HTGeometry.EndpointChirpData

/-!
# The normalised endpoint identity

Putting the endpoint expansion, the jet coefficient formula and the termwise chirp identity
together: for a factorial-slope sequence, `R ≥ 2`, `R ≤ M` and `a_M ≠ 0`,

`[X^{M+R}] P(jets) / a_M = ∑_{(j,q)} chirp(j,q)(log M)·ε_{(j,q)}(M) + [X^{M+R}] P(S) / a_M`,

where the sum runs over the finite type of endpoint pairs, `chirp(j,q)` carries the exponent
`j + (Re α)u` and the integer frequency `u = R − q + j`, and each `ε_{(j,q)} → 1`.

Everything here is exact algebra; the only asymptotic content sits in the `ε` factors and in the
remainder, which is bounded separately.
-/

open MvPolynomial PowerSeries Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- **The normalised endpoint identity.** -/
theorem coeff_aeval_div_eq_chirp_sum (hyp : FactorialSlope a α Λ Cc c) {m R M : ℕ}
    (hR : 2 ≤ R) (hRM : R ≤ M) (hM : 1 ≤ M) (haM : a M ≠ 0)
    (P : MvPolynomial (Fin (m + 2)) ℂ) :
    PowerSeries.coeff (M + R) (aeval (formalJetsOver m (PowerSeries.mk a)) P) / a M
      = (∑ jq : Fin (m + 1) × Fin R,
          chirpTerm α.im (endpointExponent α jq) (endpointFreq jq)
            (endpointCoeff α Λ (fun (j : Fin (m + 1)) (q : ℕ) =>
                PowerSeries.coeff q
                  (aeval (formalJetsOver m (PowerSeries.mk a)) (pderiv j.succ P))) jq)
            (Real.log M)
          * slopeShiftDefect a α Λ (endpointShift jq) ((jq.1 : ℕ)) M)
        + PowerSeries.coeff (M + R)
            (aeval (fun i => lowPart ((M + R) - R)
              (formalJetsOver m (PowerSeries.mk a) i)) P) / a M := by
  classical
  have hNR : 2 * R ≤ M + R := by omega
  set jets := formalJetsOver m (PowerSeries.mk a) with hjets
  set cc : Fin (m + 1) → ℕ → ℂ := fun j q =>
    PowerSeries.coeff q (aeval jets (pderiv j.succ P)) with hcc
  rw [coeff_aeval_endpoint_expansion jets P hNR, add_div]
  congr 1
  rw [endpoint_sum_eq_coeff_sum m R (M + R) hR hNR a P]
  set T : Fin (m + 1) → ℕ → ℂ := fun j q =>
    cc j q * (a ((M + R) - q + (j : ℕ))
      * (((((M + R) - q + (j : ℕ)).descFactorial (j : ℕ) : ℕ)) : ℂ)) with hT
  have hdiv : (∑ j : Fin (m + 1), ∑ q ∈ Finset.range R, T j q) / a M
      = ∑ j : Fin (m + 1), ∑ q ∈ Finset.range R, T j q / a M := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [hdiv, ← sum_endpoint_pairs (fun j q => T j q / a M)]
  refine Finset.sum_congr rfl fun jq _ => ?_
  rw [← endpoint_pair_term_eq_chirp hyp cc jq hM haM]
  rw [hT]
  ring

end

end GaloisForLFunctions.HTGeometry
