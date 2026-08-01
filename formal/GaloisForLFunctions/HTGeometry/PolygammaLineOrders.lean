import GaloisForLFunctions.HTGeometry.LineAsymptoticScale
import GaloisForLFunctions.HTGeometry.PolygammaLeadingAsymptotic

/-!
# Decay orders of the digamma jets

Reading the leading asymptotics through the asymptotic scale: every positive-order polygamma jet is
`O(s^{-(m+1)})` on a vertical line, its leading coefficient is the residue extracted by the scale,
and any monomial in the jets decays at the sum of the orders of its factors.

These are the first entries of the expansion table the general form of the residue law needs.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- Every positive-order polygamma jet decays like `s^{-(m+1)}` on a vertical line. -/
theorem isLineBigO_iteratedDeriv_succ_digamma (hσ : 0 < σ) (m : ℕ) :
    IsLineBigO σ (m + 1)
      (fun t : ℝ => iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
  isLineBigO_of_tendsto (tendsto_pow_mul_iteratedDeriv_digamma_vertical hσ m)

/-- The residue of a polygamma jet against its own monomial: the extraction lemma applied to the
leading asymptotic. -/
theorem isLineBigO_iteratedDeriv_succ_digamma_sub (hσ : 0 < σ) (m : ℕ) {c : ℂ}
    (h : IsLineBigO σ (m + 2)
      (fun t : ℝ => iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        - c * ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ ^ (m + 1))) :
    c = (-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ) :=
  tendsto_nhds_unique (tendsto_pow_mul_of_isLineBigO h)
    (tendsto_pow_mul_iteratedDeriv_digamma_vertical hσ m)

/-- A product of positive-order jets decays at the sum of the orders. -/
theorem isLineBigO_jet_mul (hσ : 0 < σ) (m n : ℕ) :
    IsLineBigO σ ((m + 1) + (n + 1))
      (fun t : ℝ => iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        * iteratedDeriv (n + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
  (isLineBigO_iteratedDeriv_succ_digamma hσ m).mul (isLineBigO_iteratedDeriv_succ_digamma hσ n)

/-- A power of a positive-order jet decays at the multiplied order. -/
theorem isLineBigO_jet_pow (hσ : 0 < σ) (m e : ℕ) :
    IsLineBigO σ ((m + 1) * e)
      (fun t : ℝ => iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e) :=
  (isLineBigO_iteratedDeriv_succ_digamma hσ m).pow e

/-- A finite monomial in the positive-order jets decays at the total weight. -/
theorem isLineBigO_jet_monomial (hσ : 0 < σ) {N : ℕ} (e : Fin N → ℕ) :
    IsLineBigO σ (∑ i : Fin N, ((i : ℕ) + 1) * e i)
      (fun t : ℝ => ∏ i : Fin N,
        iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e i) := by
  classical
  induction N with
  | zero => simpa using isLineBigO_const σ 1
  | succ N ih =>
    have hlast := isLineBigO_jet_pow hσ N (e (Fin.last N))
    have hrest := ih (fun i : Fin N => e (Fin.castSucc i))
    have hmul := hrest.mul hlast
    have hfun : (fun t : ℝ =>
        (∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e (Fin.castSucc i))
          * iteratedDeriv (N + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
            ^ e (Fin.last N))
        = fun t : ℝ => ∏ i : Fin (N + 1),
          iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e i := by
      funext t
      rw [Fin.prod_univ_castSucc]
      rfl
    rw [hfun] at hmul
    have hidx : (∑ i : Fin N, ((i : ℕ) + 1) * e (Fin.castSucc i)) + (N + 1) * e (Fin.last N)
        = ∑ i : Fin (N + 1), ((i : ℕ) + 1) * e i := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rwa [hidx] at hmul

end GaloisForLFunctions
