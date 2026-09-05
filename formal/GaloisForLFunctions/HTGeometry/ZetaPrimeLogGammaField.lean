import GaloisForLFunctions.HTGeometry.PrimeLogLatticeShifts
import GaloisForLFunctions.HTGeometry.GammaShiftZeta

/-!
# Zeta satisfies no relation over the prime-log shifted Gamma field

Combining the boundary datum of an arbitrary element of the shifted Gamma field with prime-log
lattice shifts and the projective-boundary theorem for zeta: no nontrivial differential relation
holds between the zeta jets with coefficients in that field.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The value of a quotient of normal-form sums. -/
def gammaFieldQuotientFun {r K Mn Md : ℕ} (lam : Fin r → ℝ) (idx : Fin K → Fin r × ℕ)
    (P : Fin Mn → MvPolynomial (Fin K) (Polynomial ℂ)) (ee : Fin Mn → Fin r → ℕ)
    (P' : Fin Md → MvPolynomial (Fin K) (Polynomial ℂ)) (ee' : Fin Md → Fin r → ℕ)
    (s : ℂ) : ℂ :=
  (∑ i : Fin Mn, jetFieldPolyFun lam idx (P i) s
      * gammaMonomial (fun k => ((lam k : ℝ) : ℂ)) (fun k => (ee i k : ℤ)) s)
    / ∑ i : Fin Md, jetFieldPolyFun lam idx (P' i) s
      * gammaMonomial (fun k => ((lam k : ℝ) : ℂ)) (fun k => (ee' i k : ℤ)) s

/-- **Zeta satisfies no relation with coefficients in the prime-log shifted Gamma field.** -/
theorem zeta_no_primeLogGammaShift_relation {n N : ℕ} {σ R rr ρ : ℝ} (hσ : 1 < σ)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) (hRσ : R ≤ σ - 1)
    {r K : ℕ} (mm : Fin r → (Nat.Primes →₀ ℤ)) (lam : Fin r → ℝ)
    (hlamval : ∀ k, lam k = GaloisForLFunctions.RHTower.primeLogHom (mm k))
    (hlamnn : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ m : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (m : ℂ))
    (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Mn Md : ℕ) (hMn : 0 < Mn) (hMd : 0 < Md)
    (ee : Fin N → Fin Mn → Fin r → ℕ) (hee : ∀ α, Function.Injective (ee α))
    (P : Fin N → Fin Mn → MvPolynomial (Fin K) (Polynomial ℂ)) (hP : ∀ α i, P α i ≠ 0)
    (ee' : Fin N → Fin Md → Fin r → ℕ) (hee' : ∀ α, Function.Injective (ee' α))
    (P' : Fin N → Fin Md → MvPolynomial (Fin K) (Polynomial ℂ)) (hP' : ∀ α i, P' α i ≠ 0)
    (hrel : ∀ s : ℂ, ∑ α : Fin N,
      gammaFieldQuotientFun lam idx (P α) (ee α) (P' α) (ee' α) s
        * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) riemannZeta s) ^ (e α i) = 0) :
    False := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hdatum : ∀ α : Fin N, ∃ (d : ℤ) (ω : ℝ) (b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum σ 0
        (fun σ' t => gammaFieldQuotientFun lam idx (P α) (ee α) (P' α) (ee' α)
          ((σ' : ℂ) + (t : ℂ) * Complex.I)) d ω b c := by
    intro α
    obtain ⟨d, ω, b, c, hc, hdat⟩ := exists_hasShiftTubeDatum_primeLogGammaQuotient hσ0 hMn hMd
      mm lam hlamval hlamnn hincong idx hinj (ee α) (hee α) (P α) (hP α)
      (ee' α) (hee' α) (P' α) (hP' α)
    refine ⟨d, ω, b, c, hc, ?_⟩
    have hfun : (fun (σ' t : ℝ) =>
        (∑ i : Fin Mn, jetFieldPolyFun lam idx (P α i) ((σ' : ℂ) + (t : ℂ) * Complex.I)
          * ∏ k : Fin r, gammaLine (σ' + lam k) t ^ ee α i k)
        / ∑ i : Fin Md, jetFieldPolyFun lam idx (P' α i) ((σ' : ℂ) + (t : ℂ) * Complex.I)
          * ∏ k : Fin r, gammaLine (σ' + lam k) t ^ ee' α i k)
        = fun (σ' t : ℝ) => gammaFieldQuotientFun lam idx (P α) (ee α) (P' α) (ee' α)
          ((σ' : ℂ) + (t : ℂ) * Complex.I) := by
      funext σ' t
      rw [gammaFieldQuotientFun]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by
          rw [gammaProd_eq_gammaMonomial lam (ee α i) σ' t]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [gammaProd_eq_gammaMonomial lam (ee' α i) σ' t]
    rwa [hfun] at hdat
  choose dd ww bb cc hcc hdd using hdatum
  refine zeta_no_gammaShift_relation (lam := 0) hσ (by linarith) hN hr hρ hrρ hR hRσ e he
    (fun α => gammaFieldQuotientFun lam idx (P α) (ee α) (P' α) (ee' α)) dd ww bb cc hcc ?_ hrel
  intro α
  exact ((hdd α).hasShiftDatum hσ0 le_rfl).2

end

end GaloisForLFunctions.HTGeometry
