import GaloisForLFunctions.HTGeometry.GammaBlockFinset
import GaloisForLFunctions.HTGeometry.GammaJetSumDatum

/-!
# The boundary datum of one dominance fibre

Inside a fibre of the pair `(Γ-degree, first moment)` every monomial differs from the reference one
by a balanced exponent vector, so factoring out the reference monomial turns the fibre sum into a
balanced block times a Gamma monomial, and both factors have data.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

variable {r : ℕ}

theorem HasShiftTubeDatum.congr_tube {M lam : ℝ} {φ ψ : ℝ → ℝ → ℂ} {d : ℤ} {ω : ℝ} {b : ℤ} {c : ℂ}
    (h : HasShiftTubeDatum M lam φ d ω b c) {T₀ : ℝ}
    (heq : ∀ σ t : ℝ, 0 < σ → σ ≤ M → T₀ ≤ t → φ σ t = ψ σ t) :
    HasShiftTubeDatum M lam ψ d ω b c :=
  ⟨h.1, h.2.congr (T₀ := T₀) fun σ t hσ hσM ht => by rw [heq σ t hσ hσM ht]⟩

/-- **The boundary datum of a dominance fibre.** -/
theorem exists_hasShiftTubeDatum_gammaFiberSum {M : ℝ} (hM : 0 < M) {K Mm : ℕ}
    (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    (ee : Fin Mm → Fin r → ℕ) (hee : Function.Injective ee)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ))
    (S : Finset (Fin Mm)) (ρ : Fin Mm) (hρ : ρ ∈ S) (hPρ : P ρ ≠ 0)
    (hdegS : ∀ α ∈ S, ∑ k, (ee α k : ℤ) = ∑ k, (ee ρ k : ℤ))
    (hmomS : ∀ α ∈ S, ∑ k, (ee α k : ℝ) * lam k = ∑ k, (ee ρ k : ℝ) * lam k) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => ∑ α ∈ S, jetFieldPolyFun lam idx (P α) ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ∏ k : Fin r, gammaLine (σ + lam k) t ^ ee α k)
        (∑ k : Fin r, (ee ρ k : ℤ))
        ((a : ℝ) + ∑ k : Fin r, (ee ρ k : ℝ) * lam k) b c := by
  classical
  have he' : Function.Injective
      (fun α : {α : Fin Mm // α ∈ S} => fun k => (ee α.1 k : ℤ) - (ee ρ k : ℤ)) := by
    intro α β hab
    have hfun : ∀ k, (ee α.1 k : ℤ) - (ee ρ k : ℤ) = (ee β.1 k : ℤ) - (ee ρ k : ℤ) :=
      fun k => congrFun hab k
    refine Subtype.ext (hee (funext fun k => ?_))
    have := hfun k
    omega
  have hdeg' : ∀ α : {α : Fin Mm // α ∈ S},
      ∑ k, ((ee α.1 k : ℤ) - (ee ρ k : ℤ)) = 0 := by
    intro α
    rw [Finset.sum_sub_distrib, hdegS α.1 α.2, sub_self]
  have hmom' : ∀ α : {α : Fin Mm // α ∈ S},
      ∑ k, ((((ee α.1 k : ℤ) - (ee ρ k : ℤ)) : ℤ) : ℝ) * lam k = 0 := by
    intro α
    have hstep : ∀ k : Fin r, ((((ee α.1 k : ℤ) - (ee ρ k : ℤ)) : ℤ) : ℝ) * lam k
        = (ee α.1 k : ℝ) * lam k - (ee ρ k : ℝ) * lam k := by
      intro k
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_sub_distrib, hmomS α.1 α.2, sub_self]
  obtain ⟨a, b, c, hc, hdat⟩ := exists_hasShiftTubeDatum_balancedBlockFinset lam hlam hincong idx
    hinj (fun α : {α : Fin Mm // α ∈ S} => P α.1)
    (fun α : {α : Fin Mm // α ∈ S} => fun k => (ee α.1 k : ℤ) - (ee ρ k : ℤ)) he' hdeg' hmom'
    Finset.univ ⟨ρ, hρ⟩ (Finset.mem_univ _) hPρ hM
  refine ⟨a, b, c, hc, ?_⟩
  refine (hdat.mul_gammaProd hM lam hlam (ee ρ)).congr_tube (T₀ := 0) fun σ t hσ _ _ => ?_
  have hz : ∀ k : Fin r, Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I + ((lam k : ℝ) : ℂ)) ≠ 0 := by
    intro k
    refine Complex.Gamma_ne_zero fun m => ?_
    intro hcon
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I + ((lam k : ℝ) : ℂ)).re = σ + lam k := by simp
    rw [hcon] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h2 := hlam k
    linarith
  rw [Finset.sum_mul, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mul_assoc]
  congr 1
  rw [gammaProd_eq_gammaMonomial lam (ee ρ) σ t, gammaProd_eq_gammaMonomial lam (ee α.1) σ t,
    ← gammaMonomial_add (fun i => ((lam i : ℝ) : ℂ)) _ _ hz]
  congr 1
  funext k
  omega

end

end GaloisForLFunctions.HTGeometry
