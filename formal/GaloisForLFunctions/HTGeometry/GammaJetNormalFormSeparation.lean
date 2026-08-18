import GaloisForLFunctions.HTGeometry.GammaJetNormalFormDatum
import GaloisForLFunctions.HTGeometry.GammaProductStirlingSignature

/-!
# The boundary datum from a separation hypothesis rather than `NoIntegerRelation`

`exists_hasShiftTubeDatum_jetGammaNormalForm` assumes `NoIntegerRelation` on the shifts: *no*
nonzero integer combination of them is an integer.  That hypothesis is far stronger than what the
proof uses, and it is exactly what fails for the commensurable scales `λ_j = n_j / H` of
`finite-archimedean-gamma-product-boundary-law`, where every shift lies in one arithmetic
progression.

Inspecting the proof shows the hypothesis is used in exactly one place, to prove that the dominant
class is a singleton, and only for the differences of the *actual* exponent vectors of the sum.
Abstracting that use gives `ShiftExponentSeparating`, a strictly weaker hypothesis, and the general
theorem below.  `NoIntegerRelation` together with injectivity of the exponent map is the special
case (`shiftExponentSeparating_of_noIntegerRelation`).

The point of the weakening is that `ShiftExponentSeparating` *can* hold for commensurable scales:
the Stirling signature of `GammaProductStirlingSignature` supplies the extra separating datum
`∑_k e_k λ_k log λ_k`, which `NoIntegerRelation` never saw.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

variable {r : ℕ}

/-- **The separation actually used**: among the exponent vectors of the sum, equal total degree and
an integer difference of the shift weights forces the summands to coincide. -/
def ShiftExponentSeparating {rr Mm : ℕ} (lamf : Fin rr → ℝ) (ee : Fin Mm → Fin rr → ℕ) : Prop :=
  ∀ (α β : Fin Mm) (m : ℤ),
    (∑ k : Fin rr, (ee α k : ℤ)) = ∑ k : Fin rr, (ee β k : ℤ) →
    (∑ k : Fin rr, ((((ee α k : ℤ) - (ee β k : ℤ) : ℤ)) : ℝ) * lamf k) = (m : ℝ) →
    α = β

theorem shiftExponentSeparating_of_noIntegerRelation {rr Mm : ℕ} {lamf : Fin rr → ℝ}
    (hindep : NoIntegerRelation lamf) {ee : Fin Mm → Fin rr → ℕ}
    (hee : Function.Injective ee) : ShiftExponentSeparating lamf ee := by
  intro α β m _ hrel
  have hzero := hindep (fun k => (ee α k : ℤ) - (ee β k : ℤ)) m hrel
  refine hee ?_
  funext k
  have hk := hzero k
  omega

set_option maxHeartbeats 1000000 in
/-- **The boundary datum of a normal-form Gamma sum, from separation alone.**  Strictly generalizes
`exists_hasShiftTubeDatum_jetGammaNormalForm`: the `NoIntegerRelation` hypothesis is replaced by the
separation it is only ever used to provide. -/
theorem exists_hasShiftTubeDatum_jetGammaNormalForm_of_separating {M : ℝ} (hM : 0 < M)
    {rr Mm K : ℕ} (hMm : 0 < Mm) (lamf : Fin rr → ℝ) (hlamf : ∀ k, 0 ≤ lamf k)
    (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, ((lam i : ℝ) : ℂ) - ((lam i' : ℝ) : ℂ) ≠ (n : ℂ))
    (idx : Fin K → Fin r × ℕ) (hinj : Function.Injective idx)
    (ee : Fin Mm → Fin rr → ℕ) (hsep : ShiftExponentSeparating lamf ee)
    (P : Fin Mm → MvPolynomial (Fin K) (Polynomial ℂ)) (hP : ∀ i, P i ≠ 0) :
    ∃ (β : Fin Mm) (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => ∑ i : Fin Mm, jetFieldPolyFun lam idx (P i) ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ∏ k : Fin rr, gammaLine (σ + lamf k) t ^ ee i k)
        (∑ k : Fin rr, (ee β k : ℤ)) ((a : ℝ) + ∑ k : Fin rr, (ee β k : ℝ) * lamf k) b c := by
  classical
  choose a b c hc hdat using fun i =>
    exists_hasShiftTubeDatum_jetFieldPolyFun lam hlam hincong idx hinj (hP i) hM
  have hsingleton : ∀ β : Fin Mm,
      (Finset.univ.filter (fun α : Fin Mm =>
        ∑ k : Fin rr, (ee α k : ℤ) = ∑ k : Fin rr, (ee β k : ℤ)
          ∧ ((a α : ℤ) : ℝ) + ∑ k : Fin rr, (ee α k : ℝ) * lamf k
            = ((a β : ℤ) : ℝ) + ∑ k : Fin rr, (ee β k : ℝ) * lamf k ∧ b α = b β)) = {β} := by
    intro β
    refine Finset.ext fun α => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, -⟩
      have hexp : ∀ k : Fin rr, ((((ee α k : ℤ) - (ee β k : ℤ) : ℤ) : ℝ)) * lamf k
          = (ee α k : ℝ) * lamf k - (ee β k : ℝ) * lamf k := by
        intro k
        push_cast
        ring
      have hrel : (∑ k : Fin rr, ((((ee α k : ℤ) - (ee β k : ℤ) : ℤ) : ℝ)) * lamf k)
          = ((a β - a α : ℤ) : ℝ) := by
        rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_sub_distrib]
        push_cast
        linarith
      exact hsep α β (a β - a α) h1 hrel
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
  obtain ⟨β, hβ⟩ := exists_hasShiftTubeDatum_gammaCoeffSum hM hMm lamf hlamf
    (fun i σ t => jetFieldPolyFun lam idx (P i) ((σ : ℂ) + (t : ℂ) * Complex.I)) ee
    (fun i => ((a i : ℤ) : ℝ)) b c hdat
    (fun β _ => by rw [hsingleton β, Finset.sum_singleton]; exact hc β)
  refine ⟨β, a β, b β, c β, hc β, ?_⟩
  have hres : (∑ α ∈ Finset.univ.filter (fun α : Fin Mm =>
      ∑ k : Fin rr, (ee α k : ℤ) = ∑ k : Fin rr, (ee β k : ℤ)
        ∧ ((a α : ℤ) : ℝ) + ∑ k : Fin rr, (ee α k : ℝ) * lamf k
          = ((a β : ℤ) : ℝ) + ∑ k : Fin rr, (ee β k : ℝ) * lamf k ∧ b α = b β), c α) = c β := by
    rw [hsingleton β, Finset.sum_singleton]
  rw [hres] at hβ
  exact hβ

end

end GaloisForLFunctions.HTGeometry
