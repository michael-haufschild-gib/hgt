import GaloisForLFunctions.HTGeometry.ClogVertLog
import GaloisForLFunctions.HTGeometry.GammaShiftTubeSum

/-!
# The boundary datum of a logarithmic polynomial

A polynomial in the principal logarithm with polynomial coefficients, divided by a polynomial, is
a finite sum whose members all have data: the `k`-th has argument exponent the degree difference of
its coefficient, and logarithm exponent `k`.  Since the logarithm exponents are distinct, no two
members share a signature, so the dominant member is unique and the sum has its datum.

Choosing the member by the lexicographic maximum of (coefficient degree, logarithm exponent) is
exactly the ordering the boundary shape uses.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A polynomial in the principal logarithm with polynomial coefficients, evaluated. -/
def logPolyEval (A : Polynomial (Polynomial ℂ)) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (Polynomial.evalRingHom z) (Complex.log z) A

theorem logPolyEval_eq_sum (A : Polynomial (Polynomial ℂ)) (z : ℂ) :
    logPolyEval A z = ∑ k ∈ A.support, (A.coeff k).eval z * (Complex.log z) ^ k := by
  rw [logPolyEval, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rfl

/-- **A finite sum with one strictly dominant member has that member's datum.** -/
theorem hasShiftTubeDatum_finsetSum_dominant {M : ℝ} (hM : 0 < M) {ι : Type*} [DecidableEq ι]
    {S : Finset ι} (F : ι → ℝ → ℝ → ℂ) (ω : ι → ℝ) (b : ι → ℤ) (c : ι → ℂ) {β : ι} (hβ : β ∈ S)
    (hdat : ∀ α ∈ S, HasShiftTubeDatum M 0 (F α) 0 (ω α) (b α) (c α))
    (hdom : ∀ α ∈ S, α ≠ β → ShiftShapeDominates 0 (ω β) (b β) 0 (ω α) (b α)) :
    HasShiftTubeDatum M 0 (fun σ t => ∑ α ∈ S, F α σ t) 0 (ω β) (b β) (c β) := by
  classical
  refine ⟨(hdat β hβ).1, ?_⟩
  have hterm : ∀ α ∈ S, TubeLimit M
      (fun σ t => F α σ t / gammaShiftShape 0 σ 0 (ω β) (b β) t)
      (if α = β then c β else 0) := by
    intro α hα
    by_cases hαβ : α = β
    · subst hαβ
      rw [if_pos rfl]
      exact (hdat α hα).2
    · rw [if_neg hαβ]
      have hmul := (hdat α hα).2.mul
        (tubeLimit_gammaShiftShape_ratio_zero hM le_rfl (hdom α hα hαβ))
      rw [mul_zero] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hSα : gammaShiftShape 0 σ 0 (ω α) (b α) t ≠ 0 :=
        gammaShiftShape_ne_zero (by linarith) ht _ _ _
      have hSβ : gammaShiftShape 0 σ 0 (ω β) (b β) t ≠ 0 :=
        gammaShiftShape_ne_zero (by linarith) ht _ _ _
      field_simp
  have hsum := TubeLimit.finsetSum S hterm
  rw [Finset.sum_ite_eq' S β (fun _ => c β), if_pos hβ] at hsum
  refine hsum.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  rw [Finset.sum_div]

/-- **The boundary datum of a logarithmic polynomial over a polynomial.**  The dominant member is
the lexicographic maximum of coefficient degree and logarithm exponent. -/
theorem exists_hasShiftTubeDatum_logPolyEval {M : ℝ} (hM : 0 < M)
    {A : Polynomial (Polynomial ℂ)} (hA : A ≠ 0) {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∃ k : ℕ, A.coeff k ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => logPolyEval A ((σ : ℂ) + (t : ℂ) * Complex.I)
          / Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) q)
        0 (((A.coeff k).natDegree : ℝ) - (q.natDegree : ℝ)) (k : ℤ)
        ((A.coeff k).leadingCoeff / q.leadingCoeff) := by
  classical
  have hS : A.support.Nonempty := Polynomial.support_nonempty.mpr hA
  obtain ⟨β, hβ, hmax⟩ := A.support.exists_max_image
    (fun α : ℕ => (toLex ((A.coeff α).natDegree, α) : ℕ ×ₗ ℕ)) hS
  refine ⟨β, Polynomial.mem_support_iff.mp hβ, ?_⟩
  have hdat := hasShiftTubeDatum_finsetSum_dominant (M := M) hM (S := A.support)
    (F := fun α σ t => Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) (A.coeff α)
      / Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) q
      * (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ α)
    (ω := fun α => ((A.coeff α).natDegree : ℝ) - (q.natDegree : ℝ)) (b := fun α => (α : ℤ))
    (c := fun α => (A.coeff α).leadingCoeff / q.leadingCoeff) hβ
    (fun α hα => hasShiftTubeDatum_ratEval_clogPow hM (Polynomial.mem_support_iff.mp hα) hq α)
    (fun α hα hαβ => ?_)
  · refine ⟨hdat.1, ?_⟩
    refine hdat.2.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
    simp only [logPolyEval_eq_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun α _ => ?_
    ring
  · have hle := hmax α hα
    rw [Prod.Lex.le_iff] at hle
    rcases hle with hlt | ⟨heq, hle2⟩
    · refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      have : (A.coeff α).natDegree < (A.coeff β).natDegree := hlt
      have hcast : ((A.coeff α).natDegree : ℝ) < ((A.coeff β).natDegree : ℝ) := by
        exact_mod_cast this
      linarith
    · have hdeq : (A.coeff α).natDegree = (A.coeff β).natDegree := heq
      have hlt2 : α < β := lt_of_le_of_ne hle2 hαβ
      refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
      · rw [hdeq]
      · exact_mod_cast hlt2

end

end GaloisForLFunctions.HTGeometry
