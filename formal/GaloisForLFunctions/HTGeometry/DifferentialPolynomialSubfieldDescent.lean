import GaloisForLFunctions.HTGeometry.DifferentialPolynomialNonRoot

/-!
# A differential polynomial vanishing at every point of a rich differential subfield is zero

Evaluation of a differential polynomial at a point of a differential **subfield** `C` is `C`-linear
in the coefficients, because every jet of a point of `C` again lies in `C`.  Applying a `C`-linear
functional `φ : L → C` therefore turns a differential polynomial over `L` into one over `C` with the
same values up to `φ`.  If every nonzero differential polynomial over `C` has a non-root in `C` —
which holds when `C` is differentially closed — each of those descends to zero, and the functionals
separate the points of `L`.

* `linearPush` — the coefficientwise image of a differential polynomial under a linear functional;
* `evalOver_linearPush`;
* `eq_zero_of_evalOver_subfield_eq_zero` — **the descent.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C L : Type*} [Field C] [Field L] [Algebra C L] [Differential C] [Differential L]

/-- Jets of a point of the differential subfield stay in the subfield. -/
private theorem differentialJet_algebraMap
    (hcompat : ∀ a : C, (algebraMap C L a)′ = algebraMap C L (a′)) (c : C) :
    ∀ n : ℕ, differentialJet n (algebraMap C L c) = algebraMap C L (differentialJet n c)
  | 0 => by rw [differentialJet_zero, differentialJet_zero]
  | (n + 1) => by
      rw [differentialJet_succ, differentialJet_algebraMap hcompat c n, hcompat,
        differentialJet_succ]

variable (φ : L →ₗ[C] C)

/-- The coefficientwise image of a differential polynomial under a `C`-linear functional. -/
def linearPush {ι : Type*} (G : DifferentialPolynomial ι L) : DifferentialPolynomial ι C :=
  ∑ d ∈ G.support, MvPolynomial.monomial d (φ (MvPolynomial.coeff d G))

omit [Differential C] [Differential L] in
theorem coeff_linearPush {ι : Type*} (G : DifferentialPolynomial ι L) (e : (ι × ℕ) →₀ ℕ) :
    MvPolynomial.coeff e (linearPush φ G) = φ (MvPolynomial.coeff e G) := by
  classical
  rw [linearPush, MvPolynomial.coeff_sum]
  by_cases he : e ∈ G.support
  · rw [Finset.sum_eq_single e]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro d _ hde
      rw [MvPolynomial.coeff_monomial, if_neg hde]
    · intro hcon; exact absurd he hcon
  · have hz : MvPolynomial.coeff e G = 0 := by
      by_contra hne
      exact he (MvPolynomial.mem_support_iff.mpr hne)
    rw [hz, map_zero]
    refine Finset.sum_eq_zero fun d hd => ?_
    have hde : d ≠ e := fun hcon => he (hcon ▸ hd)
    rw [MvPolynomial.coeff_monomial, if_neg hde]

omit [Differential C] [Differential L] in
theorem support_linearPush_subset {ι : Type*} (G : DifferentialPolynomial ι L) :
    (linearPush φ G).support ⊆ G.support := by
  intro e he
  by_contra hcon
  have hz : MvPolynomial.coeff e G = 0 := by
    by_contra hne
    exact hcon (MvPolynomial.mem_support_iff.mpr hne)
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [coeff_linearPush, hz, map_zero])

/-- **Evaluating the pushed polynomial is the functional applied to the evaluation.** -/
theorem evalOver_linearPush {ι : Type*}
    (hcompat : ∀ a : C, (algebraMap C L a)′ = algebraMap C L (a′))
    (x : ι → C) (G : DifferentialPolynomial ι L) :
    differentialPolynomialEvalOver (K := C) x (linearPush φ G)
      = φ (differentialPolynomialEvalOver (K := L) (fun i => algebraMap C L (x i)) G) := by
  classical
  rw [differentialPolynomialEvalOver, differentialPolynomialEvalOver, MvPolynomial.aeval_def,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, map_sum]
  have hterm : ∀ d ∈ G.support,
      φ ((algebraMap L L) (MvPolynomial.coeff d G)
          * ∏ i ∈ d.support, differentialJet i.2 (algebraMap C L (x i.1)) ^ d i)
        = (algebraMap C C) (MvPolynomial.coeff d (linearPush φ G))
          * ∏ i ∈ d.support, differentialJet i.2 (x i.1) ^ d i := by
    intro d _
    have hprod : ∏ i ∈ d.support, differentialJet i.2 (algebraMap C L (x i.1)) ^ d i
        = algebraMap C L (∏ i ∈ d.support, differentialJet i.2 (x i.1) ^ d i) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [differentialJet_algebraMap hcompat, map_pow]
    rw [hprod, Algebra.algebraMap_self_apply, coeff_linearPush,
      Algebra.algebraMap_self_apply]
    have hsm : MvPolynomial.coeff d G
        * algebraMap C L (∏ i ∈ d.support, differentialJet i.2 (x i.1) ^ d i)
        = (∏ i ∈ d.support, differentialJet i.2 (x i.1) ^ d i) • MvPolynomial.coeff d G := by
      rw [Algebra.smul_def]; ring
    rw [hsm, map_smul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_subset (support_linearPush_subset φ G) fun d _ hd => ?_
  have hz : MvPolynomial.coeff d (linearPush φ G) = 0 := by
    by_contra hne
    exact hd (MvPolynomial.mem_support_iff.mpr hne)
  rw [hz, map_zero, zero_mul]

/-- **A differential polynomial over `L` vanishing at every point of a rich differential subfield
`C` is zero.** -/
theorem eq_zero_of_evalOver_subfield_eq_zero
    (hcompat : ∀ a : C, (algebraMap C L a)′ = algebraMap C L (a′))
    (hrich : ∀ G' : DifferentialPolynomial Unit C, G' ≠ 0 →
      ∃ c : C, differentialPolynomialEvalOver (K := C) (fun _ : Unit => c) G' ≠ 0)
    {G : DifferentialPolynomial Unit L}
    (hG : ∀ c : C, differentialPolynomialEvalOver (K := L)
      (fun _ : Unit => algebraMap C L c) G = 0) :
    G = 0 := by
  classical
  have hpush : ∀ ψ : L →ₗ[C] C, linearPush ψ G = 0 := by
    intro ψ
    by_contra hne
    obtain ⟨c, hc⟩ := hrich _ hne
    exact hc (by rw [evalOver_linearPush ψ hcompat (fun _ : Unit => c) G, hG c, map_zero])
  refine MvPolynomial.ext G 0 fun d => ?_
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero C hne
  exact hψ (by rw [← coeff_linearPush ψ G d, hpush ψ, MvPolynomial.coeff_zero])

end

end GaloisForLFunctions.HTGeometry
