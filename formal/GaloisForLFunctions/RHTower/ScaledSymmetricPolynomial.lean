import Mathlib

/-!
# Rescaling a symmetric polynomial to clear a leading coefficient

The algebraic device that lifts the symmetric-function integrality of a *monic* conjugate set to a
*non-monic* one.  If `β₁,…,β_d` are the roots of an integer polynomial with leading coefficient `ℓ`,
they are not algebraic integers, but `ℓ·β₁,…,ℓ·β_d` are.  To transfer a symmetric integer polynomial
`φ` evaluated at the `β_j` to one evaluated at the algebraic integers `ℓ·β_j`, one multiplies by a
power of `ℓ`.

`exists_scaled_symmetric`: for every symmetric `φ ∈ ℤ[X₁,…,X_d]` there is a symmetric
`ψ ∈ ℤ[X₁,…,X_d]` with
`ψ(ℓ·β₁,…,ℓ·β_d) = ℓ^{deg φ} · φ(β₁,…,β_d)` for all `β`.
Concretely `ψ = ∑_s (φ.coeff s · ℓ^{deg φ − |s|}) · X^s`: each monomial of `φ` of degree `|s| ≤ deg φ`
is weighted by `ℓ^{deg φ − |s|}`, which is a nonnegative power (so `ψ` has integer coefficients).
Evaluating at `ℓ·β` contributes an extra `ℓ^{|s|}` per monomial, and `ℓ^{deg φ − |s|}·ℓ^{|s|} = ℓ^{deg φ}`
is uniform.  Symmetry is preserved because the weight depends only on the monomial degree, which the
permutation action fixes.

Together with the monic symmetric-function integrality (`symmetric_aeval_conj_isInt`) applied to the
algebraic integers `ℓ·β_j`, this yields `ℓ^{deg φ}·φ(β) ∈ ℤ` for a full non-monic conjugate set — the
leading-coefficient bookkeeping required to run the Lindemann–Weierstrass estimate over exponents that
are algebraic but not algebraic integers.
-/

open MvPolynomial Finset

namespace GaloisForLFunctions
namespace RHTower

/-- **Rescaling a symmetric polynomial to absorb a leading coefficient.**  For a symmetric integer
polynomial `φ` in `d` variables there is a symmetric integer polynomial `ψ` such that
`ψ(ℓ·β) = ℓ^{deg φ}·φ(β)` for every point `β : Fin d → ℂ`.  Built by weighting each monomial `X^s`
of `φ` by `ℓ^{deg φ − |s|}`; the extra `ℓ^{|s|}` produced by evaluating at `ℓ·β` restores a uniform
`ℓ^{deg φ}`, and the degree-only weight keeps `ψ` symmetric. -/
theorem exists_scaled_symmetric {d : ℕ} (ℓ : ℤ) (φ : MvPolynomial (Fin d) ℤ)
    (hφ : φ.IsSymmetric) :
    ∃ ψ : MvPolynomial (Fin d) ℤ, ψ.IsSymmetric ∧
      ∀ β : Fin d → ℂ, MvPolynomial.aeval (fun j => (ℓ : ℂ) * β j) ψ
        = (ℓ : ℂ) ^ φ.totalDegree * MvPolynomial.aeval β φ := by
  classical
  set D := φ.totalDegree with hD
  set c : (Fin d →₀ ℕ) → ℤ := fun s => φ.coeff s * ℓ ^ (D - s.sum (fun _ e => e)) with hc
  set ψ : MvPolynomial (Fin d) ℤ := ∑ s ∈ φ.support, monomial s (c s) with hψ
  have hcoeff : ∀ t : Fin d →₀ ℕ, ψ.coeff t = c t := by
    intro t
    rw [hψ, MvPolynomial.coeff_sum]
    rw [Finset.sum_congr rfl (fun s _ => MvPolynomial.coeff_monomial t s (c s))]
    rw [Finset.sum_ite_eq' φ.support t (fun s => c s)]
    by_cases ht : t ∈ φ.support
    · rw [if_pos ht]
    · rw [if_neg ht]
      have hz : φ.coeff t = 0 := by rwa [MvPolynomial.mem_support_iff, not_not] at ht
      simp only [hc, hz, zero_mul]
  refine ⟨ψ, ?_, ?_⟩
  · intro σ
    apply MvPolynomial.ext
    intro u
    have hukey : ∀ t : Fin d →₀ ℕ, (rename σ ψ).coeff (Finsupp.mapDomain σ t) = ψ.coeff t :=
      fun t => MvPolynomial.coeff_rename_mapDomain σ σ.injective ψ t
    have hu : u = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm u) := by
      rw [Finsupp.mapDomain_comp.symm]
      simp [Finsupp.mapDomain_id]
    rw [hu, hukey]
    set t := Finsupp.mapDomain σ.symm u with ht
    rw [hcoeff, hcoeff]
    simp only [hc]
    have hdeg : (Finsupp.mapDomain σ t).sum (fun _ e => e) = t.sum (fun _ e => e) := by
      rw [Finsupp.sum_mapDomain_index] <;> simp
    have hcf : φ.coeff (Finsupp.mapDomain σ t) = φ.coeff t := by
      have := MvPolynomial.coeff_rename_mapDomain σ σ.injective φ t
      rw [hφ σ] at this
      exact this
    rw [hdeg, hcf]
  · intro β
    rw [hψ, map_sum]
    conv_rhs => rw [show φ = ∑ s ∈ φ.support, monomial s (φ.coeff s) from MvPolynomial.as_sum φ]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
    simp only [hc]
    have hprod : (s.prod fun i k => ((ℓ : ℂ) * β i) ^ k)
        = (ℓ : ℂ) ^ (s.sum fun _ e => e) * s.prod (fun i k => (β i) ^ k) := by
      rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by rw [mul_pow])
    rw [hprod]
    have hle : s.sum (fun _ e => e) ≤ D := by rw [hD]; exact MvPolynomial.le_totalDegree hs
    have hpow : (ℓ : ℂ) ^ (D - s.sum fun _ e => e) * (ℓ : ℂ) ^ (s.sum fun _ e => e) = (ℓ : ℂ) ^ D := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_mul, Int.cast_pow]
    rw [← hpow]; ring

end RHTower
end GaloisForLFunctions
