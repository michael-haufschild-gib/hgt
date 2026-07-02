/-
# Generic separable fibre of a bivariate relation (the discriminant ≢ 0 producer)

The relative hRigid branch machinery (`RelativeBranchFamily`, `false_of_global_basin_branch_analytic`,
and the countable-avoidance crossing `RelativeFibreGeneric`) all *consume* one full-degree separable
specialization `(fibrePoly a s w).Separable` of the analytic fibre `∑_{i∈s} aᵢ(z)·Xⁱ` with
`aᵢ(z) = Qᵢ(z, φ_{c₂}(z))`.  This file *produces* that witness from the algebra of the relation.

The mathematical content (the A3 card):

> If the reassembled bivariate relation `P(z,Y,X) = ∑_{i∈s} Qᵢ(z,Y)·Xⁱ ∈ ℂ[z,Y][X]` is **separable
> over the fraction field `ℂ(z,Y)`** — the minimal/irreducible case, automatic in characteristic 0 —
> then its **discriminant `Res(P, ∂_X P) ∈ ℂ[z,Y]` is a nonzero bivariate polynomial**
> (`HolomorphicIFT.resultant_ne_zero_of_separable`).  Because `φ_{c₂}` is transcendental over `ℂ(z)`
> (`hG`), that nonzero polynomial cannot vanish identically along the curve `Y = φ_{c₂}(z)`
> (`exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental`), so there is a
> point `w` where the top coefficient, the derivative's top coefficient, and the resultant all survive
> the specialization `r ↦ r(w, φ_{c₂}(w))` — hence `∑_{i∈s} Qᵢ(w,φ_{c₂}(w))·Xⁱ` is separable.

`separable_specialize_ringHom` is the ring-hom generalization of `HolomorphicIFT.separable_specialize`
(any specialization homomorphism `R → S` into a field, not only `evalRingHom` at a point of `ℂ`);
`map_bivarPoly_eval₂` identifies the specialized reassembled polynomial with the native `fibrePoly`;
`exists_separable_fibre_witness_of_separable_over_field` is the producer.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.RelativeFibreGeneric
import GaloisForLFunctions.Bottcher.RelativeTranscendenceBridge
import GaloisForLFunctions.U0.HolomorphicIFT

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **Separable specialization along a ring homomorphism (generic form).** For any ring hom
`ψ : R →+* S` into a field `S`, if the leading coefficient of `P`, the leading coefficient of its
derivative, and the resultant `Res(P, ∂P)` all survive `ψ`, then the specialized polynomial `P.map ψ`
is separable.  This is `HolomorphicIFT.separable_specialize` with `evalRingHom z₀ : ℂ[z] →+* ℂ`
replaced by an arbitrary `ψ`; the proof is unchanged (degree preservation
`natDegree_map_of_leadingCoeff_ne_zero`, `resultant_map_map`, `resultant_eq_zero_iff`). -/
theorem separable_specialize_ringHom {R S : Type*} [CommRing R] [Field S]
    (ψ : R →+* S) {P : R[X]}
    (hlead : ψ P.leadingCoeff ≠ 0)
    (hlead' : ψ (derivative P).leadingCoeff ≠ 0)
    (hres : ψ (resultant P (derivative P)) ≠ 0) :
    (P.map ψ).Separable := by
  have hd1 : (P.map ψ).natDegree = P.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero ψ hlead
  have hd2 : ((derivative P).map ψ).natDegree = (derivative P).natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero ψ hlead'
  have hPmap_ne : P.map ψ ≠ 0 := by
    intro h
    have hc : (P.map ψ).coeff P.natDegree = ψ (P.leadingCoeff) := by rw [coeff_map]; rfl
    rw [h, coeff_zero] at hc
    exact hlead hc.symm
  have key : resultant (P.map ψ) ((derivative P).map ψ) = ψ (resultant P (derivative P)) := by
    have e := resultant_map_map (f := P) (g := derivative P)
      (m := P.natDegree) (n := (derivative P).natDegree) ψ
    rw [show resultant (P.map ψ) ((derivative P).map ψ)
          = resultant (P.map ψ) ((derivative P).map ψ)
              (P.map ψ).natDegree ((derivative P).map ψ).natDegree
        from rfl, hd1, hd2, e]
  rw [Separable, Polynomial.derivative_map]
  by_contra hnc
  have hzero : resultant (P.map ψ) ((derivative P).map ψ) = 0 := by
    rw [resultant_eq_zero_iff]; exact ⟨Or.inl hPmap_ne, hnc⟩
  rw [key] at hzero
  exact hres hzero

/-- The reassembled bivariate relation polynomial `∑_{i∈s} C(Qᵢ)·Xⁱ ∈ ℂ[z,Y][X]`. -/
noncomputable def bivarPoly (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ) :
    (Polynomial (Polynomial ℂ))[X] :=
  ∑ i ∈ s, Polynomial.C (Q i) * Polynomial.X ^ i

/-- Specializing the reassembled polynomial at `(z, γ z)` recovers the native analytic fibre. -/
theorem map_bivarPoly_eval₂ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ) (z : ℂ) (y : ℂ) :
    (bivarPoly Q s).map (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) y)
      = fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) y) s z := by
  classical
  rw [bivarPoly, fibrePoly, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coe_eval₂RingHom]

/-- `bivarPoly Q s` reconstructed from a polynomial's own support/coefficients is that polynomial. -/
theorem bivarPoly_support_coeff (P : (Polynomial (Polynomial ℂ))[X]) :
    bivarPoly (fun i => P.coeff i) P.support = P := by
  rw [bivarPoly]; exact (Polynomial.as_sum_support_C_mul_X_pow P).symm

/-- **The separable-fibre witness producer (A3 core).** Suppose the reassembled bivariate relation
`P ∈ ℂ[z,Y][X]` is separable over the fraction field `ℂ(z,Y)` (the irreducible/minimal case) and has
positive `X`-degree, and let `γ` be a function agreeing with `φ_{c₂}` on `U`, where `φ_{c₂}` is
transcendental over `ℂ(z)` (`hG`).  Then there is a point `w ∈ U ∖ K_{c₂}` at which the leading
coefficient survives and the specialized fibre `∑_{i∈s} Qᵢ(w,γ w)·Xⁱ` (with `Qᵢ = P.coeff i`,
`s = P.support`) is separable.

The nonzero bivariate polynomial `P.leadingCoeff · (∂P).leadingCoeff · Res(P,∂P) ∈ ℂ[z,Y]`
(`resultant_ne_zero_of_separable`) cannot vanish along `Y = φ_{c₂}` by transcendence, giving `w`; at
`w` all three factors survive, so `separable_specialize_ringHom` yields separability of the
specialization, and `map_bivarPoly_eval₂` rewrites it as a `fibrePoly`. -/
theorem exists_separable_fibre_witness_of_separable_over_field
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (γ : ℂ → ℂ) (hγ : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (P : (Polynomial (Polynomial ℂ))[X])
    (hsep : (P.map (algebraMap (Polynomial (Polynomial ℂ))
              (FractionRing (Polynomial (Polynomial ℂ))))).Separable)
    (hdeg : 1 ≤ P.natDegree) :
    ∃ w ∈ U, w ∈ (filledJulia c₂)ᶜ ∧
      (fun i z => (P.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z)) P.natDegree w ≠ 0 ∧
      (fibrePoly (fun i z => (P.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z))
        P.support w).Separable := by
  classical
  -- the three surviving factors, as a single nonzero bivariate polynomial
  have hP_ne : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; exact absurd hdeg (by norm_num)
  have hderiv_ne : derivative P ≠ 0 := by
    intro h; have := natDegree_eq_zero_of_derivative_eq_zero h; omega
  have hlc1 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP_ne
  have hlc2 : (derivative P).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hderiv_ne
  have hres : resultant P (derivative P) ≠ 0 :=
    HolomorphicIFT.resultant_ne_zero_of_separable P hsep
  set q : Polynomial (Polynomial ℂ) :=
    P.leadingCoeff * (derivative P).leadingCoeff * resultant P (derivative P) with hq
  have hq_ne : q ≠ 0 := by rw [hq]; exact mul_ne_zero (mul_ne_zero hlc1 hlc2) hres
  -- transcendence: the bivariate polynomial does not vanish along `Y = φ_{c₂}`
  obtain ⟨w, hwU, hwJ, hqw⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG γ hγ hq_ne
  -- decode the three surviving factors at `w`
  set ψ : Polynomial (Polynomial ℂ) →+* ℂ :=
    Polynomial.eval₂RingHom (Polynomial.evalRingHom w) (γ w) with hψ
  have hqw' : ψ q ≠ 0 := by rw [hψ, Polynomial.coe_eval₂RingHom]; exact hqw
  rw [hq, map_mul, map_mul] at hqw'
  obtain ⟨hprod, hresw⟩ := mul_ne_zero_iff.mp hqw'
  obtain ⟨hleadw, hlead'w⟩ := mul_ne_zero_iff.mp hprod
  -- specialization is separable
  have hsepw : (P.map ψ).Separable := separable_specialize_ringHom ψ hleadw hlead'w hresw
  refine ⟨w, hwU, hwJ, ?_, ?_⟩
  · -- top coefficient survives: `(P.coeff N).eval₂(...) = ψ P.leadingCoeff ≠ 0`
    show (P.coeff P.natDegree).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0
    have : (P.coeff P.natDegree).eval₂ (Polynomial.evalRingHom w) (γ w) = ψ P.leadingCoeff := by
      rw [hψ, Polynomial.coe_eval₂RingHom]; rfl
    rw [this]; exact hleadw
  · -- separability transported to the native fibre
    have hmap : (bivarPoly (fun i => P.coeff i) P.support).map ψ
        = fibrePoly (fun i z => (P.coeff i).eval₂ (Polynomial.evalRingHom z) (γ w)) P.support w := by
      rw [hψ]; exact map_bivarPoly_eval₂ (fun i => P.coeff i) P.support w (γ w)
    rw [bivarPoly_support_coeff] at hmap
    -- the fibre coefficients only depend on `z` through `evalRingHom z`, and here `z = w`
    have hfib : fibrePoly (fun i z => (P.coeff i).eval₂ (Polynomial.evalRingHom z) (γ z)) P.support w
        = fibrePoly (fun i z => (P.coeff i).eval₂ (Polynomial.evalRingHom z) (γ w)) P.support w := rfl
    rw [hfib, ← hmap]; exact hsepw

end Bottcher
