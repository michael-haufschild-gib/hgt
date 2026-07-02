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

/-! ## The descent to an irreducible relation

To feed `exists_separable_fibre_witness_of_separable_over_field` we must first replace an arbitrary
relation by one whose reassembled polynomial is separable over `ℂ(z,Y)`.  In characteristic 0 that is
the *irreducible* case, reached by factoring: a reducible relation `P = A·B` over `ℂ(z,Y)`, cleared to
`Ã, B̃ ∈ ℂ[z,Y][X]`, satisfies `relFun(Ã)·relFun(B̃) ≡ 0` on `U`, so the analytic integral domain
(`analyticOnNhd_domain`, the identity theorem on the connected `U`) forces one factor's relation — a
strictly lower `X`-degree relation.  Well-founded recursion terminates at an irreducible relation.
This mirrors `U0Transcendence.u0_no_relation`, returning the irreducible factor instead of `False`. -/

/-- The relation function of a reassembled bivariate polynomial `T ∈ ℂ[z,Y][X]`:
`z ↦ T(z, φ_{c₂}(z), φ_{c₁}(z))`, as the value of the double-evaluation ring homomorphism. -/
noncomputable def relFun (c₁ c₂ : ℂ) (T : (Polynomial (Polynomial ℂ))[X]) (z : ℂ) : ℂ :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
    (bottcherCoord c₁ z) T

/-- `relFun` is multiplicative in the polynomial argument (it is a ring-hom evaluation). -/
theorem relFun_mul (c₁ c₂ : ℂ) (A B : (Polynomial (Polynomial ℂ))[X]) (z : ℂ) :
    relFun c₁ c₂ (A * B) z = relFun c₁ c₂ A z * relFun c₁ c₂ B z := by
  simp only [relFun, map_mul]

/-- On a reassembled polynomial, `relFun` is the native support-sum relation. -/
theorem relFun_bivarPoly (c₁ c₂ : ℂ) (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ) (z : ℂ) :
    relFun c₁ c₂ (bivarPoly Q s) z
      = ∑ i ∈ s, ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i := by
  rw [relFun, bivarPoly, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_pow]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]

/-- `relFun T` in native support-sum form (via `bivarPoly_support_coeff`). -/
theorem relFun_eq_sum (c₁ c₂ : ℂ) (T : (Polynomial (Polynomial ℂ))[X]) (z : ℂ) :
    relFun c₁ c₂ T z
      = ∑ i ∈ T.support, ((T.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i := by
  conv_lhs => rw [← bivarPoly_support_coeff T]
  rw [relFun_bivarPoly]

/-- **The relation function is analytic on `U`.** Each coefficient `(T.coeff i)(z, φ_{c₂}(z))` is
analytic (`analyticOnNhd_eval₂_of_analyticOnNhd`, `φ_{c₂}` analytic on `U ⊆ escapeOpen c₂`), and
`φ_{c₁}(z)ⁱ` is analytic (`U ⊆ escapeOpen c₁`); the finite support-sum of products is analytic. -/
theorem analyticOnNhd_relFun (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (T : (Polynomial (Polynomial ℂ))[X]) :
    AnalyticOnNhd ℂ (relFun c₁ c₂ T) U := by
  have hbc1 : AnalyticOnNhd ℂ (bottcherCoord c₁) U := (analyticOnNhd_bottcherCoord_full c₁).mono hU₁
  have hbc2 : AnalyticOnNhd ℂ (bottcherCoord c₂) U := (analyticOnNhd_bottcherCoord_full c₂).mono hU₂
  have hfun : relFun c₁ c₂ T
      = fun z => ∑ i ∈ T.support,
          ((T.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i := by
    funext z; exact relFun_eq_sum c₁ c₂ T z
  rw [hfun]
  refine Finset.analyticOnNhd_fun_sum T.support (fun i _ => ?_)
  exact (analyticOnNhd_eval₂_of_analyticOnNhd hbc2 (T.coeff i)).mul (hbc1.pow i)

/-- **Descent to an irreducible relation.** From any relation `relFun T ≡ 0` on `U` with positive
`X`-degree, produce an irreducible-over-`ℂ(z,Y)` relation of positive degree still holding on `U`.
Strong induction on the `X`-degree: irreducible → done; reducible → clear a factorization to
`ℂ[z,Y][X]`, `analyticOnNhd_domain` picks the vanishing factor, recurse.  Mirrors
`U0Transcendence.u0_no_relation`. -/
theorem exists_irreducible_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (T : (Polynomial (Polynomial ℂ))[X]) (hdeg : 1 ≤ T.natDegree)
    (hrel : ∀ z ∈ U, relFun c₁ c₂ T z = 0) :
    ∃ T' : (Polynomial (Polynomial ℂ))[X],
      Irreducible (T'.map (algebraMap (Polynomial (Polynomial ℂ))
        (FractionRing (Polynomial (Polynomial ℂ))))) ∧
      1 ≤ T'.natDegree ∧ (∀ z ∈ U, relFun c₁ c₂ T' z = 0) := by
  classical
  set R := Polynomial (Polynomial ℂ)
  set alg := algebraMap R (FractionRing R) with halg
  have halginj : Function.Injective alg := IsFractionRing.injective _ _
  have hsmul : ∀ (r : R) (p : (FractionRing R)[X]), r • p = Polynomial.C (alg r) * p :=
    fun r p => by
      rw [← algebraMap_smul (FractionRing R) r p, Polynomial.smul_eq_C_mul]
  suffices H : ∀ d : ℕ, ∀ Q : R[X], Q.natDegree = d → 1 ≤ Q.natDegree →
      (∀ z ∈ U, relFun c₁ c₂ Q z = 0) →
      ∃ T' : R[X], Irreducible (T'.map alg) ∧ 1 ≤ T'.natDegree ∧
        (∀ z ∈ U, relFun c₁ c₂ T' z = 0) by
    exact H T.natDegree T rfl hdeg hrel
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro Q hQd hQ1 hQrel
    have hQ0 : Q ≠ 0 := fun h => by rw [h, natDegree_zero] at hQ1; omega
    set Qf := Q.map alg with hQf
    have hQfdeg : Qf.natDegree = Q.natDegree := natDegree_map_eq_of_injective halginj Q
    have hQf0 : Qf ≠ 0 := fun h => hQ0 ((Polynomial.map_eq_zero_iff halginj).mp h)
    by_cases hirr : Irreducible Qf
    · exact ⟨Q, hirr, hQ1, hQrel⟩
    · have hQf_nu : ¬ IsUnit Qf := fun hu => by
        have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        rw [hQfdeg, hQd] at h0; omega
      obtain ⟨A, B, hAnu, hBnu, hPfAB⟩ := (irreducible_or_factor hQf_nu).resolve_left hirr
      have hA0 : A ≠ 0 := by rintro rfl; rw [zero_mul] at hPfAB; exact hQf0 hPfAB
      have hB0 : B ≠ 0 := by rintro rfl; rw [mul_zero] at hPfAB; exact hQf0 hPfAB
      obtain ⟨bA, hbAmem, hbA⟩ :=
        IsLocalization.integerNormalization_spec (nonZeroDivisors R) A
      obtain ⟨bB, hbBmem, hbB⟩ :=
        IsLocalization.integerNormalization_spec (nonZeroDivisors R) B
      set Atil := IsLocalization.integerNormalization (nonZeroDivisors R) A with hAtil
      set Btil := IsLocalization.integerNormalization (nonZeroDivisors R) B with hBtil
      have hbApoly0 : bA ≠ 0 := nonZeroDivisors.ne_zero hbAmem
      have hbBpoly0 : bB ≠ 0 := nonZeroDivisors.ne_zero hbBmem
      have hbA0 : alg bA ≠ 0 := fun h => hbApoly0 (halginj (by rw [h, map_zero]))
      have hbB0 : alg bB ≠ 0 := fun h => hbBpoly0 (halginj (by rw [h, map_zero]))
      have hAtil0 : Atil ≠ 0 := fun h => hA0
        ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hAtil, h]))
      have hBtil0 : Btil ≠ 0 := fun h => hB0
        ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hBtil, h]))
      have hdegA : 1 ≤ A.natDegree := by
        rcases Nat.eq_zero_or_pos A.natDegree with h | h
        · exfalso; apply hAnu
          rw [Polynomial.eq_C_of_natDegree_eq_zero h]
          refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
          intro hc; apply hA0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc, map_zero]
        · exact h
      have hdegB : 1 ≤ B.natDegree := by
        rcases Nat.eq_zero_or_pos B.natDegree with h | h
        · exfalso; apply hBnu
          rw [Polynomial.eq_C_of_natDegree_eq_zero h]
          refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
          intro hc; apply hB0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc, map_zero]
        · exact h
      have hdegAtil : Atil.natDegree = A.natDegree := by
        have h1 := natDegree_map_eq_of_injective halginj Atil
        rw [hbA, hsmul, Polynomial.natDegree_C_mul hbA0] at h1; omega
      have hdegBtil : Btil.natDegree = B.natDegree := by
        have h1 := natDegree_map_eq_of_injective halginj Btil
        rw [hbB, hsmul, Polynomial.natDegree_C_mul hbB0] at h1; omega
      have hdescent : Atil * Btil = Polynomial.C (bA * bB) * Q := by
        apply Polynomial.map_injective alg halginj
        rw [Polynomial.map_mul, hbA, hbB, hsmul, hsmul, Polynomial.map_mul, Polynomial.map_C,
          map_mul alg, Polynomial.C_mul, ← hQf, hPfAB]
        ring
      have hdegsum : Atil.natDegree + Btil.natDegree = d := by
        have hm := Polynomial.natDegree_mul hAtil0 hBtil0
        rw [hdescent, Polynomial.natDegree_C_mul (mul_ne_zero hbApoly0 hbBpoly0), hQd] at hm
        omega
      have heval : EqOn (fun z => relFun c₁ c₂ Atil z * relFun c₁ c₂ Btil z) 0 U := by
        intro z hz
        simp only [Pi.zero_apply]
        rw [← relFun_mul, hdescent, relFun_mul, hQrel z hz, mul_zero]
      rcases analyticOnNhd_domain (analyticOnNhd_relFun c₁ c₂ hU₁ hU₂ Atil)
          (analyticOnNhd_relFun c₁ c₂ hU₁ hU₂ Btil) hUc hUo heval with hAz | hBz
      · exact IH Atil.natDegree (by omega) Atil rfl (by omega)
          (fun z hz => hAz hz)
      · exact IH Btil.natDegree (by omega) Btil rfl (by omega)
          (fun z hz => hBz hz)

/-- **A3 packaged: from any relation, a descended irreducible relation with a separable fibre
witness.** Given a positive-degree relation `∑_{i∈s} Qᵢ(z,φ_{c₂}z)·φ_{c₁}(z)ⁱ ≡ 0` on `U` and
transcendence of `φ_{c₂}` (`hG`), there is an irreducible-over-`ℂ(z,Y)` relation polynomial `T'`
(positive `X`-degree, still holding on `U`) and a point `w ∈ U ∖ K_{c₂}` at which the native fibre
`∑_{i∈T'.support} (T'.coeff i)(z,φ_{c₂}z)·Xⁱ` is separable with nonvanishing leading coefficient —
exactly the generic-fibre nondegeneracy that the relative branch machinery consumes.  Combines the
descent (`exists_irreducible_relation`, `Irreducible.separable`) with the witness producer
(`exists_separable_fibre_witness_of_separable_over_field`). -/
theorem exists_separable_relation_of_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hpos : 1 ≤ (bivarPoly Q s).natDegree)
    (hrel : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    ∃ (T' : (Polynomial (Polynomial ℂ))[X]) (w : ℂ),
      1 ≤ T'.natDegree ∧ w ∈ U ∧ w ∈ (filledJulia c₂)ᶜ ∧
      (T'.coeff T'.natDegree).eval₂ (Polynomial.evalRingHom w) (bottcherCoord c₂ w) ≠ 0 ∧
      (fibrePoly (fun i z => (T'.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
        T'.support w).Separable ∧
      Set.EqOn (fun z => ∑ i ∈ T'.support,
        ((T'.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U ∧
      ∀ ζ : ℂ, ‖ζ‖ = 1 → ¬ (∀ z ∈ U, ∑ i ∈ T'.support,
        ((T'.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * ζ ^ i = 0) := by
  -- descend to an irreducible relation
  obtain ⟨T', hirr, hdeg', hrel'⟩ :=
    exists_irreducible_relation hUo hUc c₁ c₂ hU₁ hU₂ (bivarPoly Q s) hpos (by
      intro z hz
      rw [relFun_bivarPoly]
      simpa using hrel hz)
  have hsep' : (T'.map (algebraMap (Polynomial (Polynomial ℂ))
      (FractionRing (Polynomial (Polynomial ℂ))))).Separable := hirr.separable
  -- the separable fibre witness (γ = bottcherCoord c₂ directly)
  obtain ⟨w, hwU, hwJ, hlead, hsepw⟩ :=
    exists_separable_fibre_witness_of_separable_over_field hUo hUc hUne hUinf c₂ hU₂ hG
      (bottcherCoord c₂) (fun _ _ => rfl) T' hsep' hdeg'
  refine ⟨T', w, hdeg', hwU, hwJ, hlead, hsepw, ?_, ?_⟩
  · intro z hz
    simp only [Pi.zero_apply]
    rw [← relFun_eq_sum]; exact hrel' z hz
  · -- **no constant unit root**: a unit `ζ` killing every specialized fibre on `U` makes
    -- `ζ` a root of `T'` over `ℂ[z,Y]` (transcendence of `φ_{c₂}` zeroes the substituted
    -- polynomial `T'(ζ)`), so `(X - C ζ) ∣ T'`; irreducibility over the fraction field then
    -- forces `T'` linear with the constant root `ζ`, and the relation factors as
    -- `g(z, φ_{c₂}(z)) · (φ_{c₁}(z) - ζ) ≡ 0` on `U`.  Since `‖φ_{c₁}‖ > 1 = ‖ζ‖` on the
    -- escape region, the second factor never vanishes, so `g` dies by transcendence — but
    -- `g` is the (nonzero) cofactor of a nonzero `T'`.  Contradiction.
    intro ζ hζ1 hall
    set R := Polynomial (Polynomial ℂ)
    set a : R := Polynomial.C (Polynomial.C ζ) with hadef
    -- the substituted polynomial `T'(ζ) ∈ ℂ[z,Y]` vanishes along the curve `Y = φ_{c₂}`
    have hqeval : ∀ z : ℂ,
        (T'.eval a).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)
          = ∑ i ∈ T'.support,
              ((T'.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) * ζ ^ i := by
      intro z
      rw [show T'.eval a = ∑ i ∈ T'.support, T'.coeff i * a ^ i by
        rw [Polynomial.eval_eq_sum, Polynomial.sum_def]]
      rw [show ((∑ i ∈ T'.support, T'.coeff i * a ^ i).eval₂
            (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          = Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (bottcherCoord c₂ z)
              (∑ i ∈ T'.support, T'.coeff i * a ^ i) from rfl]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow]
      simp [hadef, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    have hq0 : T'.eval a = 0 := by
      by_contra hne
      obtain ⟨w', hw'U, _, hw'ne⟩ :=
        exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
          hUo hUc hUne hUinf c₂ hU₂ hG (bottcherCoord c₂) (fun _ _ => rfl) hne
      exact hw'ne ((hqeval w').trans (hall w' hw'U))
    have hroot : (Polynomial.X - Polynomial.C a) ∣ T' := Polynomial.dvd_iff_isRoot.mpr hq0
    -- transport to the fraction field: irreducibility forces `T'` linear
    set alg := algebraMap R (FractionRing R) with halg
    have halginj : Function.Injective alg := IsFractionRing.injective _ _
    obtain ⟨e, he⟩ := hroot
    have heF : T'.map alg = (Polynomial.X - Polynomial.C (alg a)) * e.map alg := by
      rw [he, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hXnu : ¬ IsUnit (Polynomial.X - Polynomial.C (alg a)) := by
      intro hu
      have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [Polynomial.natDegree_X_sub_C] at h0
      exact one_ne_zero h0
    have heunit : IsUnit (e.map alg) := (hirr.isUnit_or_isUnit heF).resolve_left hXnu
    have hT'deg1 : T'.natDegree = 1 := by
      have hmap : (T'.map alg).natDegree = T'.natDegree :=
        natDegree_map_eq_of_injective halginj T'
      have hedeg : (e.map alg).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit heunit
      have hX0 : (Polynomial.X - Polynomial.C (alg a)) ≠ 0 := Polynomial.X_sub_C_ne_zero _
      have he0 : e.map alg ≠ 0 := heunit.ne_zero
      have hm := Polynomial.natDegree_mul hX0 he0
      rw [← heF, hmap, Polynomial.natDegree_X_sub_C, hedeg] at hm
      omega
    -- the cofactor in `ℂ[z,Y][X]` is a nonzero constant `g`
    have hT'ne : T' ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hdeg'; omega
    have he_ne : e ≠ 0 := fun h => hT'ne (by rw [he, h, mul_zero])
    have hXa_ne : (Polynomial.X - Polynomial.C a) ≠ 0 := Polynomial.X_sub_C_ne_zero _
    have hedeg0 : e.natDegree = 0 := by
      have hm := Polynomial.natDegree_mul hXa_ne he_ne
      rw [← he, hT'deg1, Polynomial.natDegree_X_sub_C] at hm
      omega
    have hec : e = Polynomial.C (e.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hedeg0
    have hg_ne : e.coeff 0 ≠ 0 := by
      intro h
      apply he_ne
      rw [hec, h, Polynomial.C_0]
    -- the relation factors as `(φ₁ - ζ)·g(z,φ₂) ≡ 0` on `U`
    have hfac : ∀ z ∈ U, (bottcherCoord c₁ z - ζ)
        * ((e.coeff 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) = 0 := by
      intro z hz
      have h1 : relFun c₁ c₂ T' z = 0 := hrel' z hz
      rw [he, hec, relFun_mul] at h1
      have hX : relFun c₁ c₂ (Polynomial.X - Polynomial.C a) z = bottcherCoord c₁ z - ζ := by
        simp [relFun, hadef, Polynomial.eval₂_C]
      have hC : relFun c₁ c₂ (Polynomial.C (e.coeff 0)) z
          = (e.coeff 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
        simp [relFun, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [hX, hC] at h1
      exact h1
    -- the first factor never vanishes on the escape region: `‖φ₁‖ > 1 = ‖ζ‖`
    have hφne : ∀ z ∈ U, bottcherCoord c₁ z - ζ ≠ 0 := by
      intro z hz h0
      have hesc : max 2 ‖c₁‖ < ‖z‖ := hU₁ hz
      have hgt : 1 < ‖bottcherCoord c₁ z‖ :=
        one_lt_norm_bottcherCoord (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hesc))
          (lt_of_le_of_lt (le_max_left _ _) hesc)
      rw [sub_eq_zero] at h0
      rw [h0, hζ1] at hgt
      exact lt_irrefl _ hgt
    -- so `g` vanishes along the curve, hence `g = 0` by transcendence — contradiction
    have hgz : ∀ z ∈ U, (e.coeff 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) = 0 := by
      intro z hz
      rcases mul_eq_zero.mp (hfac z hz) with h | h
      · exact absurd h (hφne z hz)
      · exact h
    obtain ⟨w', hw'U, _, hw'ne⟩ :=
      exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
        hUo hUc hUne hUinf c₂ hU₂ hG (bottcherCoord c₂) (fun _ _ => rfl) hg_ne
    exact hw'ne (hgz w' hw'U)

end Bottcher
