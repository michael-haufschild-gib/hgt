/-
# The exact minimal leading coefficient at the minimal differential order

At the minimal homogeneous order `r + 1` the symbol of any annihilator of `q + ∑_i E_i` factors as
`(c_{r+1}·X + t)·L₀`, so the rational part obeys the first-order relation
`c_{r+1}·h′ = -t·h` on the shadow `h = L₀ q`.  Over `C(s)` with polynomial coefficients both
`c_{r+1}` and the tail `t` are polynomials, and the shadow radical `rad(num h · denom h)` is
therefore the exact minimal leading coefficient: it divides every admissible `c_{r+1}`
(`shadowRadical_dvd_leadingCoeff`) and is itself realised
(`exists_polynomial_annihilator_shadowRadical`).
-/
import GaloisForLFunctions.HTGeometry.ExponentialRationalMinimalOrder
import GaloisForLFunctions.HTGeometry.RationalLogarithmicDerivativeRadical
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions.HTGeometry
open Polynomial

variable {F : Type*} [Field F] [Differential F]

omit [Differential F] in
/-- The symbol of an annihilator vanishing at every eigenvalue is divisible by `L₀`. -/
theorem factorPoly_dvd_symbolPoly {r : ℕ} {lam : Fin r → F} (hlam : Function.Injective lam)
    (c : ℕ → F) (n : ℕ) (hP : symbolPoly c n ≠ 0)
    (hsym : ∀ i, symbolEval c n (lam i) = 0) :
    factorPoly (List.ofFn lam) ∣ symbolPoly c n := by
  classical
  set l : List F := List.ofFn lam with hl
  have hnodup : l.Nodup := by rw [hl]; exact List.nodup_ofFn.mpr hlam
  have hle : (↑l : Multiset F) ≤ (symbolPoly c n).roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ l
    · have hnodupM : (↑l : Multiset F).Nodup := by rw [Multiset.coe_nodup]; exact hnodup
      have h1 : Multiset.count a (↑l : Multiset F) ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp hnodupM a
      have hroot : (symbolPoly c n).IsRoot a := by
        rw [hl, List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        rw [Polynomial.IsRoot, symbolPoly_eval]
        exact hsym i
      have h2 : 1 ≤ Multiset.count a (symbolPoly c n).roots := by
        rw [Multiset.one_le_count_iff_mem, Polynomial.mem_roots hP]
        exact hroot
      omega
    · rw [Multiset.count_eq_zero_of_notMem (by simpa using ha)]
      exact Nat.zero_le _
  have hd := (Multiset.prod_X_sub_C_dvd_iff_le_roots hP (↑l : Multiset F)).mpr hle
  have heq : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (↑l : Multiset F)).prod
      = factorPoly l := by rw [factorPoly]; simp
  rwa [heq] at hd

omit [Differential F] in
theorem symbolPoly_ne_zero_of_top {c : ℕ → F} {n : ℕ} (hc : c n ≠ 0) : symbolPoly c n ≠ 0 := by
  intro hzero
  exact hc (by rw [← symbolPoly_coeff c n (le_refl n), hzero, Polynomial.coeff_zero])

/-- The tail coefficient of the order-`r+1` symbol after removing its leading linear term. -/
def linearTail (c : ℕ → F) (l : List F) (r : ℕ) : F :=
  (symbolPoly c (r + 1) - Polynomial.C (c (r + 1)) * Polynomial.X * factorPoly l).coeff r

omit [Differential F] in
/-- **Order-`r+1` symbol factorization.**  A symbol of order `r + 1` vanishing at the `r` distinct
eigenvalues is `(c_{r+1}·X + linearTail)·L₀`. -/
theorem symbolPoly_eq_linear_mul {r : ℕ} {lam : Fin r → F} (hlam : Function.Injective lam)
    (c : ℕ → F) (hc : c (r + 1) ≠ 0)
    (hsym : ∀ i, symbolEval c (r + 1) (lam i) = 0) :
    symbolPoly c (r + 1)
      = (Polynomial.C (c (r + 1)) * Polynomial.X
          + Polynomial.C (linearTail c (List.ofFn lam) r)) * factorPoly (List.ofFn lam) := by
  classical
  set l : List F := List.ofFn lam with hl
  have hlength : l.length = r := by rw [hl, List.length_ofFn]
  have hP : symbolPoly c (r + 1) ≠ 0 := symbolPoly_ne_zero_of_top hc
  obtain ⟨Q, hQ⟩ := factorPoly_dvd_symbolPoly hlam c (r + 1) hP hsym
  rw [← hl] at hQ
  have hfacdeg : (factorPoly l).natDegree = r := by rw [factorPoly_natDegree, hlength]
  have hfacne : factorPoly l ≠ 0 := (factorPoly_monic l).ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hQ
    exact hP hQ
  have hQdeg : Q.natDegree ≤ 1 := by
    have h1 : (symbolPoly c (r + 1)).natDegree = r + Q.natDegree := by
      rw [hQ, Polynomial.natDegree_mul hfacne hQne, hfacdeg]
    have h2 := symbolPoly_natDegree_le c (r + 1)
    omega
  have hQlin : Q = Polynomial.C (Q.coeff 1) * Polynomial.X + Polynomial.C (Q.coeff 0) :=
    Polynomial.eq_X_add_C_of_degree_le_one (Polynomial.natDegree_le_iff_degree_le.mp hQdeg)
  -- the leading coefficient of the linear factor is `c (r+1)`
  have hmoniccoeff : (factorPoly l).coeff r = 1 := by
    have := (factorPoly_monic l).coeff_natDegree
    rwa [hfacdeg] at this
  have htopzero : (factorPoly l).coeff (r + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeff1 : Q.coeff 1 = c (r + 1) := by
    have hbase : (symbolPoly c (r + 1)).coeff (r + 1) = c (r + 1) :=
      symbolPoly_coeff c (r + 1) (le_refl _)
    rw [← hbase, hQ]
    have hexp : factorPoly l * (Polynomial.C (Q.coeff 1) * Polynomial.X
          + Polynomial.C (Q.coeff 0))
        = Polynomial.C (Q.coeff 1) * (factorPoly l * Polynomial.X)
          + Polynomial.C (Q.coeff 0) * factorPoly l := by ring
    conv_rhs => rw [hQlin]
    rw [hexp, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_X, hmoniccoeff, htopzero, mul_one, mul_zero, add_zero]
  -- the tail coefficient is `Q.coeff 0`
  have hQeq : Q = Polynomial.C (c (r + 1)) * Polynomial.X + Polynomial.C (Q.coeff 0) := by
    conv_lhs => rw [hQlin]
    rw [hcoeff1]
  have htail : linearTail c l r = Q.coeff 0 := by
    have hsub : symbolPoly c (r + 1)
        - Polynomial.C (c (r + 1)) * Polynomial.X * factorPoly l
        = Polynomial.C (Q.coeff 0) * factorPoly l := by
      rw [hQ]
      conv_lhs => rw [hQeq]
      ring
    rw [linearTail, hsub, Polynomial.coeff_C_mul, hmoniccoeff, mul_one]
  rw [hQ]
  conv_lhs => rw [hQeq]
  rw [htail]
  ring

/-- **The linear relation on the rational shadow.**  An order-`r+1` annihilator forces
`c_{r+1}·h′ = -(linearTail)·h` on the shadow `h = L₀ q`. -/
theorem leadingCoeff_mul_deriv_shadow {r : ℕ} {lam : Fin r → F} (hlam : Function.Injective lam)
    (hlamc : ∀ i, (lam i)′ = 0)
    (c : ℕ → F) (hc : c (r + 1) ≠ 0)
    (hsym : ∀ i, symbolEval c (r + 1) (lam i) = 0)
    (q : F) (hbase : linOpBase c (r + 1) q = 0) :
    c (r + 1) * (opList (List.ofFn lam) q)′
      = (-(linearTail c (List.ofFn lam) r)) * opList (List.ofFn lam) q := by
  classical
  set l : List F := List.ofFn lam with hl
  have hlength : l.length = r := by rw [hl, List.length_ofFn]
  have hlconst : ∀ mu ∈ l, mu′ = 0 := by
    intro mu hmu
    rw [hl, List.mem_ofFn] at hmu
    obtain ⟨i, rfl⟩ := hmu
    exact hlamc i
  have hdegFac : (factorPoly l).natDegree ≤ r := by rw [factorPoly_natDegree, hlength]
  have hsplit := symbolPoly_eq_linear_mul hlam c hc hsym
  have hrw : (Polynomial.C (c (r + 1)) * Polynomial.X
        + Polynomial.C (linearTail c l r)) * factorPoly l
      = (Polynomial.C (c (r + 1)) * Polynomial.X
        - Polynomial.C (-(linearTail c l r))) * factorPoly l := by
    rw [map_neg, sub_neg_eq_add]
  have hzero : linOpBase (symbolPoly c (r + 1)).coeff (r + 1) q = 0 := by
    rw [linOpBase_symbolPoly]; exact hbase
  rw [hsplit, hrw, linOpBase_linear_mul hdegFac (factorPoly_coeff_deriv hlconst) q] at hzero
  have hfac : linOpBase (factorPoly l).coeff r q = opList l q := by
    rw [← hlength]; exact linOpBase_factorPoly hlconst q
  rw [hfac] at hzero
  linear_combination hzero


section GeneralAnnihilator

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

omit [Field M] [Algebra F M] [Differential F] [Differential M] [DifferentialAlgebra F M] in
/-- The leading coefficient of an order-`r+1` symbol `(a·X - b)·L₀` is `a`. -/
theorem coeff_linear_mul_factorPoly_top (l : List F) (a b : F) :
    ((Polynomial.C a * Polynomial.X - Polynomial.C b) * factorPoly l).coeff (l.length + 1) = a := by
  have hfacdeg : (factorPoly l).natDegree = l.length := factorPoly_natDegree l
  have hmoniccoeff : (factorPoly l).coeff l.length = 1 := by
    have := (factorPoly_monic l).coeff_natDegree
    rwa [hfacdeg] at this
  have htopzero : (factorPoly l).coeff (l.length + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hexp : (Polynomial.C a * Polynomial.X - Polynomial.C b) * factorPoly l
      = Polynomial.C a * (factorPoly l * Polynomial.X)
        - Polynomial.C b * factorPoly l := by ring
  rw [hexp, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_X, hmoniccoeff, htopzero, mul_one, mul_zero, sub_zero]

/-- **An order-`r+1` annihilator from any realisation of the shadow's logarithmic derivative.** -/
theorem linOp_linear_mul_factorPoly_eq_zero {r : ℕ}
    (lam : Fin r → F) (hlamc : ∀ i, (lam i)′ = 0)
    (E : Fin r → M) (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (q : F) (a b : F)
    (hrel : a * (opList (List.ofFn lam) q)′ = b * opList (List.ofFn lam) q) :
    linOp ((Polynomial.C a * Polynomial.X - Polynomial.C b)
        * factorPoly (List.ofFn lam)).coeff (r + 1) (algebraMap F M q + ∑ i, E i) = 0 := by
  classical
  set l : List F := List.ofFn lam with hl
  set P : Polynomial F :=
    (Polynomial.C a * Polynomial.X - Polynomial.C b) * factorPoly l with hPdef
  have hlength : l.length = r := by rw [hl, List.length_ofFn]
  have hlconst : ∀ mu ∈ l, mu′ = 0 := by
    intro mu hmu
    rw [hl, List.mem_ofFn] at hmu
    obtain ⟨i, rfl⟩ := hmu
    exact hlamc i
  have hdegFac : (factorPoly l).natDegree ≤ r := by rw [factorPoly_natDegree, hlength]
  have hfac : linOpBase (factorPoly l).coeff r q = opList l q := by
    rw [← hlength]; exact linOpBase_factorPoly hlconst q
  have hbase : linOpBase P.coeff (r + 1) q = 0 := by
    rw [hPdef, linOpBase_linear_mul hdegFac (factorPoly_coeff_deriv hlconst) q, hfac, hrel,
      sub_self]
  have hdegP : P.natDegree ≤ r + 1 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have h1 : (Polynomial.C a * Polynomial.X - Polynomial.C b).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq Polynomial.natDegree_X)
      · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
    have h2 : (factorPoly l).natDegree ≤ r := hdegFac
    omega
  have hmodes : ∀ i, symbolEval P.coeff (r + 1) (lam i) = 0 := by
    intro i
    rw [symbolEval_coeff_eq_eval hdegP, hPdef, Polynomial.eval_mul]
    have hzero : (factorPoly l).eval (lam i) = 0 := by
      refine factorPoly_eval_eq_zero ?_
      rw [hl, List.mem_ofFn]
      exact ⟨i, rfl⟩
    rw [hzero, mul_zero]
  rw [linOp_add, linOp_algebraMap, hbase, map_zero, zero_add, linOp_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [linOp_eigen _ _ (hlamc i) (heig i), hmodes i, map_zero, zero_mul]

end GeneralAnnihilator

section RatFuncSpecialization

open GaloisForLFunctions.RationalShadow

attribute [local instance] GaloisForLFunctions.ratFuncCoordinateDifferential

theorem ratFuncDeriv_eq (z : RatFunc ℂ) : z′ = ratFuncCoordinateDerivation ℂ z := rfl

theorem algebraMap_C_eq (μ : ℂ) :
    algebraMap ℂ (RatFunc ℂ) μ = algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C μ) := by
  rw [RatFunc.algebraMap_C]; rfl

theorem deriv_algebraMap_C (μ : ℂ) : (algebraMap ℂ (RatFunc ℂ) μ)′ = 0 := by
  rw [ratFuncDeriv_eq, algebraMap_C_eq, ratFuncCoordinateDerivation_algebraMap,
    Polynomial.derivative_C, map_zero]

/-- **Rigidity of the rational base.**  No nonzero rational function has a nonzero *constant*
logarithmic derivative. -/
theorem ratFunc_hconst :
    ∀ μ : RatFunc ℂ, μ′ = 0 → μ ≠ 0 → ∀ c : RatFunc ℂ, c ≠ 0 → c′ ≠ μ * c := by
  intro μ hμc hμ c hc
  obtain ⟨m, rfl⟩ := (ratFuncCoordinateDerivation_eq_zero_iff μ).mp hμc
  have hm : m ≠ 0 := by
    intro h
    rw [h, map_zero] at hμ
    exact hμ rfl
  rw [ratFuncDeriv_eq]
  exact ratFuncCoordinateDerivation_ne_smul hc hm

/-- The abstract annihilator over `C(s)` is the shifted-derivative product. -/
theorem opList_map_algebraMap (l : List ℂ) (q : RatFunc ℂ) :
    opList (l.map (algebraMap ℂ (RatFunc ℂ))) q = shiftedDerivProd l q := by
  induction l with
  | nil => rfl
  | cons mu l ih =>
      rw [List.map_cons, opList_cons, ih, shiftedDerivProd_cons, shiftedDeriv, ratFuncDeriv_eq]

theorem coeff_mem_range {P : Polynomial (RatFunc ℂ)}
    (hP : P ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range) (n : ℕ) :
    P.coeff n ∈ (algebraMap ℂ[X] (RatFunc ℂ)).range := by
  obtain ⟨P₀, hP₀⟩ := hP
  refine ⟨P₀.coeff n, ?_⟩
  rw [← hP₀]
  simp [Polynomial.coeff_map]

theorem symbolPoly_mem_range (p : ℕ → ℂ[X]) (n : ℕ) :
    symbolPoly (fun j => algebraMap ℂ[X] (RatFunc ℂ) (p j)) n
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range := by
  rw [symbolPoly]
  refine Subring.sum_mem _ (fun j _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ ?_ _))
  · exact ⟨Polynomial.C (p j), by simp⟩
  · exact ⟨Polynomial.X, by simp⟩

theorem factorPoly_mem_range (l : List ℂ) :
    factorPoly (l.map (algebraMap ℂ (RatFunc ℂ)))
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range := by
  rw [factorPoly]
  refine Subring.list_prod_mem _ (fun x hx => ?_)
  rw [List.mem_map] at hx
  obtain ⟨mu, hmu, rfl⟩ := hx
  rw [List.mem_map] at hmu
  obtain ⟨m, _, rfl⟩ := hmu
  exact ⟨Polynomial.X - Polynomial.C (Polynomial.C m), by
    simp [Polynomial.coe_mapRingHom]⟩

/-- **Item 3 over the rational base.**  Every polynomial-coefficient annihilator of order `r + 1`
for the mixed carrier has leading coefficient divisible by the shadow radical. -/
theorem shadowRadical_dvd_leadingCoeff
    {M : Type*} [Field M] [Algebra (RatFunc ℂ) M] [Differential M]
    [DifferentialAlgebra (RatFunc ℂ) M]
    {r : ℕ} (lam : Fin r → ℂ) (hlam : Function.Injective lam) (hlam0 : ∀ i, lam i ≠ 0)
    (E : Fin r → M) (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′ = algebraMap (RatFunc ℂ) M (algebraMap ℂ (RatFunc ℂ) (lam i)) * E i)
    {q : RatFunc ℂ} (hq : q ≠ 0)
    (p : ℕ → ℂ[X]) (hp : p (r + 1) ≠ 0)
    (hann : linOp (fun j => algebraMap ℂ[X] (RatFunc ℂ) (p j)) (r + 1)
        (algebraMap (RatFunc ℂ) M q + ∑ i, E i) = 0) :
    shadowRadical (shiftedDerivProd (List.ofFn lam) q) ∣ p (r + 1) := by
  classical
  have hφinj : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  set c : ℕ → RatFunc ℂ := fun j => algebraMap ℂ[X] (RatFunc ℂ) (p j) with hcdef
  set lamF : Fin r → RatFunc ℂ := fun i => algebraMap ℂ (RatFunc ℂ) (lam i) with hlamFdef
  have hKinj : Function.Injective (algebraMap ℂ (RatFunc ℂ)) :=
    (algebraMap ℂ (RatFunc ℂ)).injective
  have hlamFinj : Function.Injective lamF := hKinj.comp hlam
  have hlamF0 : ∀ i, lamF i ≠ 0 := by
    intro i hzero
    exact hlam0 i (hKinj (by rw [map_zero]; exact hzero))
  have hlamFc : ∀ i, (lamF i)′ = 0 := fun i => deriv_algebraMap_C (lam i)
  obtain ⟨hbase, hsym⟩ :=
    linOp_eq_zero_separation lamF hlamFinj hlamF0 hlamFc E hE heig ratFunc_hconst q c (r + 1) hann
  have hc : c (r + 1) ≠ 0 := by
    intro hzero
    exact hp (hφinj (by rw [map_zero]; exact hzero))
  have hrel := leadingCoeff_mul_deriv_shadow hlamFinj hlamFc c hc hsym q hbase
  have hofn : List.ofFn lamF = (List.ofFn lam).map (algebraMap ℂ (RatFunc ℂ)) := by
    rw [List.map_ofFn]; rfl
  have hbridge : opList (List.ofFn lamF) q = shiftedDerivProd (List.ofFn lam) q := by
    rw [hofn, opList_map_algebraMap]
  have hhne : shiftedDerivProd (List.ofFn lam) q ≠ 0 := by
    refine shiftedDerivProd_ne_zero (fun mu hmu => ?_) hq
    rw [List.mem_ofFn] at hmu
    obtain ⟨i, rfl⟩ := hmu
    exact hlam0 i
  have hCmem : (Polynomial.C (c (r + 1)) : Polynomial (RatFunc ℂ))
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range :=
    ⟨Polynomial.C (p (r + 1)), by simp [hcdef]⟩
  have hXmem : (Polynomial.X : Polynomial (RatFunc ℂ))
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range := ⟨Polynomial.X, by simp⟩
  have hfacmem : factorPoly (List.ofFn lamF)
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range := by
    rw [hofn]; exact factorPoly_mem_range _
  obtain ⟨b, hb⟩ : linearTail c (List.ofFn lamF) r ∈ (algebraMap ℂ[X] (RatFunc ℂ)).range :=
    coeff_mem_range
      (Subring.sub_mem _ (symbolPoly_mem_range p (r + 1))
        (Subring.mul_mem _ (Subring.mul_mem _ hCmem hXmem) hfacmem)) r
  refine shadowRadical_dvd (b := -b) hhne hp ?_
  rw [← hbridge, ← ratFuncDeriv_eq, map_neg, hb]
  exact hrel

/-- **Item 3, attainment over the rational base.**  There is an order-`r+1` annihilator with
polynomial coefficients whose leading coefficient is exactly the shadow radical. -/
theorem exists_polynomial_annihilator_shadowRadical
    {M : Type*} [Field M] [Algebra (RatFunc ℂ) M] [Differential M]
    [DifferentialAlgebra (RatFunc ℂ) M]
    {r : ℕ} (lam : Fin r → ℂ)
    (E : Fin r → M)
    (heig : ∀ i, (E i)′ = algebraMap (RatFunc ℂ) M (algebraMap ℂ (RatFunc ℂ) (lam i)) * E i)
    (q : RatFunc ℂ) :
    ∃ p : ℕ → ℂ[X],
      p (r + 1) = shadowRadical (shiftedDerivProd (List.ofFn lam) q)
        ∧ linOp (fun j => algebraMap ℂ[X] (RatFunc ℂ) (p j)) (r + 1)
            (algebraMap (RatFunc ℂ) M q + ∑ i, E i) = 0 := by
  classical
  have hφinj : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  set lamF : Fin r → RatFunc ℂ := fun i => algebraMap ℂ (RatFunc ℂ) (lam i) with hlamFdef
  have hlamFc : ∀ i, (lamF i)′ = 0 := fun i => deriv_algebraMap_C (lam i)
  have hofn : List.ofFn lamF = (List.ofFn lam).map (algebraMap ℂ (RatFunc ℂ)) := by
    rw [List.map_ofFn]; rfl
  set hsh : RatFunc ℂ := shiftedDerivProd (List.ofFn lam) q with hshdef
  have hbridge : opList (List.ofFn lamF) q = hsh := by
    rw [hshdef, hofn, opList_map_algebraMap]
  obtain ⟨b₀, hb₀⟩ := exists_cross_shadowRadical hsh
  set a : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (shadowRadical hsh) with hadef
  set bb : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) b₀ with hbbdef
  have hrel : a * (opList (List.ofFn lamF) q)′ = bb * opList (List.ofFn lamF) q := by
    rw [hbridge, ratFuncDeriv_eq]
    exact hb₀
  have hann := linOp_linear_mul_factorPoly_eq_zero lamF hlamFc E heig q a bb hrel
  set P : Polynomial (RatFunc ℂ) :=
    (Polynomial.C a * Polynomial.X - Polynomial.C bb) * factorPoly (List.ofFn lamF) with hPdef
  have hCa : (Polynomial.C a : Polynomial (RatFunc ℂ))
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range :=
    ⟨Polynomial.C (shadowRadical hsh), by simp [hadef]⟩
  have hCb : (Polynomial.C bb : Polynomial (RatFunc ℂ))
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range :=
    ⟨Polynomial.C b₀, by simp [hbbdef]⟩
  have hXmem : (Polynomial.X : Polynomial (RatFunc ℂ))
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range := ⟨Polynomial.X, by simp⟩
  have hfacmem : factorPoly (List.ofFn lamF)
      ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range := by
    rw [hofn]; exact factorPoly_mem_range _
  obtain ⟨P₀, hP₀⟩ : P ∈ (Polynomial.mapRingHom (algebraMap ℂ[X] (RatFunc ℂ))).range :=
    Subring.mul_mem _ (Subring.sub_mem _ (Subring.mul_mem _ hCa hXmem) hCb) hfacmem
  have hcoeff : ∀ j, algebraMap ℂ[X] (RatFunc ℂ) (P₀.coeff j) = P.coeff j := by
    intro j
    rw [← hP₀]
    simp [Polynomial.coeff_map]
  refine ⟨fun j => P₀.coeff j, ?_, ?_⟩
  · refine hφinj ?_
    rw [hcoeff (r + 1), hPdef]
    have hlength : (List.ofFn lamF).length = r := List.length_ofFn
    have := coeff_linear_mul_factorPoly_top (List.ofFn lamF) a bb
    rw [hlength] at this
    rw [this, hadef]
  · have hfun : (fun j => algebraMap ℂ[X] (RatFunc ℂ) (P₀.coeff j)) = P.coeff := by
      funext j; exact hcoeff j
    rw [hfun]
    exact hann

/-- **Item 3, exact minimal leading degree.**  Every polynomial-coefficient annihilator of order
`r + 1` has leading coefficient of degree at least `deg rad(h)`, and that bound is attained. -/
theorem natDegree_shadowRadical_le_of_annihilates
    {M : Type*} [Field M] [Algebra (RatFunc ℂ) M] [Differential M]
    [DifferentialAlgebra (RatFunc ℂ) M]
    {r : ℕ} (lam : Fin r → ℂ) (hlam : Function.Injective lam) (hlam0 : ∀ i, lam i ≠ 0)
    (E : Fin r → M) (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′ = algebraMap (RatFunc ℂ) M (algebraMap ℂ (RatFunc ℂ) (lam i)) * E i)
    {q : RatFunc ℂ} (hq : q ≠ 0)
    (p : ℕ → ℂ[X]) (hp : p (r + 1) ≠ 0)
    (hann : linOp (fun j => algebraMap ℂ[X] (RatFunc ℂ) (p j)) (r + 1)
        (algebraMap (RatFunc ℂ) M q + ∑ i, E i) = 0) :
    (shadowRadical (shiftedDerivProd (List.ofFn lam) q)).natDegree ≤ (p (r + 1)).natDegree :=
  Polynomial.natDegree_le_of_dvd
    (shadowRadical_dvd_leadingCoeff lam hlam hlam0 E hE heig hq p hp hann) hp

end RatFuncSpecialization

end GaloisForLFunctions.LinDiffOp
