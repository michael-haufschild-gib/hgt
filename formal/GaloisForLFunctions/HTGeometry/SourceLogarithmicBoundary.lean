import GaloisForLFunctions.HTGeometry.AutomorphismFamilyOstrowski
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.HolderDifferenceBricks
import GaloisForLFunctions.HTGeometry.MeromorphicPoleOrbitBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

/-!
# Source-logarithmic boundary exactness

This module proves the exact single-observable multiplicative boundary theorem.  A multiplicative
primitive for an arbitrary family of compatible differential-field automorphisms is
differentially algebraic exactly when a nonzero finite differential character of its logarithmic
source increment is one simultaneous base coboundary in every source direction.  The source
family need not commute.
-/

open Polynomial
open scoped Differential
open Set

namespace GaloisForLFunctions

noncomputable section

/-- Differential algebraicity is closed under the algebraic logarithmic derivative `x'/x`. -/
theorem differentialAlgebraicOver_deriv_div_self
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero L] {x : L} (hx : DifferentialAlgebraicOver K x) :
    DifferentialAlgebraicOver K (x′ / x) := by
  simpa [div_eq_mul_inv] using HTGeometry.differentialAlgebraicOver_mul
    (HTGeometry.differentialAlgebraicOver_deriv hx)
    (HTGeometry.differentialAlgebraicOver_inv hx)

/-- An element is hypertranscendental exactly when its algebraic logarithmic derivative is. -/
theorem hypertranscendentalOver_deriv_div_self_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L] (x : L) :
    HypertranscendentalOver K (x′ / x) ↔ HypertranscendentalOver K x := by
  constructor
  · intro hell
    unfold HypertranscendentalOver at hell ⊢
    exact fun hx => hell (differentialAlgebraicOver_deriv_div_self hx)
  · intro hx
    have h := hypertranscendentalOver_rationalTensorJetObservable
      (y := x) (p := (1 : Polynomial K)) (r := Polynomial.X)
      one_ne_zero Polynomial.X_ne_zero (weight := (1 : ℤ)) one_ne_zero hx
    simpa [rationalTensorJetObservable, div_eq_mul_inv, mul_comm] using h

/-- A multiplicative source recurrence becomes an additive recurrence after logarithmic
differentiation. -/
theorem ringEquiv_deriv_div_self_of_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (sigma : L ≃+* L) (hderiv : ∀ y, sigma y′ = (sigma y)′)
    (x : L) (b : K) (hx : x ≠ 0) (hb : b ≠ 0)
    (hmul : sigma x = algebraMap K L b * x) :
    sigma (x′ / x) = x′ / x + algebraMap K L (b′ / b) := by
  rw [map_div₀, hderiv, hmul, Derivation.leibniz, deriv_algebraMap]
  simp only [map_div₀]
  field_simp [hx, hb]
  ring

/-- Absence of every simultaneous logarithmic-increment jet telescoper forces
hypertranscendence of the multiplicative primitive. -/
theorem automorphismFamily_hypertranscendental_of_no_logIncrement_jet_telescoping
    {I C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : L) (b : I → K) (hx : x ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hmul : ∀ i, sigma i x = algebraMap K L (b i) * x)
    (hnot : ∀ c : (Unit × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
      tau i k - k ≠
        Finsupp.linearCombination K
          (fun p ↦ differentialJet p.2 ((b i)′ / b i))
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) :
    HypertranscendentalOver K x := by
  let ell : L := x′ / x
  let omega : I → Unit → K := fun i _ => (b i)′ / b i
  have hshift : ∀ i u, sigma i ell =
      ell + algebraMap K L (omega i u) := by
    intro i u
    simpa [ell, omega] using
      ringEquiv_deriv_div_self_of_mul (sigma i) (hderiv i) x (b i)
        hx (hb i) (hmul i)
  have hDI : DifferentialIndependent K (fun _ : Unit => ell) :=
    automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
      tau sigma hcomp hderiv hCfixed hfixed
      (fun _ : Unit => ell) omega hshift (by
        intro c hc k
        simpa [omega] using hnot c hc k)
  have hell : HypertranscendentalOver K ell :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton K ell).mpr hDI
  exact (hypertranscendentalOver_deriv_div_self_iff x).mp hell

/-- Differential algebraicity of a multiplicative primitive produces a nonzero simultaneous
telescoper of the full jet of its logarithmic source increment. -/
theorem automorphismFamily_exists_logIncrement_jet_telescoping_of_differentialAlgebraic
    {I C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : L) (b : I → K) (hx : x ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hmul : ∀ i, sigma i x = algebraMap K L (b i) * x)
    (hDA : DifferentialAlgebraicOver K x) :
    ∃ c : (Unit × ℕ) →₀ C, c ≠ 0 ∧ ∃ k : K, ∀ i,
      tau i k - k =
        Finsupp.linearCombination K
          (fun p ↦ differentialJet p.2 ((b i)′ / b i))
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c) := by
  let ell : L := x′ / x
  let omega : I → Unit → K := fun i _ => (b i)′ / b i
  let ellJet : Unit × ℕ → L := fun p => differentialJet p.2 ell
  let omegaJet : I → Unit × ℕ → K :=
    fun i p => differentialJet p.2 (omega i p.1)
  have hshift : ∀ i u, sigma i ell =
      ell + algebraMap K L (omega i u) := by
    intro i u
    simpa [ell, omega] using
      ringEquiv_deriv_div_self_of_mul (sigma i) (hderiv i) x (b i)
        hx (hb i) (hmul i)
  have hshiftJet : ∀ i p, sigma i (ellJet p) =
      ellJet p + algebraMap K L (omegaJet i p) := by
    intro i p
    dsimp only [ellJet, omegaJet]
    rw [ringEquiv_differentialJet sigma hderiv, hshift i p.1]
    rw [differentialJet_additive,
      differentialJet_algebraMap_of_differentialAlgebra]
  have hdep : ¬ AlgebraicIndependent K ellJet := by
    exact differentialAlgebraicOver_deriv_div_self hDA
  obtain ⟨c, hc, k, hk⟩ :=
    automorphismFamily_exists_nonzero_constant_simultaneous_telescoping
      tau sigma hcomp hCfixed hfixed ellJet omegaJet hshiftJet hdep
  exact ⟨c, hc, k, by
    intro i
    simpa [omegaJet, omega] using hk i⟩

/-- A nonzero affine linear relation over the base obstructs algebraic independence. -/
theorem not_algebraicIndependent_of_finsupp_linearCombination_eq
    {κ C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    (x : κ → L) (c : κ →₀ C) (hc : c ≠ 0) (a : K)
    (hrel :
      Finsupp.linearCombination L x
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) = algebraMap K L a) :
    ¬ AlgebraicIndependent K x := by
  classical
  intro hAI
  let P : MvPolynomial κ K :=
    c.sum (fun j r => MvPolynomial.C (algebraMap C K r) * MvPolynomial.X j) -
      MvPolynomial.C a
  have hP : P ≠ 0 := by
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hc
    have hjmem : j ∈ c.support := Finsupp.mem_support_iff.mpr hj
    let e0 : κ → K := fun _ => 0
    let e1 : κ → K := fun i => if i = j then 1 else 0
    intro hzero
    have h0 := congrArg (MvPolynomial.eval e0) hzero
    have h1 := congrArg (MvPolynomial.eval e1) hzero
    rw [map_zero] at h0 h1
    have h0' : -a = 0 := by
      simpa [P, e0, Finsupp.sum] using h0
    have h1' : algebraMap C K (c j) - a = 0 := by
      simpa [P, e1, Finsupp.sum, hj, hjmem] using h1
    have hjK : algebraMap C K (c j) ≠ 0 := by
      simpa using (algebraMap C K).injective.ne hj
    apply hjK
    linear_combination h1' - h0'
  apply hP
  apply hAI.eq_zero_of_aeval_eq_zero
  have hrel' := hrel
  rw [Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (fun _ => by simp)] at hrel'
  simpa [P, Finsupp.sum, IsScalarTower.algebraMap_apply C K L]
    using sub_eq_zero.mpr hrel'

/-- A nonzero affine differential-character relation on the jet family makes the underlying
element differentially algebraic. -/
theorem differentialAlgebraicOver_of_finsupp_jet_linear_eq
    {C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
    [Differential L]
    (x : L) (c : (Unit × ℕ) →₀ C) (hc : c ≠ 0) (a : K)
    (hrel :
      Finsupp.linearCombination L
        (fun p ↦ differentialJet p.2 x)
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) = algebraMap K L a) :
    DifferentialAlgebraicOver K x := by
  unfold DifferentialAlgebraicOver DifferentialIndependent
  exact not_algebraicIndependent_of_finsupp_linearCombination_eq
    (fun p : Unit × ℕ ↦ differentialJet p.2 x) c hc a hrel

/-- A simultaneous logarithmic-increment jet telescoper forces differential algebraicity of the
multiplicative primitive. -/
theorem automorphismFamily_differentialAlgebraic_of_logIncrement_jet_telescoping
    {I C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : L) (b : I → K) (hx : x ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hmul : ∀ i, sigma i x = algebraMap K L (b i) * x)
    (c : (Unit × ℕ) →₀ C) (hc : c ≠ 0) (k : K)
    (htel : ∀ i,
      tau i k - k =
        Finsupp.linearCombination K
          (fun p ↦ differentialJet p.2 ((b i)′ / b i))
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) :
    DifferentialAlgebraicOver K x := by
  let ell : L := x′ / x
  let omega : I → Unit → K := fun i _ => (b i)′ / b i
  let ellJet : Unit × ℕ → L := fun p => differentialJet p.2 ell
  let omegaJet : I → Unit × ℕ → K :=
    fun i p => differentialJet p.2 (omega i p.1)
  let cL : (Unit × ℕ) →₀ L :=
    Finsupp.mapRange (algebraMap C L) (map_zero (algebraMap C L)) c
  let cK : (Unit × ℕ) →₀ K :=
    Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c
  let g : L := Finsupp.linearCombination L ellJet cL
  have hshift : ∀ i u, sigma i ell =
      ell + algebraMap K L (omega i u) := by
    intro i u
    simpa [ell, omega] using
      ringEquiv_deriv_div_self_of_mul (sigma i) (hderiv i) x (b i)
        hx (hb i) (hmul i)
  have hshiftJet : ∀ i p, sigma i (ellJet p) =
      ellJet p + algebraMap K L (omegaJet i p) := by
    intro i p
    dsimp only [ellJet, omegaJet]
    rw [ringEquiv_differentialJet sigma hderiv, hshift i p.1]
    rw [differentialJet_additive,
      differentialJet_algebraMap_of_differentialAlgebra]
  have hshiftg : ∀ i, sigma i g = g + algebraMap K L
      (Finsupp.linearCombination K (omegaJet i) cK) := by
    intro i
    dsimp only [g]
    rw [ringEquiv_linearCombination]
    have hcmap :
        Finsupp.mapRange (sigma i) (map_zero (sigma i)) cL = cL := by
      ext j
      simp [cL, hCfixed]
    rw [hcmap]
    simp_rw [hshiftJet i]
    rw [finsupp_linearCombination_add_family]
    rw [algebraMap_constant_finsupp_linearCombination]
  have hzfix : ∀ i,
      sigma i (g - algebraMap K L k) = g - algebraMap K L k := by
    intro i
    rw [map_sub, hshiftg i, hcomp]
    have htel' : tau i k - k =
        Finsupp.linearCombination K (omegaJet i) cK := by
      simpa [omegaJet, omega, cK] using htel i
    rw [← htel', map_sub]
    abel
  obtain ⟨c0, hc0⟩ := hfixed (g - algebraMap K L k) hzfix
  let a : K := k + algebraMap C K c0
  have hgbase : g = algebraMap K L a := by
    calc
      g = algebraMap K L k + algebraMap C L c0 := by rw [hc0]; abel
      _ = algebraMap K L a := by
        simp [a, IsScalarTower.algebraMap_apply C K L]
  have hellDA : DifferentialAlgebraicOver K ell :=
    differentialAlgebraicOver_of_finsupp_jet_linear_eq ell c hc a (by
      simpa [g, ellJet, cL] using hgbase)
  by_contra hxDA
  have hxHT : HypertranscendentalOver K x := hxDA
  have hellHT : HypertranscendentalOver K ell :=
    (hypertranscendentalOver_deriv_div_self_iff x).mpr hxHT
  exact hellHT hellDA

/-- **Exact source-logarithmic boundary criterion.**  A nonzero multiplicative primitive under an
arbitrary, possibly noncommuting family of compatible differential-field automorphisms is
differentially algebraic exactly when one nonzero finite differential character of the
logarithmic source increments is a simultaneous base coboundary. -/
theorem automorphismFamily_differentialAlgebraic_iff_exists_logIncrement_jet_telescoping
    {I C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : L) (b : I → K) (hx : x ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hmul : ∀ i, sigma i x = algebraMap K L (b i) * x) :
    DifferentialAlgebraicOver K x ↔
      ∃ c : (Unit × ℕ) →₀ C, c ≠ 0 ∧ ∃ k : K, ∀ i,
        tau i k - k =
          Finsupp.linearCombination K
            (fun p ↦ differentialJet p.2 ((b i)′ / b i))
            (Finsupp.mapRange (algebraMap C K)
              (map_zero (algebraMap C K)) c) := by
  constructor
  · exact automorphismFamily_exists_logIncrement_jet_telescoping_of_differentialAlgebraic
      tau sigma hcomp hderiv hCfixed hfixed x b hx hb hmul
  · rintro ⟨c, hc, k, htel⟩
    exact automorphismFamily_differentialAlgebraic_of_logIncrement_jet_telescoping
      tau sigma hcomp hderiv hCfixed hfixed x b hx hb hmul c hc k htel

/-- **Exact finite-resolution boundary matroid.**  For any selected packet of logarithmic jet
orders, algebraic independence of the bulk packet is equivalent to absence of a simultaneous
source coboundary supported on exactly that packet.  Thus the entire algebraic matroid of the
logarithmic clock tower, not only its eventual differential rank, is represented by the source
boundary derivatives. -/
theorem automorphismFamily_logarithmicJet_algebraicIndependent_iff
    {I κ C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : L) (b : I → K) (hx : x ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hmul : ∀ i, sigma i x = algebraMap K L (b i) * x)
    (order : κ → ℕ) :
    AlgebraicIndependent K
        (fun j => differentialJet (order j) (x′ / x)) ↔
      ∀ c : κ →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
        tau i k - k ≠
          Finsupp.linearCombination K
            (fun j => differentialJet (order j) ((b i)′ / b i))
            (Finsupp.mapRange (algebraMap C K)
              (map_zero (algebraMap C K)) c) := by
  let ell : L := x′ / x
  let obs : κ → L := fun j => differentialJet (order j) ell
  let inc : I → κ → K :=
    fun i j => differentialJet (order j) ((b i)′ / b i)
  have hshiftEll : ∀ i, sigma i ell =
      ell + algebraMap K L ((b i)′ / b i) := by
    intro i
    simpa [ell] using
      ringEquiv_deriv_div_self_of_mul (sigma i) (hderiv i) x (b i)
        hx (hb i) (hmul i)
  have hshiftObs : ∀ i j, sigma i (obs j) =
      obs j + algebraMap K L (inc i j) := by
    intro i j
    dsimp only [obs, inc]
    rw [ringEquiv_differentialJet sigma hderiv, hshiftEll i]
    rw [differentialJet_additive,
      differentialJet_algebraMap_of_differentialAlgebra]
  constructor
  · intro hAI c hc k
    by_contra hnone
    have htel : ∀ i,
        tau i k - k =
          Finsupp.linearCombination K (inc i)
            (Finsupp.mapRange (algebraMap C K)
              (map_zero (algebraMap C K)) c) := by
      intro i
      by_contra hi
      apply hnone
      exact ⟨i, by simpa [inc] using hi⟩
    let cL : κ →₀ L :=
      Finsupp.mapRange (algebraMap C L) (map_zero (algebraMap C L)) c
    let cK : κ →₀ K :=
      Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c
    let g : L := Finsupp.linearCombination L obs cL
    have hshiftg : ∀ i, sigma i g = g + algebraMap K L
        (Finsupp.linearCombination K (inc i) cK) := by
      intro i
      dsimp only [g]
      rw [ringEquiv_linearCombination]
      have hcmap :
          Finsupp.mapRange (sigma i) (map_zero (sigma i)) cL = cL := by
        ext j
        simp [cL, hCfixed]
      rw [hcmap]
      simp_rw [hshiftObs i]
      rw [finsupp_linearCombination_add_family]
      rw [algebraMap_constant_finsupp_linearCombination]
    have hzfix : ∀ i,
        sigma i (g - algebraMap K L k) = g - algebraMap K L k := by
      intro i
      rw [map_sub, hshiftg i, hcomp]
      have htel' : tau i k - k =
          Finsupp.linearCombination K (inc i) cK := by
        simpa [cK] using htel i
      rw [← htel', map_sub]
      abel
    obtain ⟨c0, hc0⟩ := hfixed (g - algebraMap K L k) hzfix
    let a : K := k + algebraMap C K c0
    have hgbase : g = algebraMap K L a := by
      calc
        g = algebraMap K L k + algebraMap C L c0 := by rw [hc0]; abel
        _ = algebraMap K L a := by
          simp [a, IsScalarTower.algebraMap_apply C K L]
    have hdep : ¬ AlgebraicIndependent K obs :=
      not_algebraicIndependent_of_finsupp_linearCombination_eq
        obs c hc a (by simpa [g, cL] using hgbase)
    apply hdep
    simpa [obs, ell] using hAI
  · intro hnot
    apply automorphismFamily_algebraicIndependent_of_no_constant_simultaneous_telescoping
      tau sigma hcomp hCfixed hfixed obs inc hshiftObs
    intro c hc k
    simpa [inc] using hnot c hc k

/-- **Twisted affine scalar-boundary obstruction.**  If the simultaneous boundary class of `h`
is non-torsion, then the class of the twisted increment `tau i h + h` is also non-torsion.  The
proof converts any telescoper of the twisted increment into one for `h` by the base gauge
`(k - P(D)h) / 2`.  This is the formal algebraic core of the `-1` affine counterexample: scalar
boundary capacity survives even when the affine observable itself is the base element `h`. -/
theorem automorphismFamily_no_telescoping_tau_add_self
    {I C K : Type*} [Field C] [Field K] [Algebra C K]
    [Differential K] [CharZero K]
    (tau : I → K ≃+* K)
    (hderiv : ∀ i y, tau i y′ = (tau i y)′)
    (hCfixed : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (h : K)
    (hnot : ∀ c : (Unit × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
      tau i k - k ≠
        Finsupp.linearCombination K
          (fun p ↦ differentialJet p.2 h)
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) :
    ∀ c : (Unit × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
      tau i k - k ≠
        Finsupp.linearCombination K
          (fun p ↦ differentialJet p.2 (tau i h + h))
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c) := by
  intro c hc k
  by_contra hall
  push Not at hall
  let cK : (Unit × ℕ) →₀ K :=
    Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c
  let pval : K := Finsupp.linearCombination K
    (fun p : Unit × ℕ => differentialJet p.2 h) cK
  let k' : K := (k - pval) / 2
  obtain ⟨i, hi⟩ := hnot c hc k'
  apply hi
  have hpmap : tau i pval =
      Finsupp.linearCombination K
        (fun p : Unit × ℕ => differentialJet p.2 (tau i h)) cK := by
    dsimp only [pval]
    rw [ringEquiv_linearCombination]
    have hcmap : Finsupp.mapRange (tau i) (map_zero (tau i)) cK = cK := by
      ext j
      simp [cK, hCfixed]
    rw [hcmap]
    apply congrArg (fun f : Unit × ℕ → K =>
      Finsupp.linearCombination K f cK)
    funext p
    exact ringEquiv_differentialJet tau hderiv i p.2 h
  have homega :
      Finsupp.linearCombination K
          (fun p : Unit × ℕ => differentialJet p.2 (tau i h + h)) cK =
        tau i pval + pval := by
    simp_rw [differentialJet_additive]
    rw [finsupp_linearCombination_add_family, ← hpmap]
  have halli : tau i k - k = tau i pval + pval := by
    simpa [cK, homega] using hall i
  dsimp only [k']
  rw [map_div₀, map_sub]
  have htwo : tau i (2 : K) = 2 := map_ofNat (tau i) 2
  rw [htwo]
  field_simp
  linear_combination halli

/-- The coefficient-aware affine boundary map `u ↦ (τᵢ(u) - Aᵢu)ᵢ`.  Its additive quotient is
the correct extension-class space for a fixed one-dimensional semilinear coefficient system. -/
def twistedAffineBoundaryMap
    {I K : Type*} [Ring K] (tau : I → K ≃+* K) (A : I → K) :
    K →+ (I → K) where
  toFun u i := tau i u - A i * u
  map_zero' := by
    ext i
    simp
  map_add' u v := by
    ext i
    simp [mul_add]
    abel

/-- Coboundaries for the fixed affine coefficient system. -/
def twistedAffineBoundarySubgroup
    {I K : Type*} [Ring K] (tau : I → K ≃+* K) (A : I → K) :
    AddSubgroup (I → K) :=
  (twistedAffineBoundaryMap tau A).range

/-- The coefficient-aware boundary class of an affine increment family. -/
def twistedAffineBoundaryClass
    {I K : Type*} [Ring K] (tau : I → K ≃+* K) (A omega : I → K) :
    (I → K) ⧸ twistedAffineBoundarySubgroup tau A :=
  QuotientAddGroup.mk omega

/-- In the `Aᵢ = -1` local system, the increment `τᵢ(h)+h` is the literal coboundary of `h`.
Thus its coefficient-aware boundary class is zero even when its ordinary translation-boundary
class is non-torsion. -/
@[simp]
theorem twistedAffineBoundaryClass_tau_add_self_eq_zero
    {I K : Type*} [Ring K] (tau : I → K ≃+* K) (h : K) :
    twistedAffineBoundaryClass tau (fun _ => -1) (fun i => tau i h + h) = 0 := by
  rw [twistedAffineBoundaryClass, QuotientAddGroup.eq_zero_iff]
  exact ⟨h, by
    ext i
    simp [twistedAffineBoundaryMap]⟩

/-- The base observable realizes the twisted affine law identically. -/
theorem twistedAffine_baseObservable_identity
    {I K : Type*} [Ring K] (tau : I → K ≃+* K) (h : K) (i : I) :
    tau i h = -h + (tau i h + h) := by
  abel

/-- The transformed linear coefficient `-τ(B)/B` is trivial exactly when `B` is a common
anti-invariant unit.  This is the precise simultaneous gauge obstruction. -/
theorem twistedAffine_gaugeLinearPart_eq_one_iff
    {K : Type*} [Field K] (x B : K) (hB : B ≠ 0) :
    -x / B = 1 ↔ x = -B := by
  constructor
  · intro h
    have hmul : -x = 1 * B := (div_eq_iff hB).mp h
    linear_combination -hmul
  · intro h
    rw [h]
    simp [hB]

/-- A gauge trivialization transports the twisted coboundary to an ordinary translation
coboundary.  Under `τᵢ(B) Aᵢ = B`, the coordinate scaling is the nonzero factor `τᵢ(B)`. -/
theorem twistedAffineBoundary_gauge_transport
    {I K : Type*} [Field K] (tau : I → K ≃+* K) (A : I → K)
    (B u : K) (htriv : ∀ i, tau i B * A i = B) (i : I) :
    tau i (B * u) - B * u = tau i B * (tau i u - A i * u) := by
  have hBu : B * u = (tau i B * A i) * u := congrArg (· * u) (htriv i).symm
  rw [map_mul, hBu]
  ring

/-- No nonzero reduced rational quotient can transform by the sign character under unit shift.
Squaring would make the quotient shift-periodic, and the existing periodic-quotient theorem then
forces numerator and denominator to be constant, contradicting anti-periodicity. -/
theorem no_nonzero_shiftAntiInvariant_quotient
    {p q : Polynomial ℂ} (hco : IsCoprime p q) (hp : p ≠ 0) (hq : q ≠ 0)
    (hanti : p.comp (Polynomial.X + Polynomial.C 1) * q =
      -(p * q.comp (Polynomial.X + Polynomial.C 1))) : False := by
  let S : Polynomial ℂ := Polynomial.X + Polynomial.C 1
  have hantiS : p.comp S * q = -(p * q.comp S) := by
    simpa [S] using hanti
  have hsquare : (p ^ 2).comp S * q ^ 2 = p ^ 2 * (q ^ 2).comp S := by
    calc
      (p ^ 2).comp S * q ^ 2 = (p.comp S) ^ 2 * q ^ 2 := by
        rw [Polynomial.pow_comp]
      _ = (p.comp S * q) ^ 2 := by ring
      _ = (-(p * q.comp S)) ^ 2 := congrArg (· ^ 2) hantiS
      _ = (p * q.comp S) ^ 2 := by ring
      _ = p ^ 2 * (q.comp S) ^ 2 := by ring
      _ = p ^ 2 * (q ^ 2).comp S := by rw [Polynomial.pow_comp]
  have hcopow : IsCoprime (p ^ 2) (q ^ 2) := hco.pow
  obtain ⟨a, b, hpconst, hqconst⟩ :=
    shift_periodic_quotient_constant hcopow (by simpa [S] using hsquare)
  have hpdeg : p.natDegree = 0 := by
    have hdeg := congrArg Polynomial.natDegree hpconst
    rw [Polynomial.natDegree_pow p 2] at hdeg
    simp at hdeg
    omega
  have hqdeg : q.natDegree = 0 := by
    have hdeg := congrArg Polynomial.natDegree hqconst
    rw [Polynomial.natDegree_pow q 2] at hdeg
    simp at hdeg
    omega
  obtain ⟨c, hpc⟩ := Polynomial.natDegree_eq_zero.mp hpdeg
  obtain ⟨d, hqd⟩ := Polynomial.natDegree_eq_zero.mp hqdeg
  have hc : c ≠ 0 := by
    intro hc0
    apply hp
    rw [← hpc, hc0]
    simp
  have hd : d ≠ 0 := by
    intro hd0
    apply hq
    rw [← hqd, hd0]
    simp
  rw [← hpc, ← hqd] at hanti
  have hconst := congrArg (fun r : Polynomial ℂ => r.coeff 0) hanti
  simp at hconst
  have hcd0 : c * d = 0 := by
    have htwo : (2 : ℂ) * (c * d) = 0 := by
      linear_combination hconst
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact (mul_ne_zero hc hd) hcd0

/-- Every nonzero constant-coefficient differential operator applied to `1/z` has one pole on the
integer translation orbit, so it cannot be a shift coboundary of any meromorphic function with
finite pole support on that orbit.  Rational functions are a special case. -/
theorem no_finitePole_solution_constantCoeffDifferentialOperator_inv
    (L : Polynomial ℂ) (hL : L ≠ 0) (g : ℂ → ℂ)
    (hg : ∀ n : ℤ, MeromorphicAt g (additiveOrbitPoint 0 1 n))
    (hfinite : (poleIndexSet g 0 1).Finite)
    (hshift : ∀ z : ℂ,
      constantCoeffDifferentialOperator L (fun w : ℂ => w⁻¹) z = g (z + 1) - g z) : False := by
  apply shiftCoboundary_not_singleton_poleOrbit g
    (constantCoeffDifferentialOperator L (fun w : ℂ => w⁻¹)) 0 1 hg hshift hfinite
  · have hinvMero : MeromorphicAt (fun w : ℂ => w⁻¹) 0 := by fun_prop
    have hinvOrder : meromorphicOrderAt (fun w : ℂ => w⁻¹) 0 =
        ((-1 : ℤ) : WithTop ℤ) := by
      simpa [zpow_neg_one, sub_zero] using
        (meromorphicOrderAt_zpow_id_sub_const (𝕜 := ℂ) (x := 0) (n := (-1 : ℤ)))
    rw [meromorphicOrderAt_constantCoeffDifferentialOperator_of_simplePole
      hL hinvMero hinvOrder]
    exact_mod_cast (show -((L.natDegree + 1 : ℕ) : ℤ) < 0 by omega)
  · intro n hn
    by_contra hn0
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hinvAnalytic : AnalyticAt ℂ (fun w : ℂ => w⁻¹) (n : ℂ) :=
      analyticAt_id.inv hnC
    have hopAnalytic := analyticAt_constantCoeffDifferentialOperator (L := L) hinvAnalytic
    rw [show additiveOrbitPoint 0 1 n = (n : ℂ) by simp [additiveOrbitPoint]] at hn
    exact (not_lt_of_ge hopAnalytic.meromorphicOrderAt_nonneg) hn

/-- **Exact arbitrary-family differential Ostrowski criterion.**  Differential independence of
an additive primitive family is equivalent to the absence of every nonzero finite differential
character whose complete source-increment family is one simultaneous base coboundary. -/
theorem automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
    {I κ C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (x : κ → L) (b : I → κ → K)
    (hshift : ∀ i j, sigma i (x j) =
      x j + algebraMap K L (b i j)) :
    DifferentialIndependent K x ↔
      ∀ c : (κ × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
        tau i k - k ≠
          Finsupp.linearCombination K
            (fun p ↦ differentialJet p.2 (b i p.1))
            (Finsupp.mapRange (algebraMap C K)
              (map_zero (algebraMap C K)) c) := by
  let xJet : κ × ℕ → L := fun p ↦ differentialJet p.2 (x p.1)
  let bJet : I → κ × ℕ → K :=
    fun i p ↦ differentialJet p.2 (b i p.1)
  have hshiftJet : ∀ i p, sigma i (xJet p) =
      xJet p + algebraMap K L (bJet i p) := by
    intro i p
    dsimp only [xJet, bJet]
    rw [ringEquiv_differentialJet sigma hderiv, hshift]
    rw [differentialJet_additive,
      differentialJet_algebraMap_of_differentialAlgebra]
  constructor
  · intro hDI c hc k
    by_contra hnone
    push Not at hnone
    let cL : (κ × ℕ) →₀ L :=
      Finsupp.mapRange (algebraMap C L) (map_zero (algebraMap C L)) c
    let cK : (κ × ℕ) →₀ K :=
      Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c
    let g : L := Finsupp.linearCombination L xJet cL
    have hshiftg : ∀ i, sigma i g = g + algebraMap K L
        (Finsupp.linearCombination K (bJet i) cK) := by
      intro i
      dsimp only [g]
      rw [ringEquiv_linearCombination]
      have hcmap :
          Finsupp.mapRange (sigma i) (map_zero (sigma i)) cL = cL := by
        ext j
        simp [cL, hCfixed]
      rw [hcmap]
      simp_rw [hshiftJet i]
      rw [finsupp_linearCombination_add_family]
      rw [algebraMap_constant_finsupp_linearCombination]
    have hzfix : ∀ i,
        sigma i (g - algebraMap K L k) = g - algebraMap K L k := by
      intro i
      rw [map_sub, hshiftg i, hcomp]
      have htel : tau i k - k =
          Finsupp.linearCombination K (bJet i) cK := by
        simpa [bJet, cK] using hnone i
      rw [← htel, map_sub]
      abel
    obtain ⟨c0, hc0⟩ := hfixed (g - algebraMap K L k) hzfix
    let a : K := k + algebraMap C K c0
    have hgbase : g = algebraMap K L a := by
      calc
        g = algebraMap K L k + algebraMap C L c0 := by rw [hc0]; abel
        _ = algebraMap K L a := by
          simp [a, IsScalarTower.algebraMap_apply C K L]
    have hdep : ¬ AlgebraicIndependent K xJet :=
      not_algebraicIndependent_of_finsupp_linearCombination_eq
        xJet c hc a (by simpa [g, cL] using hgbase)
    apply hdep
    simpa [DifferentialIndependent, xJet] using hDI
  · exact automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
      tau sigma hcomp hderiv hCfixed hfixed x b hshift

/-- **Exact split-source boundary for the linearized mixed family.**  Additive primitives and
logarithmic derivatives of nonzero multiplicative primitives form one differentially independent
family exactly when no nonzero finite differential character of their combined source increments
is a simultaneous base coboundary.  The source automorphisms need not commute. -/
theorem automorphismFamily_mixedLinearized_differentialIndependent_iff
    {I A B C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K]
    (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) =
      algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C L c = z)
    (u : A → L) (x : B → L)
    (p : I → A → K) (q : I → B → K)
    (hx : ∀ b, x b ≠ 0) (hq : ∀ i b, q i b ≠ 0)
    (hadd : ∀ i a, sigma i (u a) =
      u a + algebraMap K L (p i a))
    (hmul : ∀ i b, sigma i (x b) =
      algebraMap K L (q i b) * x b) :
    DifferentialIndependent K
        (Sum.elim u (fun b ↦ (x b)′ / x b)) ↔
      ∀ c : ((A ⊕ B) × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
        tau i k - k ≠
          Finsupp.linearCombination K
            (fun r ↦ differentialJet r.2
              (Sum.elim (p i) (fun b ↦ (q i b)′ / q i b) r.1))
            (Finsupp.mapRange (algebraMap C K)
              (map_zero (algebraMap C K)) c) := by
  let z : A ⊕ B → L := Sum.elim u (fun b ↦ (x b)′ / x b)
  let omega : I → A ⊕ B → K :=
    fun i ↦ Sum.elim (p i) (fun b ↦ (q i b)′ / q i b)
  have hshift : ∀ i j, sigma i (z j) =
      z j + algebraMap K L (omega i j) := by
    intro i j
    cases j with
    | inl a => simpa [z, omega] using hadd i a
    | inr b =>
        simpa [z, omega] using
          ringEquiv_deriv_div_self_of_mul (sigma i) (hderiv i)
            (x b) (q i b) (hx b) (hq i b) (hmul i b)
  simpa only [z, omega] using
    (automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
      tau sigma hcomp hderiv hCfixed hfixed z omega hshift)

end

end GaloisForLFunctions
