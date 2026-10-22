import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalPuiseuxRoot
import GaloisForLFunctions.HTGeometry.FirstOrderStateEvaluation

/-!
# Terminal Puiseux embedding of the first-order state field

Let `K̄` be the algebraic closure of the Laurent field `ℂ((t))` and consider the iterated Laurent
field `K̄((s))`. This module shows that the monomials `U = t^(e_U)` and `V = s^(e_V)` with nonzero
exponents are algebraically independent over `ℂ` inside `K̄((s))`. Hence the clock/value state
ring `ℂ[U, V]` embeds into `K̄((s))`, and the evaluation extends to the rational state field
`ℂ(U, V)`. Applied to the two-stage Newton–Puiseux root attached to the Wiman initial data of an
entire function satisfying an irreducible first-order algebraic differential equation
`P(z, f, f') = 0`, it exhibits that root as a root of `P` viewed as a polynomial in the derivative
coordinate over `ℂ(U, V)`. Two field-theoretic lemmas about lifting `K(x)` along a root of the
minimal polynomial are included.

## Main results

- `polynomial_eval₂_laurent_single_ne_zero`: a nonzero polynomial over a field `K` does not vanish
  at a Laurent monomial `t^e` with `e ≠ 0`.
- `firstOrderTerminalStateRingEval_injective`: evaluation `ℂ[U][V] → K̄((s))` at
  `U = t^(e_U)`, `V = s^(e_V)` with `e_U, e_V ≠ 0` is injective.
- `algebraicIndependent_firstOrderTerminalState`: these clock and value coordinates are
  algebraically independent over `ℂ`.
- `firstOrderStatePolynomialEval_terminal_injective`: state evaluation at the terminal jet
  `(U, V, W)` is injective, for any `W`.
- `exists_entireFirstOrderWiman_rationalDerivativePuiseuxRoot`: for Wiman initial data of `f`
  there are covers `N, q`, slope data `M, a` with `slope = (M - a) / q`, and a terminal power
  series `z` such that `W = s^(-R) z` is a root of the derivative polynomial of `P` over the
  rational state field embedded via `U = t^(-N q)`, `V = s^(-R)`.
- `exists_adjoinSimple_algHom_of_minpoly_root`: for `x` integral over `K` and `y` a root of the
  minimal polynomial of `x`, there is a `K`-algebra map `K(x) → M` sending `x` to `y`.
- `minpoly_isRoot_of_associated_mapped_isRoot`: a root of a polynomial associated to the minimal
  polynomial is a root of the minimal polynomial.

## Hypotheses

The embedding results are unconditional apart from nonzero exponents `e_U, e_V ≠ 0`. The Puiseux
root theorem takes as argument a structure `EntireFirstOrderWimanInitialData f`, which bundles an
irreducible relation `P(z, f(z), f'(z)) = 0` holding for all `z` together with exact Newton-edge
data; such data exist for every transcendental entire `f` satisfying a first-order algebraic
differential equation (`exists_entireFirstOrderWimanInitialData`). The minimal-polynomial lemmas
assume integrality of `x` and the stated root conditions.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Polynomial PowerSeries

noncomputable section

private theorem coeff_laurent_finset_sum_single
    {K : Type} [Field K] (s : Finset ℕ) (f : ℕ → ℤ) (g : ℕ → K) (w : ℤ) :
    (∑ n ∈ s, HahnSeries.single (f n) (g n) : LaurentSeries K).coeff w =
      ∑ n ∈ s, if f n = w then g n else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn, Finset.sum_insert hn, HahnSeries.coeff_add, ih]
      congr 1
      by_cases h : f n = w
      · subst h
        simp
      · simp [h, Ne.symm h]

private theorem algebraMap_laurent_eq_single
    {K : Type} [Field K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single (0 : ℤ) c := by
  change HahnSeries.ofPowerSeries ℤ K (PowerSeries.C c) =
    HahnSeries.single (0 : ℤ) c
  rw [HahnSeries.ofPowerSeries_C]
  exact HahnSeries.C_apply c

private theorem laurent_single_one_pow
    {K : Type} [Field K] (e : ℤ) (n : ℕ) :
    (HahnSeries.single e (1 : K)) ^ n =
      HahnSeries.single ((n : ℤ) * e) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single]
      congr 1
      · push_cast
        ring_nf
      · simp

/-- A nonzero polynomial `P` over a field `K` does not vanish at the Laurent monomial `t^e` when
`e ≠ 0`: its leading coefficient survives at exponent `deg P · e`. -/
theorem polynomial_eval₂_laurent_single_ne_zero
    {K : Type} [Field K] (P : Polynomial K) (hP : P ≠ 0)
    (e : ℤ) (he : e ≠ 0) :
    P.eval₂ (algebraMap K (LaurentSeries K))
      (HahnSeries.single e (1 : K)) ≠ 0 := by
  intro hzero
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hzero
  simp_rw [algebraMap_laurent_eq_single, laurent_single_one_pow,
    HahnSeries.single_mul_single, zero_add, mul_one] at hzero
  have hcoeff := congrArg
    (fun h : LaurentSeries K => h.coeff (((P.natDegree : ℕ) : ℤ) * e)) hzero
  rw [coeff_laurent_finset_sum_single, HahnSeries.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single_of_mem P.natDegree
    (Polynomial.natDegree_mem_support_of_nonzero hP)] at hcoeff
  · rw [if_pos rfl, Polynomial.coeff_natDegree] at hcoeff
    exact (Polynomial.leadingCoeff_ne_zero.mpr hP) hcoeff
  · intro n hn hne
    rw [if_neg]
    intro heq
    apply hne
    exact Int.ofNat_injective (mul_right_cancel₀ he heq)

/-- Evaluation `ℂ[U] → K̄` at a Laurent series `U`, where `K̄` is the algebraic closure of
`ℂ((t))`. -/
noncomputable def firstOrderTerminalInnerStateEval
    (U : LaurentSeries ℂ) : Polynomial ℂ →+* FirstOrderTerminalCoefficientField :=
  (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField).comp
    (Polynomial.eval₂RingHom (algebraMap ℂ (LaurentSeries ℂ)) U)

/-- Two-step evaluation `ℂ[U][V] → K̄((s))`: inner coefficients at `U ∈ ℂ((t))`, outer variable at
`V ∈ K̄((s))`. -/
noncomputable def firstOrderTerminalStateRingEval
    (U : LaurentSeries ℂ) (V : FirstOrderTerminalLaurentField) :
    Polynomial (Polynomial ℂ) →+* FirstOrderTerminalLaurentField :=
  (Polynomial.eval₂RingHom
    (algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField) V).comp
      (Polynomial.mapRingHom (firstOrderTerminalInnerStateEval U))

/-- A nonzero `A ∈ ℂ[U]` does not vanish at `U = t^e` with `e ≠ 0`. -/
theorem firstOrderTerminalInnerStateEval_ne_zero
    (A : Polynomial ℂ) (hA : A ≠ 0) (e : ℤ) (he : e ≠ 0) :
    firstOrderTerminalInnerStateEval (HahnSeries.single e (1 : ℂ)) A ≠ 0 := by
  change algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
    (A.eval₂ (algebraMap ℂ (LaurentSeries ℂ))
      (HahnSeries.single e (1 : ℂ))) ≠ 0
  exact (map_ne_zero
    (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField)).mpr
      (polynomial_eval₂_laurent_single_ne_zero A hA e he)

/-- A nonzero `P ∈ ℂ[U][V]` does not vanish at `U = t^(e_U)`, `V = s^(e_V)` when both exponents are
nonzero. -/
theorem firstOrderTerminalStateRingEval_ne_zero
    (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (eU eV : ℤ) (heU : eU ≠ 0) (heV : eV ≠ 0) :
    firstOrderTerminalStateRingEval
      (HahnSeries.single eU (1 : ℂ))
      (HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField)) P ≠ 0 := by
  let g : Polynomial ℂ →+* FirstOrderTerminalCoefficientField :=
    firstOrderTerminalInnerStateEval (HahnSeries.single eU (1 : ℂ))
  have hg : Function.Injective g := by
    intro A B hAB
    by_contra hne
    have hsub : A - B ≠ 0 := sub_ne_zero.mpr hne
    have hmapzero : g (A - B) = 0 := by rw [map_sub, hAB, sub_self]
    exact firstOrderTerminalInnerStateEval_ne_zero (A - B) hsub eU heU hmapzero
  have hPmap : P.map g ≠ 0 := by
    intro hzero
    apply hP
    apply Polynomial.map_injective g hg
    simpa using hzero
  change (P.map g).eval₂
    (algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField)
      (HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField)) ≠ 0
  exact polynomial_eval₂_laurent_single_ne_zero (P.map g) hPmap eV heV

/-- Evaluation of `ℂ[U][V]` at `U = t^(e_U)`, `V = s^(e_V)` with nonzero exponents is injective. -/
theorem firstOrderTerminalStateRingEval_injective
    (eU eV : ℤ) (heU : eU ≠ 0) (heV : eV ≠ 0) :
    Function.Injective (firstOrderTerminalStateRingEval
      (HahnSeries.single eU (1 : ℂ))
      (HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField))) := by
  intro P Q hPQ
  by_contra hne
  have hsub : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hmapzero : firstOrderTerminalStateRingEval
      (HahnSeries.single eU (1 : ℂ))
      (HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField)) (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  exact firstOrderTerminalStateRingEval_ne_zero (P - Q) hsub eU eV heU heV hmapzero

/-- The terminal jet with its clock and value entries swapped: `(V, U, W)` instead of
`(U, V, W)`. -/
noncomputable def firstOrderTerminalSwappedJet
    (U : LaurentSeries ℂ) (V W : FirstOrderTerminalLaurentField) :
    Fin 3 → FirstOrderTerminalLaurentField :=
  ![V,
    algebraMap FirstOrderTerminalCoefficientField FirstOrderTerminalLaurentField
      (algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField U),
    W]

theorem firstOrderStatePolynomialEquiv_X_zero : firstOrderStatePolynomialEquiv
    (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)})) =
      Polynomial.X := by
  simp [firstOrderStatePolynomialEquiv, firstOrderStateIndexEquiv]
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

theorem firstOrderStatePolynomialEquiv_X_one : firstOrderStatePolynomialEquiv
    (MvPolynomial.X (⟨1, by decide⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)})) =
      Polynomial.C Polynomial.X := by
  simp [firstOrderStatePolynomialEquiv, firstOrderStateIndexEquiv]
  change Polynomial.map _
      ((MvPolynomial.finSuccEquiv ℂ 1)
        (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.finSuccEquiv_X_zero]

/-- Evaluating the state polynomial ring at the swapped terminal jet is the two-step evaluation
`ℂ[U][V] → K̄((s))` at `(U, V)`. -/
theorem firstOrderStatePolynomialEval_terminalSwapped
    (U : LaurentSeries ℂ) (V W : FirstOrderTerminalLaurentField) :
    letI : Algebra ℂ FirstOrderTerminalLaurentField :=
      firstOrderTerminalComplexMap.toAlgebra
    (firstOrderStatePolynomialEval (firstOrderTerminalSwappedJet U V W)).toRingHom =
      firstOrderTerminalStateRingEval U V := by
  letI : Algebra ℂ FirstOrderTerminalLaurentField :=
    firstOrderTerminalComplexMap.toAlgebra
  have heval :
      (firstOrderTerminalStateRingEval U V).comp
          firstOrderStatePolynomialEquiv.toRingHom =
        (MvPolynomial.aeval
          (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} =>
            firstOrderTerminalSwappedJet U V W j.1)).toRingHom := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      change firstOrderTerminalStateRingEval U V
          (firstOrderStatePolynomialEquiv (MvPolynomial.C r)) = _
      have hC : firstOrderStatePolynomialEquiv (MvPolynomial.C r) =
          algebraMap ℂ FirstOrderStatePolynomialRing r := by
        simpa using firstOrderStatePolynomialEquiv.commutes r
      rw [hC]
      simp [firstOrderTerminalStateRingEval, firstOrderTerminalInnerStateEval]
      change firstOrderTerminalComplexMap r =
        (algebraMap ℂ FirstOrderTerminalLaurentField) r
      rfl
    · intro j
      rcases j with ⟨⟨j, hjlt⟩, hjne⟩
      interval_cases j
      · have hjEq :
            (⟨⟨0, hjlt⟩, hjne⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)}) =
              ⟨0, by decide⟩ := by
          apply Subtype.ext
          apply Fin.ext
          rfl
        rw [hjEq]
        change firstOrderTerminalStateRingEval U V
            (firstOrderStatePolynomialEquiv
              (MvPolynomial.X (⟨0, by decide⟩ :
                {j : Fin 3 // j ≠ (2 : Fin 3)}))) = _
        rw [firstOrderStatePolynomialEquiv_X_zero]
        simp [firstOrderTerminalStateRingEval, firstOrderTerminalSwappedJet,
          MvPolynomial.aeval_def]
      · have hjEq :
            (⟨⟨1, hjlt⟩, hjne⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)}) =
              ⟨1, by decide⟩ := by
          apply Subtype.ext
          apply Fin.ext
          rfl
        rw [hjEq]
        change firstOrderTerminalStateRingEval U V
            (firstOrderStatePolynomialEquiv
              (MvPolynomial.X (⟨1, by decide⟩ :
                {j : Fin 3 // j ≠ (2 : Fin 3)}))) = _
        rw [firstOrderStatePolynomialEquiv_X_one]
        simp [firstOrderTerminalStateRingEval, firstOrderTerminalInnerStateEval,
          firstOrderTerminalSwappedJet, MvPolynomial.aeval_def]
      · exfalso
        apply hjne
        rfl
  apply DFunLike.ext _ _
  intro P
  let c := firstOrderStatePolynomialEquiv.symm P
  have hP : firstOrderStatePolynomialEquiv c = P := by simp [c]
  rw [← hP]
  change firstOrderStatePolynomialEval (firstOrderTerminalSwappedJet U V W)
      (firstOrderStatePolynomialEquiv c) = _
  rw [firstOrderStatePolynomialEval_equiv]
  exact congrArg (fun g => g c) heval.symm

noncomputable def firstOrderStateSwapEquiv :
    {j : Fin 3 // j ≠ (2 : Fin 3)} ≃ {j : Fin 3 // j ≠ (2 : Fin 3)} :=
  firstOrderStateIndexEquiv.trans
    ((Equiv.swap (0 : Fin 2) (1 : Fin 2)).trans firstOrderStateIndexEquiv.symm)

theorem firstOrderStateIndexEquiv_symm_zero :
    firstOrderStateIndexEquiv.symm (0 : Fin 2) =
      (⟨0, by decide⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)}) := by
  apply firstOrderStateIndexEquiv.injective
  simp [firstOrderStateIndexEquiv]

theorem firstOrderStateIndexEquiv_symm_one :
    firstOrderStateIndexEquiv.symm (1 : Fin 2) =
      (⟨1, by decide⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)}) := by
  apply firstOrderStateIndexEquiv.injective
  simp [firstOrderStateIndexEquiv]

/-- For nonzero exponents, the clock `U = t^(e_U)` and value `V = s^(e_V)` coordinates of the
terminal jet are algebraically independent over `ℂ` in `K̄((s))`. -/
theorem algebraicIndependent_firstOrderTerminalState
    (eU eV : ℤ) (heU : eU ≠ 0) (heV : eV ≠ 0)
    (W : FirstOrderTerminalLaurentField) :
    let U := HahnSeries.single eU (1 : ℂ)
    let V := HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField)
    letI : Algebra ℂ FirstOrderTerminalLaurentField :=
      firstOrderTerminalComplexMap.toAlgebra
    AlgebraicIndependent ℂ
      (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} =>
        firstOrderTerminalJet U V W j.1) := by
  let U := HahnSeries.single eU (1 : ℂ)
  let V := HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField)
  letI : Algebra ℂ FirstOrderTerminalLaurentField :=
    firstOrderTerminalComplexMap.toAlgebra
  have hinjSwapped : Function.Injective
      (firstOrderStatePolynomialEval (firstOrderTerminalSwappedJet U V W)) := by
    intro P Q hPQ
    apply firstOrderTerminalStateRingEval_injective eU eV heU heV
    rw [← firstOrderStatePolynomialEval_terminalSwapped U V W]
    exact hPQ
  have hAI_swapped : AlgebraicIndependent ℂ
      (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} =>
        firstOrderTerminalSwappedJet U V W j.1) := by
    rw [algebraicIndependent_iff_injective_aeval]
    intro P Q hPQ
    apply firstOrderStatePolynomialEquiv.injective
    apply hinjSwapped
    simpa only [firstOrderStatePolynomialEval_equiv] using hPQ
  have hcomp := hAI_swapped.comp firstOrderStateSwapEquiv
    firstOrderStateSwapEquiv.injective
  have heq :
      ((fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} =>
          firstOrderTerminalSwappedJet U V W j.1) ∘ firstOrderStateSwapEquiv) =
        (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} =>
          firstOrderTerminalJet U V W j.1) := by
    funext j
    rcases j with ⟨⟨j, hjlt⟩, hjne⟩
    interval_cases j
    · change firstOrderTerminalSwappedJet U V W
          (firstOrderStateSwapEquiv
            (⟨⟨0, hjlt⟩, hjne⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)})).1 = _
      rw [show (⟨⟨0, hjlt⟩, hjne⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)}) =
          ⟨0, by decide⟩ by
        apply Subtype.ext
        apply Fin.ext
        rfl]
      simp only [firstOrderStateSwapEquiv, Equiv.trans_apply]
      rw [show firstOrderStateIndexEquiv (⟨0, by decide⟩ :
            {j : Fin 3 // j ≠ (2 : Fin 3)}) = 0 by rfl,
        Equiv.swap_apply_left, firstOrderStateIndexEquiv_symm_one]
      rfl
    · change firstOrderTerminalSwappedJet U V W
          (firstOrderStateSwapEquiv
            (⟨⟨1, hjlt⟩, hjne⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)})).1 = _
      rw [show (⟨⟨1, hjlt⟩, hjne⟩ : {j : Fin 3 // j ≠ (2 : Fin 3)}) =
          ⟨1, by decide⟩ by
        apply Subtype.ext
        apply Fin.ext
        rfl]
      simp only [firstOrderStateSwapEquiv, Equiv.trans_apply]
      rw [show firstOrderStateIndexEquiv (⟨1, by decide⟩ :
            {j : Fin 3 // j ≠ (2 : Fin 3)}) = 1 by rfl,
        Equiv.swap_apply_right, firstOrderStateIndexEquiv_symm_zero]
      rfl
    · exfalso
      apply hjne
      rfl
  rw [heq] at hcomp
  exact hcomp

/-- For nonzero exponents, evaluation of the clock/value state ring at the terminal jet
`(t^(e_U), s^(e_V), W)` is injective, for every `W`. -/
theorem firstOrderStatePolynomialEval_terminal_injective
    (eU eV : ℤ) (heU : eU ≠ 0) (heV : eV ≠ 0)
    (W : FirstOrderTerminalLaurentField) :
    let U := HahnSeries.single eU (1 : ℂ)
    let V := HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField)
    letI : Algebra ℂ FirstOrderTerminalLaurentField :=
      firstOrderTerminalComplexMap.toAlgebra
    Function.Injective
      (firstOrderStatePolynomialEval (firstOrderTerminalJet U V W)) := by
  let U := HahnSeries.single eU (1 : ℂ)
  let V := HahnSeries.single eV (1 : FirstOrderTerminalCoefficientField)
  letI : Algebra ℂ FirstOrderTerminalLaurentField :=
    firstOrderTerminalComplexMap.toAlgebra
  exact firstOrderStatePolynomialEval_injective_of_algebraicIndependent _
    (algebraicIndependent_firstOrderTerminalState eU eV heU heV W)

/-- Given Wiman initial data for `f` (an irreducible relation `P(z, f, f') = 0` with Newton-edge
data), the terminal Puiseux series `W = s^(-R) z` is a root of `P`, viewed as a polynomial in the
derivative coordinate over `ℂ(U, V)` embedded via `U = t^(-N q)`, `V = s^(-R)`. -/
theorem exists_entireFirstOrderWiman_rationalDerivativePuiseuxRoot
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    ∃ (M a q N : ℕ) (_hN : N ≠ 0) (z₀ : PowerSeries ℂ)
        (R : ℕ) (_hR : R ≠ 0)
        (z : PowerSeries FirstOrderTerminalCoefficientField) (_hq : q ≠ 0),
      data.slope = ((M : ℚ) - (a : ℚ)) / q ∧
      PowerSeries.constantCoeff z₀ = data.root ∧
      PowerSeries.constantCoeff z =
        algebraMap (LaurentSeries ℂ) FirstOrderTerminalCoefficientField
          (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
            algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
              ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z₀)) ∧
      let U := HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ)
      let V := HahnSeries.single (-((R : ℕ) : ℤ))
        (1 : FirstOrderTerminalCoefficientField)
      let W := HahnSeries.single (-((R : ℕ) : ℤ))
          (1 : FirstOrderTerminalCoefficientField) *
        algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
          FirstOrderTerminalLaurentField z
      letI : Algebra ℂ FirstOrderTerminalLaurentField :=
        firstOrderTerminalComplexMap.toAlgebra
      let hinj : Function.Injective
          (firstOrderStatePolynomialEval (firstOrderTerminalJet U V W)) :=
        firstOrderStatePolynomialEval_terminal_injective
          (-((N * q : ℕ) : ℤ)) (-((R : ℕ) : ℤ))
          (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (mul_ne_zero _hN _hq)))
          (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr _hR)) W
      ((firstOrderDerivativePolynomial data.P).map
        (firstOrderRationalStateEval (firstOrderTerminalJet U V W) hinj).toRingHom).IsRoot W := by
  obtain ⟨M, a, q, N, hN, z₀, R, hR, z, hq, hslope, hz₀, hz, hfull⟩ :=
    exists_entireFirstOrderWiman_fullRelationPuiseuxRoot data
  refine ⟨M, a, q, N, hN, z₀, R, hR, z, hq, hslope, hz₀, hz, ?_⟩
  let U := HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ)
  let V := HahnSeries.single (-((R : ℕ) : ℤ))
    (1 : FirstOrderTerminalCoefficientField)
  let W := HahnSeries.single (-((R : ℕ) : ℤ))
      (1 : FirstOrderTerminalCoefficientField) *
    algebraMap (PowerSeries FirstOrderTerminalCoefficientField)
      FirstOrderTerminalLaurentField z
  letI : Algebra ℂ FirstOrderTerminalLaurentField :=
    firstOrderTerminalComplexMap.toAlgebra
  let hinj : Function.Injective
      (firstOrderStatePolynomialEval (firstOrderTerminalJet U V W)) :=
    firstOrderStatePolynomialEval_terminal_injective
      (-((N * q : ℕ) : ℤ)) (-((R : ℕ) : ℤ))
      (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (mul_ne_zero hN hq)))
      (neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr hR)) W
  change Polynomial.eval W
      ((firstOrderDerivativePolynomial data.P).map
        (firstOrderRationalStateEval
          (firstOrderTerminalJet U V W) hinj).toRingHom) = 0
  rw [Polynomial.eval_map]
  change Polynomial.eval₂
      (firstOrderRationalStateEval (firstOrderTerminalJet U V W) hinj)
      W (firstOrderDerivativePolynomial data.P) = 0
  change Polynomial.eval₂
      (firstOrderRationalStateEval (firstOrderTerminalJet U V W) hinj)
      (firstOrderTerminalJet U V W 2)
      (firstOrderDerivativePolynomial data.P) = 0
  rw [firstOrderDerivativePolynomial_eval]
  change MvPolynomial.eval₂ firstOrderTerminalComplexMap
      (firstOrderTerminalJet U V W) data.P = 0
  exact hfull

/-- If `x ∈ L` is integral over `K` and `y ∈ M` is a root of the minimal polynomial of `x`, then
there is a `K`-algebra map `K(x) → M` sending `x` to `y`. -/
theorem exists_adjoinSimple_algHom_of_minpoly_root
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] (x : L) (hx : IsIntegral K x)
    (y : M) (hy : Polynomial.eval₂ (algebraMap K M) y (minpoly K x) = 0) :
    ∃ e : (IntermediateField.adjoin K {x}) →ₐ[K] M,
      e (IntermediateField.AdjoinSimple.gen K x) = y := by
  let pb : PowerBasis K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.powerBasis hx
  let inc : (IntermediateField.adjoin K {x}) →ₐ[K] L :=
    (IntermediateField.adjoin K {x}).val
  have hgen : inc pb.gen = x := by
    rw [IntermediateField.adjoin.powerBasis_gen]
    rfl
  have hmin : minpoly K pb.gen = minpoly K x := by
    calc
      minpoly K pb.gen = minpoly K (inc pb.gen) :=
        (minpoly.algHom_eq inc inc.injective pb.gen).symm
      _ = minpoly K x := congrArg (minpoly K) hgen
  have hy' : Polynomial.aeval y (minpoly K pb.gen) = 0 := by
    rw [Polynomial.aeval_def, hmin]
    exact hy
  let e : (IntermediateField.adjoin K {x}) →ₐ[K] M := pb.lift y hy'
  refine ⟨e, ?_⟩
  rw [← IntermediateField.adjoin.powerBasis_gen hx]
  exact pb.lift_gen y hy'

/-- If the minimal polynomial of `a` is associated to `p` and `y ∈ M` is a root of `p` mapped to
`M`, then `y` is a root of the minimal polynomial of `a`. -/
theorem minpoly_isRoot_of_associated_mapped_isRoot
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    {p : Polynomial K} {x : Type*} [Field x] [Algebra K x]
    (a : x) (hassoc : Associated (minpoly K a) p) (y : M)
    (hy : (p.map (algebraMap K M)).IsRoot y) :
    Polynomial.eval₂ (algebraMap K M) y (minpoly K a) = 0 := by
  rcases hassoc with ⟨u, hu⟩
  have hmap := congrArg (Polynomial.map (algebraMap K M)) hu
  have heval := congrArg (Polynomial.eval y) hmap
  rw [Polynomial.map_mul, Polynomial.eval_mul] at heval
  have huUnit : IsUnit
      (((u : Polynomial K).map (algebraMap K M)).eval y) := by
    exact (u.isUnit.map (Polynomial.mapRingHom (algebraMap K M))).map
      (Polynomial.evalRingHom y)
  have huNe : ((u : Polynomial K).map (algebraMap K M)).eval y ≠ 0 :=
    huUnit.ne_zero
  simpa [Polynomial.eval_map] using
    (mul_eq_zero.mp (heval.trans hy)).resolve_right huNe

end

end GaloisForLFunctions.HTGeometry
