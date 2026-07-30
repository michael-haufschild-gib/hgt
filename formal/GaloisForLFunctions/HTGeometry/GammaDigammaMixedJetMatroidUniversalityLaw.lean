import GaloisForLFunctions.HTGeometry.GammaDigammaJetFreeness
import GaloisForLFunctions.HTGeometry.GammaHypertranscendental

/-!
# Gamma--digamma mixed-jet matroid universality

Separate hypertranscendence of Gamma and digamma does not describe their mixed
differential matroid.  Gamma-power elimination closes that gap.  Every finite family
consisting of Gamma itself and an initial digamma jet is algebraically independent:
a polynomial in Gamma with coefficients in the digamma-jet algebra is a
`GammaPowerRel`, so all coefficients vanish.  Finitarity then gives the countably
infinite basis

`{Gamma} ∪ {digamma, digamma', digamma'', ...}`.

The Bell chain expresses every positive Gamma jet from this basis away from the poles.
Nevertheless, the full mixed Gamma/digamma jet family is dependent already at first
order, because `Gamma' = Gamma * digamma`.  Thus separate free towers fuse into one
triangular basis plus an explicit mixed circuit.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

/-- The canonical mixed basis: Gamma in the distinguished slot and every digamma
derivative in the remaining countable slots. -/
def gammaDigammaMixedJetBasis : Option ℕ → (ℂ → ℂ) :=
  fun o => o.elim Complex.Gamma
    (fun j => iteratedDeriv j Complex.digamma)

/-- **Finite mixed-basis freeness.**  Gamma together with every digamma derivative
through order `n` is algebraically independent over `ℂ`. -/
theorem algebraicIndependent_gamma_and_digamma_initialJets (n : ℕ) :
    AlgebraicIndependent ℂ
      (fun o : Option (Fin (n + 1)) =>
        o.elim Complex.Gamma
          (fun j => iteratedDeriv (j : ℕ) Complex.digamma)) := by
  let psiJet : Fin (n + 1) → (ℂ → ℂ) :=
    fun j => iteratedDeriv (j : ℕ) Complex.digamma
  have hpsi : AlgebraicIndependent ℂ psiJet := by
    simpa [psiJet] using algebraicIndependent_digamma_initialJets n
  change AlgebraicIndependent ℂ
    (fun o : Option (Fin (n + 1)) => o.elim Complex.Gamma psiJet)
  rw [hpsi.option_iff_transcendental]
  rintro ⟨p, hp, hroot⟩
  let reprCoeff : ℕ → MvPolynomial (Fin (n + 1)) ℂ :=
    fun k => hpsi.repr (p.coeff k)
  let clearedCoeff : ℕ → MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
    fun k => MvPolynomial.map Polynomial.C (reprCoeff k)
  let rationalCoeff : ℕ → MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
    fun k =>
      MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
        (clearedCoeff k)
  have hrepr (k : ℕ) :
      MvPolynomial.aeval psiJet (reprCoeff k) =
        ((p.coeff k : Algebra.adjoin ℂ (Set.range psiJet)) : ℂ → ℂ) := by
    simp [reprCoeff]
  have hclearedEval (k : ℕ) (z : ℂ) :
      polyJetEval (n + 1) z (clearedCoeff k) =
        ((p.coeff k : Algebra.adjoin ℂ (Set.range psiJet)) : ℂ → ℂ) z := by
    change polyJetEval (n + 1) z
      (MvPolynomial.map Polynomial.C (reprCoeff k)) = _
    rw [polyJetEval_eq_eval₂, eval₂_map_polyC]
    calc
      MvPolynomial.eval (digammaJet (n + 1) z) (reprCoeff k) =
          (Pi.evalAlgHom ℂ (fun _ : ℂ => ℂ) z)
            (MvPolynomial.aeval psiJet (reprCoeff k)) := by
              rw [MvPolynomial.comp_aeval_apply]
              rfl
      _ = _ := by rw [hrepr]; rfl
  have hrel : GammaPowerRel (n + 1) p.natDegree rationalCoeff := by
    refine ⟨1, one_ne_zero, clearedCoeff, ?_, ?_⟩
    · intro k hk
      simp [rationalCoeff]
    · intro z hz
      have hrootz :
          ∑ k ∈ Finset.range (p.natDegree + 1),
              ((p.coeff k : Algebra.adjoin ℂ (Set.range psiJet)) : ℂ → ℂ) z
                * Complex.Gamma z ^ k = 0 := by
        have hzroot := congrFun hroot z
        rw [Polynomial.aeval_eq_sum_range] at hzroot
        simpa [Algebra.smul_def] using hzroot
      calc
        _ = ∑ k ∈ Finset.range (p.natDegree + 1),
            Complex.Gamma z ^ k
              * ((p.coeff k : Algebra.adjoin ℂ (Set.range psiJet)) : ℂ → ℂ) z := by
                exact Finset.sum_congr rfl fun k _ => by rw [hclearedEval]
        _ = 0 := by simpa [mul_comm] using hrootz
  have hall := gammaPowerRel_eq_zero p.natDegree rationalCoeff hrel
  have hcoeff (k : ℕ) : p.coeff k = 0 := by
    by_cases hk : k ≤ p.natDegree
    · have hrat : rationalCoeff k = 0 := hall k hk
      have hclear : clearedCoeff k = 0 :=
        MvPolynomial.map_injective _
          (RatFunc.algebraMap_injective ℂ) (by
            simpa [rationalCoeff] using hrat)
      have hrepr0 : reprCoeff k = 0 :=
        MvPolynomial.map_injective Polynomial.C Polynomial.C_injective (by
          simpa [clearedCoeff] using hclear)
      apply hpsi.aevalEquiv.symm.injective
      simpa [reprCoeff, AlgebraicIndependent.repr] using hrepr0
    · exact
        Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hk)
  apply hp
  exact Polynomial.ext fun k => by simpa using hcoeff k

/-- **Countable mixed-basis freeness.**  Gamma and the complete digamma derivative
tower form one algebraically independent family. -/
theorem algebraicIndependent_gammaDigammaMixedJetBasis :
    AlgebraicIndependent ℂ gammaDigammaMixedJetBasis := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  let N : ℕ := ht.toFinset.sup (fun o : Option ℕ => o.getD 0)
  have hbound {j : ℕ} (hj : some j ∈ t) : j ≤ N := by
    change j ≤ ht.toFinset.sup (fun o : Option ℕ => o.getD 0)
    have hmem : some j ∈ ht.toFinset := ht.mem_toFinset.mpr hj
    simpa using Finset.le_sup (s := ht.toFinset)
      (f := fun o : Option ℕ => o.getD 0) hmem
  let e : t → Option (Fin (N + 1)) := fun o =>
    match h : o.1 with
    | none => none
    | some j =>
        some ⟨j, Nat.lt_succ_of_le
          (hbound (by simpa [h] using o.property))⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b => simp [e] at hab
    | some a =>
        cases b with
        | none => simp [e] at hab
        | some b =>
            have hv : a = b := by
              simpa [e] using congrArg
                (fun o : Option (Fin (N + 1)) => o.map Fin.val) hab
            exact congrArg some hv
  have hfinite :=
    (algebraicIndependent_gamma_and_digamma_initialJets N).comp e he
  convert hfinite using 1
  funext o
  rcases o with ⟨o, ho⟩
  cases o <;> rfl

/-- The Bell chain realizes every positive Gamma jet from a finite prefix of the
mixed basis at every point away from Gamma's poles. -/
theorem gamma_positiveJet_bellGenerated_by_mixedBasis
    (n : ℕ) (k : Fin (n + 1)) (s : ℂ)
    (hs : ∀ p : ℕ, s ≠ -(p : ℂ)) :
    iteratedDeriv ((k : ℕ) + 1) Complex.Gamma s =
      gammaDigammaMixedJetBasis none s *
        MvPolynomial.eval
          (fun j : Fin (n + 1) =>
            gammaDigammaMixedJetBasis (some (j : ℕ)) s)
          (bellAt n ((k : ℕ) + 1) k.isLt) := by
  simpa [gammaDigammaMixedJetBasis, digammaJet] using!
    gamma_iteratedDeriv_eq_bellAt ((k : ℕ) + 1) k.isLt hs

/-- Gamma's first derivative is globally the product of Gamma and digamma, including
the conventionally zero values at Gamma's poles. -/
theorem gamma_iteratedDeriv_one_eq_mul_digamma :
    iteratedDeriv 1 Complex.Gamma =
      Complex.Gamma * Complex.digamma := by
  funext z
  by_cases hpole : ∃ p : ℕ, z = -(p : ℂ)
  · obtain ⟨p, rfl⟩ := hpole
    rw [iteratedDeriv_one,
      deriv_zero_of_not_differentiableAt
        (Complex.not_differentiableAt_Gamma_neg_nat p)]
    simp [Pi.mul_apply, Complex.Gamma_neg_nat_eq_zero]
  · have hoff : ∀ p : ℕ, z ≠ -(p : ℂ) := by
      intro p hp
      exact hpole ⟨p, hp⟩
    rw [iteratedDeriv_one]
    have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hoff
    change deriv Complex.Gamma z =
      Complex.Gamma z * Complex.digamma z
    rw [show Complex.digamma z =
        deriv Complex.Gamma z / Complex.Gamma z by
      rw [Complex.digamma_def, logDeriv_apply]]
    field_simp

/-- The first mixed Gamma/digamma circuit packet. -/
def gammaDigammaFirstJetCircuit : Fin 3 → (ℂ → ℂ) :=
  ![Complex.Gamma, iteratedDeriv 1 Complex.Gamma, Complex.digamma]

/-- The packet `(Gamma, Gamma', digamma)` is algebraically dependent through the
nonzero circuit polynomial `X₁ - X₀ X₂`. -/
theorem not_algebraicIndependent_gammaDigammaFirstJetCircuit :
    ¬ AlgebraicIndependent ℂ gammaDigammaFirstJetCircuit := by
  intro h
  let P : MvPolynomial (Fin 3) ℂ :=
    MvPolynomial.X 1 - MvPolynomial.X 0 * MvPolynomial.X 2
  have hPne : P ≠ 0 := by
    intro hP
    have hc := congrArg
      (MvPolynomial.eval fun i : Fin 3 => if i = 1 then 1 else 0) hP
    norm_num [P] at hc
  apply hPne
  apply h.eq_zero_of_aeval_eq_zero
  ext z
  simp only [P, map_sub, aeval_X, map_mul, Pi.sub_apply,
    Pi.mul_apply, gammaDigammaFirstJetCircuit, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change iteratedDeriv 1 Complex.Gamma z -
    Complex.Gamma z * Complex.digamma z = 0
  exact sub_eq_zero.mpr (by
    simpa [Pi.mul_apply] using
      congrFun gamma_iteratedDeriv_one_eq_mul_digamma z)

/-- **Gamma--digamma mixed-jet matroid universality law.**  The countable family
`{Gamma} ∪ {digamma^(j)}` is free, every positive Gamma jet is triangularly generated
from a finite prefix away from the poles, and the full mixed jet family becomes
dependent already on `(Gamma, Gamma', digamma)`. -/
theorem gammaDigamma_mixedJetMatroidUniversality :
    AlgebraicIndependent ℂ gammaDigammaMixedJetBasis ∧
      (∀ (n : ℕ) (k : Fin (n + 1)) (s : ℂ),
        (∀ p : ℕ, s ≠ -(p : ℂ)) →
          iteratedDeriv ((k : ℕ) + 1) Complex.Gamma s =
            gammaDigammaMixedJetBasis none s *
              MvPolynomial.eval
                (fun j : Fin (n + 1) =>
                  gammaDigammaMixedJetBasis (some (j : ℕ)) s)
                (bellAt n ((k : ℕ) + 1) k.isLt)) ∧
      ¬ AlgebraicIndependent ℂ gammaDigammaFirstJetCircuit := by
  refine ⟨algebraicIndependent_gammaDigammaMixedJetBasis, ?_,
    not_algebraicIndependent_gammaDigammaFirstJetCircuit⟩
  exact fun n k s hs =>
    gamma_positiveJet_bellGenerated_by_mixedBasis n k s hs

end GaloisForLFunctions

end
