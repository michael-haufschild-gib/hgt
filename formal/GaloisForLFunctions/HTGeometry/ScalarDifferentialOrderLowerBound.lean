import GaloisForLFunctions.HTGeometry.DifferentialPolynomialRank
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver
import GaloisForLFunctions.HTGeometry.TerminalPowerCascadeInduction

/-!
# Independent jets forbid low-order algebraic differential equations

A scalar differential polynomial of order at most `n` uses only the jets `x, x', ..., x^(n)`.  If
those `n+1` jets are algebraically independent over the base, no nonzero such polynomial can
annihilate `x`: the polynomial is a rename of an honest `n+1`-variable polynomial along the injection
`i |-> ((), i)`, and evaluation on an independent family is injective.

This is the lower half of the equality between the minimal order of an algebraic differential
equation and the transcendence degree of the generated differential field.  Combined with the
terminal-power cascade induction it says that a triangular flag of depth `n` costs at least `n`
differential orders — each level contributing one, whatever the size of its exponent.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A scalar differential polynomial of order at most `n` only uses the first `n+1` jets. -/
theorem scalarDifferentialPolynomial_vars_subset_range
    {K : Type*} [CommSemiring K] {n : ℕ} {P : DifferentialPolynomial Unit K}
    (hP : scalarDifferentialPolynomialOrder P ≤ n) :
    (P.vars : Set (Unit × ℕ)) ⊆ Set.range (fun i : Fin (n + 1) => ((), (i : ℕ))) := by
  intro p hp
  have hmem : p ∈ P.vars := hp
  have h2 : p.2 ≤ n :=
    le_trans (Finset.le_sup (f := fun j : Unit × ℕ => j.2) hmem) hP
  refine ⟨⟨p.2, by omega⟩, ?_⟩
  cases p with
  | mk a b => cases a; rfl

/-- **Independent jets forbid a low-order relation.**  If the first `n+1` jets of `x` are
algebraically independent over `K`, then no nonzero scalar differential polynomial of order at most
`n` vanishes on `x`. -/
theorem differentialPolynomialEvalOver_ne_zero_of_algebraicIndependent_jets
    {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] [Differential L]
    {x : L} {n : ℕ}
    (hind : AlgebraicIndependent K (fun i : Fin (n + 1) => differentialJet (i : ℕ) x))
    {P : DifferentialPolynomial Unit K} (hP : P ≠ 0)
    (horder : scalarDifferentialPolynomialOrder P ≤ n) :
    differentialPolynomialEvalOver (K := K) (fun _ : Unit => x) P ≠ 0 := by
  have hinj : Function.Injective (fun i : Fin (n + 1) => ((), (i : ℕ))) := by
    intro i j hij
    exact Fin.ext (congrArg Prod.snd hij)
  obtain ⟨Q, hQ⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range P
      (fun i : Fin (n + 1) => ((), (i : ℕ))) hinj
      (scalarDifferentialPolynomial_vars_subset_range horder)
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, map_zero] at hQ
    exact hP hQ.symm
  subst hQ
  rw [differentialPolynomialEvalOver, MvPolynomial.aeval_rename]
  have hcomp : (fun p : Unit × ℕ => differentialJet p.2 ((fun _ : Unit => x) p.1))
      ∘ (fun i : Fin (n + 1) => ((), (i : ℕ)))
      = fun i : Fin (n + 1) => differentialJet (i : ℕ) x := rfl
  rw [hcomp]
  intro hzero
  exact hQ0 ((algebraicIndependent_iff_injective_aeval.mp hind)
    (by rw [hzero, map_zero]))

/-! ## The cascade lower bound -/

/-- **A triangular power cascade of depth `m+2` costs at least `m+2` differential orders.**  No
nonzero algebraic differential equation of order at most `m+1` over `ℂ` is satisfied by the terminal
output of the cascade. -/
theorem cascadeOutput_no_low_order_relation
    {R : Type*} [Field R] [Algebra ℂ R]
    (δ : Derivation ℂ R R) (P : ℕ → Derivation ℂ R R) (Y : ℕ → R)
    (C X : ℕ → R) (q : ℕ → ℕ)
    (hchain : ∀ k, δ (Y (k + 1)) = Y k * Y (k + 1))
    (hnz : ∀ k, Y k ≠ 0)
    (htri : ∀ k l i, l < k → P k (((δ : R → R)^[i]) (Y l)) = 0)
    (hbase : P 0 (Y 0) ≠ 0)
    (hY : ∀ k, Y (k + 1) = C k * X k ^ q k)
    (hPC : ∀ k, P (k + 1) (C k) = 0)
    (hPX : ∀ k, P (k + 1) (X k) = 1)
    (hq : ∀ k, 0 < q k) (hC : ∀ k, C k ≠ 0) (hX : ∀ k, X k ≠ 0) (m : ℕ)
    {Q : DifferentialPolynomial Unit ℂ} (hQ : Q ≠ 0)
    (horder : scalarDifferentialPolynomialOrder Q ≤ m + 1) :
    letI : Differential R := ⟨δ.restrictScalars ℤ⟩
    differentialPolynomialEvalOver (K := ℂ) (fun _ : Unit => Y (m + 1)) Q ≠ 0 := by
  letI : Differential R := ⟨δ.restrictScalars ℤ⟩
  refine differentialPolynomialEvalOver_ne_zero_of_algebraicIndependent_jets
    (n := m + 1) ?_ hQ horder
  exact algebraicIndependent_cascadeOutput_of_power δ P Y C X q hchain hnz htri hbase hY
    hPC hPX hq hC hX m

end

end GaloisForLFunctions
