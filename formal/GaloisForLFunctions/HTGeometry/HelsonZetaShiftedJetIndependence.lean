import GaloisForLFunctions.HTGeometry.ArithmeticFunctionGeneralJacobian
import GaloisForLFunctions.HTGeometry.HelsonPhaseTailIndependence
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality
import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField

/-!
# The shifted derivatives of a Helson zeta function are differentially independent

The coefficient function of the `k`-th derivative of `Z_χ(s + α)` is

```text
n ↦ χ(n) · n^{-α} · (c · log n)^k ,
```

with `c = -1` for the analytic derivative and `c = i` for the rotated logarithmic derivation that
the Dirichlet coefficient field carries.  It is supported on all of `ℕ`, not on a single prime-power
layer, so the prime-supported Jacobian bridge does not see it; the prime-evaluation criterion
without a support restriction does.

Only the restriction to the primes is constrained, and there the family is the shift--jet palette of
the phase, whose tail independence holds for every nowhere-vanishing phase.  The conclusion is that
the complete shift--jet family of `Z_χ` is algebraically independent over the intrinsic finite-prime
coefficient field, for an arbitrary set of shifts with distinct real parts — Pong's independence
conclusion in the form a Helson zeta function consumes it.  Two phases therefore generate the same
labelled differential field, and the labelled isomorphism between them is the canonical one.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix

noncomputable section

universe u

/-! ### Algebraic independence from finite subfamilies -/

/-- A family is algebraically independent as soon as each of its finite subfamilies is: a
polynomial relation involves only finitely many variables. -/
theorem algebraicIndependent_of_finite_subfamilies {ι R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (x : ι → A)
    (h : ∀ S : Finset ι, AlgebraicIndependent R fun i : S => x (i : ι)) :
    AlgebraicIndependent R x := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  have hinj : Function.Injective (Subtype.val : {i // i ∈ P.vars} → ι) := Subtype.val_injective
  have hsub : (↑P.vars : Set ι) ⊆ Set.range (Subtype.val : {i // i ∈ P.vars} → ι) := by
    intro i hi
    exact ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P Subtype.val hinj hsub
  have hqeval : MvPolynomial.aeval (fun i : P.vars => x (i : ι)) q = 0 := by
    have := MvPolynomial.aeval_rename (Subtype.val : {i // i ∈ P.vars} → ι) x q
    rw [hq] at this
    rw [show (fun i : {i // i ∈ P.vars} => x (i : ι)) = x ∘ Subtype.val from rfl, ← this, hP]
  have hq0 : q = 0 := (algebraicIndependent_iff.mp (h P.vars)) q hqeval
  rw [← hq, hq0, _root_.map_zero]

/-! ### The shifted-jet coefficient functions of a Helson zeta -/

/-- The Dirichlet coefficient function of the `k`-th jet of `Z_χ(s + α)` for the logarithmic clock
scaled by `c`. -/
def helsonClockJet (χ : ℕ → ℂ) (α c : ℂ) (k : ℕ) : ArithmeticFunction ℂ where
  toFun n :=
    if n = 0 then 0
    else χ n * Complex.exp (-α * (Real.log n : ℂ)) * (c * (Real.log n : ℂ)) ^ k
  map_zero' := by simp

theorem helsonClockJet_apply (χ : ℕ → ℂ) (α c : ℂ) (k : ℕ) (n : ℕ) :
    helsonClockJet χ α c k n
      = if n = 0 then 0
        else χ n * Complex.exp (-α * (Real.log n : ℂ)) * (c * (Real.log n : ℂ)) ^ k := rfl

theorem helsonClockJet_apply_prime (χ : ℕ → ℂ) (α c : ℂ) (k : ℕ) (p : Nat.Primes) :
    helsonClockJet χ α c k (p : ℕ)
      = c ^ k * (χ (p : ℕ) * primeShiftFactor α p * primeLogClock p ^ k) := by
  have hp0 : (p : ℕ) ≠ 0 := p.2.ne_zero
  rw [helsonClockJet_apply, if_neg hp0, primeShiftFactor, primeLogClock, mul_pow]
  ring

/-- The rotated logarithmic derivation raises the clock power by one. -/
theorem logWeight_helsonClockJet (χ : ℕ → ℂ) (α : ℂ) (k : ℕ) :
    Complex.I • logWeight (helsonClockJet χ α Complex.I k)
      = helsonClockJet χ α Complex.I (k + 1) := by
  ext n
  have hL : (Complex.I • logWeight (helsonClockJet χ α Complex.I k)) n
      = Complex.I * ((Real.log n : ℂ) * helsonClockJet χ α Complex.I k n) := rfl
  rw [hL, helsonClockJet_apply, helsonClockJet_apply]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn, pow_succ]
    ring

/-- The `k`-th jet of the shifted Helson zeta in the Dirichlet coefficient field. -/
theorem differentialJet_helsonClockJet (χ : ℕ → ℂ) (α : ℂ) (k : ℕ) :
    differentialJet k (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (helsonClockJet χ α Complex.I 0))
      = algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (helsonClockJet χ α Complex.I k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [differentialJet_succ, ih, arithmeticFunctionFractionField_deriv_apply,
        rotatedLogFractionDerivation_algebraMap, logWeight_helsonClockJet]

/-! ### Tail independence of the prime restrictions -/

/-- Tail independence is invariant under reindexing the family. -/
theorem tailCoefficientIndependent_equiv {I I' P : Type*} [Fintype I] [Fintype I']
    (e : I' ≃ I) {a : I → P → ℂ} (h : TailCoefficientIndependent a) :
    TailCoefficientIndependent (fun i' => a (e i')) := by
  intro c hc
  have hsum : ∀ p : P, ∑ i, (fun i => c (e.symm i)) i * a i p = ∑ i', c i' * a (e i') p := by
    intro p
    rw [← Equiv.sum_comp e (fun i => (fun i => c (e.symm i)) i * a i p)]
    exact Finset.sum_congr rfl fun i' _ => by simp
  have hfin : {p : P | ∑ i, (fun i => c (e.symm i)) i * a i p ≠ 0}.Finite := by
    refine hc.subset ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rwa [hsum p] at hp
  have hzero := h (fun i => c (e.symm i)) hfin
  funext i'
  have := congrFun hzero (e i')
  simpa [Equiv.symm_apply_apply] using this

/-- **The prime restrictions of the shift--jet rectangle of a nowhere-vanishing phase are tail
independent.**  The clock scaling is a column weight, which tail independence does not see. -/
theorem tailCoefficientIndependent_helsonClockJet {A : Type u} [Fintype A] [DecidableEq A]
    (χ : ℕ → ℂ) (hχ : ∀ p : Nat.Primes, χ (p : ℕ) ≠ 0) (α : A → ℂ)
    (hdistinct : Function.Injective fun a => (α a).re) (c : ℂ) (hc : c ≠ 0) (m : ℕ) :
    TailCoefficientIndependent
      (fun x : A × Fin (m + 1) => fun p : Nat.Primes =>
        helsonClockJet χ (α x.1) c (x.2 : ℕ) (p : ℕ)) := by
  classical
  have hbase : TailCoefficientIndependent
      (coefficientShiftJet (fun _ : PUnit.{u + 1} => fun p : Nat.Primes => χ (p : ℕ))
        (fun a p => primeShiftFactor (α a) p) primeLogClock m) :=
    tailCoefficientIndependent_phaseShiftJet (J := PUnit.{u + 1}) _ hχ α hdistinct m
  let e : A × Fin (m + 1) ≃ PUnit.{u + 1} × (A × Fin (m + 1)) :=
    { toFun := fun x => (PUnit.unit, x)
      invFun := fun y => y.2
      left_inv := fun _ => rfl
      right_inv := fun y => by cases y.1; rfl }
  have hre := tailCoefficientIndependent_equiv e hbase
  have hclock : ∀ x : A × Fin (m + 1), (c ^ (x.2 : ℕ)) ≠ 0 := fun x => pow_ne_zero _ hc
  have hscaled := (tailCoefficientIndependent_scale_columns_iff
    (fun x : A × Fin (m + 1) => fun p : Nat.Primes =>
      coefficientShiftJet (fun _ : PUnit.{u + 1} => fun p : Nat.Primes => χ (p : ℕ))
        (fun a p => primeShiftFactor (α a) p) primeLogClock m (e x) p)
    (fun x : A × Fin (m + 1) => c ^ (x.2 : ℕ)) hclock).mpr hre
  convert hscaled using 1
  funext x p
  rw [helsonClockJet_apply_prime]
  simp only [coefficientShiftJet, e, Equiv.coe_fn_mk]

/-! ### Algebraic independence of a finite rectangle -/

/-- **A finite shift--jet rectangle of a Helson zeta is algebraically independent over the
finite-prime coefficient field.** -/
theorem helsonClockJets_algebraicIndependent {A : Type u} [Fintype A] [DecidableEq A]
    (χ : ℕ → ℂ) (hχ : ∀ p : Nat.Primes, χ (p : ℕ) ≠ 0) (α : A → ℂ)
    (hdistinct : Function.Injective fun a => (α a).re) (c : ℂ) (hc : c ≠ 0) (m : ℕ) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun x : A × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (helsonClockJet χ (α x.1) c (x.2 : ℕ))) :=
  algebraicIndependent_fractionArithmetic_of_tailIndependent
    (fun x : A × Fin (m + 1) => helsonClockJet χ (α x.1) c (x.2 : ℕ))
    (tailCoefficientIndependent_helsonClockJet χ hχ α hdistinct c hc m)

/-! ### The complete shift--jet family -/

/-- **The complete shift--jet family of a Helson zeta is algebraically independent.**  The shifts
form an arbitrary index set with distinct real parts and the jet order is unbounded. -/
theorem helsonClockJets_algebraicIndependent_all {A : Type u}
    (χ : ℕ → ℂ) (hχ : ∀ p : Nat.Primes, χ (p : ℕ) ≠ 0) (α : A → ℂ)
    (hdistinct : Function.Injective fun a => (α a).re) (c : ℂ) (hc : c ≠ 0) :
    AlgebraicIndependent finitePrimeCoefficientField
      (fun x : A × ℕ =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (helsonClockJet χ (α x.1) c x.2)) := by
  classical
  refine algebraicIndependent_of_finite_subfamilies _ fun S => ?_
  set A' : Finset A := S.image Prod.fst with hA'
  set m : ℕ := (S.image Prod.snd).sup id with hm
  have hrect := helsonClockJets_algebraicIndependent (A := {a : A // a ∈ A'})
    χ hχ (fun a => α (a : A)) (fun a b hab => Subtype.ext (hdistinct hab)) c hc m
  refine hrect.comp (fun i : S =>
      (⟨(i : A × ℕ).1, ?_⟩, (⟨(i : A × ℕ).2, ?_⟩ : Fin (m + 1)))) ?_
  · exact Finset.mem_image_of_mem Prod.fst i.2
  · have hle : (i : A × ℕ).2 ≤ m := by
      rw [hm]
      exact Finset.le_sup (f := id) (Finset.mem_image_of_mem Prod.snd i.2)
    omega
  · intro i j hij
    have h1 : (i : A × ℕ).1 = (j : A × ℕ).1 := congrArg Subtype.val (congrArg Prod.fst hij)
    have h2 : (i : A × ℕ).2 = (j : A × ℕ).2 := by
      have := congrArg Fin.val (congrArg Prod.snd hij)
      simpa using this
    exact Subtype.ext (Prod.ext h1 h2)

/-- **The shifted Helson zeta functions are differentially independent over the finite-prime
coefficient field.** -/
theorem helsonShifts_differentialIndependent {A : Type u}
    (χ : ℕ → ℂ) (hχ : ∀ p : Nat.Primes, χ (p : ℕ) ≠ 0) (α : A → ℂ)
    (hdistinct : Function.Injective fun a => (α a).re) :
    DifferentialIndependent finitePrimeCoefficientField
      (fun a : A => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (helsonClockJet χ (α a) Complex.I 0)) := by
  have h := helsonClockJets_algebraicIndependent_all χ hχ α hdistinct Complex.I Complex.I_ne_zero
  show AlgebraicIndependent finitePrimeCoefficientField
    (fun p : A × ℕ => differentialJet p.2
      (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (helsonClockJet χ (α p.1) Complex.I 0)))
  have hfam : (fun p : A × ℕ => differentialJet p.2
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (helsonClockJet χ (α p.1) Complex.I 0)))
      = fun p : A × ℕ => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (helsonClockJet χ (α p.1) Complex.I p.2) :=
    funext fun p => differentialJet_helsonClockJet χ (α p.1) p.2
  rw [hfam]
  exact h

/-- **Unimodular phases satisfy the hypothesis.** -/
theorem helsonShifts_differentialIndependent_of_unimodular {A : Type u}
    (χ : ℕ → ℂ) (hχ : ∀ p : Nat.Primes, ‖χ (p : ℕ)‖ = 1) (α : A → ℂ)
    (hdistinct : Function.Injective fun a => (α a).re) :
    DifferentialIndependent finitePrimeCoefficientField
      (fun a : A => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (helsonClockJet χ (α a) Complex.I 0)) := by
  refine helsonShifts_differentialIndependent χ ?_ α hdistinct
  intro p hzero
  have := hχ p
  rw [hzero, norm_zero] at this
  exact zero_ne_one this

/-! ### The labelled isomorphism of two Helson differential fields -/

/-- **The universal labelled differential-field type of Helson zeta functions.**  For any two
nowhere-vanishing phases and any shift family with distinct real parts, the differential fields
generated over the finite-prime coefficient field by the shifted Helson zeta functions are
canonically isomorphic, by the map that carries each labelled generator to its counterpart. -/
def helsonLabelledAlgEquiv {A : Type u} (χ ψ : ℕ → ℂ)
    (hχ : ∀ p : Nat.Primes, χ (p : ℕ) ≠ 0) (hψ : ∀ p : Nat.Primes, ψ (p : ℕ) ≠ 0)
    (α : A → ℂ) (hdistinct : Function.Injective fun a => (α a).re) :
    differentialAdjoin finitePrimeCoefficientField
        (Set.range fun a : A => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (helsonClockJet χ (α a) Complex.I 0))
      ≃ₐ[finitePrimeCoefficientField]
      differentialAdjoin finitePrimeCoefficientField
        (Set.range fun a : A => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (helsonClockJet ψ (α a) Complex.I 0)) :=
  differentialIndependentAdjoinAlgEquiv _ _
    (helsonShifts_differentialIndependent χ hχ α hdistinct)
    (helsonShifts_differentialIndependent ψ hψ α hdistinct)

/-- The labelled isomorphism carries every jet of a generator to the corresponding jet. -/
theorem helsonLabelledAlgEquiv_jet {A : Type u} (χ ψ : ℕ → ℂ)
    (hχ : ∀ p : Nat.Primes, χ (p : ℕ) ≠ 0) (hψ : ∀ p : Nat.Primes, ψ (p : ℕ) ≠ 0)
    (α : A → ℂ) (hdistinct : Function.Injective fun a => (α a).re) (a : A) (n : ℕ) :
    (helsonLabelledAlgEquiv χ ψ hχ hψ α hdistinct
        ⟨differentialJet n (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (helsonClockJet χ (α a) Complex.I 0)),
          differentialJet_mem_differentialAdjoin finitePrimeCoefficientField
            (Set.mem_range_self a) n⟩ : _)
      = ⟨differentialJet n (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (helsonClockJet ψ (α a) Complex.I 0)),
          differentialJet_mem_differentialAdjoin finitePrimeCoefficientField
            (Set.mem_range_self a) n⟩ :=
  differentialIndependentAdjoinAlgEquiv_jet _ _
    (helsonShifts_differentialIndependent χ hχ α hdistinct)
    (helsonShifts_differentialIndependent ψ hψ α hdistinct) a n

end

end GaloisForLFunctions.HTGeometry
