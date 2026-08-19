import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import GaloisForLFunctions.HTGeometry.TriangularSubstitution

/-!
# Logarithmic jets of a rescaled substitution

Substituting a nonconstant rational change of variable `r` into a function does not commute with
differentiation; it rescales it, `(f ∘ r)' = r' · (f' ∘ r)`.  The algebraic shadow of that
situation is a field automorphism `σ` of a differential field which carries the coefficient field
onto itself and intertwines the derivation up to a nonzero coefficient factor.

The iterated derivatives of `σ x` are then a triangular coefficient combination of the images
under `σ` of the iterated derivatives of `x`, with diagonal the powers of the factor.  The
substitution therefore preserves differential algebraicity and hypertranscendence exactly.

Composing with the exact logarithmic-derivative equivalence gives the transfer law for the
**logarithmic jet** `J(x) = r' · (x'/x) ∘ r`: it is hypertranscendental over the coefficient field
exactly when `x` is.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-! ## The finite-jet polynomial form of differential algebraicity -/

section FinPoly

variable [Differential E]

/-- Differential algebraicity is the existence of a nonzero polynomial relation among finitely
many consecutive jets, with coefficients in the base field. -/
theorem differentialAlgebraicOver_iff_exists_finPoly (x : E) :
    DifferentialAlgebraicOver F x ↔
      ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 1)) F), P ≠ 0 ∧
        MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) P = 0 := by
  classical
  constructor
  · intro h
    rw [DifferentialAlgebraicOver, DifferentialIndependent, algebraicIndependent_iff] at h
    obtain ⟨P, hPeval, hPne⟩ :
        ∃ P : MvPolynomial (Unit × ℕ) F,
          MvPolynomial.aeval (fun p : Unit × ℕ => differentialJet p.2 x) P = 0 ∧ P ≠ 0 := by
      by_contra hc
      exact h fun p hp => by
        by_contra hpne
        exact hc ⟨p, hp, hpne⟩
    obtain ⟨m, f, hf, q, hq⟩ := MvPolynomial.exists_fin_rename P
    set n : ℕ := Finset.univ.sup fun i : Fin m => (f i).2 with hn
    have hlt : ∀ i : Fin m, (f i).2 < n + 1 := by
      intro i
      have := Finset.le_sup (f := fun i : Fin m => (f i).2) (Finset.mem_univ i)
      omega
    refine ⟨n, MvPolynomial.rename (fun i : Fin m => (⟨(f i).2, hlt i⟩ : Fin (n + 1))) q, ?_, ?_⟩
    · have hqne : q ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hq
        exact hPne hq
      refine fun h0 => hqne (MvPolynomial.rename_injective _ ?_ (by rw [h0, map_zero]))
      intro i j hij
      have h2 : (f i).2 = (f j).2 := by simpa using congrArg Fin.val hij
      exact hf (Prod.ext (Subsingleton.elim _ _) h2)
    · rw [MvPolynomial.aeval_rename]
      have hcomp :
          ((fun j : Fin (n + 1) => differentialJet (j : ℕ) x) ∘
            fun i : Fin m => (⟨(f i).2, hlt i⟩ : Fin (n + 1)))
            = (fun p : Unit × ℕ => differentialJet p.2 x) ∘ f := by
        funext i; rfl
      rw [hcomp, ← MvPolynomial.aeval_rename, ← hq]
      exact hPeval
  · rintro ⟨n, P, hP0, hPeval⟩
    rw [DifferentialAlgebraicOver, DifferentialIndependent, algebraicIndependent_iff]
    intro hind
    have hginj : Function.Injective (fun j : Fin (n + 1) => ((), (j : ℕ))) := by
      intro i j hij
      exact Fin.ext (congrArg Prod.snd hij)
    have hzero := hind (MvPolynomial.rename (fun j : Fin (n + 1) => ((), (j : ℕ))) P)
      (by rw [MvPolynomial.aeval_rename]; exact hPeval)
    exact hP0 (MvPolynomial.rename_injective _ hginj (by rw [hzero, map_zero]))

end FinPoly

/-! ## Rescaled substitution automorphisms -/

/-- A **rescaled differential automorphism**: a field automorphism of the ambient field which
carries the coefficient field onto itself and intertwines the derivation up to a nonzero
coefficient factor.  This is the algebraic form of substitution by a nonconstant rational change
of variable, for which `(f ∘ r)' = r' · (f' ∘ r)`. -/
structure DifferentialRescaledEquiv (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] where
  /-- The induced automorphism of the coefficient field. -/
  baseEquiv : F ≃+* F
  /-- The automorphism of the ambient field. -/
  ambientEquiv : E ≃+* E
  /-- The rescaling factor, a nonzero element of the coefficient field. -/
  factor : F
  factor_ne_zero : factor ≠ 0
  map_algebraMap' : ∀ c : F, ambientEquiv (algebraMap F E c) = algebraMap F E (baseEquiv c)
  map_deriv' : ∀ x : E,
    (ambientEquiv x)′ = algebraMap F E factor * ambientEquiv (x′)

namespace DifferentialRescaledEquiv

variable [Differential F] [Differential E]

/-- The inverse automorphism carries the embedded coefficient field onto itself through the
inverse base automorphism. -/
theorem ambientEquiv_symm_algebraMap (σ : DifferentialRescaledEquiv F E) (c : F) :
    σ.ambientEquiv.symm (algebraMap F E c) = algebraMap F E (σ.baseEquiv.symm c) := by
  have h := σ.map_algebraMap' (σ.baseEquiv.symm c)
  rw [RingEquiv.apply_symm_apply] at h
  rw [← h, RingEquiv.symm_apply_apply]

/-- The inverse substitution is again a rescaled differential automorphism, with the inverted
factor transported through the base automorphism. -/
def symm (σ : DifferentialRescaledEquiv F E) : DifferentialRescaledEquiv F E where
  baseEquiv := σ.baseEquiv.symm
  ambientEquiv := σ.ambientEquiv.symm
  factor := σ.baseEquiv.symm σ.factor⁻¹
  factor_ne_zero := by
    simp only [ne_eq, map_eq_zero_iff _ σ.baseEquiv.symm.injective, inv_eq_zero]
    exact σ.factor_ne_zero
  map_algebraMap' := σ.ambientEquiv_symm_algebraMap
  map_deriv' := by
    intro x
    have hne : (algebraMap F E σ.factor) ≠ 0 := by
      simpa using (map_ne_zero_iff _ (algebraMap F E).injective).mpr σ.factor_ne_zero
    have h := σ.map_deriv' (σ.ambientEquiv.symm x)
    rw [RingEquiv.apply_symm_apply] at h
    have h2 : σ.ambientEquiv ((σ.ambientEquiv.symm x)′)
        = (algebraMap F E σ.factor)⁻¹ * x′ := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    have h3 : (σ.ambientEquiv.symm x)′
        = σ.ambientEquiv.symm ((algebraMap F E σ.factor)⁻¹ * x′) := by
      rw [← h2, RingEquiv.symm_apply_apply]
    rw [h3, map_mul, map_inv₀]
    congr 1
    rw [σ.ambientEquiv_symm_algebraMap, map_inv₀ σ.baseEquiv.symm, map_inv₀ (algebraMap F E)]

@[simp] theorem symm_ambientEquiv (σ : DifferentialRescaledEquiv F E) :
    σ.symm.ambientEquiv = σ.ambientEquiv.symm := rfl

/-- The conjugated derivation `σ ∘ d ∘ σ⁻¹`. -/
def conjDeriv (σ : DifferentialRescaledEquiv F E) : Derivation ℤ E E :=
  Derivation.mk'
    (({ toFun := fun y => σ.ambientEquiv ((σ.ambientEquiv.symm y)′)
        map_zero' := by simp
        map_add' := fun a b => by simp } : E →+ E).toIntLinearMap)
    (by
      intro a b
      show σ.ambientEquiv ((σ.ambientEquiv.symm (a * b))′)
        = a • σ.ambientEquiv ((σ.ambientEquiv.symm b)′)
          + b • σ.ambientEquiv ((σ.ambientEquiv.symm a)′)
      rw [map_mul, Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, RingEquiv.apply_symm_apply])

@[simp] theorem conjDeriv_apply (σ : DifferentialRescaledEquiv F E) (y : E) :
    σ.conjDeriv y = σ.ambientEquiv ((σ.ambientEquiv.symm y)′) := rfl

/-- The ambient derivation is the conjugated derivation rescaled by the factor. -/
theorem deriv_eq_factor_mul_conjDeriv (σ : DifferentialRescaledEquiv F E) (y : E) :
    y′ = algebraMap F E σ.factor * σ.conjDeriv y := by
  have h := σ.map_deriv' (σ.ambientEquiv.symm y)
  rw [RingEquiv.apply_symm_apply] at h
  simpa using h

/-- The conjugated derivation is the ambient derivation rescaled by the inverted factor. -/
theorem conjDeriv_eq_inv_factor_mul_deriv (σ : DifferentialRescaledEquiv F E) (y : E) :
    σ.conjDeriv y = algebraMap F E σ.factor⁻¹ * y′ := by
  have hne : (algebraMap F E σ.factor) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F E).injective).mpr σ.factor_ne_zero
  rw [deriv_eq_factor_mul_conjDeriv σ y, map_inv₀]
  field_simp

/-- The conjugated derivation transports the jets of `x` to the jets of `σ x`. -/
theorem conjDeriv_iterate_map (σ : DifferentialRescaledEquiv F E) (n : ℕ) (x : E) :
    ((σ.conjDeriv : E → E))^[n] (σ.ambientEquiv x) = σ.ambientEquiv (differentialJet n x) := by
  induction n with
  | zero => simp [differentialJet]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, differentialJet_succ]
      show σ.ambientEquiv ((σ.ambientEquiv.symm (σ.ambientEquiv (differentialJet n x)))′) = _
      rw [RingEquiv.symm_apply_apply]

end DifferentialRescaledEquiv

/-! ## The triangular expansion -/

/-- **Triangular expansion of a rescaled derivation.**  If a derivation `d₁` is the rescaling of a
map `d₂` by a nonzero coefficient `c`, and `d₁` preserves the coefficient field, then the iterates
of `d₁` are a triangular coefficient combination of the iterates of `d₂` with diagonal `cⁿ`. -/
theorem exists_triangular_expansion
    (d₁ : Derivation ℤ E E) (d₂ : E → E) (c : F) (dF : F → F)
    (hstep : ∀ y : E, d₁ y = algebraMap F E c * d₂ y)
    (hbase : ∀ a : F, d₁ (algebraMap F E a) = algebraMap F E (dF a)) (n : ℕ) :
    ∃ a : ℕ → F, a n = c ^ n ∧ (∀ j, n < j → a j = 0) ∧
      ∀ y : E, ((d₁ : E → E))^[n] y
        = ∑ j ∈ Finset.range (n + 1), algebraMap F E (a j) * d₂^[j] y := by
  have hdF0 : dF 0 = 0 := by
    have h := hbase 0
    rw [map_zero, map_zero] at h
    have h' : (algebraMap F E) (dF 0) = (algebraMap F E) 0 := by rw [map_zero]; exact h.symm
    exact (algebraMap F E).injective h'
  induction n with
  | zero =>
      refine ⟨fun j => if j = 0 then 1 else 0, by simp, ?_, ?_⟩
      · intro j hj
        have hj0 : j ≠ 0 := Nat.ne_of_gt hj
        simp [hj0]
      · intro y
        simp
  | succ n ih =>
      obtain ⟨a, hdiag, hzero, hexp⟩ := ih
      refine ⟨fun j => match j with
        | 0 => dF (a 0)
        | (i + 1) => dF (a (i + 1)) + c * a i, ?_, ?_, ?_⟩
      · show dF (a (n + 1)) + c * a n = c ^ (n + 1)
        rw [hzero (n + 1) (by omega), hdF0, hdiag]
        ring
      · intro j hj
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        show dF (a (i + 1)) + c * a i = 0
        rw [hzero (i + 1) (by omega), hzero i (by omega), hdF0]
        ring
      · intro y
        rw [Function.iterate_succ_apply', hexp y, map_sum]
        have hterm : ∀ j : ℕ, d₁ (algebraMap F E (a j) * d₂^[j] y)
            = algebraMap F E (dF (a j)) * d₂^[j] y
              + algebraMap F E (c * a j) * d₂^[j + 1] y := by
          intro j
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hbase (a j),
            hstep (d₂^[j] y), ← Function.iterate_succ_apply' d₂, map_mul]
          ring
        rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib]
        rw [Finset.sum_range_succ' (fun k => algebraMap F E
          ((fun j => match j with
            | 0 => dF (a 0)
            | (i + 1) => dF (a (i + 1)) + c * a i) k) * d₂^[k] y) (n + 1)]
        have hsplit : ∀ i : ℕ,
            algebraMap F E (dF (a (i + 1)) + c * a i) * d₂^[i + 1] y
              = algebraMap F E (dF (a (i + 1))) * d₂^[i + 1] y
                + algebraMap F E (c * a i) * d₂^[i + 1] y := by
          intro i
          rw [map_add]
          ring
        rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
        have hdFsum : (∑ i ∈ Finset.range (n + 1),
              algebraMap F E (dF (a (i + 1))) * d₂^[i + 1] y)
              + algebraMap F E (dF (a 0)) * d₂^[0] y
            = ∑ j ∈ Finset.range (n + 1), algebraMap F E (dF (a j)) * d₂^[j] y := by
          rw [← Finset.sum_range_succ' (fun k => algebraMap F E (dF (a k)) * d₂^[k] y) (n + 1),
            Finset.sum_range_succ]
          rw [hzero (n + 1) (by omega), hdF0, map_zero, zero_mul, add_zero]
        show _ = (∑ i ∈ Finset.range (n + 1), algebraMap F E (dF (a (i + 1))) * d₂^[i + 1] y
            + ∑ i ∈ Finset.range (n + 1), algebraMap F E (c * a i) * d₂^[i + 1] y)
            + algebraMap F E (dF (a 0)) * d₂^[0] y
        rw [← hdFsum]
        ring

/-! ## Exact transfer of differential algebraicity -/

namespace DifferentialRescaledEquiv

variable [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- The conjugated derivation preserves the embedded coefficient field. -/
theorem conjDeriv_algebraMap (σ : DifferentialRescaledEquiv F E) (a : F) :
    σ.conjDeriv (algebraMap F E a) = algebraMap F E (σ.factor⁻¹ * a′) := by
  rw [conjDeriv_eq_inv_factor_mul_deriv, deriv_algebraMap, ← map_mul]

/-- The images under `σ` of the jets of `x` are a triangular coefficient combination of the jets
of `σ x`, with diagonal the inverse powers of the factor. -/
theorem exists_map_jet_expansion (σ : DifferentialRescaledEquiv F E) (n : ℕ) :
    ∃ b : ℕ → F, b n = (σ.factor⁻¹) ^ n ∧ (∀ j, n < j → b j = 0) ∧
      ∀ x : E, σ.ambientEquiv (differentialJet n x)
        = ∑ j ∈ Finset.range (n + 1), algebraMap F E (b j) * differentialJet j (σ.ambientEquiv x) := by
  obtain ⟨b, hdiag, hzero, hexp⟩ :=
    exists_triangular_expansion (F := F) σ.conjDeriv (fun y : E => y′) σ.factor⁻¹
      (fun a : F => σ.factor⁻¹ * a′) σ.conjDeriv_eq_inv_factor_mul_deriv
      σ.conjDeriv_algebraMap n
  refine ⟨b, hdiag, hzero, fun x => ?_⟩
  have h := hexp (σ.ambientEquiv x)
  rw [σ.conjDeriv_iterate_map n x] at h
  exact h

/-- **Differential algebraicity is preserved by a rescaled substitution automorphism.** -/
theorem differentialAlgebraicOver_map (σ : DifferentialRescaledEquiv F E) {x : E}
    (h : DifferentialAlgebraicOver F x) :
    DifferentialAlgebraicOver F (σ.ambientEquiv x) := by
  classical
  rw [differentialAlgebraicOver_iff_exists_finPoly] at h ⊢
  obtain ⟨n, P, hP0, hPeval⟩ := h
  choose b hbdiag hbzero hbexp using fun j : ℕ => σ.exists_map_jet_expansion j
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun j i => b (j : ℕ) (i : ℕ) with hM
  have hfinv : σ.factor⁻¹ ≠ 0 := inv_ne_zero σ.factor_ne_zero
  have htri : ∀ i j : Fin (n + 1), j < i → M j i = 0 := by
    intro i j hji
    exact hbzero (j : ℕ) (i : ℕ) (by exact_mod_cast hji)
  have hdiag : ∀ i : Fin (n + 1), IsUnit (M i i) := by
    intro i
    rw [hM]
    show IsUnit (b (i : ℕ) (i : ℕ))
    rw [hbdiag (i : ℕ)]
    exact (isUnit_iff_ne_zero).mpr (pow_ne_zero _ hfinv)
  have hdet : IsUnit M.det := isUnit_det_of_lowerTriangular htri hdiag
  -- the row identity: `σ` of a jet of `x` in terms of the jets of `σ x`
  have hrow : ∀ j : Fin (n + 1), σ.ambientEquiv (differentialJet (j : ℕ) x)
      = ∑ i : Fin (n + 1), algebraMap F E (M j i) * differentialJet (i : ℕ) (σ.ambientEquiv x) := by
    intro j
    have hMj : ∀ i : Fin (n + 1), M j i = b (j : ℕ) (i : ℕ) := fun _ => rfl
    rw [hbexp (j : ℕ) x]
    simp only [hMj]
    rw [Fin.sum_univ_eq_sum_range
        (fun k : ℕ => algebraMap F E (b (j : ℕ) k) * differentialJet k (σ.ambientEquiv x)) (n + 1)]
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      have hjn : (j : ℕ) ≤ n := j.is_le
      omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [hbzero (j : ℕ) k (by omega), map_zero, zero_mul]
  -- transport the relation through the ring automorphism
  set Q : MvPolynomial (Fin (n + 1)) F := MvPolynomial.map (σ.baseEquiv : F →+* F) P with hQ
  have hQ0 : Q ≠ 0 := by
    intro h0
    exact hP0 (MvPolynomial.map_injective (σ.baseEquiv : F →+* F) σ.baseEquiv.injective
      (by rw [← hQ, h0, map_zero]))
  have hQeval :
      MvPolynomial.aeval (fun j : Fin (n + 1) => σ.ambientEquiv (differentialJet (j : ℕ) x)) Q
        = σ.ambientEquiv
          (MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) P) := by
    have key :
        ((MvPolynomial.aeval
            (fun j : Fin (n + 1) => σ.ambientEquiv (differentialJet (j : ℕ) x)) :
              MvPolynomial (Fin (n + 1)) F →ₐ[F] E) : MvPolynomial (Fin (n + 1)) F →+* E).comp
          (MvPolynomial.map (σ.baseEquiv : F →+* F))
        = (σ.ambientEquiv : E →+* E).comp
          ((MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) :
              MvPolynomial (Fin (n + 1)) F →ₐ[F] E) : MvPolynomial (Fin (n + 1)) F →+* E) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [σ.map_algebraMap']
      · simp
    exact congrArg (fun f : MvPolynomial (Fin (n + 1)) F →+* E => f P) key
  refine ⟨n, linSub M Q, fun h0 => hQ0 (linSub_injective hdet (by rw [h0, map_zero])), ?_⟩
  have hcomp :
      ((MvPolynomial.aeval
          (fun i : Fin (n + 1) => differentialJet (i : ℕ) (σ.ambientEquiv x)) :
            MvPolynomial (Fin (n + 1)) F →ₐ[F] E).comp (linSub M))
        = MvPolynomial.aeval
          (fun j : Fin (n + 1) => σ.ambientEquiv (differentialJet (j : ℕ) x)) := by
    refine MvPolynomial.algHom_ext (fun j => ?_)
    simp [linSub_X, map_sum, hrow j]
  have := congrArg (fun f : MvPolynomial (Fin (n + 1)) F →ₐ[F] E => f Q) hcomp
  simp only [AlgHom.coe_comp, Function.comp_apply] at this
  rw [this, hQeval, hPeval, map_zero]

/-- **Differential algebraicity is exactly invariant under a rescaled substitution
automorphism.** -/
theorem differentialAlgebraicOver_map_iff (σ : DifferentialRescaledEquiv F E) (x : E) :
    DifferentialAlgebraicOver F (σ.ambientEquiv x) ↔ DifferentialAlgebraicOver F x := by
  constructor
  · intro h
    have h2 := σ.symm.differentialAlgebraicOver_map h
    simpa using h2
  · exact fun h => σ.differentialAlgebraicOver_map h

/-- **Hypertranscendence is exactly invariant under a rescaled substitution automorphism.** -/
theorem hypertranscendentalOver_map_iff (σ : DifferentialRescaledEquiv F E) (x : E) :
    HypertranscendentalOver F (σ.ambientEquiv x) ↔ HypertranscendentalOver F x :=
  not_congr (σ.differentialAlgebraicOver_map_iff x)

end DifferentialRescaledEquiv

/-! ## The logarithmic jet -/

namespace DifferentialRescaledEquiv

variable [Differential F] [Differential E] [DifferentialAlgebra F E]

/-- The **logarithmic jet** of a rescaled substitution: the algebraic form of
`J_r(f) = r' · (f'/f) ∘ r`. -/
def mobiusJet (σ : DifferentialRescaledEquiv F E) (x : E) : E :=
  algebraMap F E σ.factor * σ.ambientEquiv (x′ / x)

omit [DifferentialAlgebra F E] in
/-- The logarithmic jet is the logarithmic derivative of the substituted element: the chain rule
`(f ∘ r)' / (f ∘ r) = r' · (f'/f) ∘ r`. -/
theorem mobiusJet_eq_logDeriv (σ : DifferentialRescaledEquiv F E) (x : E) :
    σ.mobiusJet x = (σ.ambientEquiv x)′ / σ.ambientEquiv x := by
  rw [mobiusJet, σ.map_deriv' x, map_div₀, mul_div_assoc]

/-- **Möbius logarithmic-jet transfer, hypertranscendental form.**  The logarithmic jet of a
rescaled substitution is hypertranscendental over the coefficient field exactly when the element
is. -/
theorem hypertranscendentalOver_mobiusJet_iff [CharZero F] [CharZero E]
    (σ : DifferentialRescaledEquiv F E) (x : E) :
    HypertranscendentalOver F (σ.mobiusJet x) ↔ HypertranscendentalOver F x := by
  rw [mobiusJet_eq_logDeriv, hypertranscendentalOver_deriv_div_self_iff,
    σ.hypertranscendentalOver_map_iff]

/-- **Möbius logarithmic-jet transfer, differentially algebraic form.** -/
theorem differentialAlgebraicOver_mobiusJet_iff [CharZero F] [CharZero E]
    (σ : DifferentialRescaledEquiv F E) (x : E) :
    DifferentialAlgebraicOver F (σ.mobiusJet x) ↔ DifferentialAlgebraicOver F x := by
  simpa only [HypertranscendentalOver, not_not] using
    not_congr (σ.hypertranscendentalOver_mobiusJet_iff x)

/-- The logarithmic derivative itself transfers: `x'/x` is hypertranscendental exactly when the
logarithmic jet of the substitution is. -/
theorem hypertranscendentalOver_mobiusJet_iff_logDeriv [CharZero F] [CharZero E]
    (σ : DifferentialRescaledEquiv F E) (x : E) :
    HypertranscendentalOver F (σ.mobiusJet x) ↔ HypertranscendentalOver F (x′ / x) :=
  (σ.hypertranscendentalOver_mobiusJet_iff x).trans
    (hypertranscendentalOver_deriv_div_self_iff x).symm

end DifferentialRescaledEquiv

end

end GaloisForLFunctions.HTGeometry
