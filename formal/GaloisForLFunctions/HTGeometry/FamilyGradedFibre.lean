import GaloisForLFunctions.HTGeometry.FamilyDegreeFinite
import GaloisForLFunctions.HTGeometry.GradedPieceFinite
import GaloisForLFunctions.HTGeometry.FamilyIdealXGraded
import GaloisForLFunctions.HTGeometry.SaturatedFibreStep
import GaloisForLFunctions.HTGeometry.GradedMultiplication
import GaloisForLFunctions.HTGeometry.FibreNoTorsion

/-!
# The graded pieces of a family, and the Hilbert function of its fibres

A graded piece of the family is a free module over the base line on the monomials of that degree, so
it is modelled by coefficient arrays:

```text
famCoeff, famAssemble             coefficient arrays and the polynomial they assemble
exists_famAssemble_of_isXHomog    every x-homogeneous element comes from an array
famCoeffPart                      the arrays whose polynomial lies in the ideal
famFibreEval                      evaluation of an array at a point of the base line
ker_famFibreQuot                  ** the kernel of evaluation into the fibre is the graded part of
                                     the ideal, up to the linear factor of the point **
finrank_quotDegreePart_eq_fibre   ** hence the fibre of the graded piece is the graded piece of the
                                     fibre **
finrank_quotDegreePart_fibre_eq   ** and saturation at two points makes the two fibres have the same
                                     Hilbert function **
```

Working with coefficient arrays rather than with the submodule of `x`-homogeneous polynomials keeps
the module a plain finite product over the base line, which is what the structure theorem behind
`finrank_fibre_eq_of_smul_injective` consumes.

The kernel computation is where `x`-gradedness of the ideal is used: an element of the fibre ideal in
degree `e` lifts to an element of the ideal, whose degree-`e` part is again in the ideal and has the
same value at the point; the difference then has every coefficient vanishing at the point, so it is
divisible by the linear factor.
-/

namespace GaloisForLFunctions.HTGeometry
open MvPolynomial Module

universe u
variable {K : Type u} [Field K] {N e : ℕ}

/-- Coefficient arrays on the monomials of one degree: the model of a graded piece of the family. -/
abbrev famCoeff (K : Type u) [Field K] (N e : ℕ) : Type u :=
  (↥(degreeExponents N e) → Polynomial K)

/-- Assembling a coefficient array into a polynomial of the family. -/
noncomputable def famAssemble (K : Type u) [Field K] (N e : ℕ) :
    famCoeff K N e →ₗ[Polynomial K] Polynomial (MvPolynomial (Fin N) K) where
  toFun c := ∑ α : ↥(degreeExponents N e),
    (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)) (c α))
      * Polynomial.C (MvPolynomial.monomial (α : Fin N →₀ ℕ) (1 : K))
  map_add' c d := by
    simp only [Pi.add_apply, map_add, add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring

theorem coeff_famAssemble (c : famCoeff K N e) (j : ℕ) :
    (famAssemble K N e c).coeff j
      = ∑ α : ↥(degreeExponents N e),
          MvPolynomial.monomial (α : Fin N →₀ ℕ) ((c α).coeff j) := by
  show (∑ α : ↥(degreeExponents N e),
    (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)) (c α))
      * Polynomial.C (MvPolynomial.monomial (α : Fin N →₀ ℕ) (1 : K))).coeff j = _
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Polynomial.coeff_mul_C]
  show (Polynomial.map (MvPolynomial.C : K →+* MvPolynomial (Fin N) K) (c α)).coeff j * _ = _
  rw [Polynomial.coeff_map, MvPolynomial.C_mul_monomial, mul_one]

theorem isXHomog_famAssemble (c : famCoeff K N e) : IsXHomog e (famAssemble K N e c) := by
  intro j
  rw [coeff_famAssemble]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun α _ => ?_
  exact MvPolynomial.isHomogeneous_monomial ((c α).coeff j) (mem_degreeExponents.mp α.2)

theorem eval_famAssemble (lam : K) (c : famCoeff K N e) :
    Polynomial.eval (MvPolynomial.C lam) (famAssemble K N e c)
      = ∑ α : ↥(degreeExponents N e),
          MvPolynomial.monomial (α : Fin N →₀ ℕ) ((c α).eval lam) := by
  show Polynomial.eval (MvPolynomial.C lam) (∑ α : ↥(degreeExponents N e),
    (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)) (c α))
      * Polynomial.C (MvPolynomial.monomial (α : Fin N →₀ ℕ) (1 : K))) = _
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hmap : (algebraMap (Polynomial K) (Polynomial (MvPolynomial (Fin N) K)) (c α))
      = Polynomial.map (MvPolynomial.C : K →+* MvPolynomial (Fin N) K) (c α) := rfl
  rw [hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, MvPolynomial.C_mul_monomial, mul_one]



theorem exists_famAssemble_of_isXHomog {F : Polynomial (MvPolynomial (Fin N) K)}
    (hF : IsXHomog e F) : ∃ c : famCoeff K N e, famAssemble K N e c = F := by
  classical
  refine ⟨fun α => coeffPoly F (α : Fin N →₀ ℕ), Polynomial.ext fun j => ?_⟩
  rw [coeff_famAssemble]
  have hsupp : (F.coeff j).support ⊆ degreeExponents N e := by
    intro γ hγ
    refine mem_degreeExponents.mpr ?_
    have hw := (hF j) (MvPolynomial.mem_support_iff.mp hγ)
    rwa [weight_one_eq_degree] at hw
  rw [← sum_monomial_coeff_of_subset hsupp, ← Finset.sum_coe_sort (degreeExponents N e)]
  exact Finset.sum_congr rfl fun α _ => by rw [coeffPoly_coeff]

/-- Evaluating the family at a point of the base line commutes with taking `x`-homogeneous parts. -/
theorem eval_C_xComp (lam : K) (e : ℕ) (F : Polynomial (MvPolynomial (Fin N) K)) :
    Polynomial.eval (MvPolynomial.C lam) (xComp e F)
      = MvPolynomial.homogeneousComponent e (Polynomial.eval (MvPolynomial.C lam) F) := by
  classical
  have hsum : ∀ G : Polynomial (MvPolynomial (Fin N) K), ∀ s : Finset ℕ, G.support ⊆ s →
      Polynomial.eval (MvPolynomial.C lam) G
        = ∑ j ∈ s, G.coeff j * (MvPolynomial.C lam) ^ j := by
    intro G s hs
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    refine Finset.sum_subset hs fun j _ hj => ?_
    rw [Polynomial.notMem_support_iff.mp hj, zero_mul]
  rw [hsum _ F.support (le_refl _), hsum (xComp e F) F.support (support_xComp_subset e F), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [xComp_coeff, ← MvPolynomial.C_pow,
    mul_comm (MvPolynomial.homogeneousComponent e (F.coeff j)) (MvPolynomial.C (lam ^ j)),
    mul_comm (F.coeff j) (MvPolynomial.C (lam ^ j)), MvPolynomial.homogeneousComponent_C_mul]

/-- The part of an ideal of the family ring in one `x`-degree, read on coefficient arrays. -/
noncomputable def famCoeffPart (A : Ideal (Polynomial (MvPolynomial (Fin N) K))) (e : ℕ) :
    Submodule (Polynomial K) (famCoeff K N e) :=
  Submodule.comap (famAssemble K N e) (A.restrictScalars (Polynomial K))

theorem mem_famCoeffPart {A : Ideal (Polynomial (MvPolynomial (Fin N) K))} {e : ℕ}
    {c : famCoeff K N e} : c ∈ famCoeffPart A e ↔ famAssemble K N e c ∈ A := Iff.rfl

/-- Evaluating a coefficient array at a point of the base line. -/
noncomputable def famFibreEval (K : Type u) [Field K] (N e : ℕ) (lam : K) :
    famCoeff K N e →ₗ[K] homogeneousSubmodule (Fin N) K e where
  toFun c := ⟨∑ α : ↥(degreeExponents N e),
      MvPolynomial.monomial (α : Fin N →₀ ℕ) ((c α).eval lam), by
    refine Submodule.sum_mem _ fun α _ => ?_
    exact MvPolynomial.isHomogeneous_monomial ((c α).eval lam) (mem_degreeExponents.mp α.2)⟩
  map_add' c d := by
    refine Subtype.ext ?_
    show (∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
      (((c + d) α).eval lam)) = _
    rw [Submodule.coe_add]
    show _ = (∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
      ((c α).eval lam)) + ∑ α : ↥(degreeExponents N e), MvPolynomial.monomial
        (α : Fin N →₀ ℕ) ((d α).eval lam)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    show MvPolynomial.monomial (α : Fin N →₀ ℕ) (Polynomial.eval lam (c α + d α)) = _
    rw [Polynomial.eval_add, map_add]
  map_smul' r c := by
    refine Subtype.ext ?_
    show (∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
      (((r • c) α).eval lam)) = _
    rw [RingHom.id_apply, Submodule.coe_smul]
    show _ = r • ∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
      ((c α).eval lam)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.smul_monomial]
    congr 1
    show ((r • c α).eval lam) = r * (c α).eval lam
    rw [Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

theorem coe_famFibreEval (lam : K) (c : famCoeff K N e) :
    (famFibreEval K N e lam c : MvPolynomial (Fin N) K)
      = Polynomial.eval (MvPolynomial.C lam) (famAssemble K N e c) := by
  rw [eval_famAssemble]
  rfl

theorem famFibreEval_surjective (lam : K) :
    Function.Surjective (famFibreEval K N e lam) := by
  classical
  intro p
  refine ⟨fun α => Polynomial.C (MvPolynomial.coeff (α : Fin N →₀ ℕ) (p : MvPolynomial (Fin N) K)),
    Subtype.ext ?_⟩
  show (∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
    ((Polynomial.C (MvPolynomial.coeff (α : Fin N →₀ ℕ)
      (p : MvPolynomial (Fin N) K))).eval lam)) = _
  have hsupp : (p : MvPolynomial (Fin N) K).support ⊆ degreeExponents N e := by
    intro γ hγ
    refine mem_degreeExponents.mpr ?_
    have hw := p.2 (MvPolynomial.mem_support_iff.mp hγ)
    rwa [weight_one_eq_degree] at hw
  have hstep : (∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
      ((Polynomial.C (MvPolynomial.coeff (α : Fin N →₀ ℕ)
        (p : MvPolynomial (Fin N) K))).eval lam))
      = ∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
          (MvPolynomial.coeff (α : Fin N →₀ ℕ) (p : MvPolynomial (Fin N) K)) :=
    Finset.sum_congr rfl fun α _ => by rw [Polynomial.eval_C]
  rw [hstep, Finset.sum_coe_sort (degreeExponents N e)
    (fun α => MvPolynomial.monomial α (MvPolynomial.coeff α (p : MvPolynomial (Fin N) K)))]
  exact sum_monomial_coeff_of_subset hsupp


theorem coeff_sum_monomial_subtype (a : ↥(degreeExponents N e) → K) (β : ↥(degreeExponents N e)) :
    MvPolynomial.coeff (β : Fin N →₀ ℕ) (∑ α : ↥(degreeExponents N e),
      MvPolynomial.monomial (α : Fin N →₀ ℕ) (a α)) = a β := by
  classical
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single β]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro α _ hα
    rw [MvPolynomial.coeff_monomial, if_neg ?_]
    intro hcon
    exact hα (Subtype.ext hcon)
  · intro hβ
    exact absurd (Finset.mem_univ β) hβ

theorem famAssemble_smul (r : Polynomial K) (c : famCoeff K N e) :
    famAssemble K N e (r • c)
      = (Polynomial.map (MvPolynomial.C : K →+* MvPolynomial (Fin N) K) r)
        * famAssemble K N e c := by
  rw [map_smul, Algebra.smul_def]
  rfl

/-- **The kernel of the fibre evaluation.**  A coefficient array evaluates into the fibre ideal
exactly when it lies in the graded part of the family ideal, up to a multiple of the linear factor
of the point. -/
theorem ker_famFibreQuot (A : Ideal (Polynomial (MvPolynomial (Fin N) K)))
    (hA : IsXGradedIdeal A) (e : ℕ) (lam : K) :
    LinearMap.ker ((Submodule.mkQ (degreePart
        ((Ideal.map (famEval (MvPolynomial.C lam)) A).restrictScalars K) e)).comp
      (famFibreEval K N e lam))
      = Submodule.restrictScalars K (famCoeffPart A e ⊔
          (Ideal.span {(Polynomial.X - Polynomial.C lam : Polynomial K)} •
            (⊤ : Submodule (Polynomial K) (famCoeff K N e)))) := by
  classical
  ext c
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem]
  constructor
  · intro hc
    have hmem : (famFibreEval K N e lam c : MvPolynomial (Fin N) K)
        ∈ Ideal.map (famEval (MvPolynomial.C lam)) A := hc
    obtain ⟨G, hG, hGeq⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (famEval_surjective (MvPolynomial.C lam))).mp hmem
    have hev : Polynomial.eval (MvPolynomial.C lam) (xComp e G)
        = (famFibreEval K N e lam c : MvPolynomial (Fin N) K) := by
      rw [eval_C_xComp]
      have hGeq' : Polynomial.eval (MvPolynomial.C lam) G
          = (famFibreEval K N e lam c : MvPolynomial (Fin N) K) := hGeq
      rw [hGeq', MvPolynomial.homogeneousComponent_of_mem (famFibreEval K N e lam c).2]
      simp
    obtain ⟨d, hd⟩ := exists_famAssemble_of_isXHomog (isXHomog_xComp e G)
    have hdP : d ∈ famCoeffPart A e := by
      rw [mem_famCoeffPart, hd]
      exact hA e G hG
    have hdc : ∀ α : ↥(degreeExponents N e), ((c - d) α).eval lam = 0 := by
      have heq : (∑ α : ↥(degreeExponents N e),
          MvPolynomial.monomial (α : Fin N →₀ ℕ) ((d α).eval lam))
          = ∑ α : ↥(degreeExponents N e),
            MvPolynomial.monomial (α : Fin N →₀ ℕ) ((c α).eval lam) := by
        have h1 : (∑ α : ↥(degreeExponents N e),
            MvPolynomial.monomial (α : Fin N →₀ ℕ) ((d α).eval lam))
            = Polynomial.eval (MvPolynomial.C lam) (famAssemble K N e d) :=
          (eval_famAssemble lam d).symm
        rw [h1, hd, hev]
        rfl
      intro α
      have hval := congrArg (MvPolynomial.coeff (α : Fin N →₀ ℕ)) heq
      rw [coeff_sum_monomial_subtype (fun α => (d α).eval lam) α,
        coeff_sum_monomial_subtype (fun α => (c α).eval lam) α] at hval
      show Polynomial.eval lam (c α - d α) = 0
      rw [Polynomial.eval_sub, hval, sub_self]
    choose q hq using fun α : ↥(degreeExponents N e) =>
      (Polynomial.dvd_iff_isRoot.mpr (hdc α))
    have hsub : c - d = (Polynomial.X - Polynomial.C lam : Polynomial K) • q := by
      funext α
      show c α - d α = _
      rw [Pi.smul_apply, smul_eq_mul]
      exact hq α
    have hmemQ : c - d ∈ (Ideal.span {(Polynomial.X - Polynomial.C lam : Polynomial K)} •
        (⊤ : Submodule (Polynomial K) (famCoeff K N e))) := by
      rw [hsub]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    have hcd : c = d + (c - d) := by abel
    rw [hcd]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hdP) (Submodule.mem_sup_right hmemQ)
  · intro hc
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hc
    have hy0 : famFibreEval K N e lam y = 0 := by
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨z, -, rfl⟩ := hy
      refine Subtype.ext ?_
      show (∑ α : ↥(degreeExponents N e), MvPolynomial.monomial (α : Fin N →₀ ℕ)
        ((((Polynomial.X - Polynomial.C lam : Polynomial K) • z) α).eval lam)) = 0
      refine Finset.sum_eq_zero fun α _ => ?_
      have hzero : Polynomial.eval lam
          (((Polynomial.X - Polynomial.C lam : Polynomial K) • z) α) = 0 := by
        show Polynomial.eval lam ((Polynomial.X - Polynomial.C lam) * z α) = 0
        rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          sub_self, zero_mul]
      rw [hzero, MvPolynomial.monomial_zero]
    show (famFibreEval K N e lam (x + y) : MvPolynomial (Fin N) K)
        ∈ Ideal.map (famEval (MvPolynomial.C lam)) A
    rw [map_add, hy0, add_zero, coe_famFibreEval]
    exact Ideal.mem_map_of_mem _ (mem_famCoeffPart.mp hx)

/-- **The fibre of the graded piece is the graded piece of the fibre.** -/
theorem finrank_quotDegreePart_eq_fibre (A : Ideal (Polynomial (MvPolynomial (Fin N) K)))
    (hA : IsXGradedIdeal A) (e : ℕ) (lam : K) :
    finrank K (quotDegreePart
        ((Ideal.map (famEval (MvPolynomial.C lam)) A).restrictScalars K) e)
      = finrank K ((famCoeff K N e ⧸ famCoeffPart A e) ⧸
          (Ideal.span {(Polynomial.X - Polynomial.C lam : Polynomial K)} •
            (⊤ : Submodule (Polynomial K) (famCoeff K N e ⧸ famCoeffPart A e)))) := by
  classical
  set P : Submodule (Polynomial K) (famCoeff K N e) := famCoeffPart A e with hP
  set Q : Submodule (Polynomial K) (famCoeff K N e) :=
    Ideal.span {(Polynomial.X - Polynomial.C lam : Polynomial K)} • ⊤ with hQ
  have hsurj : Function.Surjective ((Submodule.mkQ (degreePart
      ((Ideal.map (famEval (MvPolynomial.C lam)) A).restrictScalars K) e)).comp
      (famFibreEval K N e lam)) :=
    (Submodule.mkQ_surjective _).comp (famFibreEval_surjective lam)
  have e1 := LinearMap.quotKerEquivOfSurjective _ hsurj
  rw [← e1.finrank_eq, ker_famFibreQuot A hA e lam]
  have e2 : (famCoeff K N e ⧸ Submodule.restrictScalars K (P ⊔ Q))
      ≃ₗ[K] (famCoeff K N e ⧸ (P ⊔ Q)) := LinearEquiv.refl K _
  have hmapeq : Submodule.map P.mkQ (P ⊔ Q)
      = Ideal.span {(Polynomial.X - Polynomial.C lam : Polynomial K)} •
        (⊤ : Submodule (Polynomial K) (famCoeff K N e ⧸ P)) := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, hQ, Submodule.map_smul'',
      Submodule.map_top, Submodule.range_mkQ]
  have e3 := Submodule.quotientQuotientEquivQuotient P (P ⊔ Q) le_sup_left
  rw [hmapeq] at e3
  rw [e2.finrank_eq, ← (e3.restrictScalars K).finrank_eq]

/-- **Saturation at two points gives the same fibre Hilbert function.** -/
theorem finrank_quotDegreePart_fibre_eq (A : Ideal (Polynomial (MvPolynomial (Fin N) K)))
    (hA : IsXGradedIdeal A) {lam mu : K}
    (hlam : ∀ F : Polynomial (MvPolynomial (Fin N) K),
      (Polynomial.X - Polynomial.C (MvPolynomial.C lam)) * F ∈ A → F ∈ A)
    (hmu : ∀ F : Polynomial (MvPolynomial (Fin N) K),
      (Polynomial.X - Polynomial.C (MvPolynomial.C mu)) * F ∈ A → F ∈ A) (e : ℕ) :
    finrank K (quotDegreePart
        ((Ideal.map (famEval (MvPolynomial.C lam)) A).restrictScalars K) e)
      = finrank K (quotDegreePart
        ((Ideal.map (famEval (MvPolynomial.C mu)) A).restrictScalars K) e) := by
  classical
  have htors : ∀ nu : K, (∀ F : Polynomial (MvPolynomial (Fin N) K),
      (Polynomial.X - Polynomial.C (MvPolynomial.C nu)) * F ∈ A → F ∈ A) →
      ∀ v : famCoeff K N e ⧸ famCoeffPart A e,
        (Polynomial.X - Polynomial.C nu : Polynomial K) • v = 0 → v = 0 := by
    intro nu hnu v hv
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (famCoeffPart A e) v
    have hmem : (Polynomial.X - Polynomial.C nu : Polynomial K) • c ∈ famCoeffPart A e := by
      have h0 : Submodule.Quotient.mk
          ((Polynomial.X - Polynomial.C nu : Polynomial K) • c) = 0 := hv
      rwa [Submodule.Quotient.mk_eq_zero] at h0
    rw [mem_famCoeffPart, famAssemble_smul] at hmem
    have hmap : Polynomial.map (MvPolynomial.C : K →+* MvPolynomial (Fin N) K)
        (Polynomial.X - Polynomial.C nu : Polynomial K)
        = Polynomial.X - Polynomial.C (MvPolynomial.C nu) := by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hmap] at hmem
    have := hnu _ hmem
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact mem_famCoeffPart.mpr this
  rw [finrank_quotDegreePart_eq_fibre A hA e lam, finrank_quotDegreePart_eq_fibre A hA e mu]
  exact finrank_fibre_eq_of_smul_injective (htors lam hlam) (htors mu hmu)


end GaloisForLFunctions.HTGeometry
