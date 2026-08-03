import GaloisForLFunctions.HTGeometry.JetRealization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The inversion gauge: a differential relation for reciprocals descends to the family

Inverting each member of a family is not a polynomial operation on jets, so the corpus's polynomial
gauges do not apply.  The substitution is rational, with denominators powers of the zeroth jets, so
it lands in the localization of the jet ring inverting those variables.

Two facts make the descent unconditional.  Evaluating the substitution at a jet point with nonzero
zeroth jets agrees with evaluating at the reciprocal jets — proved by algebra-hom uniqueness on the
jet variables, with no monomial expansion.  And the substitution is injective, because every jet
point with nonzero zeroth jets is realized by an actual smooth nonvanishing family, so a polynomial
killed by the substitution vanishes on the whole nonzero locus and is therefore zero.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The product of the zeroth jet variables of all blocks. -/
def zeroJetProduct (m n : ℕ) : MvPolynomial (FamilyJetIndex m n) ℂ :=
  ∏ i : Fin m, MvPolynomial.X (Sum.inr (i, (0 : Fin (n + 1))))

/-- The jet ring with the zeroth jets inverted. -/
abbrev JetAway (m n : ℕ) := Localization.Away (zeroJetProduct m n)

/-- The inverse of one zeroth jet variable in the localization. -/
def invZeroJet (m n : ℕ) (i : Fin m) : JetAway m n :=
  algebraMap (MvPolynomial (FamilyJetIndex m n) ℂ) (JetAway m n)
      (∏ j ∈ Finset.univ.erase i, MvPolynomial.X (Sum.inr (j, (0 : Fin (n + 1)))))
    * IsLocalization.Away.invSelf (zeroJetProduct m n)

theorem algebraMap_zeroJet_mul_invZeroJet (m n : ℕ) (i : Fin m) :
    algebraMap (MvPolynomial (FamilyJetIndex m n) ℂ) (JetAway m n)
        (MvPolynomial.X (Sum.inr (i, (0 : Fin (n + 1))))) * invZeroJet m n i = 1 := by
  rw [invZeroJet, ← mul_assoc, ← map_mul,
    Finset.mul_prod_erase Finset.univ
      (fun j : Fin m => MvPolynomial.X (Sum.inr (j, (0 : Fin (n + 1)))) :
        Fin m → MvPolynomial (FamilyJetIndex m n) ℂ) (Finset.mem_univ i)]
  rw [show (∏ j : Fin m, MvPolynomial.X (Sum.inr (j, (0 : Fin (n + 1)))) :
      MvPolynomial (FamilyJetIndex m n) ℂ) = zeroJetProduct m n from rfl]
  exact IsLocalization.Away.mul_invSelf _

/-- The rational jet substitution attached to inverting every member of a family. -/
def invJetSubst (m n : ℕ) : FamilyJetIndex m n → JetAway m n :=
  Sum.elim
    (fun _ => algebraMap (MvPolynomial (FamilyJetIndex m n) ℂ) (JetAway m n)
      (MvPolynomial.X (Sum.inl ())))
    (fun p => algebraMap (MvPolynomial (FamilyJetIndex m n) ℂ) (JetAway m n)
        (familyInvJetNum m n p.1 (p.2 : ℕ)) * (invZeroJet m n p.1) ^ ((p.2 : ℕ) + 1))

/-- The substitution as an algebra homomorphism of the jet ring into the localization. -/
def invJetAlgHom (m n : ℕ) :
    MvPolynomial (FamilyJetIndex m n) ℂ →ₐ[ℂ] JetAway m n :=
  MvPolynomial.aeval (invJetSubst m n)

section Eval

variable {m n : ℕ} {x : FamilyJetIndex m n → ℂ}

/-- Evaluation at a jet point with nonzero zeroth jets inverts the localized denominators. -/
theorem isUnit_eval_zeroJetProduct_pow (hx : ∀ i, x (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0)
    (y : Submonoid.powers (zeroJetProduct m n)) :
    IsUnit (MvPolynomial.aeval x (y : MvPolynomial (FamilyJetIndex m n) ℂ)) := by
  obtain ⟨k, hk⟩ := y.2
  have hval : MvPolynomial.aeval x (y : MvPolynomial (FamilyJetIndex m n) ℂ)
      = (MvPolynomial.aeval x (zeroJetProduct m n)) ^ k := by
    rw [← hk, map_pow]
  rw [hval]
  refine IsUnit.pow k ?_
  rw [isUnit_iff_ne_zero]
  rw [zeroJetProduct, map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rw [MvPolynomial.aeval_X]
  exact hx i

/-- Evaluation at a jet point with nonzero zeroth jets, extended to the localization. -/
def evalJetAway (hx : ∀ i, x (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0) :
    JetAway m n →ₐ[ℂ] ℂ :=
  IsLocalization.liftAlgHom (isUnit_eval_zeroJetProduct_pow hx)

@[simp]
theorem evalJetAway_algebraMap (hx : ∀ i, x (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0)
    (p : MvPolynomial (FamilyJetIndex m n) ℂ) :
    evalJetAway hx (algebraMap _ _ p) = MvPolynomial.aeval x p := by
  rw [evalJetAway, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem evalJetAway_invZeroJet (hx : ∀ i, x (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0) (i : Fin m) :
    evalJetAway hx (invZeroJet m n i) = (x (Sum.inr (i, (0 : Fin (n + 1)))))⁻¹ := by
  have hmul := congrArg (evalJetAway hx) (algebraMap_zeroJet_mul_invZeroJet m n i)
  rw [map_mul, map_one, evalJetAway_algebraMap, MvPolynomial.aeval_X] at hmul
  have hx0 : x (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0 := hx i
  calc evalJetAway hx (invZeroJet m n i)
      = (x (Sum.inr (i, (0 : Fin (n + 1)))))⁻¹
          * (x (Sum.inr (i, (0 : Fin (n + 1)))) * evalJetAway hx (invZeroJet m n i)) := by
        field_simp
    _ = (x (Sum.inr (i, (0 : Fin (n + 1)))))⁻¹ := by rw [hmul, mul_one]

end Eval

/-- **The substitution computes the reciprocal jets.**  Evaluating the localized substitution at the
jets of a family is evaluating at the jets of the reciprocal family. -/
theorem evalJetAway_comp_invJetAlgHom {m n : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) w)
    (hne : ∀ i, ∀ w ∈ U, g i w ≠ 0) {z : ℂ} (hz : z ∈ U)
    (hx : ∀ i, familyJetVec (n := n) g z (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0) :
    (evalJetAway hx).comp (invJetAlgHom m n)
      = MvPolynomial.aeval (familyJetVec (n := n) (fun i w => (g i w)⁻¹) z) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with ⟨⟩ | ⟨i, k⟩
  · rw [AlgHom.comp_apply, invJetAlgHom, MvPolynomial.aeval_X, invJetSubst, Sum.elim_inl,
      evalJetAway_algebraMap, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    rfl
  · rw [AlgHom.comp_apply, invJetAlgHom, MvPolynomial.aeval_X, invJetSubst, Sum.elim_inr,
      map_mul, map_pow, evalJetAway_algebraMap, evalJetAway_invZeroJet, MvPolynomial.aeval_X]
    rw [familyJetVec_inv_apply hU hg hne hz i k]
    rw [div_eq_mul_inv, ← inv_pow]
    congr 1

/-- Iterated derivatives only depend on the germ. -/
theorem iteratedDeriv_congr_of_eventuallyEq {f h : ℂ → ℂ} {z : ℂ} (hfh : f =ᶠ[nhds z] h)
    (k : ℕ) : iteratedDeriv k f z = iteratedDeriv k h z := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ hfh.eq_of_nhds
  rwa [nhdsWithin_univ]

/-- Iterating the derivative through a translation. -/
theorem iterate_derivative_comp_sub (p : Polynomial ℂ) (z : ℂ) (k : ℕ) :
    Polynomial.derivative^[k] (p.comp (Polynomial.X - Polynomial.C z))
      = (Polynomial.derivative^[k] p).comp (Polynomial.X - Polynomial.C z) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        Polynomial.derivative_comp]
      simp

/-- **Jet realization at an arbitrary base point.** -/
theorem exists_smooth_iteratedDeriv_eq (n : ℕ) (z : ℂ) (c : ℕ → ℂ) :
    ∃ f : ℂ → ℂ, (∀ w : ℂ, ContDiffAt ℂ (⊤ : ℕ∞) f w) ∧
      Continuous f ∧ ∀ k ≤ n, iteratedDeriv k f z = c k := by
  obtain ⟨p, hp⟩ := exists_polynomial_eval_iterate_derivative_eq n c
  refine ⟨fun w => Polynomial.eval w (p.comp (Polynomial.X - Polynomial.C z)), ?_, ?_, ?_⟩
  · intro w
    have hcd : ContDiff ℂ (⊤ : ℕ∞)
        fun w : ℂ => Polynomial.eval w (p.comp (Polynomial.X - Polynomial.C z)) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        (Polynomial.contDiff_aeval (𝕜 := ℂ) (p.comp (Polynomial.X - Polynomial.C z))
          ((⊤ : ℕ∞) : WithTop ℕ∞))
    exact hcd.contDiffAt
  · exact Polynomial.continuous (p.comp (Polynomial.X - Polynomial.C z))
  · intro k hk
    rw [iteratedDeriv_polynomial_eval, iterate_derivative_comp_sub, Polynomial.eval_comp]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    exact hp k hk

/-- **Injectivity of the inversion substitution.**  Every jet point with nonzero zeroth jets is
realized by a smooth nonvanishing family, so a polynomial killed by the substitution vanishes on the
whole nonzero locus. -/
theorem invJetAlgHom_injective (m n : ℕ) : Function.Injective (invJetAlgHom m n) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  refine mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates
    (Finset.image (fun i : Fin m => Sum.inr (i, (0 : Fin (n + 1)))) Finset.univ) P ?_
  intro y hy
  set z : ℂ := y (Sum.inl ()) with hzdef
  set c : Fin m → ℕ → ℂ :=
    fun i k => if h : k < n + 1 then y (Sum.inr (i, ⟨k, h⟩)) else 0 with hcdef
  choose f hfsmooth hfcont hfjet using fun i : Fin m => exists_smooth_iteratedDeriv_eq n z (c i)
  have hy0 : ∀ i : Fin m, y (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0 := by
    intro i
    refine hy _ ?_
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hfz : ∀ i, f i z ≠ 0 := by
    intro i
    have h0 := hfjet i 0 (Nat.zero_le n)
    rw [iteratedDeriv_zero] at h0
    rw [h0, hcdef]
    simp only [dif_pos (Nat.succ_pos n)]
    exact hy0 i
  set U : Set ℂ := {w : ℂ | ∀ i, f i w ≠ 0} with hUdef
  have hU : IsOpen U := by
    rw [hUdef, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => ?_
    exact isOpen_compl_singleton.preimage (hfcont i)
  have hzU : z ∈ U := hfz
  set g : Fin m → ℂ → ℂ := fun i w => (f i w)⁻¹ with hgdef
  have hg : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) w := by
    intro i w hw
    exact (hfsmooth i w).inv (hw i)
  have hgne : ∀ i, ∀ w ∈ U, g i w ≠ 0 := by
    intro i w hw
    exact inv_ne_zero (hw i)
  have hx : ∀ i, familyJetVec (n := n) g z (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0 := by
    intro i
    change (g i z) ≠ 0
    exact hgne i z hzU
  have hagree := evalJetAway_comp_invJetAlgHom (n := n) hU hg hgne hzU hx
  have hzero : MvPolynomial.aeval
      (familyJetVec (n := n) (fun i w => (g i w)⁻¹) z) P = 0 := by
    have := congrArg (fun F : MvPolynomial (FamilyJetIndex m n) ℂ →ₐ[ℂ] ℂ => F P) hagree
    simp only [AlgHom.comp_apply] at this
    rw [← this, hP, map_zero]
  have hjetvec : familyJetVec (n := n) (fun i w => (g i w)⁻¹) z = y := by
    funext v
    rcases v with ⟨⟩ | ⟨i, k⟩
    · rfl
    · have hfun : (fun w => (g i w)⁻¹) =ᶠ[nhds z] f i := by
        filter_upwards [hU.mem_nhds hzU] with w hw
        rw [hgdef]
        exact inv_inv (f i w)
      have hval : familyJetVec (n := n) (fun i w => (g i w)⁻¹) z (Sum.inr (i, k))
          = iteratedDeriv (k : ℕ) (fun w => (g i w)⁻¹) z := rfl
      rw [hval, iteratedDeriv_congr_of_eventuallyEq hfun (k : ℕ),
        hfjet i (k : ℕ) (Nat.lt_succ_iff.mp k.2), hcdef]
      simp only [dif_pos k.2]
  rw [hjetvec] at hzero
  rw [← MvPolynomial.coe_aeval_eq_eval]
  exact hzero

/-- **The inversion gauge.**  A differential relation among the reciprocals of a smooth nonvanishing
family descends to a differential relation among the family itself. -/
theorem familyDifferentiallyAlgebraicOn_of_inv {m : ℕ} {U : Set ℂ} (hU : IsOpen U)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) w)
    (hne : ∀ i, ∀ w ∈ U, g i w ≠ 0)
    (h : FamilyDifferentiallyAlgebraicOn (fun i w => (g i w)⁻¹) U) :
    FamilyDifferentiallyAlgebraicOn g U := by
  obtain ⟨n, P, hPne, hPzero⟩ := h
  have hQne : invJetAlgHom m n P ≠ 0 := by
    intro hcon
    exact hPne ((injective_iff_map_eq_zero (invJetAlgHom m n)).mp
      (invJetAlgHom_injective m n) P hcon)
  obtain ⟨⟨R, s⟩, hRs⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (zeroJetProduct m n)) (invJetAlgHom m n P)
  simp only at hRs
  have hRne : R ≠ 0 := by
    intro hcon
    rw [hcon, IsLocalization.mk'_zero] at hRs
    exact hQne hRs.symm
  refine ⟨n, R, hRne, ?_⟩
  intro z hz
  have hx : ∀ i, familyJetVec (n := n) g z (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0 := by
    intro i
    change g i z ≠ 0
    exact hne i z hz
  have hagree := evalJetAway_comp_invJetAlgHom (n := n) hU hg hne hz hx
  have hQzero : evalJetAway hx (invJetAlgHom m n P) = 0 := by
    have happ := congrArg (fun F : MvPolynomial (FamilyJetIndex m n) ℂ →ₐ[ℂ] ℂ => F P) hagree
    simp only [AlgHom.comp_apply] at happ
    rw [happ]
    have hconv : MvPolynomial.aeval
        (familyJetVec (n := n) (fun i w => (g i w)⁻¹) z) P
        = MvPolynomial.eval (familyJetVec (n := n) (fun i w => (g i w)⁻¹) z) P := rfl
    rw [hconv]
    exact hPzero z hz
  have hspec : invJetAlgHom m n P
      * algebraMap (MvPolynomial (FamilyJetIndex m n) ℂ) (JetAway m n)
          (s : MvPolynomial (FamilyJetIndex m n) ℂ)
      = algebraMap (MvPolynomial (FamilyJetIndex m n) ℂ) (JetAway m n) R := by
    rw [← hRs]
    exact IsLocalization.mk'_spec _ _ _
  have hval := congrArg (evalJetAway hx) hspec
  rw [map_mul, hQzero, zero_mul, evalJetAway_algebraMap] at hval
  have hconv : MvPolynomial.aeval (familyJetVec (n := n) g z) R
      = MvPolynomial.eval (familyJetVec (n := n) g z) R := rfl
  rw [← hconv]
  exact hval.symm

end

end GaloisForLFunctions.HTGeometry
