import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCoordinateAlgebras
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Laurent coefficient at zero agrees with evaluation on the affine
origin chart. -/

noncomputable section

open MvPolynomial

namespace GlobalTheory.PD

variable {k F : Type} [Field k] [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

/-- The degree-zero Laurent coefficient on homogeneous degree-zero monomials. -/
def IsRes (x : Fin (d + 1) → F) (ρ : F →ₗ[k] k) : Prop :=
  ρ 1 = 1 ∧ ∀ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 → m ≠ 0 → ρ (∏ j, x j ^ m j) = 0

/-- Evaluation at the origin of the polynomial chart. -/
def originEval (h : IsPd k x) : rA k x {0} →ₐ[k] k :=
  (aeval (fun _ : Fin d => (0 : k))).comp (h.chartPolynomialEquiv 0).symm.toAlgHom

/-- The defining equations of the origin in its coordinate polynomial chart. -/
def originChartCoordinate (j : Fin d) : rA k x {0} :=
  ⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩

private theorem chartPolynomialEquiv_origin_X (h : IsPd k x) (j : Fin d) :
    h.chartPolynomialEquiv 0 (X j) = originChartCoordinate (k := k) (x := x) j :=
  Subtype.ext (by simpa [chartCoordinates, originChartCoordinate] using h.chartPolynomialEquiv_X 0 j)

private theorem ker_aeval_zero :
    RingHom.ker (aeval (fun _ : Fin d => (0 : k))).toRingHom =
      Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) k)) := by
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra! h₀
    have he : m = 0 := Finsupp.ext (fun i => h₀ i (Set.mem_univ i))
    subst m
    change aeval (fun _ : Fin d => (0 : k)) p = 0 at hp
    have hzero : aeval (fun _ : Fin d => (0 : k)) p = coeff 0 p := by
      rw [show (fun _ : Fin d => (0 : k)) = 0 from rfl, MvPolynomial.aeval_zero]
      simp [MvPolynomial.constantCoeff_eq]
    exact (mem_support_iff.mp hm) (hzero ▸ hp)
  · rintro _ ⟨j, rfl⟩
    exact aeval_X _ _

theorem ker_originEval (h : IsPd k x) :
    RingHom.ker (originEval h).toRingHom =
      Ideal.span (Set.range (originChartCoordinate (k := k) (x := x))) := by
  let e := h.chartPolynomialEquiv 0
  have he : Set.range (originChartCoordinate (k := k) (x := x)) =
      e.toRingEquiv.toRingHom '' Set.range X := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun j => (chartPolynomialEquiv_origin_X h j).symm)
  rw [he, ← Ideal.map_span e.toRingEquiv.toRingHom, ← ker_aeval_zero]
  let J : Ideal (MvPolynomial (Fin d) k) :=
    RingHom.ker (aeval (fun _ : Fin d => (0 : k))).toRingHom
  have hJ : J.map e.toRingEquiv.toRingHom = J.comap e.symm.toRingEquiv.toRingHom :=
    Ideal.map_comap_of_equiv e.toRingEquiv
  have hleft : RingHom.ker (originEval h).toRingHom = J.comap e.symm.toRingEquiv.toRingHom := by
    ext a
    rfl
  exact hleft.trans hJ.symm

private theorem res_aeval (ρ : F →ₗ[k] k) (hρ : IsRes x ρ) (p : MvPolynomial (Fin d) k) :
    ρ (aeval (fun j : Fin d => x j.succ / x 0) p) = aeval (fun _ : Fin d => (0 : k)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Algebra.smul_def, map_smul]
    change c • ρ (∏ j : Fin d, (x j.succ / x 0) ^ n j) =
      c * ∏ j : Fin d, (0 : k) ^ n j
    by_cases hn : n = 0
    · subst n
      simp [hρ.1]
    · obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
        by_contra! h; exact hn (Finsupp.ext h)
      have hz : ∏ i : Fin d, (0 : k) ^ n i = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hj)
      let m : Fin (d + 1) → ℤ := Fin.cons (-(∑ i, (n i : ℤ))) (fun i => (n i : ℤ))
      have hs : ∑ i, m i = 0 := by rw [Fin.sum_univ_succ]; simp [m]
      have hm : m ≠ 0 := by
        intro h
        exact hj (by simpa [m] using congrFun h j.succ)
      have he : ∏ j : Fin d, (x j.succ / x 0) ^ n j = ∏ i, x i ^ m i := by
        rw [Fin.prod_univ_succ]
        simp only [m, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg, div_pow,
          Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum]
        rw [div_eq_inv_mul]
      rw [he, hρ.2 m hs hm, hz, smul_zero, mul_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]

/-- Every Laurent coefficient functional with the prescribed monomial
values restricts to ordinary origin evaluation on regular chart functions. -/
theorem res_eq_originEval (h : IsPd k x) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    (a : rA k x {0}) : ρ a = originEval h a := by
  let e := h.chartPolynomialEquiv 0
  have he : (rA k x {0}).val.comp e.toAlgHom = aeval (fun j : Fin d => x j.succ / x 0) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Subalgebra.val_apply, aeval_X]
    exact congrArg Subtype.val (chartPolynomialEquiv_origin_X h j)
  have hh (p : MvPolynomial (Fin d) k) :
      (e p : F) = aeval (fun j : Fin d => x j.succ / x 0) p := AlgHom.congr_fun he p
  obtain ⟨p, rfl⟩ := e.surjective a
  change ρ (e p : F) = aeval (fun _ : Fin d => (0 : k)) (e.symm (e p))
  rw [hh, AlgEquiv.symm_apply_apply]
  exact res_aeval ρ hρ p

end GlobalTheory.PD
