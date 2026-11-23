import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFormRestrictions
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GradedCechHomology

/-! The alternating Čech differential on affine sections is the alternating
sum of the same regular forms in the common function field. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField] [Smooth s]
  {ι : Type} [LinearOrder ι]
  {U : ι → X.Opens} {B : Finset ι → Subalgebra K X.functionField}
  (h : IsAffCover s U B) (p : ℕ)

private abbrev C := (h.formCechDatum p).cochainComplex
private abbrev R := cech (fun I => omB K X.functionField (B I) p)

private def realizeCochain {q : ℕ} (c : (h.formCechDatum p).degreeCochains q)
    (I : Finset ι) : DR K X.functionField :=
  if hi : I.Nonempty then h.sectionRationalForms hi p (c.1 I) else 0

private theorem realizeCochain_mem {q : ℕ} (c : (h.formCechDatum p).degreeCochains q) :
    realizeCochain h p c ∈ (R (K := K) (X := X) (B := B) p).C q := by
  apply Submodule.mem_pi.mpr
  intro I _
  change realizeCochain h p c I ∈
    (if I.Nonempty ∧ (I.card : ℤ) = (q : ℤ) + 1 then omB K X.functionField (B I) p else ⊥)
  split_ifs with hi
  · rw [realizeCochain, dif_pos hi.1]
    exact (h.sectionRationalForms hi.1 p (c.1 I)).2
  · suffices realizeCochain h p c I = 0 by rw [this]; exact zero_mem _
    by_cases he : I.Nonempty
    · have hc : I.card ≠ q + 1 := fun hc => hi ⟨he, by exact_mod_cast hc⟩
      simp only [realizeCochain, dif_pos he, c.2 I hc, map_zero, ZeroMemClass.coe_zero]
    · rw [realizeCochain, dif_neg he]

private def realizeDegree (q : ℕ) :
    (C h p).X q →+ (R (K := K) (X := X) (B := B) p).C q where
  toFun c := ⟨realizeCochain h p c, realizeCochain_mem h p c⟩
  map_zero' := by
    apply Subtype.ext
    funext I
    change realizeCochain h p (q := q) 0 I = 0
    by_cases hi : I.Nonempty
    · rw [realizeCochain, dif_pos hi]
      exact congrArg (fun x : omB K X.functionField (B I) p => x.val)
        (h.sectionRationalForms hi p).map_zero
    · rw [realizeCochain, dif_neg hi]
  map_add' := by
    intro a b
    apply Subtype.ext
    funext I
    change realizeCochain h p (a + b) I = realizeCochain h p a I + realizeCochain h p b I
    by_cases hi : I.Nonempty
    · simp only [realizeCochain, dif_pos hi]
      exact congrArg (fun x : omB K X.functionField (B I) p => x.val)
        ((h.sectionRationalForms hi p).map_add (a.val I) (b.val I))
    · simp only [realizeCochain, dif_neg hi, add_zero]

/-- Degreewise realization of affine Čech cochains as regular rational forms. -/
def IsAffCover.formCochainsEquiv (q : ℕ) :
    (C h p).X q ≃+ (R (K := K) (X := X) (B := B) p).C q := by
  apply AddEquiv.ofBijective (realizeDegree h p q)
  constructor
  · intro c c' e
    apply Subtype.ext
    funext I
    by_cases hi : I.Nonempty
    · have he := congrFun (congrArg Subtype.val e) I
      change realizeCochain h p c I = realizeCochain h p c' I at he
      rw [realizeCochain, dif_pos hi, realizeCochain, dif_pos hi] at he
      exact (h.sectionRationalForms hi p).injective (Subtype.ext he)
    · have hc : I.card ≠ q + 1 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hi, Finset.card_empty]
        exact (Nat.succ_ne_zero q).symm
      exact (c.2 I hc).trans (c'.2 I hc).symm
  · intro a
    have ha (I : Finset ι) := (Submodule.mem_pi.mp a.2) I (Set.mem_univ I)
    let c : (h.formCechDatum p).Cochain := fun I =>
      if hi : I.Nonempty ∧ I.card = q + 1 then
        (h.sectionRationalForms hi.1 p).symm ⟨a.val I, by
          have hc : I.Nonempty ∧ (I.card : ℤ) = (q : ℤ) + 1 :=
            ⟨hi.1, by exact_mod_cast hi.2⟩
          simpa only [if_pos hc] using ha I⟩
      else 0
    refine ⟨⟨c, fun I hi => dif_neg (fun hc => hi hc.2)⟩, Subtype.ext (funext fun I => ?_)⟩
    change realizeCochain h p ⟨c, _⟩ I = a.val I
    by_cases hi : I.Nonempty ∧ I.card = q + 1
    · simp only [realizeCochain, dif_pos hi.1, c, dif_pos hi, AddEquiv.apply_symm_apply]
    · have hc : ¬(I.Nonempty ∧ (I.card : ℤ) = (q : ℤ) + 1) := by
        intro hI
        exact hi ⟨hI.1, by exact_mod_cast hI.2⟩
      have hz : a.val I = 0 := by
        have hI := ha I
        rw [if_neg hc, Submodule.mem_bot] at hI
        exact hI
      by_cases he : I.Nonempty
      · simp only [realizeCochain, dif_pos he, c, dif_neg hi, map_zero, ZeroMemClass.coe_zero, hz]
      · rw [realizeCochain, dif_neg he, hz]

theorem IsAffCover.formCochainsEquiv_apply (q : ℕ) (c : (C h p).X q)
    {I : Finset ι} (hi : I.Nonempty) :
    (h.formCochainsEquiv p q c).val I = h.sectionRationalForms hi p (c.val I) :=
  dif_pos hi

theorem IsAffCover.formCochainsEquiv_apply_empty (q : ℕ) (c : (C h p).X q) :
    (h.formCochainsEquiv p q c).val ∅ = 0 := by
  change realizeCochain h p c (∅ : Finset ι) = 0
  have hempty : ¬(∅ : Finset ι).Nonempty := Finset.not_nonempty_empty
  rw [realizeCochain, dif_neg hempty]

theorem IsAffCover.formCochainsEquiv_d (q : ℕ) (c : (C h p).X q) :
    (h.formCochainsEquiv p (q + 1) ((C h p).d q (q + 1) c)).val =
      (R (K := K) (X := X) (B := B) p).D (h.formCochainsEquiv p q c) := by
  funext I
  change realizeCochain h p ((C h p).d q (q + 1) c) I = deltaL K ι (DR K X.functionField)
    (realizeCochain h p c) I
  rw [FinsetCechDatum.cochainComplex_d_apply, deltaL_apply]
  by_cases hi : I.Nonempty
  · rw [realizeCochain, dif_pos hi]
    let e := (omB K X.functionField (B I) p).subtype.toAddMonoidHom.comp
      (h.sectionRationalForms hi p).toAddMonoidHom
    change e ((h.formCechDatum p).d c.val I) = _
    rw [FinsetCechDatum.d, map_sum]
    refine Finset.sum_congr rfl fun i hi' => ?_
    rw [map_zsmul]
    let J := I.erase i
    let hj : J ⊆ I := Finset.erase_subset i I
    by_cases he : J.Nonempty
    · change cubeSign I i • (h.sectionRationalForms hi p ((h.formCechDatum p).res hj (c.val J)) :
        DR K X.functionField) = cubeSign I i • realizeCochain h p c J
      rw [h.sectionRationalForms_res he hj, realizeCochain, dif_pos he]
    · have hc : J.card ≠ q + 1 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.card_empty]
        exact (Nat.succ_ne_zero q).symm
      change cubeSign I i • e ((h.formCechDatum p).res hj (c.val J)) =
        cubeSign I i • realizeCochain h p c J
      simp only [c.2 J hc, map_zero, realizeCochain, dif_neg he, smul_zero]
  · have hI := Finset.not_nonempty_iff_eq_empty.mp hi
    subst I
    simp [realizeCochain]

end GlobalTheory.PD
