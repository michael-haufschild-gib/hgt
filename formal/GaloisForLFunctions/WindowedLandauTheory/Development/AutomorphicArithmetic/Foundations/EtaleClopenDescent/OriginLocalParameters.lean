import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartLocalAlgebra
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedFibreTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolynomialDiagonal
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FlatRegularSequence
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteNormalizationProjective

/-! The origin coordinates remain weakly regular over the local
normalization. At a reduced fibre point they generate precisely the
functions vanishing at that point. -/

noncomputable section

open RingTheory.Sequence GlobalTheory.WH
open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local notation "B" => rB k E x {0}

/-- The origin coordinates viewed in the function field's local chart ring. -/
def localOriginCoordinate (e : OriginFibrePoint k E x) (j : Fin d) : loc B e.1 :=
  ⟨_, le_loc B e.1 (tco_mem k E x j)⟩

theorem locEval_localOriginCoordinate (e : OriginFibrePoint k E x) (j : Fin d) :
    locEval B e.1 (localOriginCoordinate e j) = 0 :=
  (locEval_inclusion B e.1 ⟨_, tco_mem k E x j⟩).trans (e.2 j)

/-- Polynomial weak regularity extends through the flat normalization
and then through localization at the fibre point. -/
theorem IsFinCover.weaklyRegular_localOriginCoordinates (h : IsFinCover k E x)
    (e : OriginFibrePoint k E x) :
    IsWeaklyRegular (loc B e.1) ((List.finRange d).map (localOriginCoordinate e)) := by
  classical
  let A := rA k x {0}
  let B' := integralClosure A E
  let C := loc B e.1
  let S := (RingHom.ker e.1.toRingHom).primeCompl
  let P := MvPolynomial (Fin d) k
  let f := h.pd.chartPolynomialEquiv 0
  let i : A →+* B := algebraMap A B'
  let y (j : Fin d) : A := f (MvPolynomial.X j)
  letI : Algebra B C := localChartAlgebra B e.1
  letI : IsLocalization S C := localChart_isLocalization B e.1
  letI : Module.Projective A B' := (h.finiteProjective_chart 0).2
  letI : Module.Flat B C := IsLocalization.flat C S
  let l := List.finRange d
  let I : Ideal P := Ideal.span ((MvPolynomial.X : Fin d → P) '' (∅ : Set (Fin d)))
  have hreg : IsWeaklyRegular (P ⧸ I) (l.map (MvPolynomial.X : Fin d → P)) :=
    (isRegular_map_X (K := k) (∅ : Set (Fin d)) l (List.nodup_finRange d) (by simp)).1
  have hI : I = ⊥ := by simp [I]
  let q : (P ⧸ I) ≃ₐ[P] P := (Ideal.quotientEquivAlgOfEq P hI).trans (AlgEquiv.quotientBot P P)
  have hP := (q.toLinearEquiv.isWeaklyRegular_congr _).mp hreg
  have hA : IsWeaklyRegular A (l.map y) := by
    refine (f.toAddEquiv.isWeaklyRegular_congr ?_).mp hP
    exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun i _ y => map_mul f (MvPolynomial.X i) y))
  have hB' : IsWeaklyRegular B' ((l.map y).map (algebraMap A B')) :=
    weaklyRegular_map_of_flat hA
  have hB : IsWeaklyRegular B ((l.map y).map i) := hB'
  have hC : IsWeaklyRegular C (((l.map y).map i).map (algebraMap B C)) :=
    weaklyRegular_map_of_flat hB
  have he : (algebraMap B C ∘ i ∘ y) = localOriginCoordinate e := by
    funext j
    apply Subtype.ext
    change algebraMap F E (f (MvPolynomial.X j) : F) = algebraMap F E (x j.succ / x 0)
    rw [h.pd.chartPolynomialEquiv_X]
    simp [chartCoordinates]
  change IsWeaklyRegular C (l.map (localOriginCoordinate e))
  simpa only [List.map_map, he] using hC

/-- At a point of the reduced origin fibre, the origin equations
generate the kernel of local evaluation. -/
theorem IsFinCover.span_localOriginCoordinates (h : IsFinCover k E x)
    [IsReduced (B ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x) :
    Ideal.span (Set.range (localOriginCoordinate e)) = RingHom.ker (locEval B e.1).toRingHom := by
  let C := loc B e.1
  let S := (RingHom.ker e.1.toRingHom).primeCompl
  letI : Algebra B C := localChartAlgebra B e.1
  letI : IsLocalization S C := localChart_isLocalization B e.1
  let i := algebraMap B C
  let ev := locEval B e.1
  let J := Ideal.span (Set.range (localOriginCoordinate e))
  have hi (a : B) : ev (i a) = e.1 a := locEval_inclusion B e.1 a
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact locEval_localOriginCoordinate e j
  · intro z hz
    change ev z = 0 at hz
    obtain ⟨⟨a, s⟩, hzs⟩ := IsLocalization.surj S (z : C)
    have he := congrArg ev hzs
    rw [map_mul, hz, zero_mul, hi] at he
    obtain ⟨b, c, hb, ha⟩ := exists_regular_parameters_of_reduced_quotient h e.1 a he.symm
    have hab : i b * i a = ∑ j, i (c j) * localOriginCoordinate e j := by
      rw [← map_mul, ha, map_sum]
      exact Finset.sum_congr rfl fun j _ => map_mul i _ _
    have hba : i b * i a ∈ J := by
      rw [hab]
      exact J.sum_mem fun j _ => J.mul_mem_left _ (Ideal.subset_span (Set.mem_range_self j))
    have hu : IsUnit (i b * i s) := by
      apply isUnit_loc_of_eval_ne_zero
      rw [map_mul, hi, hi, hb, one_mul]
      exact s.property
    obtain ⟨u, hu⟩ := hu
    have hm : (u : C) * z ∈ J := by
      rw [hu, mul_assoc, mul_comm (i s), hzs]
      exact hba
    have hm' := J.mul_mem_left (↑u⁻¹ : C) hm
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at hm'
    exact hm'

end GlobalTheory.PD
