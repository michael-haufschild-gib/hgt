import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionNormOfBaseChange
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.FieldTheory.Minpoly.Field

/-! A generator whose positive power is a uniformizer is totally
ramified. Comparing the ramification lower bound with its defining
polynomial gives the degree and the signed uniformizer norm. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open IntermediateField Polynomial WithZero
open scoped GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

theorem degree_ramificationIdx_norm_of_uniformizer_radical {m : ℕ} (hm : 0 < m)
    (a : K) (ha : Valued.v (algebraMap K (v.adicCompletion K) a) = exp (-1 : ℤ))
    (b : L) (hb : b ^ m = algebraMap K L a) (hgen : K⟮b⟯ = ⊤) :
    Module.finrank K L = m ∧ w.asIdeal.ramificationIdx (𝓞 K) = m ∧
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) = m ∧
      Algebra.norm K b = (-1 : K) ^ (m - 1) * a := by
  let π := algebraMap K (v.adicCompletion K) a
  let β := algebraMap L (w.adicCompletion L) b
  let e := w.asIdeal.ramificationIdx (𝓞 K)
  have hb' : β ^ m = AdicLiesOver.completionMap v w π := by
    change (algebraMap L (w.adicCompletion L) b) ^ m =
      algebraMap (v.adicCompletion K) (w.adicCompletion L) (algebraMap K (v.adicCompletion K) a)
    rw [← map_pow, hb, ← IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      ← IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion L)]
  have hv := congrArg (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰) hb'
  rw [map_pow, AdicLiesOver.valued_completionMap, show Valued.v π = _ from ha,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot] at hv
  change Valued.v β ^ m = exp (-1 : ℤ) ^ e at hv
  have hb0 : Valued.v β ≠ 0 := by
    intro hz
    rw [hz, zero_pow hm.ne'] at hv
    exact (pow_ne_zero _ exp_ne_zero) hv.symm
  rw [← exp_log hb0, ← exp_nsmul, ← exp_nsmul, exp_inj, nsmul_eq_mul,
    nsmul_eq_mul, mul_neg_one] at hv
  have hdiv : m ∣ e := Int.natCast_dvd_natCast.mp ⟨-log (Valued.v β), by rw [mul_neg, hv, neg_neg]⟩
  have he : 0 < e := Ideal.ramificationIdx_pos (R := 𝓞 K) w.asIdeal
  let P : K[X] := X ^ m - C a
  have hP : P.Monic := monic_X_pow_sub_C _ hm.ne'
  have hPd : P.natDegree = m := natDegree_X_pow_sub_C
  have hroot : aeval b P = 0 := by simp [P, hb]
  have hbint : IsIntegral K b := ⟨P, hP, hroot⟩
  have hdim : (minpoly K b).natDegree = Module.finrank K L := by
    rw [← IntermediateField.adjoin.finrank hbint, hgen, IntermediateField.finrank_top']
  have hdvd : minpoly K b ∣ P := minpoly.dvd K b hroot
  have hK : Module.finrank K L ≤ m := by
    rw [← hdim, ← hPd]
    exact natDegree_le_of_dvd hdvd hP.ne_zero
  have hlocal : Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤ Module.finrank K L := by
    rw [← sum_finiteCompletion_finrank L v]
    let s : finitePlacesAbove L v := ⟨w, (mem_finitePlacesAbove L v w).mpr inferInstance⟩
    exact Finset.single_le_sum (f := fun u : finitePlacesAbove L v =>
      Module.finrank (v.adicCompletion K) (u.val.adicCompletion L)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ s)
  have heL : e ≤ Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
    rw [finiteCompletion_finrank_eq_ramification_mul_inertia L v w]
    exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos (R := 𝓞 K) w.asIdeal)
  have hmE : m ≤ e := Nat.le_of_dvd he hdiv
  have hK' : Module.finrank K L = m := le_antisymm hK (hmE.trans (heL.trans hlocal))
  have hE' : e = m := le_antisymm (heL.trans (hlocal.trans hK)) hmE
  have hL' : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = m :=
    le_antisymm (hlocal.trans hK) (hmE.trans heL)
  have hmin : minpoly K b = P := (eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hbint) hP hdvd (by rw [hPd, hdim, hK'])).symm
  refine ⟨hK', hE', hL', ?_⟩
  let pb := IntermediateField.adjoin.powerBasis hbint
  rw [Algebra.norm_eq_norm_adjoin,
    show Module.finrank K⟮b⟯ L = 1 by rw [hgen, IntermediateField.finrank_top], pow_one,
    ← IntermediateField.adjoin.powerBasis_gen hbint]
  change Algebra.norm K pb.gen = _
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb]
  have hpb : minpoly K pb.gen = P := by
    rw [show pb.gen = (IntermediateField.adjoin.powerBasis hbint).gen from rfl,
      IntermediateField.adjoin.powerBasis_gen, minpoly_gen, hmin]
  have hpd : pb.dim = m := by rw [← pb.natDegree_minpoly, hpb, hPd]
  have hsign : (-1 : K) ^ m = (-1 : K) ^ (m - 1) * (-1) := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [hpd, hpb]
  dsimp only [P]
  rw [coeff_sub, coeff_X_pow, if_neg (by omega : (0 : ℕ) ≠ m), coeff_C_zero, zero_sub, hsign]
  ring

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.degree_ramificationIdx_norm_of_uniformizer_radical
