import GaloisForLFunctions.HTGeometry.InfiniteSupportCayleyGram
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaTrace

open Filter Set Topology MeasureTheory

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem unitIntervalMeasure_support_infinite : unitIntervalMeasure.support.Infinite := by
  refine (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).mono ?_
  intro x hx
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  have hne : (V ∩ Ioo (0 : ℝ) 1).Nonempty := ⟨x, hxV, hx⟩
  have hvolne : volume (V ∩ Ioo (0 : ℝ) 1) ≠ 0 :=
    hVopen.inter isOpen_Ioo |>.measure_ne_zero volume hne
  have hvolpos : 0 < volume (V ∩ Ioo (0 : ℝ) 1) := bot_lt_iff_ne_bot.mpr hvolne
  have hsmall : V ∩ Ioo (0 : ℝ) 1 ⊆ V ∩ Icc (0 : ℝ) 1 := by
    intro y hy
    exact ⟨hy.1, hy.2.1.le, hy.2.2.le⟩
  have hVpos : 0 < unitIntervalMeasure V := by
    rw [unitIntervalMeasure, Measure.restrict_apply hVopen.measurableSet]
    exact lt_of_lt_of_le hvolpos (measure_mono hsmall)
  exact lt_of_lt_of_le hVpos (measure_mono hVU)

theorem linearIndependent_cayleyConjugateMonomialLp_unitInterval :
    LinearIndependent ℂ (cayleyConjugateMonomialLp unitIntervalMeasure) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  let p : Polynomial ℂ :=
    ∑ n ∈ s, Polynomial.C (c n) * Polynomial.X ^ n
  let f : ℝ → ℂ := fun x => p.eval (star (realCayley x))
  have hfcont : Continuous f :=
    p.continuous.comp (continuous_star.comp continuous_realCayley)
  have hsumcoe_general : ∀ t : Finset ℕ,
      ⇑(∑ n ∈ t, c n • cayleyConjugateMonomialLp unitIntervalMeasure n) =ᵐ[unitIntervalMeasure]
        fun x : ℝ => ∑ n ∈ t, c n * star (realCayley x) ^ n := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using! (Lp.coeFn_zero ℂ 2 unitIntervalMeasure)
    | @insert a t ha iht =>
        rw [Finset.sum_insert ha]
        filter_upwards [Lp.coeFn_add
            (c a • cayleyConjugateMonomialLp unitIntervalMeasure a)
            (∑ n ∈ t, c n • cayleyConjugateMonomialLp unitIntervalMeasure n),
          Lp.coeFn_smul (c a) (cayleyConjugateMonomialLp unitIntervalMeasure a),
          cayleyConjugateMonomialLp_coeFn_ae unitIntervalMeasure a, iht] with
            x hadd hsmul hmono htail
        rw [hadd]
        change ⇑(c a • cayleyConjugateMonomialLp unitIntervalMeasure a) x +
          ⇑(∑ n ∈ t, c n • cayleyConjugateMonomialLp unitIntervalMeasure n) x = _
        rw [hsmul, Pi.smul_apply, hmono, htail]
        simp [Finset.sum_insert ha]
  have hsumcoe :
      ⇑(∑ n ∈ s, c n • cayleyConjugateMonomialLp unitIntervalMeasure n) =ᵐ[unitIntervalMeasure]
        f := by
    simpa [f, p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] using hsumcoe_general s
  have hfzero : f =ᵐ[unitIntervalMeasure] 0 :=
    hsumcoe.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hc)
  have hsuppzero : ∀ x ∈ unitIntervalMeasure.support, f x = 0 :=
    continuous_eq_zero_on_support_of_ae_eq_zero unitIntervalMeasure f hfcont hfzero
  let S : Set ℂ := (fun x : ℝ => star (realCayley x)) '' unitIntervalMeasure.support
  have hSinfinite : S.Infinite := by
    apply unitIntervalMeasure_support_infinite.image
    exact (star_injective.comp injective_realCayley).injOn
  have hSroot : S ⊆ {z : ℂ | p.IsRoot z} := by
    rintro z ⟨x, hx, rfl⟩
    exact hsuppzero x hx
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot p (hSinfinite.mono hSroot)
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff i) hpzero
  simp [p] at hcoeff
  exact hcoeff hi

theorem unitIntervalL2_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (Lp ℂ 2 unitIntervalMeasure) := by
  intro hfinite
  letI : FiniteDimensional ℂ (Lp ℂ 2 unitIntervalMeasure) := hfinite
  exact Module.Finite.not_linearIndependent_of_infinite
    (cayleyConjugateMonomialLp unitIntervalMeasure)
    linearIndependent_cayleyConjugateMonomialLp_unitInterval

noncomputable instance thetaIndex_infinite : Infinite thetaIndex := by
  rw [← not_finite_iff_infinite]
  intro hfinite
  letI : Finite thetaIndex := hfinite
  letI : Fintype thetaIndex := Fintype.ofFinite thetaIndex
  let lpCoe : lp (fun _ : thetaIndex => ℂ) 2 →ₗ[ℂ] (thetaIndex → ℂ) :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hlpCoe : Function.Injective lpCoe := by
    intro x y hxy
    exact Subtype.ext hxy
  letI : Module.Finite ℂ (lp (fun _ : thetaIndex => ℂ) 2) :=
    Module.Finite.of_injective lpCoe hlpCoe
  letI : FiniteDimensional ℂ (Lp ℂ 2 unitIntervalMeasure) :=
    thetaCoord.toLinearEquiv.symm.finiteDimensional
  exact unitIntervalL2_not_finiteDimensional (by infer_instance)

end

end RHTower.HedenmalmThetaSource
