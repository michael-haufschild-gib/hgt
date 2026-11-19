import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSquareChargeInsideTheDiagonalInterval

/-!
# The displacement integral of the ordinary prime band

Time restriction and deletion of state displacements act on different variables.
Translation by each logarithmic abscissa gives one integrable density in the
displacement variable, also for profiles restricted to measurable sets.
-/

noncomputable section
open scoped Classical
open Set MeasureTheory Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- Active denominators when physical time is restricted to A. -/
def ordinaryIndicesAt (k L : ℕ) (A : Set ℝ) (v : ℝ) : Finset ℕ :=
  (Finset.Ioc k L).filter fun n => v+Real.log n ∈ A ∧ pastCriticalEdge n (v+Real.log n)

/-- Dividing the physical edge by its exponential abscissa gives the relative width. -/
theorem pastCriticalEdge_at_displacement {n : ℕ} (hn : 0<n) (v : ℝ) :
    let t := v+Real.log n
    pastCriticalEdge n t ↔ 1+Real.exp (-t/2)*Real.sqrt t < Real.exp (-v) := by
  let t := v+Real.log n
  have hn' : Real.exp t*Real.exp (-v)=(n:ℝ) := by
    rw [← Real.exp_add,show t+ -v=Real.log n by dsimp only [t]; ring,Real.exp_log (Nat.cast_pos.mpr hn)]
  have he : Real.exp t*Real.exp (-t/2)=Real.exp (t/2) := by rw [← Real.exp_add]; congr 1; ring
  change Real.exp t+Real.exp (t/2)*Real.sqrt t < (n:ℝ) ↔ _
  calc _ ↔ Real.exp t*(1+Real.exp (-t/2)*Real.sqrt t)<Real.exp t*Real.exp (-v) := by
             rw [hn',mul_add,mul_one,← mul_assoc,he]
       _ ↔ _ := mul_lt_mul_iff_right₀ (Real.exp_pos t)

private theorem coeff_eq (n : ℕ) :
    ordinaryPrimeExcessCoeff n = (if n.Prime then vonMangoldt n else 0)-1 := by
  unfold ordinaryPrimeExcessCoeff
  by_cases hp : n.Prime
  · rw [if_pos hp,if_pos hp,vonMangoldt_apply_prime hp]
  · rw [if_neg hp,if_neg hp]

/-- Translating each atom by its logarithmic abscissa expresses the physical
band on any measurable time set as an integral over state displacements. -/
theorem ordinaryBand_displacement_integral {Φ : ℝ → ℝ} (hi : Integrable Φ)
    (k L : ℕ) (T : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    let G := fun v => Φ v*(fractionalPrimeExcess (ordinaryIndicesAt k L A v) (Real.exp (T-v)) /
      Real.sqrt (Real.exp (T-v)))
    Integrable G ∧ (∫ t in A, ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t)) =
      ∫ v, G v := by
  let I := Finset.Ioc k L
  let E := fun n : ℕ => A ∩ {t : ℝ | pastCriticalEdge n t}
  let f := fun (n : ℕ) => (E n).indicator (fun t => ordinaryPrimeExcessCoeff n*continuousIntegerAtom Φ n t*
    fractionalPrimeTest (T-t))
  have hf (n : ℕ) : Integrable (f n) := by
    have hE : MeasurableSet (E n) := hA.inter (measurableSet_lt
      (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const)
    have h := ((hi.comp_sub_right (Real.log n)).const_mul (Real.sqrt n)⁻¹).const_mul (ordinaryPrimeExcessCoeff n)
    have hK := measurable_fractionalPrimeTest.comp (show Measurable (fun t : ℝ => T-t) from measurable_const.sub measurable_id)
    apply Integrable.indicator _ hE
    apply h.abs.mono' (h.aestronglyMeasurable.mul hK.aestronglyMeasurable)
    apply Eventually.of_forall
    intro t
    change |ordinaryPrimeExcessCoeff n*continuousIntegerAtom Φ n t * fractionalPrimeTest (T-t)| ≤ _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1
  have hrow (t : ℝ) : (∑ n ∈ I, f n t)= A.indicator (fun u => ordinaryPrimeComplementBand Φ k L u*
      fractionalPrimeTest (T-u)) t := by
    by_cases h : t∈A
    · rw [indicator_of_mem h,ordinaryPrimeComplementBand,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      by_cases he : pastCriticalEdge n t
      · rw [if_pos he,show f n t=_ from indicator_of_mem (show t∈E n from ⟨h,he⟩) _,coeff_eq]
      · rw [if_neg he,zero_mul]; exact indicator_of_notMem (fun hm : t∈E n => he hm.2) _
    · rw [indicator_of_notMem h]
      exact Finset.sum_eq_zero fun n _ => indicator_of_notMem (fun hm : t∈E n => h hm.1) _
  let p := fun (n : ℕ) (v : ℝ) => f n (v+Real.log n)
  have hp (n : ℕ) : Integrable (p n) := (hf n).comp_add_right _
  have hread (v : ℝ) : (∑ n ∈ I, p n v)=Φ v*(fractionalPrimeExcess (ordinaryIndicesAt k L A v)
      (Real.exp (T-v))/Real.sqrt (Real.exp (T-v))) := by
    rw [fractionalPrimeExcess,ordinaryIndicesAt,Finset.sum_filter,Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
    let t := v+Real.log n
    by_cases hm : t ∈ E n
    · rw [if_pos (show v+Real.log n∈A ∧ pastCriticalEdge n (v+Real.log n) from hm)]
      change (E n).indicator _ t=_
      rw [indicator_of_mem hm]
      have hphase : Real.exp (T-t)=Real.exp (T-v)/n := by
        rw [show T-t=(T-v)-Real.log n by dsimp only [t]; ring,Real.exp_sub,Real.exp_log hn0]
      have hroot : (Real.sqrt n)⁻¹=Real.exp (-(Real.log n)/2) := by
        rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log hn0]
      have hscale : (Real.sqrt n)⁻¹*Real.exp (-(T-t)/2)=(Real.sqrt (Real.exp (T-v)))⁻¹ := by
        rw [hroot,← Real.exp_add,← Real.exp_half,← Real.exp_neg]
        congr 1; dsimp only [t]; ring
      dsimp only [continuousIntegerAtom,fractionalPrimeTest]
      rw [show t-Real.log n=v by dsimp only [t]; ring,hphase]
      linear_combination ordinaryPrimeExcessCoeff n*Φ v*Int.fract (Real.exp (T-v)/n)*hscale
    · rw [if_neg (show ¬(v+Real.log n∈A ∧ pastCriticalEdge n (v+Real.log n)) from hm),zero_div,mul_zero]
      exact indicator_of_notMem hm _
  have hpint := integrable_finsetSum I (fun n _ => hp n)
  refine ⟨hpint.congr (Eventually.of_forall hread),?_⟩
  rw [← integral_indicator hA]
  calc _ = ∫ t, ∑ n ∈ I, f n t := integral_congr_ae (Eventually.of_forall fun t => (hrow t).symm)
       _ = ∑ n ∈ I, ∫ t, f n t := integral_finsetSum _ (fun n _ => hf n)
       _ = ∑ n ∈ I, ∫ v, p n v := Finset.sum_congr rfl fun n _ => (integral_add_right_eq_self (f n) (Real.log n)).symm
       _ = ∫ v, ∑ n ∈ I, p n v := (integral_finsetSum _ (fun n _ => hp n)).symm
       _ = _ := integral_congr_ae (Eventually.of_forall hread)

/-- Signed density of the original middle response in the displacement variable. -/
def ordinaryDisplacementDensity (Φ : ℝ → ℝ) (m T : ℝ) (k L : ℕ) (v : ℝ) : ℝ :=
  m*(Φ v*(fractionalPrimeExcess (ordinaryIndicesAt k L (Ioc (T/6) (6*T)) v) (Real.exp (T-v)) /
    Real.sqrt (Real.exp (T-v))))

theorem integrable_ordinaryDisplacementDensity {Φ : ℝ → ℝ} (hi : Integrable Φ) (m T : ℝ) (k L : ℕ) :
    Integrable (ordinaryDisplacementDensity Φ m T k L) :=
  ((ordinaryBand_displacement_integral hi k L T _ measurableSet_Ioc).1).const_mul m

/-- Deleting a measurable displacement set changes the reading by exactly
the signed mass of that set, with the same outer multiplier. -/
theorem ordinaryBand_delete_eq_setIntegral {Φ : ℝ → ℝ} (hi : Integrable Φ) (m T : ℝ) (k L : ℕ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    m*(∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t)) -
      m*(∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand (Eᶜ.indicator Φ) k L t*fractionalPrimeTest (T-t)) =
      ∫ v in E, ordinaryDisplacementDensity Φ m T k L v := by
  obtain ⟨hf,hf'⟩ := ordinaryBand_displacement_integral hi k L T _ measurableSet_Ioc
  obtain ⟨hg,hg'⟩ := ordinaryBand_displacement_integral (hi.indicator hE.compl) k L T _ measurableSet_Ioc
  rw [hf',hg',← mul_sub,← integral_sub hf hg,← integral_const_mul,← integral_indicator hE]
  apply integral_congr_ae (Eventually.of_forall fun v => ?_)
  by_cases hv : v∈E <;> simp [ordinaryDisplacementDensity,hv]

/-- A logarithmic envelope suffices on any subset of the denominator band. -/
theorem fractionalPrimeExcess_abs_le_band {S : Finset ℕ} {k L : ℕ} (hS : S ⊆ Finset.Ioc k L) (y : ℝ) :
    |fractionalPrimeExcess S y| ≤ (1+Real.log L)*L := by
  have hcard : S.card≤L := (Finset.card_le_card hS).trans (by rw [Nat.card_Ioc]; exact Nat.sub_le ..)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _ ∈ S, (1+Real.log L) := Finset.sum_le_sum fun n hn => by
            obtain ⟨hk,hnL⟩ := Finset.mem_Ioc.mp (hS hn)
            have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk)) (Nat.cast_le.mpr hnL)
            rw [abs_mul,abs_of_nonneg (Int.fract_nonneg _)]
            apply (mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le).trans
            unfold ordinaryPrimeExcessCoeff
            by_cases hp : n.Prime
            · rw [if_pos hp]
              have h := abs_sub (Real.log (n:ℝ)) 1
              rw [abs_of_nonneg (Real.log_natCast_nonneg _),abs_one] at h
              linarith only [h,hlog]
            · simp only [if_neg hp,zero_sub,abs_neg,abs_one]
              linarith only [Real.log_natCast_nonneg L]
       _ ≤ _ := by
            rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
            exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (by have := Real.log_natCast_nonneg L; positivity)

/-- On the negative half-line, confinement prices each displacement by
its exponential density, independently of the set of active abscissae. -/
theorem ordinaryDisplacementDensity_bound {Φ : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hb : ∀ v, |Φ v|≤C*Real.exp (2*v)) (m T : ℝ) (k L : ℕ) {v : ℝ} (hv : v≤0) :
    |ordinaryDisplacementDensity Φ m T k L v| ≤
      (|m| * C*((1+Real.log L)*L)*Real.exp (-T/2))*Real.exp (2*v) := by
  let S := ordinaryIndicesAt k L (Ioc (T/6) (6*T)) v
  have hrow := fractionalPrimeExcess_abs_le_band (k := k) (L := L)
    (show S ⊆ Finset.Ioc k L from Finset.filter_subset ..) (Real.exp (T-v))
  have hroot : (Real.sqrt (Real.exp (T-v)))⁻¹≤Real.exp (-T/2) := by
    rw [← Real.exp_half,← Real.exp_neg,Real.exp_le_exp]; linarith only [hv]
  change |m*(Φ v*(fractionalPrimeExcess S (Real.exp (T-v))/Real.sqrt (Real.exp (T-v))))| ≤ _
  rw [abs_mul,abs_mul,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),div_eq_mul_inv]
  have hr := mul_le_mul hrow hroot (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (by have := Real.log_natCast_nonneg L; positivity)
  exact (mul_le_mul_of_nonneg_left (mul_le_mul (hb v) hr (by positivity)
    (mul_nonneg hC (Real.exp_pos _).le)) (abs_nonneg m)).trans_eq (by ring)

#print axioms ordinaryBand_delete_eq_setIntegral
end GaloisForLFunctions.ExclusionOfTheCriticalState
