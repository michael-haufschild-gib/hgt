import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.AUniformVarianceBoundForTranslatedMoebiusSections
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.OneHeightExponentForAlmostEveryPrimeTwist
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanIntervalMeanSquare
import GaloisForLFunctions.HTGeometry.InfiniteTorusEquidistribution

/-!
# Variance of ordinary Möbius moments across starting heights

The vertical line of prime twists translates the original polynomial.
Its centered time measurement is an exponential sum on the primitive
ratios. Their angular frequencies are separated by N⁻². The interval
mean-value inequality therefore compares the variance over starting
heights to Haar variance, with an additive length cost of 52N².
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
open Filter Finset Complex MeasureTheory
open scoped ComplexConjugate
open _root_.RHTower hiding linePoint
open _root_.RHTower.Sieve GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.MultiscaleMollifiedZetaField
noncomputable section

/-- Excess of the unmollified, untwisted critical-line moment above the
squarefree diagonal for an interval with left endpoint s and length L. -/
def translatedExcess (N : ℕ) (L s : ℝ) :=
  (∫ t in s..s+L, ‖moebiusPoly N (linePoint t)‖^2) - L*harmonicMoebiusDiagonal N

private def verticalPoint (s : ℝ) : GaugeTorus := clockPhasePoint (fun p => Real.log p) (-s)

private theorem translated_power (a : ℕ → ℂ) (S : Finset ℕ) (s t : ℝ) :
    power a S (verticalPoint s) t = power a S 0 (t+s) := by
  unfold power
  apply congrArg (fun z : ℂ => ‖z‖^2)
  apply sum_congr rfl
  intro n _
  change verticalCoeff a t n * ArithmeticCorrelationGeometry.twist (verticalPoint s) n =
    verticalCoeff a (t+s) n * ArithmeticCorrelationGeometry.twist 0 n
  rw [verticalPoint,twist_clockPhasePoint,twist_zero,mul_one]
  unfold verticalCoeff
  rw [mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem excess_on_vertical_line (N : ℕ) {L : ℝ} (hL : 0 ≤ L) (s : ℝ) :
    translatedExcess N L s =
      centeredMoment (volume.restrict (Set.Ioc 0 L)) N (verticalPoint s) := by
  let a (n : ℕ) : ℂ := MoebiusGram.coeff n
  have hset : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  have ht (t : ℝ) : power a (Icc 1 N) (verticalPoint s) t = ‖moebiusPoly N (linePoint (t+s))‖^2 := by
    rw [translated_power,hset,power_at_trivial_twist]
  rw [translatedExcess,centeredMoment,measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le hL,sub_zero]
  congr 1
  change _ = ∫ t in Set.Ioc 0 L, power a (Icc 1 N) (verticalPoint s) t
  rw [←intervalIntegral.integral_of_le hL,intervalIntegral.integral_congr (fun t _ => ht t),
    intervalIntegral.integral_comp_add_right (fun t : ℝ => ‖moebiusPoly N (linePoint t)‖^2) s
      (a:=0) (b:=L),zero_add,add_comm L s]

private abbrev freq (q : ℕ × ℕ) := ratioFrequency q.1 q.2/(2*Real.pi)

private theorem vertical_charge (q : ℕ × ℕ) (s : ℝ) :
    twist (verticalPoint s) q.1 * conj (twist (verticalPoint s) q.2) = mvExp (freq q) s := by
  simp only [verticalPoint,twist_clockPhasePoint,←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,
    ←Complex.exp_add,mvExp]
  congr 1
  dsimp only [freq,ratioFrequency]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  <;> ring

private theorem frequency_separation {N : ℕ} {q p : ℕ × ℕ}
    (hq : q ∈ primitiveRatioPairs N) (hp : p ∈ primitiveRatioPairs N) (hne : q ≠ p) :
    ((N:ℝ)^2)⁻¹/(2*Real.pi) ≤ |freq q-freq p| := by
  obtain ⟨hqbox,hqc,_⟩ := mem_filter.mp hq
  obtain ⟨hpbox,hpc,_⟩ := mem_filter.mp hp
  obtain ⟨hq1,hq2⟩ := mem_product.mp hqbox
  obtain ⟨hp1,hp2⟩ := mem_product.mp hpbox
  obtain ⟨qa,qA⟩ := mem_Icc.mp hq1
  obtain ⟨qb,qB⟩ := mem_Icc.mp hq2
  obtain ⟨pa,pA⟩ := mem_Icc.mp hp1
  obtain ⟨pb,pB⟩ := mem_Icc.mp hp2
  have hd : q.2*p.1 ≠ q.1*p.2 := fun h => hne (by
    obtain ⟨ha,hb⟩ := VerticalAP.eq_of_coprime_of_mul_eq hqc hpc pa h.symm
    exact Prod.ext ha hb)
  have h := _root_.HTGeometry.inv_le_abs_log_sub_log_of_le (Nat.mul_pos qb pa) (Nat.mul_pos qa pb)
    hd (Nat.mul_le_mul qB pA) (Nat.mul_le_mul qA pB)
  simp only [Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt qb))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt pa)),Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt qa))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt pb))] at h
  simp only [freq,←sub_div,abs_div,abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ |(Real.log q.2 + Real.log p.1) - (Real.log q.1 + Real.log p.2)| := by
      simpa only [sq] using h
    _ = _ := congrArg abs (by unfold ratioFrequency; ring)

/-- On every interval of starting heights the integrated squared error
lies between (Y ± 52 N²) times the exact prime-twist variance. -/
theorem translated_variance_versus_haar {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 ≤ L) (S Y : ℝ) :
    let V := ∫ x, (centeredMoment (volume.restrict (Set.Ioc 0 L)) N x)^2 ∂gaugeHaar
    (Y-52*(N:ℝ)^2)*V ≤ (∫ s in S..S+Y, (translatedExcess N L s)^2) ∧
      (∫ s in S..S+Y, (translatedExcess N L s)^2) ≤ (Y+52*(N:ℝ)^2)*V := by
  classical
  let ν := volume.restrict (Set.Ioc 0 L)
  let P := primitiveRatioPairs N
  let w (q : ℕ × ℕ) := (MoebiusGram.atom N q.1 q.2:ℂ)*timeTransform ν (ratioFrequency q.1 q.2)
  let D := ((N:ℝ)^2)⁻¹/(2*Real.pi)
  have hD : 0 < D := div_pos (inv_pos.mpr (sq_pos_of_pos (Nat.cast_pos.mpr hN))) (by positivity)
  have cost : 26/(Real.pi*D)=52*(N:ℝ)^2 := by
    dsimp only [D]
    field_simp [Real.pi_ne_zero,Nat.cast_ne_zero.mpr hN.ne']
    <;> ring
  have hsep (q p : P) (hne : q ≠ p) : D ≤ |freq q-freq p| :=
    frequency_separation q.2 p.2 (fun e => hne (Subtype.ext e))
  have hpoint (s : ℝ) : (translatedExcess N L s)^2 = ‖∑ q : P, w q*mvExp (freq q) s‖^2 := by
    have he := centered_moment_eq_pairForm ν N (verticalPoint s)
    rw [←excess_on_vertical_line N hL s] at he
    have hs : (translatedExcess N L s:ℂ) = ∑ q : P, w q*mvExp (freq q) s := by
      rw [he,pairForm]
      simp only [vertical_charge]
      exact (Finset.sum_attach P (fun q => w q*mvExp (freq q) s)).symm
    rw [←hs,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hmass : (∑ q : P, ‖w q‖^2) = ∫ x, (centeredMoment ν N x)^2 ∂gaugeHaar := by
    rw [integral_centered_moment_sq]
    have ht := Finset.sum_attach P (fun q => ‖w q‖^2)
    refine ht.trans (sum_congr rfl (fun q _ => ?_))
    dsimp only [w]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  have hlo := interval_integral_normSq_expSum_ge (fun q : P => freq q) (fun q : P => w q) (a:=S) (ℓ:=Y) hD hsep
  have hhi := interval_integral_normSq_expSum_le (fun q : P => freq q) (fun q : P => w q) (a:=S) (ℓ:=Y) hD hsep
  rw [cost,hmass] at hlo hhi
  simp_rw [←hpoint] at hlo hhi
  exact ⟨hlo,hhi⟩

/-- An unconditional estimate for the *untwisted* Möbius polynomial,
uniform in the location of the outer averaging interval. -/
theorem translated_moebius_variance_bound {N : ℕ} (hN : 0 < N) {L Y : ℝ}
    (hL : 0 ≤ L) (hY : 0 ≤ Y) (S : ℝ) :
    (∫ s in S..S+Y, (translatedExcess N L s)^2) ≤
      6*(Y+52*(N:ℝ)^2)*L*(1+Real.log ((N:ℝ)+1))^4 := by
  have h := (translated_variance_versus_haar hN hL S Y).2
  have hvar := sharp_interval_moebius_variance N hL
  rw [sub_zero] at hvar
  exact h.trans ((mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ Y+52*(N:ℝ)^2)).trans_eq (by ring))

/-- Measure of starting heights for which the ordinary sharp local mean
misses the squarefree diagonal by at least ε per unit length. -/
theorem measure_exceptional_starting_heights {N : ℕ} (hN : 0 < N) {L Y ε : ℝ}
    (hL : 0 < L) (hY : 0 ≤ Y) (hε : 0 < ε) (S : ℝ) :
    (volume.restrict (Set.Ioc S (S+Y))).real {s | ε*L ≤ |translatedExcess N L s|} ≤
      6*(Y+52*(N:ℝ)^2)*(1+Real.log ((N:ℝ)+1))^4/(L*ε^2) := by
  let μ := volume.restrict (Set.Ioc S (S+Y))
  let F (s : ℝ) := (translatedExcess N L s)^2
  have hc : Continuous (translatedExcess N L) := by
    have he : translatedExcess N L = fun s =>
        centeredMoment (volume.restrict (Set.Ioc 0 L)) N (verticalPoint s) :=
      funext (excess_on_vertical_line N hL.le)
    rw [he]
    exact (continuous_centeredMoment _ _).comp
      ((continuous_clockPhasePoint (fun p : ℕ => Real.log p)).comp continuous_neg)
  have hint : Integrable F μ := ((hc.pow 2).intervalIntegrable S (S+Y)).1
  have hm := mul_meas_ge_le_integral_of_nonneg (μ:=μ) (.of_forall fun s => (sq_nonneg (translatedExcess N L s)))
    hint ((ε*L)^2)
  have he : {s | (ε*L)^2 ≤ F s} = {s | ε*L ≤ |translatedExcess N L s|} := by
    ext s
    change (ε*L)^2 ≤ (translatedExcess N L s)^2 ↔ ε*L ≤ |translatedExcess N L s|
    rw [←sq_abs (translatedExcess N L s),sq_le_sq₀ (mul_nonneg hε.le hL.le) (abs_nonneg _)]
  change (ε*L)^2*μ.real {s | (ε*L)^2 ≤ F s} ≤ ∫ s, F s ∂μ at hm
  rw [he] at hm
  have hb := translated_moebius_variance_bound hN hL.le hY S
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hY)] at hb
  have hh := hm.trans hb
  apply (le_div_iff₀ (mul_pos hL (sq_pos_of_pos hε))).mpr
  apply le_of_mul_le_mul_left (a:=L) _ hL
  nlinarith only [hh]

end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
