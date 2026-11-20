import GaloisForLFunctions.HTGeometry.DiscreteWeylCriterion
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Data.Nat.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Metric Weyl sampling along distinct integer clocks

Fourier orthogonality gives exact mean-square error at every prefix.
Summing the errors along square lengths and bounding the intervening terms
gives almost sure convergence along the entire sequence.
-/
open MeasureTheory Finset Filter AddCircle
open scoped Topology ComplexConjugate

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev circHaar := (haarAddCircle : Measure UnitAddCircle)

private def clockSum (b : ℕ → ℤ) (N : ℕ) : C(UnitAddCircle,ℂ) :=
  ∑ j ∈ range N, fourier (b j)

/-- Exact mean-square size of the unnormalised Weyl sum for distinct integers. -/
theorem integerClock_fourier_second_moment (b : ℕ → ℤ) (hb : Function.Injective b) (N : ℕ) :
    ∫ x, ‖∑ j ∈ range N, fourier (b j) x‖^2 ∂circHaar = (N : ℝ) := by
  let S := clockSum b N
  have hinner : inner ℂ (ContinuousMap.toLp 2 circHaar ℂ S)
      (ContinuousMap.toLp 2 circHaar ℂ S) = (N : ℂ) := by
    change inner ℂ (ContinuousMap.toLp 2 circHaar ℂ (∑ j ∈ range N, fourier (b j)))
      (ContinuousMap.toLp 2 circHaar ℂ (∑ j ∈ range N, fourier (b j))) = _
    simp only [map_sum, sum_inner, inner_sum]
    have ho := orthonormal_iff_ite.mp ((orthonormal_fourier (T := 1)).comp b hb)
    change (∑ j ∈ range N, ∑ k ∈ range N,
      inner ℂ (fourierLp (T := 1) 2 (b k)) (fourierLp 2 (b j))) = _
    simp only [Function.comp_apply] at ho
    simp [ho, Finset.filter_true_of_mem (fun j (hj : j ∈ range N) => mem_range.mp hj)]
  rw [ContinuousMap.inner_toLp] at hinner
  have hz : ∀ x, S x * (starRingEnd ℂ) (S x) = ((‖S x‖^2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.mul_conj, Complex.sq_norm]
  simp_rw [hz] at hinner
  rw [integral_complex_ofReal] at hinner
  have h := congrArg Complex.re hinner
  simpa [S, clockSum] using h

private def squareError (b : ℕ → ℤ) (k : ℕ) (x : UnitAddCircle) : ℝ :=
  ‖clockSum b (k^2) x‖^2 / (k : ℝ)^4

private theorem square_norm_converges (b : ℕ → ℤ) (hb : Function.Injective b) :
    ∀ᵐ x ∂circHaar, Tendsto (fun k => squareError b k x) atTop (𝓝 0) := by
  have hc (k) : Continuous (squareError b k) :=
    ((clockSum b (k^2)).continuous.norm.pow 2).div_const _
  have hp (k x) : 0 ≤ squareError b k x := by unfold squareError; positivity
  have hi (k) : ∫ x, squareError b k x ∂circHaar = 1/(k:ℝ)^2 := by
    simp only [squareError, integral_div]
    have h := integerClock_fourier_second_moment b hb (k^2)
    rw [show (∫ x, ‖clockSum b (k^2) x‖^2 ∂circHaar) = ((k^2:ℕ):ℝ) by simpa [clockSum] using h]
    by_cases hk : k = 0
    · simp [hk]
    · push_cast; field_simp
  have hfin : ∀ᵐ x ∂circHaar, (∑' k, ENNReal.ofReal (squareError b k x)) < ⊤ := by
    apply ae_lt_top' (AEMeasurable.tsum (fun k => ((hc k).measurable.ennreal_ofReal).aemeasurable))
    rw [lintegral_tsum (fun k => ((hc k).measurable.ennreal_ofReal).aemeasurable)]
    have heq (k) : (∫⁻ x, ENNReal.ofReal (squareError b k x) ∂circHaar) = ENNReal.ofReal (1/(k:ℝ)^2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((hc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (ae_of_all _ (hp k)), hi]
    simp only [heq]
    exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).tsum_ofReal_ne_top
  filter_upwards [hfin] with x hx
  have hnorm (k) : ‖squareError b k x‖ₑ = ENNReal.ofReal (squareError b k x) := by
    rw [Real.enorm_eq_ofReal (hp k x)]
  have hs := tsum_enorm_ne_top_iff_summable_norm.mp (by simpa only [hnorm] using hx.ne :
    (∑' k, ‖squareError b k x‖ₑ) ≠ ⊤)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hp _ _)] using hs.tendsto_atTop_zero

/-- For almost every base phase, distinct integer observation multipliers
cancel every nonconstant scalar character in the Cesàro limit. -/
theorem ae_integerClock_weyl (b : ℕ → ℤ) (hb : Function.Injective b) :
    ∀ᵐ x ∂circHaar, Tendsto (fun N : ℕ => (N:ℂ)⁻¹ *
      ∑ j ∈ range N, fourier (b j) x) atTop (𝓝 0) := by
  filter_upwards [square_norm_converges b hb] with x hx
  have hroot : Tendsto Nat.sqrt atTop atTop := tendsto_atTop.2 fun k =>
    (eventually_ge_atTop (k^2)).mono fun _ => Nat.le_sqrt'.2
  have hsq : Tendsto (fun k : ℕ => ‖clockSum b (k^2) x‖ / (k:ℝ)^2) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hx
    have he (k : ℕ) : Real.sqrt (squareError b k x) = ‖clockSum b (k^2) x‖ / (k:ℝ)^2 := by
      rw [squareError,show (k:ℝ)^4 = ((k:ℝ)^2)^2 by ring, ← div_pow,
        Real.sqrt_sq (by positivity)]
    change Tendsto (fun k => Real.sqrt (squareError b k x)) atTop (𝓝 (Real.sqrt 0)) at hs
    simpa only [he,Real.sqrt_zero] using hs
  have herr := (hsq.comp hroot).add ((tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp hroot)
  rw [add_zero] at herr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ herr
  filter_upwards [eventually_ge_atTop 1] with N hN
  let m := Nat.sqrt N
  have hm : 1 ≤ m := Nat.le_sqrt'.mpr (by simpa using hN)
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hm)
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hN)
  have hlo : m^2 ≤ N := Nat.sqrt_le' N
  have hhi : N ≤ m^2+2*m := by simpa only [sq,two_mul,add_assoc] using Nat.sqrt_le_add N
  have hlo' : (m:ℝ)^2 ≤ N := by exact_mod_cast hlo
  have htail : ‖∑ j ∈ Ico (m^2) N, fourier (b j) x‖ ≤ 2*(m:ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Ico (m^2) N, (1:ℝ) := (norm_sum_le _ _).trans
        (sum_le_sum fun j _ => (show ‖fourier (b j) x‖ = 1 from Circle.norm_coe _).le)
      _ = ((N-m^2:ℕ):ℝ) := by simp
      _ ≤ 2*(m:ℝ) := by exact_mod_cast (show N-m^2 ≤ 2*m by omega)
  let Y := ‖clockSum b (m^2) x‖
  have hS : ‖∑ j ∈ range N, fourier (b j) x‖ ≤ Y + 2*(m:ℝ) := by
    rw [← sum_range_add_sum_Ico _ hlo]
    simpa only [Y,clockSum,ContinuousMap.sum_apply] using
      (norm_add_le _ _).trans (add_le_add (le_refl ‖∑ j ∈ range (m^2), fourier (b j) x‖) htail)
  rw [norm_mul,norm_inv,Complex.norm_natCast,← div_eq_inv_mul]
  change _ ≤ Y / (m:ℝ)^2 + 2/(m:ℝ)
  calc
    _ ≤ (Y+2*(m:ℝ)) / N := div_le_div_of_nonneg_right hS hN0.le
    _ ≤ (Y+2*(m:ℝ)) / (m:ℝ)^2 :=
      div_le_div_of_nonneg_left (by dsimp [Y]; positivity) (by positivity) hlo'
    _ = _ := by field_simp

#print axioms ae_integerClock_weyl

/-- The unit-circle Weyl law pulls back to Lebesgue-almost every real frequency. -/
theorem ae_integerClock_exp (b : ℕ → ℤ) (hb : Function.Injective b) :
    ∀ᵐ u : ℝ, Tendsto (fun N : ℕ => (N:ℂ)⁻¹ *
      ∑ j ∈ range N, Complex.exp (((b j : ℝ) * u : ℝ) * Complex.I)) atTop (𝓝 0) := by
  let P (u : ℝ) := Tendsto (fun N : ℕ => (N:ℂ)⁻¹ *
      ∑ j ∈ range N, fourier (b j) (u : UnitAddCircle)) atTop (𝓝 0)
  have hvol : ∀ᵐ x ∂(volume : Measure UnitAddCircle), Tendsto (fun N : ℕ => (N:ℂ)⁻¹ *
      ∑ j ∈ range N, fourier (b j) x) atTop (𝓝 0) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simpa using ae_integerClock_weyl b hb
  have hP : ∀ᵐ u ∂(volume : Measure ℝ), P u := by
    have hlocal (i : ℤ) : ∀ᵐ u ∂(volume.restrict (Set.Ioc (i:ℝ) (i+1))), P u :=
      (AddCircle.measurePreserving_mk 1 (i:ℝ)).quasiMeasurePreserving.tendsto_ae.eventually hvol
    have h := (ae_restrict_iUnion_iff _ P).mpr hlocal
    rwa [iUnion_Ioc_intCast, Measure.restrict_univ] at h
  let c := (2*Real.pi)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscale : Measure.QuasiMeasurePreserving (fun u : ℝ => c*u) volume volume := by
    refine ⟨measurable_const_mul _,?_⟩
    rw [Real.map_volume_mul_left hc]
    exact Measure.smul_absolutelyContinuous
  filter_upwards [hscale.tendsto_ae.eventually hP] with u hu
  apply hu.congr
  intro N
  congr 1
  apply sum_congr rfl
  intro j _
  rw [fourier_coe_apply]
  congr 1
  dsimp [c]
  push_cast
  field_simp

/-- A positively homogeneous real observable avoids every Lebesgue-null set
off zero for almost every parameter. Restriction to a ray turns the observable
into multiplication by one scalar; Fubini and one invertible dilation remove
the extra ray parameter. -/
theorem homogeneous_observable_ae {m : ℕ} (g : (Fin m → ℝ) → ℝ) (hg : Measurable g)
    (hscale : ∀ (a : ℝ), 0 < a → ∀ p, g (a • p) = a*g p)
    {P : ℝ → Prop} (hP : ∀ᵐ u ∂(volume : Measure ℝ), P u) :
    ∀ᵐ p ∂(volume : Measure (Fin m → ℝ)), g p ≠ 0 → P (g p) := by
  obtain ⟨B,hsub,hm,hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  let G := {p | g p = 0} ∪ (g ⁻¹' B)ᶜ
  have hG : MeasurableSet G := (measurableSet_eq_fun hg measurable_const).union
    (hm.preimage hg).compl
  let Q (p : Fin m → ℝ) (a : ℝ) := 0 < a → a • p ∈ G
  have hmQ : MeasurableSet {x : (Fin m → ℝ) × ℝ | Q x.1 x.2} :=
    (measurableSet_lt (show Measurable (fun _ : (Fin m → ℝ) × ℝ => (0:ℝ)) from measurable_const) measurable_snd).compl.union
      (hG.preimage (measurable_snd.smul measurable_fst)) |>.congr
        (by ext; simp [Q,imp_iff_not_or])
  have hrow (p) : ∀ᵐ a ∂(volume : Measure ℝ), Q p a := by
    by_cases h0 : g p = 0
    · exact ae_of_all _ fun a ha => Or.inl (by simp [hscale a ha p,h0])
    have hbad : volume ((fun a : ℝ => g p*a) ⁻¹' B) = 0 := by
      rw [Real.volume_preimage_mul_left h0,hnull,mul_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad] with a ha
    intro hpos
    right
    change g (a • p) ∉ B
    rwa [hscale a hpos p,mul_comm]
  have hcol := (Measure.ae_ae_comm (μ := (volume : Measure (Fin m → ℝ))) (ν := volume) hmQ).mp
    (ae_of_all _ hrow)
  obtain ⟨a,ha,hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (by norm_num [Real.volume_Ioc] : volume (Set.Ioc (0:ℝ) 1) ≠ 0) (ae_restrict_of_ae hcol)
  have h := (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin m → ℝ))
    (inv_ne_zero ha.1.ne')).tendsto_ae.eventually hgood
  filter_upwards [h] with p hp
  have hmemb : p ∈ G := by simpa [Q,ha.1.ne',smul_smul] using hp ha.1
  intro hne
  exact by_contra fun hneg => (hmemb.resolve_left hne) (hsub hneg)

#print axioms ae_integerClock_exp
#print axioms homogeneous_observable_ae
end
end GaloisForLFunctions.HTGeometry
