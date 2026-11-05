import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheEvaluationGramHasNoSingularPrecontactPart
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheConstantCollarsHaveTheirExactLeadingEnergy
import GaloisForLFunctions.RHTower.CorrelationBoundsCountNotLocation

/-!
# Endpoint slopes of finite evaluation Grams

A finite combination of evaluation increments is approximated by the same
two constant collars, with its combined endpoint traces as coefficients.
The squared error is negligible compared with the aperture increment.
Thus the right derivative is the sum of the two squared trace norms, and
its integral recovers every precontact Gram increment exactly.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open _root_.RHTower CanonicalSystemOfTheWindowTower
open CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

private theorem normalized_energy_stability {S ε : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p q e h : ℝ, 0 ≤ p → 0 ≤ e → 0 < h →
      |q^2-p^2| ≤ 2*p*e+e^2 → |p^2/h-S| < δ → e^2/h < δ →
      |q^2/h-S| < ε := by
  let B : ℝ → ℝ := fun d => d+2*Real.sqrt (S+d)*Real.sqrt d+d
  have ht : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hx : Tendsto (fun d : ℝ => d) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hs₀ : Tendsto (fun d : ℝ => S+d) (𝓝[>] (0 : ℝ)) (𝓝 (S+0)) :=
      tendsto_const_nhds.add hx
    have hs := hs₀.sqrt
    have hh := ((hs.const_mul 2).mul hx.sqrt)
    simpa only [Real.sqrt_zero, mul_zero, add_zero, zero_add, B] using (hx.add hh).add hx
  have hpos : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hb⟩ := (hpos.and (ht.eventually (Iio_mem_nhds hε))).exists
  change 0 < δ at hδ
  refine ⟨δ, hδ, fun p q e h hp he hh hdiff hu herr => ?_⟩
  have hSd : 0 ≤ S+δ := add_nonneg hS hδ.le
  have hpSq : p^2 ≤ h*(S+δ) := by
    have hf := (div_lt_iff₀ hh).mp (show p^2/h < S+δ from by linarith only [(abs_lt.mp hu).2])
    nlinarith only [hf]
  have heSq : e^2 ≤ h*δ := by
    have hf := (div_lt_iff₀ hh).mp herr
    nlinarith only [hf]
  have hp' : p ≤ Real.sqrt h*Real.sqrt (S+δ) := by
    apply (sq_le_sq₀ hp (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hh.le, Real.sq_sqrt hSd] using hpSq
  have he' : e ≤ Real.sqrt h*Real.sqrt δ := by
    apply (sq_le_sq₀ he (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hh.le, Real.sq_sqrt hδ.le] using heSq
  have hc : p*e ≤ h*(Real.sqrt (S+δ)*Real.sqrt δ) := by
    calc
      _ ≤ (Real.sqrt h*Real.sqrt (S+δ))*(Real.sqrt h*Real.sqrt δ) :=
        mul_le_mul hp' he' he (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = (Real.sqrt h)^2*(Real.sqrt (S+δ)*Real.sqrt δ) := by ring
      _ = _ := by rw [Real.sq_sqrt hh.le]
  have hn : |q^2-p^2| ≤ h*(2*Real.sqrt (S+δ)*Real.sqrt δ+δ) := by
    nlinarith only [hdiff, hc, heSq]
  have hn' : |q^2/h-p^2/h| ≤ 2*Real.sqrt (S+δ)*Real.sqrt δ+δ := by
    rw [← sub_div, abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).mpr (by nlinarith only [hn])
  calc
    |q^2/h-S| = |(q^2/h-p^2/h)+(p^2/h-S)| := by congr 1; ring
    _ ≤ |q^2/h-p^2/h|+|p^2/h-S| := abs_add_le _ _
    _ < (2*Real.sqrt (S+δ)*Real.sqrt δ+δ)+δ := add_lt_add_of_le_of_lt hn' hu
    _ = B δ := by dsimp only [B]; ring
    _ < ε := hb


variable {ι : Type*} [Fintype ι]

/-- The two-trace quadratic energy of a finite evaluation combination. -/
def evalCombinationEndpointEnergy (α z : ι → ℂ) (a : PrecontactAperture) : ℝ :=
  ‖∑ i, α i*evalLeftEndpointTrace a (z i)‖^2+
    ‖∑ i, α i*evalRightEndpointTrace a (z i)‖^2

/-- Finite combinations retain the vanishing normalized collar error. -/
theorem eventually_combination_constantCollar_error_lt
    {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) (α z : ι → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ (b : PrecontactAperture)
      (hab : a.1.1 ≤ b.1.1), b.1.1 = a.1.1+h →
      ∀ l r : WeilHilbertBeforeContact b,
      ccmArchimedeanFormEmbedding b.1 (toForm b l) =
        logarithmicIntervalSource (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding b.1 (toForm b r) =
        logarithmicIntervalSource a.1.1 (a.1.1+h) →
      ‖(Real.sqrt (Real.log (1/h)) : ℂ)⁻¹ •
        ((∑ i, α i*evalLeftEndpointTrace a (z i)) • l+
         (∑ i, α i*evalRightEndpointTrace a (z i)) • r)-
          combinationIncrement α z hab‖^2/h < ε := by
  classical
  let C := ∑ i, ‖α i‖^2
  let N := (Fintype.card ι : ℝ)
  let δ := ε/(C*N+1)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => sq_nonneg ‖α i‖
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hden : 0 < C*N+1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ i,
      ∀ (b : PrecontactAperture) (hab : a.1.1 ≤ b.1.1), b.1.1 = a.1.1+h →
      ∀ l r : WeilHilbertBeforeContact b,
      ccmArchimedeanFormEmbedding b.1 (toForm b l) =
        logarithmicIntervalSource (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding b.1 (toForm b r) =
        logarithmicIntervalSource a.1.1 (a.1.1+h) →
      ‖(Real.sqrt (Real.log (1/h)) : ℂ)⁻¹ •
        (evalLeftEndpointTrace a (z i) • l+evalRightEndpointTrace a (z i) • r)-
          evalVectorIncrement hab (z i)‖^2/h < δ := by
    rw [Filter.eventually_all]
    exact fun i => eventually_constantCollar_trial_error_lt hac (z i) hδ
  filter_upwards [hall, self_mem_nhdsWithin] with h hall hh
  change 0 < h at hh
  intro b hab hb l r hl hr
  let t : ℂ := (Real.sqrt (Real.log (1/h)) : ℂ)⁻¹
  let e : ι → WeilHilbertBeforeContact b := fun i =>
    t • (evalLeftEndpointTrace a (z i) • l+evalRightEndpointTrace a (z i) • r)-
      evalVectorIncrement hab (z i)
  have hid : t • ((∑ i, α i*evalLeftEndpointTrace a (z i)) • l+
      (∑ i, α i*evalRightEndpointTrace a (z i)) • r)-combinationIncrement α z hab =
      ∑ i, α i • e i := by
    simp only [e, combinationIncrement, smul_sub, Finset.sum_sub_distrib,
      Finset.sum_smul, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib,
      mul_left_comm]
  change ‖t • _-combinationIncrement α z hab‖^2/h < ε
  rw [hid]
  have heach (i : ι) : ‖e i‖^2/h ≤ δ := (hall i b hab hb l r hl hr).le
  have hsum : (∑ i, ‖e i‖^2)/h ≤ N*δ := by
    rw [Finset.sum_div]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => heach i)
  have hcs := HTGeometry.norm_sum_smul_sq_le α e
  have hbnd : ‖∑ i, α i • e i‖^2/h ≤ C*N*δ := by
    calc
      _ ≤ (C*(∑ i, ‖e i‖^2))/h := div_le_div_of_nonneg_right hcs hh.le
      _ = C*((∑ i, ‖e i‖^2)/h) := by ring
      _ ≤ C*(N*δ) := mul_le_mul_of_nonneg_left hsum hC
      _ = _ := by ring
  have heq : (C*N+1)*δ = ε := by dsimp only [δ]; field_simp [hden.ne']
  exact hbnd.trans_lt (by nlinarith only [heq, hδ])

/-- The exact right slope of every finite evaluation Gram is its combined
two-endpoint trace energy. -/
theorem eventually_abs_evalGram_slope_sub_endpointEnergy_lt
    {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) (α z : ι → ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ (b : PrecontactAperture)
      (hab : a.1.1 ≤ b.1.1), b.1.1 = a.1.1+h →
      |(evalGram α z b.1.1-evalGram α z a.1.1)/h-
        evalCombinationEndpointEnergy α z a| < ε := by
  let A := ∑ i, α i*evalLeftEndpointTrace a (z i)
  let B := ∑ i, α i*evalRightEndpointTrace a (z i)
  let S := ‖A‖^2+‖B‖^2
  obtain ⟨δ, hδ, hstable⟩ := normalized_energy_stability
    (add_nonneg (sq_nonneg ‖A‖) (sq_nonneg ‖B‖)) hε
  filter_upwards [eventually_constantCollar_energy_lt (a := a) (c := c) A B hδ,
    eventually_combination_constantCollar_error_lt hac α z hδ,
    self_mem_nhdsWithin,
    (eventually_lt_nhds (sub_pos.mpr hac)).filter_mono nhdsWithin_le_nhds]
    with h henergy herror hh hhc
  change 0 < h at hh
  intro b hab hb
  have hbc : b.1.1 ≤ c.1.1 := by rw [hb]; linarith only [hhc]
  obtain ⟨l, r, hl, hr⟩ := exists_constantCollar_pair b a.1.2.le hh hb
  let u := (Real.sqrt (Real.log (1/h)) : ℂ)⁻¹ • (A • l+B • r)
  let v := combinationIncrement α z hab
  have hu : |‖u‖^2/h-S| < δ := henergy b hab hbc l r hl hr
  have he : ‖u-v‖^2/h < δ := herror b hab hb l r hl hr
  have hp : |‖v‖^2-‖u‖^2| ≤ 2*‖u‖*‖u-v‖+‖u-v‖^2 := by
    letI : InnerProductSpace ℝ (WeilHilbertBeforeContact b) := InnerProductSpace.complexToReal
    have ht := _root_.RHTower.sq_norm_perturbation u (v-u)
    have heq : u+(v-u) = v := by abel
    rw [heq, norm_sub_rev v u] at ht
    exact ht
  have hs := hstable ‖u‖ ‖v‖ ‖u-v‖ h (norm_nonneg _) (norm_nonneg _) hh hp hu he
  have hg (c : PrecontactAperture) : evalGram α z c.1.1 = ‖evalCombination α z c‖^2 := by
    rw [evalGram, dif_pos (show c.1.1 ∈ precontactSet from ⟨c.1.2, c.2⟩)]
    rfl
  rw [hg b, hg a, norm_evalCombination_sq α z (a := a) (b := b) hab, add_sub_cancel_left]
  exact hs

/-- The finite Gram trace energy in the real aperture coordinate. -/
def evalGramEndpointEnergy (α z : ι → ℂ) (a : ℝ) : ℝ :=
  open Classical in
  if h : a ∈ precontactSet then evalCombinationEndpointEnergy α z (toPrecontact h) else 0

/-- Every precontact right derivative is the quadratic form of the two
actual endpoint traces. -/
theorem hasDerivWithinAt_evalGram_right (α z : ι → ℂ) {a : ℝ}
    (ha : a ∈ precontactSet) :
    HasDerivWithinAt (evalGram α z) (evalGramEndpointEnergy α z a) (Ioi a) a := by
  let A := toPrecontact ha
  obtain ⟨c, hac, hc⟩ := EReal.exists_between_coe_real ha.2
  have hac' : a < c := EReal.coe_lt_coe_iff.mp hac
  let C : PrecontactAperture := ⟨⟨c, ha.1.trans hac'⟩, hc⟩
  have hshift : Tendsto (fun x : ℝ => x-a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun x : ℝ => x-a) (𝓝 a) (𝓝 (a-a)) := tendsto_id.sub_const a
      simpa only [sub_self] using ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x-a
      exact sub_pos.mpr (show a < x from hx)
  rw [evalGramEndpointEnergy, dif_pos ha,
    hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs := hshift.eventually
    (eventually_abs_evalGram_slope_sub_endpointEnergy_lt (a := A) (c := C) hac' α z hε)
  filter_upwards [hs, self_mem_nhdsWithin,
    (eventually_lt_nhds hac').filter_mono nhdsWithin_le_nhds] with x hs hax hxc
  have hx : x ∈ precontactSet :=
    ⟨ha.1.trans hax, (EReal.coe_lt_coe_iff.mpr hxc).trans hc⟩
  let B := toPrecontact hx
  have hb : B.1.1 = A.1.1+(x-a) := by dsimp only [A, B, toPrecontact]; ring
  rw [slope_def_field, Real.dist_eq]
  simpa only [A, B, toPrecontact] using hs B hax.le hb

/-- The ordinary Gram derivative agrees almost everywhere with its actual
endpoint trace energy on every compact precontact interval. -/
theorem evalDensity_ae_eq_endpointEnergy (α z : ι → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    evalDensity α z =ᵐ[volume.restrict (uIoc a b)] evalGramEndpointEnergy α z := by
  have hm := (monotoneOn_evalGram α z).mono hs
  change ∀ᵐ x ∂volume.restrict (uIoc a b), deriv (evalGram α z) x = evalGramEndpointEnergy α z x
  rw [uIoc_of_le hab, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hm.ae_differentiableWithinAt_of_mem, volume.ae_ne b] with x hx hxb hxI
  have hi : x ∈ Ioo a b := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
  have hf := (hx ⟨hi.1.le, hi.2.le⟩).differentiableAt (Icc_mem_nhds hi.1 hi.2)
  exact (hf.derivWithin (uniqueDiffWithinAt_Ioi x)).symm.trans
    ((hasDerivWithinAt_evalGram_right α z (hs ⟨hi.1.le, hi.2.le⟩)).derivWithin
      (uniqueDiffWithinAt_Ioi x))

/-- Every precontact finite Gram gain is exactly the integral of its two
combined endpoint trace energies. -/
theorem integral_evalGramEndpointEnergy_eq_sub (α z : ι → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable (evalGramEndpointEnergy α z) volume a b ∧
      (∫ x in a..b, evalGramEndpointEnergy α z x) = evalGram α z b-evalGram α z a := by
  have he := evalDensity_ae_eq_endpointEnergy α z hab hs
  have hi := (integral_evalDensity_mem α z hab hs).1.congr_ae he
  refine ⟨hi, ?_⟩
  have hc : ContinuousOn (evalGram α z) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (absolutelyContinuousOnInterval_evalGram α z hab hs).continuousOn
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hc
    (fun x hx => hasDerivWithinAt_evalGram_right α z (hs ⟨hx.1.le, hx.2.le⟩)) hi

#print axioms eventually_combination_constantCollar_error_lt
#print axioms eventually_abs_evalGram_slope_sub_endpointEnergy_lt
#print axioms hasDerivWithinAt_evalGram_right
#print axioms evalDensity_ae_eq_endpointEnergy
#print axioms integral_evalGramEndpointEnergy_eq_sub
end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
