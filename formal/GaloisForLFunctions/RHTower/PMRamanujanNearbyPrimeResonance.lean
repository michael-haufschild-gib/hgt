import GaloisForLFunctions.RHTower.PMPairedRamanujanGram
import GaloisForLFunctions.RHTower.StepFunctionCarrier
import GaloisForLFunctions.RHTower.SoninDilationContinuity
import GaloisForLFunctions.RHTower.STCPrimeWindowPackets

/-!
# Nearby-prime covariance of actual Ramanujan primitives

The primitive step functions realize the anchored Gram in the full-line
Hilbert space. Exact prime insertion and continuous normalized dilation
produce a continuous covariance profile and a quantitative error bound.
Distinct nearby primes give arbitrarily large Gram entries, even after
reciprocal-energy centering for a non-prime-power cofactor.

This rules out a uniform growing-cofactor covariance bound after mean
removal. It supplies no upper bound on the full signed natural-cutoff sum.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem pm_nearby_ae_ne_one : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
  rw [Filter.eventually_iff, mem_ae_iff]
  simp

/-- The actual primitive divided by the spatial coordinate, extended by zero below one. -/
def pmRamanujanStepSource (r : ℕ) : ℝ → ℂ :=
  stepFun (fun N => (pmRamanujanPrimitive r N).re)

private theorem pm_nearby_re_bound {r : ℕ} (hr : 1 < r) (N : ℕ) :
    |(pmRamanujanPrimitive r N).re| ≤ pmRamanujanPrimitiveBound r :=
  (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr N)

private theorem pm_nearby_source_zero {r : ℕ} {x : ℝ} (hx : x < 1) :
    pmRamanujanStepSource r x = 0 := by
  simp [pmRamanujanStepSource, stepFun, Nat.floor_eq_zero.mpr hx,
    pmRamanujanPrimitive]

/-- Every nontrivial primitive has finite anchored energy. -/
theorem memLp_pmRamanujanStepSource {r : ℕ} (hr : 1 < r) :
    MemLp (pmRamanujanStepSource r) 2 (volume : Measure ℝ) := by
  have h : MemLp ((Ioi (1 : ℝ)).indicator
      (stepFun (fun N => (pmRamanujanPrimitive r N).re))) 2 volume :=
    (memLp_indicator_iff_restrict (μ := (volume : Measure ℝ))
    (p := (2 : ENNReal)) (s := Ioi (1 : ℝ)) measurableSet_Ioi).mpr
      (memLp_stepFun (pm_nearby_re_bound hr))
  refine MemLp.ae_eq ?_ h
  filter_upwards [pm_nearby_ae_ne_one] with x hx
  by_cases h1 : 1 < x
  · simp [h1, pmRamanujanStepSource]
  · have hx1 : x < 1 := lt_of_le_of_ne (le_of_not_gt h1) hx
    simp [h1, pmRamanujanStepSource, stepFun, Nat.floor_eq_zero.mpr hx1,
      pmRamanujanPrimitive]

/-- The actual primitive step function as a full-line Hilbert vector. -/
def pmRamanujanStepVector (r : ℕ) (hr : 1 < r) : SoninL2 :=
  (memLp_pmRamanujanStepSource hr).toLp (pmRamanujanStepSource r)

/-- The Hilbert inner product is exactly the anchored reciprocal-weight Gram. -/
theorem inner_pmRamanujanStepVector {r s : ℕ} (hr : 1 < r) (hs : 1 < s) :
    inner ℂ (pmRamanujanStepVector r hr) (pmRamanujanStepVector s hs) =
      (pmRamanujanPrimitiveGram r s : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hi : (fun x : ℝ => inner ℂ
      ((pmRamanujanStepVector r hr : ℝ → ℂ) x)
      ((pmRamanujanStepVector s hs : ℝ → ℂ) x)) =ᵐ[volume]
      (Ioi (1 : ℝ)).indicator (fun x =>
        (((pmRamanujanPrimitive r ⌊x⌋₊).re *
          (pmRamanujanPrimitive s ⌊x⌋₊).re * (x⁻¹)^2 : ℝ) : ℂ)) := by
    filter_upwards [(memLp_pmRamanujanStepSource hr).coeFn_toLp,
      (memLp_pmRamanujanStepSource hs).coeFn_toLp, pm_nearby_ae_ne_one]
      with x hx hy hne
    change (pmRamanujanStepVector r hr : ℝ → ℂ) x = _ at hx
    change (pmRamanujanStepVector s hs : ℝ → ℂ) x = _ at hy
    rw [hx, hy]
    by_cases h1 : 1 < x
    · rw [indicator_of_mem (show x ∈ Ioi (1 : ℝ) from h1)]
      simp only [pmRamanujanStepSource, stepFun, RCLike.inner_apply,
        map_mul, map_inv₀, Complex.conj_ofReal]
      push_cast
      ring
    · have hx1 : x < 1 := lt_of_le_of_ne (le_of_not_gt h1) hne
      rw [pm_nearby_source_zero hx1, inner_zero_left,
        indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from h1)]
  rw [integral_congr_ae hi, integral_indicator measurableSet_Ioi,
    integral_complex_ofReal]
  congr 1
  change stepGram (fun N => (pmRamanujanPrimitive r N).re)
    (fun N => (pmRamanujanPrimitive s N).re) = pmRamanujanPrimitiveGram r s
  rw [← (hasSum_stepGram (pm_nearby_re_bound hr) (pm_nearby_re_bound hs)).tsum_eq]
  have h := (summable_pmRamanujanPrimitiveGramTerm hr hs).sum_add_tsum_nat_add 1
  have hz : pmRamanujanPrimitiveGramTerm r s 0 = 0 := by
    simp [pmRamanujanPrimitiveGramTerm]
  simp only [Finset.sum_range_one, hz, zero_add] at h
  rw [pmRamanujanPrimitiveGram, ← h]
  apply tsum_congr
  intro N
  simp only [pmRamanujanPrimitiveGramTerm, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

/-- The actual diagonal Gram is the squared Hilbert norm. -/
theorem norm_sq_pmRamanujanStepVector {r : ℕ} (hr : 1 < r) :
    ‖pmRamanujanStepVector r hr‖^2 = pmRamanujanPrimitiveGram r r := by
  have h := congrArg Complex.re (inner_pmRamanujanStepVector hr hr)
  rw [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h

/-- Prime insertion acts by an exact difference of spatial dilations. -/
theorem pmRamanujanStepSource_prime_mul {p r : ℕ} (hp : p.Prime)
    (hpr : ¬ p ∣ r) (x : ℝ) :
    pmRamanujanStepSource (p*r) x =
      pmRamanujanStepSource r (x/p) - pmRamanujanStepSource r x := by
  simp only [pmRamanujanStepSource, stepFun, pmRamanujanPrimitive_prime_mul hp hpr,
    Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Nat.floor_div_natCast]
  push_cast
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [inv_div]
  ring

/-- Prime insertion in the normalized dilation representation. -/
theorem pmRamanujanStepVector_prime_mul {p r : ℕ} (hp : p.Prime)
    (hr : 1 < r) (hpr : ¬ p ∣ r) :
    pmRamanujanStepVector (p*r) (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)) =
      (Real.sqrt (p : ℝ) : ℂ) •
        dilation (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp.pos)) (pmRamanujanStepVector r hr) -
          pmRamanujanStepVector r hr := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcomp := (memLp_pmRamanujanStepSource hr).coeFn_toLp.comp_tendsto
    (realMul_quasiMeasurePreserving (p : ℝ)⁻¹ (inv_ne_zero hpR.ne')).tendsto_ae
  apply Lp.ext
  filter_upwards [(memLp_pmRamanujanStepSource
      (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos))).coeFn_toLp,
    (memLp_pmRamanujanStepSource hr).coeFn_toLp,
    Lp.coeFn_sub ((Real.sqrt (p : ℝ) : ℂ) •
      dilation (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp.pos)) (pmRamanujanStepVector r hr))
        (pmRamanujanStepVector r hr),
    Lp.coeFn_smul (Real.sqrt (p : ℝ) : ℂ)
      (dilation (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp.pos)) (pmRamanujanStepVector r hr)),
    dilation_ae (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp.pos)) (pmRamanujanStepVector r hr), hcomp]
    with x hx hy hsub hsmul hdil hc
  change (pmRamanujanStepVector (p*r)
    (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)) : ℝ → ℂ) x = _ at hx
  change (pmRamanujanStepVector r hr : ℝ → ℂ) x = _ at hy
  change (pmRamanujanStepVector r hr : ℝ → ℂ) ((p : ℝ)⁻¹*x) =
    pmRamanujanStepSource r ((p : ℝ)⁻¹*x) at hc
  rw [hx, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hdil, hc, hy,
    ← mul_assoc]
  have hs : (Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (p : ℝ)⁻¹ : ℂ) = 1 := by
    exact_mod_cast sqrt_mul_sqrt_inv (p : ℝ) hpR
  rw [hs, one_mul, pmRamanujanStepSource_prime_mul hp hpr]
  congr 2
  ring

private theorem pm_nearby_dilation_one (f : SoninL2) :
    dilation 1 (by norm_num) f = f := by
  apply Lp.ext
  filter_upwards [dilation_ae 1 (by norm_num) f] with x hx
  simpa using hx

/-- The retained covariance profile of one actual primitive. -/
def pmRamanujanDilationProfile (r : ℕ) (hr : 1 < r) (c : ℝ) : ℝ :=
  (inner ℂ (pmRamanujanStepVector r hr)
    (rayDilate c (pmRamanujanStepVector r hr))).re

/-- Strong continuity of dilation gives continuity of the actual profile. -/
theorem continuousOn_pmRamanujanDilationProfile {r : ℕ} (hr : 1 < r) :
    ContinuousOn (pmRamanujanDilationProfile r hr) (Ioi 0) := by
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_const.inner (continuousOn_rayDilate _))

/-- The profile at matching scales is the strictly positive diagonal Gram. -/
theorem pmRamanujanDilationProfile_one {r : ℕ} (hr : 1 < r) :
    pmRamanujanDilationProfile r hr 1 = pmRamanujanPrimitiveGram r r := by
  rw [pmRamanujanDilationProfile, rayDilate_of_pos (by norm_num),
    pm_nearby_dilation_one, inner_pmRamanujanStepVector, Complex.ofReal_re]

/-- The entire profile is bounded by its value at matching scales. -/
theorem abs_pmRamanujanDilationProfile_le {r : ℕ} (hr : 1 < r)
    {c : ℝ} (hc : 0 < c) :
    |pmRamanujanDilationProfile r hr c| ≤ pmRamanujanPrimitiveGram r r := by
  exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans_eq
    (by rw [norm_rayDilate hc, ← sq, norm_sq_pmRamanujanStepVector hr]))

private theorem pm_nearby_inner_dilations (f : SoninL2) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    inner ℂ (dilation a⁻¹ (inv_pos.mpr ha) f) (dilation b⁻¹ (inv_pos.mpr hb) f) =
      inner ℂ f (rayDilate (a/b) f) := by
  have h := (dilation a ha).inner_map_map
    (dilation a⁻¹ (inv_pos.mpr ha) f) (dilation b⁻¹ (inv_pos.mpr hb) f)
  rw [dilation_dilation_inv, dilation_dilation] at h
  rw [rayDilate_of_pos (div_pos ha hb)]
  simpa only [div_eq_mul_inv] using h.symm

/-- Finite quantitative covariance law for two prime multiples of one cofactor. -/
theorem pmRamanujanPrimitiveGram_nearby_error {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : 1 < r)
    (hpr : ¬ p ∣ r) (hqr : ¬ q ∣ r) :
    |pmRamanujanPrimitiveGram (p*r) (q*r) -
        Real.sqrt (p : ℝ)*Real.sqrt (q : ℝ)*
          pmRamanujanDilationProfile r hr ((p : ℝ)/q)| ≤
      (Real.sqrt (p : ℝ)+Real.sqrt (q : ℝ)+1)*pmRamanujanPrimitiveGram r r := by
  let f := pmRamanujanStepVector r hr
  let u := dilation (p : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hp.pos)) f
  let v := dilation (q : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hq.pos)) f
  let E := pmRamanujanPrimitiveGram r r
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hu : ‖u‖ = ‖f‖ := (dilation _ _).norm_map f
  have hv : ‖v‖ = ‖f‖ := (dilation _ _).norm_map f
  have hE : ‖f‖^2 = E := norm_sq_pmRamanujanStepVector hr
  have hx : |(inner ℂ u f).re| ≤ E :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans_eq
      (by rw [hu, ← sq, hE]))
  have hy : |(inner ℂ f v).re| ≤ E :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans_eq
      (by rw [hv, ← sq, hE]))
  have huv : (inner ℂ u v).re = pmRamanujanDilationProfile r hr ((p : ℝ)/q) := by
    exact congrArg Complex.re (pm_nearby_inner_dilations f hpR hqR)
  have he := inner_pmRamanujanStepVector
    (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos))
    (lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hq.pos))
  rw [pmRamanujanStepVector_prime_mul hp hr hpr,
    pmRamanujanStepVector_prime_mul hq hr hqr] at he
  change inner ℂ ((Real.sqrt (p : ℝ) : ℂ) • u-f)
    ((Real.sqrt (q : ℝ) : ℂ) • v-f) = _ at he
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal] at he
  have heR := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at heR
  have hff : (inner ℂ f f).re = E := by
    exact congrArg Complex.re (inner_pmRamanujanStepVector hr hr)
  rw [huv, hff] at heR
  have hdiff : pmRamanujanPrimitiveGram (p*r) (q*r) -
      Real.sqrt (p : ℝ)*Real.sqrt (q : ℝ)*
        pmRamanujanDilationProfile r hr ((p : ℝ)/q) =
      -Real.sqrt (p : ℝ)*(inner ℂ u f).re -
        Real.sqrt (q : ℝ)*(inner ℂ f v).re + E := by
    linear_combination -heR
  rw [hdiff]
  rcases abs_le.mp hx with ⟨hxl,hxu⟩
  rcases abs_le.mp hy with ⟨hyl,hyu⟩
  have hE0 : 0 ≤ E := (pmRamanujanPrimitiveGram_pos hr).le
  have hp0 := Real.sqrt_nonneg (p : ℝ)
  have hq0 := Real.sqrt_nonneg (q : ℝ)
  apply abs_le.mpr
  constructor <;> dsimp only [E] at * <;> nlinarith

/-- Distinct prime multiples in one multiplicative band have unbounded covariance. -/
theorem exists_pmRamanujanPrimitiveGram_nearby_gt {r : ℕ} (hr : 1 < r) (B : ℝ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ r < p ∧ p < q ∧ q < 2*p ∧
      B < pmRamanujanPrimitiveGram (p*r) (q*r) := by
  let E := pmRamanujanPrimitiveGram r r
  have hE : 0 < E := pmRamanujanPrimitiveGram_pos hr
  have hc : ContinuousAt (pmRamanujanDilationProfile r hr) 1 :=
    (continuousOn_pmRamanujanDilationProfile hr).continuousAt (Ioi_mem_nhds (by norm_num))
  have ht : Tendsto (pmRamanujanDilationProfile r hr) (𝓝 1) (𝓝 E) := by
    simpa only [pmRamanujanDilationProfile_one] using hc.tendsto
  have hev : ∀ᶠ c in 𝓝 (1 : ℝ), 3*E/4 < pmRamanujanDilationProfile r hr c :=
    ht.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ,hδ,hclose⟩ := Metric.eventually_nhds_iff.mp hev
  let η := min δ 1
  have hη : 0 < η := lt_min hδ (by norm_num)
  let T := max (r : ℝ) (max 256 (4*(|B|+1)/E))
  obtain ⟨p,q,hp,hq,hTp,hpq,hqp⟩ := exists_prime_pair_ratio_lt hη T
  have hprR : (r : ℝ) < p := (le_max_left _ _).trans_lt hTp
  have hpr : r < p := by exact_mod_cast hprR
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hp256 : (256 : ℝ) < p :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hTp
  have hbud : 4*(|B|+1)/E < (p : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hTp
  have hp16 : (16 : ℝ) < Real.sqrt (p : ℝ) := by
    nlinarith [Real.sq_sqrt hpR.le, Real.sqrt_nonneg (p : ℝ)]
  have hq16 : (16 : ℝ) < Real.sqrt (q : ℝ) :=
    hp16.trans_le (Real.sqrt_le_sqrt hpqR.le)
  have hratio : (p : ℝ)/q < 1 := (div_lt_one hqR).mpr hpqR
  have hratioLower : 1-η < (p : ℝ)/q := by
    apply (lt_div_iff₀ hqR).mpr
    nlinarith
  have hdist : dist ((p : ℝ)/q) 1 < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hratio.le)]
    have hηδ : η ≤ δ := min_le_left _ _
    linarith
  have hK := hclose hdist
  have hndp : ¬ p ∣ r := Nat.not_dvd_of_pos_of_lt (by omega) hpr
  have hndq : ¬ q ∣ r := Nat.not_dvd_of_pos_of_lt (by omega) (hpr.trans hpq)
  have hlow := (abs_le.mp (pmRamanujanPrimitiveGram_nearby_error hp hq hr hndp hndq)).1
  have hsmall : Real.sqrt (p : ℝ)+Real.sqrt (q : ℝ)+1 <
      Real.sqrt (p : ℝ)*Real.sqrt (q : ℝ)/4 := by
    nlinarith [mul_pos (sub_pos.mpr hp16) (sub_pos.mpr hq16)]
  have hprod : 0 < Real.sqrt (p : ℝ)*Real.sqrt (q : ℝ) := by positivity
  have hKmul := mul_lt_mul_of_pos_left hK hprod
  have hsmallE := mul_lt_mul_of_pos_right hsmall hE
  have hhalf : E/2*(Real.sqrt (p : ℝ)*Real.sqrt (q : ℝ)) <
      pmRamanujanPrimitiveGram (p*r) (q*r) := by
    dsimp only [E] at *
    nlinarith
  have hprodGe : (p : ℝ) ≤ Real.sqrt (p : ℝ)*Real.sqrt (q : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpqR.le)
      (Real.sqrt_nonneg (p : ℝ))
    nlinarith [Real.sq_sqrt hpR.le]
  have hBlt : B < E/2*(Real.sqrt (p : ℝ)*Real.sqrt (q : ℝ)) := by
    have hb := (div_lt_iff₀ hE).mp hbud
    have hm := mul_le_mul_of_nonneg_left hprodGe hE.le
    nlinarith [le_abs_self B]
  have hq2 : q < 2*p := by
    have hη1 : η ≤ 1 := min_le_right _ _
    have : (q : ℝ) < 2*(p : ℝ) := by nlinarith
    exact_mod_cast this
  exact ⟨p,q,hp,hq,hpr,hpq,hq2,hBlt.trans hhalf⟩

/-- Reciprocal-mean removal leaves unbounded nearby-prime covariance. -/
theorem exists_pmRamanujanCenteredGram_nearby_gt {r : ℕ}
    (hr : 1 < r) (hrp : ¬ IsPrimePow r) (B : ℝ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ r < p ∧ p < q ∧ q < 2*p ∧
      ArithmeticFunction.vonMangoldt (p*r) = 0 ∧
      ArithmeticFunction.vonMangoldt (q*r) = 0 ∧
      B < pmRamanujanEnergyCenteredGram (p*r) (q*r) := by
  obtain ⟨p,q,hp,hq,hrp',hpq,hq2,hG⟩ := exists_pmRamanujanPrimitiveGram_nearby_gt hr B
  have hz (n : ℕ) : ArithmeticFunction.vonMangoldt (n*r) = 0 := by
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro h
    exact hrp (h.dvd (dvd_mul_left r n) (by omega))
  refine ⟨p,q,hp,hq,hrp',hpq,hq2,hz p,hz q,?_⟩
  simpa only [pmRamanujanEnergyCenteredGram, pmRamanujanEnergyCenteredPrimitive,
    pmRamanujanPrimitiveGram, pmRamanujanPrimitiveGramTerm, hz p, hz q, add_zero] using hG

end RHTower
