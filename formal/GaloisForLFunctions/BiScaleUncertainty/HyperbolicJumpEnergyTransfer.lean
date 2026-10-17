import GaloisForLFunctions.BiScaleUncertainty.HyperbolicMultiplierGramTransfer
import GaloisForLFunctions.BiScaleUncertainty.DisjointCollarCliqueDivergenceAndTuransProblem

/-!
# Hyperbolic squared-jump transfer

The discrete eigenfunction equation for the hyperbolic sine gives an exact signed
weighted-jump identity. Bounding its weight on the actual compact source support
transfers sine-multiplier Gram lower bounds to the original secant increment,
without a cosine-multiplier companion or an additive commutator error.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
variable {ι : Type*}

/-- Exact hyperbolic weighted-jump identity, valid across the nodal sign change. -/
theorem sinh_weighted_jump_identity (f : C_c(ℝ, ℝ)) (α x : ℝ) :
    (∫ u, Real.sinh (α * u) * Real.sinh (α * (u + x)) *
      (f u - f (u + x)) ^ 2) =
      2 * (Real.cosh (α * x) * autocorr (sinhCompact α f) 0 -
        autocorr (sinhCompact α f) x) := by
  let m : ℝ → ℝ := fun u => Real.sinh (α * u)
  have hm : Continuous m := Real.continuous_sinh.comp (continuous_const.mul continuous_id)
  have hfsq : HasCompactSupport (fun u : ℝ => f u ^ 2) := by
    have h : HasCompactSupport (fun u : ℝ => f u * f u) := f.hasCompactSupport.mul_left
    simpa only [sq] using h
  have hgsq : HasCompactSupport (fun u : ℝ => f (u + x) ^ 2) :=
    hasCompactSupport_comp_add hfsq x
  have hA : Integrable (fun u => m u * m (u + x) * f u ^ 2) :=
    ((hm.mul (hm.comp (continuous_add_const x))).mul (f.continuous.pow 2)).integrable_of_hasCompactSupport
      hfsq.mul_left
  have hB : Integrable (fun u => m u * m (u + x) * f (u + x) ^ 2) :=
    ((hm.mul (hm.comp (continuous_add_const x))).mul
      ((f.continuous.comp (continuous_add_const x)).pow 2)).integrable_of_hasCompactSupport
      hgsq.mul_left
  have hD : Integrable (fun u => m (u - x) * m u * f u ^ 2) :=
    (((hm.comp (continuous_id.sub continuous_const)).mul hm).mul
      (f.continuous.pow 2)).integrable_of_hasCompactSupport hfsq.mul_left
  have hcross : Integrable (fun u => (m u * f u) * (m (u + x) * f (u + x))) :=
    integrable_mul_shift (hm.mul f.continuous) f.hasCompactSupport.mul_left x
  have hshift : (∫ u, m u * m (u + x) * f (u + x) ^ 2) =
      ∫ u, m (u - x) * m u * f u ^ 2 := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun u => m (u - x) * m u * f u ^ 2) x
    simpa only [add_sub_cancel_right] using h
  have hdiag : (∫ u, m u * m (u + x) * f u ^ 2) +
      (∫ u, m (u - x) * m u * f u ^ 2) =
        2 * Real.cosh (α * x) * autocorr (sinhCompact α f) 0 := by
    rw [← integral_add hA hD, ← integral_sq_eq_autocorr_zero, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    have hs : m (u + x) + m (u - x) = 2 * Real.cosh (α * x) * m u := by
      dsimp [m]
      rw [mul_add, mul_sub, Real.sinh_add, Real.sinh_sub]
      ring
    change m u * m (u + x) * f u ^ 2 + m (u - x) * m u * f u ^ 2 =
      2 * Real.cosh (α * x) * (m u * f u) ^ 2
    linear_combination m u * f u ^ 2 * hs
  have hexpand : (fun u => m u * m (u + x) * (f u - f (u + x)) ^ 2) =
      fun u => (m u * m (u + x) * f u ^ 2 + m u * m (u + x) * f (u + x) ^ 2) -
        2 * ((m u * f u) * (m (u + x) * f (u + x))) := by
    funext u
    ring
  change (∫ u, m u * m (u + x) * (f u - f (u + x)) ^ 2) = _
  have hAB : Integrable (fun u => m u * m (u + x) * f u ^ 2 +
      m u * m (u + x) * f (u + x) ^ 2) := hA.add hB
  have hcross2 : Integrable (fun u => 2 * ((m u * f u) * (m (u + x) * f (u + x)))) :=
    hcross.const_mul 2
  rw [hexpand, integral_sub hAB hcross2,
    integral_add hA hB, integral_const_mul, hshift, hdiag]
  change 2 * Real.cosh (α * x) * autocorr (sinhCompact α f) 0 -
    2 * autocorr (sinhCompact α f) x = _
  ring

private theorem exists_multiplierSourceRadius (f : C_c(ℝ, ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ u ∈ tsupport (f : ℝ → ℝ), |u| ≤ B := by
  simpa only [Real.norm_eq_abs] using
    f.hasCompactSupport.isCompact.isBounded.exists_pos_norm_le

/-- A positive radius obtained from the actual compact source support. -/
def multiplierSourceRadius (f : C_c(ℝ, ℝ)) : ℝ :=
  Classical.choose (exists_multiplierSourceRadius f)

theorem multiplierSourceRadius_pos (f : C_c(ℝ, ℝ)) : 0 < multiplierSourceRadius f :=
  (Classical.choose_spec (exists_multiplierSourceRadius f)).1

/-- Every nonzero source value lies within the source-derived radius. -/
theorem abs_le_multiplierSourceRadius (f : C_c(ℝ, ℝ)) (u : ℝ) :
    f u ≠ 0 → |u| ≤ multiplierSourceRadius f := by
  intro hu
  exact (Classical.choose_spec (exists_multiplierSourceRadius f)).2 u
    (subset_closure (Function.mem_support.mpr hu))

/-- The endpoint-product envelope for a half-scale sine multiplier. -/
def sinhJumpEnvelope (f : C_c(ℝ, ℝ)) (x : ℝ) : ℝ :=
  Real.sinh (multiplierSourceRadius f / 2) *
    Real.sinh ((multiplierSourceRadius f + |x|) / 2)

theorem sinhJumpEnvelope_pos (f : C_c(ℝ, ℝ)) (x : ℝ) : 0 < sinhJumpEnvelope f x := by
  have hB := multiplierSourceRadius_pos f
  unfold sinhJumpEnvelope
  exact mul_pos (Real.sinh_pos_iff.mpr (by positivity))
    (Real.sinh_pos_iff.mpr (by linarith [multiplierSourceRadius_pos f, abs_nonneg x]))

theorem continuous_sinhJumpEnvelope (f : C_c(ℝ, ℝ)) : Continuous (sinhJumpEnvelope f) := by
  unfold sinhJumpEnvelope
  fun_prop

/-- Pointwise domination uses only endpoints on which the source jump is nonzero.
The sine product itself is allowed to be negative. -/
theorem sinh_weighted_jump_le_envelope (f : C_c(ℝ, ℝ)) (x u : ℝ) :
    Real.sinh (u / 2) * Real.sinh ((u + x) / 2) * (f u - f (u + x)) ^ 2 ≤
      sinhJumpEnvelope f x * (f u - f (u + x)) ^ 2 := by
  have hB := multiplierSourceRadius_pos f
  have hs (v D : ℝ) (hv : |v| ≤ D) : |Real.sinh (v / 2)| ≤ Real.sinh (D / 2) := by
    rw [Real.abs_sinh, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    exact Real.sinh_le_sinh.mpr (by linarith)
  by_cases hu : f u = 0
  · by_cases hv : f (u + x) = 0
    · simp [hu, hv]
    · have hux := abs_le_multiplierSourceRadius f (u + x) hv
      have hu' : |u| ≤ multiplierSourceRadius f + |x| := by
        have hh := abs_add_le (u + x) (-x)
        rw [show u + x + -x = u by ring, abs_neg] at hh
        linarith
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        _ ≤ |Real.sinh (u / 2)| * |Real.sinh ((u + x) / 2)| := by
          simpa only [abs_mul] using le_abs_self (Real.sinh (u / 2) * Real.sinh ((u + x) / 2))
        _ ≤ Real.sinh ((multiplierSourceRadius f + |x|) / 2) *
            Real.sinh (multiplierSourceRadius f / 2) :=
          mul_le_mul (hs u _ hu') (hs (u + x) _ hux) (abs_nonneg _)
            (Real.sinh_nonneg_iff.mpr (by positivity))
        _ = sinhJumpEnvelope f x := by unfold sinhJumpEnvelope; ring
  · have hu' := abs_le_multiplierSourceRadius f u hu
    have hux : |u + x| ≤ multiplierSourceRadius f + |x| := by
      linarith [abs_add_le u x]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      _ ≤ |Real.sinh (u / 2)| * |Real.sinh ((u + x) / 2)| := by
        simpa only [abs_mul] using le_abs_self (Real.sinh (u / 2) * Real.sinh ((u + x) / 2))
      _ ≤ sinhJumpEnvelope f x :=
        mul_le_mul (hs u _ hu') (hs (u + x) _ hux) (abs_nonneg _)
          (Real.sinh_nonneg_iff.mpr (by positivity))

/-- Uncompensated transfer: the true source increment controls the hyperbolically
strengthened sine-multiplier increment with a source-derived support factor. -/
theorem sinh_increment_le_source_increment (f : C_c(ℝ, ℝ)) (x : ℝ) :
    Real.cosh (x / 2) * autocorr (sinhCompact (1 / 2) f) 0 -
        autocorr (sinhCompact (1 / 2) f) x ≤
      sinhJumpEnvelope f x * (autocorr f 0 - autocorr f x) := by
  have hc : Continuous (fun u => (f u - f (u + x)) ^ 2) :=
    (f.continuous.sub (f.continuous.comp (continuous_add_const x))).pow 2
  have hs : HasCompactSupport (fun u => (f u - f (u + x)) ^ 2) := by
    have h : HasCompactSupport (fun u : ℝ => f u - f (u + x)) :=
      f.hasCompactSupport.sub (hasCompactSupport_comp_add f.hasCompactSupport x)
    have hsq : HasCompactSupport (fun u : ℝ => (f u - f (u + x)) * (f u - f (u + x))) :=
      h.mul_left
    simpa only [sq] using hsq
  have hi : Integrable (fun u => Real.sinh (u / 2) * Real.sinh ((u + x) / 2) *
      (f u - f (u + x)) ^ 2) :=
    ((by fun_prop : Continuous fun u : ℝ => Real.sinh (u / 2) *
      Real.sinh ((u + x) / 2)).mul hc).integrable_of_hasCompactSupport hs.mul_left
  have hj : Integrable (fun u => sinhJumpEnvelope f x * (f u - f (u + x)) ^ 2) :=
    (hc.integrable_of_hasCompactSupport hs).const_mul _
  have hle := integral_mono hi hj (sinh_weighted_jump_le_envelope f x)
  have heq := sinh_weighted_jump_identity f (1 / 2) x
  simp only [show ∀ v : ℝ, (1 / 2 : ℝ) * v = v / 2 by intro v; ring] at heq
  rw [heq, integral_const_mul,
    integral_sub_shift_sq (f := (f : ℝ → ℝ)) f.hasCompactSupport f.continuous x] at hle
  linarith

/-- Actual secant weights, rescaled by the source-support envelope. Squared
amplitudes make the transfer unconditional in the supplied real coefficients. -/
def sinhJumpTransferWeights (f : C_c(ℝ, ℝ)) (b t : ι → ℝ) (y : ℝ) (i : ι) : ℝ :=
  b i ^ 2 * archSechHalfWeight (t i - y) / sinhJumpEnvelope f (t i - y)

/-- The original, uncompensated secant increment sampled on a finite collar. -/
def secantJumpCollar (f : C_c(ℝ, ℝ)) (s : Finset ι) (b t : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, b i ^ 2 * ((autocorr f 0 - autocorr f (t i - y)) *
    archSechHalfWeight (t i - y))

/-- A full-Gram lower bound depending only on the sine-multiplied source and the
actual source support radius. -/
def sinhJumpGramBound (f : C_c(ℝ, ℝ)) (s : Finset ι) (b t : ι → ℝ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 *
      (∑ i ∈ s, sinhJumpTransferWeights f b t y i * Real.cosh ((t i - y) / 2)) -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
      translationGramEnergy (sinhCompact (1 / 2) f) s (sinhJumpTransferWeights f b t y) t)

theorem sinhJumpTransferWeights_nonneg (f : C_c(ℝ, ℝ)) (b t : ι → ℝ) (y : ℝ) (i : ι) :
    0 ≤ sinhJumpTransferWeights f b t y i :=
  div_nonneg (mul_nonneg (sq_nonneg _) (archSechHalfWeight_pos _).le)
    (sinhJumpEnvelope_pos _ _).le

/-- Scalar transfer in exactly the secant weight of the original functional. -/
theorem secant_jump_ge_sinh_jump (f : C_c(ℝ, ℝ)) (b x : ℝ) :
    (b ^ 2 * archSechHalfWeight x / sinhJumpEnvelope f x) *
        (Real.cosh (x / 2) * autocorr (sinhCompact (1 / 2) f) 0 -
          autocorr (sinhCompact (1 / 2) f) x) ≤
      b ^ 2 * ((autocorr f 0 - autocorr f x) * archSechHalfWeight x) := by
  have hK := sinhJumpEnvelope_pos f x
  have h := mul_le_mul_of_nonneg_left (sinh_increment_le_source_increment f x)
    (div_nonneg (mul_nonneg (sq_nonneg b) (archSechHalfWeight_pos x).le) hK.le)
  have heq : (b ^ 2 * archSechHalfWeight x / sinhJumpEnvelope f x) *
      (sinhJumpEnvelope f x * (autocorr f 0 - autocorr f x)) =
        b ^ 2 * ((autocorr f 0 - autocorr f x) * archSechHalfWeight x) := by
    field_simp [hK.ne']
  rwa [heq] at h

/-- Uncompensated multi-node transfer. No parity, zero-grid, or multiplier-clique
hypothesis is required: all actual off-diagonal correlations remain in the Gram. -/
theorem secantJumpCollar_ge_gram (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    sinhJumpGramBound f s b t y ≤ secantJumpCollar f s b t y := by
  have hpair := translationPacket_correlation_le (sinhCompact (1 / 2) f) s
    (sinhJumpTransferWeights f b t y) t y
  unfold sinhJumpGramBound secantJumpCollar
  calc
    _ ≤ autocorr (sinhCompact (1 / 2) f) 0 *
        (∑ i ∈ s, sinhJumpTransferWeights f b t y i * Real.cosh ((t i - y) / 2)) -
      ∑ i ∈ s, sinhJumpTransferWeights f b t y i *
        autocorr (sinhCompact (1 / 2) f) (t i - y) := sub_le_sub_left hpair _
    _ = ∑ i ∈ s, sinhJumpTransferWeights f b t y i *
        (Real.cosh ((t i - y) / 2) * autocorr (sinhCompact (1 / 2) f) 0 -
          autocorr (sinhCompact (1 / 2) f) (t i - y)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => secant_jump_ge_sinh_jump f (b i) (t i - y)

/-- Clique lower bound with the positive part of the measured multiplier Gram
defect as an explicit penalty. This does not infer multiplier zeros from source zeros. -/
theorem secantJumpCollar_ge_clique_penalty (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    autocorr (sinhCompact (1 / 2) f) 0 *
        ((∑ i ∈ s, sinhJumpTransferWeights f b t y i * Real.cosh ((t i - y) / 2)) -
          Real.sqrt (∑ i ∈ s, sinhJumpTransferWeights f b t y i ^ 2)) -
      Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
        max (sinhCliqueGramDefect f (1 / 2) s (sinhJumpTransferWeights f b t y) t) 0) ≤
      secantJumpCollar f s b t y := by
  let R := autocorr (sinhCompact (1 / 2) f) 0
  let A := ∑ i ∈ s, sinhJumpTransferWeights f b t y i ^ 2
  let D := sinhCliqueGramDefect f (1 / 2) s (sinhJumpTransferWeights f b t y) t
  have hR : 0 ≤ R := autocorr_zero_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ R * max D 0 := mul_nonneg hR (le_max_right _ _)
  have hsq : (R * Real.sqrt A) ^ 2 = R * (R * A) := by
    rw [mul_pow, Real.sq_sqrt hA]
    ring
  have hroot : Real.sqrt (R * (R * A + D)) ≤
      R * Real.sqrt A + Real.sqrt (R * max D 0) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hcost : R * D ≤ R * max D 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hR
    have hcross : 0 ≤ (R * Real.sqrt A) * Real.sqrt (R * max D 0) := by positivity
    nlinarith [Real.sq_sqrt hB]
  have h := secantJumpCollar_ge_gram f s b t y
  unfold sinhJumpGramBound at h
  rw [sinhGram_eq_diagonal_add_defect] at h
  change R * (∑ i ∈ s, sinhJumpTransferWeights f b t y i * Real.cosh ((t i - y) / 2)) -
    Real.sqrt (R * (R * A + D)) ≤ _ at h
  change R * ((∑ i ∈ s, sinhJumpTransferWeights f b t y i * Real.cosh ((t i - y) / 2)) -
    Real.sqrt A) - Real.sqrt (R * max D 0) ≤ _
  linarith

theorem continuous_sinhJumpTransferWeights (f : C_c(ℝ, ℝ)) (b t : ι → ℝ) (i : ι) :
    Continuous (fun y => sinhJumpTransferWeights f b t y i) := by
  unfold sinhJumpTransferWeights archSechHalfWeight
  apply Continuous.div
  · apply continuous_const.mul
    exact continuous_const.div (by fun_prop) fun y => (Real.cosh_pos _).ne'
  · exact (continuous_sinhJumpEnvelope f).comp (continuous_const.sub continuous_id)
  · intro y
    exact (sinhJumpEnvelope_pos f _).ne'

theorem continuous_secantJumpIntegrand (f : C_c(ℝ, ℝ)) :
    Continuous (fun x => (autocorr f 0 - autocorr f x) * archSechHalfWeight x) := by
  apply (continuous_const.sub (continuous_autocorr_compact f)).mul
  unfold archSechHalfWeight
  exact continuous_const.div (by fun_prop) fun x => (Real.cosh_pos _).ne'

theorem continuous_secantJumpCollar (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) : Continuous (secantJumpCollar f s b t) := by
  unfold secantJumpCollar
  exact continuous_finsetSum s fun i _ => continuous_const.mul
    ((continuous_secantJumpIntegrand f).comp (continuous_const.sub continuous_id))

theorem continuous_sinhJumpGramBound (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) : Continuous (sinhJumpGramBound f s b t) := by
  have hv := continuous_sinhJumpTransferWeights f b t
  have hg : Continuous (fun y => translationGramEnergy (sinhCompact (1 / 2) f) s
      (sinhJumpTransferWeights f b t y) t) := by
    unfold translationGramEnergy
    exact continuous_finsetSum s fun i _ => continuous_finsetSum s fun j _ =>
      ((hv i).mul (hv j)).mul continuous_const
  unfold sinhJumpGramBound
  exact (continuous_const.mul (continuous_finsetSum s fun i _ =>
    (hv i).mul (by fun_prop))).sub
    (Real.continuous_sqrt.comp (continuous_const.mul hg))

/-- Integration over any compact collar preserves the uncompensated transfer. -/
theorem integral_secantJumpCollar_ge_gram (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (a z : ℝ) :
    (∫ y in min a z..max a z, sinhJumpGramBound f s b t y) ≤
      ∫ y in min a z..max a z, secantJumpCollar f s b t y :=
  intervalIntegral.integral_mono_on (min_le_max : min a z ≤ max a z)
    ((continuous_sinhJumpGramBound f s b t).intervalIntegrable _ _)
    ((continuous_secantJumpCollar f s b t).intervalIntegrable _ _)
    (fun y _ => secantJumpCollar_ge_gram f s b t y)

/-- Exponential domination of the smooth secant kernel. -/
theorem archSechHalfWeight_le_exp (x : ℝ) :
    archSechHalfWeight x ≤ 2 * Real.exp (-x / 2) := by
  unfold archSechHalfWeight
  rw [div_le_iff₀ (Real.cosh_pos _), Real.cosh_eq]
  have he : Real.exp (-x / 2) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add, show -x / 2 + x / 2 = 0 by ring, Real.exp_zero]
  rw [show -(x / 2) = -x / 2 by ring]
  nlinarith [sq_nonneg (Real.exp (-x / 2))]

/-- Secant energy needs only continuity and compact support, since its kernel is
bounded at the origin and decays exponentially at infinity. -/
theorem integrableOn_secantJumpIntegrand_compact (f : C_c(ℝ, ℝ)) :
    IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archSechHalfWeight x) (Ioi 0) := by
  have hR := autocorr_zero_nonneg (f : ℝ → ℝ)
  have hg : IntegrableOn (fun x : ℝ => 4 * autocorr f 0 * Real.exp ((-1 / 2) * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).const_mul _
  refine hg.mono' (continuous_secantJumpIntegrand f).aestronglyMeasurable ?_
  filter_upwards [] with x
  have hΔ := autocorr_sub_nonneg f.hasCompactSupport f.continuous x
  have hsech := (archSechHalfWeight_pos x).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hΔ hsech)]
  have hupper : autocorr f 0 - autocorr f x ≤ 2 * autocorr f 0 := by
    have ha := abs_autocorr_le_zero f.hasCompactSupport f.continuous x
    linarith [neg_abs_le (autocorr f x)]
  calc
    _ ≤ (2 * autocorr f 0) * (2 * Real.exp (-x / 2)) :=
      mul_le_mul hupper (archSechHalfWeight_le_exp x) hsech (by positivity)
    _ = _ := by rw [show -x / 2 = (-1 / 2 : ℝ) * x by ring]; ring

/-- A finite family of disjoint arithmetic collars transfers the multiplier Gram
bound into the full original secant functional. Choosing `δ = log 2` gives dyadic
logarithmic nodes. The statement is unconditional for every compact source. -/
theorem biScaleSecantEnergy_ge_sinhJumpGram (f : C_c(ℝ, ℝ)) (δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, sinhJumpGramBound f (Finset.range K) (fun _ => 1)
      (fun k => (k : ℝ) * |δ|) (-y)) ≤ biScaleSecantEnergy f := by
  let t : ℕ → ℝ := fun k => (k : ℝ) * |δ|
  have h1 := intervalIntegral.integral_mono_on (μ := volume) (abs_nonneg δ)
    (((continuous_sinhJumpGramBound f (Finset.range K) (fun _ => 1) t).comp
      continuous_neg).intervalIntegrable 0 |δ|)
    (((continuous_secantJumpCollar f (Finset.range K) (fun _ => 1) t).comp
      continuous_neg).intervalIntegrable 0 |δ|)
    (fun y _ => secantJumpCollar_ge_gram f (Finset.range K) (fun _ => 1) t (-y))
  have htile := intervalIntegral_periodic_collar_sum_eq (continuous_secantJumpIntegrand f)
    0 |δ| K
  simp only [zero_add] at htile
  have hcollar : (fun y => secantJumpCollar f (Finset.range K) (fun _ => 1) t (-y)) =
      fun y => ∑ k ∈ Finset.range K,
        (autocorr f 0 - autocorr f ((k : ℝ) * |δ| + y)) *
          archSechHalfWeight ((k : ℝ) * |δ| + y) := by
    funext y
    simp [secantJumpCollar, t, sub_neg_eq_add]
  simp only [Function.comp_def] at h1
  rw [hcollar, ← htile] at h1
  apply h1.trans
  unfold biScaleSecantEnergy
  rw [intervalIntegral.integral_of_le (mul_nonneg (Nat.cast_nonneg K) (abs_nonneg δ))]
  refine setIntegral_mono_set (integrableOn_secantJumpIntegrand_compact f) ?_ ?_
  · filter_upwards [] with x
    exact mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x)
      (archSechHalfWeight_pos x).le
  · exact Filter.Eventually.of_forall fun x hx => hx.1

end
end GaloisForLFunctions.BiScaleUncertainty
