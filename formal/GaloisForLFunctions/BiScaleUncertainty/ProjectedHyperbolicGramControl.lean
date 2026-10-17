import GaloisForLFunctions.BiScaleUncertainty.CenteredHyperbolicGramControl

/-!
# Source-orthogonal control of hyperbolic multiplier leakage

The centered weighted source is orthogonal to the original source. Projecting
the difference packet off that source replaces its Gram energy by its Schur
residual. The resulting envelope improves every scalar-centered envelope and
transfers into the full odd secant and plastic functionals.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ProjectedHyperbolicGram
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram
noncomputable section
variable {ι : Type*}

/-- The actual quadratic source mean; division by zero has its usual real value. -/
def sourceMean (f : C_c(ℝ, ℝ)) (α : ℝ) : ℝ := coshMass f α / autocorr f 0

/-- Pairing of a translation packet with its original source. -/
def packetCovariance (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * autocorr f (t i)

/-- Exact Gram energy after removing the component along the original source. -/
def packetSchurEnergy (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) : ℝ :=
  translationGramEnergy f s w t - packetCovariance f s w t ^ 2 / autocorr f 0

private def compactPacket (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => ∑ i ∈ s, w i * f (u + t i),
    continuous_finsetSum s fun i _ =>
      continuous_const.mul (f.continuous.comp (continuous_add_const (t i)))⟩, by
    have hs := HasCompactSupport.finset_sum (s := s)
      (f := fun i u => w i * f (u + t i))
      (fun i _ => (hasCompactSupport_comp_add f.hasCompactSupport (t i)).mul_left)
    have he : (∑ i ∈ s, fun u => w i * f (u + t i)) =
        (fun u => ∑ i ∈ s, w i * f (u + t i)) := by
      funext u
      simp only [Finset.sum_apply]
    rwa [he] at hs⟩

private def subtractSource (p f : C_c(ℝ, ℝ)) (c : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => p u - c * f u, p.continuous.sub (continuous_const.mul f.continuous)⟩,
    p.hasCompactSupport.sub f.hasCompactSupport.mul_left⟩

private def pairing (f g : C_c(ℝ, ℝ)) : ℝ := ∫ u, f u * g u

private theorem pairing_self (f : C_c(ℝ, ℝ)) : pairing f f = autocorr f 0 := by
  simp only [pairing, autocorr, add_zero]

private theorem pairing_comm (f g : C_c(ℝ, ℝ)) : pairing f g = pairing g f := by
  unfold pairing
  simp only [mul_comm]

private theorem pairing_sq_le (f g : C_c(ℝ, ℝ)) :
    pairing f g ^ 2 ≤ autocorr f 0 * autocorr g 0 := by
  have h := HTGeometry.sq_integral_mul_le (f := (f : ℝ → ℝ)) (g := (g : ℝ → ℝ))
    f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable
    (integrable_sq f.continuous f.hasCompactSupport)
    (integrable_sq g.continuous g.hasCompactSupport)
  rwa [integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero] at h

private theorem pairing_sub_right (p q f : C_c(ℝ, ℝ)) (c : ℝ) :
    pairing p (subtractSource q f c) = pairing p q - c * pairing p f := by
  have hiq : Integrable (fun u => p u * q u) :=
    (p.continuous.mul q.continuous).integrable_of_hasCompactSupport p.hasCompactSupport.mul_right
  have hif : Integrable (fun u => p u * f u) :=
    (p.continuous.mul f.continuous).integrable_of_hasCompactSupport p.hasCompactSupport.mul_right
  have he : (fun u => p u * subtractSource q f c u) =
      fun u => p u * q u - c * (p u * f u) := by
    funext u
    change p u * (q u - c * f u) = _
    ring
  unfold pairing
  rw [he, integral_sub hiq (hif.const_mul c), integral_const_mul]

private theorem subtractSource_energy (p f : C_c(ℝ, ℝ)) (c : ℝ) :
    autocorr (subtractSource p f c) 0 =
      autocorr p 0 - 2 * c * pairing p f + c ^ 2 * autocorr f 0 := by
  rw [← pairing_self, pairing_sub_right, pairing_comm (subtractSource p f c) p,
    pairing_sub_right, pairing_comm (subtractSource p f c) f, pairing_sub_right,
    pairing_self, pairing_self, pairing_comm f p]
  ring

private theorem pairing_packet (f q : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    pairing q (compactPacket f s w t) =
      ∑ i ∈ s, w i * (∫ u, q u * f (u + t i)) := by
  have hint (i : ι) : Integrable (fun u => w i * (q u * f (u + t i))) :=
    ((q.continuous.mul (f.continuous.comp (continuous_add_const (t i)))).integrable_of_hasCompactSupport
      q.hasCompactSupport.mul_right).const_mul _
  have he : (fun u => q u * compactPacket f s w t u) =
      fun u => ∑ i ∈ s, w i * (q u * f (u + t i)) := by
    funext u
    change q u * (∑ i ∈ s, w i * f (u + t i)) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold pairing
  rw [he, integral_finsetSum _ (fun i _ => hint i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

private theorem packet_energy (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    autocorr (compactPacket f s w t) 0 = translationGramEnergy f s w t := by
  rw [← integral_sq_eq_autocorr_zero, translationGramEnergy_eq_integral]
  rfl

private theorem pairing_source_packet (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    pairing f (compactPacket f s w t) = packetCovariance f s w t := by
  rw [pairing_packet]
  rfl

theorem packetCovariance_sq_le (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    packetCovariance f s w t ^ 2 ≤ autocorr f 0 * translationGramEnergy f s w t := by
  have h := pairing_sq_le f (compactPacket f s w t)
  rwa [pairing_source_packet, packet_energy] at h

private theorem projected_packet_energy (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    autocorr (subtractSource (compactPacket f s w t) f
      (packetCovariance f s w t / autocorr f 0)) 0 = packetSchurEnergy f s w t := by
  rw [subtractSource_energy, packet_energy, pairing_comm, pairing_source_packet]
  unfold packetSchurEnergy
  by_cases hR : autocorr f 0 = 0
  · simp [hR]
  · field_simp
    ring

theorem packetSchurEnergy_nonneg (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    0 ≤ packetSchurEnergy f s w t := by
  rw [← projected_packet_energy]
  exact autocorr_zero_nonneg _

theorem packetSchurEnergy_le_gram (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    packetSchurEnergy f s w t ≤ translationGramEnergy f s w t := by
  unfold packetSchurEnergy
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (autocorr_zero_nonneg f))

private theorem pairing_centered_source (f : C_c(ℝ, ℝ)) (α c : ℝ) :
    pairing (centeredSource f α c) f = coshMass f α - c * autocorr f 0 := by
  have hs : HasCompactSupport (fun u => f u ^ 2) := by
    have h : HasCompactSupport (fun u => f u * f u) := f.hasCompactSupport.mul_right
    simpa only [sq] using h
  have hc : Continuous (fun u => Real.cosh (2 * α * u) * f u ^ 2) :=
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul (f.continuous.pow 2)
  have hm : Integrable (fun u => Real.cosh (2 * α * u) * f u ^ 2) :=
    hc.integrable_of_hasCompactSupport hs.mul_left
  have hf := integrable_sq (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have he : (fun u => centeredSource f α c u * f u) =
      fun u => Real.cosh (2 * α * u) * f u ^ 2 - c * (f u ^ 2) := by
    funext u
    change ((Real.cosh (2 * α * u) - c) * f u) * f u = _
    ring
  unfold pairing
  rw [he, integral_sub hm (hf.const_mul c), integral_const_mul, integral_sq_eq_autocorr_zero]
  rfl

/-- Orthogonality is proved from actual source data, with no nonzero-energy premise. -/
theorem centered_source_orthogonal (f : C_c(ℝ, ℝ)) (α : ℝ) :
    (∫ u, centeredSource f α (sourceMean f α) u * f u) = 0 := by
  change pairing _ _ = 0
  rw [pairing_centered_source]
  unfold sourceMean
  by_cases hR : autocorr f 0 = 0
  · have h := sourceVariance_nonneg f α
    unfold sourceVariance at h
    rw [hR] at h
    have hm : coshMass f α = 0 := by nlinarith [sq_nonneg (coshMass f α)]
    simp [hR, hm]
  · field_simp
    ring

/-- Source-orthogonal packet control removes its full source-parallel energy. -/
theorem centered_mixedPacket_abs_le_schur (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    |∑ i ∈ s, w i * (∫ u, centeredSource f α (sourceMean f α) u * f (u + t i))| ≤
      Real.sqrt (autocorr (centeredSource f α (sourceMean f α)) 0 *
        packetSchurEnergy f s w t) := by
  let q := centeredSource f α (sourceMean f α)
  let p := subtractSource (compactPacket f s w t) f (packetCovariance f s w t / autocorr f 0)
  have ho : pairing q f = 0 := centered_source_orthogonal f α
  have hp : pairing q p = pairing q (compactPacket f s w t) := by
    dsimp [p]
    rw [pairing_sub_right, ho, mul_zero, sub_zero]
  have h := pairing_sq_le q p
  rw [hp, pairing_packet, projected_packet_energy] at h
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- Actual multiplier leakage uses the source Schur residual, without a free center. -/
def projectedDefectUpper (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ) : ℝ :=
  sourceCorrection f α (sourceMean f α) s w t +
    Real.sqrt (autocorr (centeredSource f α (sourceMean f α)) 0 *
      packetSchurEnergy f s.offDiag (differenceWeight α w t) (differenceNode t))

theorem odd_defect_abs_sub_meanCorrection_le (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    |sinhCliqueGramDefect (oddCompactSource f) α s w t -
        sourceCorrection (oddCompactSource f) α (sourceMean (oddCompactSource f) α) s w t| ≤
      Real.sqrt (autocorr (centeredSource (oddCompactSource f) α
        (sourceMean (oddCompactSource f) α)) 0 *
          packetSchurEnergy (oddCompactSource f) s.offDiag
            (differenceWeight α w t) (differenceNode t)) := by
  rw [odd_defect_eq_source, add_sub_cancel_left]
  exact centered_mixedPacket_abs_le_schur _ _ _ _ _

theorem odd_defect_le_projectedDefectUpper (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    sinhCliqueGramDefect (oddCompactSource f) α s w t ≤
      projectedDefectUpper (oddCompactSource f) α s w t := by
  have h := (le_abs_self _).trans (odd_defect_abs_sub_meanCorrection_le f α s w t)
  unfold projectedDefectUpper
  linarith

private theorem scalar_projection_bound (R A G K z : ℝ)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hK : K ^ 2 ≤ R * G) (hH : 0 ≤ G - K ^ 2 / R) :
    Real.sqrt (A * (G - K ^ 2 / R)) ≤
      z * K + Real.sqrt ((A + R * z ^ 2) * G) := by
  by_cases hR0 : R = 0
  · have hK0 : K = 0 := by rw [hR0] at hK; nlinarith [sq_nonneg K]
    simp [hR0, hK0]
  · have hr : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hR (Ne.symm hR0))).ne'
    have hk : Real.sqrt R * (K / Real.sqrt R) = K := by field_simp
    have hG : Real.sqrt (G - K ^ 2 / R) ^ 2 + (K / Real.sqrt R) ^ 2 = G := by
      rw [Real.sq_sqrt hH, div_pow, Real.sq_sqrt hR]
      ring
    have hQ : Real.sqrt A ^ 2 + (z * Real.sqrt R) ^ 2 = A + R * z ^ 2 := by
      rw [Real.sq_sqrt hA, mul_pow, Real.sq_sqrt hR]
      ring
    let a := Real.sqrt A
    let b := Real.sqrt (G - K ^ 2 / R)
    let x := z * Real.sqrt R
    let k := K / Real.sqrt R
    have hid : (a ^ 2 + x ^ 2) * (b ^ 2 + k ^ 2) - (a * b - x * k) ^ 2 =
        (a * k + x * b) ^ 2 := by ring
    have hsq : (a * b - x * k) ^ 2 ≤ (A + R * z ^ 2) * G := by
      rw [← hG, ← hQ]
      nlinarith only [sq_nonneg (a * k + x * b), hid]
    have hle : a * b - x * k ≤ Real.sqrt ((A + R * z ^ 2) * G) :=
      (le_abs_self _).trans (by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq)
    have hab : a * b = Real.sqrt (A * (G - K ^ 2 / R)) := (Real.sqrt_mul hA _).symm
    have hxk : x * k = z * K := by dsimp [x, k]; rw [mul_assoc, hk]
    rw [hab, hxk] at hle
    linarith

/-- Changing the center shifts its explicit source correction by the packet covariance. -/
theorem sourceCorrection_shift (f : C_c(ℝ, ℝ)) (α c d : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    sourceCorrection f α c s w t = sourceCorrection f α d s w t +
      (c - d) * packetCovariance f s.offDiag (differenceWeight α w t) (differenceNode t) := by
  unfold sourceCorrection packetCovariance
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- Projection improves every scalar-centered envelope, including signed correlations. -/
theorem projectedDefectUpper_le_every_center (f : C_c(ℝ, ℝ)) (α c : ℝ)
    (s : Finset ι) (w t : ι → ℝ) :
    projectedDefectUpper f α s w t ≤ sourceDefectUpper f α c s w t := by
  let P := s.offDiag
  let a := differenceWeight α w t
  let d := differenceNode t
  have h := scalar_projection_bound (autocorr f 0)
    (autocorr (centeredSource f α (sourceMean f α)) 0)
    (translationGramEnergy f P a d) (packetCovariance f P a d) (c - sourceMean f α)
    (autocorr_zero_nonneg _) (autocorr_zero_nonneg _)
    (packetCovariance_sq_le f P a d) (packetSchurEnergy_nonneg f P a d)
  have he := centered_energy_minimizer f α c
  change autocorr (centeredSource f α (sourceMean f α)) 0 +
    autocorr f 0 * (c - sourceMean f α) ^ 2 = autocorr (centeredSource f α c) 0 at he
  rw [he] at h
  unfold projectedDefectUpper sourceDefectUpper packetSchurEnergy
  rw [sourceCorrection_shift f α c (sourceMean f α)]
  linarith

/-- On an exact source clique, scalar centering is already optimal at the mean:
the source projection gives no further gain and every source correction vanishes. -/
theorem sourceClique_centering_boundary (f : C_c(ℝ, ℝ)) (α : ℝ)
    (s : Finset ι) (w t : ι → ℝ)
    (hzero : ∀ p ∈ s.offDiag, autocorr f (differenceNode t p) = 0) :
    (∀ c, sourceCorrection f α c s w t = 0) ∧
      projectedDefectUpper f α s w t = sourceDefectUpper f α (sourceMean f α) s w t ∧
        ∀ c, sourceDefectUpper f α (sourceMean f α) s w t ≤ sourceDefectUpper f α c s w t := by
  have hk : packetCovariance f s.offDiag (differenceWeight α w t) (differenceNode t) = 0 := by
    unfold packetCovariance
    exact Finset.sum_eq_zero fun p hp => by rw [hzero p hp, mul_zero]
  have he (c : ℝ) : sourceCorrection f α c s w t = 0 := by
    unfold sourceCorrection
    exact Finset.sum_eq_zero fun p hp => by rw [hzero p hp, mul_zero]
  have hu : projectedDefectUpper f α s w t = sourceDefectUpper f α (sourceMean f α) s w t := by
    unfold projectedDefectUpper sourceDefectUpper packetSchurEnergy
    rw [hk]
    norm_num
  refine ⟨he, hu, fun c => ?_⟩
  rw [← hu]
  exact projectedDefectUpper_le_every_center f α c s w t

/-- Uncompensated jump lower bound with the projected leakage penalty. -/
def projectedJumpBound (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) : ℝ :=
  autocorr (sinhCompact (1 / 2) f) 0 *
      ((∑ i ∈ s, sinhJumpTransferWeights f b t y i * Real.cosh ((t i - y) / 2)) -
        Real.sqrt (∑ i ∈ s, sinhJumpTransferWeights f b t y i ^ 2)) -
    Real.sqrt (autocorr (sinhCompact (1 / 2) f) 0 *
      max (projectedDefectUpper f (1 / 2) s (sinhJumpTransferWeights f b t y) t) 0)

/-- The projected lower bound dominates all previous centered lower bounds. -/
theorem every_center_le_projectedJumpBound (f : C_c(ℝ, ℝ)) (c : ℝ)
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    centeredJumpBound f c s b t y ≤ projectedJumpBound f s b t y := by
  have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (max_le_max_right 0 (projectedDefectUpper_le_every_center f (1 / 2) c s
      (sinhJumpTransferWeights f b t y) t)) (autocorr_zero_nonneg (sinhCompact (1 / 2) f)))
  unfold centeredJumpBound projectedJumpBound
  linarith

theorem odd_projectedJumpBound_le_gram (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    projectedJumpBound (oddCompactSource f) s b t y ≤
      sinhJumpGramBound (oddCompactSource f) s b t y := by
  let F := oddCompactSource f
  let v := sinhJumpTransferWeights F b t y
  let R := autocorr (sinhCompact (1 / 2) F) 0
  let A := ∑ i ∈ s, v i ^ 2
  let D := sinhCliqueGramDefect F (1 / 2) s v t
  let U := projectedDefectUpper F (1 / 2) s v t
  have hR : 0 ≤ R := autocorr_zero_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD : D ≤ U := odd_defect_le_projectedDefectUpper f (1 / 2) s v t
  have hB : 0 ≤ R * max U 0 := mul_nonneg hR (le_max_right _ _)
  have hsq : (R * Real.sqrt A) ^ 2 = R * (R * A) := by
    rw [mul_pow, Real.sq_sqrt hA]
    ring
  have hroot : Real.sqrt (R * (R * A + D)) ≤
      R * Real.sqrt A + Real.sqrt (R * max U 0) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hcost : R * D ≤ R * max U 0 :=
      mul_le_mul_of_nonneg_left (hD.trans (le_max_left _ _)) hR
    have hcross : 0 ≤ (R * Real.sqrt A) * Real.sqrt (R * max U 0) := by positivity
    nlinarith [Real.sq_sqrt hB]
  unfold projectedJumpBound sinhJumpGramBound
  rw [sinhGram_eq_diagonal_add_defect]
  change R * ((∑ i ∈ s, v i * Real.cosh ((t i - y) / 2)) - Real.sqrt A) -
      Real.sqrt (R * max U 0) ≤
    R * (∑ i ∈ s, v i * Real.cosh ((t i - y) / 2)) - Real.sqrt (R * (R * A + D))
  linarith

theorem odd_secantJumpCollar_ge_projected (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) (y : ℝ) :
    projectedJumpBound (oddCompactSource f) s b t y ≤
      secantJumpCollar (oddCompactSource f) s b t y :=
  (odd_projectedJumpBound_le_gram f s b t y).trans (secantJumpCollar_ge_gram _ _ _ _ _)

theorem continuous_projectedJumpBound (f : C_c(ℝ, ℝ))
    (s : Finset ι) (b t : ι → ℝ) : Continuous (projectedJumpBound f s b t) := by
  have hv := continuous_sinhJumpTransferWeights f b t
  have ha (p : ι × ι) : Continuous (fun y =>
      differenceWeight (1 / 2) (sinhJumpTransferWeights f b t y) t p) := by
    unfold differenceWeight
    exact ((hv p.1).mul (hv p.2)).div_const _
  have he : Continuous (fun y => sourceCorrection f (1 / 2) (sourceMean f (1 / 2)) s
      (sinhJumpTransferWeights f b t y) t) := by
    unfold sourceCorrection
    exact continuous_finsetSum _ fun p _ => ((ha p).mul continuous_const).mul continuous_const
  have hg : Continuous (fun y => translationGramEnergy f s.offDiag
      (differenceWeight (1 / 2) (sinhJumpTransferWeights f b t y) t) (differenceNode t)) := by
    unfold translationGramEnergy
    exact continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ =>
      ((ha p).mul (ha q)).mul continuous_const
  have hk : Continuous (fun y => packetCovariance f s.offDiag
      (differenceWeight (1 / 2) (sinhJumpTransferWeights f b t y) t) (differenceNode t)) := by
    unfold packetCovariance
    exact continuous_finsetSum _ fun p _ => (ha p).mul continuous_const
  have hu : Continuous (fun y => projectedDefectUpper f (1 / 2) s
      (sinhJumpTransferWeights f b t y) t) := by
    unfold projectedDefectUpper packetSchurEnergy
    exact he.add (Real.continuous_sqrt.comp
      (continuous_const.mul (hg.sub ((hk.pow 2).div_const _))))
  unfold projectedJumpBound
  exact (continuous_const.mul
    ((continuous_finsetSum _ fun i _ => (hv i).mul (by fun_prop)).sub
      (Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (hv i).pow 2)))).sub
    (Real.continuous_sqrt.comp (continuous_const.mul (hu.max continuous_const)))

/-- Full secant-energy receiver with the source-parallel packet cost removed. -/
theorem odd_secantEnergy_ge_projected (f : C_c(ℝ, ℝ)) (δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, projectedJumpBound (oddCompactSource f) (Finset.range K)
      (fun _ => 1) (fun k => (k : ℝ) * |δ|) (-y)) ≤ biScaleSecantEnergy (oddCompactSource f) := by
  refine le_trans ?_ (biScaleSecantEnergy_ge_sinhJumpGram (oddCompactSource f) δ K)
  exact intervalIntegral.integral_mono_on (μ := volume) (abs_nonneg δ)
    (((continuous_projectedJumpBound _ _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (((continuous_sinhJumpGramBound _ _ _ _).comp continuous_neg).intervalIntegrable _ _)
    (fun y _ => odd_projectedJumpBound_le_gram f _ _ _ (-y))

/-- Actual odd plastic crossover with the improved source Schur penalty. -/
theorem odd_plasticCrossover_ge_projected (f : C_c(ℝ, ℝ)) (δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, projectedJumpBound (oddCompactSource f) (Finset.range K)
      (fun _ => 1) (fun k => (k : ℝ) * |δ|) (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      plasticCrossover (oddCompactSource f) := by
  have h := odd_secantEnergy_ge_projected f δ K
  rw [plasticCrossover_eq_secant_add_remainder_add_moment, hyperbolicMomentEnergy_oddSource]
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty.ProjectedHyperbolicGram
