import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SignPacking.WindowGrid
import GaloisForLFunctions.HTGeometry.Quantum.TranslatedCircuitExcursion
import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw

/-!
# Time occupation of a projective circuit tube

A bounded family of spectral reflection visits supplies separated shifts. At any observation time the shifted evolutions are
projectively separated. A fixed target accepts at most one shift. Comparing
Lebesgue lengths gives a bound uniform in the observation interval's origin.
-/

open MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- If different translates of a time set are disjoint, its occupation of
every interval is bounded by the interval length plus the span of the shifts. -/
private theorem occupation_of_separated_translates {ι : Type*} [Fintype ι]
    (τ : ι → ℝ) (S : ℝ) (hS : 0 ≤ S) (hs : ∀ i, τ i ∈ Icc 0 S)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hdis : ∀ t i j, t + τ i ∈ B → t + τ j ∈ B → i = j)
    (A T : ℝ) (hT : 0 ≤ T) :
    (Fintype.card ι : ℝ) * volume.real (B ∩ Icc A (A+T)) ≤ T+S := by
  let K := B ∩ Icc A (A+T)
  let f (i : ι) := (fun t : ℝ => t+τ i) ⁻¹' K
  have hm : MeasurableSet K := hB.inter measurableSet_Icc
  have hfm (i : ι) : MeasurableSet (f i) := hm.preimage (measurable_id.add_const _)
  have hval (i : ι) : volume (f i) = volume K :=
    (measurePreserving_add_right volume (τ i)).measure_preimage hm.nullMeasurableSet
  have hfin : volume K ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hpair : Pairwise (fun i j => Disjoint (f i) (f j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hi hj
    exact hij (hdis t i j hi.1 hj.1)
  have hsub : (⋃ i, f i) ⊆ Icc (A-S) (A+T) := by
    intro t ht
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ht
    have hb : t + τ i ∈ Icc A (A+T) := hi.2
    exact ⟨by linarith only [hb.1,(hs i).2], by linarith only [hb.2,(hs i).1]⟩
  calc
    _ = ∑ i : ι, volume.real (f i) := by simp [Measure.real, hval, K]
    _ = volume.real (⋃ i, f i) := (measureReal_iUnion_fintype hpair hfm
      (fun i => (hval i).symm ▸ hfin)).symm
    _ ≤ volume.real (Icc (A-S) (A+T)) := measureReal_mono hsub measure_Icc_lt_top.ne
    _ = T+S := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring

private def phased (A : Reg n) : Set (Reg n) :=
  (fun z : ℂ => z • A) '' Metric.sphere 0 1

private theorem phased_compact (A : Reg n) : IsCompact (phased A) :=
  (isCompact_sphere (0 : ℂ) 1).image (by fun_prop)

private theorem phased_nonempty (A : Reg n) : (phased A).Nonempty :=
  ⟨(1 : ℂ) • A, 1, by simp, rfl⟩

/-- Physical times within projective operator distance 2/5 of a fixed target. -/
private def phaseTube (H W : Reg n) : Set ℝ :=
  {t | Metric.infDist (unitaryEvolution H t) (phased W) ≤ 2/5}

private theorem phaseTube_iff (H W : Reg n) (t : ℝ) :
    t ∈ phaseTube H W ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution H t - c • W‖ ≤ 2/5 := by
  constructor
  · intro ht
    obtain ⟨_,⟨c,hc,rfl⟩,hd⟩ := exists_compactTarget_minDist
      (phased_compact W) (phased_nonempty W) (unitaryEvolution H t)
    exact ⟨c,by simpa using hc, by simpa only [← hd,dist_eq_norm] using
      (show Metric.infDist (unitaryEvolution H t) (phased W) ≤ 2/5 from ht)⟩
  · rintro ⟨c,hc,h⟩
    apply (Metric.infDist_le_dist_of_mem (show c • W ∈ phased W from ⟨c,by simpa using hc,rfl⟩)).trans
    simpa only [dist_eq_norm] using h

private theorem phaseTube_measurable (H : selfAdjoint (Reg n)) (W : Reg n) :
    MeasurableSet (phaseTube (H : Reg n) W) := by
  have hL : LipschitzWith ⟨‖(H : Reg n)‖,norm_nonneg _⟩ (unitaryEvolution (H : Reg n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    change dist (unitaryEvolution (H : Reg n) t) (unitaryEvolution H u) ≤ ‖(H : Reg n)‖ * dist t u
    rw [dist_eq_norm,Real.dist_eq]
    exact norm_unitaryEvolution_time_sub_le H.2 t u
  exact (isClosed_compactTargetCaptureTimeSet _ hL.continuous (phased W) _).measurableSet

/-- Undo right translation by a unitary and remove the common scalar phase. -/
private theorem untranslate_error (X A : Reg n) (U : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (z c : ℂ) (hz : ‖z‖ = 1) :
    ‖X - (z⁻¹*c) • (A * (U⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val)‖ =
      ‖z • (X * (U : Reg n)) - c • A‖ := by
  have h1 : (U⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val * (U : Reg n) = 1 :=
    congrArg Subtype.val (inv_mul_cancel U)
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
  rw [← CStarRing.norm_mul_coe_unitary _ U, sub_mul, Matrix.smul_mul, mul_assoc, h1, mul_one]
  have hf : z • (X*(U : Reg n) - (z⁻¹*c) • A) = z • (X*(U : Reg n)) - c • A := by
    rw [smul_sub, smul_smul, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
  rw [← hf,norm_smul,hz,one_mul]

private theorem cannot_share_center (X Y A : Reg n)
    (hsep : ∀ z : ℂ, ‖z‖ = 1 → 1 ≤ ‖X - z • Y‖)
    (b c : ℂ) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hX : ‖X-b • A‖ < 1/2) (hY : ‖Y-c • A‖ < 1/2) : False := by
  let z := b/c
  have hz : ‖z‖ = 1 := by simp [z,hb,hc]
  have hzc : z*c = b := div_mul_cancel₀ _ (norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero))
  have hclose : ‖b • A - z • Y‖ = ‖Y-c • A‖ := by
    rw [← hzc, ← smul_smul, ← smul_sub, norm_smul, hz,one_mul,norm_sub_rev]
  have h := norm_sub_le_norm_sub_add_norm_sub X (b • A) (z • Y)
  rw [hclose] at h
  linarith only [h,hsep z hz,hX,hY]

private def evolutionUnitary (H : selfAdjoint (Reg n)) (t : ℝ) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  ⟨unitaryEvolution (H : Reg n) t,unitaryEvolution_mem_unitary H.2 t⟩

/-- A tube hit after a spectral-sign shift becomes a hit of one common
backwards-translated target in spectral coordinates. -/
private theorem shifted_hit_center (H : selfAdjoint (Reg n)) (B W : Reg n)
    (s u : ℝ) (z : ℂ) (hz : ‖z‖ = 1) (hs : ‖unitaryEvolution (H : Reg n) s - z • B‖ < 1/40)
    (hx : s+u ∈ phaseTube (H : Reg n) W) :
    ∃ b : ℂ, ‖b‖ = 1 ∧
      ‖B-b • (W * ((evolutionUnitary H u)⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val)‖ < 1/2 := by
  let U := evolutionUnitary H u
  obtain ⟨c,hc,hh⟩ := (phaseTube_iff (H : Reg n) W (s+u)).mp hx
  refine ⟨z⁻¹*c,by rw [norm_mul,norm_inv,hz,hc,inv_one,one_mul],?_⟩
  rw [untranslate_error B W (evolutionUnitary H u) z c hz]
  have hp : unitaryEvolution (H : Reg n) s * (U : Reg n) = unitaryEvolution H (s+u) := by
    change unitaryEvolution (H : Reg n) s * unitaryEvolution H u = unitaryEvolution H (s+u)
    simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul H (s+u) u
  have hnear : ‖unitaryEvolution (H : Reg n) (s+u) - z • (B*(U : Reg n))‖ < 1/40 := by
    rw [← hp, ← Matrix.smul_mul, ← sub_mul, CStarRing.norm_mul_coe_unitary]
    exact hs
  rw [norm_sub_rev] at hnear
  have h := norm_sub_le_norm_sub_add_norm_sub (z • (B*(U : Reg n)))
    (unitaryEvolution (H : Reg n) (s+u)) (c • W)
  change ‖z • (B*(U : Reg n)) - c • W‖ < 1/2
  linarith only [h,hh,hnear]

/-- Visiting all anchored reflections by time S bounds the occupation of each
projective tube on every interval, with additive correction S. -/
theorem spectral_sign_visits_tube_occupation {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n))
    {S : ℝ} (hS : 0 ≤ S)
    (visits : ∀ x : Fin d → Bool, ∃ s ∈ Icc 0 S, ∃ z : ℂ, ‖z‖ = 1 ∧
      ‖unitaryEvolution H.val s - z • anchoredSpectralBooleanReflection e
        (hermitianEigenbasisUnitary H.2.isHermitian) x‖ < 1/40) :
    ∀ (W : Reg n) (offset A T : ℝ), 0 ≤ T →
      (2:ℝ)^d * volume.real
        ({t | ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution (H : Reg n) (t+offset) - c • W‖ ≤ 2/5}
          ∩ Icc A (A+T)) ≤ T+S := by
  classical
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let B := anchoredSpectralBooleanReflection e V
  choose s hs z hz hhit using visits
  intro W offset A T hT
  let hits := (fun t : ℝ => t+offset) ⁻¹' phaseTube (H : Reg n) W
  have hm : MeasurableSet hits := (phaseTube_measurable H W).preimage (measurable_id.add_const _)
  have hdis (t : ℝ) (i j : Fin d → Bool) (hi : t+s i ∈ hits) (hj : t+s j ∈ hits) : i = j := by
    let u := t+offset
    let P := W * ((evolutionUnitary H u)⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).val
    have hc (x : Fin d → Bool) (hx : t+s x ∈ hits) : ∃ b : ℂ, ‖b‖ = 1 ∧ ‖B x-b • P‖ < 1/2 := by
      apply shifted_hit_center H (B x) W (s x) u (z x) (hz x) (hhit x)
      change t+s x+offset ∈ phaseTube (H : Reg n) W at hx
      rwa [show s x+u = t+s x+offset by dsimp [u]; ring]
    by_contra hn
    obtain ⟨b,hb,hbi⟩ := hc i hi
    obtain ⟨c,hc',hcj⟩ := hc j hj
    exact cannot_share_center (B i) (B j) P
      (anchoredSpectralBooleanReflection_projective_separated e V hn) b c hb hc' hbi hcj
  have h := occupation_of_separated_translates s S hS hs hits hm hdis A T hT
  have he : hits = {t | ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖unitaryEvolution (H : Reg n) (t+offset) - c • W‖ ≤ 2/5} := by
    ext t
    exact phaseTube_iff (H : Reg n) W (t+offset)
  simpa only [he,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using h

/-- Cover a circuit visit by a gate-net target and a time grid point, then
sum the single-target occupation bound over both finite sets. -/
theorem circuit_window_occupation_of_tube_bound {n d : ℕ}
    (H : selfAdjoint (Reg n))
    {S : ℝ} (hh : ∀ (W : Reg n) (offset A T : ℝ), 0 ≤ T →
      (2:ℝ)^d * volume.real
        ({t | ∃ c : ℂ, ‖c‖ = 1 ∧ ‖unitaryEvolution H.val (t+offset) - c • W‖ ≤ 2/5}
          ∩ Icc A (A+T)) ≤ T+S) :
    ∀ (s : ℕ) (W mesh : ℝ), 0 < mesh → ‖(H : Reg n)‖*mesh ≤ 1/40 →
      ∀ A T : ℝ, 0 ≤ T →
      (2:ℝ)^d * volume.real ({u | ∃ t ∈ Icc u (u+W), HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution H.val t)} ∩ Icc A (A+T)) ≤
        (plateauGridCount W mesh : ℝ) * ((atMostQuarterCircuitNet n s).card : ℝ) * (T+S) :=
  circuit_window_occupation_at_error H (1/10) (by norm_num) hh

#print axioms spectral_sign_visits_tube_occupation
#print axioms circuit_window_occupation_of_tube_bound
end
end GaloisForLFunctions.HTGeometry
