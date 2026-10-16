import GaloisForLFunctions.RHTower.CHMDStationaryVolumeCutoff

/-!
# Bounded local inverses of the theta transform

Multiplication by theta maps the mass space to ordinary L2. After a compact
cutoff its inverse is bounded as well. These maps transport literal difference
graphs and allow operator-domain arguments using adjoints, without a global
inverse or an unproved global domain identification.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

section Multiplier
variable (μ ν : Measure ℝ) (b : ℝ → ℝ) (hν : ν ≪ μ)
  (hm : ∀ u : Lp ℝ 2 μ, MemLp (fun x => b x * u x) 2 ν)

def admittedMultiplierLM : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν where
  toFun u := (hm u).toLp (fun x => b x * u x)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp, (hm v).coeFn_toLp,
      Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _), hν.ae_le (Lp.coeFn_add u v)]
      with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at *
    rw [h1, h4, h2, h3, h5, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp,
      Lp.coeFn_smul c ((hm u).toLp _), hν.ae_le (Lp.coeFn_smul c u)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at *
    change (hm (c • u)).toLp _ x = (c • (hm u).toLp _) x
    rw [h1, h3, h2, h4]
    ring

theorem admittedMultiplierLM_ae (u : Lp ℝ 2 μ) :
    admittedMultiplierLM μ ν b hν hm u =ᵐ[ν] (fun x => b x * u x) := (hm u).coeFn_toLp

theorem continuous_admittedMultiplierLM : Continuous (admittedMultiplierLM μ ν b hν hm) := by
  apply LinearMap.continuous_of_isClosed_graph
  have heq : ((admittedMultiplierLM μ ν b hν hm).graph : Set (Lp ℝ 2 μ × Lp ℝ 2 ν)) =
      {p | p.2 =ᵐ[ν] (fun x => b x * p.1 x)} := by
    ext p
    change p.2 = admittedMultiplierLM μ ν b hν hm p.1 ↔
      p.2 =ᵐ[ν] (fun x => b x * p.1 x)
    constructor
    · intro h
      rw [h]
      exact admittedMultiplierLM_ae μ ν b hν hm p.1
    · intro h
      exact Lp.ext (h.trans (admittedMultiplierLM_ae μ ν b hν hm p.1).symm)
  rw [heq]
  apply isSeqClosed_iff_isClosed.mp
  intro u p hu hp
  obtain ⟨ns, hns, hs⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((continuous_fst.tendsto p).comp hp)).exists_seq_tendsto_ae
  obtain ⟨ms, hms, he⟩ := (tendstoInMeasure_of_tendsto_Lp
    (((continuous_snd.tendsto p).comp hp).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hg : ∀ᵐ x ∂ν, ∀ n : ℕ, (u (ns (ms n))).2 x = b x * (u (ns (ms n))).1 x :=
    ae_all_iff.mpr fun n => hu (ns (ms n))
  filter_upwards [hν.ae_le hs, he, hg] with x h1 h2 h3
  exact tendsto_nhds_unique h2
    (((h1.comp hms.tendsto_atTop).const_mul (b x)).congr fun n => (h3 n).symm)

def admittedMultiplier : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  ⟨admittedMultiplierLM μ ν b hν hm, continuous_admittedMultiplierLM μ ν b hν hm⟩

theorem admittedMultiplier_ae (u : Lp ℝ 2 μ) :
    admittedMultiplier μ ν b hν hm u =ᵐ[ν] (fun x => b x * u x) :=
  admittedMultiplierLM_ae μ ν b hν hm u
end Multiplier

def thetaToVolume : MassSpace →L[ℝ] StationaryVolumeSpace :=
  admittedMultiplier massMeasure volume riemannKernelReal volume_absolutelyContinuous_mass
    (fun u => memLp_thetaProduct (Lp.stronglyMeasurable u).measurable (Lp.memLp u))

theorem thetaToVolume_ae (u : MassSpace) : thetaToVolume u =ᵐ[volume] thetaProduct u :=
  admittedMultiplier_ae _ _ _ _ _ u

theorem thetaToVolume_injective : Function.Injective thetaToVolume := by
  intro u v h
  apply Lp.ext
  apply (withDensity_absolutelyContinuous volume _).ae_le
  filter_upwards [thetaToVolume_ae u, thetaToVolume_ae v] with x hu hv
  rw [h, hv] at hu
  exact mul_left_cancel₀ (riemannKernelReal_pos x).ne' hu.symm

theorem groundToVolume_source (p : stationaryGroundGraph) :
    volumeSourceMap (groundToVolume p) = thetaToVolume (stationaryGroundSourceMap p) :=
  Lp.ext ((groundToVolume_source_ae p).trans (thetaToVolume_ae p.val.fst).symm)

def localThetaInverseFactor (n : ℕ) (x : ℝ) : ℝ := cutoff n x * (riemannKernelReal x)⁻¹

theorem localThetaInverseFactor_contDiff (n : ℕ) : ContDiff ℝ 2 (localThetaInverseFactor n) :=
  (cutoff_contDiff n).mul (contDiff_riemannKernelReal.inv fun x => (riemannKernelReal_pos x).ne')

theorem localThetaInverseFactor_compact (n : ℕ) : HasCompactSupport (localThetaInverseFactor n) :=
  (cutoff_hasCompactSupport n).mul_right

theorem memLp_localThetaInverse (n : ℕ) (u : StationaryVolumeSpace) :
    MemLp (fun x => localThetaInverseFactor n x * u x) 2 massMeasure := by
  have hm := (localThetaInverseFactor_contDiff n).continuous.measurable.mul
    (Lp.stronglyMeasurable u).measurable
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  rw [massMeasure,
    integrable_weighted_iff volume continuous_massDensity.measurable
      (Eventually.of_forall fun x => (massDensity_pos x).le)]
  let b : ℝ → ℝ := fun x => massDensity x * localThetaInverseFactor n x ^ 2
  have hb : Continuous b := continuous_massDensity.mul ((localThetaInverseFactor_contDiff n).continuous.pow 2)
  have hs : HasCompactSupport (fun x => localThetaInverseFactor n x ^ 2) :=
    (localThetaInverseFactor_compact n).comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hc : HasCompactSupport b := hs.mul_left
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hb
  have hi : Integrable (fun x => b x * u x ^ 2) := by
    refine ((Lp.memLp u).integrable_sq.const_mul C).mono'
      (hb.measurable.mul ((Lp.stronglyMeasurable u).measurable.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hC x) (sq_nonneg _)
  exact hi.congr (Eventually.of_forall fun x => by dsimp [b]; ring)

def localThetaInverse (n : ℕ) : StationaryVolumeSpace →L[ℝ] MassSpace :=
  admittedMultiplier volume massMeasure (localThetaInverseFactor n)
    (withDensity_absolutelyContinuous volume _) (memLp_localThetaInverse n)

theorem localThetaInverse_ae (n : ℕ) (u : StationaryVolumeSpace) :
    localThetaInverse n u =ᵐ[massMeasure] fun x => localThetaInverseFactor n x * u x :=
  admittedMultiplier_ae _ _ _ _ _ u

theorem thetaToVolume_localInverse (n : ℕ) (u : StationaryVolumeSpace) :
    thetaToVolume (localThetaInverse n u) = volumeCutoff n u := by
  apply Lp.ext
  filter_upwards [thetaToVolume_ae (localThetaInverse n u), volumeCutoff_ae n u,
    volume_absolutelyContinuous_mass.ae_le (localThetaInverse_ae n u)] with x ht hc hi
  rw [ht, hc]
  dsimp only [thetaProduct]
  rw [hi]
  dsimp only [localThetaInverseFactor]
  field_simp [(riemannKernelReal_pos x).ne']

theorem localInverse_thetaToVolume (n : ℕ) (u : MassSpace) :
    localThetaInverse n (thetaToVolume u) = massCutoff n u := by
  apply Lp.ext
  filter_upwards [localThetaInverse_ae n (thetaToVolume u), massCutoff_ae n u,
    (withDensity_absolutelyContinuous volume _).ae_le (thetaToVolume_ae u)] with x hi hc ht
  rw [hi, hc, ht]
  dsimp only [localThetaInverseFactor, thetaProduct]
  field_simp [(riemannKernelReal_pos x).ne']

def localToGround (n : ℕ) (q : StationaryVolumeGraph) : stationaryGroundGraph := by
  refine ⟨WithLp.toLp 2 (localThetaInverse n (volumeSourceMap q), (volumeGraphCutoff n q).val.snd), ?_⟩
  have hs : volumeSourceMap (volumeGraphCutoff n q) =
      thetaToVolume (localThetaInverse n (volumeSourceMap q)) := by
    rw [volumeGraphCutoff_source, thetaToVolume_localInverse]
  have he := (volumeGraphCutoff n q).property
  change (volumeGraphCutoff n q).val.snd =ᵐ[stationaryMeasure]
    difference (volumeSourceMap (volumeGraphCutoff n q)) at he
  rw [hs] at he
  filter_upwards [he,
    nonsingular_stationary_volume_left.ae (thetaToVolume_ae (localThetaInverse n (volumeSourceMap q))),
    nonsingular_stationary_volume_right.ae (thetaToVolume_ae (localThetaInverse n (volumeSourceMap q)))]
    with e he hl hr
  change (volumeGraphCutoff n q).val.snd e = difference (thetaProduct (localThetaInverse n (volumeSourceMap q))) e
  simpa only [difference, hl, hr] using he

theorem localToGround_source (n : ℕ) (q : StationaryVolumeGraph) :
    stationaryGroundSourceMap (localToGround n q) = localThetaInverse n (volumeSourceMap q) := rfl

theorem localToGround_edge (n : ℕ) (q : StationaryVolumeGraph) :
    (localToGround n q).val.snd = (volumeGraphCutoff n q).val.snd := rfl

end RHTower.CHMDDoobGraph
