import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheCutoffArchimedeanEnergyHasItsLiteralKernel
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszEquationHasBoundedForcing

/-!
# Bounded physical representatives of the completed Weil Riesz vectors

Positive-level truncation is admissible in the full inverse-Doob graph domain.
The cutoff archimedean row mass dominates the mass term, while its off-diagonal
part is bounded. The literal Riesz equation then forces each sufficiently high
positive truncation to vanish. Applying this to both signs of both real coordinates
gives a bounded measurable physical representative with the exact aperture support.
-/

open MeasureTheory Set Filter Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar
open HTGeometry

private theorem mul_truncPos (t r : ℝ) :
    r * truncPos t r = truncPos t r ^ 2 + t * truncPos t r := by
  unfold truncPos
  by_cases h : r - t ≤ 0
  · rw [max_eq_right h]
    ring
  · rw [max_eq_left (le_of_not_ge h)]
    ring

/-- Divergent cutoff row mass forces every sufficiently high positive truncation to vanish. -/
private theorem upper_bound_from_level_tests (a : SuzukiPositiveAperture)
    (p : apertureGraphCompletion a) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ t : ℝ, 0 ≤ t →
      inner ℝ p.val.val.snd (positiveLevelGraph p.val t).val.snd ≤
        inner ℝ p.val.val.fst (positiveLevelGraph p.val t).val.fst +
          B * ∫ x, (positiveLevelGraph p.val t).val.fst x ∂massMeasure) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂massMeasure, p.val.val.fst x ≤ M := by
  obtain ⟨δ, hδ, _, hrow⟩ := archTailMass_uniformly_unbounded a.1 2
  let C := archTailBound δ * ‖p.val.val.fst‖
  have hC : 0 ≤ C := mul_nonneg (archTailBound_pos hδ).le (norm_nonneg _)
  let t := C + B
  have ht : 0 ≤ t := add_nonneg hC hB
  let q := positiveLevelGraph p.val t
  let F := p.val.val.fst
  let G := q.val.fst
  have hq : q ∈ apertureGraphCompletion a := positiveLevelGraph_mem_aperture a p.property ht
  have hsupport := (graphPhysicalSource_supported_iff a.1 q).mp
    (physicalSource_supported_of_mem_apertureGraphCompletion a hq)
  have htrunc : G =ᵐ[massMeasure] fun x => truncPos t (F x) :=
    positiveLevelGraph_source_ae p.val t
  have hGnn : ∀ᵐ x ∂massMeasure, 0 ≤ G x := htrunc.mono fun x hx => by
    rw [hx]
    exact le_max_right _ _
  have hFG : Integrable (fun x => F x * G x) massMeasure :=
    (Lp.memLp F).integrable_mul (Lp.memLp G)
  have hGi : Integrable G massMeasure := (Lp.memLp G).integrable (by norm_num)
  have hbalance := integrable_archTail_balance δ hδ F G
  have hpoint : ∀ᵐ x ∂massMeasure,
      2 * (F x * G x) - C * G x ≤
        G x * (F x * archTailMass δ x - archTailReadout δ hδ F x) := by
    filter_upwards [htrunc, hsupport, hGnn] with x hx hs hG
    by_cases ha : x ∈ Icc (-a.1) a.1
    · have hprod : 0 ≤ F x * G x := by
        rw [hx, mul_truncPos]
        exact add_nonneg (sq_nonneg _) (mul_nonneg ht (le_max_right _ _))
      have hm := mul_le_mul_of_nonneg_right (hrow x (abs_le.mpr ha)).le hprod
      have hK : archTailReadout δ hδ F x ≤ C :=
        (le_abs_self _).trans (archTailReadout_abs_le δ hδ F x)
      have hK' := mul_le_mul_of_nonneg_right hK hG
      nlinarith only [hm, hK']
    · have hzero : G x = 0 := hs ha
      rw [hzero]
      ring_nf
      exact le_rfl
  have hlower : 2 * (∫ x, F x * G x ∂massMeasure) - C * (∫ x, G x ∂massMeasure) ≤
      archTailPair δ p.val q := by
    rw [archTailPair_eq_mass_sub_readout δ hδ]
    change _ ≤ ∫ x, G x * (F x * archTailMass δ x - archTailReadout δ hδ F x) ∂massMeasure
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hFG.const_mul 2) (hGi.const_mul C)]
    exact integral_mono_ae ((hFG.const_mul 2).sub (hGi.const_mul C)) hbalance hpoint
  have hupper := hE t ht
  have hpair : inner ℝ F G = ∫ x, F x * G x ∂massMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  change inner ℝ p.val.val.snd q.val.snd ≤ inner ℝ F G + B * ∫ x, G x ∂massMeasure at hupper
  rw [hpair] at hupper
  have htotal : (∫ x, F x * G x ∂massMeasure) ≤ t * (∫ x, G x ∂massMeasure) := by
    have hcut := archTailPair_positiveLevel_le δ p.val t
    change archTailPair δ p.val q ≤ inner ℝ p.val.val.snd q.val.snd at hcut
    dsimp only [t]
    nlinarith only [hlower, hcut, hupper]
  have hsplit : (∫ x, F x * G x ∂massMeasure) =
      (∫ x, G x ^ 2 ∂massMeasure) + t * (∫ x, G x ∂massMeasure) := by
    calc
      _ = ∫ x, G x ^ 2 + t * G x ∂massMeasure := by
        apply integral_congr_ae
        filter_upwards [htrunc] with x hx
        rw [hx, mul_truncPos]
      _ = _ := by
        rw [integral_add (Lp.memLp G).integrable_sq (hGi.const_mul t), integral_const_mul]
  have hzero : G = 0 := by
    have hn := CHMDPolar.norm_sq_eq_integral G
    rw [hsplit] at htotal
    apply norm_eq_zero.mp
    nlinarith only [hn, htotal, norm_nonneg G]
  refine ⟨t, ht, ?_⟩
  filter_upwards [htrunc, Lp.coeFn_zero ℝ 2 massMeasure] with x hx hz
  rw [hzero, hz] at hx
  have h := le_max_left (F x - t) 0
  change F x - t ≤ truncPos t (F x) at h
  rw [← hx] at h
  exact sub_nonpos.mp h

private theorem abs_inner_tanhL_le_mass (G : MassSpace)
    (hG : ∀ᵐ x ∂massMeasure, 0 ≤ G x) :
    |inner ℝ G tanhL| ≤ ∫ x, G x ∂massMeasure := by
  have hi := (Lp.memLp G).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hp := (Lp.memLp G).integrable_mul memLp_tanhHalf
  rw [inner_tanhL]
  apply abs_le.mpr
  constructor
  · rw [← integral_neg]
    apply integral_mono_ae hi.neg hp
    filter_upwards [hG] with x hx
    change -G x ≤ G x * tanhHalf x
    have h := (abs_le.mp (abs_tanhHalf_le_one x)).1
    simpa only [mul_neg, mul_one] using mul_le_mul_of_nonneg_left h hx
  · apply integral_mono_ae hp hi
    filter_upwards [hG] with x hx
    change G x * tanhHalf x ≤ G x
    have h := (abs_le.mp (abs_tanhHalf_le_one x)).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h hx

/-- The two polar terms contribute bounded profiles in inverse-Doob coordinates. -/
private theorem upper_bound_from_weil_mass_forcing (a : SuzukiPositiveAperture)
    (p : apertureGraphCompletion a) (E : ℝ) (hE : 0 ≤ E)
    (hW : ∀ q : apertureGraphCompletion a,
      (∀ᵐ x ∂massMeasure, 0 ≤ q.val.val.fst x) →
      |weilBilin p.val q.val| ≤ E * ∫ x, q.val.val.fst x ∂massMeasure) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂massMeasure, p.val.val.fst x ≤ M := by
  let F := p.val.val.fst
  let B := E + 2 * |inner ℝ F oneL| + 2 * |inner ℝ F tanhL|
  apply upper_bound_from_level_tests a p B (by dsimp only [B]; positivity)
  intro t ht
  let q : apertureGraphCompletion a :=
    ⟨positiveLevelGraph p.val t, positiveLevelGraph_mem_aperture a p.property ht⟩
  let G := q.val.val.fst
  have hG : ∀ᵐ x ∂massMeasure, 0 ≤ G x := by
    filter_upwards [positiveLevelGraph_source_ae p.val t] with x hx
    change 0 ≤ (positiveLevelGraph p.val t).val.fst x
    rw [hx]
    exact le_max_right _ _
  have hI : 0 ≤ ∫ x, G x ∂massMeasure := integral_nonneg_of_ae hG
  have hW' := (le_abs_self (weilBilin p.val q.val)).trans (hW q hG)
  have htan := abs_inner_tanhL_le_mass G hG
  have htanprod : inner ℝ F tanhL * inner ℝ G tanhL ≤
      |inner ℝ F tanhL| * ∫ x, G x ∂massMeasure := by
    calc
      _ ≤ |inner ℝ F tanhL * inner ℝ G tanhL| := le_abs_self _
      _ = |inner ℝ F tanhL| * |inner ℝ G tanhL| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left htan (abs_nonneg _)
  have hone : -(inner ℝ F oneL * inner ℝ G oneL) ≤
      |inner ℝ F oneL| * ∫ x, G x ∂massMeasure := by
    rw [inner_oneL G]
    simpa only [neg_mul] using
      mul_le_mul_of_nonneg_right (neg_le_abs (inner ℝ F oneL)) hI
  unfold weilBilin at hW'
  rw [graph_inner] at hW'
  change inner ℝ F G + inner ℝ p.val.val.snd q.val.val.snd -
      2 * inner ℝ F G + 2 * (inner ℝ F oneL * inner ℝ G oneL) -
      2 * (inner ℝ F tanhL * inner ℝ G tanhL) ≤ E * ∫ x, G x ∂massMeasure at hW'
  change inner ℝ p.val.val.snd q.val.val.snd ≤
    inner ℝ F G + B * ∫ x, G x ∂massMeasure
  dsimp only [B]
  nlinarith only [hW', htanprod, hone]

private theorem bounded_from_weil_mass_forcing (a : SuzukiPositiveAperture)
    (p : apertureGraphCompletion a) (E : ℝ) (hE : 0 ≤ E)
    (hW : ∀ q : apertureGraphCompletion a,
      (∀ᵐ x ∂massMeasure, 0 ≤ q.val.val.fst x) →
      |weilBilin p.val q.val| ≤ E * ∫ x, q.val.val.fst x ∂massMeasure) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂massMeasure, |p.val.val.fst x| ≤ M := by
  obtain ⟨M, hM, hp⟩ := upper_bound_from_weil_mass_forcing a p E hE hW
  have hneg : ∀ q : apertureGraphCompletion a,
      (∀ᵐ x ∂massMeasure, 0 ≤ q.val.val.fst x) →
      |weilBilin (-p).val q.val| ≤ E * ∫ x, q.val.val.fst x ∂massMeasure := by
    intro q hq
    have h := weilBilin_sub_left 0 p.val q.val
    have hz : weilBilin 0 q.val = 0 := by simp [weilBilin]
    rw [zero_sub, hz, zero_sub] at h
    change |weilBilin (-p.val) q.val| ≤ _
    rw [h, abs_neg]
    exact hW q hq
  obtain ⟨N, hN, hn⟩ := upper_bound_from_weil_mass_forcing a (-p) E hE hneg
  refine ⟨M + N, add_nonneg hM hN, ?_⟩
  filter_upwards [hp, hn, Lp.coeFn_neg p.val.val.fst] with x hx hy he
  change (-p.val.val.fst) x ≤ N at hy
  rw [he, Pi.neg_apply] at hy
  exact abs_le.mpr ⟨by linarith only [hy, hM], by linarith only [hx, hN]⟩

namespace WeilHilbertBeforeContact

/-- The actual Fourier Riesz vector has two bounded inverse-Doob coordinates. -/
theorem evalVector_bounded_real_graph_coordinates (a : PrecontactAperture) (z : ℂ) :
    ∃ p r : apertureGraphCompletion a.1,
      evalVector a z = ofRealGraph a p + I • ofRealGraph a r ∧
      ∃ M N : ℝ, 0 ≤ M ∧ 0 ≤ N ∧
        (∀ᵐ x ∂massMeasure, |p.val.val.fst x| ≤ M) ∧
        (∀ᵐ x ∂massMeasure, |r.val.val.fst x| ≤ N) := by
  obtain ⟨p, r, hv, hW⟩ := riesz_real_graph_forcing a z
  obtain ⟨M, hM, hp⟩ := bounded_from_weil_mass_forcing a.1 p
    (Real.exp (a.1.1 * |z.im|)) (Real.exp_pos _).le (fun q hq => (hW q hq).1)
  obtain ⟨N, hN, hr⟩ := bounded_from_weil_mass_forcing a.1 r
    (Real.exp (a.1.1 * |z.im|)) (Real.exp_pos _).le (fun q hq => (hW q hq).2)
  exact ⟨p, r, hv, M, N, hM, hN, hp, hr⟩

/-- Every completed Fourier-evaluation Riesz source before contact is essentially bounded. -/
theorem evalVector_physical_essentially_bounded (a : PrecontactAperture) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume,
      ‖ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) x‖ ≤ C := by
  obtain ⟨p, r, hv, M, N, hM, hN, hp, hr⟩ := evalVector_bounded_real_graph_coordinates a z
  obtain ⟨T, hT, htheta⟩ := exists_theta_bound
  have hphys : ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) =
      graphPhysicalSource p.val + I • graphPhysicalSource r.val := by
    rw [hv, map_add, map_smul, toForm_ofRealGraph, toForm_ofRealGraph,
      map_add, map_smul, apertureGraphWeilEquiv_physical, apertureGraphWeilEquiv_physical]
  refine ⟨T * (M + N), mul_nonneg hT (add_nonneg hM hN), ?_⟩
  rw [hphys]
  filter_upwards [volume_absolutelyContinuous_mass.ae_le hp,
    volume_absolutelyContinuous_mass.ae_le hr, graphPhysicalSource_ae p.val,
    graphPhysicalSource_ae r.val,
    Lp.coeFn_add (graphPhysicalSource p.val) (I • graphPhysicalSource r.val),
    Lp.coeFn_smul I (graphPhysicalSource r.val)] with x hp hr hpx hrx hadd hsmul
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hpx, hrx]
  calc
    _ ≤ ‖(phiDoobTest p.val.val.fst x : ℂ)‖ +
        ‖I • (phiDoobTest r.val.val.fst x : ℂ)‖ := norm_add_le _ _
    _ = riemannKernelReal x * (|p.val.val.fst x| + |r.val.val.fst x|) := by
      rw [norm_smul, Complex.norm_I, one_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs, phiDoobTest, abs_mul,
        abs_of_pos (riemannKernelReal_pos x)]
      ring
    _ ≤ T * (M + N) := mul_le_mul (htheta x) (add_le_add hp hr)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)) hT

#print axioms evalVector_bounded_real_graph_coordinates
#print axioms evalVector_physical_essentially_bounded

/-- A bounded measurable representative retains the exact closed aperture support. -/
theorem evalVector_has_bounded_physical_representative (a : PrecontactAperture) (z : ℂ) :
    ∃ f : ℝ → ℂ, Measurable f ∧
      f =ᵐ[volume] ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) ∧
      (∀ x ∉ Icc (-a.1.1) a.1.1, f x = 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  classical
  obtain ⟨C, hC, hb⟩ := evalVector_physical_essentially_bounded a z
  let F := ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))
  let S := {x : ℝ | x ∈ Icc (-a.1.1) a.1.1 ∧ ‖F x‖ ≤ C}
  have hS : MeasurableSet S :=
    measurableSet_Icc.inter (measurableSet_le (Lp.stronglyMeasurable F).measurable.norm measurable_const)
  let f : ℝ → ℂ := S.indicator F
  have hs : ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1) a.1.1 → F x = 0 := by
    have h := suzukiCutoff_ae_eq_zero_off a.1.1 F
    have hfix : suzukiCutoff a.1.1 F = F :=
      indicatorCutoff_ccmArchimedeanFormEmbedding a.1 _
    rw [hfix] at h
    exact h
  refine ⟨f, (Lp.stronglyMeasurable F).measurable.indicator hS, ?_, ?_, C, hC, ?_⟩
  · filter_upwards [hb, hs] with x hx hz
    change S.indicator F x = F x
    by_cases ha : x ∈ Icc (-a.1.1) a.1.1
    · exact indicator_of_mem (show x ∈ S from ⟨ha, hx⟩) F
    · rw [indicator_of_notMem (show x ∉ S from fun h => ha h.1), hz ha]
  · intro x hx
    exact indicator_of_notMem (show x ∉ S from fun h => hx h.1) F
  · intro x
    change ‖S.indicator F x‖ ≤ C
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact hx.2
    · rw [indicator_of_notMem hx, norm_zero]
      exact hC

#print axioms evalVector_has_bounded_physical_representative

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
