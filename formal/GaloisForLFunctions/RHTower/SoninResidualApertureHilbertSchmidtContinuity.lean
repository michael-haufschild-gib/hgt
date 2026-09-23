import GaloisForLFunctions.RHTower.SoninProjectionApertureStrongContinuity
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import GaloisForLFunctions.RHTower.SummableEulerCalkinInjectivity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry
open ContinuousLinearMap

private def innerAperture' (a : ℝ) (n : ℕ) : ℝ :=
  a - 1 / ((n : ℝ) + 1)

private theorem innerAperture'_lt (a : ℝ) (n : ℕ) :
    innerAperture' a n < a := by
  dsimp [innerAperture']
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hn
  linarith

private theorem physical_zero_at_limit_of_mem_orthogonal_all_lt
    {a : ℝ} {f : SoninL2}
    (hf : ∀ b : Set.Iio a, f ∈ (centralPhysicalForbidden b.1)ᗮ) :
    (centralInterval a).indicator (⇑f) =ᵐ[volume] 0 := by
  have hzero : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ centralInterval (innerAperture' a n) → (f : ℝ → ℂ) x = 0 := by
    intro n
    have hmem := indicator_ae_zero_of_mem_physicalForbidden_orthogonal
      (hf ⟨innerAperture' a n, innerAperture'_lt a n⟩)
    filter_upwards [hmem] with x hx
    intro hxmem
    rw [centralInterval] at hxmem
    rw [Set.indicator_of_mem hxmem] at hx
    simpa using hx
  rw [← ae_all_iff] at hzero
  filter_upwards [hzero, volume.ae_ne (-a), volume.ae_ne a] with x hx hleft hright
  by_cases hxmem : x ∈ centralInterval a
  · have hxlt : |x| < a := by
      rw [centralInterval, Set.mem_Icc] at hxmem
      rw [abs_lt]
      exact ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hleft),
        lt_of_le_of_ne hxmem.2 hright⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < a - |x| by linarith)
    have hbound : |x| ≤ innerAperture' a n := by
      dsimp [innerAperture']
      have : 1 / ((n : ℝ) + 1) < a - |x| := hn
      linarith
    rw [Set.indicator_of_mem hxmem, hx n (abs_le.mp hbound)]
    rfl
  · rw [Set.indicator_of_notMem hxmem]
    rfl

private theorem fourier_zero_at_limit_of_mem_orthogonal_all_lt
    {a : ℝ} {f : SoninL2}
    (hf : ∀ b : Set.Iio a, f ∈ (centralFourierForbidden b.1)ᗮ) :
    (centralInterval a).indicator (⇑(fourierUnitary f)) =ᵐ[volume] 0 := by
  have hzero : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ centralInterval (innerAperture' a n) →
        ((fourierUnitary f : SoninL2) : ℝ → ℂ) x = 0 := by
    intro n
    have hmem := fourier_indicator_ae_zero_of_mem_fourierOrthogonal
      (hf ⟨innerAperture' a n, innerAperture'_lt a n⟩)
    filter_upwards [hmem] with x hx
    intro hxmem
    simpa [Set.indicator_of_mem hxmem] using hx
  rw [← ae_all_iff] at hzero
  filter_upwards [hzero, volume.ae_ne (-a), volume.ae_ne a] with x hx hleft hright
  by_cases hxmem : x ∈ centralInterval a
  · have hxlt : |x| < a := by
      rw [centralInterval, Set.mem_Icc] at hxmem
      rw [abs_lt]
      exact ⟨lt_of_le_of_ne hxmem.1 (Ne.symm hleft),
        lt_of_le_of_ne hxmem.2 hright⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < a - |x| by linarith)
    have hbound : |x| ≤ innerAperture' a n := by
      dsimp [innerAperture']
      have : 1 / ((n : ℝ) + 1) < a - |x| := hn
      linarith
    rw [Set.indicator_of_mem hxmem, hx n (abs_le.mp hbound)]
    rfl
  · rw [Set.indicator_of_notMem hxmem]
    rfl

theorem topologicalClosure_iSup_lt_centralPhysicalForbidden (a : ℝ) :
    (⨆ b : Set.Iio a, centralPhysicalForbidden b.1).topologicalClosure =
      centralPhysicalForbidden a := by
  let L := (⨆ b : Set.Iio a, centralPhysicalForbidden b.1).topologicalClosure
  have hLA : L ≤ centralPhysicalForbidden a := by
    apply Submodule.topologicalClosure_minimal
    · exact iSup_le fun b => centralPhysicalForbidden_mono (le_of_lt b.2)
    · rw [← (centralPhysicalForbidden a).orthogonal_orthogonal]
      exact (centralPhysicalForbidden a)ᗮ.isClosed_orthogonal
  apply le_antisymm hLA
  apply (Submodule.orthogonal_le_orthogonal_iff (K₀ := L)
    (K₁ := centralPhysicalForbidden a)).mp
  intro f hf
  apply mem_physicalForbidden_orthogonal_of_indicator_ae_zero
  apply physical_zero_at_limit_of_mem_orthogonal_all_lt
  intro b
  apply Submodule.orthogonal_le
    (show centralPhysicalForbidden b.1 ≤ L from
      (le_iSup (fun c : Set.Iio a => centralPhysicalForbidden c.1) b).trans
        (⨆ c : Set.Iio a, centralPhysicalForbidden c.1).le_topologicalClosure)
  exact hf

theorem topologicalClosure_iSup_lt_centralFourierForbidden (a : ℝ) :
    (⨆ b : Set.Iio a, centralFourierForbidden b.1).topologicalClosure =
      centralFourierForbidden a := by
  let L := (⨆ b : Set.Iio a, centralFourierForbidden b.1).topologicalClosure
  have hLA : L ≤ centralFourierForbidden a := by
    apply Submodule.topologicalClosure_minimal
    · exact iSup_le fun b => centralFourierForbidden_mono (le_of_lt b.2)
    · rw [← (centralFourierForbidden a).orthogonal_orthogonal]
      exact (centralFourierForbidden a)ᗮ.isClosed_orthogonal
  apply le_antisymm hLA
  apply (Submodule.orthogonal_le_orthogonal_iff (K₀ := L)
    (K₁ := centralFourierForbidden a)).mp
  intro f hf
  apply mem_centralFourierForbidden_orthogonal_of_indicator_ae_zero
  apply fourier_zero_at_limit_of_mem_orthogonal_all_lt
  intro b
  apply Submodule.orthogonal_le
    (show centralFourierForbidden b.1 ≤ L from
      (le_iSup (fun c : Set.Iio a => centralFourierForbidden c.1) b).trans
        (⨆ c : Set.Iio a, centralFourierForbidden c.1).le_topologicalClosure)
  exact hf

private theorem continuousAt_centralPhysicalForbidden_projection_apply
    (a : ℝ) (g : SoninL2) :
    ContinuousAt (fun b : ℝ => (centralPhysicalForbidden b).starProjection g) a := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · change Tendsto (fun b : ℝ => (centralPhysicalForbidden b).starProjection g)
      (𝓝[<] a) (𝓝 ((centralPhysicalForbidden a).starProjection g))
    rw [← tendsto_comp_coe_Iio_atTop]
    have hmono : Monotone (fun b : Set.Iio a => centralPhysicalForbidden b.1) :=
      fun b c hbc => centralPhysicalForbidden_mono hbc
    have h := Submodule.starProjection_tendsto_closure_iSup
      (fun b : Set.Iio a => centralPhysicalForbidden b.1) hmono g
    have hproj : (⨆ b : Set.Iio a,
        centralPhysicalForbidden b.1).topologicalClosure.starProjection g =
        (centralPhysicalForbidden a).starProjection g :=
      starProjection_congr (topologicalClosure_iSup_lt_centralPhysicalForbidden a) g
    rw [hproj] at h
    exact h
  · change Tendsto (fun b : ℝ => (centralPhysicalForbidden b).starProjection g)
      (𝓝[>] a) (𝓝 ((centralPhysicalForbidden a).starProjection g))
    rw [← tendsto_comp_coe_Ioi_atBot]
    let U : (Set.Ioi a)ᵒᵈ → Submodule ℂ SoninL2 :=
      fun b => centralPhysicalForbidden b.1
    have hanti : Antitone U := by
      intro b c hbc
      exact centralPhysicalForbidden_mono hbc
    have hinf : (⨅ b, U b) = centralPhysicalForbidden a := by
      change (⨅ b : Set.Ioi a, centralPhysicalForbidden b.1) =
        centralPhysicalForbidden a
      exact iInf_centralPhysicalForbidden a
    letI : (⨅ b, U b).HasOrthogonalProjection := by
      rw [hinf]
      infer_instance
    have h := starProjection_tendsto_iInf_of_antitone U hanti g
    have hproj : (⨅ b, U b).starProjection g =
        (centralPhysicalForbidden a).starProjection g :=
      starProjection_congr hinf g
    rw [hproj] at h
    change Tendsto (fun b : (Set.Ioi a)ᵒᵈ =>
      (centralPhysicalForbidden b.1).starProjection g) atTop
      (𝓝 ((centralPhysicalForbidden a).starProjection g))
    simpa [U] using h

private theorem continuousAt_centralFourierForbidden_projection_apply
    (a : ℝ) (g : SoninL2) :
    ContinuousAt (fun b : ℝ => (centralFourierForbidden b).starProjection g) a := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · change Tendsto (fun b : ℝ => (centralFourierForbidden b).starProjection g)
      (𝓝[<] a) (𝓝 ((centralFourierForbidden a).starProjection g))
    rw [← tendsto_comp_coe_Iio_atTop]
    have hmono : Monotone (fun b : Set.Iio a => centralFourierForbidden b.1) :=
      fun b c hbc => centralFourierForbidden_mono hbc
    have h := Submodule.starProjection_tendsto_closure_iSup
      (fun b : Set.Iio a => centralFourierForbidden b.1) hmono g
    have hproj : (⨆ b : Set.Iio a,
        centralFourierForbidden b.1).topologicalClosure.starProjection g =
        (centralFourierForbidden a).starProjection g :=
      starProjection_congr (topologicalClosure_iSup_lt_centralFourierForbidden a) g
    rw [hproj] at h
    exact h
  · change Tendsto (fun b : ℝ => (centralFourierForbidden b).starProjection g)
      (𝓝[>] a) (𝓝 ((centralFourierForbidden a).starProjection g))
    rw [← tendsto_comp_coe_Ioi_atBot]
    let U : (Set.Ioi a)ᵒᵈ → Submodule ℂ SoninL2 :=
      fun b => centralFourierForbidden b.1
    have hanti : Antitone U := by
      intro b c hbc
      exact centralFourierForbidden_mono hbc
    have hinf : (⨅ b, U b) = centralFourierForbidden a := by
      change (⨅ b : Set.Ioi a, centralFourierForbidden b.1) =
        centralFourierForbidden a
      exact iInf_centralFourierForbidden a
    letI : (⨅ b, U b).HasOrthogonalProjection := by
      rw [hinf]
      infer_instance
    have h := starProjection_tendsto_iInf_of_antitone U hanti g
    have hproj : (⨅ b, U b).starProjection g =
        (centralFourierForbidden a).starProjection g :=
      starProjection_congr hinf g
    rw [hproj] at h
    change Tendsto (fun b : (Set.Ioi a)ᵒᵈ =>
      (centralFourierForbidden b.1).starProjection g) atTop
      (𝓝 ((centralFourierForbidden a).starProjection g))
    simpa [U] using h

theorem continuousAt_centralSoninProjectionCorrection_apply
    {a : ℝ} (ha : 0 < a) (g : SoninL2) :
    ContinuousAt (fun b : ℝ => centralSoninProjectionCorrection b g) a := by
  have hQ := continuousAt_centralSoninProjection_apply ha g
  have hP := continuousAt_centralPhysicalForbidden_projection_apply a g
  have hF := continuousAt_centralFourierForbidden_projection_apply a g
  have heq : (fun b : ℝ => centralSoninProjectionCorrection b g) =
      fun b : ℝ => centralSoninProjection b g -
        (g - (centralPhysicalForbidden b).starProjection g -
          (centralFourierForbidden b).starProjection g) := by
    funext b
    simp [centralSoninProjectionCorrection, centralPhysicalForbidden,
      centralFourierForbidden, centralInterval,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection, sub_apply]
  rw [heq]
  convert hQ.sub ((continuousAt_const.sub hP).sub hF) using 1 <;> rfl

private theorem hsInner_hsTruncation_left
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)
    (T S : H →L[ℂ] H) (hS : IsHilbertSchmidt S) (s : Finset ι) :
    hsInner (hsTruncation b T s) S =
      ∑ i ∈ s, inner ℂ (T (b i)) (S (b i)) := by
  have hR : IsHilbertSchmidt (hsTruncation b T s) :=
    isHilbertSchmidt_hsTruncation b T s
  rw [hsInner_eq_tsum_basis hR hS b,
    tsum_eq_sum (s := s) (fun i hi => by
      rw [hsTruncation_apply_basis b T s i, if_neg hi]
      simp)]
  exact Finset.sum_congr rfl fun i hi => by
    rw [hsTruncation_apply_basis b T s i, if_pos hi]

/-- Strong operator convergence plus convergence of Hilbert--Schmidt energies upgrades to weak
Hilbert--Schmidt convergence against the limit. -/
theorem tendsto_hsInner_of_strong_of_hsNormSq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Tn : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hTn : ∀ n, IsHilbertSchmidt (Tn n)) (hT : IsHilbertSchmidt T)
    (hstrong : ∀ x : H, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (henergy : Tendsto (fun n => hsNormSq (Tn n)) atTop (𝓝 (hsNormSq T))) :
    Tendsto (fun n => hsInner T (Tn n)) atTop (𝓝 (hsInner T T)) := by
  classical
  have hnorm : Tendsto (fun n => hsNorm (Tn n)) atTop (𝓝 (hsNorm T)) := by
    exact (Real.continuous_sqrt.tendsto (hsNormSq T)).comp henergy
  let M : ℝ := hsNorm T + 1
  have hM : 0 < M := by dsimp [M]; linarith [hsNorm_nonneg T]
  have hbound : ∀ᶠ n in atTop, hsNorm (Tn n) ≤ M := by
    apply (hnorm.eventually (Iio_mem_nhds (show hsNorm T < M by dsimp [M]; linarith))).mono
    intro n hn
    exact hn.le
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε / (4 * M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, _hsRank, hsTail⟩ := hT.exists_hasRankLE_hsNorm_sub_lt hδ
  let b := hsBasis ℂ H
  let R : H →L[ℂ] H := hsTruncation b T s
  let D : H →L[ℂ] H := T - R
  have hR : IsHilbertSchmidt R := isHilbertSchmidt_hsTruncation b T s
  have hD : IsHilbertSchmidt D := hT.sub hR
  have hDsmall : hsNorm D < δ := by simpa [D, R, b] using hsTail
  have hfinite : Tendsto (fun n => hsInner R (Tn n)) atTop (𝓝 (hsInner R T)) := by
    rw [show (fun n => hsInner R (Tn n)) =
        fun n => ∑ i ∈ s, inner ℂ (T (b i)) (Tn n (b i)) by
      funext n
      exact hsInner_hsTruncation_left b T (Tn n) (hTn n) s,
      show hsInner R T = ∑ i ∈ s, inner ℂ (T (b i)) (T (b i)) by
        exact hsInner_hsTruncation_left b T T hT s]
    exact tendsto_finsetSum s fun i _ => tendsto_const_nhds.inner (hstrong (b i))
  have hfiniteEventually : ∀ᶠ n in atTop,
      dist (hsInner R (Tn n)) (hsInner R T) < ε / 2 :=
    hfinite.eventually (Metric.ball_mem_nhds _ (by linarith))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hbound.and hfiniteEventually)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hnBound, hnFinite⟩ := hN n hn
  have hdecompN : hsInner T (Tn n) = hsInner D (Tn n) + hsInner R (Tn n) := by
    have h := hsInner_add_left hD hR (hTn n)
    have hDR : D + R = T := by dsimp [D]; abel
    rwa [hDR] at h
  have hdecompT : hsInner T T = hsInner D T + hsInner R T := by
    have h := hsInner_add_left hD hR hT
    have hDR : D + R = T := by dsimp [D]; abel
    rwa [hDR] at h
  have htailN := norm_hsInner_le hD (hTn n)
  have htailT := norm_hsInner_le hD hT
  have hTM : hsNorm T ≤ M := by dsimp [M]; linarith
  have hδM : δ * M = ε / 4 := by
    dsimp [δ]
    field_simp
  rw [dist_eq_norm] at hnFinite
  rw [hdecompN, hdecompT, dist_eq_norm]
  calc
    ‖(hsInner D (Tn n) + hsInner R (Tn n)) -
        (hsInner D T + hsInner R T)‖ =
        ‖hsInner D (Tn n) + (hsInner R (Tn n) - hsInner R T) -
          hsInner D T‖ := by congr 1; abel
    _ ≤ ‖hsInner D (Tn n)‖ + ‖hsInner R (Tn n) - hsInner R T‖ +
        ‖hsInner D T‖ := by
      calc
        ‖hsInner D (Tn n) + (hsInner R (Tn n) - hsInner R T) - hsInner D T‖
            ≤ ‖hsInner D (Tn n) + (hsInner R (Tn n) - hsInner R T)‖ +
                ‖hsInner D T‖ := norm_sub_le _ _
        _ ≤ (‖hsInner D (Tn n)‖ + ‖hsInner R (Tn n) - hsInner R T‖) +
                ‖hsInner D T‖ := by
          have h := norm_add_le (hsInner D (Tn n))
            (hsInner R (Tn n) - hsInner R T)
          linarith
    _ < ε := by
      have hN : ‖hsInner D (Tn n)‖ < ε / 4 := by
        calc
          ‖hsInner D (Tn n)‖ ≤ hsNorm D * hsNorm (Tn n) := htailN
          _ ≤ hsNorm D * M :=
            mul_le_mul_of_nonneg_left hnBound (hsNorm_nonneg D)
          _ < δ * M := mul_lt_mul_of_pos_right hDsmall hM
          _ = ε / 4 := hδM
      have hT' : ‖hsInner D T‖ < ε / 4 := by
        calc
          ‖hsInner D T‖ ≤ hsNorm D * hsNorm T := htailT
          _ ≤ hsNorm D * M := mul_le_mul_of_nonneg_left hTM (hsNorm_nonneg D)
          _ < δ * M := mul_lt_mul_of_pos_right hDsmall hM
          _ = ε / 4 := hδM
      linarith

/-- Strong convergence and convergence of Hilbert--Schmidt energies imply convergence in the
Hilbert--Schmidt norm. -/
theorem tendsto_hsNormSq_sub_of_strong_of_hsNormSq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Tn : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hTn : ∀ n, IsHilbertSchmidt (Tn n)) (hT : IsHilbertSchmidt T)
    (hstrong : ∀ x : H, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (henergy : Tendsto (fun n => hsNormSq (Tn n)) atTop (𝓝 (hsNormSq T))) :
    Tendsto (fun n => hsNormSq (Tn n - T)) atTop (𝓝 0) := by
  have hweak := tendsto_hsInner_of_strong_of_hsNormSq Tn T hTn hT hstrong henergy
  have hre : Tendsto (fun n => (hsInner T (Tn n)).re) atTop
      (𝓝 ((hsInner T T).re)) := Complex.continuous_re.continuousAt.tendsto.comp hweak
  have hre' : Tendsto (fun n => (hsInner (Tn n) T).re) atTop
      (𝓝 ((hsInner T T).re)) := by
    convert hre using 1
    · funext n
      rw [hsInner_conj_symm, Complex.conj_re]
  have htwo : Tendsto (fun n => (2 : ℝ) * (hsInner (Tn n) T).re) atTop
      (𝓝 ((2 : ℝ) * (hsInner T T).re)) := tendsto_const_nhds.mul hre'
  have hlim : Tendsto
      (fun n => hsNormSq (Tn n) - 2 * (hsInner (Tn n) T).re + hsNormSq T)
      atTop (𝓝 (hsNormSq T - 2 * (hsInner T T).re + hsNormSq T)) :=
    (henergy.sub htwo).add_const (hsNormSq T)
  have hself : (hsInner T T).re = hsNormSq T := hsInner_self_re hT
  convert hlim using 1
  · funext n
    exact hsNormSq_sub (hTn n) hT
  · rw [hself]
    ring

/-- Along any positive aperture sequence converging to a positive aperture, the projection
correction converges in Hilbert--Schmidt norm. -/
theorem tendsto_hsNormSq_centralSoninProjectionCorrection_sub_of_tendsto
    {u : ℕ → ℝ} {a : ℝ} (huPos : ∀ n, 0 < u n) (ha : 0 < a)
    (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => hsNormSq
      (centralSoninProjectionCorrection (u n) - centralSoninProjectionCorrection a))
      atTop (𝓝 0) := by
  let Tn : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => centralSoninProjectionCorrection (u n)
  let T : SoninL2 →L[ℂ] SoninL2 := centralSoninProjectionCorrection a
  have hTn : ∀ n, IsHilbertSchmidt (Tn n) := fun n =>
    centralSoninProjectionCorrection_isHilbertSchmidt (u n) (huPos n)
  have hT : IsHilbertSchmidt T :=
    centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hstrong : ∀ x : SoninL2, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)) := by
    intro x
    exact (continuousAt_centralSoninProjectionCorrection_apply ha x).tendsto.comp hu
  have hpoly : Tendsto (fun n => 8 * (u n) ^ (2 : ℕ)) atTop (𝓝 (8 * a ^ (2 : ℕ))) :=
    tendsto_const_nhds.mul (hu.pow 2)
  have henergy : Tendsto (fun n => hsNormSq (Tn n)) atTop (𝓝 (hsNormSq T)) := by
    have hfun : (fun n => hsNormSq (Tn n)) = fun n => 8 * (u n) ^ (2 : ℕ) := by
      funext n
      exact hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq
        (u n) (huPos n)
    have hval : hsNormSq T = 8 * a ^ (2 : ℕ) :=
      hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq a ha
    rw [hfun, hval]
    exact hpoly
  exact tendsto_hsNormSq_sub_of_strong_of_hsNormSq Tn T hTn hT hstrong henergy

/-- The projection correction is Hilbert--Schmidt continuous at every positive aperture. -/
theorem tendsto_hsNormSq_centralSoninProjectionCorrection_sub
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun b : ℝ => hsNormSq
      (centralSoninProjectionCorrection b - centralSoninProjectionCorrection a))
      (𝓝 a) (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have huEventually : ∀ᶠ n in atTop, 0 < u n :=
    hu.eventually (Ioi_mem_nhds ha)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 huEventually
  have huTail : Tendsto (fun n => u (n + N)) atTop (𝓝 a) :=
    (Filter.tendsto_add_atTop_iff_nat N).2 hu
  have htail :=
    tendsto_hsNormSq_centralSoninProjectionCorrection_sub_of_tendsto
      (u := fun n => u (n + N)) (fun n => hN (n + N) (Nat.le_add_left N n)) ha huTail
  apply (Filter.tendsto_add_atTop_iff_nat N).1
  simpa [Function.comp_def] using htail

/-- Uniformly bounded strong convergence to zero becomes Hilbert--Schmidt norm convergence after
right multiplication by a fixed Hilbert--Schmidt operator. -/
theorem tendsto_hsNormSq_comp_left_zero_of_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (An : ℕ → H →L[ℂ] H) (K : H →L[ℂ] H)
    (hK : IsHilbertSchmidt K)
    (hstrong : ∀ x : H, Tendsto (fun n => An n x) atTop (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖An n‖ ≤ M) :
    Tendsto (fun n => hsNormSq (An n * K)) atTop (𝓝 0) := by
  classical
  have hnorm : Tendsto (fun n => hsNorm (An n * K)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    let δ : ℝ := ε / (2 * (M + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨s, _hsRank, hsTail⟩ := hK.exists_hasRankLE_hsNorm_sub_lt hδ
    let b := hsBasis ℂ H
    let R : H →L[ℂ] H := hsTruncation b K s
    let D : H →L[ℂ] H := K - R
    have hR : IsHilbertSchmidt R := isHilbertSchmidt_hsTruncation b K s
    have hD : IsHilbertSchmidt D := hK.sub hR
    have hDsmall : hsNorm D < δ := by simpa [D, R, b] using hsTail
    have hfiniteSq : Tendsto (fun n => hsNormSq (An n * R)) atTop (𝓝 0) := by
      have heq : (fun n => hsNormSq (An n * R)) =
          fun n => ∑ i ∈ s, ‖An n (K (b i))‖ ^ (2 : ℕ) := by
        funext n
        have hAR : IsHilbertSchmidt (An n * R) := hR.comp_left (An n)
        rw [hsNormSq_eq hAR b,
          tsum_eq_sum (s := s) (fun i hi => by
            change ‖An n (R (b i))‖ ^ (2 : ℕ) = 0
            rw [hsTruncation_apply_basis b K s i, if_neg hi]
            simp)]
        exact Finset.sum_congr rfl fun i hi => by
          change ‖An n (R (b i))‖ ^ (2 : ℕ) = ‖An n (K (b i))‖ ^ (2 : ℕ)
          rw [hsTruncation_apply_basis b K s i, if_pos hi]
      rw [heq]
      simpa using tendsto_finsetSum s fun i _ =>
        ((tendsto_norm.comp (hstrong (K (b i)))).pow 2)
    have hfinite : Tendsto (fun n => hsNorm (An n * R)) atTop (𝓝 0) := by
      have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hfiniteSq
      simpa [hsNorm, Function.comp_def] using hsqrt
    have hfiniteEventually : ∀ᶠ n in atTop, hsNorm (An n * R) < ε / 2 :=
      hfinite.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hfiniteEventually
    refine ⟨N, fun n hn => ?_⟩
    have hAK : IsHilbertSchmidt (An n * K) := hK.comp_left (An n)
    have hAR : IsHilbertSchmidt (An n * R) := hR.comp_left (An n)
    have hAD : IsHilbertSchmidt (An n * D) := hD.comp_left (An n)
    have hsplit : An n * K = An n * R + An n * D := by
      dsimp [D]
      noncomm_ring
    have htail : hsNorm (An n * D) < ε / 2 := by
      calc
        hsNorm (An n * D) ≤ ‖An n‖ * hsNorm D := hD.hsNorm_comp_left_le (An n)
        _ ≤ (M + 1) * hsNorm D :=
          mul_le_mul_of_nonneg_right (by linarith [hbound n]) (hsNorm_nonneg D)
        _ < (M + 1) * δ :=
          mul_lt_mul_of_pos_left hDsmall (by linarith : 0 < M + 1)
        _ = ε / 2 := by
          dsimp [δ]
          field_simp
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (hsNorm_nonneg _), hsplit]
    exact (hsNorm_add_le hAR hAD).trans_lt (by linarith [hN n hn])
  have hsq : (fun n => hsNormSq (An n * K)) =
      fun n => hsNorm (An n * K) ^ (2 : ℕ) := by
    funext n
    rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg _)]
  rw [hsq]
  simpa using hnorm.pow 2

/-- Adjoint-strong convergence to zero becomes Hilbert--Schmidt norm convergence after left
multiplication by a fixed Hilbert--Schmidt operator. -/
theorem tendsto_hsNormSq_comp_right_zero_of_adjoint_strong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Bn : ℕ → H →L[ℂ] H) (K : H →L[ℂ] H)
    (hK : IsHilbertSchmidt K)
    (hstrong : ∀ x : H,
      Tendsto (fun n => ContinuousLinearMap.adjoint (Bn n) x) atTop (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖Bn n‖ ≤ M) :
    Tendsto (fun n => hsNormSq (K * Bn n)) atTop (𝓝 0) := by
  let An : ℕ → H →L[ℂ] H := fun n => ContinuousLinearMap.adjoint (Bn n)
  let K' : H →L[ℂ] H := ContinuousLinearMap.adjoint K
  have hK' : IsHilbertSchmidt K' := hK.adjoint
  have hbound' : ∀ n, ‖An n‖ ≤ M := by
    intro n
    simpa [An] using hbound n
  have hleft := tendsto_hsNormSq_comp_left_zero_of_strong
    An K' hK' hstrong hM hbound'
  convert hleft using 1
  funext n
  have hcomp : IsHilbertSchmidt (K * Bn n) := hK.comp_right (Bn n)
  calc
    hsNormSq (K * Bn n) = hsNormSq (ContinuousLinearMap.adjoint (K * Bn n)) :=
      hcomp.hsNormSq_adjoint.symm
    _ = hsNormSq (An n * K') := by
      congr 1
      change ContinuousLinearMap.adjoint (K ∘L Bn n) =
        ContinuousLinearMap.adjoint (Bn n) ∘L ContinuousLinearMap.adjoint K
      exact ContinuousLinearMap.adjoint_comp K (Bn n)

/-- Two Hilbert--Schmidt families vanishing in Hilbert--Schmidt norm have a vanishing sum. -/
theorem tendsto_hsNormSq_add_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (An Bn : ℕ → H →L[ℂ] H)
    (hAn : ∀ n, IsHilbertSchmidt (An n)) (hBn : ∀ n, IsHilbertSchmidt (Bn n))
    (hA : Tendsto (fun n => hsNormSq (An n)) atTop (𝓝 0))
    (hB : Tendsto (fun n => hsNormSq (Bn n)) atTop (𝓝 0)) :
    Tendsto (fun n => hsNormSq (An n + Bn n)) atTop (𝓝 0) := by
  have hnormA : Tendsto (fun n => hsNorm (An n)) atTop (𝓝 0) := by
    simpa [hsNorm, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hA
  have hnormB : Tendsto (fun n => hsNorm (Bn n)) atTop (𝓝 0) := by
    simpa [hsNorm, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hB
  have hnorm : Tendsto (fun n => hsNorm (An n + Bn n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => hsNorm_nonneg _) (fun n => hsNorm_add_le (hAn n) (hBn n))
      (by simpa using hnormA.add hnormB)
  have hsq : (fun n => hsNormSq (An n + Bn n)) =
      fun n => hsNorm (An n + Bn n) ^ (2 : ℕ) := by
    funext n
    rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg _)]
  rw [hsq]
  simpa using hnorm.pow 2

/-- Two Hilbert--Schmidt families vanishing in Hilbert--Schmidt norm have a vanishing
difference. -/
theorem tendsto_hsNormSq_sub_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (An Bn : ℕ → H →L[ℂ] H)
    (hAn : ∀ n, IsHilbertSchmidt (An n)) (hBn : ∀ n, IsHilbertSchmidt (Bn n))
    (hA : Tendsto (fun n => hsNormSq (An n)) atTop (𝓝 0))
    (hB : Tendsto (fun n => hsNormSq (Bn n)) atTop (𝓝 0)) :
    Tendsto (fun n => hsNormSq (An n - Bn n)) atTop (𝓝 0) := by
  have hneg : Tendsto (fun n => hsNormSq (-(Bn n))) atTop (𝓝 0) := by
    convert hB using 1
    funext n
    exact hsNormSq_neg_eq_self (Bn n)
  simpa [sub_eq_add_neg] using tendsto_hsNormSq_add_zero An (fun n => -(Bn n))
    hAn (fun n => (hBn n).neg) hA hneg

/-- The formal physical/Fourier complement is self-adjoint at every aperture. -/
theorem centralSoninFormalComplement_isSelfAdjoint (a : ℝ) :
    IsSelfAdjoint (centralSoninFormalComplement a) := by
  rw [centralSoninFormalComplement,
    indicatorCutoff_eq_physicalForbidden_starProjection,
    fourierCutoff_eq_fourierForbidden_starProjection]
  exact ((IsSelfAdjoint.one _).sub (isSelfAdjoint_starProjection _)).sub
    (isSelfAdjoint_starProjection _)

/-- The formal physical/Fourier complement is strongly continuous in aperture. -/
theorem continuousAt_centralSoninFormalComplement_apply
    (a : ℝ) (g : SoninL2) :
    ContinuousAt (fun b : ℝ => centralSoninFormalComplement b g) a := by
  have hP := continuousAt_centralPhysicalForbidden_projection_apply a g
  have hF := continuousAt_centralFourierForbidden_projection_apply a g
  have heq : (fun b : ℝ => centralSoninFormalComplement b g) =
      fun b : ℝ => g - (centralPhysicalForbidden b).starProjection g -
        (centralFourierForbidden b).starProjection g := by
    funext b
    simp [centralSoninFormalComplement, centralPhysicalForbidden,
      centralFourierForbidden, centralInterval,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection, sub_apply]
  rw [heq]
  exact (continuousAt_const.sub hP).sub hF

/-- A uniformly operator-norm bounded left factor preserves vanishing Hilbert--Schmidt energy. -/
theorem tendsto_hsNormSq_comp_left_zero_of_hsNormSq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (An Kn : ℕ → H →L[ℂ] H) (hKn : ∀ n, IsHilbertSchmidt (Kn n))
    (hK : Tendsto (fun n => hsNormSq (Kn n)) atTop (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖An n‖ ≤ M) :
    Tendsto (fun n => hsNormSq (An n * Kn n)) atTop (𝓝 0) := by
  refine squeeze_zero (g := fun n => M ^ (2 : ℕ) * hsNormSq (Kn n))
    (fun n => hsNormSq_nonneg _) (fun n => ?_)
    (by simpa using (tendsto_const_nhds.mul hK :
      Tendsto (fun n => M ^ (2 : ℕ) * hsNormSq (Kn n)) atTop (𝓝 (M ^ (2 : ℕ) * 0))))
  calc
    hsNormSq (An n * Kn n) ≤ ‖An n‖ ^ (2 : ℕ) * hsNormSq (Kn n) :=
      hsNormSq_comp_left_le (hKn n) (An n)
    _ ≤ M ^ (2 : ℕ) * hsNormSq (Kn n) :=
      mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hM).2 (hbound n)) (hsNormSq_nonneg _)

/-- A uniformly operator-norm bounded right factor preserves vanishing Hilbert--Schmidt energy. -/
theorem tendsto_hsNormSq_comp_right_zero_of_hsNormSq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Kn Bn : ℕ → H →L[ℂ] H) (hKn : ∀ n, IsHilbertSchmidt (Kn n))
    (hK : Tendsto (fun n => hsNormSq (Kn n)) atTop (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖Bn n‖ ≤ M) :
    Tendsto (fun n => hsNormSq (Kn n * Bn n)) atTop (𝓝 0) := by
  refine squeeze_zero (g := fun n => M ^ (2 : ℕ) * hsNormSq (Kn n))
    (fun n => hsNormSq_nonneg _) (fun n => ?_)
    (by simpa using (tendsto_const_nhds.mul hK :
      Tendsto (fun n => M ^ (2 : ℕ) * hsNormSq (Kn n)) atTop (𝓝 (M ^ (2 : ℕ) * 0))))
  calc
    hsNormSq (Kn n * Bn n) ≤ ‖Bn n‖ ^ (2 : ℕ) * hsNormSq (Kn n) :=
      hsNormSq_comp_right_le (hKn n) (Bn n)
    _ ≤ M ^ (2 : ℕ) * hsNormSq (Kn n) :=
      mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hM).2 (hbound n)) (hsNormSq_nonneg _)

set_option maxHeartbeats 2000000 in
/-- Along every positive aperture sequence, each fixed prime-scale Sonin residual is continuous
in Hilbert--Schmidt norm. -/
theorem tendsto_hsNormSq_centralSoninDilationCornerResidual_sub_of_tendsto
    {u : ℕ → ℝ} {a p : ℝ} (huPos : ∀ n, 0 < u n) (ha : 0 < a) (hp : 1 < p)
    (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => hsNormSq
      (centralSoninDilationCornerResidual (u n) p hp -
        centralSoninDilationCornerResidual a p hp)) atTop (𝓝 0) := by
  let Qn : ℕ → SoninL2 →L[ℂ] SoninL2 := fun n => centralSoninProjection (u n)
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let Cn : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => centralSoninProjectionCorrection (u n)
  let C : SoninL2 →L[ℂ] SoninL2 := centralSoninProjectionCorrection a
  let Q₀n : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => centralSoninFormalComplement (u n)
  let Q₀ : SoninL2 →L[ℂ] SoninL2 := centralSoninFormalComplement a
  let D : SoninL2 →L[ℂ] SoninL2 := dilationSum p hp
  have hC : IsHilbertSchmidt C := by
    simpa [C] using centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hCn : ∀ n, IsHilbertSchmidt (Cn n) := fun n => by
    simpa [Cn] using centralSoninProjectionCorrection_isHilbertSchmidt (u n) (huPos n)
  have hCdiff : ∀ n, IsHilbertSchmidt (Cn n - C) := fun n => (hCn n).sub hC
  have hCdiffLim : Tendsto (fun n => hsNormSq (Cn n - C)) atTop (𝓝 0) := by
    simpa [Cn, C] using
      tendsto_hsNormSq_centralSoninProjectionCorrection_sub_of_tendsto huPos ha hu
  have hD : ‖D‖ ≤ 2 := by
    simpa [D] using norm_dilationSum_le_two p hp
  have hQstrong : ∀ x : SoninL2,
      Tendsto (fun n => ((1 - Qn n) - (1 - Q)) x) atTop (𝓝 0) := by
    intro x
    have hq : Tendsto (fun n => Qn n x) atTop (𝓝 (Q x)) := by
      simpa [Qn, Q, Function.comp_def] using
        (continuousAt_centralSoninProjection_apply ha x).tendsto.comp hu
    have hdiff : Tendsto (fun n => Q x - Qn n x) atTop (𝓝 (Q x - Q x)) :=
      tendsto_const_nhds.sub hq
    simpa [sub_apply] using hdiff
  have hQdiffBound : ∀ n, ‖(1 - Qn n) - (1 - Q)‖ ≤ 2 := by
    intro n
    calc
      ‖(1 - Qn n) - (1 - Q)‖ ≤ ‖1 - Qn n‖ + ‖1 - Q‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
        (by simpa [Qn] using norm_one_sub_centralSoninProjection_le_one (u n))
        (by simpa [Q] using norm_one_sub_centralSoninProjection_le_one a)
      _ = 2 := by norm_num
  have hQ₀strong : ∀ x : SoninL2,
      Tendsto (fun n => (Q₀n n - Q₀) x) atTop (𝓝 0) := by
    intro x
    have hq₀ : Tendsto (fun n => Q₀n n x) atTop (𝓝 (Q₀ x)) := by
      simpa [Q₀n, Q₀, Function.comp_def] using
        (continuousAt_centralSoninFormalComplement_apply a x).tendsto.comp hu
    have hdiff : Tendsto (fun n => Q₀n n x - Q₀ x) atTop (𝓝 (Q₀ x - Q₀ x)) :=
      hq₀.sub tendsto_const_nhds
    simpa [sub_apply] using hdiff
  have hQ₀adj (b : ℝ) :
      ContinuousLinearMap.adjoint (centralSoninFormalComplement b) =
        centralSoninFormalComplement b := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (centralSoninFormalComplement_isSelfAdjoint b).star_eq
  have hQ₀adjStrong : ∀ x : SoninL2,
      Tendsto (fun n => ContinuousLinearMap.adjoint (Q₀n n - Q₀) x)
        atTop (𝓝 0) := by
    intro x
    convert hQ₀strong x using 1
    funext n
    rw [map_sub, show ContinuousLinearMap.adjoint (Q₀n n) = Q₀n n by
      simpa [Q₀n] using hQ₀adj (u n),
      show ContinuousLinearMap.adjoint Q₀ = Q₀ by simpa [Q₀] using hQ₀adj a]
  have hQ₀diffBound : ∀ n, ‖Q₀n n - Q₀‖ ≤ 2 := by
    intro n
    calc
      ‖Q₀n n - Q₀‖ ≤ ‖Q₀n n‖ + ‖Q₀‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add
        (by simpa [Q₀n] using norm_centralSoninFormalComplement_le_one (u n))
        (by simpa [Q₀] using norm_centralSoninFormalComplement_le_one a)
      _ = 2 := by norm_num
  let X₁ : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => ((1 - Qn n) * D) * (Cn n - C)
  let X₂ : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => ((1 - Qn n) - (1 - Q)) * (D * C)
  let Y₁ : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => (Cn n - C) * (D * Q₀n n)
  let Y₂ : ℕ → SoninL2 →L[ℂ] SoninL2 :=
    fun n => (C * D) * (Q₀n n - Q₀)
  have hX₁ : ∀ n, IsHilbertSchmidt (X₁ n) := fun n => by
    exact (hCdiff n).comp_left ((1 - Qn n) * D)
  have hX₂ : ∀ n, IsHilbertSchmidt (X₂ n) := fun n => by
    exact (hC.comp_left D).comp_left ((1 - Qn n) - (1 - Q))
  have hY₁ : ∀ n, IsHilbertSchmidt (Y₁ n) := fun n => by
    exact (hCdiff n).comp_right (D * Q₀n n)
  have hY₂ : ∀ n, IsHilbertSchmidt (Y₂ n) := fun n => by
    exact (hC.comp_right D).comp_right (Q₀n n - Q₀)
  have hleftBound : ∀ n, ‖(1 - Qn n) * D‖ ≤ 2 := by
    intro n
    calc
      ‖(1 - Qn n) * D‖ ≤ ‖1 - Qn n‖ * ‖D‖ := norm_mul_le _ _
      _ ≤ 1 * 2 := mul_le_mul
        (by simpa [Qn] using norm_one_sub_centralSoninProjection_le_one (u n)) hD
        (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hrightBound : ∀ n, ‖D * Q₀n n‖ ≤ 2 := by
    intro n
    calc
      ‖D * Q₀n n‖ ≤ ‖D‖ * ‖Q₀n n‖ := norm_mul_le _ _
      _ ≤ 2 * 1 := mul_le_mul hD
        (by simpa [Q₀n] using norm_centralSoninFormalComplement_le_one (u n))
        (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hX₁lim : Tendsto (fun n => hsNormSq (X₁ n)) atTop (𝓝 0) := by
    simpa [X₁] using tendsto_hsNormSq_comp_left_zero_of_hsNormSq
      (fun n => (1 - Qn n) * D) (fun n => Cn n - C) hCdiff hCdiffLim
      (by norm_num : (0 : ℝ) ≤ 2) hleftBound
  have hX₂lim : Tendsto (fun n => hsNormSq (X₂ n)) atTop (𝓝 0) := by
    simpa [X₂] using tendsto_hsNormSq_comp_left_zero_of_strong
      (fun n => (1 - Qn n) - (1 - Q)) (D * C) (hC.comp_left D)
      hQstrong (by norm_num : (0 : ℝ) ≤ 2) hQdiffBound
  have hY₁lim : Tendsto (fun n => hsNormSq (Y₁ n)) atTop (𝓝 0) := by
    simpa [Y₁] using tendsto_hsNormSq_comp_right_zero_of_hsNormSq
      (fun n => Cn n - C) (fun n => D * Q₀n n) hCdiff hCdiffLim
      (by norm_num : (0 : ℝ) ≤ 2) hrightBound
  have hY₂lim : Tendsto (fun n => hsNormSq (Y₂ n)) atTop (𝓝 0) := by
    simpa [Y₂] using tendsto_hsNormSq_comp_right_zero_of_adjoint_strong
      (fun n => Q₀n n - Q₀) (C * D) (hC.comp_right D)
      hQ₀adjStrong (by norm_num : (0 : ℝ) ≤ 2) hQ₀diffBound
  have hXlim : Tendsto (fun n => hsNormSq (X₁ n + X₂ n)) atTop (𝓝 0) :=
    tendsto_hsNormSq_add_zero X₁ X₂ hX₁ hX₂ hX₁lim hX₂lim
  have hYlim : Tendsto (fun n => hsNormSq (Y₁ n + Y₂ n)) atTop (𝓝 0) :=
    tendsto_hsNormSq_add_zero Y₁ Y₂ hY₁ hY₂ hY₁lim hY₂lim
  have hfinal := tendsto_hsNormSq_sub_zero
    (fun n => X₁ n + X₂ n) (fun n => Y₁ n + Y₂ n)
    (fun n => (hX₁ n).add (hX₂ n)) (fun n => (hY₁ n).add (hY₂ n)) hXlim hYlim
  convert hfinal using 1
  funext n
  rw [centralSoninDilationCornerResidual_eq_correction_factorization (u n) p hp,
    centralSoninDilationCornerResidual_eq_correction_factorization a p hp]
  dsimp [X₁, X₂, Y₁, Y₂, Qn, Q, Cn, C, Q₀n, Q₀, D]
  noncomm_ring

/-- Every fixed prime-scale Sonin residual is Hilbert--Schmidt continuous at each positive
aperture. -/
theorem tendsto_hsNormSq_centralSoninDilationCornerResidual_sub
    {a p : ℝ} (ha : 0 < a) (hp : 1 < p) :
    Tendsto (fun b : ℝ => hsNormSq
      (centralSoninDilationCornerResidual b p hp -
        centralSoninDilationCornerResidual a p hp)) (𝓝 a) (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have huEventually : ∀ᶠ n in atTop, 0 < u n := hu.eventually (Ioi_mem_nhds ha)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 huEventually
  have huTail : Tendsto (fun n => u (n + N)) atTop (𝓝 a) :=
    (Filter.tendsto_add_atTop_iff_nat N).2 hu
  have htail := tendsto_hsNormSq_centralSoninDilationCornerResidual_sub_of_tendsto
    (u := fun n => u (n + N)) (p := p)
    (fun n => hN (n + N) (Nat.le_add_left N n)) ha hp huTail
  apply (Filter.tendsto_add_atTop_iff_nat N).1
  simpa [Function.comp_def] using htail

/-- Every logarithmically weighted prime-power residual block is Hilbert--Schmidt continuous at
each positive aperture. -/
theorem tendsto_hsNormSq_centralSoninWeightedPrimePowerResidual_sub
    {a : ℝ} (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    Tendsto (fun b : ℝ => hsNormSq
      (centralSoninWeightedPrimePowerResidual b pk -
        centralSoninWeightedPrimePowerResidual a pk)) (𝓝 a) (𝓝 0) := by
  let c : ℂ := soninLogPrimePowerCoefficient pk
  let R : ℝ → SoninL2 →L[ℂ] SoninL2 := fun b =>
    centralSoninPrimePowerResidual b pk
  have hbase := tendsto_hsNormSq_centralSoninDilationCornerResidual_sub ha
    (one_lt_soninPrimePowerScale pk)
  have hHS : IsHilbertSchmidt (R a) := by
    simpa [R, centralSoninPrimePowerResidual] using
      centralSoninDilationCornerResidual_isHilbertSchmidt a
        (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)
  have hevent : ∀ᶠ b in 𝓝 a, IsHilbertSchmidt (R b - R a) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact (centralSoninDilationCornerResidual_isHilbertSchmidt b
      (soninPrimePowerScale pk) hb (one_lt_soninPrimePowerScale pk)).sub hHS
  have heq : (fun b : ℝ => hsNormSq
      (centralSoninWeightedPrimePowerResidual b pk -
        centralSoninWeightedPrimePowerResidual a pk)) =ᶠ[𝓝 a]
      (fun b : ℝ => ‖c‖ ^ (2 : ℕ) * hsNormSq (R b - R a)) :=
    hevent.mono fun b hb => by
      change hsNormSq (c • R b - c • R a) = ‖c‖ ^ (2 : ℕ) * hsNormSq (R b - R a)
      rw [← smul_sub, hsNormSq_smul_eq hb]
  have hmul : Tendsto (fun b : ℝ => ‖c‖ ^ (2 : ℕ) * hsNormSq (R b - R a))
      (𝓝 a) (𝓝 (‖c‖ ^ (2 : ℕ) * 0)) := by
    simpa [R, centralSoninPrimePowerResidual] using tendsto_const_nhds.mul hbase
  exact (show Tendsto (fun b : ℝ => ‖c‖ ^ (2 : ℕ) * hsNormSq (R b - R a))
    (𝓝 a) (𝓝 0) by simpa using hmul).congr' heq.symm

end RHTower
