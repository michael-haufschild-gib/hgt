import GaloisForLFunctions.RHTower.RoutePCriticalBoundaryOrdinateDiagonalization
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Route P: critical collision-scale kernel

P-G171 diagonalizes fixed distinct ordinates at the critical Euler boundary. Height-local packets,
however, may contain gaps that close with the boundary clock. This module computes that missing
mesoscopic regime exactly. If `delta - gamma = kappa * (sigma - 1)`, the zeta pole retains the
complex Cauchy frequency `R * (a + b) + i * kappa`; the cubic tangent retains its four-term third-
order polarization. Thus fixed-gap dephasing is pointwise, not uniform over growing height packets.
The positive survivor is an exact finite collision-packet Gram law that a completed trace estimate
must control without a zero-spacing hypothesis.
-/

open Complex Filter Set Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

theorem tendsto_sub_one_cube_mul_iteratedDeriv_two_riemannZeta :
    Tendsto
      (fun s : ℂ => (s - 1) ^ 3 * iteratedDeriv 2 riemannZeta s)
      (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) (nhds 2) := by
  have h := GaloisForLFunctions.iteratedDeriv_residue_of_factor_add
    riemannZeta zetaResidueUnit (-1) ({(1 : ℂ)}ᶜ)
    (fun s hs => by
      have hs1 : s ≠ 1 := by simpa using hs
      simpa [sub_eq_add_neg] using sub_ne_zero.mpr hs1)
    (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simpa only [neg_neg] using hs)
    (fun s _ n => (analyticAt_zetaResidueUnit s).contDiffAt)
    (fun n => by simpa using zetaResidueUnit_analyticAt.contDiffAt (n := n))
    (fun s hs => by
      have hs1 : s ≠ 1 := by simpa using hs
      have hunit : zetaResidueUnit =ᶠ[nhds s]
          fun t => (t - 1) * riemannZeta t :=
        zetaResidueUnit_eventuallyEq hs1
      filter_upwards [hunit, isOpen_compl_singleton.mem_nhds hs] with t ht ht1'
      have ht1 : t ≠ 1 := by simpa using ht1'
      simp only [Pi.mul_apply]
      rw [ht]
      rw [show t + (-1 : ℂ) = t - 1 by ring]
      field_simp [sub_ne_zero.mpr ht1])
    2
  simpa [sub_eq_add_neg] using h

/-- Moving distinct ordinate on the critical collision scale. -/
def routePCollisionOrdinate (gamma kappa sigma : ℝ) : ℝ :=
  gamma + kappa * (sigma - 1)

/-- Complex mesoscopic frequency retained by a collision-scale ordinate pair. -/
def routePCollisionPairFrequency (R a b kappa : ℝ) : ℂ :=
  ((R * (a + b) : ℝ) : ℂ) + (kappa : ℂ) * I

theorem routePProjectiveOrdinatePairParameter_collision
    (sigma R a gamma b kappa : ℝ) :
    routePProjectiveOrdinatePairParameter sigma R a gamma b
        (routePCollisionOrdinate gamma kappa sigma) =
      1 + ((sigma - 1 : ℝ) : ℂ) *
        routePCollisionPairFrequency R a b kappa := by
  unfold routePCollisionOrdinate routePCollisionPairFrequency
    routePProjectiveOrdinatePairParameter
  push_cast
  ring

theorem routePCollisionPairFrequency_ne_zero
    {R a b kappa : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    routePCollisionPairFrequency R a b kappa ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [routePCollisionPairFrequency] at hre
  rcases hre with hR0 | hab0
  · linarith
  · nlinarith [add_pos ha hb]

theorem tendsto_routePProjectiveOrdinateZetaOverlap_collision
    {R a b gamma kappa : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinateZetaOverlap R a gamma b
          (routePCollisionOrdinate gamma kappa sigma) sigma)
      (nhdsWithin 1 (Ioi 1))
      (nhds ((R : ℂ) / routePCollisionPairFrequency R a b kappa)) := by
  let q := routePCollisionPairFrequency R a b kappa
  have hq : q ≠ 0 := routePCollisionPairFrequency_ne_zero hR ha hb
  let s : ℝ → ℂ := fun sigma => 1 + ((sigma - 1 : ℝ) : ℂ) * q
  have hs : Tendsto s (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) := by
    have hc : ContinuousAt s 1 := by
      unfold s
      fun_prop
    simpa [s] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsig : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hGs : Tendsto (fun sigma : ℝ => zetaResidueUnit (s sigma))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    simpa only [Function.comp_def, zetaResidueUnit_one] using
      zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hs
  have hGsig : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    simpa only [Function.comp_def, zetaResidueUnit_one] using
      zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsig
  have hratio := hGs.div hGsig (by norm_num : (1 : ℂ) ≠ 0)
  have hscaled := hratio.const_mul ((R : ℂ) / q)
  change Tendsto
    (fun sigma : ℝ => ((R : ℂ) / q) *
      (zetaResidueUnit (s sigma) / zetaResidueUnit (sigma : ℂ)))
    (nhdsWithin 1 (Ioi 1))
    (nhds (((R : ℂ) / q) * ((1 : ℂ) / 1))) at hscaled
  have hscaled' : Tendsto
      (fun sigma : ℝ => ((R : ℂ) / q) *
        (zetaResidueUnit (s sigma) / zetaResidueUnit (sigma : ℂ)))
      (nhdsWithin 1 (Ioi 1)) (nhds ((R : ℂ) / q)) := by
    simpa only [div_one, mul_one] using hscaled
  apply hscaled'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  have hsigma1 : sigma ≠ 1 := hsigma.ne'
  have hsigma1C : (sigma : ℂ) ≠ 1 := by exact_mod_cast hsigma1
  have hsq : s sigma ≠ 1 := by
    intro h
    have hzero : (((sigma - 1 : ℝ) : ℂ) * q) = 0 := by
      dsimp only [s] at h
      linear_combination h
    exact mul_ne_zero (by exact_mod_cast sub_ne_zero.mpr hsigma1) hq hzero
  symm
  rw [routePProjectiveOrdinateZetaOverlap,
    routePProjectiveOrdinatePairParameter_collision]
  change (R : ℂ) * (riemannZeta (s sigma) / riemannZeta (sigma : ℂ)) = _
  rw [show zetaResidueUnit (s sigma) = (s sigma - 1) * riemannZeta (s sigma) by
      simp [zetaResidueUnit, Function.update_of_ne hsq],
    show zetaResidueUnit (sigma : ℂ) = ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) by
      simp [zetaResidueUnit, Function.update_of_ne hsigma1C]]
  have hsubC : ((sigma : ℂ) - 1) ≠ 0 := sub_ne_zero.mpr hsigma1C
  have hsSub : s sigma - 1 = ((sigma : ℂ) - 1) * q := by
    dsimp only [s]
    push_cast
    ring
  rw [hsSub]
  field_simp [hsubC, hq]

/-- Mesoscopic cubic kernel retained when ordinate gaps close at the critical-clock scale. -/
def routePCollisionCubicKernel (R a b kappa : ℝ) : ℂ :=
  2 * (R : ℂ) ^ 3 /
      routePCollisionPairFrequency R a b kappa ^ 3 -
    2 * (R : ℂ) ^ 3 /
      routePCollisionPairFrequency R a (2 * b) kappa ^ 3 -
    2 * (R : ℂ) ^ 3 /
      routePCollisionPairFrequency R (2 * a) b kappa ^ 3 +
    2 * (R : ℂ) ^ 3 /
      routePCollisionPairFrequency R (2 * a) (2 * b) kappa ^ 3

theorem tendsto_routePProjectiveOrdinateLogMomentGramTerm_collision
    {R a b gamma kappa : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinateLogMomentGramTerm R a gamma b
          (routePCollisionOrdinate gamma kappa sigma) sigma)
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 * (R : ℂ) ^ 3 /
        routePCollisionPairFrequency R a b kappa ^ 3)) := by
  let q := routePCollisionPairFrequency R a b kappa
  have hq : q ≠ 0 := routePCollisionPairFrequency_ne_zero hR ha hb
  let s : ℝ → ℂ := fun sigma => 1 + ((sigma - 1 : ℝ) : ℂ) * q
  have hs : Tendsto s (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) := by
    have hc : ContinuousAt s 1 := by
      unfold s
      fun_prop
    simpa [s] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsmem : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
      s sigma ∈ Set.compl ({(1 : ℂ)} : Set ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    change 1 < sigma at hsigma
    have hsigma1 : sigma ≠ 1 := hsigma.ne'
    have hsub : ((sigma - 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hsigma1
    change s sigma ≠ 1
    intro heq
    have hzero : ((sigma - 1 : ℝ) : ℂ) * q = 0 := by
      dsimp only [s] at heq
      linear_combination heq
    exact mul_ne_zero hsub hq hzero
  have hsWithin : Tendsto s (nhdsWithin 1 (Ioi 1))
      (nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs, hsmem⟩
  have hjet :=
    tendsto_sub_one_cube_mul_iteratedDeriv_two_riemannZeta.comp hsWithin
  have hsig : Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hGsig : Tendsto (fun sigma : ℝ => zetaResidueUnit (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    simpa only [Function.comp_def, zetaResidueUnit_one] using
      zetaResidueUnit_analyticAt.continuousAt.tendsto.comp hsig
  have hratio := hjet.div hGsig (by norm_num : (1 : ℂ) ≠ 0)
  change Tendsto
    (fun sigma : ℝ =>
      ((s sigma - 1) ^ 3 * iteratedDeriv 2 riemannZeta (s sigma)) /
        zetaResidueUnit (sigma : ℂ))
    (nhdsWithin 1 (Ioi 1)) (nhds ((2 : ℂ) / 1)) at hratio
  have hscaled := hratio.const_mul ((R : ℂ) ^ 3 / q ^ 3)
  have hscaled' : Tendsto
      (fun sigma : ℝ => ((R : ℂ) ^ 3 / q ^ 3) *
        (((s sigma - 1) ^ 3 * iteratedDeriv 2 riemannZeta (s sigma)) /
          zetaResidueUnit (sigma : ℂ)))
      (nhdsWithin 1 (Ioi 1))
      (nhds (2 * (R : ℂ) ^ 3 / q ^ 3)) := by
    convert hscaled using 1
    all_goals ring
  apply hscaled'.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  have hsigma1 : sigma ≠ 1 := hsigma.ne'
  have hsigma1C : (sigma : ℂ) ≠ 1 := by exact_mod_cast hsigma1
  have hsubC : ((sigma : ℂ) - 1) ≠ 0 := sub_ne_zero.mpr hsigma1C
  symm
  rw [routePProjectiveOrdinateLogMomentGramTerm,
    routePProjectiveOrdinatePairParameter_collision]
  change
    (((R * (R * (sigma - 1)) ^ 2 : ℝ) : ℂ) *
        (iteratedDeriv 2 riemannZeta (s sigma) /
          riemannZeta (sigma : ℂ))) = _
  rw [show zetaResidueUnit (sigma : ℂ) =
      ((sigma : ℂ) - 1) * riemannZeta (sigma : ℂ) by
    simp [zetaResidueUnit, Function.update_of_ne hsigma1C]]
  have hsSub : s sigma - 1 = ((sigma : ℂ) - 1) * q := by
    dsimp only [s]
    push_cast
    ring
  rw [hsSub]
  push_cast
  field_simp [hsubC, hq]

theorem tendsto_routePProjectiveOrdinateCubicTangentGram_collision
    {R a b gamma kappa : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinateCubicTangentGram R a gamma b
          (routePCollisionOrdinate gamma kappa sigma) sigma)
      (nhdsWithin 1 (Ioi 1))
      (nhds (routePCollisionCubicKernel R a b kappa)) := by
  have h1 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_collision
    (gamma := gamma) (kappa := kappa) hR ha hb
  have h2 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_collision
    (gamma := gamma) (kappa := kappa) hR ha (mul_pos two_pos hb)
  have h3 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_collision
    (gamma := gamma) (kappa := kappa) hR (mul_pos two_pos ha) hb
  have h4 := tendsto_routePProjectiveOrdinateLogMomentGramTerm_collision
    (gamma := gamma) (kappa := kappa) hR
      (mul_pos two_pos ha) (mul_pos two_pos hb)
  have h := ((h1.sub h2).sub h3).add h4
  simpa only [routePProjectiveOrdinateCubicTangentGram,
    routePCollisionCubicKernel] using h

/-- Two co-moving ordinates see only their relative collision frequency. -/
theorem routePProjectiveOrdinateLogMomentGramTerm_twoCollisions
    (R a b gamma kappa lambda sigma : ℝ) :
    routePProjectiveOrdinateLogMomentGramTerm R a
        (routePCollisionOrdinate gamma kappa sigma) b
        (routePCollisionOrdinate gamma lambda sigma) sigma =
      routePProjectiveOrdinateLogMomentGramTerm R a gamma b
        (routePCollisionOrdinate gamma (lambda - kappa) sigma) sigma := by
  unfold routePProjectiveOrdinateLogMomentGramTerm
  congr 3
  unfold routePProjectiveOrdinatePairParameter routePCollisionOrdinate
  push_cast
  ring

/-- Full two-column collision law: common ordinate motion is gauge; relative motion survives. -/
theorem tendsto_routePProjectiveOrdinateCubicTangentGram_twoCollisions
    {R a b gamma kappa lambda : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinateCubicTangentGram R a
          (routePCollisionOrdinate gamma kappa sigma) b
          (routePCollisionOrdinate gamma lambda sigma) sigma)
      (nhdsWithin 1 (Ioi 1))
      (nhds (routePCollisionCubicKernel R a b (lambda - kappa))) := by
  have hbase := tendsto_routePProjectiveOrdinateCubicTangentGram_collision
    (gamma := gamma) (kappa := lambda - kappa) hR ha hb
  apply hbase.congr'
  filter_upwards with sigma
  unfold routePProjectiveOrdinateCubicTangentGram
  rw [routePProjectiveOrdinateLogMomentGramTerm_twoCollisions,
    routePProjectiveOrdinateLogMomentGramTerm_twoCollisions,
    routePProjectiveOrdinateLogMomentGramTerm_twoCollisions,
    routePProjectiveOrdinateLogMomentGramTerm_twoCollisions]

/-- Finite packet of ordinates collapsing around a common physical height. -/
def routePFiniteCollisionCubicQuadraticForm
    {ι : Type*} [Fintype ι]
    (R sigma gamma : ℝ) (a kappa : ι → ℝ) (c : ι → ℂ) : ℂ :=
  routePFiniteOrdinateCubicQuadraticForm R sigma a
    (fun i => routePCollisionOrdinate gamma (kappa i) sigma) c

/-- Exact mesoscopic finite-packet law. The projector limit is replaced on collision clusters by
the non-diagonal translation-invariant kernel indexed by `kappa j - kappa i`. -/
theorem tendsto_routePFiniteCollisionCubicQuadraticForm
    {ι : Type*} [Fintype ι]
    {R gamma : ℝ} {a kappa : ι → ℝ} (c : ι → ℂ)
    (hR : 0 < R) (ha : ∀ i, 0 < a i) :
    Tendsto
      (fun sigma : ℝ =>
        routePFiniteCollisionCubicQuadraticForm
          R sigma gamma a kappa c)
      (nhdsWithin 1 (Ioi 1))
      (nhds
        (∑ i : ι, ∑ j : ι,
          (c j * (starRingEnd ℂ) (c i)) *
            routePCollisionCubicKernel R (a i) (a j)
              (kappa j - kappa i))) := by
  have hentry : ∀ i j : ι,
      Tendsto
        (fun sigma : ℝ =>
          (c j * (starRingEnd ℂ) (c i)) *
            routePProjectiveOrdinateCubicTangentGram R (a i)
              (routePCollisionOrdinate gamma (kappa i) sigma) (a j)
              (routePCollisionOrdinate gamma (kappa j) sigma) sigma)
        (nhdsWithin 1 (Ioi 1))
        (nhds
          ((c j * (starRingEnd ℂ) (c i)) *
            routePCollisionCubicKernel R (a i) (a j)
              (kappa j - kappa i))) := by
    intro i j
    exact
      (tendsto_routePProjectiveOrdinateCubicTangentGram_twoCollisions
        hR (ha i) (ha j)).const_mul
          (c j * (starRingEnd ℂ) (c i))
  have hsum := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset ι) fun j _ => hentry i j
  simpa [routePFiniteCollisionCubicQuadraticForm,
    routePFiniteOrdinateCubicQuadraticForm] using hsum

theorem routePCollisionOrdinate_ne
    {gamma kappa sigma : ℝ} (hkappa : kappa ≠ 0) (hsigma : 1 < sigma) :
    routePCollisionOrdinate gamma kappa sigma ≠ gamma := by
  unfold routePCollisionOrdinate
  exact add_ne_left.mpr (mul_ne_zero hkappa (sub_ne_zero.mpr hsigma.ne'))

theorem not_tendsto_routePProjectiveOrdinateZetaOverlap_zero_along_collisions
    {R a b gamma kappa : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ¬ Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinateZetaOverlap R a gamma b
          (routePCollisionOrdinate gamma kappa sigma) sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  intro hzero
  have hnonzero := tendsto_routePProjectiveOrdinateZetaOverlap_collision
    (gamma := gamma) (kappa := kappa) hR ha hb
  have heq := tendsto_nhds_unique hzero hnonzero
  have hq := routePCollisionPairFrequency_ne_zero
    (kappa := kappa) hR ha hb
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  exact (div_ne_zero hR0 hq) heq.symm

theorem routePCollisionCubicKernel_one_ne_zero :
    routePCollisionCubicKernel 1 1 1 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [routePCollisionCubicKernel, routePCollisionPairFrequency,
    pow_succ, Complex.div_re, Complex.normSq_apply] at hre

theorem not_tendsto_routePProjectiveOrdinateCubicTangentGram_zero_along_collisions :
    ¬ Tendsto
      (fun sigma : ℝ =>
        routePProjectiveOrdinateCubicTangentGram 1 1 0 1
          (sigma - 1) sigma)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  intro hzero
  have hlimit :=
    tendsto_routePProjectiveOrdinateCubicTangentGram_collision
      (R := 1) (a := 1) (b := 1) (gamma := 0) (kappa := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hfun : (fun sigma : ℝ =>
      routePProjectiveOrdinateCubicTangentGram 1 1 0 1
        (routePCollisionOrdinate 0 1 sigma) sigma) =
      (fun sigma : ℝ =>
        routePProjectiveOrdinateCubicTangentGram 1 1 0 1
          (sigma - 1) sigma) := by
    funext sigma
    congr 2
    simp [routePCollisionOrdinate]
  rw [hfun] at hlimit
  exact routePCollisionCubicKernel_one_ne_zero
    (tendsto_nhds_unique hzero hlimit).symm

end

end RHTower

