import GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherConormalResidueSplit
import GaloisForLFunctions.RHTower.SoninCofinalComplexPhaseOddFisherSplice

/-!
# Physical cofinal law for the squarefree Fisher regular conormal germ

At a fixed strict-right Xi zero `rho`, the squarefree logarithmic derivative has a pole of its
exact Xi multiplicity plus one analytic germ `g`.  In physical source coordinates
`epsilon = sigma - 1`, this yields an exact Fisher-conormal split at every `sigma > 1`.

The analytic regular germ has universal value `2` in the cofinal limit at the moving zero, so its
squared magnitude converges exactly to the four-unit source budget.  This closes the distinguished-
point regular finite-part burden.  It does not annihilate the forced residue or prove full graph
nonexpansiveness.
-/

open Complex Filter Set Topology
open scoped Topology

namespace RHTower

noncomputable section

/-- Physical source coordinate carrying the fixed spectral point `rho`. -/
def mscPhysicalZeroCoordinate (rho : ℂ) (sigma : ℝ) : ℂ :=
  (rho - (sigma : ℂ)) / ((sigma - 1 : ℝ) : ℂ)

/-- Explicit regular part obtained from a fixed spectral logarithmic-derivative germ. -/
def mscPhysicalRegularGerm (_rho : ℂ) (g : ℂ → ℂ) (sigma : ℝ) (v : ℂ) : ℂ :=
  2 * ((sigma - 1 : ℝ) : ℂ) *
    (g ((sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ)) +
      GaloisForLFunctions.squarefreeFixedCurrent (sigma : ℂ))

theorem mscPhysicalZeroCoordinate_landing
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    (sigma : ℂ) + mscPhysicalZeroCoordinate rho sigma *
        ((sigma - 1 : ℝ) : ℂ) = rho := by
  rw [mscPhysicalZeroCoordinate]
  have heps : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigma
  field_simp [heps]
  ring

theorem deriv_squarefreeBoundaryOverlap_eq_affine_partition
    {sigma epsilon v : ℂ}
    (hshift : AnalyticAt ℂ GaloisForLFunctions.squarefreePartition
      (sigma + v * epsilon)) :
    deriv (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) v =
      epsilon * deriv GaloisForLFunctions.squarefreePartition
          (sigma + v * epsilon) /
        GaloisForLFunctions.squarefreePartition sigma := by
  have houter := hshift.differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun w : ℂ => sigma + w * epsilon) epsilon v := by
    convert! (hasDerivAt_const (x := v) (c := sigma)).add
      ((hasDerivAt_id v).mul_const epsilon) using 1
    ring
  have hcomp : HasDerivAt
      (fun w : ℂ => GaloisForLFunctions.squarefreePartition
        (sigma + w * epsilon))
      (deriv GaloisForLFunctions.squarefreePartition
          (sigma + v * epsilon) * epsilon) v := by
    simpa only using! houter.comp v hinner
  have hquot := hcomp.div_const
    (GaloisForLFunctions.squarefreePartition sigma)
  rw [show GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon =
      fun w => GaloisForLFunctions.squarefreePartition
        (sigma + w * epsilon) /
          GaloisForLFunctions.squarefreePartition sigma by rfl,
    hquot.deriv]
  ring

theorem tendsto_mscPhysicalAffine_punctured
    (rho : ℂ) {sigma : ℝ} (hsigma : sigma ≠ 1) :
    Tendsto
      (fun v : ℂ => (sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ))
      (𝓝[≠] (mscPhysicalZeroCoordinate rho sigma))
      (𝓝[≠] rho) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hcont : Continuous
        (fun v : ℂ => (sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ)) := by
      fun_prop
    have ht : Tendsto
        (fun v : ℂ => (sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ))
        (𝓝[≠] (mscPhysicalZeroCoordinate rho sigma))
        (𝓝 ((sigma : ℂ) + mscPhysicalZeroCoordinate rho sigma *
          ((sigma - 1 : ℝ) : ℂ))) :=
      (hcont.tendsto
        (mscPhysicalZeroCoordinate rho sigma)).mono_left nhdsWithin_le_nhds
    convert ht using 1
    rw [mscPhysicalZeroCoordinate_landing rho hsigma]
  · filter_upwards [self_mem_nhdsWithin] with v hv
    change v ≠ mscPhysicalZeroCoordinate rho sigma at hv
    change (sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ) ≠ rho
    intro heq
    have hland := mscPhysicalZeroCoordinate_landing rho hsigma
    have hmul :
        (v - mscPhysicalZeroCoordinate rho sigma) *
            ((sigma - 1 : ℝ) : ℂ) = 0 := by
      linear_combination heq - hland
    have heps : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hsigma
    exact hv (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right heps))

theorem exists_squarefreePartition_logDeriv_regularGerm_of_strictRightXiZero
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        logDeriv GaloisForLFunctions.squarefreePartition =ᶠ[𝓝[≠] rho]
          fun s => ((k + 1 : ℕ) : ℂ) / (s - rho) + g s := by
  obtain ⟨k, hkXi, _h⟩ :=
    squarefreeFisherConormal_residueSplit_of_strictRightXiZero
      (sigma := (2 : ℂ)) (epsilon := (1 : ℂ))
      (u := rho - 2) (rho := rho)
      (by norm_num) (by norm_num) (by ring) hhalf hone hzero
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hone
    norm_num at hone
  have hPAn : AnalyticAt ℂ GaloisForLFunctions.squarefreePartition rho :=
    analyticAt_squarefreePartition_of_half_lt_re hhalf hrho1
  have hPOrder :
      analyticOrderAt GaloisForLFunctions.squarefreePartition rho =
        (k + 1 : ℕ) := by
    rw [analyticOrderAt_squarefreePartition_eq_xi_of_strictRightStrip
      hhalf hone, hkXi]
  have hMOrder :
      meromorphicOrderAt GaloisForLFunctions.squarefreePartition rho =
        ((k + 1 : ℕ) : ℤ) := by
    rw [hPAn.meromorphicOrderAt_eq, hPOrder]
    rw [ENat.map_coe]
  obtain ⟨g, hg, hlog⟩ :=
    GaloisForLFunctions.HTGeometry.exists_analyticAt_logDeriv_local_form
      hPAn.meromorphicAt hMOrder
  refine ⟨k, hkXi, g, hg, ?_⟩
  simpa using hlog

theorem analyticAt_mscPhysicalRegularGerm
    {rho : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g rho)
    {sigma : ℝ} (hsigma : sigma ≠ 1) :
    AnalyticAt ℂ (mscPhysicalRegularGerm rho g sigma)
      (mscPhysicalZeroCoordinate rho sigma) := by
  let affine : ℂ → ℂ :=
    fun v => (sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ)
  have haffine : AnalyticAt ℂ affine
      (mscPhysicalZeroCoordinate rho sigma) := by
    dsimp only [affine]
    fun_prop
  have hland : affine (mscPhysicalZeroCoordinate rho sigma) = rho := by
    exact mscPhysicalZeroCoordinate_landing rho hsigma
  have hcomp : AnalyticAt ℂ (g ∘ affine)
      (mscPhysicalZeroCoordinate rho sigma) :=
    hg.comp_of_eq haffine hland
  change AnalyticAt ℂ
    (fun v => 2 * ((sigma - 1 : ℝ) : ℂ) *
      (g (affine v) +
        GaloisForLFunctions.squarefreeFixedCurrent (sigma : ℂ)))
    (mscPhysicalZeroCoordinate rho sigma)
  exact analyticAt_const.mul (hcomp.add analyticAt_const)

theorem mscPhysicalRegularGerm_residueSplit
    {rho : ℂ} {k : ℕ} {g : ℂ → ℂ}
    (hPAn : AnalyticAt ℂ GaloisForLFunctions.squarefreePartition rho)
    (hPOrder : analyticOrderAt GaloisForLFunctions.squarefreePartition rho =
      (k + 1 : ℕ))
    (hlog :
      logDeriv GaloisForLFunctions.squarefreePartition =ᶠ[𝓝[≠] rho]
        fun s => ((k + 1 : ℕ) : ℂ) / (s - rho) + g s)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (fun v =>
      GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v /
        GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v) =ᶠ[
      𝓝[≠] (mscPhysicalZeroCoordinate rho sigma)]
        fun v => 2 * ((k + 1 : ℕ) : ℂ) /
          (v - mscPhysicalZeroCoordinate rho sigma) +
            mscPhysicalRegularGerm rho g sigma v := by
  have hsigmaNe : sigma ≠ 1 := hsigma.ne'
  have heps : (((sigma - 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hsigmaNe
  have hbase :
      GaloisForLFunctions.squarefreePartition (sigma : ℂ) ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero (by simpa using hsigma)
  have hfinite :
      analyticOrderAt GaloisForLFunctions.squarefreePartition rho ≠ ⊤ := by
    rw [hPOrder]
    exact ENat.coe_ne_top (k + 1)
  have hPne : ∀ᶠ s in 𝓝[≠] rho,
      GaloisForLFunctions.squarefreePartition s ≠ 0 := by
    rcases hPAn.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim (hfinite (analyticOrderAt_eq_top.mpr hzero))
    · exact hne
  have hmap := tendsto_mscPhysicalAffine_punctured rho hsigmaNe
  have hlogv := hmap.eventually hlog
  have hPnev := hmap.eventually hPne
  have hPAnPunct : ∀ᶠ s in 𝓝[≠] rho,
      AnalyticAt ℂ GaloisForLFunctions.squarefreePartition s :=
    hPAn.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hPAnv := hmap.eventually hPAnPunct
  filter_upwards [hlogv, hPnev, hPAnv, self_mem_nhdsWithin]
      with v hvlog hvne hvAn hvpunct
  have hvneU : v ≠ mscPhysicalZeroCoordinate rho sigma := hvpunct
  have haffineSub :
      (sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ) - rho =
        (v - mscPhysicalZeroCoordinate rho sigma) *
          ((sigma - 1 : ℝ) : ℂ) := by
    rw [mscPhysicalZeroCoordinate]
    field_simp [heps]
    ring
  have hquot :
      GaloisForLFunctions.squarefreeFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v /
        GaloisForLFunctions.squarefreeBoundaryOverlap
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v =
      2 * ((sigma - 1 : ℝ) : ℂ) *
        (logDeriv GaloisForLFunctions.squarefreePartition
            ((sigma : ℂ) + v * ((sigma - 1 : ℝ) : ℂ)) +
          GaloisForLFunctions.squarefreeFixedCurrent (sigma : ℂ)) := by
    have hvne' : GaloisForLFunctions.squarefreePartition
        ((sigma : ℂ) + ((sigma - 1 : ℝ) : ℂ) * v) ≠ 0 := by
      simpa [mul_comm] using hvne
    rw [GaloisForLFunctions.squarefreeFisherScore,
      deriv_squarefreeBoundaryOverlap_eq_affine_partition hvAn,
      GaloisForLFunctions.squarefreeBoundaryOverlap, logDeriv_apply]
    field_simp [hvne, hvne', hbase]
  rw [hquot, hvlog, haffineSub]
  dsimp only [mscPhysicalRegularGerm]
  field_simp [heps, hvneU]
  ring

/-- The source-scaled regular germ has universal cofinal value two at its moving zero. -/
theorem tendsto_mscPhysicalRegularGerm_at_zeroCoordinate
    (rho : ℂ) (g : ℂ → ℂ) :
    Tendsto
      (fun sigma : ℝ =>
        mscPhysicalRegularGerm rho g sigma
          (mscPhysicalZeroCoordinate rho sigma))
      (nhdsWithin 1 (Ioi 1)) (nhds 2) := by
  let l := nhdsWithin (1 : ℝ) (Ioi 1)
  have hcurrent :=
    tendsto_sub_one_mul_squarefreeFixedCurrent_complexPath
      (u := (0 : ℂ)) (by norm_num)
  have hcurrent' : Tendsto
      (fun sigma : ℝ =>
        ((sigma - 1 : ℝ) : ℂ) *
          GaloisForLFunctions.squarefreeFixedCurrent (sigma : ℂ))
      l (nhds 1) := by
    simpa [soninComplexCriticalPath] using hcurrent
  have heps : Tendsto (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ)) l (nhds 0) := by
    have hcont : Continuous (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ)) := by
      fun_prop
    simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hgzero : Tendsto
      (fun sigma : ℝ => ((sigma - 1 : ℝ) : ℂ) * g rho)
      l (nhds 0) := by
    simpa using heps.mul_const (g rho)
  have hsum := hgzero.add hcurrent'
  have hconst : Tendsto (fun _ : ℝ => (2 : ℂ)) l (nhds 2) :=
    tendsto_const_nhds
  have htwo : Tendsto
      (fun sigma : ℝ => (2 : ℂ) *
        (((sigma - 1 : ℝ) : ℂ) * g rho +
          ((sigma - 1 : ℝ) : ℂ) *
            GaloisForLFunctions.squarefreeFixedCurrent (sigma : ℂ)))
      l (nhds 2) := by
    simpa using hconst.mul hsum
  apply htwo.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [mscPhysicalRegularGerm,
    mscPhysicalZeroCoordinate_landing rho hsigma.ne']
  ring

/-- The regular-germ energy at the moving zero converges to the exact four-unit budget. -/
theorem tendsto_normSq_mscPhysicalRegularGerm_at_zeroCoordinate
    (rho : ℂ) (g : ℂ → ℂ) :
    Tendsto
      (fun sigma : ℝ =>
        Complex.normSq
          (mscPhysicalRegularGerm rho g sigma
            (mscPhysicalZeroCoordinate rho sigma)))
      (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  have h := Complex.continuous_normSq.continuousAt.tendsto.comp
    (tendsto_mscPhysicalRegularGerm_at_zeroCoordinate rho g)
  have h4 : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq]
  rw [← h4]
  change Tendsto
    (Complex.normSq ∘ fun sigma : ℝ =>
      mscPhysicalRegularGerm rho g sigma
        (mscPhysicalZeroCoordinate rho sigma))
    (nhdsWithin 1 (Ioi 1)) (nhds (Complex.normSq (2 : ℂ)))
  exact h

/-- At each strict-right Xi zero, physical source scaling exposes the exact pole and an analytic
regular conormal germ whose energy at the moving zero converges to four. -/
theorem exists_mscPhysicalRegularGerm_residueSplit_tendsto_four
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho ∧
        (∀ sigma : ℝ, 1 < sigma →
          AnalyticAt ℂ (mscPhysicalRegularGerm rho g sigma)
              (mscPhysicalZeroCoordinate rho sigma) ∧
            (fun v =>
              GaloisForLFunctions.squarefreeFisherScore
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v /
                GaloisForLFunctions.squarefreeBoundaryOverlap
                  (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) v) =ᶠ[
              𝓝[≠] (mscPhysicalZeroCoordinate rho sigma)]
                fun v => 2 * ((k + 1 : ℕ) : ℂ) /
                  (v - mscPhysicalZeroCoordinate rho sigma) +
                    mscPhysicalRegularGerm rho g sigma v) ∧
          Tendsto
            (fun sigma : ℝ =>
              Complex.normSq
                (mscPhysicalRegularGerm rho g sigma
                  (mscPhysicalZeroCoordinate rho sigma)))
            (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  obtain ⟨k, hk, g, hg, hlog⟩ :=
    exists_squarefreePartition_logDeriv_regularGerm_of_strictRightXiZero
      hhalf hone hzero
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hone
    norm_num at hone
  have hPAn : AnalyticAt ℂ GaloisForLFunctions.squarefreePartition rho :=
    analyticAt_squarefreePartition_of_half_lt_re hhalf hrho1
  have hPOrder :
      analyticOrderAt GaloisForLFunctions.squarefreePartition rho =
        (k + 1 : ℕ) := by
    rw [analyticOrderAt_squarefreePartition_eq_xi_of_strictRightStrip
      hhalf hone, hk]
  refine ⟨k, hk, g, hg, ?_,
    tendsto_normSq_mscPhysicalRegularGerm_at_zeroCoordinate rho g⟩
  intro sigma hsigma
  exact ⟨analyticAt_mscPhysicalRegularGerm hg hsigma.ne',
    mscPhysicalRegularGerm_residueSplit hPAn hPOrder hlog hsigma⟩

end

end RHTower
