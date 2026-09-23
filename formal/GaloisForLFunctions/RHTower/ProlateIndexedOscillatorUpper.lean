import GaloisForLFunctions.RHTower.ProlateIndexedSeparationOrder
import GaloisForLFunctions.RHTower.ProlateTrialSpaceTransport
import GaloisForLFunctions.RHTower.LeastSquaresProjection

/-!
# Canonical exhaustion and the indexed prolate oscillator upper law

Every smooth nonzero even joint Slepian/prolate mode at physical aperture `a` lies on exactly one
canonical signed eigenline.  Global strict separation order therefore identifies any high-mode
spectral subspace below a canonical cutoff with a finite span of initial canonical eigenlines.

This supplies the missing upper half of large-aperture index retention.  If canonical mode `n`
had scaled separation at least `4n+1+ε`, its high-mode space would have rank at most `n`; the
existing Hermite trial transport forces rank at least `n+1`.  Hence the scaled separation of the
actual indexed mode is eventually strictly below the corresponding even oscillator rung.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Spectral exhaustion for the joint problem: every live smooth even joint mode is a scalar
multiple of one canonical signed radial mode, with both its band and separation labels fixed by
that same index. -/
theorem exists_canonical_signedIndex_of_even_joint_prolate
    {a lam eta : ℝ} {Phi : ℝ → ℝ}
    (ha : 0 < a) (hlam : lam ≠ 0)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hne : Phi ≠ 0) (heven : Function.Even Phi)
    (hband : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) Phi x = lam * Phi x)
    (hprolate : ∀ x : ℝ,
      prolateSLAction (signedModeRadialBandwidth a) Phi x = eta * Phi x) :
    ∃ n : ℕ,
      evenProlateSignedValue a n ^ (2 : ℕ) = lam ∧
      eta = (signedModeRadialData a n).chi ∧
      ∃ r : ℝ, ∀ x : ℝ, Phi x = r * (signedModeRadialData a n).R x := by
  let f : RealIntervalL2 (-1 : ℝ) 1 := bandClass Phi hsm.continuous
  have hfne : f ≠ 0 :=
    bandClass_ne_zero_of_global_band_eigen hsm.continuous hlam hne hband
  have hfmem : f ∈ unitBandEvenSubspace :=
    bandClass_mem_unitBandEvenSubspace_of_even hsm.continuous heven
  have hproj : unitBandEvenProjection f ≠ 0 := by
    have hfix : unitBandEvenProjection f = f := by
      rw [unitBandEvenProjection_apply,
        (mem_unitBandEvenSubspace_iff f).mp hfmem]
      module
    rwa [hfix]
  have hfeig : bandOperatorL2 (signedModeRadialBandwidth a) f = lam • f :=
    bandOperatorL2_bandClass_eq_smul_of_global_band_eigen hsm.continuous hband
  obtain ⟨n, hnlam⟩ :=
    exists_evenProlateSignedValue_sq_eq_of_bandEigen_evenProjection_ne
      ha hlam hproj hfeig
  let D := signedModeRadialData a n
  have hD := signedModeRadialData_isExact_of_pos ha n
  rcases hD with ⟨hDPhiSm, hDPhiNe, hDPhiEven, hDPhiOne, hDRdef,
    hDRsm, hDREven, hDROne, hDPhiBand, hDRProlate, hDsdef, hDsNonneg,
    hDend, hDode⟩
  have hDRne : D.R ≠ 0 := by
    intro hzero
    have := congrFun hzero 1
    rw [hDROne] at this
    exact one_ne_zero this
  have hDRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) D.R x = lam * D.R x := by
    intro x
    rw [hDRdef]
    have h := bandTransform_endpointNormalize_eigen hDPhiBand x
    rw [hnlam] at h
    exact h
  have heta : eta = D.chi :=
    separation_eq_of_same_live_even_band hlam hsm hDRsm hne hDRne
      heven hDREven hband hDRBand hprolate hDRProlate
  obtain ⟨r, hr⟩ := continuous_real_bandEigen_proportional
    (by dsimp [signedModeRadialBandwidth]; positivity) hlam hDRsm.continuous hsm.continuous
      hDRne hDRBand hband
  exact ⟨n, hnlam, heta, r, hr⟩

/-- Canonical indices strictly above the high-mode separation threshold and below cutoff `n`. -/
def HighCanonicalIndex (a K : ℝ) (n : ℕ) :=
  {k : Fin n // -K < (signedModeRadialData a (k : ℕ)).chi}

noncomputable instance (a K : ℝ) (n : ℕ) : Fintype (HighCanonicalIndex a K n) :=
  by
    classical
    unfold HighCanonicalIndex
    infer_instance

/-- Band class of a canonical high index. -/
noncomputable def highCanonicalBandClass
    (a K : ℝ) (n : ℕ) (ha : 0 < a) (k : HighCanonicalIndex a K n) :
    RealIntervalL2 (-1 : ℝ) 1 :=
  bandClass (signedModeRadialData a k.1.1).R
    (signedModeRadialData_isExact_of_pos ha k.1.1).2.2.2.2.2.1.continuous

/-- Exact canonical exhaustion of the high joint-mode space below a canonical cutoff. -/
theorem highProlateSpan_eq_span_highCanonicalBandClass
    {a K : ℝ} (ha : 0 < a) (n : ℕ)
    (hcut : (signedModeRadialData a n).chi ≤ -K) :
    highProlateSpan (signedModeRadialBandwidth a) K =
      Submodule.span ℝ (Set.range (highCanonicalBandClass a K n ha)) := by
  apply le_antisymm
  · rw [highProlateSpan]
    apply Submodule.span_le.mpr
    rintro w ⟨Phi, hPhic, hhigh, rfl⟩
    obtain ⟨lam, eta, hlam, heta, hsm, hne, heven, hband, hprolate⟩ := hhigh
    obtain ⟨k, hklam, hketa, r, hr⟩ :=
      exists_canonical_signedIndex_of_even_joint_prolate ha hlam hsm hne heven
        hband hprolate
    have hkn : k < n := by
      by_contra hnot
      have hnk : n ≤ k := Nat.le_of_not_gt hnot
      have hanti := (signedModeRadialData_chi_strictAnti ha).antitone hnk
      rw [hketa] at heta
      linarith
    let i : HighCanonicalIndex a K n :=
      ⟨⟨k, hkn⟩, by simpa [hketa] using heta⟩
    have hmem : highCanonicalBandClass a K n ha i ∈
        Submodule.span ℝ (Set.range (highCanonicalBandClass a K n ha)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have hfun : Phi = fun x => r * (signedModeRadialData a k).R x := funext hr
    have htargetCont : Continuous (fun x => r * (signedModeRadialData a k).R x) :=
      continuous_const.mul
        (signedModeRadialData_isExact_of_pos ha k).2.2.2.2.2.1.continuous
    have hclassPhi : bandClass Phi hPhic =
        bandClass (fun x => r * (signedModeRadialData a k).R x) htargetCont :=
      bandClass_congr hPhic htargetCont hfun
    rw [hclassPhi]
    have hclass : bandClass (fun x => r * (signedModeRadialData a k).R x) htargetCont =
        r • highCanonicalBandClass a K n ha i := by
      simpa [highCanonicalBandClass, i] using
        bandClass_smul
          (signedModeRadialData_isExact_of_pos ha k).2.2.2.2.2.1.continuous r htargetCont
    rw [hclass]
    exact Submodule.smul_mem _ r hmem
  · apply Submodule.span_le.mpr
    rintro w ⟨i, rfl⟩
    let k : ℕ := i.1.1
    have hD := signedModeRadialData_isExact_of_pos ha k
    rcases hD with ⟨hDPhiSm, hDPhiNe, hDPhiEven, hDPhiOne, hDRdef,
      hDRsm, hDREven, hDROne, hDPhiBand, hDRProlate, hDsdef, hDsNonneg,
      hDend, hDode⟩
    have hDRne : (signedModeRadialData a k).R ≠ 0 := by
      intro hzero
      have := congrFun hzero 1
      rw [hDROne] at this
      exact one_ne_zero this
    have hDRBand : ∀ x : ℝ,
        bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a k).R x =
          evenProlateSignedValue a k ^ (2 : ℕ) * (signedModeRadialData a k).R x := by
      rw [hDRdef]
      exact bandTransform_endpointNormalize_eigen hDPhiBand
    rw [highCanonicalBandClass]
    exact bandClass_mem_highProlateSpan hDRsm.continuous
      ⟨evenProlateSignedValue a k ^ (2 : ℕ), (signedModeRadialData a k).chi,
        pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha k), by simpa [k] using i.property,
        hDRsm, hDRne, hDREven, hDRBand, hDRProlate⟩

/-- Canonical exhaustion makes the high-mode space projectable without an external closedness
hypothesis. -/
theorem highProlateSpan_hasOrthogonalProjection_of_chi_le
    {a K : ℝ} (ha : 0 < a) (n : ℕ)
    (hcut : (signedModeRadialData a n).chi ≤ -K) :
    (highProlateSpan (signedModeRadialBandwidth a) K).HasOrthogonalProjection := by
  rw [highProlateSpan_eq_span_highCanonicalBandClass ha n hcut]
  exact _root_.RHTower.hasOrthogonalProjection_span
    (highCanonicalBandClass a K n ha)

/-- If canonical index `n` lies below the high-mode cutoff, at most the preceding `n` canonical
lines remain above it. -/
theorem rank_highProlateSpan_le_of_chi_le
    {a K : ℝ} (ha : 0 < a) (n : ℕ)
    (hcut : (signedModeRadialData a n).chi ≤ -K) :
    Module.rank ℝ (highProlateSpan (signedModeRadialBandwidth a) K) ≤
      (n : Cardinal) := by
  rw [highProlateSpan_eq_span_highCanonicalBandClass ha n hcut]
  calc
    Module.rank ℝ (Submodule.span ℝ
        (Set.range (highCanonicalBandClass a K n ha)))
        ≤ Cardinal.mk (Set.range (highCanonicalBandClass a K n ha)) :=
      rank_span_le _
    _ ≤ Cardinal.mk (HighCanonicalIndex a K n) := Cardinal.mk_range_le
    _ ≤ Cardinal.mk (Fin n) := by
      exact Cardinal.mk_subtype_le
        (fun k : Fin n => -K < (signedModeRadialData a (k : ℕ)).chi)
    _ = (n : Cardinal) := Cardinal.mk_fin n

/-- Exact conversion from radial ratio to angular separation at positive aperture. -/
theorem signedModeRadialData_chi_eq_neg_bandwidth_sq_mul_s
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (signedModeRadialData a n).chi =
      -(signedModeRadialBandwidth a) ^ (2 : ℕ) * (signedModeRadialData a n).s := by
  have hs := (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.2.2.2.2.2.1
  have hc : signedModeRadialBandwidth a ≠ 0 := by
    dsimp [signedModeRadialBandwidth]
    positivity
  dsimp [radialSeparationRatio] at hs
  field_simp [hc] at hs
  nlinarith

/-- Sharp indexed upper half of the large-aperture oscillator law. -/
theorem eventually_signedModeRadialBandwidth_mul_s_lt_evenOscillatorRung
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop,
      signedModeRadialBandwidth a * (signedModeRadialData a n).s <
        4 * (n : ℝ) + 1 + ε := by
  have hrankC := eventually_rank_highProlateSpan_even_ge n hε
  have hrankA := tendsto_signedModeRadialBandwidth_atTop.eventually hrankC
  filter_upwards [eventually_gt_atTop (0 : ℝ), hrankA] with a ha hrank
  by_contra hnot
  let Λ : ℝ := 4 * (n : ℝ) + 1 + ε
  let c : ℝ := signedModeRadialBandwidth a
  have hc : 0 < c := by
    dsimp [c, signedModeRadialBandwidth]
    positivity
  have hΛ : Λ ≤ c * (signedModeRadialData a n).s := by
    exact le_of_not_gt (by simpa [Λ, c] using hnot)
  have hcut : (signedModeRadialData a n).chi ≤ -(Λ * c) := by
    rw [signedModeRadialData_chi_eq_neg_bandwidth_sq_mul_s ha n]
    change -(c ^ (2 : ℕ)) * (signedModeRadialData a n).s ≤ -(Λ * c)
    nlinarith
  let hproj : (highProlateSpan c (Λ * c)).HasOrthogonalProjection := by
    exact highProlateSpan_hasOrthogonalProjection_of_chi_le ha n hcut
  have hlower : ((n : Cardinal) + 1) ≤
      Module.rank ℝ (highProlateSpan c (Λ * c)) := by
    simpa [Λ, c] using hrank hproj
  have hupper : Module.rank ℝ (highProlateSpan c (Λ * c)) ≤
      (n : Cardinal) := by
    exact rank_highProlateSpan_le_of_chi_le ha n hcut
  have hbad : ((n : Cardinal) + 1) ≤ (n : Cardinal) := hlower.trans hupper
  have hlt : (n : Cardinal) < (n : Cardinal) + 1 := by
    exact_mod_cast Nat.lt_succ_self n
  exact (not_le_of_gt hlt) hbad

end GaloisForLFunctions.RHTower
