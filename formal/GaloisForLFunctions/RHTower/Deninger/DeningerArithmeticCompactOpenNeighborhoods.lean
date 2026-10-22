import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticFiniteJetPeeling
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Ball control of compact-open source neighborhoods

Every neighborhood of zero in the compact-open entire source is controlled by one sufficiently
large centered disk: a sequence converging locally uniformly to zero on that disk is eventually
inside the neighborhood.

This is the topological exhaustion input for `[DAC_LOCAL_QUOTIENT_OPENNESS]`.  The proof reduces a
compact-open neighborhood to finitely many compact source sets, puts their union in one centered
ball, and applies uniform convergence on each compact set.
-/

open Complex Filter Function Set Topology UniformSpace

namespace RHTower

noncomputable section

/--
One centered disk controls any prescribed compact-open neighborhood of zero.

Only convergence on that disk is assumed; no global convergence or global interpolation theorem is
used.
-/
theorem exists_deningerCompactOpen_ball_eventually_mem
    {A : Set DeningerCompactOpenEntire}
    (hA : A ∈ 𝓝 0) :
    ∃ n : ℕ, ∀ G : ℕ → DeningerCompactOpenEntire,
      TendstoLocallyUniformlyOn
          (fun j z => G j z) (fun _ => 0)
          atTop (Metric.ball 0 n) →
        ∀ᶠ j in atTop, G j ∈ A := by
  obtain ⟨B, hB, hBA⟩ :=
    (mem_nhds_induced
      deningerCompactOpenEntireSubmodule.subtype
      (0 : DeningerCompactOpenEntire) A).mp hA
  obtain ⟨T, hTfinite, hTdata, hTB⟩ :=
    ContinuousMap.mem_nhds_iff.mp hB
  let Kall : Set ℂ := ⋃ KU ∈ T, KU.1
  have hKall : IsCompact Kall := by
    exact hTfinite.isCompact_biUnion fun KU hKU =>
      (hTdata KU.1 KU.2 hKU).1
  obtain ⟨r, hr⟩ :=
    hKall.isBounded.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  refine ⟨n, fun G hG => ?_⟩
  have hKallBall :
      Kall ⊆ Metric.ball (0 : ℂ) n :=
    hr.trans (Metric.ball_subset_ball (by
      exact_mod_cast hn.le))
  have hEach :
      ∀ KU ∈ T,
        ∀ᶠ j in atTop,
          MapsTo (G j) KU.1 KU.2 := by
    intro KU hKU
    have hK : IsCompact KU.1 :=
      (hTdata KU.1 KU.2 hKU).1
    have hU : IsOpen KU.2 :=
      (hTdata KU.1 KU.2 hKU).2.1
    have hzero :
        MapsTo (0 : C(ℂ, ℂ)) KU.1 KU.2 :=
      (hTdata KU.1 KU.2 hKU).2.2
    have hKsub : KU.1 ⊆ Metric.ball (0 : ℂ) n := by
      intro z hz
      apply hKallBall
      exact mem_iUnion₂_of_mem hKU hz
    have hloc :
        TendstoLocallyUniformlyOn
          (fun j z => G j z) (fun _ => 0)
          atTop KU.1 :=
      hG.mono hKsub
    have hunif :
        TendstoUniformlyOn
          (fun j z => G j z) (fun _ => 0)
          atTop KU.1 :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        hK).mp hloc
    obtain ⟨V, hV, -, hVzero⟩ :=
      lebesgue_number_of_compact_open
        (hK.image (map_continuous (0 : C(ℂ, ℂ))))
        hU hzero.image_subset
    filter_upwards [hunif V hV] with j hj z hz
    exact hVzero _ (mem_image_of_mem (0 : C(ℂ, ℂ)) hz)
      (hj z hz)
  filter_upwards [hTfinite.eventually_all.mpr hEach] with j hj
  apply hBA
  apply hTB
  intro K U hKU
  exact hj (K, U) hKU

end

end RHTower
