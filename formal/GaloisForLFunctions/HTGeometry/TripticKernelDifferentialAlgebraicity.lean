import GaloisForLFunctions.HTGeometry.TripticAtomSumDifferentiallyAlgebraic
import GaloisForLFunctions.HTGeometry.TripticKernelIdentification

/-!
# A source with vanishing orbital divisor is differentially algebraic

The kernel identification presents such a source, off a countable set, as an explicit finite
combination of theta-source jets plus a constant.  Two meromorphic functions agreeing off a
countable set have the same canonical normal form — the complement of a countable set is dense, so
the difference vanishes frequently near every point of its analytic locus and the identity theorem
spreads that to the whole locus, which contains a punctured neighbourhood of every point.  The atom
sum is differentially algebraic, and so is a constant, so the source is too.

This identifies the kernel of the triptic orbit-residue divisor: a mixed-constraint source whose
orbital divisor vanishes satisfies an algebraic differential equation.

* `toMeromorphicNFOn_eq_of_eq_off_countable`;
* `differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-- A punctured neighbourhood meets the complement of a countable set. -/
theorem frequently_nhdsNE_notMem_of_countable {S : Set ℂ} (hS : S.Countable) (z₀ : ℂ) :
    ∃ᶠ z in 𝓝[≠] z₀, z ∉ S := by
  have hdense : Dense Sᶜ := hS.dense_compl ℂ
  rw [Filter.frequently_iff]
  intro A hA
  rw [mem_nhdsWithin] at hA
  obtain ⟨u, hu, hz₀u, hsub⟩ := hA
  have hne : (u ∩ {z₀}ᶜ).Nonempty := by
    refine Filter.NeBot.nonempty_of_mem (f := 𝓝[≠] z₀) inferInstance ?_
    exact Filter.inter_mem (nhdsWithin_le_nhds (hu.mem_nhds hz₀u)) self_mem_nhdsWithin
  obtain ⟨w, hw⟩ := hdense.inter_open_nonempty (u ∩ {z₀}ᶜ) (hu.inter isOpen_compl_singleton) hne
  exact ⟨w, hsub ⟨hw.1.1, hw.1.2⟩, hw.2⟩

/-- **Two meromorphic functions agreeing off a countable set have the same normal form.** -/
theorem toMeromorphicNFOn_eq_of_eq_off_countable {f g : ℂ → ℂ}
    (hf : MeromorphicOn f (Set.univ : Set ℂ)) (hg : MeromorphicOn g (Set.univ : Set ℂ))
    {S : Set ℂ} (hS : S.Countable) (h : ∀ z ∉ S, f z = g z) :
    toMeromorphicNFOn f (Set.univ : Set ℂ) = toMeromorphicNFOn g (Set.univ : Set ℂ) := by
  classical
  set F : ℂ → ℂ := toMeromorphicNFOn f (Set.univ : Set ℂ) with hFdef
  set G : ℂ → ℂ := toMeromorphicNFOn g (Set.univ : Set ℂ) with hGdef
  have hNFF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hNFG : MeromorphicNFOn G (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  set H : ℂ → ℂ := fun z ↦ F z - G z with hHdef
  have hHmer : MeromorphicOn H (Set.univ : Set ℂ) := fun z _ ↦
    (hNFF.meromorphicOn z (Set.mem_univ z)).sub (hNFG.meromorphicOn z (Set.mem_univ z))
  set N : Set ℂ := {z : ℂ | AnalyticAt ℂ H z}ᶜ with hNdef
  have hNcount : N.Countable :=
    Meromorphic.countable_compl_analyticAt fun z ↦ hHmer z (Set.mem_univ z)
  set W : Set ℂ := {z : ℂ | AnalyticAt ℂ H z} with hWdef
  have hWo : IsOpen W := isOpen_analyticAt ℂ H
  have hWconn : IsPreconnected W := by
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      norm_num
    have hWN : W = Nᶜ := by rw [hNdef, hWdef, compl_compl]
    rw [hWN]
    exact (Set.Countable.isPathConnected_compl_of_one_lt_rank hrank
      hNcount).isConnected.isPreconnected
  -- the bad set off which the two normal forms are the two functions
  set T : Set ℂ := S ∪ ({z : ℂ | AnalyticAt ℂ f z}ᶜ ∪ {z : ℂ | AnalyticAt ℂ g z}ᶜ) with hTdef
  have hTcount : T.Countable :=
    hS.union ((Meromorphic.countable_compl_analyticAt fun z ↦ hf z (Set.mem_univ z)).union
      (Meromorphic.countable_compl_analyticAt fun z ↦ hg z (Set.mem_univ z)))
  have hHzero : ∀ z ∉ T, H z = 0 := by
    intro z hz
    have hzS : z ∉ S := fun hc ↦ hz (Or.inl hc)
    have hfz : AnalyticAt ℂ f z := by
      by_contra hc
      exact hz (Or.inr (Or.inl hc))
    have hgz : AnalyticAt ℂ g z := by
      by_contra hc
      exact hz (Or.inr (Or.inr hc))
    have hFz : F z = f z := by
      have hord : 0 ≤ meromorphicOrderAt f z :=
        hfz.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hfz
      have hFord : 0 ≤ meromorphicOrderAt F z := by
        rw [hFdef, meromorphicOrderAt_toMeromorphicNFOn hf (Set.mem_univ z)]
        exact hord
      have hFan : AnalyticAt ℂ F z :=
        (hNFF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hFord
      exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt
        (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)) hFan.continuousAt
        hfz.continuousAt).eq_of_nhds
    have hGz : G z = g z := by
      have hord : 0 ≤ meromorphicOrderAt g z :=
        hgz.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hgz
      have hGord : 0 ≤ meromorphicOrderAt G z := by
        rw [hGdef, meromorphicOrderAt_toMeromorphicNFOn hg (Set.mem_univ z)]
        exact hord
      have hGan : AnalyticAt ℂ G z :=
        (hNFG (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hGord
      exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt
        (hg.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)) hGan.continuousAt
        hgz.continuousAt).eq_of_nhds
    rw [hHdef]
    simp only
    rw [hFz, hGz, h z hzS, sub_self]
  -- the difference vanishes on the whole analytic locus
  have hWne : W.Nonempty := by
    have hdense : Dense Nᶜ := hNcount.dense_compl ℂ
    obtain ⟨w, _, hw⟩ := hdense.inter_open_nonempty Set.univ isOpen_univ ⟨0, Set.mem_univ 0⟩
    exact ⟨w, by rwa [hWdef, ← compl_compl {z : ℂ | AnalyticAt ℂ H z}, ← hNdef]⟩
  obtain ⟨z₀, hz₀⟩ := hWne
  have hHW : AnalyticOnNhd ℂ H W := fun z hz ↦ hz
  have hEqW : Set.EqOn H 0 W :=
    hHW.eqOn_zero_of_preconnected_of_frequently_eq_zero hWconn hz₀
      ((frequently_nhdsNE_notMem_of_countable hTcount z₀).mono fun z hz ↦ hHzero z hz)
  -- hence the two normal forms have the same punctured germ everywhere
  have hFG : ∀ z, f =ᶠ[𝓝[≠] z] g := by
    intro z
    have hpunctH : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ H w :=
      (hHmer z (Set.mem_univ z)).eventually_analyticAt
    have hFGpunct : F =ᶠ[𝓝[≠] z] G := by
      filter_upwards [hpunctH] with w hw
      have hzero := hEqW hw
      simp only [hHdef, Pi.zero_apply] at hzero
      exact sub_eq_zero.mp hzero
    exact ((hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)).symm.trans
      hFGpunct).trans (hg.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z))
  exact toMeromorphicNFOn_congr hf hg hFG

/-- A constant function is realized by a differentially algebraic germ. -/
theorem realizedDA_const (c : ℂ) : RealizedDA (fun _ : ℂ ↦ c) := by
  refine ⟨algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
    (constToAnalytic Set.univ c), ⟨constToAnalytic Set.univ c, 1, fun _ ↦ c, 1, one_ne_zero,
      analyticOnNhd_const, analyticOnNhd_const, rfl, map_one _, ?_, fun z _ ↦ ?_⟩, ?_⟩
  · rw [map_one, div_one]
  · simp
  · exact daOverRatFuncField.algebraMap_mem c

set_option maxHeartbeats 1000000 in
/-- **A mixed-constraint source with vanishing orbital divisor is differentially algebraic.**  This
is the kernel of the triptic orbit-residue divisor: the source agrees, off a countable set, with an
explicit finite combination of theta-source jets plus a constant, every one of which is
differentially algebraic, and agreement off a countable set does not change the normal form. -/
theorem differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor
    {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ))
    (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hvanish : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      ∑ᶠ m : ℤ, laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ = 0) :
    Cst = 0 ∧ DifferentiallyAlgebraic (toMeromorphicNFOn F (Set.univ : Set ℂ)) := by
  obtain ⟨hCst, n, Rτ, Rσ, c, S, hScount, hFS⟩ :=
    exists_const_sub_totalAtomSum_of_vanishing_divisor hF hper hmixed hτ hσ hindep hindepτ hindepσ
      hvanish
  refine ⟨hCst, ?_⟩
  have hgDA : RealizedDA (totalAtomSum F τ σ n Rτ Rσ + fun _ : ℂ ↦ c) :=
    (realizedDA_totalAtomSum hτ hσ F n Rτ Rσ).add (realizedDA_const c)
  obtain ⟨x, hx, hxmem⟩ := hgDA
  have hgmer : MeromorphicOn (totalAtomSum F τ σ n Rτ Rσ + fun _ : ℂ ↦ c) (Set.univ : Set ℂ) :=
    meromorphicOn_of_realizesMero hx
  rw [toMeromorphicNFOn_eq_of_eq_off_countable hF hgmer hScount fun z hz ↦ hFS z hz]
  exact RealizedDA.differentiallyAlgebraic ⟨x, hx, hxmem⟩


set_option maxHeartbeats 1000000 in
/-- **A mixed-constraint source with vanishing orbital divisor agrees, off a countable set, with a
realized differentially algebraic function.**  This is the kernel theorem in the form that keeps the
realizing germ, so that differential algebraicity can be transported through sums of functions
without factorising the source itself. -/
theorem exists_realizesMero_of_vanishing_orbital_divisor
    {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ))
    (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hvanish : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      ∑ᶠ m : ℤ, laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ = 0) :
    Cst = 0 ∧ ∃ (x : meroField (Set.univ : Set ℂ)) (g : ℂ → ℂ) (S : Set ℂ),
      RealizesMero x g ∧ x ∈ daOverRatFuncField ∧ S.Countable ∧ ∀ z ∉ S, F z = g z := by
  obtain ⟨hCst, n, Rτ, Rσ, c, S, hScount, hFS⟩ :=
    exists_const_sub_totalAtomSum_of_vanishing_divisor hF hper hmixed hτ hσ hindep hindepτ hindepσ
      hvanish
  obtain ⟨x, hx, hxmem⟩ :=
    (realizedDA_totalAtomSum hτ hσ F n Rτ Rσ).add (realizedDA_const c)
  exact ⟨hCst, x, totalAtomSum F τ σ n Rτ Rσ + fun _ : ℂ ↦ c, S, hx, hxmem, hScount,
    fun z hz ↦ hFS z hz⟩

end

end GaloisForLFunctions.HTGeometry
