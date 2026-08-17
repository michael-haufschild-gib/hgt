import GaloisForLFunctions.HTGeometry.HelsonContinuationData

/-!
# A continuation produces a certificate at every level

If `Z(χ, ·)` continues meromorphically to the plane then, on each disc, the continuation has
finitely many poles; clearing them with the factorized rational function built from the negative
part of the divisor leaves a function holomorphic on the disc, whose Taylor coefficients at `s = 2`
obey the geometric bound coming from the radius of convergence.

The poles all lie in `Re s ≤ 1`, because on the half plane of absolute convergence the continuation
agrees with the Euler product and is therefore holomorphic there.
-/

open Complex Filter Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **A continuable phase carries a certificate at every level.** -/
theorem exists_levelData_of_mem_continuableStratum {χ : PhaseTorus}
    (hχ : χ ∈ continuableStratum) (N : ℕ) :
    ∃ (B d : ℕ) (u : Fin d → ℂ) (c : ℕ → ℂ), LevelData χ N B u c := by
  classical
  obtain ⟨F, hFmero, hFprod⟩ := hχ
  set ρ : ℝ := levelRadius N with hρdef
  have hρpos : 0 < ρ := levelRadius_pos N
  set V : Set ℂ := Metric.ball (2 : ℂ) (ρ + 1) with hVdef
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hVconn : IsPreconnected V := (convex_ball (2 : ℂ) (ρ + 1)).isPreconnected
  have hFV : MeromorphicOn F V := fun z _ => hFmero z (Set.mem_univ z)
  have hFVc : MeromorphicOn F (Metric.closedBall (2 : ℂ) (ρ + 1)) :=
    fun z _ => hFmero z (Set.mem_univ z)
  have hFeq : ∀ s : ℂ, 1 < s.re → helsonZetaValue s χ = F s := fun s hs => (hFprod s hs).tprod_eq
  have hhalfopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hFana : ∀ s : ℂ, 1 < s.re → AnalyticAt ℂ F s := by
    intro s hs
    have hZ : AnalyticAt ℂ (fun z : ℂ => helsonZetaValue z χ) s :=
      (differentiableOn_helsonZetaValue χ).analyticAt (hhalfopen.mem_nhds hs)
    refine hZ.congr ?_
    filter_upwards [hhalfopen.mem_nhds hs] with z hz
    exact hFeq z hz
  have hmem2 : (2 : ℂ) ∈ V := by
    simp only [hVdef, Metric.mem_ball, dist_self]
    linarith
  -- the order of `F` is finite everywhere on `V`
  have hFordtop : ∀ z ∈ V, meromorphicOrderAt F z ≠ ⊤ := by
    have h2 : meromorphicOrderAt F 2 ≠ ⊤ := by
      refine (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hFV 2 hmem2)).2 ?_
      have hnb : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hhalfopen.mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hnb] with z hz
      rw [← hFeq z hz]
      exact helsonZetaValue_ne_zero hz χ
    intro z hz
    exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hFV hVconn hmem2 hz h2
  -- the divisor and its negative part
  set D : ℂ → ℤ := fun z => (MeromorphicOn.divisor F V) z with hDdef
  have hDfin : (Function.support D).Finite :=
    MeromorphicOn.divisor_ball_support_finite hFVc
  set e : ℂ → ℤ := fun z => -min (D z) 0 with hedef
  have hesupp : Function.support e ⊆ Function.support D := by
    intro z hz
    simp only [hedef, Function.mem_support, neg_ne_zero] at hz
    simp only [Function.mem_support]
    intro h
    rw [h] at hz
    simp at hz
  have hefin : Function.HasFiniteSupport e := hDfin.subset hesupp
  have hennoneg : ∀ z : ℂ, 0 ≤ e z := by
    intro z
    simp only [hedef, neg_nonneg]
    exact min_le_right _ _
  set q : ℂ → ℂ := ∏ᶠ a : ℂ, (fun x : ℂ => x - a) ^ e a with hqdef
  have hqorder : ∀ z : ℂ, meromorphicOrderAt q z = ((e z : ℤ) : WithTop ℤ) :=
    fun z => Function.FactorizedRational.meromorphicOrderAt_eq e hefin
  have hqana : ∀ z : ℂ, AnalyticAt ℂ q z := fun z =>
    Function.FactorizedRational.analyticAt (hennoneg z)
  have hqmero : MeromorphicOn q V := fun z _ => (hqana z).meromorphicAt
  have hqF : MeromorphicOn (q * F) V := hqmero.mul hFV
  -- clearing the poles makes the product analytic
  have hordernonneg : ∀ z ∈ V, 0 ≤ meromorphicOrderAt (q * F) z := by
    intro z hz
    have hFz : meromorphicOrderAt F z = ((D z : ℤ) : WithTop ℤ) := by
      have hval := hFV.divisor_apply hz
      have hne := hFordtop z hz
      rw [hDdef]
      simp only
      rw [hval]
      exact (WithTop.coe_untop₀_of_ne_top hne).symm
    rw [meromorphicOrderAt_mul (hqmero z hz) (hFV z hz), hqorder z, hFz]
    have hsum : (0 : ℤ) ≤ e z + D z := by
      simp only [hedef]
      omega
    calc (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_num
      _ ≤ ((e z + D z : ℤ) : WithTop ℤ) := by exact_mod_cast hsum
      _ = ((e z : ℤ) : WithTop ℤ) + ((D z : ℤ) : WithTop ℤ) := by norm_cast
  set G : ℂ → ℂ := toMeromorphicNFOn (q * F) V with hGdef
  have hGnf : MeromorphicNFOn G V := meromorphicNFOn_toMeromorphicNFOn _ _
  have hGdiv : MeromorphicOn.divisor G V = MeromorphicOn.divisor (q * F) V :=
    (MeromorphicOn.divisor_congr_codiscreteWithin
      (toMeromorphicNFOn_eqOn_codiscrete hqF) hVopen).symm
  have hGnonneg : 0 ≤ MeromorphicOn.divisor G V := by
    intro z
    rw [hGdiv]
    by_cases hz : z ∈ V
    · rw [hqF.divisor_apply hz]
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
      exact WithTop.untop₀_nonneg.2 (hordernonneg z hz)
    · simp [hz]
  have hGana : AnalyticOnNhd ℂ G V := hGnf.divisor_nonneg_iff_analyticOnNhd.1 hGnonneg
  -- the Taylor coefficients on the disc
  have hsub : Metric.closedBall (2 : ℂ) (ρ + 1 / 2) ⊆ V :=
    Metric.closedBall_subset_ball (by linarith)
  have hGdiff : DifferentiableOn ℂ G (Metric.closedBall (2 : ℂ) (ρ + 1 / 2)) :=
    (hGana.mono hsub).differentiableOn
  obtain ⟨c, B', hcbound, hcsum⟩ := exists_seriesSum_of_differentiableOn
    (z₀ := (2 : ℂ)) (R := ρ + 1 / 2) (by linarith) hGdiff (r := ρ) hρpos (by linarith)
  -- the roots
  set S : Finset ℂ := hDfin.toFinset.filter (fun z => D z < 0) with hSdef
  obtain ⟨d, v, hvmem, hvprod⟩ := exists_root_vector S (fun z => (e z).toNat)
  have hqeval : ∀ s : ℂ, q s = ∏ z ∈ S, (s - z) ^ (e z).toNat := by
    intro s
    have hfun := Function.FactorizedRational.finprod_eq_fun (d := e) hefin
    have hq1 : q s = ∏ᶠ a : ℂ, (s - a) ^ e a := by
      rw [hqdef, hfun]
    rw [hq1]
    have hsupp : (Function.mulSupport fun a : ℂ => (s - a) ^ e a) ⊆ (S : Set ℂ) := by
      intro a ha
      simp only [Function.mem_mulSupport] at ha
      by_contra hnot
      have hea : e a = 0 := by
        by_contra hne
        refine hnot ?_
        simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq, Set.Finite.mem_toFinset]
        refine ⟨?_, ?_⟩
        · exact hesupp (by simpa [Function.mem_support] using hne)
        · simp only [hedef, neg_ne_zero] at hne
          omega
      rw [hea] at ha
      simp at ha
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
    refine Finset.prod_congr rfl fun z _ => ?_
    have htn : ((e z).toNat : ℤ) = e z := Int.toNat_of_nonneg (hennoneg z)
    conv_lhs => rw [← htn]
    rw [zpow_natCast]
  refine ⟨⌈B'⌉₊, d, fun i => v i - 2, c, ?_, ?_, ?_⟩
  · -- the roots lie in the admissible box
    intro i
    have hvi := hvmem i
    simp only [hSdef, Finset.mem_filter, Set.Finite.mem_toFinset] at hvi
    have hvV : v i ∈ V := by
      have := hvi.1
      have hsupp : Function.support D ⊆ V := by
        intro z hz
        by_contra hzV
        simp only [hDdef, Function.mem_support] at hz
        exact hz (by simp [hzV])
      exact hsupp this
    constructor
    · have : ‖v i - 2‖ < ρ + 1 := by
        simpa [hVdef, Metric.mem_ball, dist_eq_norm] using hvV
      linarith
    · -- a pole cannot lie in the half plane of absolute convergence
      by_contra hre
      rw [not_le] at hre
      have hre1 : 1 < (v i).re := by
        have : (v i - 2).re = (v i).re - 2 := by simp
        simp only [Complex.sub_re] at hre
        norm_num at hre
        linarith
      have hana := hFana (v i) hre1
      have hnonneg : 0 ≤ meromorphicOrderAt F (v i) := hana.meromorphicOrderAt_nonneg
      have : 0 ≤ D (v i) := by
        rw [hDdef]
        simp only
        rw [hFV.divisor_apply hvV]
        exact WithTop.untop₀_nonneg.2 hnonneg
      exact absurd hvi.2 (not_lt.2 this)
  · -- the coefficient bound
    intro n
    exact le_trans (hcbound n) (Nat.le_ceil B')
  · -- the certificate identity
    intro s hsnorm hsre
    have hsV : s ∈ V := by
      simp only [hVdef, Metric.mem_ball, dist_eq_norm]
      linarith
    have hq : rootPoly (fun i => v i - 2) (s - 2) = q s := by
      rw [rootPoly, hqeval s, ← hvprod s, rootPoly]
      refine Finset.prod_congr rfl fun i _ => ?_
      ring
    have hana : AnalyticAt ℂ (q * F) s := (hqana s).mul (hFana s hsre)
    have hGs : G s = q s * F s := by
      rw [hGdef, toMeromorphicNFOn_eq_toMeromorphicNFAt hqF hsV,
        toMeromorphicNFAt_eq_self.2 hana.meromorphicNFAt]
      rfl
    have hseries : G (2 + (s - 2)) = seriesSum c (s - 2) := by
      refine hcsum (s - 2) ?_
      linarith
    rw [hq, hFeq s hsre]
    rw [show (2 : ℂ) + (s - 2) = s by ring] at hseries
    rw [← hseries, hGs]

end GaloisForLFunctions.HTGeometry

end
