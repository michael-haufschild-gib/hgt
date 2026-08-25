import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCubicResidual
import GaloisForLFunctions.HTGeometry.StretchedExponentialFiniteDifference

/-!
# Cold all-order prime/Gamma wall Malgrange jets

Cold prime-2 Stokes condensation kills every fixed complete Fredholm coefficient above order one.
Faà di Bruno then shows that every non-atomic logarithmic-jet partition vanishes: only the atomic
partition survives, so the wall log germ converges jetwise to `log (1 + c z)`. Subtracting the
canonical Xi seam jet gives the exact all-order Malgrange correction sequence after first-jet
normalization.

This is a fixed-jet theorem. It never interchanges the cold limit with the infinite Fredholm
series and introduces no fitted correction parameter.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower

noncomputable section

private def complexLogJet (j : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) * (z ^ (j + 1))⁻¹

private theorem hasDerivAt_complexLogJet (j : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (complexLogJet j) (complexLogJet (j + 1) z) z := by
  have hbase : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have hpow := hbase.pow (j + 1)
  have hinv := hpow.inv (pow_ne_zero _ hz)
  have hscaled := hinv.const_mul ((-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ))
  apply hscaled.congr_deriv
  rw [complexLogJet]
  push_cast [Nat.factorial_succ]
  simp only [Pi.pow_apply]
  field_simp [hz]
  ring

private theorem iteratedDeriv_complexLog_of_mem_slitPlane (j : ℕ) :
    ∀ {z : ℂ}, z ∈ Complex.slitPlane →
      iteratedDeriv (j + 1) Complex.log z = complexLogJet j z := by
  induction j with
  | zero =>
      intro z hz
      rw [iteratedDeriv_one, (Complex.hasDerivAt_log hz).deriv]
      simp [complexLogJet]
  | succ j ih =>
      intro z hz
      have hlocal : iteratedDeriv (j + 1) Complex.log =ᶠ[𝓝 z]
          complexLogJet j := by
        filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
        exact ih hw
      rw [iteratedDeriv_succ, hlocal.deriv_eq,
        (hasDerivAt_complexLogJet j (Complex.slitPlane_ne_zero hz)).deriv]

private theorem iteratedDeriv_complexLog_one_of_pos (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n Complex.log 1 =
      (-1 : ℂ) ^ (n - 1) * (((n - 1).factorial : ℕ) : ℂ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [iteratedDeriv_complexLog_of_mem_slitPlane j Complex.one_mem_slitPlane]
  simp [complexLogJet]

private theorem tendsto_finset_sum_complex
    {α ι : Type*} [DecidableEq ι] {l : Filter α}
    (s : Finset ι) (f : ι → α → ℂ) (a : ι → ℂ)
    (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) l (𝓝 (∑ i ∈ s, a i)) := by
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℂ)) l (𝓝 0))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      simpa [Finset.sum_insert hi] using (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem tendsto_scaledTau_jet_of_pos (c : ℂ) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun d : ℝ => iteratedDeriv k
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0)
      atTop (𝓝 (if k = 1 then c else 0)) := by
  by_cases hk1 : k = 1
  · subst k
    simp only [if_pos]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
    rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_of_pos
      d c 1 (by norm_num),
      routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_one hd]
    norm_num
  · have hk2 : 2 ≤ k := by omega
    have hcoeff :=
      tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_atTop_of_two_le
        hk2
    have hconst : Tendsto (fun _ : ℝ =>
        ((k.factorial : ℕ) : ℂ) * c ^ k) atTop
        (𝓝 (((k.factorial : ℕ) : ℂ) * c ^ k)) := tendsto_const_nhds
    have hmul := hconst.mul hcoeff
    simp only [if_neg hk1]
    convert hmul using 1
    · funext d
      rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_of_pos
        d c k hk]
    · simp

private theorem tendsto_scaledTau_partition_product
    {n : ℕ} (c : ℂ) (p : OrderedFinpartition n) :
    Tendsto (fun d : ℝ => ∏ j : Fin p.length,
      iteratedDeriv (p.partSize j)
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0)
      atTop (𝓝 (∏ j : Fin p.length, if p.partSize j = 1 then c else 0)) := by
  classical
  have hprod : ∀ s : Finset (Fin p.length),
      Tendsto (fun d : ℝ => ∏ j ∈ s,
        iteratedDeriv (p.partSize j)
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0)
        atTop (𝓝 (∏ j ∈ s, if p.partSize j = 1 then c else 0)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj]
        simpa [Finset.prod_insert hj] using
          (tendsto_scaledTau_jet_of_pos c (p.partSize j) (p.partSize_pos j)).mul ih
  simpa only [Finset.prod_attach] using hprod Finset.univ

private theorem orderedFinpartition_limit_product
    {n : ℕ} (c : ℂ) (p : OrderedFinpartition n) :
    (∏ j : Fin p.length, if p.partSize j = 1 then c else 0) =
      if p = OrderedFinpartition.atomic n then c ^ n else 0 := by
  classical
  by_cases hp : p = OrderedFinpartition.atomic n
  · rw [if_pos hp]
    have hlen : p.length = n := by simp [hp]
    simp_rw [p.partSize_eq_one_of_length_eq hlen]
    simp [hlen]
  · rw [if_neg hp]
    have hex : ∃ j : Fin p.length, p.partSize j ≠ 1 := by
      by_contra h
      push Not at h
      have hcard : ∑ j : Fin p.length, p.partSize j = n := by
        simpa only [Fintype.card_sigma, Fintype.card_fin] using
          Fintype.card_congr p.equivSigma
      have hlen : p.length = n := by simpa [h] using hcard
      exact hp (p.eq_atomic_of_length_eq hlen)
    obtain ⟨j, hj⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private theorem iteratedDeriv_scaledTauLog_eq_partition_sum
    (d : ℝ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n
        (fun z => Complex.log
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) 0 =
      ∑ p : OrderedFinpartition n,
        iteratedDeriv p.length Complex.log 1 *
          ∏ j : Fin p.length,
            iteratedDeriv (p.partSize j)
              (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0 := by
  have hlogAnalytic : AnalyticAt ℂ Complex.log 1 := by
    simpa using (analyticAt_id.clog Complex.one_mem_slitPlane)
  have hwallAnalytic : AnalyticAt ℂ
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0 :=
    (differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c).analyticAt 0
  have hlogDiff : ContDiffAt ℂ ⊤ Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c 0) := by
    rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
    exact hlogAnalytic.contDiffAt
  rw [show (fun z => Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) =
      Complex.log ∘ routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c by rfl]
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    hlogDiff hwallAnalytic.contDiffAt le_top,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]

/-- Cold prime-2 Stokes condensation makes every fixed positive wall log jet equal in the limit
to the corresponding jet of `log (1 + c z)`. -/
theorem tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_atTop
    (c : ℂ) (n : ℕ) (hn : 0 < n) :
    Tendsto (fun d : ℝ => iteratedDeriv n
      (fun z => Complex.log
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) 0)
      atTop (𝓝 ((-1 : ℂ) ^ (n - 1) *
        (((n - 1).factorial : ℕ) : ℂ) * c ^ n)) := by
  classical
  let target : ℂ := (-1 : ℂ) ^ (n - 1) *
    (((n - 1).factorial : ℕ) : ℂ) * c ^ n
  have hterm (p : OrderedFinpartition n) :
      Tendsto (fun d : ℝ =>
        iteratedDeriv p.length Complex.log 1 *
          ∏ j : Fin p.length,
            iteratedDeriv (p.partSize j)
              (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0)
        atTop (𝓝 (if p = OrderedFinpartition.atomic n then target else 0)) := by
    have hp := tendsto_scaledTau_partition_product c p
    have hconst : Tendsto (fun _ : ℝ => iteratedDeriv p.length Complex.log 1)
        atTop (𝓝 (iteratedDeriv p.length Complex.log 1)) := tendsto_const_nhds
    have hmul := hconst.mul hp
    convert hmul using 1
    rw [orderedFinpartition_limit_product]
    by_cases hpa : p = OrderedFinpartition.atomic n
    · rw [if_pos hpa]
      subst p
      simp only [OrderedFinpartition.atomic_length]
      rw [iteratedDeriv_complexLog_one_of_pos n hn]
      rfl
    · simp [hpa]
  have hsum := tendsto_finset_sum_complex Finset.univ
    (fun p : OrderedFinpartition n => fun d : ℝ =>
      iteratedDeriv p.length Complex.log 1 *
        ∏ j : Fin p.length,
          iteratedDeriv (p.partSize j)
            (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0)
    (fun p => if p = OrderedFinpartition.atomic n then target else 0)
    (fun p _ => hterm p)
  have hlimit : (∑ p : OrderedFinpartition n,
      if p = OrderedFinpartition.atomic n then target else 0) = target := by
    rw [Finset.sum_eq_single (OrderedFinpartition.atomic n)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards with d
  exact (iteratedDeriv_scaledTauLog_eq_partition_sum d c n).symm

/-- Exact conversion from canonical seam-moment normalization to every positive Xi log jet. -/
theorem iteratedDeriv_canonicalXiSeamLog_succ (n : ℕ) :
    iteratedDeriv (n + 1) canonicalXiSeamLog 0 =
      (-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) / 2 *
        (normalizedPrimeArchMoment n : ℂ) := by
  have h := canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment n
  unfold canonicalXiSeamLogMoment canonicalXiSeamLogCoeff seamLogCoeff at h
  push_cast [Nat.factorial_succ] at h
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn] at h
  rw [pow_succ] at h
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have h' :
      2 * (-1 : ℂ) ^ n * iteratedDeriv (n + 1) canonicalXiSeamLog 0 /
          ((n.factorial : ℕ) : ℂ) = (normalizedPrimeArchMoment n : ℂ) := by
    calc
      _ = -(2 * ((-1 : ℂ) ^ n * -1) *
          iteratedDeriv (n + 1) canonicalXiSeamLog 0 /
            ((n.factorial : ℕ) : ℂ)) := by ring
      _ = _ := h
  have hmul :
      2 * (-1 : ℂ) ^ n * iteratedDeriv (n + 1) canonicalXiSeamLog 0 =
        (normalizedPrimeArchMoment n : ℂ) * ((n.factorial : ℕ) : ℂ) :=
    (div_eq_iff hfac).mp h'
  have hcore :
      (-1 : ℂ) ^ n * iteratedDeriv (n + 1) canonicalXiSeamLog 0 =
        ((n.factorial : ℕ) : ℂ) * (normalizedPrimeArchMoment n : ℂ) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    linear_combination hmul
  calc
    iteratedDeriv (n + 1) canonicalXiSeamLog 0 =
        ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
          iteratedDeriv (n + 1) canonicalXiSeamLog 0 := by
            rw [← mul_pow]
            norm_num
    _ = (-1 : ℂ) ^ n *
        (((n.factorial : ℕ) : ℂ) * (normalizedPrimeArchMoment n : ℂ) / 2) := by
          rw [mul_assoc, hcore]
    _ = (-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) / 2 *
        (normalizedPrimeArchMoment n : ℂ) := by ring

/-- Full cold irregular-RH correction sequence after the forced Xi first-jet scaling. -/
theorem tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_atTop
    (n : ℕ) :
    Tendsto (fun d : ℝ => iteratedDeriv (n + 1)
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0)
      atTop (𝓝 ((-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) *
        ((normalizedPrimeArchMoment n : ℂ) / 2 -
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ (n + 1)))) := by
  have hwall :=
    tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_atTop
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale (n + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hwall
  have hXi : Tendsto (fun _ : ℝ =>
      (-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) / 2 *
        (normalizedPrimeArchMoment n : ℂ)) atTop
      (𝓝 ((-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) / 2 *
        (normalizedPrimeArchMoment n : ℂ))) := tendsto_const_nhds
  have hraw := hXi.sub hwall
  have hlimit :
      (-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) / 2 *
          (normalizedPrimeArchMoment n : ℂ) -
        (-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) *
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ (n + 1) =
      (-1 : ℂ) ^ n * ((n.factorial : ℕ) : ℂ) *
        ((normalizedPrimeArchMoment n : ℂ) / 2 -
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ (n + 1)) := by ring
  rw [hlimit] at hraw
  refine hraw.congr' ?_
  filter_upwards with d
  have hXiDiff : ContDiffAt ℂ (n + 1) canonicalXiSeamLog 0 :=
    analyticAt_canonicalXiSeamLog.contDiffAt
  have hwallDiff : ContDiffAt ℂ (n + 1)
      (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
    have hanalytic : AnalyticAt ℂ
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
      apply ((differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale).analyticAt 0).clog
      rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
      exact Complex.one_mem_slitPlane
    exact hanalytic.contDiffAt
  symm
  change iteratedDeriv (n + 1)
    (canonicalXiSeamLog - fun z => Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 = _
  rw [iteratedDeriv_sub hXiDiff hwallDiff, iteratedDeriv_canonicalXiSeamLog_succ]

end

end RHTower
