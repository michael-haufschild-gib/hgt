import GaloisForLFunctions.RHTower.ZetaTwistedDirichletHeadsNearAZeroHaveVanishingHaarMass
import GaloisForLFunctions.RHTower.ZetaPartialSumIsolatedZeroHeightsAndUniformPairReturns
import GaloisForLFunctions.RHTower.ZetaTypicalHeightDiscSupTailLawAndOrbitPrecompactness

/-!
# Twisted Dirichlet heads approximate `ζ` with positive Haar mass iff the disc is zero-free

For a strip disc `D = closedBall z₀ r` with doubled closure in the strip and a tolerance `ε`,
`twistedHeadPhaseSet M D ε` is the open set of prime phases `ω` under which the twisted Dirichlet
head of length `M` is within `ε` of `ζ` on `D`.  Its Haar mass is the probability that a random
completely multiplicative twist of the head reproduces `ζ` on the disc.

* **Zero-free discs: mass bounded below** (`exists_pos_forall_eventually_torusHaar_twistedHeadPhaseSet_ge`).
  Strong recurrence gives head-target heights of lower density `≥ c` uniformly in long heads; a
  Urysohn function `ψ` with `1_{U(ε/2)} ≤ ψ ≤ 1_{U(ε)}` on the prime torus turns the visit density
  into the Haar integral of `ψ` by the Kronecker–Weyl limit law, so `Haar(U(ε)) ≥ c`.
* **Discs with a zero: explicit decay** (`torusHaar_twistedHeadPhaseSet_le_tailMass`).  Below the
  self-return threshold `d`, `Haar(U_M(ε)) ≤ 28 K ε'^{−2} · tailMass(M, Re z₀ − 2r)` with
  `ε' = (d − ε)/2`, `K = (1 + r/(1 − Re z₀ − 2r))²` and `tailMass(M, σ) = Σ_{n > M} n^{−2σ}`,
  which is `≤ C (M+1)^{1 − 2(Re z₀ − 2r)}`: the approximation probability decays like the
  Carlson tail mass of the head.
* **The Riemann hypothesis** (`riemannHypothesis_iff_forall_twistedHeadPhaseSet_haar_pos`): RH holds
  iff on every strip disc with doubled closure in the strip and for every tolerance, the Haar mass
  of the approximating twists of long heads is bounded below by a positive constant.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## 1. A Urysohn function between two approximation sets -/

/-- The closed set of phases whose twisted head is within `ε` of `ζ` on `K` (non-strictly). -/
theorem isClosed_twistedHead_le_set (M : ℕ) (K : Set ℂ) (ε : ℝ) :
    IsClosed {ω : Nat.Primes → Circle | ∀ z ∈ K, ‖twistedDirichletHead M ω z - riemannZeta z‖ ≤ ε} := by
  have : {ω : Nat.Primes → Circle | ∀ z ∈ K, ‖twistedDirichletHead M ω z - riemannZeta z‖ ≤ ε}
      = ⋂ z ∈ K, {ω | ‖twistedDirichletHead M ω z - riemannZeta z‖ ≤ ε} := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter]
  rw [this]
  refine isClosed_biInter fun z _ => isClosed_le ?_ continuous_const
  exact (((continuous_twistedDirichletHead_prod M).comp
    (continuous_id.prodMk continuous_const)).sub continuous_const).norm

/-- A continuous `ψ : torus → [0, 1]` with `ψ = 1` where the twisted head is within `ε/2` of `ζ`
and `ψ = 0` where it is not within `ε`. -/
theorem exists_urysohn_twistedHeadPhaseSet (M : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hre : ∀ z ∈ K, z ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : C((Nat.Primes → Circle), ℝ), (∀ ω, ψ ω ∈ Icc (0 : ℝ) 1) ∧
      (∀ ω ∈ twistedHeadPhaseSet M K (ε / 2), ψ ω = 1) ∧
      (∀ ω ∉ twistedHeadPhaseSet M K ε, ψ ω = 0) := by
  obtain ⟨ψ, h0, h1, h01⟩ := exists_continuous_zero_one_of_isClosed
    (isOpen_twistedHeadPhaseSet M hK hre ε).isClosed_compl (isClosed_twistedHead_le_set M K (ε / 2))
    (by
      rw [Set.disjoint_left]
      intro ω hω hωC
      exact hω fun z hz => (hωC z hz).trans_lt (half_lt_self hε))
  refine ⟨ψ, h01, fun ω hω => h1 fun z hz => (hω z hz).le, fun ω hω => h0 hω⟩

/-! ## 2. Visit densities bound the Haar mass from below -/

/-- **Haar mass dominates the visit density.**  If the prime phase flow visits the `ε/2`-approximating
phases of a fixed head with lower density `≥ c`, then the `ε`-approximating phases have Haar
mass `≥ c`. -/
theorem le_torusHaar_twistedHeadPhaseSet_of_density (M : ℕ) {z₀ : ℂ} {r ε c : ℝ}
    (h1 : z₀.re + r < 1) (hε : 0 < ε)
    (hvisit : ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (c * T) ≤
      volume (headTargetReturnSet M (closedBall z₀ r) (ε / 2) ∩ Icc 0 T)) :
    c ≤ (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
      twistedHeadPhaseSet M (closedBall z₀ r) ε)).toReal := by
  obtain ⟨ψ, hψ01, hψ1, hψ0⟩ := exists_urysohn_twistedHeadPhaseSet M (isCompact_closedBall z₀ r)
    (fun z hz => ne_one_of_mem_closedBall_of_lt h1 hz) hε
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ,
      S = circlePhaseFlow primeFrequency ⁻¹' twistedHeadPhaseSet M (closedBall z₀ r) (ε / 2) :=
    ⟨_, rfl⟩
  have hSopen : IsOpen S := by
    rw [hS]
    exact (isOpen_twistedHeadPhaseSet M (isCompact_closedBall z₀ r)
      (fun z hz => ne_one_of_mem_closedBall_of_lt h1 hz) (ε / 2)).preimage
      (continuous_circlePhaseFlow _)
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  rw [headTargetReturnSet_eq_preimage, ← hS] at hvisit
  have hcont : Continuous fun τ : ℝ => ψ (circlePhaseFlow primeFrequency τ) :=
    ψ.continuous.comp (continuous_circlePhaseFlow _)
  -- the window average of `ψ` along the flow dominates the visit proportion
  have hlow : ∀ᶠ T : ℝ in atTop,
      c ≤ T⁻¹ * ∫ τ in (0 : ℝ)..T, ψ (circlePhaseFlow primeFrequency τ) := by
    filter_upwards [hvisit, eventually_gt_atTop 0] with T hT hT0
    have hfin : volume (S ∩ Ioc 0 T) ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne
    have hIcc : volume (S ∩ Icc 0 T) ≤ volume (S ∩ Ioc 0 T) := by
      calc volume (S ∩ Icc 0 T) ≤ volume (S ∩ Ioc 0 T ∪ {0}) := by
            refine measure_mono fun x ⟨hxS, hx⟩ => ?_
            rcases eq_or_lt_of_le hx.1 with h | h
            · exact Or.inr (by rw [← h]; rfl)
            · exact Or.inl ⟨hxS, h, hx.2⟩
        _ ≤ volume (S ∩ Ioc 0 T) + volume ({0} : Set ℝ) := measure_union_le _ _
        _ = volume (S ∩ Ioc 0 T) := by rw [Real.volume_singleton, add_zero]
    have hcT : c * T ≤ (volume (S ∩ Ioc 0 T)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin).mp (hT.trans hIcc)
    have hind : ∫ τ in (0 : ℝ)..T, S.indicator (fun _ => (1 : ℝ)) τ
        = (volume (S ∩ Ioc 0 T)).toReal := by
      rw [intervalIntegral.integral_of_le hT0.le, integral_indicator hSmeas, setIntegral_const,
        smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply' measurableSet_Ioc]
    have hmono : ∫ τ in (0 : ℝ)..T, S.indicator (fun _ => (1 : ℝ)) τ ≤
        ∫ τ in (0 : ℝ)..T, ψ (circlePhaseFlow primeFrequency τ) := by
      refine intervalIntegral.integral_mono_on hT0.le ?_ (hcont.intervalIntegrable _ _)
        fun τ _ => ?_
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le).mpr
          ((integrableOn_const measure_Ioc_lt_top.ne).indicator hSmeas)
      · by_cases hτ : τ ∈ S
        · rw [Set.indicator_of_mem hτ]
          exact (hψ1 _ (by rw [hS] at hτ; exact hτ)).ge
        · rw [Set.indicator_of_notMem hτ]
          exact (hψ01 _).1
    calc c = T⁻¹ * (c * T) := by field_simp
      _ ≤ T⁻¹ * (volume (S ∩ Ioc 0 T)).toReal := by gcongr
      _ = T⁻¹ * ∫ τ in (0 : ℝ)..T, S.indicator (fun _ => (1 : ℝ)) τ := by rw [hind]
      _ ≤ _ := by gcongr
  -- pass to the Haar integral by the Kronecker–Weyl law, then compare with the indicator
  have hlim := ge_of_tendsto (tendsto_windowAverage_primeFlow_real ψ) hlow
  obtain ⟨V, hV⟩ : ∃ V : Set (UnitAddTorus Nat.Primes), V = unitTorusHomeomorphCircles Nat.Primes ⁻¹'
      twistedHeadPhaseSet M (closedBall z₀ r) ε := ⟨_, rfl⟩
  have hVmeas : MeasurableSet V := by
    rw [hV]
    exact ((isOpen_twistedHeadPhaseSet M (isCompact_closedBall z₀ r)
      (fun z hz => ne_one_of_mem_closedBall_of_lt h1 hz) ε).preimage
      (unitTorusHomeomorphCircles Nat.Primes).continuous).measurableSet
  have hψint : Integrable (fun x => ψ (unitTorusHomeomorphCircles Nat.Primes x))
      (torusHaar Nat.Primes) :=
    (ψ.continuous.comp (unitTorusHomeomorphCircles Nat.Primes).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hle : ∫ x, ψ (unitTorusHomeomorphCircles Nat.Primes x) ∂(torusHaar Nat.Primes) ≤
      ∫ x, V.indicator (fun _ => (1 : ℝ)) x ∂(torusHaar Nat.Primes) := by
    refine integral_mono hψint ((integrable_const (1 : ℝ)).indicator hVmeas) fun x => ?_
    by_cases hx : unitTorusHomeomorphCircles Nat.Primes x ∈
        twistedHeadPhaseSet M (closedBall z₀ r) ε
    · rw [Set.indicator_of_mem (by rw [hV]; exact hx)]
      exact (hψ01 _).2
    · rw [Set.indicator_of_notMem (by rw [hV]; exact hx), hψ0 _ hx]
  rw [integral_indicator hVmeas, setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at hle
  rw [← hV]
  exact hlim.trans hle

/-- **Zero-free discs: the approximating twists have Haar mass bounded below.**  If `ζ` has no
zero in the open disc (doubled closure in the strip), then for every `ε > 0` there is `c > 0`
with `Haar(twistedHeadPhaseSet M D ε) ≥ c` for all long heads. -/
theorem exists_pos_forall_eventually_torusHaar_twistedHeadPhaseSet_ge {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1)
    (hζ : ∀ z ∈ ball z₀ r, riemannZeta z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ M : ℕ in atTop, c ≤ (torusHaar Nat.Primes
      (unitTorusHomeomorphCircles Nat.Primes ⁻¹' twistedHeadPhaseSet M (closedBall z₀ r) ε)).toReal := by
  have hrec : ZetaDiscStronglyRecurrentOn (closedBall z₀ r) :=
    (zetaDiscStronglyRecurrentOn_iff_forall_ball_ne_zero hr h0 h1).mpr hζ
  obtain ⟨c, hc, hM⟩ := headTargetUniformlyDense_of_zetaDiscStronglyRecurrentOn_of_lt
    (show r < 2 * r by linarith) h0 h1 hrec (ε / 2) (half_pos hε)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hM] with M hT
  exact le_torusHaar_twistedHeadPhaseSet_of_density M (by linarith) hε hT

/-! ## 3. Explicit decay of the Haar mass below the threshold -/

/-- **Explicit decay near a zero.**  Below the self-return threshold `d`, the Haar mass of the
`ε`-approximating twists of the length-`M` head is at most
`28 K ε'^{−2} · tailMass(M, Re z₀ − 2r)`, `ε' = (d − ε)/2`, `K = (1 + r/(1 − Re z₀ − 2r))²`. -/
theorem torusHaar_twistedHeadPhaseSet_le_tailMass {z₀ : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1)
    (hε : ε < zetaNonvanishingDistance z₀ r) (M : ℕ) :
    (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
      twistedHeadPhaseSet M (closedBall z₀ r) ε)).toReal ≤
      28 * (1 + r / (1 - (z₀.re + 2 * r))) ^ 2 / ((zetaNonvanishingDistance z₀ r - ε) / 2) ^ 2 *
        zetaCoefficientTailMass M (z₀.re - 2 * r) := by
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = (zetaNonvanishingDistance z₀ r - ε) / 2 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  have hsum : ε' + ε < zetaNonvanishingDistance z₀ r := by rw [hε']; linarith
  rw [← hε']
  obtain ⟨θ, hθ, T₀, hT₀⟩ := exists_volume_zetaReturnSet_le_rpow_of_lt_distance hr
    (by linarith) (by linarith) hsum
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 28 * (1 + r / (1 - (z₀.re + 2 * r))) ^ 2 / ε' ^ 2 *
      zetaCoefficientTailMass M (z₀.re - 2 * r) := ⟨_, rfl⟩
  rw [← hB]
  refine le_of_forall_pos_lt_add fun κ hκ => ?_
  by_contra hcon
  push Not at hcon
  have hκ4 : 0 < κ / 4 := by positivity
  have hvisit := eventually_ofReal_mul_le_volume_preimage_primeFlow
    (isOpen_twistedHeadPhaseSet M (isCompact_closedBall z₀ r)
      (fun z hz => ne_one_of_mem_closedBall_of_lt (by linarith) hz) ε)
    (show B + κ / 2 < _ by linarith)
  rw [← headTargetReturnSet_eq_preimage] at hvisit
  have hbad := eventually_volume_discTailBadSet_le_tailMass M hr h0 h1 hε'0 hκ4
  have hsub : headTargetReturnSet M (closedBall z₀ r) ε ⊆
      discTailBadSet M z₀ r ε' ∪ zetaReturnSet (closedBall z₀ r) (ε' + ε) := by
    intro τ hτ
    by_cases hb : τ ∈ discTailBadSet M z₀ r ε'
    · exact Or.inl hb
    · exact Or.inr
        (headTargetReturnSet_diff_discTailBadSet_subset_zetaReturnSet M z₀ r ε ε' ⟨hτ, hb⟩)
  obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ := (hvisit.and (hbad.and ((eventually_ge_atTop T₀).and
    ((eventually_rpow_lt_const_mul_atTop hθ hκ4).and (eventually_ge_atTop 0))))).exists
  have hle : volume (headTargetReturnSet M (closedBall z₀ r) ε ∩ Icc 0 T) ≤
      ENNReal.ofReal ((B + κ / 4) * T) + ENNReal.ofReal (T ^ θ) := by
    calc volume (headTargetReturnSet M (closedBall z₀ r) ε ∩ Icc 0 T)
        ≤ volume (discTailBadSet M z₀ r ε' ∩ Icc 0 T ∪
            zetaReturnSet (closedBall z₀ r) (ε' + ε) ∩ Icc 0 T) := by
          refine measure_mono ?_
          rw [← Set.union_inter_distrib_right]
          exact inter_subset_inter_left _ hsub
      _ ≤ _ := by
          refine (measure_union_le _ _).trans (add_le_add ?_ (hT₀ T hT3))
          refine hT2.trans (ENNReal.ofReal_le_ofReal ?_)
          rw [hB]
  have h := hT1.trans hle
  have hTθ : 0 ≤ T ^ θ := Real.rpow_nonneg hT5 θ
  have hB0 : 0 ≤ B := by
    rw [hB]
    have := zetaCoefficientTailMass_nonneg M (z₀.re - 2 * r)
    positivity
  rw [← ENNReal.ofReal_add (by positivity) hTθ,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith

/-- The explicit decay rate: the Haar mass is `O((M + 1)^{1 − 2(Re z₀ − 2r)})`. -/
theorem torusHaar_twistedHeadPhaseSet_le_rpow {z₀ : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1)
    (hε : ε < zetaNonvanishingDistance z₀ r) (M : ℕ) :
    (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
      twistedHeadPhaseSet M (closedBall z₀ r) ε)).toReal ≤
      28 * (1 + r / (1 - (z₀.re + 2 * r))) ^ 2 / ((zetaNonvanishingDistance z₀ r - ε) / 2) ^ 2 *
        (2 * (z₀.re - 2 * r) / (2 * (z₀.re - 2 * r) - 1) *
          ((M : ℝ) + 1) ^ (1 - 2 * (z₀.re - 2 * r))) := by
  refine (torusHaar_twistedHeadPhaseSet_le_tailMass hr h0 h1 hε M).trans ?_
  have hL : 0 < 1 - (z₀.re + 2 * r) := by linarith
  have hd : 0 < (zetaNonvanishingDistance z₀ r - ε) / 2 := by linarith
  exact mul_le_mul_of_nonneg_left (zetaCoefficientTailMass_le M h0) (by positivity)

/-! ## 4. The Riemann hypothesis as a Haar-mass law for twisted heads -/

/-- **RH is positivity of the Haar mass of approximating twists on every disc.**  The Riemann
hypothesis holds iff for every strip disc with doubled closure in the strip and every `ε > 0`,
the Haar mass of the prime phases under which the twisted head of length `M` is within `ε` of
`ζ` on the disc is bounded below by a positive constant for all long heads. -/
theorem riemannHypothesis_iff_forall_twistedHeadPhaseSet_haar_pos :
    RiemannHypothesis ↔ ∀ (z₀ : ℂ) (r : ℝ), 0 < r → 1 / 2 < z₀.re - 2 * r → z₀.re + 2 * r < 1 →
      ∀ ε > 0, ∃ c > 0, ∀ᶠ M : ℕ in atTop, c ≤ (torusHaar Nat.Primes
        (unitTorusHomeomorphCircles Nat.Primes ⁻¹' twistedHeadPhaseSet M (closedBall z₀ r) ε)).toReal := by
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro hRH z₀ r hr h0 h1 ε hε
    refine exists_pos_forall_eventually_torusHaar_twistedHeadPhaseSet_ge hr h0 h1
      (fun z hz => hRH z ?_ ?_) hε
    · have := (abs_lt.mp ((abs_re_le_norm (z - z₀)).trans_lt (mem_ball_iff_norm.mp hz))).1
      rw [sub_re] at this
      linarith
    · have := (abs_lt.mp ((abs_re_le_norm (z - z₀)).trans_lt (mem_ball_iff_norm.mp hz))).2
      rw [sub_re] at this
      linarith
  · intro hall s hs1 hs2 hs0
    obtain ⟨r, hr0, ⟨h0, h1⟩, ε, hε, hdecay⟩ :=
      exists_eventually_torusHaar_twistedHeadPhaseSet_le_of_zero hs0 hs1 hs2
    obtain ⟨c, hc, hM⟩ := hall s r hr0 h0 h1 ε hε
    obtain ⟨M, hM1, hM2⟩ := (hM.and (hdecay (c / 2) (half_pos hc))).exists
    linarith

end

end RHTower
