import GaloisForLFunctions.RHTower.LiEvenCrossCassiniAllMassPole
import GaloisForLFunctions.HTGeometry.VivantiPringsheim
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Cofinal sign oscillation of the actual LI logarithmic-mass jets

For every positive mass, the even Cassini logarithmic-mass germ has real canonical
Taylor coefficients of both signs arbitrarily far out.  Its actual retained pole
forces a finite Taylor radius, while its analytic positive real ray rules out
both eventual coefficient orientations by Vivanti--Pringsheim.  The finite-tail
argument retains the full analytic germ and does not assume a radius or a
continuation.  Consequently neither closed all-even jet cone contains this source.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open scoped ENNReal NNReal

namespace RHTower

private theorem eulerJet_meromorphic_germ_propagation
    {f g : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsPreconnected U) (hu : u ∈ U)
    (hseed : f =ᶠ[𝓝[≠] u] g) :
    ∀ z ∈ U, f =ᶠ[𝓝[≠] z] g := by
  have hsub : MeromorphicOn (f - g) U := hf.sub hg
  have htopu : meromorphicOrderAt (f - g) u = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hseed] with z hz using sub_eq_zero.mpr hz
  let S : Set U := {x | meromorphicOrderAt (f - g) x = ⊤}
  have hSclopen : IsClopen S := hsub.isClopen_setOf_meromorphicOrderAt_eq_top
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hSne : S ≠ ∅ := by
    intro hS
    have huS : (⟨u, hu⟩ : U) ∈ S := htopu
    rw [hS] at huS
    exact huS
  have hSuniv : S = Set.univ := (isClopen_iff.mp hSclopen).resolve_left hSne
  intro z hz
  have htopz : meromorphicOrderAt (f - g) z = ⊤ := by
    have hzS : (⟨z, hz⟩ : U) ∈ S := by rw [hSuniv]; trivial
    exact hzS
  rw [eventuallyEq_iff_sub]
  exact meromorphicOrderAt_eq_top_iff.mp htopz

private theorem eulerJet_germ_eq_sum {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0) :
    f =ᶠ[𝓝 0] p.sum := by
  filter_upwards [hp.eventually_hasSum] with z hz
  simpa only [zero_add, FormalMultilinearSeries.sum] using hz.tsum_eq.symm

private theorem eulerJet_radius_ne_top_of_pole {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0)
    (hf : Meromorphic f) (hpole : ∃ z, meromorphicOrderAt f z < 0) :
    p.radius ≠ ⊤ := by
  intro htop
  have hsum : AnalyticOnNhd ℂ p.sum Set.univ := by
    have h := (p.hasFPowerSeriesOnBall hp.radius_pos).analyticOnNhd
    simpa [htop, Metric.eball_top_eq_univ] using h
  have heq := eulerJet_meromorphic_germ_propagation
    (U := Set.univ) (u := 0) hf.meromorphicOn hsum.meromorphicOn
    isPreconnected_univ (Set.mem_univ 0)
    ((eulerJet_germ_eq_sum hp).filter_mono nhdsWithin_le_nhds)
  obtain ⟨z, hz⟩ := hpole
  have heqz := heq z (Set.mem_univ z)
  rw [meromorphicOrderAt_congr heqz] at hz
  exact (not_lt_of_ge (hsum z (Set.mem_univ z)).meromorphicOrderAt_nonneg) hz

private theorem eulerJet_continuesAcross {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p 0)
    (hf : Meromorphic f) {R : ℝ} (hR : 0 < R)
    (hrad : p.radius = ENNReal.ofReal R) (hreal : AnalyticAt ℂ f (R : ℂ)) :
    GaloisForLFunctions.HTGeometry.ContinuesAcross p.sum (Metric.ball 0 R) (R : ℂ) := by
  have hsum : AnalyticOnNhd ℂ p.sum (Metric.ball 0 R) := by
    have h := (p.hasFPowerSeriesOnBall hp.radius_pos).analyticOnNhd
    simpa [hrad] using h
  have heq := eulerJet_meromorphic_germ_propagation
    (U := Metric.ball 0 R) (u := 0) hf.meromorphicOn
    hsum.meromorphicOn (convex_ball (0 : ℂ) R).isPreconnected
    (Metric.mem_ball_self hR)
    ((eulerJet_germ_eq_sum hp).filter_mono nhdsWithin_le_nhds)
  refine ⟨f, hreal, ?_⟩
  filter_upwards [hreal.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hzball
  have hstrong : f =ᶠ[𝓝 z] p.sum :=
    (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hz.continuousAt
      (hsum z hzball).continuousAt).1 (heq z hzball)
  exact hstrong.eq_of_nhds

private theorem eulerJet_nonnegative_impossible {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun n => (a n : ℂ))) 0)
    (hf : Meromorphic f) (hreal : ∀ R : ℝ, 0 ≤ R → AnalyticAt ℂ f (R : ℂ))
    (hfinite : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius ≠ ⊤)
    (ha : ∀ n, 0 ≤ a n) : False := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  let R := p.radius.toReal
  have hR : 0 < R := ENNReal.toReal_pos hp.radius_pos.ne' hfinite
  have hrad : p.radius = ENNReal.ofReal R := (ENNReal.ofReal_toReal hfinite).symm
  have hconv : ∀ s : ℝ, 0 ≤ s → s < R → Summable (fun n => a n * s ^ n) := by
    intro s hs hsR
    let sNN : ℝ≥0 := ⟨s, hs⟩
    have hsrad : (sNN : ℝ≥0∞) < p.radius := by
      rw [hrad, ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg sNN.coe_nonneg |>.mpr hsR
    refine (p.summable_norm_mul_pow (r := sNN) hsrad).congr fun n => ?_
    change ‖p n‖ * (sNN : ℝ) ^ n = a n * s ^ n
    have hn : ‖p n‖ = a n := by
      change ‖FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ)) n‖ = a n
      rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ha n)]
    rw [hn]
    rfl
  have hdiv : ∀ s : ℝ, R < s → ¬ Summable (fun n => a n * s ^ n) := by
    intro s hs hsum
    have hs0 : 0 ≤ s := (hR.trans hs).le
    have hle : ENNReal.ofReal s ≤ p.radius := by
      rw [ENNReal.ofReal_eq_coe_nnreal hs0]
      apply p.le_radius_of_summable_norm
      simpa [p, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
        abs_of_nonneg (ha _)] using hsum
    rw [hrad] at hle
    have : s ≤ R := (ENNReal.ofReal_le_ofReal_iff hR.le).mp hle
    exact (not_le_of_gt hs) this
  have hcontin := eulerJet_continuesAcross hp hf hR hrad (hreal R hR.le)
  have hsumid : p.sum = GaloisForLFunctions.HTGeometry.realSeriesSum a := by
    funext z
    simp [p, FormalMultilinearSeries.sum,
      GaloisForLFunctions.HTGeometry.realSeriesSum, smul_eq_mul, mul_comm]
  rw [hsumid] at hcontin
  exact GaloisForLFunctions.HTGeometry.not_continuesAcross_of_nonneg
    ha hR hconv hdiv hcontin

end RHTower

namespace RHTower

private theorem eulerJet_not_eventually_nonnegative {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun n => (a n : ℂ))) 0)
    (hf : Meromorphic f) (hreal : ∀ R : ℝ, 0 ≤ R → AnalyticAt ℂ f (R : ℂ))
    (hfinite : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius ≠ ⊤) :
    ¬ ∀ᶠ n in atTop, 0 ≤ a n := by
  classical
  intro hnonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnonneg
  let c : ℕ → ℝ := fun n => if n < N then a n else 0
  let b : ℕ → ℝ := fun n => a n - c n
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  let q := FormalMultilinearSeries.ofScalars ℂ (fun n => (c n : ℂ))
  let r := FormalMultilinearSeries.ofScalars ℂ (fun n => (b n : ℂ))
  have hqtop : q.radius = ⊤ := by
    apply q.radius_eq_top_of_eventually_eq_zero
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [q, c, Nat.not_lt.mpr hn]
  have hr : r = p - q := by
    ext n
    simp [r, p, q, b, FormalMultilinearSeries.ofScalars]
  have hrad : r.radius = p.radius := by
    apply le_antisymm
    · have h := (p - q).min_radius_le_radius_add q
      simpa [hqtop, hr, sub_add_cancel] using h
    · have h := p.min_radius_le_radius_add (-q)
      simpa [hqtop, hr, sub_eq_add_neg] using h
  have hqp : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall (by rw [hqtop]; simp)
  have hqsum : AnalyticOnNhd ℂ q.sum Set.univ := by
    simpa [hqtop] using hqp.analyticOnNhd
  have hsubp : HasFPowerSeriesAt (f - q.sum) r 0 := by
    rw [hr]
    exact hp.sub hqp.hasFPowerSeriesAt
  have hb : ∀ n, 0 ≤ b n := by
    intro n
    by_cases hn : n < N
    · simp [b, c, hn]
    · simpa [b, c, hn] using hN n (Nat.le_of_not_gt hn)
  apply eulerJet_nonnegative_impossible hsubp (hf.sub (fun z => (hqsum z (Set.mem_univ z)).meromorphicAt))
      (fun R hR => (hreal R hR).sub (hqsum (R : ℂ) (Set.mem_univ _))) ?_ hb
  change r.radius ≠ ⊤
  rw [hrad]
  exact hfinite

private theorem eulerJet_schwarz_iteratedDeriv {f : ℂ → ℂ}
    (hf : ∀ z, f (conj z) = conj (f z)) (n : ℕ) :
    ∀ z, iteratedDeriv n f (conj z) = conj (iteratedDeriv n f z) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n hn =>
    let g := iteratedDeriv n f
    have hn' : ∀ z, g (conj z) = conj (g z) := hn
    have heq : (conj ∘ g ∘ conj) = g := by
      funext z
      simpa [Function.comp_apply] using (hn' (conj z)).symm
    have hd := deriv_conj_conj (f := g)
    rw [heq] at hd
    intro z
    simpa [iteratedDeriv_succ, Function.comp_apply, g] using congrFun hd (conj z)

private theorem eulerJet_odd_coeff_zero {f : ℂ → ℂ}
    (hf : ∀ z, f (-z) = f z) (k : ℕ) :
    iteratedDeriv (2 * k + 1) f 0 = 0 := by
  have heq : (fun z => f (-z)) = f := funext hf
  have h := iteratedDeriv_comp_neg (2 * k + 1) f (0 : ℂ)
  rw [heq] at h
  have hpow : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    simp
  simp only [neg_zero, hpow, neg_smul, one_smul] at h
  have hre : (iteratedDeriv (2 * k + 1) f 0).re =
      -(iteratedDeriv (2 * k + 1) f 0).re := by
    simpa only [Complex.neg_re] using congrArg Complex.re h
  have him : (iteratedDeriv (2 * k + 1) f 0).im =
      -(iteratedDeriv (2 * k + 1) f 0).im := by
    simpa only [Complex.neg_im] using congrArg Complex.im h
  apply Complex.ext
  · simp only [Complex.zero_re]; linarith
  · simp only [Complex.zero_im]; linarith

end RHTower

namespace RHTower

private theorem eulerJet_not_eventually_nonpositive {f : ℂ → ℂ} {a : ℕ → ℝ}
    (hp : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ
      (fun n => (a n : ℂ))) 0)
    (hf : Meromorphic f) (hreal : ∀ R : ℝ, 0 ≤ R → AnalyticAt ℂ f (R : ℂ))
    (hfinite : (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius ≠ ⊤) :
    ¬ ∀ᶠ n in atTop, a n ≤ 0 := by
  have hneg : (FormalMultilinearSeries.ofScalars ℂ (fun n => ((-a n : ℝ) : ℂ))) =
      -(FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))) := by
    ext n
    simp [FormalMultilinearSeries.ofScalars]
  have hpneg : HasFPowerSeriesAt (-f)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => ((-a n : ℝ) : ℂ))) 0 := by
    rw [hneg]
    exact hp.neg
  have hfinneg : (FormalMultilinearSeries.ofScalars ℂ
      (fun n => ((-a n : ℝ) : ℂ))).radius ≠ ⊤ := by
    rw [hneg, FormalMultilinearSeries.radius_neg]
    exact hfinite
  intro hnonpos
  apply eulerJet_not_eventually_nonnegative hpneg hf.neg
    (fun R hR => (hreal R hR).neg) hfinneg
  simpa only [neg_nonneg] using hnonpos

private theorem eulerJet_cofinal_negative_even {a : ℕ → ℝ}
    (hne : ¬ ∀ᶠ n in atTop, 0 ≤ a n) (hodd : ∀ k, a (2 * k + 1) = 0)
    (N : ℕ) : ∃ k, N ≤ k ∧ a (2 * k) < 0 := by
  have hex : ∃ n, 2 * N ≤ n ∧ a n < 0 := by
    by_contra h
    push Not at h
    apply hne
    exact eventually_atTop.2 ⟨2 * N, h⟩
  obtain ⟨n, hn, ha⟩ := hex
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · rw [hk] at hn ha
    exact ⟨k, by omega, ha⟩
  · rw [hk, hodd] at ha
    exact (lt_irrefl 0 ha).elim

private theorem eulerJet_cofinal_positive_even {a : ℕ → ℝ}
    (hne : ¬ ∀ᶠ n in atTop, a n ≤ 0) (hodd : ∀ k, a (2 * k + 1) = 0)
    (N : ℕ) : ∃ k, N ≤ k ∧ 0 < a (2 * k) := by
  have hex : ∃ n, 2 * N ≤ n ∧ 0 < a n := by
    by_contra h
    push Not at h
    apply hne
    exact eventually_atTop.2 ⟨2 * N, h⟩
  obtain ⟨n, hn, ha⟩ := hex
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · rw [hk] at hn ha
    exact ⟨k, by omega, ha⟩
  · rw [hk, hodd] at ha
    exact (lt_irrefl 0 ha).elim

end RHTower

namespace RHTower

noncomputable section

/-- Canonical real Taylor coefficient of the actual even logarithmic-mass germ. -/
def liEvenCrossEulerJetTaylorCoeff (v : LiEvenCrossPositiveMass) (n : ℕ) : ℝ :=
  (iteratedDeriv n (liEvenCrossCassiniEvenLogMassGerm v.val) 0 /
    (n.factorial : ℂ)).re

/-- Schwarz reality identifies the real coefficient with the full complex Taylor jet. -/
@[simp] theorem ofReal_liEvenCrossEulerJetTaylorCoeff (v : LiEvenCrossPositiveMass) (n : ℕ) :
    (liEvenCrossEulerJetTaylorCoeff v n : ℂ) =
      iteratedDeriv n (liEvenCrossCassiniEvenLogMassGerm v.val) 0 /
        (n.factorial : ℂ) := by
  unfold liEvenCrossEulerJetTaylorCoeff
  apply Complex.conj_eq_iff_re.mp
  have hjet : conj (iteratedDeriv n (liEvenCrossCassiniEvenLogMassGerm v.val) 0) =
      iteratedDeriv n (liEvenCrossCassiniEvenLogMassGerm v.val) 0 := by
    simpa using (eulerJet_schwarz_iteratedDeriv
      (liEvenCrossCassiniEvenLogMassGerm_conj v.val) n (0 : ℂ)).symm
  simp only [map_div₀, map_natCast, hjet]

/-- Odd Taylor coefficients vanish exactly. -/
@[simp] theorem liEvenCrossEulerJetTaylorCoeff_odd (v : LiEvenCrossPositiveMass) (k : ℕ) :
    liEvenCrossEulerJetTaylorCoeff v (2 * k + 1) = 0 := by
  have hjet := eulerJet_odd_coeff_zero (liEvenCrossCassiniEvenLogMassGerm_even v.val) k
  simp [liEvenCrossEulerJetTaylorCoeff, hjet]

/-- Native factorial normalization of the real iterated derivative. -/
theorem liEvenCrossEulerJetTaylorCoeff_eq_real_jet (v : LiEvenCrossPositiveMass) (n : ℕ) :
    liEvenCrossEulerJetTaylorCoeff v n =
      (iteratedDeriv n (liEvenCrossCassiniEvenLogMassGerm v.val) 0).re /
        (n.factorial : ℝ) := by
  simp [liEvenCrossEulerJetTaylorCoeff]

/-- The canonical Taylor series, not a freely chosen local expansion. -/
def liEvenCrossEulerJetTaylorSeries (v : LiEvenCrossPositiveMass) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (liEvenCrossEulerJetTaylorCoeff v n : ℂ))

/-- The actual source germ is represented by its canonical Taylor series. -/
theorem hasFPowerSeriesAt_liEvenCrossEulerJetTaylorSeries (v : LiEvenCrossPositiveMass) :
    HasFPowerSeriesAt (liEvenCrossCassiniEvenLogMassGerm v.val)
      (liEvenCrossEulerJetTaylorSeries v) 0 := by
  have h := (analyticAt_liEvenCrossCassiniEvenLogMassGerm_real v.property 0).hasFPowerSeriesAt
  simpa only [liEvenCrossEulerJetTaylorSeries, ofReal_liEvenCrossEulerJetTaylorCoeff,
    Complex.ofReal_zero] using h

/-- The canonical radius is strictly positive. -/
theorem liEvenCrossEulerJetTaylorSeries_radius_pos (v : LiEvenCrossPositiveMass) :
    0 < (liEvenCrossEulerJetTaylorSeries v).radius :=
  (hasFPowerSeriesAt_liEvenCrossEulerJetTaylorSeries v).radius_pos

/-- The actual cubic pole prevents an entire Taylor germ. -/
theorem liEvenCrossEulerJetTaylorSeries_radius_ne_top (v : LiEvenCrossPositiveMass) :
    (liEvenCrossEulerJetTaylorSeries v).radius ≠ ⊤ := by
  apply eulerJet_radius_ne_top_of_pole (hasFPowerSeriesAt_liEvenCrossEulerJetTaylorSeries v)
    (meromorphicOn_univ.mp (meromorphicOn_liEvenCrossCassiniEvenLogMassGerm v.val))
  obtain ⟨t, ht⟩ := exists_liEvenCrossCassiniEvenLogMassGerm_cubic_pole_positive v
  refine ⟨t, ?_⟩
  rw [ht]
  exact_mod_cast (show (-3 : ℤ) < 0 by norm_num)

/-- Finite-tail positivity is impossible for the actual canonical coefficient sequence. -/
theorem liEvenCrossEulerJetTaylorCoeff_not_eventually_nonneg (v : LiEvenCrossPositiveMass) :
    ¬ ∀ᶠ n in atTop, 0 ≤ liEvenCrossEulerJetTaylorCoeff v n := by
  apply eulerJet_not_eventually_nonnegative (hasFPowerSeriesAt_liEvenCrossEulerJetTaylorSeries v)
    (meromorphicOn_univ.mp (meromorphicOn_liEvenCrossCassiniEvenLogMassGerm v.val))
    (fun R _ => analyticAt_liEvenCrossCassiniEvenLogMassGerm_real v.property R)
    (liEvenCrossEulerJetTaylorSeries_radius_ne_top v)

/-- Finite-tail negativity is also impossible. -/
theorem liEvenCrossEulerJetTaylorCoeff_not_eventually_nonpos (v : LiEvenCrossPositiveMass) :
    ¬ ∀ᶠ n in atTop, liEvenCrossEulerJetTaylorCoeff v n ≤ 0 := by
  apply eulerJet_not_eventually_nonpositive (hasFPowerSeriesAt_liEvenCrossEulerJetTaylorSeries v)
    (meromorphicOn_univ.mp (meromorphicOn_liEvenCrossCassiniEvenLogMassGerm v.val))
    (fun R _ => analyticAt_liEvenCrossCassiniEvenLogMassGerm_real v.property R)
    (liEvenCrossEulerJetTaylorSeries_radius_ne_top v)

/-- Every even-jet tail contains a strictly negative canonical coefficient. -/
theorem liEvenCrossEulerJetTaylorCoeff_cofinal_negative (v : LiEvenCrossPositiveMass) (N : ℕ) :
    ∃ k, N ≤ k ∧ liEvenCrossEulerJetTaylorCoeff v (2 * k) < 0 :=
  eulerJet_cofinal_negative_even (liEvenCrossEulerJetTaylorCoeff_not_eventually_nonneg v)
    (liEvenCrossEulerJetTaylorCoeff_odd v) N

/-- Every even-jet tail contains a strictly positive canonical coefficient. -/
theorem liEvenCrossEulerJetTaylorCoeff_cofinal_positive (v : LiEvenCrossPositiveMass) (N : ℕ) :
    ∃ k, N ≤ k ∧ 0 < liEvenCrossEulerJetTaylorCoeff v (2 * k) :=
  eulerJet_cofinal_positive_even (liEvenCrossEulerJetTaylorCoeff_not_eventually_nonpos v)
    (liEvenCrossEulerJetTaylorCoeff_odd v) N

/-- **Actual-source oscillation:** both signs occur cofinally among the even canonical jets. -/
theorem liEvenCrossEulerJetTaylorCoeff_cofinal_both_signs (v : LiEvenCrossPositiveMass) :
    (∀ N : ℕ, ∃ k, N ≤ k ∧ liEvenCrossEulerJetTaylorCoeff v (2 * k) < 0) ∧
      (∀ N : ℕ, ∃ k, N ≤ k ∧ 0 < liEvenCrossEulerJetTaylorCoeff v (2 * k)) :=
  ⟨liEvenCrossEulerJetTaylorCoeff_cofinal_negative v,
    liEvenCrossEulerJetTaylorCoeff_cofinal_positive v⟩

/-- The closed nonnegative all-even-jet cone fails at every positive mass. -/
theorem liEvenCrossEulerJetTaylorCoeff_not_all_even_nonneg (v : LiEvenCrossPositiveMass) :
    ¬ ∀ k, 0 ≤ liEvenCrossEulerJetTaylorCoeff v (2 * k) := by
  intro h
  obtain ⟨k, _, hk⟩ := liEvenCrossEulerJetTaylorCoeff_cofinal_negative v 0
  exact (not_lt_of_ge (h k)) hk

/-- Reversing the closed cone does not restore an eventual orientation. -/
theorem liEvenCrossEulerJetTaylorCoeff_not_all_even_nonpos (v : LiEvenCrossPositiveMass) :
    ¬ ∀ k, liEvenCrossEulerJetTaylorCoeff v (2 * k) ≤ 0 := by
  intro h
  obtain ⟨k, _, hk⟩ := liEvenCrossEulerJetTaylorCoeff_cofinal_positive v 0
  exact (not_lt_of_ge (h k)) hk


/-- The same cofinal oscillation in the unnormalized real iterated derivatives. -/
theorem liEvenCrossEulerJet_real_cofinal_both_signs (v : LiEvenCrossPositiveMass) :
    (∀ N : ℕ, ∃ k, N ≤ k ∧
      (iteratedDeriv (2 * k) (liEvenCrossCassiniEvenLogMassGerm v.val) 0).re < 0) ∧
    (∀ N : ℕ, ∃ k, N ≤ k ∧
      0 < (iteratedDeriv (2 * k) (liEvenCrossCassiniEvenLogMassGerm v.val) 0).re) := by
  constructor
  · intro N
    obtain ⟨k, hNk, hk⟩ := liEvenCrossEulerJetTaylorCoeff_cofinal_negative v N
    refine ⟨k, hNk, ?_⟩
    rw [liEvenCrossEulerJetTaylorCoeff_eq_real_jet] at hk
    have hfact : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
    simpa using (div_lt_iff₀ hfact).mp hk
  · intro N
    obtain ⟨k, hNk, hk⟩ := liEvenCrossEulerJetTaylorCoeff_cofinal_positive v N
    refine ⟨k, hNk, ?_⟩
    rw [liEvenCrossEulerJetTaylorCoeff_eq_real_jet] at hk
    have hfact : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
    simpa using (lt_div_iff₀ hfact).mp hk

/-- Unnormalized derivatives also exclude the closed nonnegative all-even jet cone. -/
theorem liEvenCrossEulerJet_real_not_all_even_nonneg (v : LiEvenCrossPositiveMass) :
    ¬ ∀ k, 0 ≤ (iteratedDeriv (2 * k)
      (liEvenCrossCassiniEvenLogMassGerm v.val) 0).re := by
  intro h
  obtain ⟨k, _, hk⟩ := (liEvenCrossEulerJet_real_cofinal_both_signs v).1 0
  exact (not_lt_of_ge (h k)) hk


end

end RHTower
