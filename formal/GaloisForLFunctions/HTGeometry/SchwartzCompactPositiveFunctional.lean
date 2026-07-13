import GaloisForLFunctions.HTGeometry.SchwartzCompactContinuousDensity
import Mathlib.Analysis.PSeries

/-!
# Positive compactly supported functional reconstructed from a Schwartz form

A nonnegative momentum-symmetric continuous sesquilinear form on complex Schwartz space has a
canonical diagonal distribution in Fourier coordinates.  The local order-zero estimate and
compactly supported uniform density extend that distribution to a positive real functional on
`C_c(ℝ, ℝ)`.  This is the constructive Riesz--Markov input for the Bochner--Schwartz converse in
the exact category needed by the Hedenmalm theta problem.
-/

open Complex Function Filter Set MeasureTheory TopologicalSpace
open scoped SchwartzMap FourierTransform Topology Polynomial ContDiff CompactlySupported

noncomputable section

namespace SchwartzMap

/-- A common-packet Schwartz approximation to a compactly supported continuous real function. -/
structure CompactContinuousSchwartzApproximation (f : C_c(ℝ, ℝ)) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  seq : ℕ → SchwartzMap ℝ ℝ
  seq_tsupport : ∀ n, tsupport (seq n) ⊆ {t : ℝ | |t| ≤ radius}
  tendsto_uniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ, |seq n t - f t| < ε

/-- Every compactly supported continuous real function has a common-packet Schwartz
approximation. -/
theorem exists_compactContinuousSchwartzApproximation (f : C_c(ℝ, ℝ)) :
    Nonempty (CompactContinuousSchwartzApproximation f) := by
  have hb : Bornology.IsBounded (tsupport f) := f.hasCompactSupport.isCompact.isBounded
  rw [Metric.isBounded_iff_subset_closedBall 0] at hb
  obtain ⟨R₀, hR₀⟩ := hb
  let R : ℝ := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hf : tsupport f ⊆ {t : ℝ | |t| ≤ R} := by
    intro t ht
    have htball := hR₀ ht
    rw [Metric.mem_closedBall, Real.dist_0_eq_abs] at htball
    exact htball.trans (le_max_left _ _)
  obtain ⟨P, hP, hPsupp⟩ := exists_realPolynomialCutoff_sequence_uniform f hR hf
  refine ⟨⟨R + 2, by linarith, fun n ↦ realPolynomialCutoff (P n) R, hPsupp, ?_⟩⟩
  intro ε hε
  have hzero : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1 : ℝ) < ε :=
    (tendsto_order.1 hzero).2 ε hε
  filter_upwards [hevent] with n hn
  intro t
  exact (hP n t).trans hn

/-- The real Schwartz seminorm of order `(0,0)` is bounded by a pointwise uniform bound. -/
theorem seminorm_zero_le_of_forall_abs_le
    (h : SchwartzMap ℝ ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hh : ∀ t, |h t| ≤ M) :
    SchwartzMap.seminorm ℝ 0 0 h ≤ M := by
  apply SchwartzMap.seminorm_le_bound' ℝ 0 0 h hM
  intro t
  simpa only [pow_zero, one_mul, iteratedDeriv_zero, Real.norm_eq_abs] using hh t

@[simp] theorem realToComplexSchwartz_tsupport (h : SchwartzMap ℝ ℝ) :
    tsupport (realToComplexSchwartz h) = tsupport h := by
  rw [tsupport, tsupport]
  congr 1
  ext t
  simp only [Function.mem_support, realToComplexSchwartz_apply, ne_eq]
  norm_cast

/-- Joint continuity of a Schwartz sesquilinear form gives one finite family of Schwartz
seminorms controlling its diagonal.  This is the finite-order input behind temperate growth of
the represented positive measure. -/
theorem ContinuousSchwartzSesquilinearForm.exists_finset_diagonal_bound
    (Q : ContinuousSchwartzSesquilinearForm) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap ℝ ℂ,
      ‖Q f f‖ ≤ C *
        (1 + s.sup (schwartzSeminormFamily ℂ ℝ ℂ) f) ^ 2 := by
  have hzero : Q (0 : SchwartzMap ℝ ℂ) 0 = 0 := by
    have h := Q.map_smul_left 0 0 0
    simpa using h
  have hpre : (fun p : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ => Q p.1 p.2) ⁻¹'
      Metric.ball 0 1 ∈ 𝓝 ((0, 0) : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ) := by
    apply Q.continuous.continuousAt
    simpa [hzero] using (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  let p := schwartzSeminormFamily ℂ ℝ ℂ
  have hb : (𝓝 ((0, 0) : SchwartzMap ℝ ℂ × SchwartzMap ℝ ℂ)).HasBasis
      (fun i : Set (SchwartzMap ℝ ℂ) × Set (SchwartzMap ℝ ℂ) =>
        i.1 ∈ p.basisSets ∧ i.2 ∈ p.basisSets)
      (fun i => i.1 ×ˢ i.2) := by
    rw [nhds_prod_eq]
    exact (schwartz_withSeminorms ℂ ℝ ℂ).hasBasis.prod
      (schwartz_withSeminorms ℂ ℝ ℂ).hasBasis
  obtain ⟨⟨U, V⟩, ⟨hU, hV⟩, hUV⟩ := hb.mem_iff.mp hpre
  obtain ⟨s, r, hr, rfl⟩ := p.basisSets_iff.mp hU
  obtain ⟨t, q, hq, rfl⟩ := p.basisSets_iff.mp hV
  let w : Finset (ℕ × ℕ) := s ∪ t
  let δ : ℝ := min r q
  have hδ : 0 < δ := lt_min hr hq
  refine ⟨w, (2 / δ) ^ 2, by positivity, ?_⟩
  intro f
  let P : ℝ := w.sup p f
  have hP : 0 ≤ P := by positivity
  let c : ℝ := δ / (2 * (P + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcalc : c * P < δ := by
    dsimp [c]
    have hfrac : P / (P + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc
      δ / (2 * (P + 1)) * P = δ / 2 * (P / (P + 1)) := by
        field_simp
      _ < δ / 2 * 1 := mul_lt_mul_of_pos_left hfrac (by linarith)
      _ < δ := by linarith
  have hcs : (s.sup p) ((c : ℂ) • f) < r := by
    change (s.sup p).toFun ((c : ℂ) • f) < r
    rw [(s.sup p).smul']
    change ‖(c : ℂ)‖ * (s.sup p) f < r
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have hsw : (s.sup p) f ≤ P :=
      (Finset.sup_mono Finset.subset_union_left : s.sup p ≤ w.sup p) f
    exact (mul_le_mul_of_nonneg_left hsw hc.le).trans_lt
      (hcalc.trans_le (min_le_left _ _))
  have hct : (t.sup p) ((c : ℂ) • f) < q := by
    change (t.sup p).toFun ((c : ℂ) • f) < q
    rw [(t.sup p).smul']
    change ‖(c : ℂ)‖ * (t.sup p) f < q
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have htw : (t.sup p) f ≤ P :=
      (Finset.sup_mono Finset.subset_union_right : t.sup p ≤ w.sup p) f
    exact (mul_le_mul_of_nonneg_left htw hc.le).trans_lt
      (hcalc.trans_le (min_le_right _ _))
  have hmem : ((c : ℂ) • f, (c : ℂ) • f) ∈
      (s.sup p).ball 0 r ×ˢ (t.sup p).ball 0 q := by
    constructor
    · simpa [Seminorm.mem_ball_zero] using hcs
    · simpa [Seminorm.mem_ball_zero] using hct
  have hQsmall := hUV hmem
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hQsmall
  have hscale : Q ((c : ℂ) • f) ((c : ℂ) • f) = (c : ℂ) ^ 2 * Q f f := by
    rw [Q.apply_smul_left, Q.apply_smul_right, Complex.conj_ofReal]
    ring
  rw [hscale, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hc] at hQsmall
  have hnorm : ‖Q f f‖ < 1 / c ^ 2 := by
    rw [lt_div_iff₀' (sq_pos_of_pos hc)]
    simpa [mul_comm] using hQsmall
  have hcEq : 1 / c ^ 2 = (2 / δ) ^ 2 * (P + 1) ^ 2 := by
    dsimp [c]
    field_simp
  rw [hcEq] at hnorm
  change ‖Q f f‖ ≤ (2 / δ) ^ 2 * (1 + P) ^ 2
  nlinarith

/-- The scalar diagonal sequence attached to a common-packet approximation. -/
def CompactContinuousSchwartzApproximation.diagonalSequence
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (n : ℕ) : ℝ :=
  (Q.compactIntervalDiagonalFunctional (A.radius + 4)
    (realToComplexSchwartz (A.seq n))).re

/-- The local cutoff mass controlling a common packet. -/
def CompactContinuousSchwartzApproximation.cutoffMass
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) : ℝ :=
  (Q.compactIntervalDiagonalFunctional (A.radius + 4)
    (realToComplexSchwartz (realCompactIntervalCutoff A.radius))).re

theorem CompactContinuousSchwartzApproximation.cutoffMass_nonnegative
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    0 ≤ A.cutoffMass Q := by
  have hsupp : tsupport (realCompactIntervalCutoff A.radius) ⊆
      {t : ℝ | |t| ≤ A.radius + 2} := by
    rw [realCompactIntervalCutoff_tsupport]
    simpa [abs_of_nonneg A.radius_nonneg]
  have hpos := Q.compactIntervalDiagonalFunctional_nonnegative_real hQ hQnonneg
    (realCompactIntervalCutoff A.radius)
    (realCompactIntervalCutoff_nonnegative A.radius)
    (show 0 ≤ A.radius + 2 by linarith [A.radius_nonneg]) hsupp
  have hradius : A.radius + 2 + 2 = A.radius + 4 := by ring
  rw [hradius] at hpos
  exact hpos.1

/-- The diagonal values of every common-packet approximation form a Cauchy sequence. -/
theorem CompactContinuousSchwartzApproximation.cauchySeq_diagonalSequence
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    CauchySeq (A.diagonalSequence Q) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let C : ℝ := A.cutoffMass Q
  have hC : 0 ≤ C := A.cutoffMass_nonnegative Q hQ hQnonneg
  let δ : ℝ := ε / (4 * (C + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hEventually := A.tendsto_uniform δ hδ
  rw [eventually_atTop] at hEventually
  obtain ⟨N, hN⟩ := hEventually
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmnear := hN m hm
  have hnnear := hN n hn
  let d : SchwartzMap ℝ ℝ := A.seq m - A.seq n
  have hdsupp : tsupport d ⊆ {t : ℝ | |t| ≤ A.radius} := by
    intro t ht
    have ht' := tsupport_sub (A.seq m) (A.seq n) ht
    rcases ht' with htm | htn
    · exact A.seq_tsupport m htm
    · exact A.seq_tsupport n htn
  have hdpoint (t : ℝ) : |d t| ≤ 2 * δ := by
    change |A.seq m t - A.seq n t| ≤ 2 * δ
    have hlt : |A.seq m t - A.seq n t| < 2 * δ := by
      calc
      |A.seq m t - A.seq n t| =
          |(A.seq m t - f t) - (A.seq n t - f t)| := by ring_nf
      _ ≤ |A.seq m t - f t| + |A.seq n t - f t| := abs_sub _ _
      _ < δ + δ := add_lt_add (hmnear t) (hnnear t)
      _ = 2 * δ := by ring
    exact hlt.le
  have hdsemi : SchwartzMap.seminorm ℝ 0 0 d ≤ 2 * δ :=
    seminorm_zero_le_of_forall_abs_le d (by positivity) hdpoint
  have hbound :=
    Q.compactIntervalDiagonalFunctional_norm_le_seminorm_zero hQ hQnonneg d
      A.radius_nonneg hdsupp
  change ‖Q.compactIntervalDiagonalFunctional (A.radius + 4)
      (realToComplexSchwartz d)‖ ≤
        SchwartzMap.seminorm ℝ 0 0 d * C at hbound
  have hcomplex :
      Q.compactIntervalDiagonalFunctional (A.radius + 4)
          (realToComplexSchwartz d) =
        Q.compactIntervalDiagonalFunctional (A.radius + 4)
            (realToComplexSchwartz (A.seq m)) -
          Q.compactIntervalDiagonalFunctional (A.radius + 4)
            (realToComplexSchwartz (A.seq n)) := by
    change Q.compactIntervalDiagonalFunctional (A.radius + 4)
        (realToComplexSchwartz (A.seq m - A.seq n)) = _
    have hrtc : realToComplexSchwartz (A.seq m - A.seq n) =
        realToComplexSchwartz (A.seq m) - realToComplexSchwartz (A.seq n) := by
      ext t
      simp [realToComplexSchwartz_apply]
    rw [hrtc, map_sub]
  have hreal :
      |A.diagonalSequence Q m - A.diagonalSequence Q n| ≤
        ‖Q.compactIntervalDiagonalFunctional (A.radius + 4)
          (realToComplexSchwartz d)‖ := by
    rw [hcomplex]
    change |(Q.compactIntervalDiagonalFunctional (A.radius + 4)
        (realToComplexSchwartz (A.seq m)) -
      Q.compactIntervalDiagonalFunctional (A.radius + 4)
        (realToComplexSchwartz (A.seq n))).re| ≤ _
    exact Complex.abs_re_le_norm _
  have hmass : (2 * δ) * C < ε := by
    have hle : (2 * δ) * C ≤ (2 * δ) * (C + 1) := by
      gcongr
      linarith
    have heq : (2 * δ) * (C + 1) = ε / 2 := by
      dsimp [δ]
      field_simp
      <;> ring
    rw [heq] at hle
    linarith
  rw [Real.dist_eq]
  exact hreal.trans_lt (hbound.trans_lt ((mul_le_mul_of_nonneg_right hdsemi hC).trans_lt hmass))

/-- The limit of the diagonal values attached to one approximation. -/
def CompactContinuousSchwartzApproximation.diagonalLimit
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) : ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (A.cauchySeq_diagonalSequence Q hQ hQnonneg))

theorem CompactContinuousSchwartzApproximation.tendsto_diagonalLimit
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    Tendsto (A.diagonalSequence Q) atTop
      (𝓝 (A.diagonalLimit Q hQ hQnonneg)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (A.cauchySeq_diagonalSequence Q hQ hQnonneg))

/-- Local diagonal functionals agree when both cutoff radii dominate one common packet. -/
theorem ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional_stable_of_le
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (h : SchwartzMap ℝ ℂ) {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S)
    (hh : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    Q.compactIntervalDiagonalFunctional (R + 4) h =
      Q.compactIntervalDiagonalFunctional (S + 4) h := by
  apply Q.fourierPullback_compactIntervalCutoff_stable hQ h hh
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- Two common-packet approximations to the same compactly supported function have asymptotically
identical diagonal values, even when their packet radii differ. -/
theorem CompactContinuousSchwartzApproximation.tendsto_diagonalSequence_sub_zero
    {f : C_c(ℝ, ℝ)} (A B : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    Tendsto (fun n ↦ A.diagonalSequence Q n - B.diagonalSequence Q n)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let T : ℝ := max A.radius B.radius
  have hT : 0 ≤ T := A.radius_nonneg.trans (le_max_left _ _)
  let C : ℝ :=
    (Q.compactIntervalDiagonalFunctional (T + 4)
      (realToComplexSchwartz (realCompactIntervalCutoff T))).re
  have hCsupp : tsupport (realCompactIntervalCutoff T) ⊆
      {t : ℝ | |t| ≤ T + 2} := by
    rw [realCompactIntervalCutoff_tsupport]
    simpa [abs_of_nonneg hT]
  have hCpos := Q.compactIntervalDiagonalFunctional_nonnegative_real hQ hQnonneg
    (realCompactIntervalCutoff T) (realCompactIntervalCutoff_nonnegative T)
    (show 0 ≤ T + 2 by linarith) hCsupp
  have hTradius : T + 2 + 2 = T + 4 := by ring
  rw [hTradius] at hCpos
  have hC : 0 ≤ C := hCpos.1
  let δ : ℝ := ε / (4 * (C + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hAevent := A.tendsto_uniform δ hδ
  have hBevent := B.tendsto_uniform δ hδ
  rw [eventually_atTop] at hAevent hBevent
  obtain ⟨NA, hNA⟩ := hAevent
  obtain ⟨NB, hNB⟩ := hBevent
  refine ⟨max NA NB, ?_⟩
  intro n hn
  have hAn := hNA n ((le_max_left NA NB).trans hn)
  have hBn := hNB n ((le_max_right NA NB).trans hn)
  let d : SchwartzMap ℝ ℝ := A.seq n - B.seq n
  have hdsupp : tsupport d ⊆ {t : ℝ | |t| ≤ T} := by
    intro t ht
    rcases tsupport_sub (A.seq n) (B.seq n) ht with htA | htB
    · change |t| ≤ T
      exact (A.seq_tsupport n htA).trans (le_max_left _ _)
    · change |t| ≤ T
      exact (B.seq_tsupport n htB).trans (le_max_right _ _)
  have hdpoint (t : ℝ) : |d t| ≤ 2 * δ := by
    change |A.seq n t - B.seq n t| ≤ 2 * δ
    have hlt : |A.seq n t - B.seq n t| < 2 * δ := by
      calc
        |A.seq n t - B.seq n t| =
            |(A.seq n t - f t) - (B.seq n t - f t)| := by ring_nf
        _ ≤ |A.seq n t - f t| + |B.seq n t - f t| := abs_sub _ _
        _ < δ + δ := add_lt_add (hAn t) (hBn t)
        _ = 2 * δ := by ring
    exact hlt.le
  have hdsemi : SchwartzMap.seminorm ℝ 0 0 d ≤ 2 * δ :=
    seminorm_zero_le_of_forall_abs_le d (by positivity) hdpoint
  have hbound :=
    Q.compactIntervalDiagonalFunctional_norm_le_seminorm_zero hQ hQnonneg d hT hdsupp
  change ‖Q.compactIntervalDiagonalFunctional (T + 4)
      (realToComplexSchwartz d)‖ ≤
        SchwartzMap.seminorm ℝ 0 0 d * C at hbound
  have hAcommon :
      Q.compactIntervalDiagonalFunctional (A.radius + 4)
          (realToComplexSchwartz (A.seq n)) =
        Q.compactIntervalDiagonalFunctional (T + 4)
          (realToComplexSchwartz (A.seq n)) :=
    Q.compactIntervalDiagonalFunctional_stable_of_le hQ
      (realToComplexSchwartz (A.seq n)) A.radius_nonneg (le_max_left _ _)
      (by
        rw [realToComplexSchwartz_tsupport]
        exact A.seq_tsupport n)
  have hBcommon :
      Q.compactIntervalDiagonalFunctional (B.radius + 4)
          (realToComplexSchwartz (B.seq n)) =
        Q.compactIntervalDiagonalFunctional (T + 4)
          (realToComplexSchwartz (B.seq n)) :=
    Q.compactIntervalDiagonalFunctional_stable_of_le hQ
      (realToComplexSchwartz (B.seq n)) B.radius_nonneg (le_max_right _ _)
      (by
        rw [realToComplexSchwartz_tsupport]
        exact B.seq_tsupport n)
  have hrtc : realToComplexSchwartz d =
      realToComplexSchwartz (A.seq n) - realToComplexSchwartz (B.seq n) := by
    ext t
    simp [d, realToComplexSchwartz_apply]
  have hcomplex :
      Q.compactIntervalDiagonalFunctional (T + 4)
          (realToComplexSchwartz d) =
        Q.compactIntervalDiagonalFunctional (T + 4)
            (realToComplexSchwartz (A.seq n)) -
          Q.compactIntervalDiagonalFunctional (T + 4)
            (realToComplexSchwartz (B.seq n)) := by
    rw [hrtc, map_sub]
  have hreal : |A.diagonalSequence Q n - B.diagonalSequence Q n| ≤
      ‖Q.compactIntervalDiagonalFunctional (T + 4)
        (realToComplexSchwartz d)‖ := by
    rw [hcomplex]
    change |(Q.compactIntervalDiagonalFunctional (A.radius + 4)
        (realToComplexSchwartz (A.seq n))).re -
      (Q.compactIntervalDiagonalFunctional (B.radius + 4)
        (realToComplexSchwartz (B.seq n))).re| ≤ _
    rw [hAcommon, hBcommon]
    change |(Q.compactIntervalDiagonalFunctional (T + 4)
        (realToComplexSchwartz (A.seq n)) -
      Q.compactIntervalDiagonalFunctional (T + 4)
        (realToComplexSchwartz (B.seq n))).re| ≤ _
    exact Complex.abs_re_le_norm _
  have hmass : (2 * δ) * C < ε := by
    have hle : (2 * δ) * C ≤ (2 * δ) * (C + 1) := by
      gcongr
      linarith
    have heq : (2 * δ) * (C + 1) = ε / 2 := by
      dsimp [δ]
      field_simp
      <;> ring
    rw [heq] at hle
    linarith
  rw [Real.dist_eq, sub_zero]
  exact hreal.trans_lt
    (hbound.trans_lt ((mul_le_mul_of_nonneg_right hdsemi hC).trans_lt hmass))

/-- The reconstructed diagonal limit is independent of the common-packet approximation. -/
theorem CompactContinuousSchwartzApproximation.diagonalLimit_eq
    {f : C_c(ℝ, ℝ)} (A B : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    A.diagonalLimit Q hQ hQnonneg = B.diagonalLimit Q hQ hQnonneg := by
  have hsub : Tendsto
      (fun n ↦ A.diagonalSequence Q n - B.diagonalSequence Q n) atTop
      (𝓝 (A.diagonalLimit Q hQ hQnonneg - B.diagonalLimit Q hQ hQnonneg)) :=
    (A.tendsto_diagonalLimit Q hQ hQnonneg).sub
      (B.tendsto_diagonalLimit Q hQ hQnonneg)
  have hzero := A.tendsto_diagonalSequence_sub_zero B Q hQ hQnonneg
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub hzero)

/-- Addition of common-packet approximations, promoted to one common radius. -/
def CompactContinuousSchwartzApproximation.add
    {f g : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (B : CompactContinuousSchwartzApproximation g) :
    CompactContinuousSchwartzApproximation (f + g) where
  radius := max A.radius B.radius
  radius_nonneg := A.radius_nonneg.trans (le_max_left _ _)
  seq n := A.seq n + B.seq n
  seq_tsupport n := by
    intro t ht
    rcases tsupport_add (A.seq n) (B.seq n) ht with htA | htB
    · change |t| ≤ max A.radius B.radius
      exact (A.seq_tsupport n htA).trans (le_max_left _ _)
    · change |t| ≤ max A.radius B.radius
      exact (B.seq_tsupport n htB).trans (le_max_right _ _)
  tendsto_uniform ε hε := by
    have hhalf : 0 < ε / 2 := by linarith
    filter_upwards [A.tendsto_uniform (ε / 2) hhalf,
      B.tendsto_uniform (ε / 2) hhalf] with n hA hB
    intro t
    change |(A.seq n t + B.seq n t) - (f t + g t)| < ε
    calc
      |(A.seq n t + B.seq n t) - (f t + g t)| =
          |(A.seq n t - f t) + (B.seq n t - g t)| := by ring_nf
      _ ≤ |A.seq n t - f t| + |B.seq n t - g t| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hA t) (hB t)
      _ = ε := by ring

/-- Real scalar multiplication of common-packet approximations. -/
def CompactContinuousSchwartzApproximation.smul
    {f : C_c(ℝ, ℝ)} (c : ℝ) (A : CompactContinuousSchwartzApproximation f) :
    CompactContinuousSchwartzApproximation (c • f) where
  radius := A.radius
  radius_nonneg := A.radius_nonneg
  seq n := c • A.seq n
  seq_tsupport n := by
    have hs := tsupport_smul_subset_right (fun _t : ℝ => c) (A.seq n)
    exact hs.trans (A.seq_tsupport n)
  tendsto_uniform ε hε := by
    by_cases hc : c = 0
    · subst c
      simp only [zero_smul, sub_self, abs_zero]
      exact Filter.Eventually.of_forall (fun _n _t => by simpa using hε)
    · have hcabs : 0 < |c| := abs_pos.mpr hc
      have hδ : 0 < ε / |c| := div_pos hε hcabs
      filter_upwards [A.tendsto_uniform (ε / |c|) hδ] with n hn
      intro t
      change |c * A.seq n t - c * f t| < ε
      rw [← mul_sub, abs_mul]
      calc
        |c| * |A.seq n t - f t| < |c| * (ε / |c|) :=
          mul_lt_mul_of_pos_left (hn t) hcabs
        _ = ε := by field_simp

theorem CompactContinuousSchwartzApproximation.diagonalSequence_add
    {f g : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (B : CompactContinuousSchwartzApproximation g)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (n : ℕ) :
    (A.add B).diagonalSequence Q n =
      A.diagonalSequence Q n + B.diagonalSequence Q n := by
  let T : ℝ := max A.radius B.radius
  have hAcommon : Q.compactIntervalDiagonalFunctional (A.radius + 4)
      (realToComplexSchwartz (A.seq n)) =
      Q.compactIntervalDiagonalFunctional (T + 4)
        (realToComplexSchwartz (A.seq n)) :=
    Q.compactIntervalDiagonalFunctional_stable_of_le (S := T) hQ
    (realToComplexSchwartz (A.seq n)) A.radius_nonneg
      (show A.radius ≤ T from le_max_left _ _)
    (by rw [realToComplexSchwartz_tsupport]; exact A.seq_tsupport n)
  have hBcommon : Q.compactIntervalDiagonalFunctional (B.radius + 4)
      (realToComplexSchwartz (B.seq n)) =
      Q.compactIntervalDiagonalFunctional (T + 4)
        (realToComplexSchwartz (B.seq n)) :=
    Q.compactIntervalDiagonalFunctional_stable_of_le (S := T) hQ
    (realToComplexSchwartz (B.seq n)) B.radius_nonneg
      (show B.radius ≤ T from le_max_right _ _)
    (by rw [realToComplexSchwartz_tsupport]; exact B.seq_tsupport n)
  change (Q.compactIntervalDiagonalFunctional (T + 4)
      (realToComplexSchwartz (A.seq n + B.seq n))).re = _
  have hrtc : realToComplexSchwartz (A.seq n + B.seq n) =
      realToComplexSchwartz (A.seq n) + realToComplexSchwartz (B.seq n) := by
    ext t
    simp [realToComplexSchwartz_apply]
  rw [hrtc, map_add, ← hAcommon, ← hBcommon, Complex.add_re]
  rfl

theorem CompactContinuousSchwartzApproximation.diagonalSequence_smul
    {f : C_c(ℝ, ℝ)} (c : ℝ) (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (n : ℕ) :
    (A.smul c).diagonalSequence Q n = c * A.diagonalSequence Q n := by
  change (Q.compactIntervalDiagonalFunctional (A.radius + 4)
      (realToComplexSchwartz (c • A.seq n))).re = _
  have hrtc : realToComplexSchwartz (c • A.seq n) =
      (c : ℂ) • realToComplexSchwartz (A.seq n) := by
    ext t
    simp [realToComplexSchwartz_apply]
  rw [hrtc, map_smul]
  change (((c : ℂ) * Q.compactIntervalDiagonalFunctional (A.radius + 4)
    (realToComplexSchwartz (A.seq n))).re) =
      c * (Q.compactIntervalDiagonalFunctional (A.radius + 4)
        (realToComplexSchwartz (A.seq n))).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem CompactContinuousSchwartzApproximation.diagonalLimit_add
    {f g : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (B : CompactContinuousSchwartzApproximation g)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    (A.add B).diagonalLimit Q hQ hQnonneg =
      A.diagonalLimit Q hQ hQnonneg + B.diagonalLimit Q hQ hQnonneg := by
  have hadd : Tendsto ((A.add B).diagonalSequence Q) atTop
      (𝓝 (A.diagonalLimit Q hQ hQnonneg + B.diagonalLimit Q hQ hQnonneg)) := by
    convert (A.tendsto_diagonalLimit Q hQ hQnonneg).add
      (B.tendsto_diagonalLimit Q hQ hQnonneg) using 1
    ext n
    exact A.diagonalSequence_add B Q hQ n
  exact tendsto_nhds_unique
    ((A.add B).tendsto_diagonalLimit Q hQ hQnonneg) hadd

theorem CompactContinuousSchwartzApproximation.diagonalLimit_smul
    {f : C_c(ℝ, ℝ)} (c : ℝ) (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    (A.smul c).diagonalLimit Q hQ hQnonneg =
      c * A.diagonalLimit Q hQ hQnonneg := by
  have hsmul : Tendsto ((A.smul c).diagonalSequence Q) atTop
      (𝓝 (c * A.diagonalLimit Q hQ hQnonneg)) := by
    convert tendsto_const_nhds.mul (A.tendsto_diagonalLimit Q hQ hQnonneg) using 1
    ext n
    exact A.diagonalSequence_smul c Q n
  exact tendsto_nhds_unique
    ((A.smul c).tendsto_diagonalLimit Q hQ hQnonneg) hsmul

/-- A fixed, noncanonical approximation used only to define the canonical approximation-independent
value. -/
def chosenCompactContinuousSchwartzApproximation (f : C_c(ℝ, ℝ)) :
    CompactContinuousSchwartzApproximation f :=
  Classical.choice (exists_compactContinuousSchwartzApproximation f)

/-- The canonical real `C_c` value reconstructed from the local Schwartz diagonal. -/
def ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalValue
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : C_c(ℝ, ℝ)) : ℝ :=
  (chosenCompactContinuousSchwartzApproximation f).diagonalLimit Q hQ hQnonneg

theorem ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalValue_eq
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) {f : C_c(ℝ, ℝ)}
    (A : CompactContinuousSchwartzApproximation f) :
    Q.compactContinuousDiagonalValue hQ hQnonneg f =
      A.diagonalLimit Q hQ hQnonneg :=
  (chosenCompactContinuousSchwartzApproximation f).diagonalLimit_eq A Q hQ hQnonneg

theorem ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalValue_add
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f g : C_c(ℝ, ℝ)) :
    Q.compactContinuousDiagonalValue hQ hQnonneg (f + g) =
      Q.compactContinuousDiagonalValue hQ hQnonneg f +
        Q.compactContinuousDiagonalValue hQ hQnonneg g := by
  let A := chosenCompactContinuousSchwartzApproximation f
  let B := chosenCompactContinuousSchwartzApproximation g
  rw [Q.compactContinuousDiagonalValue_eq hQ hQnonneg (A.add B),
    A.diagonalLimit_add B Q hQ hQnonneg]
  rfl

theorem ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalValue_smul
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (c : ℝ) (f : C_c(ℝ, ℝ)) :
    Q.compactContinuousDiagonalValue hQ hQnonneg (c • f) =
      c * Q.compactContinuousDiagonalValue hQ hQnonneg f := by
  let A := chosenCompactContinuousSchwartzApproximation f
  rw [Q.compactContinuousDiagonalValue_eq hQ hQnonneg (A.smul c),
    A.diagonalLimit_smul c Q hQ hQnonneg]
  rfl

/-- Positivity survives the uniform extension from compactly supported real Schwartz tests to
compactly supported continuous tests. -/
theorem CompactContinuousSchwartzApproximation.diagonalLimit_nonnegative
    {f : C_c(ℝ, ℝ)} (A : CompactContinuousSchwartzApproximation f)
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (hf : ∀ t, 0 ≤ f t) :
    0 ≤ A.diagonalLimit Q hQ hQnonneg := by
  by_contra hnot
  have hL : A.diagonalLimit Q hQ hQnonneg < 0 := lt_of_not_ge hnot
  let C : ℝ := A.cutoffMass Q
  have hC : 0 ≤ C := A.cutoffMass_nonnegative Q hQ hQnonneg
  let η : ℝ := -A.diagonalLimit Q hQ hQnonneg / (2 * (C + 1))
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (neg_pos.mpr hL) (mul_pos (by norm_num) (by linarith))
  have hpositiveEventually : ∀ᶠ n in atTop,
      0 ≤ A.diagonalSequence Q n + η * C := by
    filter_upwards [A.tendsto_uniform η hη] with n hn
    let p : SchwartzMap ℝ ℝ :=
      A.seq n + η • realCompactIntervalCutoff A.radius
    have hpsupp : tsupport p ⊆ {t : ℝ | |t| ≤ A.radius + 2} := by
      intro t ht
      rcases tsupport_add (A.seq n) (η • realCompactIntervalCutoff A.radius) ht with
        htA | htχ
      · have hle : |t| ≤ A.radius := A.seq_tsupport n htA
        change |t| ≤ A.radius + 2
        linarith
      · have hs := tsupport_smul_subset_right (fun _t : ℝ => η)
          (realCompactIntervalCutoff A.radius) htχ
        rw [realCompactIntervalCutoff_tsupport] at hs
        simpa [abs_of_nonneg A.radius_nonneg] using hs
    have hpnonneg (t : ℝ) : 0 ≤ p t := by
      by_cases ht : t ∈ tsupport (A.seq n)
      · have htR := A.seq_tsupport n ht
        have hχ : realCompactIntervalCutoff A.radius t = 1 := by
          apply realCompactIntervalCutoff_apply_of_abs_le_add_one
          have habs : |t| ≤ A.radius := htR
          rw [abs_of_nonneg A.radius_nonneg]
          linarith
        have hlower : -η < A.seq n t - f t := (abs_lt.mp (hn t)).1
        change 0 ≤ A.seq n t + η * realCompactIntervalCutoff A.radius t
        rw [hχ, mul_one]
        linarith [hf t]
      · have hzero : A.seq n t = 0 := image_eq_zero_of_notMem_tsupport ht
        change 0 ≤ A.seq n t + η * realCompactIntervalCutoff A.radius t
        rw [hzero, zero_add]
        exact mul_nonneg hη.le (realCompactIntervalCutoff_nonnegative A.radius t)
    have hp := Q.compactIntervalDiagonalFunctional_nonnegative_real hQ hQnonneg p hpnonneg
      (show 0 ≤ A.radius + 2 by linarith [A.radius_nonneg]) hpsupp
    have hradius : A.radius + 2 + 2 = A.radius + 4 := by ring
    rw [hradius] at hp
    have hrtc : realToComplexSchwartz p =
        realToComplexSchwartz (A.seq n) +
          (η : ℂ) • realToComplexSchwartz (realCompactIntervalCutoff A.radius) := by
      ext t
      change ((A.seq n t + η * realCompactIntervalCutoff A.radius t : ℝ) : ℂ) =
        (A.seq n t : ℂ) + (η : ℂ) * (realCompactIntervalCutoff A.radius t : ℂ)
      push_cast
      rfl
    rw [hrtc, map_add, map_smul] at hp
    change 0 ≤ A.diagonalSequence Q n + η * C
    simpa [CompactContinuousSchwartzApproximation.diagonalSequence,
      CompactContinuousSchwartzApproximation.cutoffMass,
      Complex.mul_re] using hp.1
  have hlimit : Tendsto (fun n ↦ A.diagonalSequence Q n + η * C) atTop
      (𝓝 (A.diagonalLimit Q hQ hQnonneg + η * C)) :=
    (A.tendsto_diagonalLimit Q hQ hQnonneg).add tendsto_const_nhds
  have hnonnegLimit : 0 ≤ A.diagonalLimit Q hQ hQnonneg + η * C :=
    ge_of_tendsto hlimit hpositiveEventually
  have hηeq : 2 * η * (C + 1) = -A.diagonalLimit Q hQ hQnonneg := by
    dsimp [η]
    field_simp
    <;> ring
  have hηC : η * C ≤ η * (C + 1) := by
    gcongr
    linarith
  linarith

theorem ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalValue_nonnegative
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : C_c(ℝ, ℝ)) (hf : ∀ t, 0 ≤ f t) :
    0 ≤ Q.compactContinuousDiagonalValue hQ hQnonneg f :=
  (chosenCompactContinuousSchwartzApproximation f).diagonalLimit_nonnegative
    Q hQ hQnonneg hf

/-- The real linear extension of the compact spectral diagonal. -/
def ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalLinearMap
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) : C_c(ℝ, ℝ) →ₗ[ℝ] ℝ where
  toFun := Q.compactContinuousDiagonalValue hQ hQnonneg
  map_add' := Q.compactContinuousDiagonalValue_add hQ hQnonneg
  map_smul' c f := by
    simpa only [smul_eq_mul] using
      Q.compactContinuousDiagonalValue_smul hQ hQnonneg c f

/-- The positive real functional on `C_c(ℝ,ℝ)` canonically reconstructed from the Schwartz form. -/
def ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalPositiveLinearMap
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) : C_c(ℝ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk (Q.compactContinuousDiagonalLinearMap hQ hQnonneg) (by
    intro f g hfg
    have hnonneg : 0 ≤ Q.compactContinuousDiagonalValue hQ hQnonneg (g - f) :=
      Q.compactContinuousDiagonalValue_nonnegative hQ hQnonneg (g - f) (fun t => by
        change 0 ≤ g t - f t
        exact sub_nonneg.mpr (hfg t))
    change Q.compactContinuousDiagonalValue hQ hQnonneg f ≤
      Q.compactContinuousDiagonalValue hQ hQnonneg g
    have hsub : Q.compactContinuousDiagonalValue hQ hQnonneg (g - f) =
        Q.compactContinuousDiagonalValue hQ hQnonneg g -
          Q.compactContinuousDiagonalValue hQ hQnonneg f := by
      have heq : g - f = g + (-1 : ℝ) • f := by
        ext t
        change g t - f t = g t + (-1 : ℝ) * f t
        ring
      rw [heq, Q.compactContinuousDiagonalValue_add hQ hQnonneg,
        Q.compactContinuousDiagonalValue_smul hQ hQnonneg]
      ring
    rw [hsub] at hnonneg
    linarith)

@[simp] theorem ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalPositiveLinearMap_apply
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : C_c(ℝ, ℝ)) :
    Q.compactContinuousDiagonalPositiveLinearMap hQ hQnonneg f =
      Q.compactContinuousDiagonalValue hQ hQnonneg f := rfl

/-- The Riesz measure represented by the canonical compact spectral functional. -/
def ContinuousSchwartzSesquilinearForm.compactSpectralRieszMeasure
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) : MeasureTheory.Measure ℝ :=
  RealRMK.rieszMeasure (Q.compactContinuousDiagonalPositiveLinearMap hQ hQnonneg)

/-- Riesz--Markov representation on every compactly supported continuous real spectral test. -/
theorem ContinuousSchwartzSesquilinearForm.integral_compactSpectralRieszMeasure
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : C_c(ℝ, ℝ)) :
    ∫ t, f t ∂Q.compactSpectralRieszMeasure hQ hQnonneg =
      Q.compactContinuousDiagonalValue hQ hQnonneg f := by
  exact RealRMK.integral_rieszMeasure
    (Q.compactContinuousDiagonalPositiveLinearMap hQ hQnonneg) f

/-- A compactly supported real Schwartz map viewed as a compactly supported continuous test. -/
def realSchwartzToCompactContinuous (h : SchwartzMap ℝ ℝ) (hh : HasCompactSupport h) :
    C_c(ℝ, ℝ) :=
  ⟨⟨h, h.continuous⟩, hh⟩

@[simp] theorem realSchwartzToCompactContinuous_apply
    (h : SchwartzMap ℝ ℝ) (hh : HasCompactSupport h) (t : ℝ) :
    realSchwartzToCompactContinuous h hh t = h t := rfl

/-- The constant approximation of a compactly supported real Schwartz test. -/
def constantCompactContinuousSchwartzApproximation
    (h : SchwartzMap ℝ ℝ) (hh : HasCompactSupport h)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    CompactContinuousSchwartzApproximation (realSchwartzToCompactContinuous h hh) where
  radius := R
  radius_nonneg := hR
  seq _ := h
  seq_tsupport _ := hsupp
  tendsto_uniform ε hε := Filter.Eventually.of_forall (fun _n t => by
    change |h t - h t| < ε
    simpa using hε)

theorem constantCompactContinuousSchwartzApproximation_diagonalLimit
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (h : SchwartzMap ℝ ℝ) (hh : HasCompactSupport h)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    (constantCompactContinuousSchwartzApproximation h hh hR hsupp).diagonalLimit
        Q hQ hQnonneg =
      (Q.compactIntervalDiagonalFunctional (R + 4)
        (realToComplexSchwartz h)).re := by
  let A := constantCompactContinuousSchwartzApproximation h hh hR hsupp
  have hconst : Tendsto (A.diagonalSequence Q) atTop
      (𝓝 ((Q.compactIntervalDiagonalFunctional (R + 4)
        (realToComplexSchwartz h)).re)) := by
    have hseq : A.diagonalSequence Q = fun _n : ℕ =>
        (Q.compactIntervalDiagonalFunctional (R + 4)
          (realToComplexSchwartz h)).re := by
      funext n
      rfl
    rw [hseq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (A.tendsto_diagonalLimit Q hQ hQnonneg) hconst

/-- On a compactly supported real Schwartz test, the reconstructed `C_c` functional is exactly
the stabilized local diagonal distribution. -/
theorem ContinuousSchwartzSesquilinearForm.compactContinuousDiagonalValue_realSchwartz
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (h : SchwartzMap ℝ ℝ) (hh : HasCompactSupport h)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    Q.compactContinuousDiagonalValue hQ hQnonneg
        (realSchwartzToCompactContinuous h hh) =
      (Q.compactIntervalDiagonalFunctional (R + 4)
        (realToComplexSchwartz h)).re := by
  rw [Q.compactContinuousDiagonalValue_eq hQ hQnonneg
    (constantCompactContinuousSchwartzApproximation h hh hR hsupp)]
  exact constantCompactContinuousSchwartzApproximation_diagonalLimit
    Q hQ hQnonneg h hh hR hsupp

/-- The real Schwartz modulus square of a complex Schwartz map. -/
def pointwiseNormSqReal (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℝ :=
  (pointwiseMulConj f f).postcompCLM Complex.reCLM

@[simp] theorem pointwiseNormSqReal_apply (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    pointwiseNormSqReal f t = Complex.normSq (f t) := by
  simp [pointwiseNormSqReal, pointwiseMulConj_apply, Complex.mul_conj]

theorem pointwiseNormSqReal_nonnegative (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    0 ≤ pointwiseNormSqReal f t := by
  rw [pointwiseNormSqReal_apply]
  exact Complex.normSq_nonneg _

theorem pointwiseNormSqReal_tsupport_subset (f : SchwartzMap ℝ ℂ) :
    tsupport (pointwiseNormSqReal f) ⊆ tsupport f := by
  apply closure_mono
  intro t ht
  simp only [Function.mem_support, pointwiseNormSqReal_apply, ne_eq] at ht ⊢
  intro hzero
  exact ht (by simp [hzero])

theorem pointwiseNormSqReal_hasCompactSupport
    (f : SchwartzMap ℝ ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (pointwiseNormSqReal f) := by
  exact IsCompact.of_isClosed_subset hf.isCompact
    (isClosed_tsupport _) (pointwiseNormSqReal_tsupport_subset f)

theorem realToComplexSchwartz_pointwiseNormSqReal (f : SchwartzMap ℝ ℂ) :
    realToComplexSchwartz (pointwiseNormSqReal f) = pointwiseMulConj f f := by
  ext t
  simp [pointwiseNormSqReal_apply, pointwiseMulConj_apply, Complex.mul_conj,
    Complex.normSq]

/-- The Riesz measure recovers the original positive quadratic form on every compact spectral
packet. -/
theorem ContinuousSchwartzSesquilinearForm.integral_pointwiseNormSqReal_compactSpectralRieszMeasure
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (f : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hf : tsupport f ⊆ {t : ℝ | |t| ≤ R}) :
    ∫ t, pointwiseNormSqReal f t ∂Q.compactSpectralRieszMeasure hQ hQnonneg =
      (Q.fourierPullback f f).re := by
  let h := pointwiseNormSqReal f
  have hfcompact : HasCompactSupport f := by
    exact IsCompact.of_isClosed_subset
      (show IsCompact (Set.Icc (-R) R) from isCompact_Icc)
      (isClosed_tsupport _) (by
        intro t ht
        have habs := hf ht
        exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩)
  have hhcompact : HasCompactSupport h := pointwiseNormSqReal_hasCompactSupport f hfcompact
  have hhsupp : tsupport h ⊆ {t : ℝ | |t| ≤ R} :=
    (pointwiseNormSqReal_tsupport_subset f).trans hf
  change ∫ t, realSchwartzToCompactContinuous h hhcompact t
      ∂Q.compactSpectralRieszMeasure hQ hQnonneg = _
  rw [Q.integral_compactSpectralRieszMeasure hQ hQnonneg,
    Q.compactContinuousDiagonalValue_realSchwartz hQ hQnonneg h hhcompact hR hhsupp]
  have hstable : Q.compactIntervalDiagonalFunctional R (pointwiseMulConj f f) =
      Q.compactIntervalDiagonalFunctional (R + 4) (pointwiseMulConj f f) := by
    apply Q.fourierPullback_compactIntervalCutoff_stable hQ
    · rw [← realToComplexSchwartz_pointwiseNormSqReal,
        realToComplexSchwartz_tsupport]
      exact hhsupp
    · rw [abs_of_nonneg hR]
    · rw [abs_of_nonneg (by linarith)]
      linarith
  rw [realToComplexSchwartz_pointwiseNormSqReal, ← hstable]
  exact congrArg Complex.re
    (Q.compactIntervalDiagonalFunctional_pointwiseMulConj_self hQ f hR hf)

/-! ## Temperate growth of the represented measure -/

/-- A unit spectral bump centered at `x`, obtained by translating one fixed compact cutoff. -/
def unitSpectralBump (x : ℝ) : SchwartzMap ℝ ℂ :=
  translateCLM ℂ (-x) (compactIntervalCutoff 0)

theorem unitSpectralBump_hasCompactSupport (x : ℝ) :
    HasCompactSupport (unitSpectralBump x) := by
  exact (compactIntervalCutoff_hasCompactSupport 0).comp_homeomorph
    (Homeomorph.addRight (-x))

/-- Every fixed Schwartz seminorm of the translated unit bump has polynomial growth in its
center. -/
theorem seminorm_unitSpectralBump_le (x : ℝ) (k m : ℕ) :
    SchwartzMap.seminorm ℂ k m (unitSpectralBump x) ≤
      (2 + |x|) ^ k *
        (2 ^ k * ((Finset.Iic (k, m)).sup
          (fun p => SchwartzMap.seminorm ℂ p.1 p.2))
            (compactIntervalCutoff 0)) := by
  apply SchwartzMap.seminorm_le_bound' ℂ k m
  · positivity
  intro y
  have h := weighted_iteratedDeriv_translate_bound
    (compactIntervalCutoff 0) (-x) 0 y k m (by simp)
  change |y| ^ k * ‖iteratedDeriv m (fun z : ℝ =>
    compactIntervalCutoff 0 (z + -x)) y‖ ≤ _
  rw [congrFun (iteratedDeriv_comp_add_const m (compactIntervalCutoff 0) (-x)) y]
  simpa [abs_neg, add_assoc] using h

@[simp] theorem unitSpectralBump_apply_of_abs_sub_le_one
    (x t : ℝ) (ht : |t - x| ≤ 1) :
    unitSpectralBump x t = 1 := by
  change compactIntervalCutoff 0 (t + -x) = 1
  apply compactIntervalCutoff_apply_of_abs_le_add_one
  simpa [sub_eq_add_neg] using ht

theorem unitSpectralBump_tsupport_subset (x : ℝ) :
    tsupport (unitSpectralBump x) ⊆ {t : ℝ | |t - x| ≤ 2} := by
  have hcomp := congrArg tsupport
    (show (unitSpectralBump x : ℝ → ℂ) =
      (compactIntervalCutoff 0 : ℝ → ℂ) ∘ (Homeomorph.addRight (-x)) by rfl)
  rw [tsupport_comp_eq_preimage (compactIntervalCutoff 0)
    (Homeomorph.addRight (-x))] at hcomp
  rw [hcomp, compactIntervalCutoff_tsupport]
  intro t ht
  simpa [sub_eq_add_neg] using ht

/-- Continuity of the spectral pullback form gives a polynomial diagonal bound along all
translated unit bumps. -/
theorem ContinuousSchwartzSesquilinearForm.exists_unitSpectralBump_diagonal_polynomial_bound
    (Q : ContinuousSchwartzSesquilinearForm) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖Q.fourierPullback (unitSpectralBump x) (unitSpectralBump x)‖ ≤
        C * (3 + |x|) ^ d := by
  obtain ⟨s, C₀, hC₀, hdiag⟩ := Q.fourierPullback.exists_finset_diagonal_bound
  let d₀ : ℕ := ∑ p ∈ s, p.1
  let c : ℕ × ℕ → ℝ := fun p =>
    2 ^ p.1 * ((Finset.Iic p).sup
      (fun q => SchwartzMap.seminorm ℂ q.1 q.2)) (compactIntervalCutoff 0)
  let A : ℝ := 1 + ∑ p ∈ s, c p
  have hc (p : ℕ × ℕ) : 0 ≤ c p := by dsimp [c]; positivity
  have hA : 1 ≤ A := by
    dsimp [A]
    have : 0 ≤ ∑ p ∈ s, c p := Finset.sum_nonneg fun p _ => hc p
    linarith
  refine ⟨2 * d₀, C₀ * (1 + A) ^ 2, by positivity, ?_⟩
  intro x
  let B : ℝ := 3 + |x|
  have hB : 1 ≤ B := by dsimp [B]; linarith [abs_nonneg x]
  have hsup : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (unitSpectralBump x) ≤
      A * B ^ d₀ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro p hp
    have hpdeg : p.1 ≤ d₀ := by
      dsimp [d₀]
      exact Finset.single_le_sum (fun q _ => Nat.zero_le q.1) hp
    have hpsemi := seminorm_unitSpectralBump_le x p.1 p.2
    have hbase : 2 + |x| ≤ B := by dsimp [B]; linarith
    have hpowbase : (2 + |x|) ^ p.1 ≤ B ^ p.1 :=
      pow_le_pow_left₀ (by positivity) hbase p.1
    have hpowdeg : B ^ p.1 ≤ B ^ d₀ := pow_le_pow_right₀ hB hpdeg
    have hcpA : c p ≤ A := by
      dsimp [A]
      have hle : c p ≤ ∑ q ∈ s, c q :=
        Finset.single_le_sum (fun q _ => hc q) hp
      linarith
    calc
      (schwartzSeminormFamily ℂ ℝ ℂ p) (unitSpectralBump x)
          ≤ (2 + |x|) ^ p.1 * c p := hpsemi
      _ ≤ B ^ d₀ * A := by
        exact mul_le_mul (hpowbase.trans hpowdeg) hcpA (hc p) (by positivity)
      _ = A * B ^ d₀ := by ring
  have hPnonneg : 0 ≤ s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (unitSpectralBump x) := by positivity
  have hpowone : 1 ≤ B ^ d₀ := one_le_pow₀ hB
  have honeP : 1 + s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (unitSpectralBump x) ≤ (1 + A) * B ^ d₀ := by
    calc
      1 + s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (unitSpectralBump x)
          ≤ 1 + A * B ^ d₀ := by linarith
      _ ≤ B ^ d₀ + A * B ^ d₀ := by linarith
      _ = (1 + A) * B ^ d₀ := by ring
  calc
    ‖Q.fourierPullback (unitSpectralBump x) (unitSpectralBump x)‖
        ≤ C₀ * (1 + s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (unitSpectralBump x)) ^ 2 := hdiag _
    _ ≤ C₀ * ((1 + A) * B ^ d₀) ^ 2 := by gcongr
    _ = (C₀ * (1 + A) ^ 2) * B ^ (2 * d₀) := by ring

/-- The mass of every unit interval is bounded by the diagonal value of the corresponding
translated unit bump. -/
theorem ContinuousSchwartzSesquilinearForm.compactSpectralRieszMeasure_real_Icc_le_bump
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (x : ℝ) :
    (Q.compactSpectralRieszMeasure hQ hQnonneg).real (Set.Icc x (x + 1)) ≤
      (Q.fourierPullback (unitSpectralBump x) (unitSpectralBump x)).re := by
  let b : SchwartzMap ℝ ℂ := unitSpectralBump x
  have hbcompact : HasCompactSupport b := unitSpectralBump_hasCompactSupport x
  let h : SchwartzMap ℝ ℝ := pointwiseNormSqReal b
  have hhcompact : HasCompactSupport h :=
    pointwiseNormSqReal_hasCompactSupport b hbcompact
  let g : C_c(ℝ, ℝ) := realSchwartzToCompactContinuous h hhcompact
  have hgnonneg : ∀ t, 0 ≤ g t := fun t => pointwiseNormSqReal_nonnegative b t
  have hgK : ∀ t ∈ Set.Icc x (x + 1), g t = 1 := by
    intro t ht
    have habs : |t - x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hb1 : b t = 1 := unitSpectralBump_apply_of_abs_sub_le_one x t habs
    simp [g, h, pointwiseNormSqReal_apply, hb1]
  let Λ := Q.compactContinuousDiagonalPositiveLinearMap hQ hQnonneg
  have hmapnonneg : 0 ≤ Λ g := Λ.map_nonneg hgnonneg
  have hR : 0 ≤ |x| + 2 := by positivity
  have hbsupp : tsupport b ⊆ {t : ℝ | |t| ≤ |x| + 2} := by
    intro t ht
    have htx : |t - x| ≤ 2 := unitSpectralBump_tsupport_subset x ht
    calc
      |t| = |(t - x) + x| := by ring_nf
      _ ≤ |t - x| + |x| := abs_add_le _ _
      _ ≤ |x| + 2 := by linarith
  have hmap : Λ g =
      (Q.fourierPullback b b).re := by
    change Q.compactContinuousDiagonalValue hQ hQnonneg g = _
    rw [Q.compactContinuousDiagonalValue_realSchwartz hQ hQnonneg
      h hhcompact hR ((pointwiseNormSqReal_tsupport_subset b).trans hbsupp)]
    have hstable : Q.compactIntervalDiagonalFunctional (|x| + 2)
        (pointwiseMulConj b b) =
        Q.compactIntervalDiagonalFunctional ((|x| + 2) + 4)
          (pointwiseMulConj b b) := by
      apply Q.fourierPullback_compactIntervalCutoff_stable
        (R := |x| + 2) (S := |x| + 2) (T := (|x| + 2) + 4) hQ
      · rw [← realToComplexSchwartz_pointwiseNormSqReal,
          realToComplexSchwartz_tsupport]
        exact (pointwiseNormSqReal_tsupport_subset b).trans hbsupp
      · rw [abs_of_nonneg hR]
      · have hTnonneg : 0 ≤ (|x| + 2) + 4 := by positivity
        rw [abs_of_nonneg hTnonneg]
        linarith
    rw [realToComplexSchwartz_pointwiseNormSqReal, ← hstable]
    exact congrArg Complex.re
      (Q.compactIntervalDiagonalFunctional_pointwiseMulConj_self
        hQ b hR hbsupp)
  have hENN := RealRMK.rieszMeasure_le_of_eq_one Λ hgnonneg
    (isCompact_Icc : IsCompact (Set.Icc x (x + 1))) hgK
  have hleft : Q.compactSpectralRieszMeasure hQ hQnonneg
      (Set.Icc x (x + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN
  have hreal := (ENNReal.toReal_le_toReal hleft ENNReal.ofReal_ne_top).2 hENN
  change (Q.compactSpectralRieszMeasure hQ hQnonneg).real
      (Set.Icc x (x + 1)) ≤ (ENNReal.ofReal (Λ g)).toReal at hreal
  rw [ENNReal.toReal_ofReal hmapnonneg, hmap] at hreal
  exact hreal

/-- The reconstructed measure has a polynomial unit-interval mass bound. -/
theorem ContinuousSchwartzSesquilinearForm.exists_compactSpectralRieszMeasure_real_Icc_bound
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      (Q.compactSpectralRieszMeasure hQ hQnonneg).real (Set.Icc x (x + 1)) ≤
        C * (3 + |x|) ^ d := by
  obtain ⟨d, C, hC, hbound⟩ := Q.exists_unitSpectralBump_diagonal_polynomial_bound
  refine ⟨d, C, hC, fun x => ?_⟩
  exact (Q.compactSpectralRieszMeasure_real_Icc_le_bump hQ hQnonneg x).trans
    ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (hbound x)))

theorem intCast_abs_le_one_add_abs_of_mem_Icc
    (n : ℤ) {t : ℝ} (ht : t ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    |(n : ℝ)| ≤ 1 + |t| := by
  have hdiff : |(n : ℝ) - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  calc
    |(n : ℝ)| = |((n : ℝ) - t) + t| := by ring_nf
    _ ≤ |(n : ℝ) - t| + |t| := abs_add_le _ _
    _ ≤ 1 + |t| := by linarith

/-- The continuous polynomial-decay weight used to certify temperate growth. -/
def polynomialDecayContinuous (N : ℕ) : C(ℝ, ℝ) :=
  ⟨fun t => (1 + |t|) ^ (-(N : ℝ)), by
    rw [continuous_iff_continuousAt]
    intro t
    have hb : ContinuousAt (fun y : ℝ => 1 + |y|) t :=
      (continuous_const.add continuous_abs).continuousAt
    exact hb.rpow_const (Or.inl (by positivity))⟩

@[simp] theorem polynomialDecayContinuous_apply (N : ℕ) (t : ℝ) :
    polynomialDecayContinuous N t = (1 + |t|) ^ (-(N : ℝ)) := rfl

theorem polynomialDecayContinuous_restrict_Icc_norm_le
    (N : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖(polynomialDecayContinuous N).restrict
      (⟨Set.Icc (n : ℝ) ((n : ℝ) + 1), isCompact_Icc⟩ : Compacts ℝ)‖ ≤
      |(n : ℝ)| ^ (-(N : ℝ)) := by
  rw [ContinuousMap.norm_le _ (Real.rpow_nonneg (abs_nonneg _) _)]
  intro t
  rw [ContinuousMap.restrict_apply, Real.norm_eq_abs]
  change |(1 + |(t : ℝ)|) ^ (-(N : ℝ))| ≤ |(n : ℝ)| ^ (-(N : ℝ))
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  apply Real.rpow_le_rpow_of_nonpos
  · exact abs_pos.mpr (by exact_mod_cast hn)
  · exact intCast_abs_le_one_add_abs_of_mem_Icc n t.property
  · simp

/-- The Riesz measure reconstructed from a continuous nonnegative momentum-symmetric Schwartz
form has temperate growth. -/
theorem ContinuousSchwartzSesquilinearForm.compactSpectralRieszMeasure_hasTemperateGrowth
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) :
    (Q.compactSpectralRieszMeasure hQ hQnonneg).HasTemperateGrowth := by
  let μ := Q.compactSpectralRieszMeasure hQ hQnonneg
  let Λ := Q.compactContinuousDiagonalPositiveLinearMap hQ hQnonneg
  have hμ : μ = RealRMK.rieszMeasure Λ := rfl
  letI : IsFiniteMeasureOnCompacts μ := hμ ▸
    (RealRMK.regular_rieszMeasure Λ).toIsFiniteMeasureOnCompacts
  obtain ⟨d, C, hC, hmass⟩ :=
    Q.exists_compactSpectralRieszMeasure_real_Icc_bound hQ hQnonneg
  let N : ℕ := d + 3
  let K : ℝ := C * 4 ^ d
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let s : ℤ → Compacts ℝ := fun n =>
    ⟨Set.Icc (n : ℝ) ((n : ℝ) + 1), isCompact_Icc⟩
  let a : ℤ → ℝ := fun n =>
    ‖(polynomialDecayContinuous N).restrict (s n)‖ * μ.real (s n)
  let b : ℤ → ℝ := fun n =>
    if n = 0 then a n else K * |(n : ℝ)| ^ (-3 : ℝ)
  have hbase : Summable (fun n : ℤ => K * |(n : ℝ)| ^ (-3 : ℝ)) :=
    (Real.summable_abs_int_rpow (b := 3) (by norm_num)).mul_left K
  have hb : Summable b := by
    apply hbase.congr_cofinite
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
    simp [b, hn]
  have ha_nonneg (n : ℤ) : 0 ≤ a n := by
    dsimp [a]
    exact mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hab (n : ℤ) : a n ≤ b n := by
    by_cases hn : n = 0
    · simp [b, hn]
    · rw [show b n = K * |(n : ℝ)| ^ (-3 : ℝ) by simp [b, hn]]
      have hnabs : 1 ≤ |(n : ℝ)| := by
        exact_mod_cast Int.one_le_abs hn
      have hnorm := polynomialDecayContinuous_restrict_Icc_norm_le N n hn
      have hmassn : μ.real (s n) ≤ C * (3 + |(n : ℝ)|) ^ d := by
        exact hmass (n : ℝ)
      have hthree : 3 + |(n : ℝ)| ≤ 4 * |(n : ℝ)| := by linarith
      have hpow : (3 + |(n : ℝ)|) ^ d ≤
          (4 * |(n : ℝ)|) ^ d :=
        pow_le_pow_left₀ (by positivity) hthree d
      have hdecay :
          |(n : ℝ)| ^ (-(N : ℝ)) * (C * (3 + |(n : ℝ)|) ^ d) ≤
            K * |(n : ℝ)| ^ (-3 : ℝ) := by
        have hnpos : 0 < |(n : ℝ)| := lt_of_lt_of_le zero_lt_one hnabs
        have hexp : -(N : ℝ) + (d : ℝ) = -3 := by
          dsimp [N]
          push_cast
          ring
        calc
          |(n : ℝ)| ^ (-(N : ℝ)) * (C * (3 + |(n : ℝ)|) ^ d)
              ≤ |(n : ℝ)| ^ (-(N : ℝ)) *
                  (C * (4 * |(n : ℝ)|) ^ d) := by gcongr
          _ = C * 4 ^ d *
                (|(n : ℝ)| ^ (-(N : ℝ)) * |(n : ℝ)| ^ (d : ℝ)) := by
              rw [mul_pow, Real.rpow_natCast]
              ring
          _ = K * |(n : ℝ)| ^ (-3 : ℝ) := by
              rw [← Real.rpow_add hnpos, hexp]
      exact (mul_le_mul hnorm hmassn ENNReal.toReal_nonneg
        (Real.rpow_nonneg (abs_nonneg _) _)).trans hdecay
  have hasum : Summable a := Summable.of_nonneg_of_le ha_nonneg hab hb
  refine ⟨N, ?_⟩
  change Integrable (polynomialDecayContinuous N) μ
  apply integrable_of_summable_norm_restrict (s := s)
  · exact hasum
  · exact iUnion_Icc_intCast ℝ

end SchwartzMap
