import GaloisForLFunctions.RHTower.ThetaDerivativePacketLogConcavity
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

/-!
# Theta derivative packets: the dark divisor theorem and the spectral-infinity boundary

The deformations `k_t = k + t k^{(4m)}` combine into one statement: for small `t > 0` they are
positive, even, globally strongly log-concave sources with every exponential moment and the moments
of `k` below order `4m`, whose transforms `XiC(z)(1 + t z^{4m})` keep the real divisor of `XiC` and
add the simple nonreal packet `α_j`.

Let `𝓔` be the smooth even sources whose derivatives decay at every exponential rate, topologised
by `p_{A,n}(f) = sup e^{A|x|}|f^{(n)}(x)|`, and `𝓗 ⊆ 𝓔` those with only real transform zeros. Then
`p_{A,n}(k_t - k) = t p_{A,n}(k^{(4m)})`, `k_t → k` in `𝓔` and `k_t ∉ 𝓗`; so `k` lies in the
closure of `𝓔 \ 𝓗` (on the boundary of `𝓗` exactly when the Riemann hypothesis holds, since
`k ∈ 𝓗 ↔ RH`). Consequently finitely many strict inequalities for statistics continuous at `k`
hold at some positive strongly log-concave source with a nonreal transform zero, and every
Schwartz neighbourhood of `k` contains such a source with the moments of `k` through any fixed
depth and the complete real divisor of `XiC`.
-/
open Filter Topology MeasureTheory Set Metric
open scoped ContDiff

namespace RHTower

noncomputable section

/-! ## The dark divisor packet as one theorem -/

/-- **Positive theta deformations with an exact invisible off-line divisor packet.** For `m ≥ 1`
there is `ε > 0` such that for every `0 < t < ε` the source `k_t = k + t k^{(4m)}` is strictly
positive, even and globally strongly log-concave, has every exponential moment and the moments of
`k` below order `4m`, has entire transform `XiC(z)(1 + t z^{4m})`, the same real zeros as `XiC` with
the same multiplicities, and the additional simple nonreal zeros `α_j`, none on either axis. -/
theorem thetaDerivativePacket_dark_divisor (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε →
      (∀ x, 0 < thetaDerivativePacket m t x) ∧
      (∀ x, thetaDerivativePacket m t (-x) = thetaDerivativePacket m t x) ∧
      (∃ δ > 0, ∀ x, iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x ≤ -δ) ∧
      (∀ c : ℝ, Integrable (fun x => Real.exp (c * |x|) * |thetaDerivativePacket m t x|)) ∧
      (∀ j < 4 * m, ∫ x : ℝ, x ^ j * thetaDerivativePacket m t x =
        ∫ x : ℝ, x ^ j * thetaCuspFullSource x) ∧
      (∀ z : ℂ, sourceTransform (thetaDerivativePacketC m t) z = XiC z * (1 + t * z ^ (4 * m))) ∧
      (∀ x : ℝ, analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (x : ℂ) =
        analyticOrderAt XiC x) ∧
      (∀ j < 4 * m, sourceTransform (thetaDerivativePacketC m t) (thetaPacketRoot m t j) = 0 ∧
        analyticOrderAt (sourceTransform (thetaDerivativePacketC m t)) (thetaPacketRoot m t j) =
          analyticOrderAt XiC (thetaPacketRoot m t j) + 1 ∧
        (thetaPacketRoot m t j).re ≠ 0 ∧ (thetaPacketRoot m t j).im ≠ 0) := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_thetaDerivativePacket_stronglyLogConcave m hm
  refine ⟨ε, hε, fun t ht htε => ⟨(h t ht.le htε).1, thetaDerivativePacket_neg m t,
    ⟨δ, hδ, (h t ht.le htε).2⟩, integrable_exp_abs_mul_abs_thetaDerivativePacket m t,
    fun j hj => integral_pow_mul_thetaDerivativePacket_of_lt m t hj,
    sourceTransform_thetaDerivativePacketC m t,
    fun x => (thetaDerivativePacketC_real_divisor m ht.le x).2.2, fun j _ => ?_⟩⟩
  exact ⟨sourceTransform_thetaDerivativePacketC_root m hm ht j,
    analyticOrderAt_thetaDerivativePacketC_root m hm ht j,
    thetaPacketRoot_re_ne_zero m hm ht j, thetaPacketRoot_im_ne_zero m hm ht j⟩

/-! ## The ambient source topology -/

/-- The ambient class `𝓔`: smooth even real sources all of whose derivatives decay at every
exponential rate. -/
def ThetaExpDecaySource (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x, f (-x) = f x) ∧
    ∀ (A : ℝ) (n : ℕ), ∃ C, ∀ x, Real.exp (A * |x|) * |iteratedDeriv n f x| ≤ C

/-- The class `𝓗` of sources in `𝓔` whose entire transform has only real zeros. -/
def ThetaRealRootedSource (f : ℝ → ℝ) : Prop :=
  ThetaExpDecaySource f ∧ ∀ z : ℂ, sourceTransform (fun x => (f x : ℂ)) z = 0 → z.im = 0

/-- The seminorm `p_{A,n}(f) = sup_x e^{A|x|} |f^{(n)}(x)|`. -/
def thetaExpSeminorm (A : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ⨆ x, Real.exp (A * |x|) * |iteratedDeriv n f x|

/-- The neighbourhood filter of `g` within `𝓔` for the topology of the seminorms `p_{A,n}`. -/
def thetaExpSourceNhds (g : ℝ → ℝ) : Filter (ℝ → ℝ) :=
  ⨅ (A : ℝ) (n : ℕ) (ε : ℝ) (_ : 0 < ε), 𝓟 {f | ThetaExpDecaySource f ∧
    ∀ x, Real.exp (A * |x|) * |iteratedDeriv n (fun y => f y - g y) x| ≤ ε}

theorem thetaExpDecaySource_thetaCuspFullSource : ThetaExpDecaySource thetaCuspFullSource :=
  ⟨contDiff_thetaCuspFullSource, thetaCuspFullSource_neg,
    fun A n => thetaCuspFullSource_derivative_exp_bound A n⟩

theorem thetaExpDecaySource_thetaDerivativePacket (m : ℕ) (t : ℝ) :
    ThetaExpDecaySource (thetaDerivativePacket m t) := by
  refine ⟨contDiff_thetaDerivativePacket m t, thetaDerivativePacket_neg m t, fun A n => ?_⟩
  obtain ⟨C₁, h₁⟩ := thetaCuspFullSource_derivative_exp_bound A n
  obtain ⟨C₂, h₂⟩ := thetaCuspFullSource_derivative_exp_bound A (n + 4 * m)
  refine ⟨C₁ + |t| * C₂, fun x => ?_⟩
  rw [iteratedDeriv_thetaDerivativePacket]
  have hx := Real.exp_pos (A * |x|)
  have habs := abs_add_le (iteratedDeriv n thetaCuspFullSource x)
    (t * iteratedDeriv (n + 4 * m) thetaCuspFullSource x)
  rw [abs_mul] at habs
  have h1 := h₁ x
  have h2 := h₂ x
  calc Real.exp (A * |x|) * |iteratedDeriv n thetaCuspFullSource x +
        t * iteratedDeriv (n + 4 * m) thetaCuspFullSource x|
      ≤ Real.exp (A * |x|) * (|iteratedDeriv n thetaCuspFullSource x| +
          |t| * |iteratedDeriv (n + 4 * m) thetaCuspFullSource x|) :=
        mul_le_mul_of_nonneg_left habs hx.le
    _ = Real.exp (A * |x|) * |iteratedDeriv n thetaCuspFullSource x| +
          |t| * (Real.exp (A * |x|) * |iteratedDeriv (n + 4 * m) thetaCuspFullSource x|) := by ring
    _ ≤ C₁ + |t| * C₂ := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg t))

/-- For `t ≠ 0` the packet root `α_0` is a nonreal zero, so `k_t ∉ 𝓗`. -/
theorem not_thetaRealRootedSource_thetaDerivativePacket (m : ℕ) (hm : 0 < m) {t : ℝ}
    (ht : 0 < t) : ¬ThetaRealRootedSource (thetaDerivativePacket m t) := by
  rintro ⟨-, h⟩
  exact thetaPacketRoot_im_ne_zero m hm ht 0
    (h _ (sourceTransform_thetaDerivativePacketC_root m hm ht 0))

/-- The literal source lies in `𝓗` exactly when the Riemann hypothesis holds. -/
theorem thetaRealRootedSource_thetaCuspFullSource_iff :
    ThetaRealRootedSource thetaCuspFullSource ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  have hT : ∀ z, sourceTransform (fun x => (thetaCuspFullSource x : ℂ)) z = XiC z :=
    sourceTransform_thetaSourceC
  constructor
  · rintro ⟨-, h⟩ z hz
    exact h z (by rw [hT]; exact hz)
  · intro h
    exact ⟨thetaExpDecaySource_thetaCuspFullSource, fun z hz => h z (by rw [← hT]; exact hz)⟩

theorem iteratedDeriv_thetaDerivativePacket_sub (m : ℕ) (t : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y => thetaDerivativePacket m t y - thetaCuspFullSource y) =
      fun x => t * iteratedDeriv (n + 4 * m) thetaCuspFullSource x := by
  have hfun : (fun y => thetaDerivativePacket m t y - thetaCuspFullSource y) =
      fun y => t * iteratedDeriv (4 * m) thetaCuspFullSource y := by
    funext y; simp [thetaDerivativePacket]
  rw [hfun]
  funext x
  rw [iteratedDeriv_const_mul t ((contDiff_iteratedDeriv_thetaCuspFullSource _).contDiffAt.of_le
    (by exact_mod_cast le_top)), iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, ← iteratedDeriv_eq_iterate]

/-- **Exact seminorm scaling.** `p_{A,n}(k_t - k) = t p_{A,n}(k^{(4m)})` for `t ≥ 0`. -/
theorem thetaExpSeminorm_thetaDerivativePacket_sub (m : ℕ) {t : ℝ} (ht : 0 ≤ t) (A : ℝ)
    (n : ℕ) :
    thetaExpSeminorm A n (fun y => thetaDerivativePacket m t y - thetaCuspFullSource y) =
      t * thetaExpSeminorm A n (iteratedDeriv (4 * m) thetaCuspFullSource) := by
  unfold thetaExpSeminorm
  rw [Real.mul_iSup_of_nonneg ht, iteratedDeriv_thetaDerivativePacket_sub]
  congr 1
  funext x
  rw [iteratedDeriv_eq_iterate (n := n) (f := iteratedDeriv (4 * m) thetaCuspFullSource),
    iteratedDeriv_eq_iterate (n := 4 * m), ← Function.iterate_add_apply, ← iteratedDeriv_eq_iterate,
    abs_mul, abs_of_nonneg ht]
  ring

theorem tendsto_thetaExpSeminorm_thetaDerivativePacket_sub (m : ℕ) (A : ℝ) (n : ℕ) :
    Tendsto (fun t => thetaExpSeminorm A n
      (fun y => thetaDerivativePacket m t y - thetaCuspFullSource y)) (𝓝[≥] 0) (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => t * thetaExpSeminorm A n
      (iteratedDeriv (4 * m) thetaCuspFullSource)) (𝓝[≥] 0) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const
      (thetaExpSeminorm A n (iteratedDeriv (4 * m) thetaCuspFullSource))
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (thetaExpSeminorm_thetaDerivativePacket_sub m ht A n).symm

/-- `k_t → k` in the source topology of `𝓔` as `t ↓ 0`. -/
theorem tendsto_thetaDerivativePacket_thetaExpSourceNhds (m : ℕ) :
    Tendsto (fun t => thetaDerivativePacket m t) (𝓝[>] 0)
      (thetaExpSourceNhds thetaCuspFullSource) := by
  simp only [thetaExpSourceNhds, tendsto_iInf, tendsto_principal]
  intro A n ε hε
  obtain ⟨C, hC⟩ := exists_expWeighted_iteratedDeriv_thetaDerivativePacket_sub_le m A n
  have hC0 : 0 ≤ C := le_trans (by positivity) ((hC 1 0).trans (by simp))
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), |t| * C ≤ ε := by
    have h : Tendsto (fun t : ℝ => |t| * C) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_abs.tendsto (0 : ℝ)).mul_const C
      rw [abs_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact h.eventually (ge_mem_nhds hε)
  filter_upwards [hsmall] with t ht
  exact ⟨thetaExpDecaySource_thetaDerivativePacket m t, fun x => (hC t x).trans ht⟩

/-- **Spectral-infinity boundary theorem.** Every neighbourhood of the literal source in the
exponentially weighted source topology contains a positive, even, globally strongly log-concave
source in `𝓔 \ 𝓗`. -/
theorem exists_mem_thetaExpSourceNhds_not_realRooted (m : ℕ) (hm : 0 < m) {s : Set (ℝ → ℝ)}
    (hs : s ∈ thetaExpSourceNhds thetaCuspFullSource) :
    ∃ f ∈ s, ThetaExpDecaySource f ∧ ¬ThetaRealRootedSource f ∧ (∀ x, 0 < f x) ∧
      ∃ δ > 0, ∀ x, iteratedDeriv 2 (fun y => Real.log (f y)) x ≤ -δ := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_thetaDerivativePacket_stronglyLogConcave m hm
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), thetaDerivativePacket m t ∈ s ∧ 0 < t ∧ t < ε := by
    filter_upwards [tendsto_thetaDerivativePacket_thetaExpSourceNhds m hs, self_mem_nhdsWithin,
      Ioo_mem_nhdsGT hε] with t h1 h2 h3
    exact ⟨h1, h2, h3.2⟩
  obtain ⟨t, hts, ht, htε⟩ := hev.exists
  exact ⟨_, hts, thetaExpDecaySource_thetaDerivativePacket m t,
    not_thetaRealRootedSource_thetaDerivativePacket m hm ht, (h t ht.le htε).1, δ, hδ,
    (h t ht.le htε).2⟩

/-- Under the Riemann hypothesis the literal source lies on the boundary of `𝓗`: it belongs to
`𝓗`, yet every neighbourhood meets `𝓔 \ 𝓗`. -/
theorem thetaCuspFullSource_boundary_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ThetaRealRootedSource thetaCuspFullSource ∧
      ∀ s ∈ thetaExpSourceNhds thetaCuspFullSource, ∃ f ∈ s,
        ThetaExpDecaySource f ∧ ¬ThetaRealRootedSource f := by
  refine ⟨thetaRealRootedSource_thetaCuspFullSource_iff.2 hRH, fun s hs => ?_⟩
  obtain ⟨f, hf, h1, h2, -⟩ := exists_mem_thetaExpSourceNhds_not_realRooted 1 one_pos hs
  exact ⟨f, hf, h1, h2⟩

/-- **No strict continuous margins certify real-rootedness.** If finitely many source statistics
are continuous at the literal source in the topology of `𝓔` and strictly positive there, then they
are all strictly positive at some positive, even, globally strongly log-concave source of `𝓔` whose
transform has a nonreal zero. -/
theorem exists_not_realRooted_of_strict_continuous_margins {ι : Type*} [Finite ι]
    (C : ι → (ℝ → ℝ) → ℝ)
    (hC : ∀ i, Tendsto (C i) (thetaExpSourceNhds thetaCuspFullSource)
      (𝓝 (C i thetaCuspFullSource)))
    (hpos : ∀ i, 0 < C i thetaCuspFullSource) :
    ∃ f, ThetaExpDecaySource f ∧ ¬ThetaRealRootedSource f ∧ (∀ x, 0 < f x) ∧
      (∃ δ > 0, ∀ x, iteratedDeriv 2 (fun y => Real.log (f y)) x ≤ -δ) ∧ ∀ i, 0 < C i f := by
  have hs : {f | ∀ i, 0 < C i f} ∈ thetaExpSourceNhds thetaCuspFullSource := by
    have : ∀ i, ∀ᶠ f in thetaExpSourceNhds thetaCuspFullSource, 0 < C i f :=
      fun i => (hC i).eventually (lt_mem_nhds (hpos i))
    exact (eventually_all.2 this)
  obtain ⟨f, hf, h1, h2, h3, h4⟩ := exists_mem_thetaExpSourceNhds_not_realRooted 1 one_pos hs
  exact ⟨f, h1, h2, h3, h4, hf⟩

/-! ## The Schwartz-neighbourhood consequence -/

/-- **Finite moment data and the full real divisor do not force real zeros.** For every moment
depth `J` and every Schwartz neighbourhood of the literal theta source there is a strictly
positive, even, globally strongly log-concave Schwartz source in it with the moments of `k` through
`J`, the same real zeros as `XiC` with multiplicities, and a nonreal zero of its entire
transform. -/
theorem exists_thetaSchwartz_nearby_same_moments_real_divisor_nonreal_zero (J : ℕ)
    {U : Set (SchwartzMap ℝ ℝ)} (hU : U ∈ 𝓝 thetaCuspSchwartzReal) :
    ∃ g : SchwartzMap ℝ ℝ, g ∈ U ∧ (∀ x, 0 < g x) ∧ (∀ x, g (-x) = g x) ∧
      (∃ δ > 0, ∀ x, iteratedDeriv 2 (fun y => Real.log (g y)) x ≤ -δ) ∧
      (∀ j ≤ J, ∫ x : ℝ, x ^ j * g x = ∫ x : ℝ, x ^ j * thetaCuspFullSource x) ∧
      (∀ x : ℝ, analyticOrderAt (sourceTransform (fun y => (g y : ℂ))) (x : ℂ) =
        analyticOrderAt XiC x) ∧
      ∃ z : ℂ, z.im ≠ 0 ∧ sourceTransform (fun y => (g y : ℂ)) z = 0 := by
  set m := J + 1
  have hm : 0 < m := Nat.succ_pos J
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_thetaDerivativePacket_stronglyLogConcave m hm
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), thetaDerivativePacketSchwartz m t ∈ U ∧ 0 < t ∧ t < ε := by
    filter_upwards [((tendsto_thetaDerivativePacketSchwartz m).mono_left nhdsWithin_le_nhds) hU,
      self_mem_nhdsWithin, Ioo_mem_nhdsGT hε] with t h1 h2 h3
    exact ⟨h1, h2, h3.2⟩
  obtain ⟨t, htU, ht, htε⟩ := hev.exists
  have hcoe : (fun y => ((thetaDerivativePacketSchwartz m t y : ℝ) : ℂ)) =
      thetaDerivativePacketC m t := by
    funext y; simp [thetaDerivativePacketC]
  refine ⟨thetaDerivativePacketSchwartz m t, htU, fun x => by simpa using (h t ht.le htε).1 x,
    fun x => by simpa using thetaDerivativePacket_neg m t x, ⟨δ, hδ, fun x => ?_⟩,
    fun j hj => ?_, fun x => ?_, thetaPacketRoot m t 0, thetaPacketRoot_im_ne_zero m hm ht 0, ?_⟩
  · simpa using (h t ht.le htε).2 x
  · simpa using integral_pow_mul_thetaDerivativePacket_of_lt m t (by omega : j < 4 * m)
  · rw [hcoe]; exact (thetaDerivativePacketC_real_divisor m ht.le x).2.2
  · rw [hcoe]; exact sourceTransform_thetaDerivativePacketC_root m hm ht 0

end

end RHTower
