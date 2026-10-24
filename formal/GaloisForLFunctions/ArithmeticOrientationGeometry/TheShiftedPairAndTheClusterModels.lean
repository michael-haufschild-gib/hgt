import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSelectivityBatteryOfOrientation
import GaloisForLFunctions.SquareRootThreshold.WindowedBlindnessForClustersAndProfiles

/-!
# The shifted pair and the cluster models

On a symmetric tempered configuration the orbit of one spectrally generic real test reads the
depth of every zero (`generic_orbitCorr_rate_iff`): its orbit correlation grows like `e^{σt}` iff no
zero lies deeper than `σ`. The battery models of the programme are therefore placed by one number,
and this module computes it for two more of them.

* **The shifted pair of a curve** (`curveShiftedPair`). For a curve datum with normalized eigenvalues
  `β_i`, the product `ζ_C(s − a) ζ_C(s + a)` is again a curve datum, with eigenvalues `q^{±a} β_i`:
  it is closed under conjugation and under the functional equation, its zero configuration is
  tempered and symmetric, and every identity of the scaling datum holds. Its Frobenius traces are
  those of the curve multiplied by `q^{am} + q^{−am}` (`powerSum_curveShiftedPair`), the analogue of
  the weights `Λ(n)(n^a + n^{−a})` of `ζ(s − a) ζ(s + a)` (`RHTower.shiftedPairVonMangoldt`); the
  purity bound fails exactly by `q^{a}`. For a curve satisfying RH every zero of the shifted pair
  has depth `a` (`abs_re_sub_half_shiftedPairConfig`), so a generic orbit has orientation rate
  exactly `a` (`shiftedPair_orbitCorr_rate_iff`) and is not oriented (`shiftedPair_not_oriented`).
* **Clusters** (`fesSymmetric_clusterConfig`, `cluster_heightAverages_blind_orbit_not`). A cluster
  of off-line zeros with symmetric depth profile `d_k` is a symmetric configuration. Every windowed
  Weil form at resolution `r` with `r · TV(d) · sinh(2δr) ≤ 1` is nonnegative on it, for tests of
  every aperture (Square-Root Threshold): height averages do not see it. The orbit of one generic
  test does: its orientation rate is exactly the maximal depth `max_k d_k`
  (`cluster_orbitCorr_rate_iff`), and it is not oriented.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig clusterConfig
  temperedConfig_clusterConfig windowedW re_windowedW_clusterConfig_nonneg depthVariation)

/-! ### A generic orbit reads the depth -/

/-- **A generic orbit reads the depth of every zero.** On a symmetric tempered configuration, for a
spectrally generic real test and `σ ≥ 0`, the orbit correlation grows at most like `e^{σt}` iff every
zero has depth at most `σ`. -/
theorem generic_orbitCorr_rate_iff (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    (x : ScalingCycle) (hgen : RealSpectrallyGeneric Z x.2.2) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (σ * t)) ↔
      ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ σ := by
  rw [orbitCorr_rate_iff_blindAbove Z hZ hFE hσ x, blindAbove_iff_of_generic Z hgen]

/-- A generic orbit of a symmetric configuration with an off-line zero is not oriented. -/
theorem generic_not_oriented (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    (x : ScalingCycle) (hgen : RealSpectrallyGeneric Z x.2.2) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hoff : ρ.re ≠ 1 / 2) : ¬ ∀ t : ℝ, (configScalingDatum Z hZ).HasseWeilAt x t := fun h =>
  hoff ((onLine_iff_blindOffLine_of_generic Z hgen).mp
    (((orientation_tfae Z hZ hFE x).out 0 2).mp h) ρ hρ)

/-! ### The shifted pair of a curve -/

section ShiftedPair

variable {ι : Type*} [Fintype ι]

/-- **The shifted pair of a curve**, `ζ_C(s − a) ζ_C(s + a)`: normalized eigenvalues `q^{a} β_i`
(left copy) and `q^{−a} β_i` (right copy). The functional equation exchanges the copies. -/
def curveShiftedPair (D : CurveDatum ι) (a : ℝ) : CurveDatum (ι ⊕ ι) where
  q := D.q
  one_lt_q := D.one_lt_q
  β := Sum.elim (fun i => ((D.q ^ a : ℝ) : ℂ) * D.β i) (fun i => ((D.q ^ (-a) : ℝ) : ℂ) * D.β i)
  conjPerm := Equiv.sumCongr D.conjPerm D.conjPerm
  β_conjPerm := by
    rintro (i | i) <;>
      simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
        D.β_conjPerm, map_mul, Complex.conj_ofReal]
  fePerm := (Equiv.sumCongr D.fePerm D.fePerm).trans (Equiv.sumComm ι ι)
  β_fePerm := by
    have hq : (0 : ℝ) ≤ D.q := by linarith [D.one_lt_q]
    have h1 : ((D.q ^ (-a) : ℝ) : ℂ) * ((D.q ^ a : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, Real.rpow_neg hq,
        inv_mul_cancel₀ (Real.rpow_pos_of_pos (by linarith [D.one_lt_q]) a).ne', Complex.ofReal_one]
    rintro (i | i)
    · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumComm_apply,
        Sum.swap_inl, Sum.elim_inr, Sum.elim_inl]
      calc ((D.q ^ (-a) : ℝ) : ℂ) * D.β (D.fePerm i) * (((D.q ^ a : ℝ) : ℂ) * D.β i)
          = (((D.q ^ (-a) : ℝ) : ℂ) * ((D.q ^ a : ℝ) : ℂ)) * (D.β (D.fePerm i) * D.β i) := by ring
        _ = 1 := by rw [h1, D.β_fePerm, one_mul]
    · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumComm_apply,
        Sum.swap_inr, Sum.elim_inl, Sum.elim_inr]
      calc ((D.q ^ a : ℝ) : ℂ) * D.β (D.fePerm i) * (((D.q ^ (-a) : ℝ) : ℂ) * D.β i)
          = (((D.q ^ (-a) : ℝ) : ℂ) * ((D.q ^ a : ℝ) : ℂ)) * (D.β (D.fePerm i) * D.β i) := by ring
        _ = 1 := by rw [h1, D.β_fePerm, one_mul]

/-- **The Frobenius traces of the shifted pair** are those of the curve multiplied by
`q^{am} + q^{−am}`. -/
theorem powerSum_curveShiftedPair (D : CurveDatum ι) (a : ℝ) (m : ℕ) :
    (curveShiftedPair D a).powerSum m =
      ((((D.q ^ a) ^ m + (D.q ^ (-a)) ^ m : ℝ)) : ℂ) * D.powerSum m := by
  simp only [CurveDatum.powerSum, curveShiftedPair, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, mul_pow, ← Finset.mul_sum, Complex.ofReal_add, Complex.ofReal_pow]
  ring

theorem norm_curveShiftedPair_inl (D : CurveDatum ι) (a : ℝ) (i : ι) :
    ‖(curveShiftedPair D a).β (Sum.inl i)‖ = D.q ^ a * ‖D.β i‖ := by
  show ‖((D.q ^ a : ℝ) : ℂ) * D.β i‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [D.one_lt_q]) _)]

theorem norm_curveShiftedPair_inr (D : CurveDatum ι) (a : ℝ) (i : ι) :
    ‖(curveShiftedPair D a).β (Sum.inr i)‖ = D.q ^ (-a) * ‖D.β i‖ := by
  show ‖((D.q ^ (-a) : ℝ) : ℂ) * D.β i‖ = _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [D.one_lt_q]) _)]

/-- The shifted pair of a curve satisfying RH lies in the strip for `0 ≤ a ≤ ½`. -/
theorem curveShiftedPair_strip (D : CurveDatum ι) (hU : ∀ i, ‖D.β i‖ = 1) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a ≤ 1 / 2) : ∀ j, ‖(curveShiftedPair D a).β j‖ ≤ (curveShiftedPair D a).sqrtq := by
  have hq : 1 ≤ D.q := D.one_lt_q.le
  have hs : (curveShiftedPair D a).sqrtq = D.q ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  rintro (i | i)
  · rw [norm_curveShiftedPair_inl, hU, mul_one, hs]
    exact Real.rpow_le_rpow_of_exponent_le hq ha
  · rw [norm_curveShiftedPair_inr, hU, mul_one, hs]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)

/-- The shifted pair of a curve satisfying RH is impure for `a ≠ 0`. -/
theorem curveShiftedPair_not_pure (D : CurveDatum ι) [Nonempty ι] (hU : ∀ i, ‖D.β i‖ = 1)
    {a : ℝ} (ha : a ≠ 0) : ¬ ∀ j, ‖(curveShiftedPair D a).β j‖ = 1 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 := h (Sum.inl i)
  rw [norm_curveShiftedPair_inl, hU, mul_one] at h1
  have h2 := congrArg Real.log h1
  rw [Real.log_rpow (by linarith [D.one_lt_q]), Real.log_one] at h2
  exact ha ((mul_eq_zero.mp h2).resolve_right D.log_q_pos.ne')

variable (D : CurveDatum ι) (hU : ∀ i, ‖D.β i‖ = 1) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2)

/-- The zeros of the shifted pair of a curve satisfying RH. -/
abbrev shiftedPairConfig : ZeroConfig :=
  (curveShiftedPair D a).curveConfig (curveShiftedPair_strip D hU ha0 ha)

theorem temperedConfig_shiftedPairConfig : TemperedConfig (shiftedPairConfig D hU ha0 ha) :=
  (curveShiftedPair D a).temperedConfig_curveConfig _

theorem fesSymmetric_shiftedPairConfig : FESymmetric (shiftedPairConfig D hU ha0 ha) :=
  fesSymmetric_curveConfig _ _

/-- **Every zero of the shifted pair has depth exactly `a`.** -/
theorem abs_re_sub_half_shiftedPairConfig {ρ : ℂ} (hρ : ρ ∈ (shiftedPairConfig D hU ha0 ha).carrier) :
    |ρ.re - 1 / 2| = a := by
  obtain ⟨⟨j, k⟩, rfl⟩ := hρ
  rw [CurveDatum.re_zetaZero, add_sub_cancel_left]
  have hq : 0 < D.q := by linarith [D.one_lt_q]
  have hl : Real.log D.q ≠ 0 := D.log_q_pos.ne'
  show |Real.log ‖(curveShiftedPair D a).β j‖ / Real.log D.q| = a
  rcases j with i | i
  · rw [norm_curveShiftedPair_inl, hU, mul_one, Real.log_rpow hq, mul_div_cancel_right₀ _ hl,
      abs_of_nonneg ha0]
  · rw [norm_curveShiftedPair_inr, hU, mul_one, Real.log_rpow hq, mul_div_cancel_right₀ _ hl,
      abs_neg, abs_of_nonneg ha0]

/-- **The orientation rate of a generic cycle of the shifted pair is `a`.** -/
theorem shiftedPair_orbitCorr_rate_iff [Nonempty ι] (x : ScalingCycle)
    (hgen : RealSpectrallyGeneric (shiftedPairConfig D hU ha0 ha) x.2.2) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
      |(configScalingDatum _ (temperedConfig_shiftedPairConfig D hU ha0 ha)).orbitCorr x t| ≤
        K * Real.exp (σ * t)) ↔ a ≤ σ := by
  rw [generic_orbitCorr_rate_iff _ _ (fesSymmetric_shiftedPairConfig D hU ha0 ha) x hgen hσ]
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hmem : (curveShiftedPair D a).zetaZero (Sum.inl i) 0 ∈
      (shiftedPairConfig D hU ha0 ha).carrier := ⟨⟨Sum.inl i, 0⟩, rfl⟩
  constructor
  · intro h
    rw [← abs_re_sub_half_shiftedPairConfig D hU ha0 ha hmem]
    exact h _ hmem
  · intro h ρ hρ
    rw [abs_re_sub_half_shiftedPairConfig D hU ha0 ha hρ]
    exact h

/-- **The shifted pair orients no generic cycle** for `0 < a`. -/
theorem shiftedPair_not_oriented [Nonempty ι] (ha' : 0 < a) (x : ScalingCycle)
    (hgen : RealSpectrallyGeneric (shiftedPairConfig D hU ha0 ha) x.2.2) :
    ¬ ∀ t : ℝ,
      (configScalingDatum _ (temperedConfig_shiftedPairConfig D hU ha0 ha)).HasseWeilAt x t := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hmem : (curveShiftedPair D a).zetaZero (Sum.inl i) 0 ∈
      (shiftedPairConfig D hU ha0 ha).carrier := ⟨⟨Sum.inl i, 0⟩, rfl⟩
  refine generic_not_oriented _ _ (fesSymmetric_shiftedPairConfig D hU ha0 ha) x hgen hmem
    fun hre => ?_
  have h := abs_re_sub_half_shiftedPairConfig D hU ha0 ha hmem
  rw [hre, sub_self, abs_zero] at h
  exact ha'.ne h

end ShiftedPair

/-! ### Clusters -/

section Clusters

variable {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k)
  (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)

theorem one_sub_verticalLatticePoint (δ : ℝ) (k : ℤ) :
    1 - _root_.RHTower.verticalLatticePoint L δ k =
      _root_.RHTower.verticalLatticePoint L (-δ) (-k) := by
  apply Complex.ext <;>
    simp only [_root_.RHTower.verticalLatticePoint, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Int.cast_neg] <;> ring

/-- **A cluster with a symmetric depth profile is symmetric under the functional equation.** -/
theorem fesSymmetric_clusterConfig (hS : ∀ k, k ∈ S → -k ∈ S) (hdS : ∀ k ∈ S, d (-k) = d k) :
    FESymmetric (clusterConfig hL S d hd0 hd1) := by
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · rcases hρ with (⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · refine Or.inl (Or.inl ⟨⟨-k.1, fun h => k.2 (by simpa using hS _ h)⟩, ?_⟩)
      rw [one_sub_verticalLatticePoint, neg_zero]
    · refine Or.inr ⟨⟨-k.1, hS _ k.2⟩, ?_⟩
      rw [one_sub_verticalLatticePoint]
      exact congrArg (fun δ => _root_.RHTower.verticalLatticePoint L (-δ) (-k.1)) (hdS _ k.2)
    · refine Or.inl (Or.inr ⟨⟨-k.1, hS _ k.2⟩, ?_⟩)
      rw [one_sub_verticalLatticePoint, neg_neg]
      exact congrArg (fun δ => _root_.RHTower.verticalLatticePoint L δ (-k.1)) (hdS _ k.2)
  · show (if (1 - ρ).re = 1 / 2 then 2 else 1) = (if ρ.re = 1 / 2 then 2 else 1)
    have hre : (1 - ρ).re = 1 - ρ.re := by simp
    by_cases h : ρ.re = 1 / 2
    · rw [if_pos h, if_pos (by rw [hre, h]; norm_num)]
    · rw [if_neg h, if_neg (fun h' => h (by rw [hre] at h'; linarith))]

/-- The depths of a cluster: `0` on the line and `d_k` at the `k`-th cluster point. -/
theorem cluster_depth_le_iff {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ ρ ∈ (clusterConfig hL S d hd0 hd1).carrier, |ρ.re - 1 / 2| ≤ σ) ↔ ∀ k ∈ S, d k ≤ σ := by
  have hre : ∀ δ (k : ℤ), (_root_.RHTower.verticalLatticePoint L δ k).re - 1 / 2 = δ := fun δ k => by
    simp [_root_.RHTower.verticalLatticePoint]
  constructor
  · intro h k hk
    have := h _ (Or.inl (Or.inr ⟨⟨k, hk⟩, rfl⟩))
    rwa [hre, abs_of_pos (hd0 k hk)] at this
  · rintro h _ ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩)
    · rw [hre, abs_zero]; exact hσ
    · rw [hre, abs_of_pos (hd0 k k.2)]; exact h k k.2
    · rw [hre, abs_neg, abs_of_pos (hd0 k k.2)]; exact h k k.2

/-- **The orientation rate of a generic cycle of a symmetric cluster is its maximal depth.** -/
theorem cluster_orbitCorr_rate_iff (hS : ∀ k, k ∈ S → -k ∈ S) (hdS : ∀ k ∈ S, d (-k) = d k)
    (x : ScalingCycle) (hgen : RealSpectrallyGeneric (clusterConfig hL S d hd0 hd1) x.2.2)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
      |(configScalingDatum _ (temperedConfig_clusterConfig hL S d hd0 hd1)).orbitCorr x t| ≤
        K * Real.exp (σ * t)) ↔ ∀ k ∈ S, d k ≤ σ := by
  rw [generic_orbitCorr_rate_iff _ _ (fesSymmetric_clusterConfig hL S d hd0 hd1 hS hdS) x hgen hσ,
    cluster_depth_le_iff hL S d hd0 hd1 hσ]

/-- **Height averages are blind to a cluster; one generic orbit is not.** For a symmetric cluster
with depths at most `δ` and `r · TV(d) · sinh(2δr) ≤ 1`, `4r ≤ L`: every windowed Weil form with
window supported in `[−r, r]` is nonnegative, for tests of every aperture; yet a generic orbit is
not oriented, and its orientation rate is the maximal depth. -/
theorem cluster_heightAverages_blind_orbit_not (hS : ∀ k, k ∈ S → -k ∈ S)
    (hdS : ∀ k ∈ S, d (-k) = d k) {δ r : ℝ} (hdδ : ∀ k ∈ S, d k ≤ δ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hrL : 4 * r ≤ L) (hTV : r * depthVariation S d * Real.sinh (2 * δ * r) ≤ 1) {k₀ : ℤ}
    (hk₀ : k₀ ∈ S) :
    (∀ {f η : ℝ → ℂ}, ContDiff ℝ 2 f → HasCompactSupport f → ContDiff ℝ 2 η →
        tsupport η ⊆ Set.Icc (-r) r → 0 ≤ (windowedW (clusterConfig hL S d hd0 hd1) f η).re) ∧
      ∃ x : ScalingCycle,
        (¬ ∀ t : ℝ,
          (configScalingDatum _ (temperedConfig_clusterConfig hL S d hd0 hd1)).HasseWeilAt x t) ∧
        ∀ σ : ℝ, 0 ≤ σ → ((∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
          |(configScalingDatum _ (temperedConfig_clusterConfig hL S d hd0 hd1)).orbitCorr x t| ≤
            K * Real.exp (σ * t)) ↔ ∀ k ∈ S, d k ≤ σ) := by
  refine ⟨fun hf hfc hη hηs =>
    re_windowedW_clusterConfig_nonneg hL S d hd0 hd1 hdδ hδ hr hrL hTV hf hfc hη hηs, ?_⟩
  obtain ⟨f, hf, hgen⟩ := exists_realSpectrallyGeneric (clusterConfig hL S d hd0 hd1)
  have hmem : _root_.RHTower.verticalLatticePoint L (d k₀) k₀ ∈
      (clusterConfig hL S d hd0 hd1).carrier := Or.inl (Or.inr ⟨⟨k₀, hk₀⟩, rfl⟩)
  refine ⟨(0, 0, ⟨f, hf⟩), generic_not_oriented _ _
      (fesSymmetric_clusterConfig hL S d hd0 hd1 hS hdS) _ hgen hmem fun h => ?_,
    fun σ hσ => cluster_orbitCorr_rate_iff hL S d hd0 hd1 hS hdS _ hgen hσ⟩
  have hre : (_root_.RHTower.verticalLatticePoint L (d k₀) k₀).re = 1 / 2 + d k₀ := rfl
  rw [hre] at h
  linarith [hd0 k₀ hk₀]

end Clusters

end GaloisForLFunctions.ArithmeticOrientationGeometry
