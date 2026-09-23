import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionDegreeCenteredArithmeticSourceRecession

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

def projectiveLowEdgeAnchor (s : ℕ → ℝ) : ℝ :=
  4 * HTGeometry.monicOrthoBeta s 1 /
    (HTGeometry.monicOrthoAlpha s 0 ^ (2 : ℕ) + 2 * HTGeometry.monicOrthoBeta s 1)

theorem projectiveLowEdgeAnchor_pos
    {s : ℕ → ℝ} {N : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hN : 1 < N) :
    0 < projectiveLowEdgeAnchor s := by
  have hb := HTGeometry.monicOrthoBeta_pos_below h (by omega : 0 < 1) hN
  unfold projectiveLowEdgeAnchor
  positivity

theorem tendsto_projectiveLowEdgeAnchor :
    Tendsto (fun w : ℝ => projectiveLowEdgeAnchor
      (xiShiftedFarRightNormalizedMoment w)) atTop (nhds 1) := by
  have ha := tendsto_dimensionless_monicOrthoAlpha 0
  have hb := tendsto_dimensionless_monicOrthoBeta (n := 1) (by omega)
  rw [monicOrthoBeta_normalizedCentralBinom_one] at hb
  have hden : ((1 / 2 : ℝ) ^ (2 : ℕ) + 2 * (1 / 8 : ℝ)) ≠ 0 := by norm_num
  have h := (hb.const_mul 4).div ((ha.pow 2).add (hb.const_mul 2)) hden
  convert h using 1
  · funext w
    simp [projectiveLowEdgeAnchor]
  · norm_num

theorem lowEdge_scalar_completion (a b μ : ℝ)
    (hden : a ^ (2 : ℕ) + 2 * b ≠ 0) :
    2 * (a - μ) ^ (2 : ℕ) + 4 * b -
        (4 * b / (a ^ (2 : ℕ) + 2 * b)) * μ ^ (2 : ℕ) =
      2 / (a ^ (2 : ℕ) + 2 * b) * (a * μ - (a ^ (2 : ℕ) + 2 * b)) ^ (2 : ℕ) := by
  field_simp [hden]
  ring

theorem projectiveGaussRootSpread_succ_sub
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n + 1 < N) :
    projectiveGaussRootSpread s (n + 1) - projectiveGaussRootSpread s n =
      (n : ℝ) / (n + 1 : ℝ) *
          (HTGeometry.monicOrthoAlpha s n -
            (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) / (n : ℝ)) ^ (2 : ℕ) +
        2 * HTGeometry.monicOrthoBeta s n := by
  rw [projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory h (by omega) hnN,
    projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory h hn (by omega)]
  rw [Finset.sum_range_succ]
  unfold projectiveJacobiLowerAlphaDispersion
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn10 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hn10]
  ring

theorem projectiveGaussRootSpread_strictMono_step
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n + 1 < N) :
    projectiveGaussRootSpread s n < projectiveGaussRootSpread s (n + 1) := by
  rw [sub_pos.symm, projectiveGaussRootSpread_succ_sub h hn hnN]
  have hbeta := HTGeometry.monicOrthoBeta_pos_below h (by omega : 0 < n) (by omega)
  positivity

theorem projectiveGaussRootSpread_ge_two_beta_prefix
    {s : ℕ → ℝ} {N n J : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) (hJn : J ≤ n) :
    2 * (∑ j ∈ Finset.range J, HTGeometry.monicOrthoBeta s j) ≤
      projectiveGaussRootSpread s n := by
  rw [projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory h hn hnN]
  have hdisp := projectiveJacobiLowerAlphaDispersion_nonneg s (by omega : 0 < n)
  have hsub : Finset.range J ⊆ Finset.range n := Finset.range_mono hJn
  have hbeta_nonneg : ∀ j ∈ Finset.range n,
      0 ≤ HTGeometry.monicOrthoBeta s j := by
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (by omega) (by
        have := Finset.mem_range.mp hj
        omega)).le
  have hsum : (∑ j ∈ Finset.range J, HTGeometry.monicOrthoBeta s j) ≤
      ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj _ => hbeta_nonneg j hj)
  linarith

theorem projectiveSurplus_ge_lowEdgeAnchor_mul_flux_sq_div_degree
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n + 1 < N) :
    let F := 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      HTGeometry.monicOrthoAlpha s n
    let D := 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
      HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) +
      4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
      2 * (n + 1 : ℝ) *
        (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1))
    (2 * n + 1 : ℝ) * D - F ^ (2 : ℕ) ≥
      projectiveLowEdgeAnchor s / (2 * n + 1 : ℝ) * F ^ (2 : ℕ) := by
  dsimp only
  let c : ℝ := 2 * (n : ℝ) + 1
  let F : ℝ := 2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
    HTGeometry.monicOrthoAlpha s n
  let μ : ℝ := F / c
  let a := HTGeometry.monicOrthoAlpha s 0
  let b := HTGeometry.monicOrthoBeta s 1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hb : 0 < b := by
    dsimp only [b]
    exact HTGeometry.monicOrthoBeta_pos_below h (by omega) (by omega)
  have hden : a ^ (2 : ℕ) + 2 * b ≠ 0 := by positivity
  have hcenter_expand :
      (∑ j ∈ Finset.range n,
        (HTGeometry.monicOrthoAlpha s j - μ) ^ (2 : ℕ)) =
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) -
          2 * μ * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
          (n : ℝ) * μ ^ (2 : ℕ) := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hmid : (∑ x ∈ Finset.range n,
        2 * HTGeometry.monicOrthoAlpha s x * μ) =
        2 * μ * ∑ x ∈ Finset.range n, HTGeometry.monicOrthoAlpha s x := by
      calc
        (∑ x ∈ Finset.range n, 2 * HTGeometry.monicOrthoAlpha s x * μ) =
            ∑ x ∈ Finset.range n, (2 * μ) * HTGeometry.monicOrthoAlpha s x := by
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = 2 * μ * ∑ x ∈ Finset.range n, HTGeometry.monicOrthoAlpha s x :=
          (Finset.mul_sum (Finset.range n) (fun x => HTGeometry.monicOrthoAlpha s x)
            (2 * μ)).symm
    rw [hmid]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsumalpha :
      c * (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
          HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ)) - F ^ (2 : ℕ) =
        c * (2 * (∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j - μ) ^ (2 : ℕ)) +
          (HTGeometry.monicOrthoAlpha s n - μ) ^ (2 : ℕ)) := by
    rw [hcenter_expand]
    unfold μ
    field_simp [hc.ne']
    ring
  have hcenter_nonneg : ∀ j ∈ Finset.range n,
      0 ≤ (HTGeometry.monicOrthoAlpha s j - μ) ^ (2 : ℕ) :=
    fun _ _ => sq_nonneg _
  have ha_mem : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have halpha_floor :
      2 * (a - μ) ^ (2 : ℕ) ≤
        2 * (∑ j ∈ Finset.range n,
          (HTGeometry.monicOrthoAlpha s j - μ) ^ (2 : ℕ)) := by
    have hsingle : (a - μ) ^ (2 : ℕ) ≤
        ∑ j ∈ Finset.range n, (HTGeometry.monicOrthoAlpha s j - μ) ^ (2 : ℕ) := by
      calc
        (a - μ) ^ (2 : ℕ) = ∑ j ∈ ({0} : Finset ℕ),
            (HTGeometry.monicOrthoAlpha s j - μ) ^ (2 : ℕ) := by simp [a]
        _ ≤ ∑ j ∈ Finset.range n,
            (HTGeometry.monicOrthoAlpha s j - μ) ^ (2 : ℕ) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.mpr ha_mem)
            (fun j hj _ => hcenter_nonneg j hj)
    linarith
  have hbeta_floor : 4 * b ≤
      4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) := by
    have hnonneg : ∀ j ∈ Finset.range n,
        0 ≤ HTGeometry.monicOrthoBeta s j := by
      intro j hj
      rcases j with _ | j
      · simp [HTGeometry.monicOrthoBeta]
      · exact (HTGeometry.monicOrthoBeta_pos_below h (by omega) (by
          have := Finset.mem_range.mp hj
          omega)).le
    have hone : 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    have hsingle : b ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
      calc
        b = ∑ j ∈ ({1} : Finset ℕ), HTGeometry.monicOrthoBeta s j := by simp [b]
        _ ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.mpr hone)
            (fun j hj _ => hnonneg j hj)
    linarith
  have hboundary : 0 ≤ 2 * (n + 1 : ℝ) *
      (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
    have hbn := HTGeometry.monicOrthoBeta_pos_below h (by omega : 0 < n) (by omega)
    have hbn1 := HTGeometry.monicOrthoBeta_pos_below h (by omega : 0 < n + 1) hnN
    positivity
  have hbase :
      c * (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
        HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) +
        4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j) +
        2 * (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1))) - F ^ (2 : ℕ) ≥
        c * (2 * (a - μ) ^ (2 : ℕ) + 4 * b) := by
    rw [show c * (_ + _ + _ + _) - F ^ (2 : ℕ) =
        (c * (2 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
          HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ)) - F ^ (2 : ℕ)) +
        c * (4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j)) +
        c * (2 * (n + 1 : ℝ) *
          (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1))) by ring]
    rw [hsumalpha]
    have hlast : 0 ≤ (HTGeometry.monicOrthoAlpha s n - μ) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  have hscalar : projectiveLowEdgeAnchor s * μ ^ (2 : ℕ) ≤
      2 * (a - μ) ^ (2 : ℕ) + 4 * b := by
    change 4 * b / (a ^ (2 : ℕ) + 2 * b) * μ ^ (2 : ℕ) ≤ 2 * (a - μ) ^ (2 : ℕ) + 4 * b
    have hid := lowEdge_scalar_completion a b μ hden
    have hrhs : 0 ≤ 2 / (a ^ (2 : ℕ) + 2 * b) *
        (a * μ - (a ^ (2 : ℕ) + 2 * b)) ^ (2 : ℕ) := by positivity
    nlinarith
  have hFmu : F = c * μ := by
    unfold μ
    field_simp [hc.ne']
  change projectiveLowEdgeAnchor s / c * F ^ (2 : ℕ) ≤ _
  rw [hFmu]
  have hanchor_nonneg : 0 ≤ projectiveLowEdgeAnchor s :=
    (projectiveLowEdgeAnchor_pos h (by omega)).le
  have hscaled := mul_le_mul_of_nonneg_left hscalar hc.le
  have hrhs : projectiveLowEdgeAnchor s / c * (c * μ) ^ (2 : ℕ) =
      c * (projectiveLowEdgeAnchor s * μ ^ (2 : ℕ)) := by
    field_simp [hc.ne']
  rw [hrhs]
  exact le_trans hscaled hbase

theorem exists_uniform_lowEdgeAnchor_half :
    ∃ W : ℝ, ∀ w ≥ W,
      (1 / 2 : ℝ) ≤ projectiveLowEdgeAnchor
        (xiShiftedFarRightNormalizedMoment w) := by
  have hev := tendsto_projectiveLowEdgeAnchor.eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨W, hW⟩ := eventually_atTop.1 hev
  exact ⟨W, fun w hw => (hW w hw).le⟩

theorem dimensionlessProjectiveArithmeticSurplus_ge_harmonic
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef)
    (hanchor : (1 / 2 : ℝ) ≤ projectiveLowEdgeAnchor
      (xiShiftedFarRightNormalizedMoment w)) :
    dimensionlessProjectiveArithmeticSurplus w n ≥
      1 / (2 * (2 * n + 1 : ℝ)) * dimensionlessCumulativeJacobiFlux w n ^ (2 : ℕ) := by
  let s := xiShiftedFarRightNormalizedMoment w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hbase := projectiveSurplus_ge_lowEdgeAnchor_mul_flux_sq_div_degree
    hbelow hn (by omega : n + 1 < n + 2)
  have hgap := dimensionlessProjectiveArithmeticSurplus_eq_cauchyGap
    (w := w) hw (by omega : 0 < n) hH
  rw [hgap]
  dsimp only [s] at hbase
  have hdeg : 0 < (2 * n + 1 : ℝ) := by positivity
  have hcoeff : 1 / (2 * (2 * n + 1 : ℝ)) ≤
      projectiveLowEdgeAnchor (xiShiftedFarRightNormalizedMoment w) /
        (2 * n + 1 : ℝ) := by
    rw [show 1 / (2 * (2 * n + 1 : ℝ)) =
      (1 / 2 : ℝ) / (2 * n + 1 : ℝ) by
        field_simp [hdeg.ne']]
    exact (div_le_div_iff_of_pos_right hdeg).2 hanchor
  exact le_trans (mul_le_mul_of_nonneg_right hcoeff
    (sq_nonneg (dimensionlessCumulativeJacobiFlux w n))) hbase

theorem xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual
    {w : ℝ} (hw : 1 < w) (n : ℕ)
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) n).PosDef) :
    (xiShiftedFarRightNormalizedHankelMatrix w n).PosDef := by
  let D := xiShiftedFarRightDilation w n
  let H := xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) n
  let c : ℝ := 2 * w / Real.log w
  have hc : 0 < c := div_pos (mul_pos (by norm_num) (lt_trans zero_lt_one hw))
    (Real.log_pos hw)
  have hH' : H.PosDef := by
    have heq : H = HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) n := by
      ext i j
      rfl
    rwa [heq]
  have hconj : (star D * H * D).PosDef :=
    (xiShiftedFarRightDilation_isUnit
      (ne_of_gt (lt_trans zero_lt_one hw)) n).posDef_star_left_conjugate_iff.mpr hH'
  have hscaled := hconj.smul hc
  rw [xiShiftedFarRightNormalizedHankelMatrix_eq_congruence hw n]
  exact hscaled

theorem tendsto_projectiveGaussRootSpread_along_cofinal_positive_blocks
    (w : ℕ → ℝ) (n : ℕ → ℕ)
    (hw : Tendsto w atTop atTop) (hn : Tendsto n atTop atTop)
    (hH : ∀ᶠ l in atTop, (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment (w l)) (n l + 2)).PosDef) :
    Tendsto (fun l => projectiveGaussRootSpread
      (xiShiftedFarRightNormalizedMoment (w l)) (n l)) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 2 (16 * A + 3))
  have hJ2 : 2 ≤ J := by
    have hJreal : (2 : ℝ) < J := lt_of_le_of_lt (le_max_left _ _) hJ
    exact_mod_cast hJreal.le
  have hbeta : ∀ j ∈ Finset.Icc 2 J,
      Tendsto (fun l => HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment (w l)) j) atTop (nhds (1 / 16 : ℝ)) := by
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have ht := (tendsto_dimensionless_monicOrthoBeta (n := j) (by omega)).comp hw
    rw [monicOrthoBeta_normalizedCentralBinom_of_two_le hj2] at ht
    exact ht
  have heach : ∀ j ∈ Finset.Icc 2 J,
      ∀ᶠ l in atTop, (1 / 32 : ℝ) < HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment (w l)) j := by
    intro j hj
    exact (hbeta j hj).eventually (eventually_gt_nhds (by norm_num))
  have hall := (eventually_all_finset (Finset.Icc 2 J)).2 heach
  have hnlarge : ∀ᶠ l in atTop, J + 1 ≤ n l := (tendsto_atTop.1 hn) (J + 1)
  filter_upwards [hall, hnlarge, hH] with l hl hnl hHl
  let s := xiShiftedFarRightNormalizedMoment (w l)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHl
  have hprefix := projectiveGaussRootSpread_ge_two_beta_prefix
    hbelow (by omega : 2 ≤ n l) (by omega : n l < n l + 2) (by omega : J + 1 ≤ n l)
  have hsumlower : ((J - 1 : ℕ) : ℝ) * (1 / 32 : ℝ) <
      ∑ j ∈ Finset.Icc 2 J, HTGeometry.monicOrthoBeta s j := by
    have hnonempty : (Finset.Icc 2 J).Nonempty := by
      exact ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hJ2⟩⟩
    have := Finset.sum_lt_sum_of_nonempty hnonempty (fun j hj => hl j hj)
    simpa [Finset.sum_const, Nat.card_Icc, hJ2, nsmul_eq_mul, s] using this
  have hsubset : Finset.Icc 2 J ⊆ Finset.range (J + 1) := by
    intro j hj
    have := (Finset.mem_Icc.mp hj).2
    exact Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ j ∈ Finset.range (J + 1),
      0 ≤ HTGeometry.monicOrthoBeta s j := by
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by
        have := Finset.mem_range.mp hj
        omega)).le
  have hsubsum : (∑ j ∈ Finset.Icc 2 J, HTGeometry.monicOrthoBeta s j) ≤
      ∑ j ∈ Finset.range (J + 1), HTGeometry.monicOrthoBeta s j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j hj _ => hnonneg j hj)
  have hJA : A < 2 * (((J - 1 : ℕ) : ℝ) * (1 / 32 : ℝ)) := by
    have hJraw : 16 * A + 3 < (J : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hJ
    rw [Nat.cast_sub (by omega : 1 ≤ J)]
    norm_num
    linarith
  dsimp only [s] at hprefix hsumlower hsubsum
  linarith

theorem tendsto_projectiveGaussRootSpread_along_cofinal_actual_positive_blocks
    (w : ℕ → ℝ) (n : ℕ → ℕ)
    (hw : Tendsto w atTop atTop) (hn : Tendsto n atTop atTop)
    (hH : ∀ l, (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef) :
    Tendsto (fun l => projectiveGaussRootSpread
      (xiShiftedFarRightNormalizedMoment (w l)) (n l)) atTop atTop := by
  apply tendsto_projectiveGaussRootSpread_along_cofinal_positive_blocks w n hw hn
  filter_upwards [hw.eventually_gt_atTop 1] with l hwl
  exact xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual hwl (n l + 2) (hH l)

/-- Closed Route-U synchronization surface: no premise is asserted outside the quantified
schedule, and both conclusions are unconditional theorems about the literal shifted-Xi source. -/
theorem routeU_cofinalSpread_and_harmonicWork_closed :
    (∀ (w : ℕ → ℝ) (n : ℕ → ℕ),
      Tendsto w atTop atTop → Tendsto n atTop atTop →
      (∀ l, (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef) →
      Tendsto (fun l => projectiveGaussRootSpread
        (xiShiftedFarRightNormalizedMoment (w l)) (n l)) atTop atTop) ∧
    (∃ W : ℝ, ∀ w ≥ W, ∀ n : ℕ, 2 ≤ n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef →
      dimensionlessProjectiveArithmeticSurplus w n ≥
        1 / (2 * (2 * n + 1 : ℝ)) * dimensionlessCumulativeJacobiFlux w n ^ (2 : ℕ)) := by
  constructor
  · intro w n hw hn hH
    exact tendsto_projectiveGaussRootSpread_along_cofinal_actual_positive_blocks
      w n hw hn hH
  · obtain ⟨W, hW⟩ := exists_uniform_lowEdgeAnchor_half
    refine ⟨max W 2, ?_⟩
    intro w hw n hn hH
    have hwW : W ≤ w := le_trans (le_max_left _ _) hw
    have hw1 : 1 < w := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hw)
    exact dimensionlessProjectiveArithmeticSurplus_ge_harmonic hw1 hn hH (hW w hwW)

end
end XiShiftedCanonicalAdmission
end RHTower
