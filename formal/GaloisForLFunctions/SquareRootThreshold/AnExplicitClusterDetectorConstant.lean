import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import GaloisForLFunctions.RHTower.SubNyquistHodgeExclusion
import GaloisForLFunctions.SquareRootThreshold.ClusterProductHorizon

/-!
# An explicit local count and cluster-detector horizon

The xi-copy count and the endpoint-source height gap give
`N(t,t+1] ≤ 240 log(|t|+3)` at every height. Substituting this numerical
constant into the cluster detector removes its unspecified local-count input.
-/

noncomputable section
open Complex Set Metric
open scoped BigOperators

namespace GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower Zeta23

private def zetaXiPoint (ρ : ℂ) (hρ : ρ ∈ zetaZeroConfig.carrier) : XiDivisorSupport :=
  ⟨ρ, mem_xi_divisor_support_of_eq_zero ((xi_eq_zero_iff hρ.2.1 (by
    intro he; have hh := hρ.2.2; rw [he] at hh; norm_num at hh)).mpr hρ.1)⟩

private theorem zetaXiPoint_multiplicity (ρ : ℂ) (hρ : ρ ∈ zetaZeroConfig.carrier) :
    (MeromorphicOn.divisor xi univ (zetaXiPoint ρ hρ : ℂ)).toNat =
      zetaZeroConfig.mult ρ := by
  rw [xi_divisor_apply_of_mem (mem_univ _), Int.toNat_natCast]
  change (analyticOrderAt xi ρ).toNat = (analyticOrderAt riemannZeta ρ).toNat
  rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hρ.2]

/-- The xi divisor points in a zeta window, with their original complex values. -/
def zetaWindowXiSupport (a b : ℝ) : Finset XiDivisorSupport :=
  (zetaZeroConfig.finite_window a b).toFinset.attach.map
    ⟨fun (ρ : {ρ : ℂ // ρ ∈ (zetaZeroConfig.finite_window a b).toFinset}) =>
      zetaXiPoint ρ.1 ((zetaZeroConfig.finite_window a b).mem_toFinset.mp ρ.2).1,
      fun _ _ h => Subtype.ext (congrArg (fun q : XiDivisorSupport => (q : ℂ)) h)⟩

/-- All multiplicity copies of the zeros in `(a,b]`. -/
def zetaWindowXiCopies (a b : ℝ) : Finset XiZeroCopy :=
  (zetaWindowXiSupport a b).sigma (fun _ => Finset.univ)

theorem card_zetaWindowXiCopies (a b : ℝ) :
    (zetaWindowXiCopies a b).card = zetaZeroConfig.N a b := by
  classical
  rw [zetaWindowXiCopies, Finset.card_sigma]
  rw [zetaWindowXiSupport, Finset.sum_map]
  simp only [Finset.card_univ, Fintype.card_fin]
  trans ∑ ρ ∈ (zetaZeroConfig.finite_window a b).toFinset.attach, zetaZeroConfig.mult ρ.1
  · exact Finset.sum_congr rfl fun ρ _ => zetaXiPoint_multiplicity ρ.1
      ((zetaZeroConfig.finite_window a b).mem_toFinset.mp ρ.2).1
  · rw [Finset.sum_attach, ZeroConfig.N]
    exact (finsum_mem_eq_finite_toFinset_sum _ (zetaZeroConfig.finite_window a b)).symm

theorem mem_zetaWindowXiCopies_ordinates {a b : ℝ} {q : XiZeroCopy}
    (hq : q ∈ zetaWindowXiCopies a b) : a < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ b := by
  classical
  obtain ⟨hbase, _⟩ := Finset.mem_sigma.mp hq
  rw [zetaWindowXiSupport] at hbase
  obtain ⟨ρ, _, heq⟩ := Finset.mem_map.mp hbase
  have hρ := ((zetaZeroConfig.finite_window a b).mem_toFinset.mp ρ.2).2
  have hv : (ρ.1 : ℂ) = (q.1 : ℂ) :=
    congrArg (fun z : XiDivisorSupport => (z : ℂ)) heq
  rwa [hv] at hρ

/-- The local zeta zero count has the absolute numerical constant `240`. -/
theorem zeta_unit_count_le_240 (t : ℝ) :
    (zetaZeroConfig.N t (t + 1) : ℝ) ≤ 240 * Real.log (|t| + 3) := by
  classical
  let F := zetaWindowXiCopies t (t + 1)
  have hF : ∀ q ∈ F, |(q.1 : ℂ).im - (t + 1 / 2)| ≤ 1 / 2 := by
    intro q hq
    obtain ⟨hlo, hhi⟩ := mem_zetaWindowXiCopies_ordinates hq
    rw [abs_le]
    constructor <;> linarith only [hlo, hhi]
  rw [← card_zetaWindowXiCopies]
  change (F.card : ℝ) ≤ _
  by_cases ht : 4 ≤ |t + 1 / 2|
  · have hcount := card_le_of_ordinates_in_window ht F
      (fun q hq => (hF q hq).trans (by norm_num))
    have hB : 3 ≤ |t| + 3 := by linarith only [abs_nonneg t]
    have hT : |t + 1 / 2| ≤ |t| + 3 := by
      have hh := abs_add_le t (1 / 2)
      norm_num at hh
      linarith only [hh]
    have hpow : 180 ≤ (|t| + 3) ^ 5 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hB 5
      norm_num at hh
      linarith only [hh]
    have hprod : 180 * |t + 1 / 2| ≤ (|t| + 3) ^ 6 := by
      calc 180 * |t + 1 / 2| ≤ 180 * (|t| + 3) :=
          mul_le_mul_of_nonneg_left hT (by norm_num)
        _ ≤ (|t| + 3) ^ 5 * (|t| + 3) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = (|t| + 3) ^ 6 := by ring
    have hlog := Real.log_le_log (by positivity : 0 < 180 * |t + 1 / 2|) hprod
    rw [Real.log_pow] at hlog
    norm_num at hlog
    linarith only [hcount, hlog]
  · have hcard : F.card = 0 := by
      by_contra hne
      obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      have hheight := xiZeroCopy_fortyOne_div_two_lt_im_sq q
      have habs : |(q.1 : ℂ).im| ≤ 9 / 2 := by
        have htri := abs_add_le ((q.1 : ℂ).im - (t + 1 / 2)) (t + 1 / 2)
        rw [sub_add_cancel] at htri
        linarith only [htri, hF q hq, not_le.mp ht]
      nlinarith only [hheight, habs, sq_abs (q.1 : ℂ).im, abs_nonneg (q.1 : ℂ).im]
    rw [hcard, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [abs_nonneg t]))

/-- A high off-line zero has a detector at an entirely explicit aperture,
with no separation or simplicity assumption. -/
theorem not_hodgeIndex_of_explicit_cluster_aperture {δ : ℝ} (hδ : 0 < δ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : δ ≤ |ρ.re - 1 / 2|)
    (hγ : 102 ≤ |ρ.im|) {a : ℝ}
    (hsize : 480000 * Real.log (|ρ.im| + 3) * Real.log (10 ^ 6 / δ) ≤ a) :
    ¬ HodgeIndexAtLevel zetaZeroConfig a := by
  let L := Real.log (|ρ.im| + 3)
  let Λ := Real.log (10 ^ 6 / δ)
  have hst := zetaZeroConfig.strip ρ hρ
  have hδ2 : δ ≤ 1 / 2 := by
    apply hre.trans
    rw [abs_le]
    constructor <;> linarith only [hst.1, hst.2]
  have hL1 : 1 ≤ L := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have hh := Real.exp_one_lt_d9
    linarith only [hh, hγ]
  have hΛ1 : 1 ≤ Λ := by
    have he : Real.exp 1 ≤ 10 ^ 6 / δ := by
      rw [le_div_iff₀ hδ]
      have hh := Real.exp_one_lt_d9
      nlinarith only [hh, hδ2, hδ, Real.exp_pos 1]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr he
  have hcount := RHTower.Nd_le_of_local_count zetaZeroConfig
    (by norm_num : (1 : ℝ) ≤ 240) zeta_unit_count_le_240 (ρ.im - 100) 200
  have hwin : ρ.im - 100 + ((200 : ℕ) : ℝ) = ρ.im + 100 := by norm_num; ring
  rw [hwin] at hcount
  have hlog : Real.log (|ρ.im - 100| + ((200 : ℕ) : ℝ) + 3) ≤ 2 * L := by
    change _ ≤ 2 * Real.log (|ρ.im| + 3)
    calc
      _ ≤ Real.log ((|ρ.im| + 3) ^ 2) := by
        apply Real.log_le_log (by positivity)
        have hh := abs_sub ρ.im 100
        norm_num at hh
        norm_num only [Nat.cast_ofNat]
        nlinarith only [hh, hγ, sq_nonneg (|ρ.im| - 102)]
      _ = 2 * Real.log (|ρ.im| + 3) := by rw [Real.log_pow]; norm_num
  have hn : (zetaZeroConfig.Nd (ρ.im - 100) (ρ.im + 100) : ℝ) ≤ 96000 * L := by
    norm_num only [Nat.cast_ofNat] at hcount hlog
    linarith only [hcount, hlog]
  apply not_hodgeIndex_below_nyquist_horizon zetaZeroConfig
    (by norm_num : (1 : ℝ) ≤ 240) zeta_unit_count_le_240 hρ hδ hre hγ le_rfl
  have hlog240 : Real.log 240 ≤ 240 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hG : Real.log (240 * (|ρ.im| + 3)) ≤ 240 + L := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith only [hlog240]
  have hnl : ((zetaZeroConfig.Nd (ρ.im - 100) (ρ.im + 100) : ℝ) + 1) * Λ ≤
      (96000 * L + L) * Λ :=
    mul_le_mul_of_nonneg_right (by linarith only [hn, hL1]) (by linarith only [hΛ1])
  have hLΛ : L ≤ L * Λ := le_mul_of_one_le_right (by linarith only [hL1]) hΛ1
  have hG' : Real.log (240 * (|ρ.im| + 3)) ≤ 241 * (L * Λ) := by
    linarith only [hG, hL1, hLΛ]
  have hpos : 0 ≤ L * Λ :=
    mul_nonneg (by linarith only [hL1]) (by linarith only [hΛ1])
  change 480000 * L * Λ ≤ a at hsize
  change 4 * (((zetaZeroConfig.Nd (ρ.im - 100) (ρ.im + 100) : ℝ) + 1) * Λ +
    Real.log (240 * (|ρ.im| + 3))) ≤ a
  nlinarith only [hnl, hG', hpos, hsize]

/-- The numerical horizon produces a smooth, compactly supported negative Weil test. -/
theorem exists_smooth_explicit_cluster_detector {δ : ℝ} (hδ : 0 < δ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : δ ≤ |ρ.re - 1 / 2|)
    (hγ : 102 ≤ |ρ.im|) {a : ℝ}
    (hsize : 480000 * Real.log (|ρ.im| + 3) * Real.log (10 ^ 6 / δ) ≤ a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Icc (-(a + 1)) (a + 1) ∧ (zetaZeroConfig.W f f).re < 0 :=
  RHTower.exists_smooth_weil_negative_of_not_hodgeIndex
    (not_hodgeIndex_of_explicit_cluster_aperture hδ hρ hre hγ hsize)


/-- The product detector supplies a numerical horizon also below height `102`. -/
theorem not_hodgeIndex_of_explicit_product_aperture {δ : ℝ} (hδ : 0 < δ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : δ ≤ |ρ.re - 1 / 2|)
    (hγ : 2 ≤ |ρ.im|) {a : ℝ} (ha6 : Real.exp 6 ≤ a) (haδ : 1 / δ ≤ a)
    (hsize : 24000000 * Real.log (|ρ.im| + 306) * Real.log a ≤ a) :
    ¬ HodgeIndexAtLevel zetaZeroConfig a := by
  let L := Real.log (|ρ.im| + 306)
  let ℓ := Real.log a
  have ha0 : 0 < a := (Real.exp_pos 6).trans_le ha6
  have hℓ1 : 1 ≤ ℓ := by
    have hh := Real.log_le_log (Real.exp_pos 6) ha6
    rw [Real.log_exp] at hh
    linarith only [hh]
  have hL1 : 1 ≤ L := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    have hh := Real.exp_one_lt_d9
    linarith only [hh, hγ]
  have hcount := RHTower.Nd_le_of_local_count zetaZeroConfig
    (by norm_num : (1 : ℝ) ≤ 240) zeta_unit_count_le_240 (ρ.im - 101) 202
  have hwin : ρ.im - 101 + ((202 : ℕ) : ℝ) = ρ.im + 101 := by norm_num; ring
  rw [hwin] at hcount
  have hlog : Real.log (|ρ.im - 101| + ((202 : ℕ) : ℝ) + 3) ≤ L := by
    apply Real.log_le_log (by positivity)
    have hh := abs_sub ρ.im 101
    norm_num at hh ⊢
    linarith only [hh]
  have hn : (zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) ≤ 48480 * L := by
    norm_num only [Nat.cast_ofNat] at hcount hlog
    linarith only [hcount, hlog]
  apply _root_.SquareRootThreshold.not_hodgeIndex_below_cluster_product_horizon zetaZeroConfig
    (by norm_num : (1 : ℝ) ≤ 240) zeta_unit_count_le_240 hρ hδ hre hγ ha6 haδ le_rfl
  have hG : Real.log (240 * (|ρ.im| + 4)) ≤ 240 + L := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have hlog240 : Real.log 240 ≤ 240 :=
      (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hlog4 : Real.log (|ρ.im| + 4) ≤ L :=
      Real.log_le_log (by positivity) (by linarith only [])
    exact add_le_add hlog240 hlog4
  have hnl : ((zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) + 1) * ℓ ≤
      (48480 * L + L) * ℓ :=
    mul_le_mul_of_nonneg_right (by linarith only [hn, hL1]) (by linarith only [hℓ1])
  have hLℓ : L ≤ L * ℓ := le_mul_of_one_le_right (by linarith only [hL1]) hℓ1
  have hG' : Real.log (240 * (|ρ.im| + 4)) ≤ 241 * (L * ℓ) := by
    linarith only [hG, hL1, hLℓ]
  have hpos : 0 ≤ L * ℓ :=
    mul_nonneg (by linarith only [hL1]) (by linarith only [hℓ1])
  change 24000000 * L * ℓ ≤ a at hsize
  change 100 * (((zetaZeroConfig.Nd (ρ.im - 101) (ρ.im + 101) : ℝ) + 1) * ℓ +
    Real.log (240 * (|ρ.im| + 4))) ≤ a
  nlinarith only [hnl, hG', hpos, hsize]

/-- Every off-line zeta zero has an explicit product-horizon smooth detector. -/
theorem exists_smooth_explicit_product_detector {δ : ℝ} (hδ : 0 < δ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : δ ≤ |ρ.re - 1 / 2|)
    {a : ℝ} (ha6 : Real.exp 6 ≤ a) (haδ : 1 / δ ≤ a)
    (hsize : 24000000 * Real.log (|ρ.im| + 306) * Real.log a ≤ a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Icc (-(a + 1)) (a + 1) ∧ (zetaZeroConfig.W f f).re < 0 := by
  have hxi : RHTower.xi ρ = 0 :=
    (RHTower.xi_eq_zero_iff hρ.2.1 (by
      intro he; have hh := hρ.2.2; rw [he] at hh; norm_num at hh)).mpr hρ.1
  have hheight := fortyOne_div_two_lt_im_sq_of_xi_eq_zero hxi
  have hγ : 2 ≤ |ρ.im| := by
    nlinarith only [hheight, sq_abs ρ.im, abs_nonneg ρ.im]
  exact RHTower.exists_smooth_weil_negative_of_not_hodgeIndex
    (not_hodgeIndex_of_explicit_product_aperture hδ hρ hre hγ ha6 haδ hsize)

/-- A positive Hodge level confines every high zero to an explicit exponential corridor. -/
theorem depth_lt_explicit_of_hodgeIndex {a : ℝ}
    (hodge : HodgeIndexAtLevel zetaZeroConfig a) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) (hγ : 102 ≤ |ρ.im|) :
    |ρ.re - 1 / 2| < 10 ^ 6 *
      Real.exp (-(a / (480000 * Real.log (|ρ.im| + 3)))) := by
  let δ := |ρ.re - 1 / 2|
  let K := 480000 * Real.log (|ρ.im| + 3)
  have hK : 0 < K := mul_pos (by norm_num) (Real.log_pos (by linarith only [hγ]))
  have hE : 0 < 10 ^ 6 * Real.exp (-(a / K)) := by positivity
  by_contra h
  have hge : 10 ^ 6 * Real.exp (-(a / K)) ≤ δ := not_lt.mp h
  have hδ : 0 < δ := hE.trans_le hge
  have hdiv : 10 ^ 6 / δ ≤ Real.exp (a / K) := by
    rw [div_le_iff₀ hδ]
    have hh := mul_le_mul_of_nonneg_right hge (Real.exp_pos (a / K)).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hh
    simpa only [mul_comm] using hh
  have hlog := Real.log_le_log (by positivity : 0 < 10 ^ 6 / δ) hdiv
  rw [Real.log_exp, le_div_iff₀ hK] at hlog
  exact not_hodgeIndex_of_explicit_cluster_aperture hδ hρ le_rfl hγ
    (by change K * Real.log (10 ^ 6 / δ) ≤ a; linarith only [hlog]) hodge

/-- A closed numerical aperture for the product detector at every height. -/
def explicitProductDetectorAperture (δ γ : ℝ) : ℝ :=
  max (Real.exp 6) (max (1 / δ) (48000000 * Real.log (|γ| + 306)) ^ 2)

private theorem explicitProductDetectorAperture_size (δ γ : ℝ) :
    Real.exp 6 ≤ explicitProductDetectorAperture δ γ ∧
      1 / δ ≤ explicitProductDetectorAperture δ γ ∧
      24000000 * Real.log (|γ| + 306) *
        Real.log (explicitProductDetectorAperture δ γ) ≤
          explicitProductDetectorAperture δ γ := by
  let a := explicitProductDetectorAperture δ γ
  let b := max (1 / δ) (48000000 * Real.log (|γ| + 306))
  have he : Real.exp 6 ≤ a := le_max_left _ _
  have ha0 : 0 < a := (Real.exp_pos 6).trans_le he
  have hL1 : 1 ≤ Real.log (|γ| + 306) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    have hh := Real.exp_one_lt_d9
    linarith only [hh, abs_nonneg γ]
  have hb1 : 1 ≤ b := by
    have hh : 48000000 * Real.log (|γ| + 306) ≤ b := le_max_right _ _
    linarith only [hh, hL1]
  have hb2 : b ^ 2 ≤ a := le_max_right _ _
  have hb : b ≤ a := by nlinarith only [hb1, hb2]
  have hroot : b ≤ Real.sqrt a := by
    nlinarith only [hb1, hb2, Real.sq_sqrt ha0.le, Real.sqrt_nonneg a]
  have hlog : Real.log a ≤ 2 * Real.sqrt a := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ha0)
    have heq := Real.log_pow (Real.sqrt a) 2
    rw [Real.sq_sqrt ha0.le] at heq
    norm_num only [Nat.cast_ofNat] at heq
    linarith only [hh, heq]
  refine ⟨he, (le_max_left _ _).trans hb, ?_⟩
  change 24000000 * Real.log (|γ| + 306) * Real.log a ≤ a
  calc
    _ ≤ 24000000 * Real.log (|γ| + 306) * (2 * Real.sqrt a) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ b * Real.sqrt a := by
      have hh := mul_le_mul_of_nonneg_right
        (le_max_right (1 / δ) (48000000 * Real.log (|γ| + 306))) (Real.sqrt_nonneg a)
      nlinarith only [hh]
    _ ≤ Real.sqrt a * Real.sqrt a :=
      mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg a)
    _ = a := Real.mul_self_sqrt ha0.le

/-- Every off-line zero yields a smooth negative Weil test inside a closed-form
numerical support interval. -/
theorem exists_smooth_detector_at_explicit_product_aperture {δ : ℝ} (hδ : 0 < δ)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : δ ≤ |ρ.re - 1 / 2|) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Icc (-(explicitProductDetectorAperture δ ρ.im + 1))
        (explicitProductDetectorAperture δ ρ.im + 1) ∧ (zetaZeroConfig.W f f).re < 0 := by
  obtain ⟨he, hδa, hsize⟩ := explicitProductDetectorAperture_size δ ρ.im
  exact exists_smooth_explicit_product_detector hδ hρ hre he hδa hsize

#print axioms zeta_unit_count_le_240
#print axioms not_hodgeIndex_of_explicit_cluster_aperture
#print axioms exists_smooth_explicit_cluster_detector
#print axioms not_hodgeIndex_of_explicit_product_aperture
#print axioms exists_smooth_explicit_product_detector
#print axioms depth_lt_explicit_of_hodgeIndex
#print axioms exists_smooth_detector_at_explicit_product_aperture

end GaloisForLFunctions.SquareRootThreshold
