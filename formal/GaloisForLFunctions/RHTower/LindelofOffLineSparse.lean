import GaloisForLFunctions.RHTower.XiCosineShiftSparseCluster
import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# The Lindelöf hypothesis makes off-line zeros sparse, and the cosine level an eventual strip

**Lindelöf hypothesis (half-plane form).** For every `ε > 0` there is `C ≥ 1` with
`‖ζ(s)‖ ≤ C |Im s|^ε` whenever `Re s ≥ ½` and `|Im s| ≥ 1`. By convexity of the Lindelöf function
this is equivalent to the bound on the critical line alone.

**Theorem** (`offLineSparse_of_lindelof`, Backlund's direction). Under the Lindelöf hypothesis, for
every `η, L, c > 0`, every window of length `2L` at a large height `t` contains at most `c log t`
zero copies with `|β − ½| > η`.

**Corollary** (`eventually_strip_of_lindelof_of_cosShiftXi_real`). Under the Lindelöf hypothesis,
if `(ξ(s+h) + ξ(s−h))/2 = cos(hD)Ξ` has only real zeros for some `h > 0`, then for every `ε > 0` all
zeros of large height satisfy `β ≥ ½ − h − ε`. So under LH the real-rootedness threshold of the
differenced `ξ` is an eventual zero-free strip.

**Proof.** Jensen's inequality for `ζ` between the discs of radii `3/2 − η/8` and `3/2` centred at
`2 + η/2 + iτ`. The outer circle stays in `Re s ≥ ½ + η/2`, where `‖ζ‖ ≤ C(|τ| + 2)^ε`. At the centre
`‖ζ‖ ≥ 1/3`. Since `log((3/2)/(3/2 − η/8)) ≥ η/12`, the inner disc carries at most
`(12/η)(log 3C + ε log(|τ| + 2))` zeros. It contains every zero with `Re ρ ≥ ½ + η` and
`|Im ρ − τ| ≤ √η/2`. Covering the window by `O(L/√η)` such discs, and reflecting `ρ ↦ 1 − ρ` for the
left half, gives `O_{η,L}(log C_ε + ε log t)` copies. Then let `ε → 0`.
-/

open Complex Filter Topology Set Metric

namespace RHTower.LindelofSparse

open GaloisForLFunctions.HTGeometry RHTower.DeBruijn RHTower.CosineDefectBudget
  RHTower.CosineSparseCluster

noncomputable section

/-- The Lindelöf hypothesis in half-plane form. -/
def LindelofHalfPlane : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ C * |s.im| ^ ε

/-! ## Copies in a disc and the divisor of `ζ` -/

theorem analyticOnNhd_riemannZeta_of_ne_one {B : Set ℂ} (hB : ∀ ρ ∈ B, ρ ≠ 1) :
    AnalyticOnNhd ℂ riemannZeta B := by
  have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact (hd.analyticOnNhd isOpen_ne).mono fun z hz => hB z hz

/-- A finite set of zero copies whose points lie in a closed disc in `Re > 0` avoiding `1` has at
most as many elements as the zero count of `ζ` in the disc. -/
theorem card_le_divisor_sum_of_ball {c : ℂ} {R : ℝ}
    (hB : ∀ ρ ∈ closedBall c |R|, 0 < ρ.re ∧ ρ ≠ 1) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, (q.1 : ℂ) ∈ closedBall c |R|) :
    (F.card : ℝ) ≤ ((∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c |R|)) u : ℤ) : ℝ) := by
  classical
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall c |R|) :=
    analyticOnNhd_riemannZeta_of_ne_one fun ρ hρ => (hB ρ hρ).2
  set D := MeromorphicOn.divisor riemannZeta (closedBall c |R|) with hD
  have hDnn : ∀ ρ, 0 ≤ D ρ := by
    intro ρ
    by_cases hρ : ρ ∈ closedBall c |R|
    · rw [hD, MeromorphicOn.divisor_apply hana.meromorphicOn hρ, (hana ρ hρ).meromorphicOrderAt_eq,
        WithTop.untop₀_nonneg]
      cases h : analyticOrderAt riemannZeta ρ with
      | top => simp
      | coe n => simp
    · have := D.supportWithinDomain
      have h0 : D ρ = 0 := by
        by_contra hne
        exact hρ (this hne)
      rw [h0]
  have hDxi : ∀ ρ ∈ closedBall c |R|, (MeromorphicOn.divisor xi Set.univ) ρ = D ρ := by
    intro ρ hρ
    rw [MeromorphicOn.divisor_apply xi_meromorphicOn_univ (Set.mem_univ ρ), hD,
      MeromorphicOn.divisor_apply hana.meromorphicOn hρ,
      meromorphicOrderAt_xi_eq_zeta (hB ρ hρ).1 (hB ρ hρ).2]
  set T : Finset ℂ := F.image (fun q : XiZeroCopy => (q.1 : ℂ)) with hT
  have hmaps : Set.MapsTo (fun q : XiZeroCopy => (q.1 : ℂ)) (F : Set XiZeroCopy) (T : Set ℂ) :=
    fun q hq => Finset.mem_image_of_mem _ hq
  have hfiber : ∀ ρ ∈ T, ((F.filter fun q : XiZeroCopy => (q.1 : ℂ) = ρ).card : ℤ) ≤ D ρ := by
    intro ρ hρT
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hρT
    have hDρ := hDxi _ (hF q₀ hq₀)
    rw [← hDρ]
    have hcard : (F.filter fun q : XiZeroCopy => (q.1 : ℂ) = (q₀.1 : ℂ)).card
        ≤ ((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)).toNat := by
      refine (Finset.card_le_card_of_injOn (fun q : XiZeroCopy => (q.2 : ℕ))
        (t := Finset.range (((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)).toNat)) ?_ ?_).trans
        (by rw [Finset.card_range])
      · intro q hq
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
        rw [Finset.coe_range, Set.mem_Iio]
        have h := q.2.isLt
        exact lt_of_lt_of_eq h (by rw [hq.2])
      · intro q hq q' hq' hqq'
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
        have h1 : q.1 = q'.1 := Subtype.ext (hq.2.trans hq'.2.symm)
        exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).mpr hqq')
    have hnn : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ) := by rw [hDρ]; exact hDnn _
    calc ((F.filter fun q : XiZeroCopy => (q.1 : ℂ) = (q₀.1 : ℂ)).card : ℤ)
        ≤ (((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ)).toNat : ℤ) := by exact_mod_cast hcard
      _ = (MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ) := Int.toNat_of_nonneg hnn
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  set S : Finset ℂ := hfin.toFinset with hS
  have hsupp : Function.support (fun u => D u) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [hS, Set.Finite.coe_toFinset]
    exact hu
  have hfinsum : (∑ᶠ u, D u) = ∑ u ∈ S, D u := finsum_eq_sum_of_support_subset _ hsupp
  have hTle : (∑ ρ ∈ T, D ρ) ≤ ∑ ρ ∈ S, D ρ := by
    calc (∑ ρ ∈ T, D ρ) ≤ ∑ ρ ∈ T ∪ S, D ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun ρ _ _ => hDnn ρ)
      _ = ∑ ρ ∈ S, D ρ := by
          symm
          refine Finset.sum_subset Finset.subset_union_right fun ρ _ hρS => ?_
          by_contra hne
          exact hρS (by rw [hS, Set.Finite.mem_toFinset]; exact hne)
  have hcardT : (F.card : ℤ) ≤ ∑ ρ ∈ T, D ρ := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    exact Finset.sum_le_sum hfiber
  have : (F.card : ℤ) ≤ ∑ᶠ u, D u := by rw [hfinsum]; exact hcardT.trans hTle
  exact_mod_cast this

/-! ## One Jensen disc under the Lindelöf hypothesis -/

theorem spectral_im_eq (q : XiZeroCopy) : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  simp [xiSpectralPoint, Complex.mul_im]

theorem spectral_re_eq (q : XiZeroCopy) : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint, Complex.mul_re]

/-- The disc centre `2 + η/2 + iτ`. -/
def lhCentre (η τ : ℝ) : ℂ := ((2 + η / 2 : ℝ) : ℂ) + (τ : ℂ) * I

theorem re_im_sub_lhCentre (η τ : ℝ) (z : ℂ) :
    (z - lhCentre η τ).re = z.re - (2 + η / 2) ∧ (z - lhCentre η τ).im = z.im - τ := by
  simp [lhCentre]

theorem mem_closedBall_lhCentre {η τ : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) {ρ : ℂ}
    (hre : 1 / 2 + η ≤ ρ.re) (hre1 : ρ.re < 1) (him : |ρ.im - τ| ≤ Real.sqrt η / 2) :
    ρ ∈ closedBall (lhCentre η τ) |3 / 2 - η / 8| := by
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by linarith)]
  obtain ⟨hr, hi⟩ := re_im_sub_lhCentre η τ ρ
  have hsq : ‖ρ - lhCentre η τ‖ ^ 2 = (ρ.re - (2 + η / 2)) ^ 2 + (ρ.im - τ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hr, hi]; ring
  have h1 : (ρ.re - (2 + η / 2)) ^ 2 ≤ (3 / 2 - η / 2) ^ 2 := by nlinarith
  have h2 : (ρ.im - τ) ^ 2 ≤ η / 4 := by
    have hs := Real.sq_sqrt hη.le
    have := sq_abs (ρ.im - τ)
    have h0 : 0 ≤ |ρ.im - τ| := abs_nonneg _
    nlinarith
  have hle : ‖ρ - lhCentre η τ‖ ^ 2 ≤ (3 / 2 - η / 8) ^ 2 := by rw [hsq]; nlinarith
  nlinarith [norm_nonneg (ρ - lhCentre η τ)]

theorem re_pos_ne_one_of_mem_lhBall {η τ : ℝ} (hη : 0 < η) (hτ : 3 ≤ |τ|) {ρ : ℂ}
    (hρ : ρ ∈ closedBall (lhCentre η τ) |3 / 2|) : 0 < ρ.re ∧ ρ ≠ 1 ∧ 1 / 2 + η / 2 ≤ ρ.re ∧
      |τ| - 3 / 2 ≤ |ρ.im| ∧ |ρ.im| ≤ |τ| + 2 := by
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num)] at hρ
  obtain ⟨hr, hi⟩ := re_im_sub_lhCentre η τ ρ
  have hre := Complex.abs_re_le_norm (ρ - lhCentre η τ)
  have him := Complex.abs_im_le_norm (ρ - lhCentre η τ)
  rw [hr] at hre
  rw [hi] at him
  have hre' := abs_le.mp (hre.trans hρ)
  have him' := him.trans hρ
  have hlow : |τ| - 3 / 2 ≤ |ρ.im| := by
    have := abs_sub_abs_le_abs_sub τ ρ.im
    rw [abs_sub_comm] at this
    linarith
  have hup : |ρ.im| ≤ |τ| + 2 := by
    have := abs_sub_abs_le_abs_sub ρ.im τ
    linarith
  refine ⟨by linarith, fun h => ?_, by linarith, hlow, hup⟩
  rw [h] at hlow
  simp at hlow
  linarith

theorem log_ratio_ge {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    η / 12 ≤ Real.log ((3 / 2) / (3 / 2 - η / 8)) := by
  have hpos : 0 < 3 / 2 - η / 8 := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (3 / 2 - η / 8) / (3 / 2) by positivity)
  have e : Real.log ((3 / 2) / (3 / 2 - η / 8)) = -Real.log ((3 / 2 - η / 8) / (3 / 2)) := by
    rw [← Real.log_inv, inv_div]
  rw [e]
  have : (3 / 2 - η / 8) / (3 / 2) - 1 = -(η / 12) := by field_simp; ring
  linarith

/-- **One disc.** Under `‖ζ(s)‖ ≤ C|Im s|^ε` on `Re s ≥ ½ + η/2`, `|Im s| ≥ T`, and for
`|τ| ≥ max 3 (T + 3/2)`, at most `(12/η)(log 3C + ε log(|τ| + 2))` copies have `Re ρ ≥ ½ + η` and
`|Im ρ − τ| ≤ √η/2`. -/
theorem card_le_disc_of_bound {C ε η τ T : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) (hη : 0 < η)
    (hη2 : η < 1 / 2) (hτ : 3 ≤ |τ|) (hτT : T + 3 / 2 ≤ |τ|)
    (hLH : ∀ s : ℂ, 1 / 2 + η / 2 ≤ s.re → T ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| ^ ε)
    (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, 1 / 2 + η ≤ (q.1 : ℂ).re ∧ |(q.1 : ℂ).im - τ| ≤ Real.sqrt η / 2) :
    (F.card : ℝ) ≤ 12 / η * (Real.log (3 * C) + ε * Real.log (|τ| + 2)) := by
  set c := lhCentre η τ with hc
  set r := 3 / 2 - η / 8 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hrR : r < 3 / 2 := by rw [hr]; linarith
  have hball : ∀ ρ ∈ closedBall c |r|, 0 < ρ.re ∧ ρ ≠ 1 := by
    intro ρ hρ
    have hρ' : ρ ∈ closedBall c |3 / 2| := by
      refine closedBall_subset_closedBall ?_ hρ
      rw [abs_of_pos hr0, abs_of_pos (by norm_num)]; exact hrR.le
    obtain ⟨h1, h2, -⟩ := re_pos_ne_one_of_mem_lhBall hη hτ hρ'
    exact ⟨h1, h2⟩
  have hcard := card_le_divisor_sum_of_ball hball F fun q hq =>
    mem_closedBall_lhCentre hη hη2 (hF q hq).1 (xiZeroCopy_re_lt_one q) (hF q hq).2
  set M := C * (|τ| + 2) ^ ε with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    have : 1 ≤ (|τ| + 2) ^ ε := Real.one_le_rpow (by linarith [abs_nonneg τ]) hε.le
    nlinarith
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall c |3 / 2|) :=
    analyticOnNhd_riemannZeta_of_ne_one fun ρ hρ => (re_pos_ne_one_of_mem_lhBall hη hτ hρ).2.1
  have hcentre : 1 / 3 ≤ ‖riemannZeta c‖ := norm_riemannZeta_ge_third (by
    rw [hc, lhCentre]; simp; linarith)
  have hsphere : ∀ z ∈ sphere c |3 / 2|, ‖riemannZeta z‖ ≤ M := by
    intro z hz
    obtain ⟨-, -, hre, hlow, hup⟩ := re_pos_ne_one_of_mem_lhBall hη hτ (sphere_subset_closedBall hz)
    refine (hLH z hre (by linarith)).trans ?_
    rw [hM]
    gcongr
  have hJ := sum_divisor_le_of_bounds (c := c) (r := r) (R := 3 / 2) (M := M) (m := 1 / 3)
    (f := riemannZeta) (by rw [abs_of_pos hr0]; exact hr0)
    (by rw [abs_of_pos hr0, abs_of_pos (by norm_num)]; exact hrR) hM1 (by norm_num) hana hcentre
    hsphere
  have hlogM : Real.log (M / (1 / 3)) = Real.log (3 * C) + ε * Real.log (|τ| + 2) := by
    rw [hM, show C * (|τ| + 2) ^ ε / (1 / 3) = (3 * C) * (|τ| + 2) ^ ε by ring,
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by linarith [abs_nonneg τ])]
  have hnum : 0 ≤ Real.log (3 * C) + ε * Real.log (|τ| + 2) := by
    have : 0 ≤ Real.log (3 * C) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (|τ| + 2) := Real.log_nonneg (by linarith [abs_nonneg τ])
    positivity
  have hlr := log_ratio_ge hη hη2
  calc (F.card : ℝ)
      ≤ ((∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c |r|)) u : ℤ) : ℝ) := hcard
    _ ≤ Real.log (M / (1 / 3)) / Real.log ((3 / 2) / r) := by exact_mod_cast hJ
    _ = (Real.log (3 * C) + ε * Real.log (|τ| + 2)) / Real.log ((3 / 2) / r) := by rw [hlogM]
    _ ≤ (Real.log (3 * C) + ε * Real.log (|τ| + 2)) / (η / 12) :=
        div_le_div_of_nonneg_left hnum (by positivity) hlr
    _ = 12 / η * (Real.log (3 * C) + ε * Real.log (|τ| + 2)) := by field_simp

/-! ## Windows -/

/-- **One window.** Under `‖ζ(s)‖ ≤ C|Im s|^ε` on `Re s ≥ ½ + η/2`, `|Im s| ≥ T`, at most
`(⌊2L/w⌋ + 1)(12/η)(log 3C + ε log(|t| + L + 2))` copies have `Re ρ ≥ ½ + η` and ordinate within
`L` of `t`, where `w = √η/2` and `|t| ≥ L + max 3 (T + 3/2)`. -/
theorem card_le_window_of_bound {C ε η L t T : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) (hη : 0 < η)
    (hη2 : η < 1 / 2) (hL : 0 < L) (ht : L + 3 ≤ |t|) (htT : L + T + 3 / 2 ≤ |t|)
    (hLH : ∀ s : ℂ, 1 / 2 + η / 2 ≤ s.re → T ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| ^ ε)
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, 1 / 2 + η ≤ (q.1 : ℂ).re ∧ |(q.1 : ℂ).im - t| ≤ L) :
    (F.card : ℝ) ≤ (⌊2 * L / (Real.sqrt η / 2)⌋₊ + 1 : ℕ) *
      (12 / η * (Real.log (3 * C) + ε * Real.log (|t| + L + 2))) := by
  classical
  set w := Real.sqrt η / 2 with hw
  have hw0 : 0 < w := by rw [hw]; have := Real.sqrt_pos.mpr hη; linarith
  set K := ⌊2 * L / w⌋₊ with hK
  set k : XiZeroCopy → ℕ := fun q => ⌊((q.1 : ℂ).im - (t - L)) / w⌋₊ with hk
  have hmaps : ∀ q ∈ F, k q ∈ Finset.range (K + 1) := by
    intro q hq
    rw [Finset.mem_range, Nat.lt_succ_iff, hk, hK]
    apply Nat.floor_mono
    have := abs_le.mp (hF q hq).2
    exact div_le_div_of_nonneg_right (by linarith) hw0.le
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hB : 0 ≤ 12 / η * (Real.log (3 * C) + ε * Real.log (|t| + L + 2)) := by
    have : 0 ≤ Real.log (3 * C) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (|t| + L + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    positivity
  calc ∑ j ∈ Finset.range (K + 1), ((F.filter fun q => k q = j).card : ℝ)
      ≤ ∑ _j ∈ Finset.range (K + 1),
          12 / η * (Real.log (3 * C) + ε * Real.log (|t| + L + 2)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        set τ := t - L + j * w with hτ
        have hjK : (j : ℝ) ≤ K := by
          have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj); exact_mod_cast this
        have hKle : (K : ℝ) * w ≤ 2 * L := by
          have := Nat.floor_le (show 0 ≤ 2 * L / w by positivity)
          rw [← hK] at this
          calc (K : ℝ) * w ≤ 2 * L / w * w := mul_le_mul_of_nonneg_right this hw0.le
            _ = 2 * L := by field_simp
        have hτt : |τ - t| ≤ L := by
          rw [abs_le]
          have : 0 ≤ (j : ℝ) * w := by positivity
          have : (j : ℝ) * w ≤ K * w := mul_le_mul_of_nonneg_right hjK hw0.le
          constructor <;> linarith
        have hτ3 : 3 ≤ |τ| := by
          have := abs_sub_abs_le_abs_sub t τ
          rw [abs_sub_comm] at hτt
          linarith
        have hτT : T + 3 / 2 ≤ |τ| := by
          have := abs_sub_abs_le_abs_sub t τ
          rw [abs_sub_comm] at hτt
          linarith
        have hdisc := card_le_disc_of_bound hC hε hη hη2 hτ3 hτT hLH (F.filter fun q => k q = j)
          (by
            intro q hq
            obtain ⟨hqF, hqj⟩ := Finset.mem_filter.mp hq
            refine ⟨(hF q hqF).1, ?_⟩
            have hx0 : 0 ≤ ((q.1 : ℂ).im - (t - L)) / w := by
              have := abs_le.mp (hF q hqF).2
              exact div_nonneg (by linarith) hw0.le
            have h1 := Nat.floor_le hx0
            have h2 := Nat.lt_floor_add_one (((q.1 : ℂ).im - (t - L)) / w)
            rw [show ⌊((q.1 : ℂ).im - (t - L)) / w⌋₊ = j from hqj] at h1 h2
            rw [le_div_iff₀ hw0] at h1
            rw [div_lt_iff₀ hw0] at h2
            rw [abs_le]
            constructor <;> nlinarith)
        refine hdisc.trans ?_
        have hτle : |τ| ≤ |t| + L := by
          have := abs_sub_abs_le_abs_sub τ t
          linarith
        have hlog : Real.log (|τ| + 2) ≤ Real.log (|t| + L + 2) :=
          Real.log_le_log (by positivity) (by linarith)
        have h1 : ε * Real.log (|τ| + 2) ≤ ε * Real.log (|t| + L + 2) :=
          mul_le_mul_of_nonneg_left hlog hε.le
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (K + 1 : ℝ) * (12 / η * (Real.log (3 * C) + ε * Real.log (|t| + L + 2))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-! ## Backlund's direction -/

/-- **Subpolynomial growth to the right of every line `Re s = ½ + η/2` makes off-line zeros
sparse** (Backlund). The bound may hold only above a height `T` depending on `η` and `ε`. -/
theorem offLineSparse_of_eventual_bound
    (hb : ∀ η ε : ℝ, 0 < η → 0 < ε → ∃ C T : ℝ, 1 ≤ C ∧
      ∀ s : ℂ, 1 / 2 + η / 2 ≤ s.re → T ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| ^ ε) :
    OffLineSparse := by
  classical
  intro η L c hη hL hc
  set η' := min η (1 / 4) with hη'
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  have hη'2 : η' < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hη'η : η' ≤ η := min_le_left _ _
  set K := ⌊2 * L / (Real.sqrt η' / 2)⌋₊ with hK
  set ε := c * η' / (96 * (K + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨C, T, hC, hbound⟩ := hb η' ε hη'0 hε0
  set A := 48 * (K + 1) * Real.log (3 * C) / (c * η') with hA
  refine ⟨max (max (L + 3) (L + T + 3 / 2)) (Real.exp A), fun t ht G hG => ?_⟩
  have htL : L + 3 ≤ t := le_trans (le_max_left _ _) (le_of_max_le_left ht)
  have htT : L + T + 3 / 2 ≤ t := le_trans (le_max_right _ _) (le_of_max_le_left ht)
  have htA : Real.exp A ≤ t := le_of_max_le_right ht
  have ht0 : 0 < t := by linarith
  have habs : |t| = t := abs_of_pos ht0
  -- split into the two sides of the line
  set Gp := G.filter fun q => (xiSpectralPoint q).im < 0 with hGp
  set Gm := G.filter fun q => ¬ (xiSpectralPoint q).im < 0 with hGm
  have hsplit : (G.card : ℝ) = Gp.card + Gm.card := by
    have := Finset.card_filter_add_card_filter_not (s := G) (fun q => (xiSpectralPoint q).im < 0)
    rw [← this]; push_cast; ring
  set B := 12 / η' * (Real.log (3 * C) + ε * Real.log (t + L + 2)) with hBdef
  have hp : (Gp.card : ℝ) ≤ (K + 1 : ℕ) * B := by
    have := card_le_window_of_bound hC hε0 hη'0 hη'2 hL (by rw [habs]; exact htL)
      (by rw [habs]; exact htT) hbound Gp
      (by
        intro q hq
        obtain ⟨hqG, hneg⟩ := Finset.mem_filter.mp hq
        obtain ⟨h1, h2⟩ := hG q hqG
        rw [abs_of_neg hneg, spectral_im_eq] at h2
        rw [spectral_re_eq] at h1
        exact ⟨by linarith, h1⟩)
    rwa [habs] at this
  have hm : (Gm.card : ℝ) ≤ (K + 1 : ℕ) * B := by
    have hinj := xiZeroCopyReflectEquiv.injective
    have := card_le_window_of_bound (t := -t) hC hε0 hη'0 hη'2 hL (by rw [abs_neg, habs]; exact htL)
      (by rw [abs_neg, habs]; exact htT) hbound (Gm.image xiZeroCopyReflectEquiv)
      (by
        intro q' hq'
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
        obtain ⟨hqG, hnn⟩ := Finset.mem_filter.mp hq
        obtain ⟨h1, h2⟩ := hG q hqG
        rw [not_lt] at hnn
        rw [abs_of_nonneg hnn, spectral_im_eq] at h2
        rw [spectral_re_eq] at h1
        rw [xiZeroCopy_reflect_val]
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
        refine ⟨by linarith, ?_⟩
        rw [show -(q.1 : ℂ).im - -t = -((q.1 : ℂ).im - t) by ring, abs_neg]
        exact h1)
    rwa [Finset.card_image_of_injective _ hinj, abs_neg, habs] at this
  -- the bound
  have hlog2 : Real.log (t + L + 2) ≤ 2 * Real.log t := by
    have e : 2 * Real.log t = Real.log (t ^ 2) := by rw [Real.log_pow]; push_cast; ring
    rw [e]
    have : t * (L + 3) ≤ t * t := mul_le_mul_of_nonneg_left htL ht0.le
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hlogA : A ≤ Real.log t := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) htA
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hcalc : 2 * ((K + 1 : ℕ) * B) ≤ c * Real.log t := by
    push_cast
    rw [hBdef]
    have hlog3 : 0 ≤ Real.log (3 * C) := Real.log_nonneg (by linarith)
    have e1 : 2 * ((K + 1 : ℝ) * (12 / η' * (Real.log (3 * C) + ε * Real.log (t + L + 2)))) =
        c / 2 * A + (c * Real.log (t + L + 2)) / 4 := by
      rw [hA, hε]; field_simp; ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hlogA (by positivity : (0 : ℝ) ≤ c / 2)
    have := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ c / 4)
    nlinarith
  rw [hsplit]
  linarith

/-- **The Lindelöf hypothesis makes off-line zeros sparse** (Backlund). -/
theorem offLineSparse_of_lindelof (hLH : LindelofHalfPlane) : OffLineSparse :=
  offLineSparse_of_eventual_bound fun η ε hη hε => by
    obtain ⟨C, hC, hbound⟩ := hLH ε hε
    exact ⟨C, 1, hC, fun s hs h1 => hbound s (by linarith) h1⟩

/-- **Under the Lindelöf hypothesis a real-rooted cosine level is an eventual strip.** If LH holds
and `cos(hD)Ξ = (ξ(s+h) + ξ(s−h))/2` has only real zeros, then for every `ε > 0` all zeros of large
height satisfy `Im ζ ≤ h + ε`, i.e. `β ≥ ½ − h − ε`. -/
theorem eventually_strip_of_lindelof_of_cosShiftXi_real (hLH : LindelofHalfPlane) {h : ℝ}
    (hh : 0 < h) (hreal : ∀ z, cosShiftXi h z = 0 → z.im = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ q : XiZeroCopy, T ≤ (xiSpectralPoint q).re → (xiSpectralPoint q).im ≤ h + ε :=
  eventually_im_le_of_cosShiftXi_real_of_sparse (offLineSparse_of_lindelof hLH) hh hreal hε

end

end RHTower.LindelofSparse
