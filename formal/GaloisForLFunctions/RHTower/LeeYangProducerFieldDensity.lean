import GaloisForLFunctions.RHTower.LeeYangFieldDensityBudget
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer
import GaloisForLFunctions.RHTower.LeeYangPrimeStabilityNoGo
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass

/-!
# Field density of Lee–Yang producers

Let `L_a` be Lee–Yang data, affine and present in every field, and suppose the normalized
restrictions `κ_a f_a` converge locally uniformly to an entire function `g` that has no zero on the
circle `|z − T/2| = T/2 + η`. Then eventually
`Σ_j (⌈λ_j T/2π⌉ − 1) ≤ N_g`, the number of zeros of `g` in that disc
(`eventually_sum_ceil_sub_one_le_zeroSumBall`), and hence
`Σ_j max(λ_j − 2π/T, 0) ≤ (2π/T) N_g` (`eventually_sum_max_sub_le_zeroSumBall`).

For `g = E·Ξ` with `E` zero-free and `0 < η ≤ 1`, the disc sees only `ξ`-zeros with ordinate in
`(0, T + η]` (`zeroSumBall_le_xiZeroCount`), so eventually
`Σ_j max(λ_j − 2π/T, 0) ≤ (2π/T) N_Ξ(T + η)` (`eventually_fieldDensity_le_xiZeroCount`).
With `N_Ξ(T) = (T/2π)(log(T/2π) − 1) + O(log T)` this bounds the field density of every Lee–Yang
producer of `Ξ` by the `Γ(s/2)` density: eventually
`Σ_j max(λ_j − 2π/T, 0) ≤ log(T/2π) − 1 + C/√T` with an absolute `C`
(`exists_eventually_fieldDensity_le_gammaDensity`, via `exists_abs_xiZeroCount_sub_smooth_le_sqrt`).

**Proof.** All zeros of a Lee–Yang restriction are real, so the zeros in `(0, T]` lie in the disc,
and the field-density budget (`LeeYangDatum.sum_ceil_sub_one_le_zeroCount`) bounds the disc count
from below. Hurwitz (`eventually_zeroSumBall_eq_of_tendstoLocallyUniformly`) transfers the disc
count to the limit.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.LeeYangCount

noncomputable section

theorem zeroSumBall_const_mul {f : ℂ → ℂ} {κ : ℂ} (hκ : κ ≠ 0) (c : ℂ) (t : ℝ) :
    zeroSumBall (fun z => κ * f z) c t = zeroSumBall f c t := by
  unfold zeroSumBall
  congr 1
  have h : (fun ζ => logDeriv (fun z => κ * f z) ζ) = fun ζ => logDeriv f ζ :=
    funext fun ζ => logDeriv_const_mul ζ κ hκ
  simp only [h]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Budget in a disc.** If the restriction has no zero on the circle `|z − T/2| = T/2 + η`, the
field-density budget bounds the zero count of the disc. -/
theorem sum_ceil_sub_one_le_zeroSumBall (L : LeeYangDatum ι) (hdeg : ∀ j, L.P.degreeOf j = 1)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), L.restr z ≠ 0) :
    ∑ j, (((⌈L.freq j * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤
      (zeroSumBall L.restr ((T : ℂ) / 2) (T / 2 + η)).re := by
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall (U := Set.univ)
    (R := T / 2 + η + 1) (by positivity) (by linarith) isOpen_univ (subset_univ _)
    L.differentiable_restr.differentiableOn hsph
  have hsub : L.zeroSet T ⊆ Z := by
    intro w hw
    rw [L.mem_zeroSet] at hw
    obtain ⟨him, ⟨hre0, hreT⟩, hz⟩ := hw
    apply (hZzero w _).mp hz
    rw [mem_ball, Complex.dist_eq]
    have hw' : w - (T : ℂ) / 2 = ((w.re - T / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hw', Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hcount := L.sum_ceil_sub_one_le_zeroCount hdeg hT
  refine hcount.trans ?_
  rw [hsum, Complex.re_sum]
  simp only [Complex.natCast_re]
  unfold LeeYangDatum.zeroCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

/-- A locally uniform limit with no zero on a circle keeps every approximant zero-free there. -/
theorem eventually_ne_zero_on_sphere {α : Type*} {p : Filter α} {F : α → ℂ → ℂ} {g : ℂ → ℂ}
    (hg : Continuous g) (hconv : TendstoLocallyUniformly F g p) {c : ℂ} {r : ℝ}
    (hsph : ∀ z ∈ sphere c r, g z ≠ 0) : ∀ᶠ a in p, ∀ z ∈ sphere c r, F a z ≠ 0 := by
  have hK : IsCompact (sphere c r) := isCompact_sphere c r
  rcases (sphere c r).eq_empty_or_nonempty with he | hne
  · exact Eventually.of_forall fun a z hz => by rw [he] at hz; exact absurd hz (Set.notMem_empty z)
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne (continuous_norm.comp hg).continuousOn
  have hm : 0 < ‖g z₀‖ := norm_pos_iff.mpr (hsph z₀ hz₀)
  have hunif : TendstoUniformlyOn F g p (sphere c r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      hconv.tendstoLocallyUniformlyOn
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif) _ hm] with a ha z hz hzero
  have h1 := ha z hz
  rw [dist_eq_norm, hzero, sub_zero] at h1
  have h2 : ‖g z₀‖ ≤ ‖g z‖ := hmin hz
  linarith

/-- **Producer budget.** If normalized Lee–Yang restrictions converge locally uniformly to `g`
with no zero on the circle `|z − T/2| = T/2 + η`, then eventually
`Σ_j (⌈λ_j T/2π⌉ − 1)` is at most the number of zeros of `g` in the disc. -/
theorem eventually_sum_ceil_sub_one_le_zeroSumBall {α : Type*} {p : Filter α}
    {κι : α → Type*} [∀ a, Fintype (κι a)] [∀ a, DecidableEq (κι a)]
    (L : ∀ a, LeeYangDatum (κι a)) (hdeg : ∀ a j, (L a).P.degreeOf j = 1)
    (κ : α → ℂ) (hκ : ∀ a, κ a ≠ 0) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hconv : TendstoLocallyUniformly (fun a z => κ a * (L a).restr z) g p)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), g z ≠ 0) :
    ∀ᶠ a in p, ∑ j, (((⌈(L a).freq j * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤
      (zeroSumBall g ((T : ℂ) / 2) (T / 2 + η)).re := by
  have hdiff : ∀ a, Differentiable ℂ (fun z => κ a * (L a).restr z) := fun a =>
    (L a).differentiable_restr.const_mul (κ a)
  have hH := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hdiff hg hconv
    (c := (T : ℂ) / 2) (r := T / 2 + η) (R := T / 2 + η + 1) (by positivity) (by linarith) hsph
  have hS := eventually_ne_zero_on_sphere hg.continuous hconv hsph
  filter_upwards [hH, hS] with a ha hs
  have hsph' : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), (L a).restr z ≠ 0 := fun z hz h =>
    hs z hz (by simp [h])
  have hb := sum_ceil_sub_one_le_zeroSumBall (L a) (hdeg a) hT hη hsph'
  rw [← zeroSumBall_const_mul (hκ a), ha] at hb
  exact hb

theorem max_sub_le_mul_ceil_sub_one {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) :
    max (lam - 2 * Real.pi / T) 0 ≤
      2 * Real.pi / T * ((((⌈lam * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hx : 0 < lam * T / (2 * Real.pi) := by positivity
  have hceil : (1 : ℝ) ≤ (⌈lam * T / (2 * Real.pi)⌉ : ℤ) := by
    have : (1 : ℤ) ≤ ⌈lam * T / (2 * Real.pi)⌉ := Int.one_le_ceil_iff.mpr hx
    exact_mod_cast this
  have hle := Int.le_ceil (lam * T / (2 * Real.pi))
  apply max_le
  · have h : lam - 2 * Real.pi / T = 2 * Real.pi / T * (lam * T / (2 * Real.pi) - 1) := by
      field_simp
    rw [h]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · exact mul_nonneg (by positivity) (by linarith)

/-- **Field density of producers.** Under the hypotheses of
`eventually_sum_ceil_sub_one_le_zeroSumBall`, eventually
`Σ_j max(λ_j − 2π/T, 0) ≤ (2π/T)·N_g`. -/
theorem eventually_sum_max_sub_le_zeroSumBall {α : Type*} {p : Filter α}
    {κι : α → Type*} [∀ a, Fintype (κι a)] [∀ a, DecidableEq (κι a)]
    (L : ∀ a, LeeYangDatum (κι a)) (hdeg : ∀ a j, (L a).P.degreeOf j = 1)
    (κ : α → ℂ) (hκ : ∀ a, κ a ≠ 0) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hconv : TendstoLocallyUniformly (fun a z => κ a * (L a).restr z) g p)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), g z ≠ 0) :
    ∀ᶠ a in p, ∑ j, max ((L a).freq j - 2 * Real.pi / T) 0 ≤
      2 * Real.pi / T * (zeroSumBall g ((T : ℂ) / 2) (T / 2 + η)).re := by
  filter_upwards [eventually_sum_ceil_sub_one_le_zeroSumBall L hdeg κ hκ hg hconv hT hη hsph]
    with a ha
  calc ∑ j, max ((L a).freq j - 2 * Real.pi / T) 0
      ≤ ∑ j, 2 * Real.pi / T * ((((⌈(L a).freq j * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)) :=
        Finset.sum_le_sum fun j _ => max_sub_le_mul_ceil_sub_one ((L a).freq_pos j) hT
    _ = 2 * Real.pi / T * ∑ j, ((((⌈(L a).freq j * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)

/-! ## Producers of `Ξ` -/

/-- **The `Ξ` disc count.** The disc `|z − T/2| < T/2 + η` (`0 < η ≤ 1`) contains only spectral
points of `ξ`-zeros with ordinate in `(0, T + η]`. -/
theorem zeroSumBall_le_xiZeroCount {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), E z * XiC z ≠ 0) :
    (zeroSumBall (fun z => E z * XiC z) ((T : ℂ) / 2) (T / 2 + η)).re ≤
      (xiZeroCount (T + η) : ℝ) := by
  classical
  set F : ℂ → ℂ := fun z => E z * XiC z with hFdef
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hFd : Differentiable ℂ F := hE.mul hXiCd
  obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall (U := Set.univ)
    (R := T / 2 + η + 1) (by positivity) (by linarith) isOpen_univ (subset_univ _)
    hFd.differentiableOn hsph
  have hzm : ∀ z, zeroMult F z = (analyticOrderAt XiC z).toNat := by
    intro z
    have hmul : analyticOrderAt F z = analyticOrderAt E z + analyticOrderAt XiC z :=
      analyticOrderAt_mul (hE.analyticAt z) (hXiCd.analyticAt z)
    have h0 : analyticOrderAt E z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (hEne z))
    rw [zeroMult, hmul, h0, zero_add]
  set g : XiDivisorSupport → ℂ := fun ρ => ((ρ : ℂ) - 1 / 2) * (-I) with hg
  set S := xiSupportsPos (T + η)
  have hsub : Z ⊆ S.image g := by
    intro z hz
    have hball := hZball z hz
    have hFz : F z = 0 := (hZzero z hball).mpr hz
    have hXi : XiC z = 0 := by
      rcases mul_eq_zero.mp hFz with h | h
      · exact absurd h (hEne z)
      · exact h
    set ρ : ℂ := 1 / 2 + z * I with hρ
    have hxi : xi ρ = 0 := hXi
    have hmem : ρ ∈ (MeromorphicOn.divisor xi Set.univ).support :=
      Function.mem_support.mpr (xi_divisor_pos_of_eq_zero hxi).ne'
    have hρim : ρ.im = z.re := by simp [hρ]
    have hdist : ‖z - (T : ℂ) / 2‖ < T / 2 + η := by
      rw [mem_ball, Complex.dist_eq] at hball; exact hball
    have hre : |z.re - T / 2| < T / 2 + η := by
      have h1 : |(z - (T : ℂ) / 2).re| ≤ ‖z - (T : ℂ) / 2‖ := Complex.abs_re_le_norm _
      have h2 : (z - (T : ℂ) / 2).re = z.re - T / 2 := by simp
      rw [h2] at h1
      linarith
    rw [abs_lt] at hre
    have hpos : 0 < ρ.im := by
      by_contra hle
      push Not at hle
      apply xi_ne_zero_of_abs_im_le_one (ρ := ρ) _ hxi
      rw [abs_le]; constructor <;> linarith
    refine Finset.mem_image.mpr ⟨⟨ρ, hmem⟩, ?_, ?_⟩
    · rw [mem_xiSupportsPos]
      refine ⟨?_, hpos⟩
      rw [abs_of_pos hpos, hρim]; linarith
    · simp only [hg, hρ]
      have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, I_mul_I]; ring
      calc (1 / 2 + z * I - 1 / 2) * -I = z * (I * -I) := by ring
        _ = z := by rw [hI, mul_one]
  have hinj : Set.InjOn g ↑S := by
    intro a _ b _ hab
    apply Subtype.ext
    have := congrArg (fun w => w * I + 1 / 2) hab
    simp only [hg] at this
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [mul_assoc, hI, mul_one, mul_assoc, hI, mul_one] at this
    linear_combination this
  have hcount : (xiZeroCount (T + η) : ℝ) = ∑ z ∈ S.image g, (zeroMult F z : ℝ) := by
    rw [xiZeroCount_eq_pos_sum (by linarith), Finset.sum_image hinj]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hzm, hg, analyticOrderAt_XiC_centeredCoordinate,
      xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  rw [hcount, hsum, Complex.re_sum]
  simp only [Complex.natCast_re]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _

/-- **Γ-criticality of Lee–Yang producers of `Ξ`.** If normalized Lee–Yang restrictions, affine and
present in every field, converge locally uniformly to `E·Ξ` with `E` entire and zero-free, then for
every `T > 0` and `0 < η ≤ 1` with no zero of `Ξ` on the circle `|z − T/2| = T/2 + η`, eventually
`Σ_j max(λ_j − 2π/T, 0) ≤ (2π/T)·N_Ξ(T + η)`. -/
theorem eventually_fieldDensity_le_xiZeroCount {α : Type*} {p : Filter α}
    {κι : α → Type*} [∀ a, Fintype (κι a)] [∀ a, DecidableEq (κι a)]
    (L : ∀ a, LeeYangDatum (κι a)) (hdeg : ∀ a j, (L a).P.degreeOf j = 1)
    (κ : α → ℂ) (hκ : ∀ a, κ a ≠ 0) {E : ℂ → ℂ} (hE : Differentiable ℂ E) (hEne : ∀ z, E z ≠ 0)
    (hconv : TendstoLocallyUniformly (fun a z => κ a * (L a).restr z) (fun z => E z * XiC z) p)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), E z * XiC z ≠ 0) :
    ∀ᶠ a in p, ∑ j, max ((L a).freq j - 2 * Real.pi / T) 0 ≤
      2 * Real.pi / T * (xiZeroCount (T + η) : ℝ) := by
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  filter_upwards [eventually_sum_max_sub_le_zeroSumBall L hdeg κ hκ (hE.mul hXiCd) hconv hT hη hsph]
    with a ha
  exact ha.trans (mul_le_mul_of_nonneg_left
    (zeroSumBall_le_xiZeroCount hE hEne hT hη hη1 hsph) (by positivity))

/-- **The `Γ(s/2)` density.** `(2π/T) N_Ξ(T + η) ≤ log(T/2π) − 1 + C/√T` for `T ≥ 4`, `η ≤ 1`. -/
theorem exists_two_pi_div_mul_xiZeroCount_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ T η : ℝ, 4 ≤ T → 0 < η →
    η ≤ 1 → 2 * Real.pi / T * (xiZeroCount (T + η) : ℝ) ≤
      Real.log (T / (2 * Real.pi)) - 1 + C / Real.sqrt T := by
  obtain ⟨C₀, hC₀, hrvm⟩ := exists_abs_xiZeroCount_sub_smooth_le_sqrt
  refine ⟨4 + 2 * Real.pi + 4 * Real.pi * C₀, by positivity, fun T η hT hη hη1 => ?_⟩
  have hπ := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hsT : 2 ≤ Real.sqrt T := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  have hsTpos : 0 < Real.sqrt T := by linarith
  have hTsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have h1 := hrvm (T + η) (by linarith)
  have hcount : (xiZeroCount (T + η) : ℝ) ≤
      (T + η) / (2 * Real.pi) * Real.log ((T + η) / routeKRVMBase) + 7 / 8 +
        C₀ * Real.sqrt (T + η) := by
    have := (abs_le.mp h1).2
    unfold routeKSmoothRVMCount at this
    linarith
  -- the logarithm
  set L := Real.log (T / (2 * Real.pi)) - 1 with hL
  have hlogsplit : Real.log ((T + η) / routeKRVMBase) = L + Real.log (1 + η / T) := by
    rw [hL, routeKRVMBase, show (T + η) / (2 * Real.pi * Real.exp 1) =
      (T / (2 * Real.pi)) * (1 + η / T) / Real.exp 1 by field_simp,
      Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_mul (by positivity) (by positivity)]
    ring
  have hlog1 : Real.log (1 + η / T) ≤ η / T := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + η / T by positivity); linarith
  have hηT0' : 0 ≤ η / T := by positivity
  have hlog1' : 0 ≤ Real.log (1 + η / T) := Real.log_nonneg (by linarith)
  have hLabs : |L| ≤ 2 * Real.sqrt T + 2 := by
    have hlogT : Real.log (T / (2 * Real.pi)) ≤ 2 * Real.sqrt T := by
      have h2 : T / (2 * Real.pi) ≤ T := div_le_self hT0.le (by linarith [Real.pi_gt_three])
      have h3 : Real.log (T / (2 * Real.pi)) ≤ Real.log T := Real.log_le_log (by positivity) h2
      have h4 : Real.log T = 2 * Real.log (Real.sqrt T) := by
        conv_lhs => rw [← hTsq]
        rw [Real.log_mul hsTpos.ne' hsTpos.ne']; ring
      have h5 : Real.log (Real.sqrt T) ≤ Real.sqrt T - 1 := Real.log_le_sub_one_of_pos hsTpos
      linarith
    have hlogT' : -1 ≤ Real.log (T / (2 * Real.pi)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have he : Real.exp (-1) ≤ 1 / 2 := by
        have := Real.add_one_le_exp (1 : ℝ)
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
      have h8 : 1 / 2 ≤ T / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_four]
      linarith
    rw [abs_le]; constructor <;> linarith
  have hηT : η / T ≤ 1 / T := div_le_div_of_nonneg_right hη1 hT0.le
  have hinvT : 1 / T ≤ 1 / (2 * Real.sqrt T) := by
    rw [div_le_div_iff₀ hT0 (by positivity)]; nlinarith
  have hsq1 : Real.sqrt (T + η) ≤ 2 * Real.sqrt T := by
    rw [show 2 * Real.sqrt T = Real.sqrt (4 * T) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  calc 2 * Real.pi / T * (xiZeroCount (T + η) : ℝ)
      ≤ 2 * Real.pi / T * ((T + η) / (2 * Real.pi) * Real.log ((T + η) / routeKRVMBase) + 7 / 8 +
          C₀ * Real.sqrt (T + η)) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (1 + η / T) * (L + Real.log (1 + η / T)) + 2 * Real.pi / T * (7 / 8) +
          2 * Real.pi / T * (C₀ * Real.sqrt (T + η)) := by
        rw [hlogsplit]; field_simp
    _ ≤ L + (η / T) * |L| + 2 * (η / T) + 2 * Real.pi / T * (7 / 8) +
          2 * Real.pi / T * (C₀ * (2 * Real.sqrt T)) := by
        have hηT0 : 0 ≤ η / T := by positivity
        have hηT1 : η / T ≤ 1 := by
          rw [div_le_one hT0]; linarith
        have e1 : (1 + η / T) * (L + Real.log (1 + η / T)) ≤ L + (η / T) * |L| + 2 * (η / T) := by
          have := le_abs_self L
          nlinarith [mul_le_mul_of_nonneg_left (le_abs_self L) hηT0]
        have e2 : 2 * Real.pi / T * (C₀ * Real.sqrt (T + η)) ≤
            2 * Real.pi / T * (C₀ * (2 * Real.sqrt T)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq1 hC₀) (by positivity)
        linarith
    _ ≤ L + (4 + 2 * Real.pi + 4 * Real.pi * C₀) / Real.sqrt T := by
        have hT2 : 2 / T ≤ 1 / Real.sqrt T := by
          rw [div_le_div_iff₀ hT0 hsTpos]; nlinarith
        have hA : (η / T) * |L| ≤ 3 / Real.sqrt T := by
          have h1 : (η / T) * |L| ≤ (1 / T) * (2 * Real.sqrt T + 2) :=
            mul_le_mul hηT hLabs (abs_nonneg _) (by positivity)
          have h2 : (1 / T) * (2 * Real.sqrt T + 2) = 2 / Real.sqrt T + 2 / T := by
            field_simp; nlinarith [hTsq]
          have h3 : 2 / Real.sqrt T + 1 / Real.sqrt T = 3 / Real.sqrt T := by ring
          linarith
        have hB : 2 * (η / T) ≤ 1 / Real.sqrt T := by
          have : 2 * (η / T) ≤ 2 / T := by
            have := mul_le_mul_of_nonneg_left hηT (show (0 : ℝ) ≤ 2 by norm_num)
            rw [mul_one_div] at this; exact this
          linarith
        have hC : 2 * Real.pi / T * (7 / 8) ≤ 2 * Real.pi / Real.sqrt T := by
          have : 1 / T ≤ 1 / Real.sqrt T := by
            rw [div_le_div_iff₀ hT0 hsTpos]; nlinarith
          have e : 2 * Real.pi / T * (7 / 8) = 2 * Real.pi * (7 / 8) * (1 / T) := by ring
          have e' : 2 * Real.pi / Real.sqrt T = 2 * Real.pi * (1 / Real.sqrt T) := by ring
          rw [e, e']
          nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ 2 * Real.pi by positivity)]
        have hD : 2 * Real.pi / T * (C₀ * (2 * Real.sqrt T)) = 4 * Real.pi * C₀ / Real.sqrt T := by
          field_simp
          nlinarith [hTsq]
        have hsplit : (4 + 2 * Real.pi + 4 * Real.pi * C₀) / Real.sqrt T =
            4 / Real.sqrt T + 2 * Real.pi / Real.sqrt T + 4 * Real.pi * C₀ / Real.sqrt T := by ring
        rw [hsplit, hD]
        have h4 : 3 / Real.sqrt T + 1 / Real.sqrt T = 4 / Real.sqrt T := by ring
        linarith

/-- **Γ-criticality with the explicit main term.** There is an absolute `C` such that for every
family of normalized Lee–Yang restrictions converging locally uniformly to `E·Ξ` and every
admissible `T ≥ 4`, `0 < η ≤ 1`, eventually `Σ_j max(λ_j − 2π/T, 0) ≤ log(T/2π) − 1 + C/√T`. -/
theorem exists_eventually_fieldDensity_le_gammaDensity : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {α : Type*} {p : Filter α} {κι : α → Type*} [∀ a, Fintype (κι a)]
      [∀ a, DecidableEq (κι a)] (L : ∀ a, LeeYangDatum (κι a)),
      (∀ a j, (L a).P.degreeOf j = 1) → ∀ (κ : α → ℂ), (∀ a, κ a ≠ 0) →
      ∀ {E : ℂ → ℂ}, Differentiable ℂ E → (∀ z, E z ≠ 0) →
      TendstoLocallyUniformly (fun a z => κ a * (L a).restr z) (fun z => E z * XiC z) p →
      ∀ {T η : ℝ}, 4 ≤ T → 0 < η → η ≤ 1 →
      (∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), E z * XiC z ≠ 0) →
      ∀ᶠ a in p, ∑ j, max ((L a).freq j - 2 * Real.pi / T) 0 ≤
        Real.log (T / (2 * Real.pi)) - 1 + C / Real.sqrt T := by
  obtain ⟨C, hC, hbound⟩ := exists_two_pi_div_mul_xiZeroCount_le
  refine ⟨C, hC, fun L hdeg κ hκ E hE hEne hconv T η hT hη hη1 hsph => ?_⟩
  filter_upwards [eventually_fieldDensity_le_xiZeroCount L hdeg κ hκ hE hEne hconv
    (by linarith : (0 : ℝ) < T) hη hη1 hsph] with a ha
  exact ha.trans (hbound T η hT hη hη1)

end

end RHTower.LeeYangCount
