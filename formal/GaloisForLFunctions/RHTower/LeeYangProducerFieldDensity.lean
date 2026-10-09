import GaloisForLFunctions.RHTower.LeeYangFieldDensityBudget
import GaloisForLFunctions.HTGeometry.LocallyUniformZeroCountTransfer

/-!
# Field density of Lee–Yang producers

Let `L_a` be Lee–Yang data, affine and present in every field, and suppose the normalized
restrictions `κ_a f_a` converge locally uniformly to an entire function `g` that has no zero on the
circle `|z − T/2| = T/2 + η`. Then eventually
`Σ_j (⌈λ_j T/2π⌉ − 1) ≤ N_g`, the number of zeros of `g` in that disc
(`eventually_sum_ceil_sub_one_le_zeroSumBall`), and hence
`Σ_j max(λ_j − 2π/T, 0) ≤ (2π/T) N_g` (`eventually_sum_max_sub_le_zeroSumBall`).

For `g = E·Ξ` with `E` zero-free, `N_g` counts the zeros of `Ξ` with ordinate in `(−η, T + η)`.
With `N_Ξ(T) = (T/2π)(log(T/2π) − 1) + O(log T)` this bounds the field density of every Lee–Yang
producer of `Ξ` by the `Γ(s/2)` density: `Σ_{λ_j > 2π/T}(λ_j − 2π/T) ≤ log(T/2π) − 1 + o(1)`.

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

end

end RHTower.LeeYangCount
