import GaloisForLFunctions.RHTower.XiReciprocalSlicePositiveUnbounded
import GaloisForLFunctions.RHTower.SeparatedSimpleZeros
import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.HTGeometry.SeparatedPointsInverseSquarePacking
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Reciprocal slice positivity holds at a positive proportion of heights

**Theorem** (`exists_pos_density_xiReciprocalSlicePositive`).  There is `c > 0` such that for all
large `T`, the set of heights `t ∈ [T, 3T]` with `Ξ(t) ≠ 0` and with nonnegative Taylor
coefficients of `1/(Ξ(t+σ)Ξ(t−σ))` at `0` has Lebesgue measure at least `cT`.

Proof.  Fix `r = ½` and `L = log(T/2π)`.  By the separated-zero theorem
(`separated_simple_critical`), at least `N(T,2T)/8` zeros `ρ = ½ + iγ` with `T < γ ≤ 2T` are
simple, critical and have no other zero within `r/L`.  Call this set `G`.
* **Packing.**  The ordinates in `G` are `r/L`-separated, and every other zero is `r/L` away from
  each of them.  So for every zero copy `z`, `Σ_{γ ∈ G} 1/|z − γ|² ≤ A L²/r²`
  (`sum_inv_sq_le_of_separated`).
* Summing over the `O(T L)` copies with ordinate near `[T, 2T]`, and using the Lorentzian mass bound
  for the far copies, gives `Σ_{γ ∈ G} S(γ) = O(T L³)` with `S(γ) = Σ_{z ≠ γ} 1/|z − γ|²`.  So
  `S(γ) ≤ K L²` for at least half of `G`.
* **Dominance.**  For such `γ` and `0 < t − γ < c₀/L`, `(t − γ)² Σ_{z ≠ γ} 1/|z − t|² ≤ 1/20`.  The
  dominance law (`xiReciprocalSlicePositive_of_dominant_zero`) gives positivity at `t`.
* The intervals `(γ, γ + c₀/L)` are disjoint and have total length `≥ |G| c₀/(2L) ≫ T`.

No pair correlation is used: the separation of `G` alone controls the double sum.
-/

open Complex Filter Topology Metric MeasureTheory
open scoped ComplexOrder Nat
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- `HD(1) > 1/2`, from `tan x > x` at `x = 1/√2`. -/
theorem half_lt_HD_one : (1 / 2 : ℝ) < Zeta23.ThmD.HD 1 := by
  rw [Zeta23.ThmD.HD_one]
  set x : ℝ := (Real.sqrt 2)⁻¹ with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < Real.pi / 2 := by
    have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    have : x ≤ 1 := by rw [hx]; exact inv_le_one_of_one_le₀ h2
    linarith [Real.pi_gt_three]
  have htan := Real.lt_tan hx0 hx1
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
  have : x * (Real.cos x / Real.sin x) < 1 := by
    rw [mul_div_assoc', div_lt_one hsin]
    linarith
  linarith

/-- A zero copy is a nontrivial zero of `ζ`. -/
theorem isNontrivialZero_xiZeroCopy (q : XiZeroCopy) : Zeta23.IsNontrivialZero (q.1 : ℂ) := by
  have hre0 := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  refine ⟨(xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).1
    (xi_eq_zero_of_mem_divisor_support q.1), hre0, hre1⟩

/-- The distance from a zero copy to a critical point `½ + iγ` in spectral coordinates. -/
theorem norm_xiSpectralPoint_sub_im {q : XiZeroCopy} {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖xiSpectralPoint q - (ρ.im : ℂ)‖ = ‖(q.1 : ℂ) - ρ‖ := by
  have hρ : (ρ.im : ℂ) = (ρ - 1 / 2) * (-I) := by
    apply Complex.ext <;> simp [hre]
  rw [xiSpectralPoint, hρ, ← sub_mul, norm_mul, norm_neg, Complex.norm_I, mul_one]
  congr 1
  ring

/-- The separated simple critical zeros in `(T, 2T]` at radius `r` and scale `L`. -/
def sepZeroSet (r L T : ℝ) : Set ℂ :=
  Zeta23.zerosIn T (2 * T) ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | Zeta23.zeroMult ρ = 1} ∩
    {ρ | ZetaSeparated r L ρ}

theorem sepZeroSet_finite (r L T : ℝ) : (sepZeroSet r L T).Finite :=
  (Zeta23.zerosIn_finite T (2 * T)).subset fun _ hρ => hρ.1.1.1

theorem ncard_sepZeroSet (r L T : ℝ) :
    (sepZeroSet r L T).ncard = N0simpleSeparated r L T (2 * T) := rfl

/-- A separated simple critical zero is carried by exactly one zero copy. -/
theorem exists_unique_copy_of_mem_sepZeroSet {r L T : ℝ} {ρ : ℂ} (hρ : ρ ∈ sepZeroSet r L T) :
    ∃ q₀ : XiZeroCopy, xiSpectralPoint q₀ = (ρ.im : ℂ) ∧
      ∀ q, xiSpectralPoint q = (ρ.im : ℂ) → q = q₀ := by
  obtain ⟨⟨⟨⟨⟨hzeta, hre0, hre1⟩, -, -⟩, hre⟩, hmult⟩, -⟩ := hρ
  simp only [Set.mem_setOf_eq] at hre hmult
  have hord : (analyticOrderAt xi ρ).toNat = 1 := by
    rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩]
    exact hmult
  exact exists_unique_xiZeroCopy_of_simple_critical hre hord

/-- Every other zero copy is at distance more than `r/L` from a separated zero. -/
theorem le_norm_of_mem_sepZeroSet {r L T : ℝ} (hL : 0 < L) {ρ : ℂ} (hρ : ρ ∈ sepZeroSet r L T)
    {q : XiZeroCopy} (hq : xiSpectralPoint q ≠ (ρ.im : ℂ)) :
    r / L ≤ ‖xiSpectralPoint q - (ρ.im : ℂ)‖ := by
  have hre : ρ.re = 1 / 2 := hρ.1.1.2
  have hsep : ZetaSeparated r L ρ := hρ.2
  rw [norm_xiSpectralPoint_sub_im hre]
  have hne : (q.1 : ℂ) ≠ ρ := by
    intro h
    apply hq
    have := norm_xiSpectralPoint_sub_im (q := q) hre
    rw [h, sub_self, norm_zero] at this
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  by_contra hlt
  push Not at hlt
  exact hsep _ (isNontrivialZero_xiZeroCopy q) hne (by
    rw [lt_div_iff₀ hL] at hlt
    linarith)

/-- Distinct separated zeros have ordinates at least `r/L` apart. -/
theorem le_abs_im_sub_of_mem_sepZeroSet {r L T : ℝ} (hL : 0 < L) {ρ ρ' : ℂ}
    (hρ : ρ ∈ sepZeroSet r L T) (hρ' : ρ' ∈ sepZeroSet r L T) (hne : ρ ≠ ρ') :
    r / L ≤ |ρ.im - ρ'.im| := by
  have hre : ρ.re = 1 / 2 := hρ.1.1.2
  have hre' : ρ'.re = 1 / 2 := hρ'.1.1.2
  have hdist : ‖ρ' - ρ‖ = |ρ.im - ρ'.im| := by
    have : ρ' - ρ = ((ρ'.im - ρ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hre, hre']
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_sub_comm]
  rw [← hdist]
  by_contra hlt
  push Not at hlt
  exact hρ.2 ρ' hρ'.1.1.1.1 (Ne.symm hne) (by
    rw [lt_div_iff₀ hL] at hlt
    linarith)

/-- `O(T log T)` zero copies have ordinate in `[T − 1, 2T + 1]`. -/
theorem exists_card_nearCopies_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, T - 1 ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T + 1) →
        (F.card : ℝ) ≤ C * (T * Real.log T) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_card_near_xi_zeros_le
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp hC
  refine ⟨10 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (t₀ + 1) 4)] with T hT F hF
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hTt : t₀ + 1 ≤ T := le_trans (le_max_left _ _) hT
  set M : ℕ := ⌊T⌋₊ + 4 with hM
  set j : XiZeroCopy → ℕ := fun q => ⌊(q.1 : ℂ).im - T + 1⌋₊ with hj
  have hmaps : Set.MapsTo j (F : Set XiZeroCopy) (Finset.range M : Set ℕ) := by
    intro q hq
    have h := hF q hq
    simp only [Finset.coe_range, Set.mem_Iio, hj, hM]
    have h1 : ⌊(q.1 : ℂ).im - T + 1⌋₊ ≤ ⌊T + 2⌋₊ := Nat.floor_le_floor (by linarith)
    have h2 : ⌊T + 2⌋₊ = ⌊T⌋₊ + 2 := by
      rw [show T + 2 = T + ((2 : ℕ) : ℝ) by norm_num, Nat.floor_add_natCast (by linarith)]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hfib : ∀ k ∈ Finset.range M, (({q ∈ F | j q = k}.card : ℕ) : ℝ) ≤ C * Real.log (3 * T) := by
    intro k hk
    set c : ℝ := T - 1 / 2 + k with hc
    have hk' : (k : ℝ) < M := by exact_mod_cast Finset.mem_range.mp hk
    have hMle : (M : ℝ) ≤ T + 4 := by
      rw [hM]
      push_cast
      linarith [Nat.floor_le (show 0 ≤ T by linarith)]
    have hcT : t₀ ≤ c := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hwin := ht₀ c hcT ({q ∈ F | j q = k}) (fun q hq => by
      obtain ⟨hqF, hqk⟩ := Finset.mem_filter.mp hq
      have h := hF q hqF
      have hy0 : 0 ≤ (q.1 : ℂ).im - T + 1 := by linarith
      have hfl1 := Nat.floor_le hy0
      have hfl2 := Nat.lt_floor_add_one ((q.1 : ℂ).im - T + 1)
      simp only [hj] at hqk
      rw [hqk] at hfl1 hfl2
      rw [abs_le]
      constructor <;> linarith)
    refine hwin.trans (mul_le_mul_of_nonneg_left ?_ hC0.le)
    have hcpos : 0 < c := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    exact Real.log_le_log hcpos (by linarith)
  calc ∑ k ∈ Finset.range M, (({q ∈ F | j q = k}.card : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.range M, C * Real.log (3 * T) := Finset.sum_le_sum hfib
    _ = M * (C * Real.log (3 * T)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (T + 4) * (C * (2 * Real.log T)) := by
        have hMle : (M : ℝ) ≤ T + 4 := by
          rw [hM]
          push_cast
          linarith [Nat.floor_le (show 0 ≤ T by linarith)]
        have hlog3 : Real.log (3 * T) ≤ 2 * Real.log T := by
          rw [Real.log_mul (by norm_num) (by linarith)]
          have h3 : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
          linarith
        have hlog0 : 0 ≤ Real.log (3 * T) := Real.log_nonneg (by linarith)
        exact mul_le_mul hMle (mul_le_mul_of_nonneg_left hlog3 hC0.le) (by positivity)
          (by linarith)
    _ ≤ 10 * C * (T * Real.log T) := by
        have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have hk : 0 ≤ 2 * C * Real.log T := by positivity
        calc (T + 4) * (C * (2 * Real.log T)) = (2 * C * Real.log T) * (T + 4) := by ring
          _ ≤ (2 * C * Real.log T) * (5 * T) := mul_le_mul_of_nonneg_left (by linarith) hk
          _ = 10 * C * (T * Real.log T) := by ring

/-- **The packing double sum.**  Summed over the separated zeros, the inverse-square distances to
all zero copies are at most `A δ⁻²` per nearby copy plus twice the Lorentzian masses. -/
theorem sum_tsum_inv_sq_le {r L T : ℝ} (hr : 0 < r) (hL : 0 < L) (G : Finset ℂ)
    (hG : ∀ ρ ∈ G, ρ ∈ sepZeroSet r L T) (near : Finset XiZeroCopy)
    (hnear : ∀ q, T - 1 ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T + 1 → q ∈ near) :
    ∑ ρ ∈ G, ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 ≤
      packConstant / (r / L) ^ 2 * near.card + 2 * ∑ ρ ∈ G, lorentzMass ρ.im := by
  classical
  have hδ : 0 < r / L := div_pos hr hL
  have hc0 : 0 ≤ packConstant / (r / L) ^ 2 := div_nonneg packConstant_pos.le (by positivity)
  have hsum : ∀ ρ ∈ G, Summable (fun q => 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2) :=
    fun ρ _ => summable_inv_sq_norm_xiSpectralPoint_sub _
  rw [← Summable.tsum_finsetSum hsum]
  have hg₁ : Summable (fun q : XiZeroCopy => if q ∈ near then packConstant / (r / L) ^ 2 else 0) :=
    summable_of_ne_finset_zero (s := near) fun q hq => if_neg hq
  have hg₂ : Summable (fun q : XiZeroCopy => 2 * ∑ ρ ∈ G, lorentzMassTerm ρ.im q) :=
    (summable_sum fun ρ _ => summable_lorentzMassTerm ρ.im).mul_left 2
  have hbound : ∀ q, ∑ ρ ∈ G, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 ≤
      (if q ∈ near then packConstant / (r / L) ^ 2 else 0) +
        2 * ∑ ρ ∈ G, lorentzMassTerm ρ.im q := by
    intro q
    have hlt0 : 0 ≤ 2 * ∑ ρ ∈ G, lorentzMassTerm ρ.im q :=
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun ρ _ => lorentzMassTerm_nonneg _ _)
    by_cases hq : T - 1 ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T + 1
    · -- packing
      have hqn : q ∈ near := hnear q hq
      rw [if_pos hqn]
      refine le_trans ?_ (le_add_of_nonneg_right hlt0)
      have hsplit : ∑ ρ ∈ G, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 =
          ∑ ρ ∈ G.filter (fun ρ => xiSpectralPoint q ≠ (ρ.im : ℂ)),
            1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        split_ifs with h
        · rfl
        · push Not at h
          rw [h, sub_self, norm_zero]
          simp
      have hinj : Set.InjOn (fun ρ : ℂ => ρ.im)
          ((G.filter (fun ρ => xiSpectralPoint q ≠ (ρ.im : ℂ)) : Finset ℂ) : Set ℂ) := by
        intro ρ hρ ρ' hρ' heq
        by_contra hne
        have hρG : ρ ∈ G := (Finset.mem_filter.mp hρ).1
        have hρ'G : ρ' ∈ G := (Finset.mem_filter.mp hρ').1
        have := le_abs_im_sub_of_mem_sepZeroSet hL (hG ρ hρG) (hG ρ' hρ'G) hne
        simp only at heq
        rw [heq, sub_self, abs_zero] at this
        linarith
      rw [hsplit, ← Finset.sum_image (f := fun p : ℝ => 1 / ‖xiSpectralPoint q - (p : ℂ)‖ ^ 2) hinj]
      refine sum_inv_sq_le_of_separated hδ _ ?_ _ ?_
      · intro p hp p' hp' hpp
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_image.mp hp'
        have hne : ρ ≠ ρ' := fun h => hpp (by rw [h])
        exact le_abs_im_sub_of_mem_sepZeroSet hL (hG ρ (Finset.mem_filter.mp hρ).1)
          (hG ρ' (Finset.mem_filter.mp hρ').1) hne
      · intro p hp
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨hρG, hne⟩ := Finset.mem_filter.mp hρ
        exact le_norm_of_mem_sepZeroSet hL (hG ρ hρG) hne
    · -- far copies: Lorentzian bound
      have hif : 0 ≤ (if q ∈ near then packConstant / (r / L) ^ 2 else 0) := by
        split_ifs
        · exact hc0
        · exact le_rfl
      refine le_trans ?_ (le_add_of_nonneg_left hif)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      have hρw := (hG ρ hρ).1.1.1
      have hρT : T < ρ.im ∧ ρ.im ≤ 2 * T := ⟨hρw.2.1, hρw.2.2⟩
      set y : ℝ := (ρ.im - (q.1 : ℂ).im) ^ 2 with hy
      have hfar : 1 ≤ y := by
        push Not at hq
        rcases le_or_gt (T - 1) (q.1 : ℂ).im with h | h
        · have := hq h
          nlinarith
        · nlinarith
      have hnorm : y ≤ ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 := by
        have := Complex.abs_re_le_norm (xiSpectralPoint q - (ρ.im : ℂ))
        have hre0 : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
        rw [Complex.sub_re, Complex.ofReal_re, hre0] at this
        rw [hy, ← sq_abs, abs_sub_comm]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      unfold lorentzMassTerm
      rw [← hy]
      calc 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 ≤ 1 / y :=
            one_div_le_one_div_of_le (by linarith) hnorm
        _ ≤ 2 * (1 / (1 + y)) := by
            rw [show 2 * (1 / (1 + y)) = 2 / (1 + y) by ring,
              div_le_div_iff₀ (by linarith) (by linarith)]
            linarith
  calc ∑' q, ∑ ρ ∈ G, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2
      ≤ ∑' q, ((if q ∈ near then packConstant / (r / L) ^ 2 else 0) +
          2 * ∑ ρ ∈ G, lorentzMassTerm ρ.im q) :=
        Summable.tsum_le_tsum hbound (summable_sum fun ρ hρ => hsum ρ hρ) (hg₁.add hg₂)
    _ = packConstant / (r / L) ^ 2 * near.card + 2 * ∑ ρ ∈ G, lorentzMass ρ.im := by
        rw [Summable.tsum_add hg₁ hg₂]
        congr 1
        · rw [tsum_eq_sum (s := near) (fun q hq => if_neg hq),
            Finset.sum_congr rfl fun q hq => if_pos hq, Finset.sum_const, nsmul_eq_mul]
          ring
        · rw [tsum_mul_left]
          congr 1
          have h := Summable.tsum_finsetSum (L := SummationFilter.unconditional XiZeroCopy)
            (f := fun (ρ : ℂ) (q : XiZeroCopy) => lorentzMassTerm ρ.im q) (s := G)
            (fun ρ _ => summable_lorentzMassTerm ρ.im)
          simpa only [lorentzMass] using h

/-- The copies with ordinate in `[T − 1, 2T + 1]` form a finite set. -/
theorem finite_nearCopies (T : ℝ) (hT : 0 ≤ T) :
    {q : XiZeroCopy | T - 1 ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T + 1}.Finite := by
  refine (finite_xiZeroCopy_norm_le (2 * T + 2)).subset fun q hq => ?_
  obtain ⟨h1, h2⟩ := hq
  simp only [Set.mem_setOf_eq]
  have hre0 := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have him : |(xiSpectralPoint q).im| ≤ 1 := by
    have : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by simp [xiSpectralPoint]
    rw [this, abs_neg, abs_le]
    constructor <;> linarith
  have hre : |(xiSpectralPoint q).re| ≤ 2 * T + 1 := by
    have hre0 : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    rw [hre0, abs_le]
    constructor <;> linarith
  linarith

/-- Markov's inequality on a finite set: if the average of `S ≥ 0` over `G` is at most `M`, at
least half of `G` has `S ≤ 2M`. -/
theorem card_le_two_mul_card_filter {G : Finset ℂ} {S : ℂ → ℝ} (hS : ∀ ρ, 0 ≤ S ρ) {M : ℝ}
    (hM : 0 < M) (hsum : ∑ ρ ∈ G, S ρ ≤ M * G.card) :
    (G.card : ℝ) ≤ 2 * (G.filter fun ρ => S ρ ≤ 2 * M).card := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not G (fun ρ => S ρ ≤ 2 * M) S
  have hbad : ((G.filter fun ρ => ¬ S ρ ≤ 2 * M).card : ℝ) * (2 * M) ≤
      ∑ ρ ∈ G.filter (fun ρ => ¬ S ρ ≤ 2 * M), S ρ := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun ρ hρ => (not_le.mp (Finset.mem_filter.mp hρ).2).le
  have hgood : 0 ≤ ∑ ρ ∈ G.filter (fun ρ => S ρ ≤ 2 * M), S ρ :=
    Finset.sum_nonneg fun ρ _ => hS ρ
  have hcards : ((G.filter fun ρ => S ρ ≤ 2 * M).card : ℝ) +
      (G.filter fun ρ => ¬ S ρ ≤ 2 * M).card = G.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := G) _
  have hb : ((G.filter fun ρ => ¬ S ρ ≤ 2 * M).card : ℝ) * 2 * M ≤ G.card * M := by
    linarith
  have hb' : ((G.filter fun ρ => ¬ S ρ ≤ 2 * M).card : ℝ) * 2 ≤ G.card :=
    le_of_mul_le_mul_right (by linarith) hM
  linarith

/-- Near a separated zero with small inverse-square mass, every height is a positivity height. -/
theorem ioo_subset_xiReciprocalSlicePositive {L T K c₀ : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T)
    (hK : 0 < K) (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ 1 / 13) (hc₀K : 8 * K * c₀ ^ 2 ≤ 1 / 20)
    {ρ : ℂ} (hρ : ρ ∈ sepZeroSet (1 / 2) L T)
    (hS : ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 ≤ 2 * K * L ^ 2) :
    Set.Ioo ρ.im (ρ.im + c₀ / L) ⊆
      {t : ℝ | t ∈ Set.Icc T (3 * T) ∧ XiC t ≠ 0 ∧ XiReciprocalSlicePositive t} := by
  intro t htI
  have hL0 : 0 < L := by linarith
  have hρw := hρ.1.1.1
  obtain ⟨q₀, hq₀, huniq⟩ := exists_unique_copy_of_mem_sepZeroSet hρ
  have htγ : 0 < t - ρ.im := by linarith [htI.1]
  have htγ' : t - ρ.im < c₀ / L := by linarith [htI.2]
  have hcL : c₀ / L ≤ 1 / 13 := by
    rw [div_le_iff₀ hL0]
    nlinarith
  have hδhalf : c₀ / L ≤ 1 / 2 / L / 2 := by
    rw [div_div, div_le_div_iff₀ hL0 (by positivity)]
    nlinarith
  have hfar : ∀ q, q ≠ q₀ → 1 / 2 / L ≤ ‖xiSpectralPoint q - (ρ.im : ℂ)‖ := fun q hq =>
    le_norm_of_mem_sepZeroSet hL0 hρ fun h => hq (huniq q h)
  have hXt : XiC t ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp h0
    have hqne : q ≠ q₀ := by
      intro hqq
      rw [hqq, hq₀] at hq
      have : t = ρ.im := by exact_mod_cast hq.symm
      linarith
    have h1 := hfar q hqne
    rw [hq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htγ] at h1
    linarith
  refine ⟨⟨by linarith [hρw.2.1], by linarith [hρw.2.2]⟩, hXt, ?_⟩
  refine xiReciprocalSlicePositive_of_dominant_zero hXt q₀ hq₀ fun F hF => ?_
  have hterm : ∀ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤
      4 * (1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2) := by
    intro q hq
    have hqne : q ≠ q₀ := fun h => hF (h ▸ hq)
    have h1 := hfar q hqne
    have h2 : ‖xiSpectralPoint q - (ρ.im : ℂ)‖ / 2 ≤ ‖xiSpectralPoint q - t‖ := by
      have := norm_sub_le (xiSpectralPoint q - t) ((ρ.im : ℂ) - t)
      rw [show xiSpectralPoint q - t - ((ρ.im : ℂ) - t) = xiSpectralPoint q - ρ.im by ring,
        show ‖(ρ.im : ℂ) - t‖ = t - ρ.im by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
            abs_of_pos htγ]] at this
      linarith
    have h3 : 0 < ‖xiSpectralPoint q - (ρ.im : ℂ)‖ / 2 := by
      have : 0 < 1 / 2 / L := by positivity
      linarith
    calc 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 1 / (‖xiSpectralPoint q - (ρ.im : ℂ)‖ / 2) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h3.le h2 2)
      _ = 4 * (1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2) := by field_simp; ring
  have hsumF : ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ 8 * K * L ^ 2 := by
    calc ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2
        ≤ ∑ q ∈ F, 4 * (1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2) := Finset.sum_le_sum hterm
      _ = 4 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact (summable_inv_sq_norm_xiSpectralPoint_sub _).sum_le_tsum F
            (fun q _ => by positivity)
      _ ≤ 8 * K * L ^ 2 := by linarith
  have hsq : (t - ρ.im) ^ 2 ≤ (c₀ / L) ^ 2 := pow_le_pow_left₀ htγ.le htγ'.le 2
  calc (t - ρ.im) ^ 2 * ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2
      ≤ (c₀ / L) ^ 2 * (8 * K * L ^ 2) :=
        mul_le_mul hsq hsumF (Finset.sum_nonneg fun q _ => by positivity) (by positivity)
    _ = 8 * K * c₀ ^ 2 := by field_simp
    _ ≤ 1 / 20 := hc₀K

/-- The intervals `(γ, γ + c₀/L)` over separated zeros are disjoint and have total length
`|G| c₀/L`. -/
theorem volume_biUnion_ioo_sepZeroSet {L T c₀ : ℝ} (hL : 0 < L) (hc₀le : c₀ < 1 / 2) (G : Finset ℂ) (hG : ∀ ρ ∈ G, ρ ∈ sepZeroSet (1 / 2) L T) :
    volume (⋃ ρ ∈ G, Set.Ioo ρ.im (ρ.im + c₀ / L)) = ENNReal.ofReal (G.card * (c₀ / L)) := by
  have hdisj : (G : Set ℂ).PairwiseDisjoint fun ρ => Set.Ioo ρ.im (ρ.im + c₀ / L) := by
    intro ρ hρ ρ' hρ' hne
    rw [Function.onFun, Set.disjoint_iff]
    rintro t ⟨ht1, ht2⟩
    have hsep := le_abs_im_sub_of_mem_sepZeroSet hL (hG ρ hρ) (hG ρ' hρ') hne
    have hδ : c₀ / L < 1 / 2 / L := div_lt_div_of_pos_right hc₀le hL
    simp only [Set.mem_Ioo] at ht1 ht2
    have : |ρ.im - ρ'.im| < 1 / 2 / L := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  rw [measure_biUnion_finset hdisj (fun ρ _ => measurableSet_Ioo)]
  simp only [Real.volume_Ioo, add_sub_cancel_left]
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

/-- The logarithmic scale bounds used for the density theorem. -/
theorem density_scale_bounds {T C : ℝ} (hT : 2 * Real.pi * Real.exp (max 5 C) ≤ T) :
    5 ≤ Zeta23.l T ∧ C ≤ Zeta23.l T ∧ Real.log T ≤ 2 * Zeta23.l T ∧
      Real.log (2 * T + 4) ≤ 2 * Zeta23.l T := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hLge : max 5 C ≤ Zeta23.l T := by
    rw [Zeta23.l, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith
  have hL5 : 5 ≤ Zeta23.l T := le_trans (le_max_left _ _) hLge
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    nlinarith [Real.pi_lt_d2]
  have hlogT : Real.log T = Zeta23.l T + Real.log (2 * Real.pi) := by
    rw [Zeta23.l, Real.log_div hT0.ne' (by positivity)]
    ring
  have h3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hT4 : 4 ≤ T := by
    have : (1 : ℝ) ≤ Real.exp (max 5 C) := Real.one_le_exp (by positivity)
    nlinarith [Real.pi_gt_three]
  refine ⟨hL5, le_trans (le_max_right _ _) hLge, by linarith, ?_⟩
  have h1 : Real.log (2 * T + 4) ≤ Real.log (3 * T) := Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (3 * T) = Real.log 3 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
  linarith

/-- The dyadic zero count is at least `T L/(4π)`. -/
theorem le_Ncount_of_large {CR T : ℝ}
    (hRvM : |(Zeta23.Ncount T (2 * T) : ℝ) - T / (2 * Real.pi) * Zeta23.ell1 T| ≤ CR * Real.log T)
    (hT : 8 * Real.pi * (|CR| + 1) ≤ T) (hL : 1 ≤ Zeta23.l T)
    (hlogT : Real.log T ≤ 2 * Zeta23.l T) :
    T / (4 * Real.pi) * Zeta23.l T ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hL0 : 0 < Zeta23.l T := by linarith
  have hell : Zeta23.l T ≤ Zeta23.ell1 T := by
    rw [Zeta23.ell1]
    have : (1 : ℝ) ≤ 2 * Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    linarith
  have h1 := (abs_le.mp hRvM).1
  have h2 : T / (2 * Real.pi) * Zeta23.l T ≤ T / (2 * Real.pi) * Zeta23.ell1 T :=
    mul_le_mul_of_nonneg_left hell (by positivity)
  have hT1 : 1 ≤ T := by nlinarith [Real.pi_gt_three, abs_nonneg CR]
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have h3 : CR * Real.log T ≤ T / (4 * Real.pi) * Zeta23.l T := by
    have ha : CR * Real.log T ≤ |CR| * (2 * Zeta23.l T) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hlogT0).trans
        (mul_le_mul_of_nonneg_left hlogT (abs_nonneg _))
    have hb : 8 * Real.pi * |CR| * Zeta23.l T ≤ T * Zeta23.l T := by
      have : 8 * Real.pi * |CR| ≤ T := by nlinarith [Real.pi_pos]
      exact mul_le_mul_of_nonneg_right this hL0.le
    have hc : |CR| * (2 * Zeta23.l T) = (8 * Real.pi * |CR| * Zeta23.l T) / (4 * Real.pi) := by
      field_simp
      ring
    have hd : T / (4 * Real.pi) * Zeta23.l T = T * Zeta23.l T / (4 * Real.pi) := by ring
    rw [hd]
    calc CR * Real.log T ≤ |CR| * (2 * Zeta23.l T) := ha
      _ = (8 * Real.pi * |CR| * Zeta23.l T) / (4 * Real.pi) := hc
      _ ≤ T * Zeta23.l T / (4 * Real.pi) := div_le_div_of_nonneg_right hb (by positivity)
  have h4 : T / (2 * Real.pi) * Zeta23.l T = 2 * (T / (4 * Real.pi) * Zeta23.l T) := by
    field_simp
    ring
  linarith

/-- **Reciprocal slice positivity at a positive proportion of heights.** -/
theorem exists_pos_density_xiReciprocalSlicePositive :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (c * T) ≤
        volume {t : ℝ | t ∈ Set.Icc T (3 * T) ∧ XiC t ≠ 0 ∧ XiReciprocalSlicePositive t} := by
  classical
  obtain ⟨Cn, hCn0, hnear⟩ := exists_card_nearCopies_le
  obtain ⟨CR, TR, hRvM⟩ := Zeta23.riemannVonMangoldt_zeta.main
  obtain ⟨TS, hTS⟩ := separated_simple_critical (r := 1 / 2) (by norm_num) (by norm_num)
    (1 / 8) (by norm_num)
  obtain ⟨Tn, hTn⟩ := eventually_atTop.mp hnear
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 256 * Real.pi * packConstant * Cn + 48 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; have := packConstant_pos; positivity
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = 1 / (13 * (K + 1)) := ⟨_, rfl⟩
  have hc₀0 : 0 < c₀ := by rw [hc₀def]; positivity
  have hc₀le : c₀ ≤ 1 / 13 := by
    rw [hc₀def]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hc₀K : 8 * K * c₀ ^ 2 ≤ 1 / 20 := by
    rw [hc₀def, div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨c₀ / (64 * Real.pi), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop TR, eventually_ge_atTop TS, eventually_ge_atTop Tn,
    eventually_ge_atTop (2 * Real.pi * Real.exp (max 5 xiLineTwoLogDerivConstant)),
    eventually_ge_atTop (8 * Real.pi * (|CR| + 1))] with T hTR hTS' hTn' hTexp hTCR
  obtain ⟨hL5, hLCx, hlogT2, hlog2T4⟩ := density_scale_bounds hTexp
  have hT1 : 1 ≤ T := le_trans (by nlinarith [Real.pi_gt_three, abs_nonneg CR]) hTCR
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Zeta23.l T := ⟨_, rfl⟩
  rw [← hLdef] at hL5 hLCx hlogT2 hlog2T4
  have hL0 : 0 < L := by linarith
  have hN : T / (4 * Real.pi) * L ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by
    rw [hLdef]
    exact le_Ncount_of_large (hRvM T hTR) hTCR (by rw [← hLdef]; linarith)
      (by rw [← hLdef]; exact hlogT2)
  -- the separated set
  obtain ⟨G, hGdef⟩ : ∃ G : Finset ℂ, G = (sepZeroSet_finite (1 / 2) L T).toFinset := ⟨_, rfl⟩
  have hGmem : ∀ ρ ∈ G, ρ ∈ sepZeroSet (1 / 2) L T := fun ρ hρ => by
    rw [hGdef] at hρ
    exact (Set.Finite.mem_toFinset _).mp hρ
  have hGcard : T * L / (32 * Real.pi) ≤ (G.card : ℝ) := by
    have h := hTS T hTS'
    have hcard : (G.card : ℝ) = N0simpleSeparated (1 / 2) L T (2 * T) := by
      rw [hGdef, ← ncard_sepZeroSet, Set.ncard_eq_toFinset_card _ (sepZeroSet_finite (1 / 2) L T)]
    rw [hcard, hLdef]
    have hNnn : (0 : ℝ) ≤ Zeta23.Ncount T (2 * T) := Nat.cast_nonneg _
    have hHD := half_lt_HD_one
    have h8 : (1 / 8 : ℝ) * Zeta23.Ncount T (2 * T) ≤
        (Zeta23.ThmD.HD 1 - (1 / 2) ^ 2 - 1 / 8) * Zeta23.Ncount T (2 * T) :=
      mul_le_mul_of_nonneg_right (by linarith) hNnn
    rw [← hLdef]
    calc T * L / (32 * Real.pi) = 1 / 8 * (T / (4 * Real.pi) * L) := by field_simp; ring
      _ ≤ 1 / 8 * (Zeta23.Ncount T (2 * T) : ℝ) := by gcongr
      _ ≤ _ := h8.trans (by rw [hLdef]; exact h)
  -- the nearby copies
  have hnearFin := finite_nearCopies T hT0.le
  obtain ⟨near, hneardef⟩ : ∃ near : Finset XiZeroCopy, near = hnearFin.toFinset := ⟨_, rfl⟩
  have hnearmem : ∀ q, T - 1 ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T + 1 → q ∈ near := by
    intro q hq
    rw [hneardef]
    exact hnearFin.mem_toFinset.mpr hq
  have hnearcard : (near.card : ℝ) ≤ 2 * Cn * (T * L) := by
    have h := hTn T hTn' near (fun q hq => by
      rw [hneardef] at hq
      exact hnearFin.mem_toFinset.mp hq)
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    calc (near.card : ℝ) ≤ Cn * (T * Real.log T) := h
      _ ≤ Cn * (T * (2 * L)) := by gcongr
      _ = 2 * Cn * (T * L) := by ring
  -- the double sum
  have hsumS : ∑ ρ ∈ G, ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 ≤ K * L ^ 2 * G.card := by
    have h := sum_tsum_inv_sq_le (r := 1 / 2) (by norm_num) hL0 G hGmem near hnearmem
    have hlor : ∑ ρ ∈ G, lorentzMass ρ.im ≤ G.card * (24 * L) := by
      calc ∑ ρ ∈ G, lorentzMass ρ.im ≤ ∑ ρ ∈ G, (24 * L) := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            have hρw := (hGmem ρ hρ).1.1.1
            have hρ0 : 0 < ρ.im := by linarith [hρw.2.1]
            refine (lorentzMass_le_log ρ.im).trans ?_
            have : Real.log (|ρ.im| + 4) ≤ Real.log (2 * T + 4) :=
              Real.log_le_log (by positivity) (by rw [abs_of_pos hρ0]; linarith [hρw.2.2])
            linarith
        _ = G.card * (24 * L) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hpack : packConstant / (1 / 2 / L) ^ 2 = 4 * packConstant * L ^ 2 := by
      field_simp
      ring
    have hP0 := packConstant_pos
    have hG0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
    have h1 : T * L ≤ 32 * Real.pi * G.card := by
      have := hGcard
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hLsq : L ≤ L ^ 2 := by nlinarith
    calc ∑ ρ ∈ G, ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2
        ≤ packConstant / (1 / 2 / L) ^ 2 * near.card + 2 * ∑ ρ ∈ G, lorentzMass ρ.im := h
      _ ≤ 4 * packConstant * L ^ 2 * (2 * Cn * (T * L)) + 2 * (G.card * (24 * L)) := by
          rw [hpack]
          gcongr
      _ ≤ 4 * packConstant * L ^ 2 * (2 * Cn * (32 * Real.pi * G.card)) +
          2 * (G.card * (24 * L ^ 2)) := by
          gcongr
      _ = K * L ^ 2 * G.card := by rw [hKdef]; ring
  -- Markov
  have hKL : 0 < K * L ^ 2 := by positivity
  have hG₁ := card_le_two_mul_card_filter
    (S := fun ρ => ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2)
    (fun ρ => tsum_nonneg fun q => by positivity) hKL hsumS
  obtain ⟨G₁, hG₁def⟩ : ∃ G₁ : Finset ℂ, G₁ = G.filter fun ρ =>
      ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 ≤ 2 * (K * L ^ 2) := ⟨_, rfl⟩
  rw [← hG₁def] at hG₁
  have hG₁mem : ∀ ρ ∈ G₁, ρ ∈ sepZeroSet (1 / 2) L T := fun ρ hρ => by
    rw [hG₁def] at hρ
    exact hGmem ρ (Finset.mem_filter.mp hρ).1
  have hsub : (⋃ ρ ∈ G₁, Set.Ioo ρ.im (ρ.im + c₀ / L)) ⊆
      {t : ℝ | t ∈ Set.Icc T (3 * T) ∧ XiC t ≠ 0 ∧ XiReciprocalSlicePositive t} := by
    refine Set.iUnion₂_subset fun ρ hρ => ?_
    have hρS : ∑' q, 1 / ‖xiSpectralPoint q - (ρ.im : ℂ)‖ ^ 2 ≤ 2 * K * L ^ 2 := by
      have := (Finset.mem_filter.mp (hG₁def ▸ hρ)).2
      linarith
    exact ioo_subset_xiReciprocalSlicePositive (by linarith) hT1 hK0 hc₀0 hc₀le hc₀K
      (hG₁mem ρ hρ) hρS
  have hvol := volume_biUnion_ioo_sepZeroSet (c₀ := c₀) hL0 (by linarith) G₁ hG₁mem
  calc ENNReal.ofReal (c₀ / (64 * Real.pi) * T) ≤ ENNReal.ofReal (G₁.card * (c₀ / L)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : T * L / (64 * Real.pi) ≤ G₁.card := by
          have h' := hGcard
          rw [div_le_iff₀ (by positivity)] at h' ⊢
          have h'' := mul_le_mul_of_nonneg_left hG₁ (show (0 : ℝ) ≤ 32 * Real.pi by positivity)
          linarith
        calc c₀ / (64 * Real.pi) * T = (T * L / (64 * Real.pi)) * (c₀ / L) := by
              field_simp
          _ ≤ G₁.card * (c₀ / L) := by gcongr
    _ = volume (⋃ ρ ∈ G₁, Set.Ioo ρ.im (ρ.im + c₀ / L)) := hvol.symm
    _ ≤ _ := measure_mono hsub

end

end RHTower
