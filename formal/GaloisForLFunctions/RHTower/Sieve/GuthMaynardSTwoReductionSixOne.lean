import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionClasses

/-!
# Guth–Maynard §6: the reduction of `S₂` to (6.1)

Guth–Maynard (arXiv:2405.20552, proof of Proposition 6.1, (6.1)):

`S₂ ⪅ (N²/M) Σ_{t₁,t₂∈W} |Σ_{m∼M} a_m m^{i(t₁−t₂)}|²` for some `M ⪅ T/N`, `|a_m| ≤ 1`.

This module proves it for the Chen–Gupta–Li bump in the summed form

`‖S₂‖ ≤ C T^{4ε} Σ_{k long} Σ_{j ≤ log₂ M_k} (N²/2^j) Σ_{t₁,t₂∈W} |Σ_{m ∈ [2^j,2^{j+1}) ∩ [1,M_k]} m^{i(t₁−t₂)}|²
      + C N² |W|²`

for `W ⊂ [0,T]` `T^ε`-separated, `N ≥ 1`, `T ≥ 1` (`gmS2_le_sixOne`, assembled in
`GuthMaynardSTwoReductionAssembly`).  This module holds the objects of (6.1) and the bound for
one long class.  The last term is the block `M = 1`, `a₁ = 1`
(`Σ_{t₁,t₂} 1 = |W|²`), as in the paper ("the dyadic range `M = 1` dominates the error").

Mechanism: `S₂ = 3N³ ĥ₀(0) Σ|A(t₁−t₂)|² + O(N²|W|²)` (planes, diagonal, (5.1));
for `t₁ ≠ t₂` in a long class `k` Lemma 6.2 at length `M_k`, squared with Cauchy–Schwarz in `u`,
the majorant principle removing `u`, and the dyadic split of `[1, M_k]`; short classes and the
diagonal are `O(N²)` per pair by Lemma 4.3.
-/

set_option autoImplicit false

open Complex Finset
open scoped FourierTransform

noncomputable section

namespace RHTower.GuthMaynard

open Sieve

/-- The conclusion of Lemma 6.2 for `ζ` with a free admissible length, at a constant `C`. -/
def GMLemma62Bound (w : CGLRealSmoothBump) (ε C : ℝ) : Prop :=
  ∀ (T t N : ℝ) (M : ℕ), 1 ≤ T → 1 ≤ N → T ^ ε ≤ |t| → |t| ≤ T → 1 ≤ M →
    |t| ^ (1 + ε) / N ≤ M → (M : ℝ) ≤ 8 * T ^ 2 →
    ‖gmNonzero w N t‖ ≤ C * |t| ^ (-(1 / 2 : ℝ)) *
        (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly M (t + u)‖) + C * T ^ (-100 : ℝ)

theorem exists_gmLemma62Bound (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ GMLemma62Bound w ε C :=
  cglGM_lemma62_zeta_of_length w hε

/-- Long classes: `k < K(T)` with `N ≤ (2^{k+1})^{1+ε}`. -/
def gmLongClasses (ε N T : ℝ) : Finset ℕ :=
  (Finset.range (gmClassCount T)).filter (fun k => N ≤ ((2 : ℝ) ^ (k + 1)) ^ (1 + ε))

/-- The dyadic blocks of class `k`: `Σ_{j ≤ log₂ M_k} (N²/2^j) Σ_{t₁,t₂} |Σ_{m ∈ block j} m^{i(t₁−t₂)}|²`. -/
def gmClassBlockSum (ε N : ℝ) (W : Finset ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (Nat.log 2 (gmClassLength ε N k) + 1),
    N ^ 2 / 2 ^ j * hbPairSum W (dyadicSegmentBlock (gmClassLength ε N k) j)
      (fun _ => ((1 : ℝ) : ℂ))

/-- The right side of (6.1), summed over the long classes. -/
def gmSixOneSum (ε N T : ℝ) (W : Finset ℝ) : ℝ :=
  ∑ k ∈ gmLongClasses ε N T, gmClassBlockSum ε N W k

/-- The class integral `G_k(x,y) = ∫_{−U}^{U} |D_{M_k}(x−y+u)|² du`, `U = T^ε/2`. -/
def gmClassIntegral (ε N T : ℝ) (k : ℕ) (x y : ℝ) : ℝ :=
  ∫ u in (-(T ^ ε / 2))..(T ^ ε / 2), ‖cglGMHeadPoly (gmClassLength ε N k) (x - y + u)‖ ^ 2

/-- The class weight `N³ · 4C² U / 2^k`, `U = T^ε/2`. -/
def gmClassWeight (ε C N T : ℝ) (k : ℕ) : ℝ :=
  N ^ 3 * (4 * C ^ 2 * (T ^ ε / 2) * ((2 : ℝ) ^ k)⁻¹)

theorem gmClassBlockSum_nonneg (ε N : ℝ) (W : Finset ℝ) (k : ℕ) :
    0 ≤ gmClassBlockSum ε N W k :=
  Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hbPairSum_nonneg _ _ _)

theorem gmSixOneSum_nonneg (ε N T : ℝ) (W : Finset ℝ) : 0 ≤ gmSixOneSum ε N T W :=
  Finset.sum_nonneg fun k _ => gmClassBlockSum_nonneg ε N W k

theorem gmClassWeight_nonneg (ε C N T : ℝ) (hN : 0 ≤ N) (hT : 0 ≤ T) (k : ℕ) :
    0 ≤ gmClassWeight ε C N T k := by
  have := Real.rpow_nonneg hT ε
  unfold gmClassWeight
  positivity

theorem gmClassIntegral_nonneg (ε N T : ℝ) (hT : 0 ≤ T) (k : ℕ) (x y : ℝ) :
    0 ≤ gmClassIntegral ε N T k x y := by
  have := Real.rpow_nonneg hT ε
  exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity

/-- `∫_{−U}^{U} Σ_{x,y} |D_M(x−y+u)|² ≤ 2U Σ_{x,y} |Σ_{m≤M} m^{i(x−y)}|²`. -/
theorem integral_sum_normSq_head_le (M : ℕ) (W : Finset ℝ) {U : ℝ} (hU : 0 ≤ U) :
    ∫ u in (-U)..U, ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly M (x - y + u)‖ ^ 2 ≤
      2 * U * hbPairSum W (Finset.Icc 1 M) (fun _ => ((1 : ℝ) : ℂ)) := by
  have hcont : Continuous fun u : ℝ =>
      ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly M (x - y + u)‖ ^ 2 :=
    continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      (((continuous_cglGMHeadPoly M).comp (continuous_const.add continuous_id)).norm).pow 2
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by linarith : -U ≤ U)
    (hcont.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun u _ => sum_normSq_head_le_hbPairSum M W u)
  rwa [intervalIntegral.integral_const, smul_eq_mul, show U - -U = 2 * U by ring] at h

/-- The class integrals sum to the integral of the pair sum. -/
theorem sum_gmClassIntegral_eq (ε N T : ℝ) (k : ℕ) (W : Finset ℝ) :
    ∑ x ∈ W, ∑ y ∈ W, gmClassIntegral ε N T k x y =
      ∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
        ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly (gmClassLength ε N k) (x - y + u)‖ ^ 2 := by
  have hc : ∀ x y : ℝ, Continuous fun u : ℝ =>
      ‖cglGMHeadPoly (gmClassLength ε N k) (x - y + u)‖ ^ 2 := fun x y =>
    (((continuous_cglGMHeadPoly _).comp (continuous_const.add continuous_id)).norm).pow 2
  rw [intervalIntegral.integral_finsetSum fun x _ => (continuous_finsetSum _ fun y _ =>
    hc x y).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [intervalIntegral.integral_finsetSum fun y _ => (hc x y).intervalIntegrable _ _]
  rfl

/-- `(2T)^ε ≤ 2 T^ε` for `ε ≤ 1`. -/
theorem two_mul_rpow_le {T ε : ℝ} (hT : 0 ≤ T) (hε1 : ε ≤ 1) :
    (2 * T) ^ ε ≤ 2 * T ^ ε := by
  rw [Real.mul_rpow (by norm_num) hT]
  have : (2 : ℝ) ^ ε ≤ 2 := by
    calc (2 : ℝ) ^ ε ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
      _ = 2 := Real.rpow_one 2
  exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hT ε)

/-- **One long class.**
`(N³ 4C²U/2^k) ∫_{−U}^{U} Σ_{x,y} |D_{M_k}(x−y+u)|² ≤ 16 C² (15 + 4/ε) (T^ε)^4 Σ_j (N²/2^j) hbPairSum_j`. -/
theorem gmClassWeight_mul_integral_le {ε C N T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ N)
    (hT : 1 ≤ T) {k : ℕ} (hk : k ∈ gmLongClasses ε N T) (W : Finset ℝ) :
    gmClassWeight ε C N T k * (∫ u in (-(T ^ ε / 2))..(T ^ ε / 2),
        ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly (gmClassLength ε N k) (x - y + u)‖ ^ 2) ≤
      16 * C ^ 2 * (15 + 4 / ε) * (T ^ ε) ^ 4 * gmClassBlockSum ε N W k := by
  obtain ⟨hkK, hlong⟩ := Finset.mem_filter.mp hk
  have hk2 : (2 : ℝ) ^ k ≤ T := two_pow_le_of_lt_count hT (Finset.mem_range.mp hkK)
  obtain ⟨hM1, hM8, _⟩ := gmClassLength_spec hε hε1 hN hT hk2
  set M := gmClassLength ε N k with hM
  have hT0 : 0 < T := by linarith
  have hTe : 0 < T ^ ε := Real.rpow_pos_of_pos hT0 ε
  set U : ℝ := T ^ ε / 2 with hU
  have hU0 : 0 ≤ U := by positivity
  have hN0 : 0 < N := by linarith
  set S : ℝ := ∑ j ∈ Finset.range (Nat.log 2 M + 1),
    hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)) with hS
  have hint := integral_sum_normSq_head_le M W hU0
  have hdy := hbPairSum_Icc_le_dyadicBlocks W M (fun _ => ((1 : ℝ) : ℂ))
  have hlog := log_count_le hε hT hM1 hM8
  have hconv : ∀ j ∈ Finset.range (Nat.log 2 M + 1),
      N ^ 3 * ((2 : ℝ) ^ k)⁻¹ * hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)) ≤
        4 * (2 * T) ^ ε * (N ^ 2 / 2 ^ j *
          hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ))) := by
    intro j hj
    have hjM : 2 ^ j ≤ M := by
      have hjl : j ≤ Nat.log 2 M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (Nat.pow_le_pow_right (by norm_num) hjl).trans (Nat.pow_log_le_self 2 (by omega))
    have hmul := mul_two_pow_le_of_long hε hε1 hN hT hk2 hlong hjM
    have hhb := hbPairSum_nonneg W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ))
    have hw : N ^ 3 * ((2 : ℝ) ^ k)⁻¹ ≤ 4 * (2 * T) ^ ε * (N ^ 2 / 2 ^ j) := by
      rw [show N ^ 3 * ((2 : ℝ) ^ k)⁻¹ = N ^ 2 * (N / 2 ^ k) by ring,
        show 4 * (2 * T) ^ ε * (N ^ 2 / 2 ^ j) = N ^ 2 * (4 * (2 * T) ^ ε / 2 ^ j) by ring]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
    calc _ ≤ 4 * (2 * T) ^ ε * (N ^ 2 / 2 ^ j) *
          hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)) :=
          mul_le_mul_of_nonneg_right hw hhb
      _ = _ := by ring
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hbPairSum_nonneg _ _ _
  have hBS : N ^ 3 * ((2 : ℝ) ^ k)⁻¹ * S ≤ 4 * (2 * T) ^ ε * gmClassBlockSum ε N W k := by
    rw [hS, Finset.mul_sum, gmClassBlockSum, ← hM, Finset.mul_sum]
    exact Finset.sum_le_sum hconv
  have h2T := two_mul_rpow_le hT0.le hε1
  have hB0 := gmClassBlockSum_nonneg ε N W k
  have hlog0 : (0 : ℝ) ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc gmClassWeight ε C N T k * (∫ u in (-U)..U,
        ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly M (x - y + u)‖ ^ 2)
      ≤ gmClassWeight ε C N T k * (2 * U * (((Nat.log 2 M + 1 : ℕ) : ℝ) * S)) :=
        mul_le_mul_of_nonneg_left (hint.trans (mul_le_mul_of_nonneg_left hdy (by positivity)))
          (gmClassWeight_nonneg ε C N T hN0.le hT0.le k)
    _ = 8 * C ^ 2 * U ^ 2 * ((Nat.log 2 M + 1 : ℕ) : ℝ) * (N ^ 3 * ((2 : ℝ) ^ k)⁻¹ * S) := by
        unfold gmClassWeight; ring
    _ ≤ 8 * C ^ 2 * U ^ 2 * ((15 + 4 / ε) * T ^ ε) *
          (4 * (2 * T) ^ ε * gmClassBlockSum ε N W k) := by
        gcongr
    _ ≤ 8 * C ^ 2 * U ^ 2 * ((15 + 4 / ε) * T ^ ε) *
          (4 * (2 * T ^ ε) * gmClassBlockSum ε N W k) := by
        gcongr
    _ = 16 * C ^ 2 * (15 + 4 / ε) * (T ^ ε) ^ 4 * gmClassBlockSum ε N W k := by
        rw [hU]; ring

end RHTower.GuthMaynard
