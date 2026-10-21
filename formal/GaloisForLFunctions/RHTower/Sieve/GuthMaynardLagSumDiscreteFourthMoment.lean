import GaloisForLFunctions.RHTower.Sieve.GuthMaynardDifferenceMultiplicity
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenTwo
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumLocalConstancy

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 11.6: the discrete fourth moment of `R`

For `W ⊆ [T₀, T₀ + T]`, `M ≥ 1` and `S ⊆ (M, 2M+1]` (Guth–Maynard, arXiv 2405.20552, Lemma 11.6):

`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|⁴ ⪅ |W|⁴ M + M² E(W) + E(W)^{3/4} |W| T^{1/2} M`.

Proof (`sum_lagSum_pow_four_le_of_blockBound`). Split `|R(v)|² = Σ_{j<J} R_j(v)` by the dyadic class
of the multiplicity of `⌊t₁ − t₂⌋` (`GuthMaynardDifferenceMultiplicity`) and use Cauchy–Schwarz,
`|R|⁴ ≤ J Σ_j |R_j|²`. The duality identity turns `Σ_{n₁,n₂} |R_j(n₁/n₂)|²` into
`Σ_{p,q ∈ P_j} |F(y_p − y_q)|²`, `F(z) = Σ_{n ∈ S} n^{iz}`. Writing `y_p − y_q = (u_p − u_q) − σ`
with `|σ| < 1`, the shifted square form of Lemma 11.3 bounds `|F(y_p − y_q)|²` by a Cauchy-weighted
average of `|F(u_p − u_q + η)|²`; regrouping by `u` costs `4^{j+1}`, and for each `η` the sum over
`u₁, u₂ ∈ U_j` is a Heath-Brown pair sum over the integer set `U_j ⊆ [−T−1, T]` (scale `2T + 1`)
with unimodular coefficients `n^{iη}`. Finally `2^j |U_j| ≤ |W|²` and `4^j |U_j| ≤ E(W)` give
`4^j (|U_j|² M + |U_j| M² + |U_j|^{5/4} T^{1/2} M) ≤ |W|⁴ M + E M² + E^{3/4} |W| T^{1/2} M`.

* `guthMaynard_lemma116`: every `M ≥ 1`, over `HeathBrownPairSumBound`;
* `guthMaynard_lemma116_short`: `M ≤ T^{1/4}`, unconditional (corpus short-block theorem).
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### The block polynomial `F(z) = Σ_{n∈S} n^{iz}` -/

/-- `F(z) = Σ_{n ∈ S} n^{iz}`. -/
def blockPoly (S : Finset ℕ) (z : ℝ) : ℂ := ∑ n ∈ S, Complex.exp (Complex.I * z * Real.log n)

theorem blockPoly_eq_finiteFrequencyPoly (S : Finset ℕ) (z : ℝ) :
    blockPoly S z = Sieve.finiteFrequencyPoly (fun _ => 1) S
      (fun n => Real.log n / (2 * Real.pi)) z := by
  unfold blockPoly Sieve.finiteFrequencyPoly
  refine sum_congr rfl fun n _ => ?_
  rw [one_mul]
  congr 1
  have h : 2 * Real.pi * (z * (Real.log n / (2 * Real.pi))) = z * Real.log n := by field_simp
  rw [h]; push_cast; ring_nf

theorem continuous_blockPoly (S : Finset ℕ) : Continuous (blockPoly S) := by
  unfold blockPoly; fun_prop

theorem norm_blockPoly_le (S : Finset ℕ) (z : ℝ) : ‖blockPoly S z‖ ≤ S.card := by
  unfold blockPoly
  calc _ ≤ ∑ n ∈ S, ‖Complex.exp (Complex.I * z * Real.log n)‖ := norm_sum_le _ _
    _ = ∑ _n ∈ S, (1 : ℝ) := sum_congr rfl fun n _ => norm_exp_mul_log _ _
    _ = S.card := by simp

/-- The frequencies `log n/2π`, `M < n ≤ 2M + 1`, lie within `1` of `log M/2π`. -/
theorem abs_log_div_two_pi_sub_le_of_mem {M n : ℕ} (hM : 1 ≤ M)
    (hn : n ∈ Finset.Ioc M (2 * M + 1)) :
    |Real.log n / (2 * Real.pi) - Real.log M / (2 * Real.pi)| ≤ 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hn1 : (M : ℝ) ≤ n := by exact_mod_cast h1.le
  have hn2 : (n : ℝ) ≤ 3 * M := by
    have : n ≤ 3 * M := by omega
    exact_mod_cast this
  have hlog0 : 0 ≤ Real.log n - Real.log M := sub_nonneg.mpr (Real.log_le_log (by linarith) hn1)
  have hlog1 : Real.log n - Real.log M ≤ 2 := by
    rw [← Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
    have : (n : ℝ) / M ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc Real.log (n / M) ≤ n / M - 1 :=
          Real.log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
      _ ≤ 2 := by linarith
  rw [← sub_div, abs_div, abs_of_nonneg hlog0, abs_of_pos Real.two_pi_pos,
    div_le_one Real.two_pi_pos]
  linarith [Real.pi_gt_three]

/-- The Cauchy weight `w(η) = 3 bandCauchy / (1 + η²)`, of total mass `3π bandCauchy`. -/
def cauchyWeight (η : ℝ) : ℝ := 3 * bandCauchy / (1 + η ^ 2)

theorem cauchyWeight_nonneg (η : ℝ) : 0 ≤ cauchyWeight η := by
  unfold cauchyWeight; have := bandCauchy_nonneg; positivity

theorem integrable_cauchyWeight : Integrable cauchyWeight := by
  have e : cauchyWeight = fun η => 3 * bandCauchy * (1 + η ^ 2)⁻¹ := by
    funext η; simp [cauchyWeight, div_eq_mul_inv]
  rw [e]
  exact integrable_inv_one_add_sq.const_mul _

theorem integral_cauchyWeight : ∫ η, cauchyWeight η = 3 * Real.pi * bandCauchy := by
  simp only [cauchyWeight, div_eq_mul_inv]
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  ring

/-- **Shifted square form for `F`** (Lemma 11.3 at unit scale): for `|σ| ≤ 1`,
`|F(x − σ)|² ≤ ‖K‖₁ ∫ w(η) |F(x + η)|² dη`. -/
theorem norm_blockPoly_sub_sq_le {M : ℕ} (hM : 1 ≤ M) {S : Finset ℕ}
    (hS : S ⊆ Finset.Ioc M (2 * M + 1)) (x σ : ℝ) (hσ : |σ| ≤ 1) :
    ‖blockPoly S (x - σ)‖ ^ 2 ≤ bandMass * ∫ η, cauchyWeight η * ‖blockPoly S (x + η)‖ ^ 2 := by
  have h := norm_finiteFrequencyPoly_sub_sq_le (fun _ => (1 : ℂ)) S
    (fun n => Real.log n / (2 * Real.pi)) (a := Real.log M / (2 * Real.pi))
    (fun n hn => abs_log_div_two_pi_sub_le_of_mem hM (hS hn)) x σ hσ
  simpa only [← blockPoly_eq_finiteFrequencyPoly, cauchyWeight] using h

theorem integrable_cauchyWeight_mul (S : Finset ℕ) (x : ℝ) :
    Integrable fun η => cauchyWeight η * ‖blockPoly S (x + η)‖ ^ 2 := by
  refine integrable_cauchyWeight.mul_bdd (c := (S.card : ℝ) ^ 2)
    (((continuous_blockPoly S).comp (continuous_const_add x)).norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_blockPoly_le S _) 2

/-! ### Step 1: classes and Cauchy–Schwarz -/

/-- `Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|⁴ ≤ J Σ_{j<J} Σ_{p,q ∈ P_j} |F(y_p − y_q)|²`. -/
theorem sum_lagSum_pow_four_le_classes (W : Finset ℝ) {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4 ≤
      diffClassCount W * ∑ j ∈ range (diffClassCount W),
        ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j,
          ‖blockPoly S ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 := by
  set J := diffClassCount W
  have hpt : ∀ v : ℝ, ‖lagSum W v‖ ^ 4 ≤
      J * ∑ j ∈ range J, ‖labelledLagSum (diffClassSet W j) (fun p => p.1 - p.2) v‖ ^ 2 := by
    intro v
    have h1 : ‖lagSum W v‖ ^ 4 = ‖((‖lagSum W v‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]; ring
    rw [h1, normSq_lagSum_eq_sum_classes]
    calc ‖∑ j ∈ range J, labelledLagSum (diffClassSet W j) (fun p => p.1 - p.2) v‖ ^ 2
        ≤ (∑ j ∈ range J, ‖labelledLagSum (diffClassSet W j) (fun p => p.1 - p.2) v‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (range J).card * ∑ j ∈ range J,
            ‖labelledLagSum (diffClassSet W j) (fun p => p.1 - p.2) v‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = J * _ := by rw [card_range]
  calc ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4
      ≤ ∑ n₁ ∈ S, ∑ n₂ ∈ S, J * ∑ j ∈ range J,
          ‖labelledLagSum (diffClassSet W j) (fun p => p.1 - p.2) ((n₁ : ℝ) / n₂)‖ ^ 2 :=
        sum_le_sum fun _ _ => sum_le_sum fun _ _ => hpt _
    _ = J * ∑ j ∈ range J, ∑ n₁ ∈ S, ∑ n₂ ∈ S,
          ‖labelledLagSum (diffClassSet W j) (fun p => p.1 - p.2) ((n₁ : ℝ) / n₂)‖ ^ 2 := by
        simp only [← mul_sum]
        congr 1
        refine (sum_congr rfl fun n₁ _ => sum_comm).trans ?_
        exact sum_comm
    _ = _ := by
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [sum_normSq_labelledLagSum_eq _ _ hS]
        refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
        unfold blockPoly
        push_cast
        rfl

/-! ### Step 2: one class -/

/-- **One class.** Under `HeathBrownBlockBound M (2T+1) K`:
`Σ_{p,q ∈ P_j} |F(y_p − y_q)|² ≤ ‖K‖₁ 4^{j+1} 3π bandCauchy (2K+2) HB(|U_j|, M, 2T+1)`. -/
theorem sum_class_le {M : ℕ} {T K : ℝ} (hHB : HeathBrownBlockBound M (2 * T + 1) K)
    (hT : 0 ≤ T) (hM : 1 ≤ M) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc M (2 * M + 1))
    {W : Finset ℝ} {T₀ : ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) (j : ℕ) :
    ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j,
        ‖blockPoly S ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 ≤
      bandMass * (((2 : ℝ) ^ (j + 1)) ^ 2 * (3 * Real.pi * bandCauchy * ((2 * K + 2) *
        heathBrownMajorant (diffClassValues W j).card M (2 * T + 1)))) := by
  classical
  set Φ : ℤ → ℝ := fun u => ∫ η, cauchyWeight η * ‖blockPoly S (u + η)‖ ^ 2 with hΦdef
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u =>
    integral_nonneg fun η => mul_nonneg (cauchyWeight_nonneg η) (by positivity)
  -- shift each difference to the integer lattice
  have hshift : ∀ p q : ℝ × ℝ, ‖blockPoly S ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 ≤
      bandMass * Φ (diffFloor p - diffFloor q) := by
    intro p q
    set σ : ℝ := ((diffFloor p - diffFloor q : ℤ) : ℝ) - ((p.1 - p.2) - (q.1 - q.2))
    have hσ : |σ| ≤ 1 := by
      have a1 := Int.floor_le (p.1 - p.2)
      have a2 := Int.lt_floor_add_one (p.1 - p.2)
      have b1 := Int.floor_le (q.1 - q.2)
      have b2 := Int.lt_floor_add_one (q.1 - q.2)
      simp only [σ, diffFloor, Int.cast_sub]
      rw [abs_le]; constructor <;> linarith
    have h := norm_blockPoly_sub_sq_le hM hS ((diffFloor p - diffFloor q : ℤ) : ℝ) σ hσ
    simp only [σ, sub_sub_cancel] at h
    exact h
  -- the Heath-Brown pair sum for each shift `η`
  have hHBη : ∀ η : ℝ, ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j,
      ‖blockPoly S ((u₁ - u₂ : ℤ) + η)‖ ^ 2 ≤
        (2 * K + 2) * heathBrownMajorant (diffClassValues W j).card M (2 * T + 1) := by
    intro η
    set 𝒯 : Finset ℝ := (diffClassValues W j).image (fun u : ℤ => (u : ℝ))
    have hinj : Set.InjOn (fun u : ℤ => (u : ℝ)) (diffClassValues W j) :=
      fun _ _ _ _ h => Int.cast_injective h
    have hcard : 𝒯.card = (diffClassValues W j).card := card_image_of_injOn hinj
    have h𝒯 : ∀ t ∈ 𝒯, -T - 1 ≤ t ∧ t ≤ -T - 1 + (2 * T + 1) := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hu
      exact diffFloor_mem hW (mem_filter.mp hp).1
    have hsep : IsSeparated 1 𝒯 := by
      intro t ht t' ht' hne
      obtain ⟨u, -, rfl⟩ := mem_image.mp ht
      obtain ⟨u', -, rfl⟩ := mem_image.mp ht'
      have hne' : u ≠ u' := fun h => hne (by rw [h])
      rw [← Int.cast_sub, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne')
    have hpair := pairSum_le_of_blockBound hHB (by linarith) hM hS
      (a := fun n => Complex.exp (Complex.I * η * Real.log n))
      (fun n => by rw [norm_exp_mul_log]) h𝒯 hsep
    rw [hcard] at hpair
    refine le_of_eq_of_le ?_ hpair
    rw [sum_image hinj]
    refine sum_congr rfl fun u₁ _ => ?_
    rw [sum_image hinj]
    refine sum_congr rfl fun u₂ _ => ?_
    unfold blockPoly
    congr 2
    refine sum_congr rfl fun n _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j,
        ‖blockPoly S ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2
      ≤ ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j,
          bandMass * Φ (diffFloor p - diffFloor q) :=
        sum_le_sum fun p _ => sum_le_sum fun q _ => hshift p q
    _ = bandMass * ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j,
          Φ (diffFloor p - diffFloor q) := by simp only [mul_sum]
    _ ≤ bandMass * (((2 : ℝ) ^ (j + 1)) ^ 2 *
          ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j, Φ (u₁ - u₂)) :=
        mul_le_mul_of_nonneg_left (sum_sum_diffClassSet_le W j hΦ0) bandMass_nonneg
    _ ≤ bandMass * (((2 : ℝ) ^ (j + 1)) ^ 2 * (3 * Real.pi * bandCauchy * ((2 * K + 2) *
          heathBrownMajorant (diffClassValues W j).card M (2 * T + 1)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          bandMass_nonneg
        -- swap the finite sums with the integral
        have hswap : ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j, Φ (u₁ - u₂) =
            ∫ η, cauchyWeight η * ∑ u₁ ∈ diffClassValues W j, ∑ u₂ ∈ diffClassValues W j,
              ‖blockPoly S ((u₁ - u₂ : ℤ) + η)‖ ^ 2 := by
          simp only [hΦdef, mul_sum]
          rw [integral_finsetSum _ fun u₁ _ => integrable_finsetSum _ fun u₂ _ =>
            integrable_cauchyWeight_mul S _]
          refine sum_congr rfl fun u₁ _ => ?_
          rw [integral_finsetSum _ fun u₂ _ => integrable_cauchyWeight_mul S _]
        rw [hswap, ← integral_cauchyWeight, ← integral_mul_const]
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun η => mul_nonneg (cauchyWeight_nonneg η)
            (sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity))
          (integrable_cauchyWeight.mul_const _) (Filter.Eventually.of_forall fun η => ?_)
        exact mul_le_mul_of_nonneg_left (hHBη η) (cauchyWeight_nonneg η)

/-! ### Step 3: the class bounds `2^j |U_j| ≤ |W|²`, `4^j |U_j| ≤ E(W)` -/

/-- `4^j HB(|U_j|, M, T') ≤ |W|⁴ M + E M² + E^{3/4} |W| T'^{1/2} M`. -/
theorem four_pow_mul_heathBrownMajorant_le (W : Finset ℝ) (j : ℕ) {M T' : ℝ} (hM : 0 ≤ M)
    (hT' : 0 ≤ T') :
    ((2 : ℝ) ^ j) ^ 2 * heathBrownMajorant (diffClassValues W j).card M T' ≤
      (W.card : ℝ) ^ 4 * M + (additiveEnergy W : ℝ) * M ^ 2 +
        (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * T' ^ (1 / 2 : ℝ) * M := by
  set B : ℝ := (2 : ℝ) ^ j
  set X : ℝ := ((diffClassValues W j).card : ℝ)
  set E : ℝ := (additiveEnergy W : ℝ)
  set w : ℝ := (W.card : ℝ)
  have hB : 0 ≤ B := by positivity
  have hX : 0 ≤ X := Nat.cast_nonneg _
  have hE : 0 ≤ E := Nat.cast_nonneg _
  have hw : 0 ≤ w := Nat.cast_nonneg _
  have h1 : B * X ≤ w ^ 2 := by
    have := two_pow_mul_card_diffClassValues_le W j
    simp only [B, X, w]; exact_mod_cast this
  have h2 : B ^ 2 * X ≤ E := by
    have := four_pow_mul_card_diffClassValues_le W j
    simp only [B, X, E]; exact_mod_cast this
  -- the third term: `B² X^{5/4} ≤ E^{3/4} w`, compared through fourth powers
  have h3 : B ^ 2 * X ^ (5 / 4 : ℝ) ≤ E ^ (3 / 4 : ℝ) * w := by
    have hX5 : (X ^ (5 / 4 : ℝ)) ^ 4 = X ^ 5 := by
      rw [rpow_pow_eq_rpow_mul hX, show (5 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hE3 : (E ^ (3 / 4 : ℝ)) ^ 4 = E ^ 3 := by
      rw [rpow_pow_eq_rpow_mul hE, show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hl : (B ^ 2 * X ^ (5 / 4 : ℝ)) ^ 4 = (B ^ 2 * X) ^ 3 * (B * X) ^ 2 := by
      rw [mul_pow, hX5]; ring
    have hr : (E ^ (3 / 4 : ℝ) * w) ^ 4 = E ^ 3 * (w ^ 2) ^ 2 := by
      rw [mul_pow, hE3]; ring
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0), hl, hr]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h2 3)
      (pow_le_pow_left₀ (by positivity) h1 2) (by positivity) (by positivity)
  unfold heathBrownMajorant
  have e1 : B ^ 2 * (X ^ 2 * M) = (B * X) ^ 2 * M := by ring
  have e2 : B ^ 2 * (X * M ^ 2) = (B ^ 2 * X) * M ^ 2 := by ring
  have e3 : B ^ 2 * (X ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M) =
      (B ^ 2 * X ^ (5 / 4 : ℝ)) * T' ^ (1 / 2 : ℝ) * M := by ring
  have hT2 : 0 ≤ T' ^ (1 / 2 : ℝ) * M := by positivity
  have k1 : (B * X) ^ 2 * M ≤ (w ^ 2) ^ 2 * M :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 2) hM
  have k2 : (B ^ 2 * X) * M ^ 2 ≤ E * M ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
  have k3 : (B ^ 2 * X ^ (5 / 4 : ℝ)) * (T' ^ (1 / 2 : ℝ) * M) ≤
      (E ^ (3 / 4 : ℝ) * w) * (T' ^ (1 / 2 : ℝ) * M) := mul_le_mul_of_nonneg_right h3 hT2
  calc B ^ 2 * (X ^ 2 * M + X * M ^ 2 + X ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M)
      = (B * X) ^ 2 * M + (B ^ 2 * X) * M ^ 2 +
          (B ^ 2 * X ^ (5 / 4 : ℝ)) * (T' ^ (1 / 2 : ℝ) * M) := by ring
    _ ≤ (w ^ 2) ^ 2 * M + E * M ^ 2 + (E ^ (3 / 4 : ℝ) * w) * (T' ^ (1 / 2 : ℝ) * M) := by
        linarith
    _ = w ^ 4 * M + E * M ^ 2 + E ^ (3 / 4 : ℝ) * w * T' ^ (1 / 2 : ℝ) * M := by ring

/-! ### Lemma 11.6 -/

/-- The factor of Lemma 11.6 for a per-block constant `K`: `12π ‖K‖₁ bandCauchy (2K + 2)`. -/
def fourthMomentConst (K : ℝ) : ℝ := 12 * Real.pi * bandMass * bandCauchy * (2 * K + 2)

theorem fourthMomentConst_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ fourthMomentConst K := by
  unfold fourthMomentConst
  have := bandMass_nonneg
  have := bandCauchy_nonneg
  positivity

/-- **Lemma 11.6 from a per-block bound.** Under `HeathBrownBlockBound M (2T+1) K`, for every
`W ⊆ [T₀, T₀ + T]` and `S ⊆ (M, 2M+1]`, with `J = ⌊log₂|W|²⌋ + 1`:
`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|⁴ ≤ J² · 12π‖K‖₁ bandCauchy (2K+2) ·
  (|W|⁴ M + E(W) M² + E(W)^{3/4} |W| (2T+1)^{1/2} M)`. -/
theorem sum_lagSum_pow_four_le_of_blockBound {M : ℕ} {T K : ℝ}
    (hHB : HeathBrownBlockBound M (2 * T + 1) K) (hK : 0 ≤ K) (hT : 0 ≤ T) (hM : 1 ≤ M)
    {S : Finset ℕ} (hS : S ⊆ Finset.Ioc M (2 * M + 1)) {W : Finset ℝ} {T₀ : ℝ}
    (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) :
    ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4 ≤
      (diffClassCount W : ℝ) ^ 2 * fourthMomentConst K *
        ((W.card : ℝ) ^ 4 * M + (additiveEnergy W : ℝ) * (M : ℝ) ^ 2 +
          (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * (2 * T + 1) ^ (1 / 2 : ℝ) * M) := by
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => by have := (mem_Ioc.mp (hS hn)).1; omega
  set Q : ℝ := (W.card : ℝ) ^ 4 * M + (additiveEnergy W : ℝ) * (M : ℝ) ^ 2 +
    (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * (2 * T + 1) ^ (1 / 2 : ℝ) * M
  have hclass : ∀ j, ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j,
      ‖blockPoly S ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 ≤ fourthMomentConst K * Q := by
    intro j
    refine (sum_class_le hHB hT hM hS hW j).trans ?_
    have h4 := four_pow_mul_heathBrownMajorant_le W j (M := (M : ℝ)) (T' := 2 * T + 1)
      (Nat.cast_nonneg _) (by linarith)
    have hc : 0 ≤ 12 * Real.pi * bandMass * bandCauchy * (2 * K + 2) := by
      have := bandMass_nonneg; have := bandCauchy_nonneg; positivity
    calc bandMass * (((2 : ℝ) ^ (j + 1)) ^ 2 * (3 * Real.pi * bandCauchy * ((2 * K + 2) *
          heathBrownMajorant (diffClassValues W j).card M (2 * T + 1))))
        = 12 * Real.pi * bandMass * bandCauchy * (2 * K + 2) * (((2 : ℝ) ^ j) ^ 2 *
            heathBrownMajorant (diffClassValues W j).card M (2 * T + 1)) := by ring
      _ ≤ fourthMomentConst K * Q := mul_le_mul_of_nonneg_left h4 hc
  calc ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4
      ≤ diffClassCount W * ∑ j ∈ range (diffClassCount W),
          ∑ p ∈ diffClassSet W j, ∑ q ∈ diffClassSet W j,
            ‖blockPoly S ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 :=
        sum_lagSum_pow_four_le_classes W hpos
    _ ≤ diffClassCount W * ∑ _j ∈ range (diffClassCount W), fourthMomentConst K * Q := by
        gcongr with j
        exact hclass j
    _ = (diffClassCount W : ℝ) ^ 2 * fourthMomentConst K * Q := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **Lemma 11.6 with a `T^ε` per-block constant.** For every `ε > 0` there is `c ≥ 0` such that,
whenever `HeathBrownBlockBound M (2T+1) (C (2T+1)^ε)` holds, for every `1`-separated
`W ⊆ [T₀, T₀ + T]` (`T ≥ 2`) and `S ⊆ (M, 2M+1]`:
`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|⁴ ≤ c (C + 1) T^{2ε} (|W|⁴ M + M² E(W) + E(W)^{3/4} |W| T^{1/2} M)`. -/
theorem sum_lagSum_pow_four_le_of_blockBound_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ c, 0 ≤ c ∧ ∀ (C : ℝ) (W : Finset ℝ) (M : ℕ) (S : Finset ℕ) (T T₀ : ℝ), 0 ≤ C → 2 ≤ T →
      1 ≤ M → S ⊆ Finset.Ioc M (2 * M + 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      IsSeparated 1 W → HeathBrownBlockBound M (2 * T + 1) (C * (2 * T + 1) ^ ε) →
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4 ≤
        c * (C + 1) * T ^ (2 * ε) * ((W.card : ℝ) ^ 4 * M + (M : ℝ) ^ 2 * additiveEnergy W +
          (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * T ^ (1 / 2 : ℝ) * M) := by
  set a : ℝ := 4 / (ε * Real.log 2) + 1
  have ha : 0 ≤ a := by have := Real.log_pos one_lt_two; positivity
  have hbm := bandMass_nonneg
  have hbc := bandCauchy_nonneg
  set c : ℝ := a ^ 2 * (2 : ℝ) ^ ε * (12 * Real.pi * bandMass * bandCauchy) *
    (4 * (3 : ℝ) ^ ε) * 2
  refine ⟨c, by positivity, fun C W M S T T₀ hC hT hM hS hW hsep hHB => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hK0 : 0 ≤ C * (2 * T + 1) ^ ε := by positivity
  have h := sum_lagSum_pow_four_le_of_blockBound hHB hK0 hT0 hM hS hW
  -- the number of classes
  have hJ : (diffClassCount W : ℝ) ≤ a * (2 * T) ^ (ε / 2) := by
    have hcard := card_le_of_isSeparated_of_mem hT0 hW hsep
    have hK : ((W.card ^ 2 : ℕ) : ℝ) ≤ (2 * T) ^ 2 := by
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
    have := natLog_add_one_le hε (by linarith : (1 : ℝ) ≤ 2 * T) hK
    unfold diffClassCount
    push_cast
    exact this
  have hJ2 : (diffClassCount W : ℝ) ^ 2 ≤ a ^ 2 * (2 : ℝ) ^ ε * T ^ ε := by
    have h2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ 2
    have e : (a * (2 * T) ^ (ε / 2)) ^ 2 = a ^ 2 * (2 : ℝ) ^ ε * T ^ ε := by
      rw [mul_pow, rpow_pow_eq_rpow_mul (by positivity), Real.mul_rpow (by norm_num) hT0]
      push_cast; ring_nf
    rwa [e] at h2
  -- the per-block factor
  have hF : fourthMomentConst (C * (2 * T + 1) ^ ε) ≤
      12 * Real.pi * bandMass * bandCauchy * (4 * (3 : ℝ) ^ ε) * (C + 1) * T ^ ε := by
    unfold fourthMomentConst
    have h3 : (2 * T + 1) ^ ε ≤ (3 : ℝ) ^ ε * T ^ ε := by
      rw [← Real.mul_rpow (by norm_num) hT0]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
    have h31 : (1 : ℝ) ≤ (3 : ℝ) ^ ε := Real.one_le_rpow (by norm_num) hε.le
    have hk : 2 * (C * (2 * T + 1) ^ ε) + 2 ≤ 4 * (3 : ℝ) ^ ε * (C + 1) * T ^ ε := by
      have : C * (2 * T + 1) ^ ε ≤ C * ((3 : ℝ) ^ ε * T ^ ε) := mul_le_mul_of_nonneg_left h3 hC
      have : (1 : ℝ) ≤ (3 : ℝ) ^ ε * T ^ ε := one_le_mul_of_one_le_of_one_le h31 hTε
      nlinarith
    have hp : 0 ≤ 12 * Real.pi * bandMass * bandCauchy := by positivity
    calc 12 * Real.pi * bandMass * bandCauchy * (2 * (C * (2 * T + 1) ^ ε) + 2)
        ≤ 12 * Real.pi * bandMass * bandCauchy * (4 * (3 : ℝ) ^ ε * (C + 1) * T ^ ε) :=
          mul_le_mul_of_nonneg_left hk hp
      _ = _ := by ring
  -- `(2T+1)^{1/2} ≤ 2 T^{1/2}`
  have hsq : (2 * T + 1) ^ (1 / 2 : ℝ) ≤ 2 * T ^ (1 / 2 : ℝ) := by
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    calc (2 * T + 1) ^ (1 / 2 : ℝ) ≤ (4 * T) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = 2 * T ^ (1 / 2 : ℝ) := by rw [Real.mul_rpow (by norm_num) hT0, h4]
  set Q : ℝ := (W.card : ℝ) ^ 4 * M + (M : ℝ) ^ 2 * additiveEnergy W +
    (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * T ^ (1 / 2 : ℝ) * M
  have hQ : (W.card : ℝ) ^ 4 * M + (additiveEnergy W : ℝ) * (M : ℝ) ^ 2 +
      (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * (2 * T + 1) ^ (1 / 2 : ℝ) * M ≤ 2 * Q := by
    have h0 : 0 ≤ (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * M := by positivity
    have := mul_le_mul_of_nonneg_left hsq h0
    have : 0 ≤ (W.card : ℝ) ^ 4 * M + (M : ℝ) ^ 2 * additiveEnergy W := by positivity
    simp only [Q]
    nlinarith
  have hFn := fourthMomentConst_nonneg hK0
  have hQ0 : 0 ≤ (W.card : ℝ) ^ 4 * M + (additiveEnergy W : ℝ) * (M : ℝ) ^ 2 +
      (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * (2 * T + 1) ^ (1 / 2 : ℝ) * M := by
    positivity
  have hTT : T ^ ε * T ^ ε = T ^ (2 * ε) := by rw [← Real.rpow_add (by linarith)]; ring_nf
  calc ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4
      ≤ (a ^ 2 * (2 : ℝ) ^ ε * T ^ ε) *
          (12 * Real.pi * bandMass * bandCauchy * (4 * (3 : ℝ) ^ ε) * (C + 1) * T ^ ε) * (2 * Q) := by
        refine h.trans ?_
        gcongr
    _ = c * (C + 1) * (T ^ ε * T ^ ε) * Q := by simp only [c]; ring
    _ = c * (C + 1) * T ^ (2 * ε) * Q := by rw [hTT]

/-- **Guth–Maynard Lemma 11.6**, for every block length (assembly over `HeathBrownPairSumBound`):
for every `ε > 0` there is `C ≥ 0` such that for every `1`-separated `W ⊆ [T₀, T₀ + T]`
(`T ≥ 2`), every `M ≥ 1` and every `S ⊆ (M, 2M+1]` (in particular `S = (M, 2M]`),
`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|⁴ ≤ C T^ε (|W|⁴ M + M² E(W) + E(W)^{3/4} |W| T^{1/2} M)`. -/
theorem guthMaynard_lemma116 (hHB : HeathBrownPairSumBound) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (W : Finset ℝ) (M : ℕ) (S : Finset ℕ) (T T₀ : ℝ),
      2 ≤ T → 1 ≤ M → S ⊆ Finset.Ioc M (2 * M + 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      IsSeparated 1 W →
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4 ≤
        C * T ^ ε * ((W.card : ℝ) ^ 4 * M + (M : ℝ) ^ 2 * additiveEnergy W +
          (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * T ^ (1 / 2 : ℝ) * M) := by
  obtain ⟨c, hc, hmain⟩ := sum_lagSum_pow_four_le_of_blockBound_rpow (ε := ε / 2) (by positivity)
  obtain ⟨C, hC, hblock⟩ := hHB.blockBound (ε := ε / 2) (by positivity)
  refine ⟨c * (C + 1), by positivity, fun W M S T T₀ hT hM hS hW hsep => ?_⟩
  have h := hmain C W M S T T₀ hC hT hM hS hW hsep (hblock M (2 * T + 1) (by linarith) hM)
  rwa [show 2 * (ε / 2) = ε by ring] at h

/-- **Guth–Maynard Lemma 11.6 for blocks `M ≤ T^{1/4}`, unconditionally** (Heath-Brown's theorem
for short blocks): for every `ε > 0` there is `C ≥ 0` such that for every `1`-separated
`W ⊆ [T₀, T₀ + T]` (`T ≥ 2`), `1 ≤ M ≤ T^{1/4}` and `S ⊆ (M, 2M+1]`,
`Σ_{n₁,n₂ ∈ S} |R(n₁/n₂)|⁴ ≤ C T^ε (|W|⁴ M + M² E(W) + E(W)^{3/4} |W| T^{1/2} M)`. -/
theorem guthMaynard_lemma116_short {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (W : Finset ℝ) (M : ℕ) (S : Finset ℕ) (T T₀ : ℝ),
      2 ≤ T → 1 ≤ M → (M : ℝ) ≤ T ^ (1 / 4 : ℝ) → S ⊆ Finset.Ioc M (2 * M + 1) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W →
      ∑ n₁ ∈ S, ∑ n₂ ∈ S, ‖lagSum W ((n₁ : ℝ) / n₂)‖ ^ 4 ≤
        C * T ^ ε * ((W.card : ℝ) ^ 4 * M + (M : ℝ) ^ 2 * additiveEnergy W +
          (additiveEnergy W : ℝ) ^ (3 / 4 : ℝ) * W.card * T ^ (1 / 2 : ℝ) * M) := by
  obtain ⟨c, hc, hmain⟩ := sum_lagSum_pow_four_le_of_blockBound_rpow (ε := ε / 2) (by positivity)
  obtain ⟨C, hC, hblock⟩ := exists_heathBrownBlockBound_short (ε := ε / 2) (by positivity)
  refine ⟨c * (C + 1), by positivity, fun W M S T T₀ hT hM hMT hS hW hsep => ?_⟩
  have hMT' : (M : ℝ) ≤ (2 * T + 1) ^ (1 / 4 : ℝ) :=
    hMT.trans (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num))
  have h := hmain C W M S T T₀ hC hT hM hS hW hsep (hblock M (2 * T + 1) (by linarith) hM hMT')
  rwa [show 2 * (ε / 2) = ε by ring] at h

end

end RHTower.GuthMaynard
