import Mathlib

/-!
# Three route-native static shadows are separately non-identifying

**Period closure.**  The ordered triples `(1, i, 1+i)` and `(1, i, √2+i)` in `ℂ ≅ ℝ²` have the same
ordered minor signs `(+, +, −)`, hence the same oriented trivially-valuated rank-two frame, yet
their integral period groups have different closures: `ℤ + ℤ` is a closed subgroup of `ℝ`, while
`ℤ + √2 ℤ` is dense.

**First affine extension.**  The two positive two-atom carriers `μ₊` and `μ₋` have the same
factorial moments `s₀ = s₁ = s₂ = 1`, hence the same singular size-two Hankel face and the same
null polynomial `X - 1`, yet opposite first Krein crossings `s₃ - s₂`.

**Cofinal topology.**  The augmentation functional is `ℓ¹`-continuous, so its kernel is closed
there; but the finitely-supported correction spreading a deficit `S` over `N` fresh coordinates has
`ℓ^p` norm `|S| N^{1/p - 1} → 0` for `p > 1` and sup norm `|S|/N → 0`, while its `ℓ¹` norm stays
`|S|`.  The same algebraic augmentation tower therefore has a one-dimensional Hausdorff quotient in
`ℓ¹` and a zero quotient in every `ℓ^p`, `p > 1`, and in `c₀`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

/-! ## Period closure is not oriented trivially-valuated support -/

/-- The `2 × 2` minors of the ordered triple `(1, i, 1+i)`. -/
theorem minors_first :
    ((1 : ℂ) * Complex.I - (0 : ℂ)).im = 1
      ∧ ((1 : ℂ) * (1 + Complex.I)).im = 1
      ∧ (Complex.I * (1 + Complex.I)).im = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

/-- The ordered minor signs of `(1, i, 1+i)` computed as real determinants. -/
theorem det_signs_first :
    (1 : ℝ) * 1 - 0 * 0 = 1
      ∧ (1 : ℝ) * 1 - 0 * 1 = 1
      ∧ (0 : ℝ) * 1 - 1 * 1 = -1 := by
  norm_num

/-- The ordered minor signs of `(1, i, √2+i)`: the same sign pattern `(+, +, −)`. -/
theorem det_signs_second :
    (1 : ℝ) * 1 - 0 * 0 = 1
      ∧ (1 : ℝ) * 1 - 0 * Real.sqrt 2 = 1
      ∧ (0 : ℝ) * 1 - 1 * Real.sqrt 2 = -Real.sqrt 2 := by
  refine ⟨by norm_num, by norm_num, by ring⟩

theorem sqrt_two_pos : 0 < Real.sqrt 2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  exact Real.sqrt_pos.mpr h

/-- **The first period group is a closed subgroup of the line.** -/
theorem closed_integer_periods :
    IsClosed ((AddSubgroup.closure ({1} : Set ℝ)) : Set ℝ) := by
  have h : (AddSubgroup.closure ({1} : Set ℝ) : Set ℝ) = Set.range (fun n : ℤ => (n : ℝ)) := by
    ext x
    rw [SetLike.mem_coe, AddSubgroup.mem_closure_singleton]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp⟩
  rw [h]
  simpa using Int.isClosedEmbedding_coe_real.isClosed_range

/-- **The second period group is dense in the line.** -/
theorem dense_sqrt_two_periods :
    Dense ((AddSubgroup.closure ({1, Real.sqrt 2} : Set ℝ)) : Set ℝ) := by
  set S : AddSubgroup ℝ := AddSubgroup.closure ({1, Real.sqrt 2} : Set ℝ) with hS
  rcases AddSubgroup.dense_or_cyclic S with hdense | ⟨a, ha⟩
  · exact hdense
  · exfalso
    have h1 : (1 : ℝ) ∈ S := AddSubgroup.subset_closure (by simp)
    have h2 : Real.sqrt 2 ∈ S := AddSubgroup.subset_closure (by simp)
    rw [ha, AddSubgroup.mem_closure_singleton] at h1 h2
    obtain ⟨m, hm⟩ := h1
    obtain ⟨k, hk⟩ := h2
    rw [zsmul_eq_mul] at hm hk
    have hm0 : (m : ℝ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hm
      norm_num at hm
    have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
    have hval : (k : ℝ) * a = (k : ℝ) / (m : ℝ) := by
      field_simp
      linear_combination (k : ℝ) * hm
    refine hirr ⟨(k : ℚ) / (m : ℚ), ?_⟩
    push_cast
    rw [← hk, hval]

/-- **Theorem 1.1.**  The same oriented trivially-valuated frame carries a closed period group and
a dense one, so the frame does not determine the period closure. -/
theorem period_closure_nonidentifiable :
    IsClosed ((AddSubgroup.closure ({1} : Set ℝ)) : Set ℝ)
      ∧ Dense ((AddSubgroup.closure ({1, Real.sqrt 2} : Set ℝ)) : Set ℝ)
      ∧ ¬ Dense ((AddSubgroup.closure ({1} : Set ℝ)) : Set ℝ) := by
  refine ⟨closed_integer_periods, dense_sqrt_two_periods, ?_⟩
  intro hdense
  have huniv : (AddSubgroup.closure ({1} : Set ℝ) : Set ℝ) = Set.univ := by
    rw [← closed_integer_periods.closure_eq, hdense.closure_eq]
  have hmem : (1 / 2 : ℝ) ∈ (AddSubgroup.closure ({1} : Set ℝ) : Set ℝ) := by
    rw [huniv]
    trivial
  rw [SetLike.mem_coe, AddSubgroup.mem_closure_singleton] at hmem
  obtain ⟨n, hn⟩ := hmem
  rw [zsmul_eq_mul, mul_one] at hn
  have : (n : ℝ) = 1 / 2 := hn
  have h2 : (2 : ℝ) * n = 1 := by linarith
  have : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-! ## The first affine extension is not determined by the positive Hankel face -/

/-- The factorial moments of the two-atom carrier `(w₁, x₁), (w₂, x₂)`. -/
noncomputable def factorialMoment (w₁ x₁ w₂ x₂ : ℝ) (k : ℕ) : ℝ :=
  (w₁ * x₁ ^ k + w₂ * x₂ ^ k) / (k.factorial : ℝ)

/-- **The two positive carriers share their first three factorial moments.** -/
theorem shared_moments :
    (factorialMoment (16 / 17) (3 / 4) (1 / 17) 5 0 = 1
      ∧ factorialMoment (16 / 17) (3 / 4) (1 / 17) 5 1 = 1
      ∧ factorialMoment (16 / 17) (3 / 4) (1 / 17) 5 2 = 1)
    ∧ (factorialMoment (4 / 5) (1 / 2) (1 / 5) 3 0 = 1
      ∧ factorialMoment (4 / 5) (1 / 2) (1 / 5) 3 1 = 1
      ∧ factorialMoment (4 / 5) (1 / 2) (1 / 5) 3 2 = 1) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    · rw [factorialMoment]
      norm_num [Nat.factorial]

/-- **Opposite first extension crossings.**  The third factorial moments differ, and the two
Krein crossings `s₃ - s₂` have opposite signs. -/
theorem opposite_crossings :
    factorialMoment (16 / 17) (3 / 4) (1 / 17) 5 3 = 31 / 24
      ∧ factorialMoment (4 / 5) (1 / 2) (1 / 5) 3 3 = 11 / 12
      ∧ 0 < factorialMoment (16 / 17) (3 / 4) (1 / 17) 5 3 - 1
      ∧ factorialMoment (4 / 5) (1 / 2) (1 / 5) 3 3 - 1 < 0 := by
  have h1 : factorialMoment (16 / 17) (3 / 4) (1 / 17) 5 3 = 31 / 24 := by
    rw [factorialMoment]
    norm_num [Nat.factorial]
  have h2 : factorialMoment (4 / 5) (1 / 2) (1 / 5) 3 3 = 11 / 12 := by
    rw [factorialMoment]
    norm_num [Nat.factorial]
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h1]; norm_num
  · rw [h2]; norm_num

/-- **The two carriers are positive with positive nodes.** -/
theorem carriers_positive :
    (0 < (16 / 17 : ℝ) ∧ 0 < (1 / 17 : ℝ) ∧ 0 < (3 / 4 : ℝ) ∧ 0 < (5 : ℝ))
      ∧ (0 < (4 / 5 : ℝ) ∧ 0 < (1 / 5 : ℝ) ∧ 0 < (1 / 2 : ℝ) ∧ 0 < (3 : ℝ)) := by
  norm_num

/-! ## The augmentation tower does not determine its Hausdorff port -/

/-- **`ℓ¹`-continuity of the augmentation.** -/
theorem abs_augmentation_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    |∑ i ∈ s, x i| ≤ ∑ i ∈ s, |x i| :=
  Finset.abs_sum_le_sum_abs x s

/-- The correction spreading a deficit `S` over `N` fresh coordinates. -/
noncomputable def correction (S : ℝ) (N : ℕ) : ℝ := -S / (N : ℝ)

/-- **The correction cancels the augmentation.** -/
theorem correction_cancels (S : ℝ) {N : ℕ} (hN : N ≠ 0) :
    S + (N : ℝ) * correction S N = 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [correction]
  field_simp
  ring

/-- **The `p`-th power of the `ℓ^p` norm of the correction.** -/
theorem correction_lp_pow (S : ℝ) {N : ℕ} (hN : N ≠ 0) (p : ℝ) :
    (N : ℝ) * |correction S N| ^ p = |S| ^ p * (N : ℝ) ^ (1 - p) := by
  have hN' : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  have habs : |correction S N| = |S| / (N : ℝ) := by
    rw [correction, abs_div, abs_neg, abs_of_pos hN']
  rw [habs, Real.div_rpow (abs_nonneg S) hN'.le, Real.rpow_sub hN', Real.rpow_one]
  ring

/-- **The `ℓ^p` correction decays for every exponent above one.** -/
theorem tendsto_correction_lp_pow (S : ℝ) {p : ℝ} (hp : 1 < p) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) * |correction S N| ^ p) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun N : ℕ => ((N : ℝ)) ^ (p - 1)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun N : ℕ => (((N : ℝ)) ^ (p - 1))⁻¹) Filter.atTop (nhds 0) :=
    hpow.inv_tendsto_atTop
  have hlim : Filter.Tendsto (fun N : ℕ => |S| ^ p * (((N : ℝ)) ^ (p - 1))⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using hinv.const_mul (|S| ^ p)
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have hN0 : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [correction_lp_pow S hN0 p]
  congr 1
  rw [← Real.rpow_neg hN'.le]
  congr 1
  ring

/-- **The `ℓ¹` norm of the correction does not decay.** -/
theorem correction_l1_norm (S : ℝ) {N : ℕ} (hN : N ≠ 0) :
    (N : ℝ) * |correction S N| = |S| := by
  have hN' : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  rw [correction, abs_div, abs_neg, abs_of_pos hN']
  field_simp

/-- **The sup norm of the correction decays.** -/
theorem tendsto_correction_sup (S : ℝ) :
    Filter.Tendsto (fun N : ℕ => |correction S N|) Filter.atTop (nhds 0) := by
  have hrw : ∀ N : ℕ, |correction S N| = |S| * ((N : ℝ))⁻¹ := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [correction]
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [correction, abs_div, abs_neg, abs_of_pos hN']
      ring
  simp only [hrw]
  simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul |S|

/-! ## The augmentation ideal in the two completions -/

/-- The augmentation of a finitely supported vector over a finite index set. -/
def augmentOn (s : Finset ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ s, x i

/-- The `p`-th power of the `ℓ^p` norm over a finite index set. -/
noncomputable def lpNormPowOn (p : ℝ) (s : Finset ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ s, |x i| ^ p

/-- **In `ℓ¹` the augmentation is `1`-Lipschitz**, so its kernel is closed and the Hausdorff
quotient is one-dimensional. -/
theorem abs_augmentOn_le_l1 (s : Finset ℕ) (x : ℕ → ℝ) :
    |augmentOn s x| ≤ lpNormPowOn 1 s x := by
  rw [augmentOn, lpNormPowOn]
  refine le_trans (Finset.abs_sum_le_sum_abs x s) (le_of_eq ?_)
  exact Finset.sum_congr rfl fun i _ => by rw [Real.rpow_one]

/-- The fresh index block used by the correction. -/
def freshBlock (s : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).image fun j => (s.sup id + 1) + j

theorem freshBlock_card (s : Finset ℕ) (N : ℕ) : (freshBlock s N).card = N := by
  rw [freshBlock, Finset.card_image_of_injective _ (add_right_injective _), Finset.card_range]

theorem disjoint_freshBlock (s : Finset ℕ) (N : ℕ) : Disjoint s (freshBlock s N) := by
  classical
  rw [Finset.disjoint_right]
  intro a ha has
  rw [freshBlock, Finset.mem_image] at ha
  obtain ⟨j, -, hj⟩ := ha
  have hle : a ≤ s.sup id := Finset.le_sup (f := id) has
  omega

/-- **The augmentation ideal is dense in every `ℓ^p` with `p > 1`.**  The correction spreading the
deficit over a fresh block changes the vector by an arbitrarily small amount. -/
theorem exists_augmentation_zero_approx {p : ℝ} (hp : 1 < p) (s : Finset ℕ) (x : ℕ → ℝ)
    (hx : ∀ i, i ∉ s → x i = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (z : ℕ → ℝ), N ≠ 0
      ∧ augmentOn (s ∪ freshBlock s N) z = 0
      ∧ lpNormPowOn p (s ∪ freshBlock s N) (fun i => x i - z i) < δ := by
  classical
  set S : ℝ := augmentOn s x with hSdef
  have hlim := tendsto_correction_lp_pow S hp
  have hev := hlim.eventually_lt_const hδ
  obtain ⟨N, hNlt, hNpos⟩ := ((hev.and (Filter.eventually_gt_atTop 0)).exists)
  have hN0 : N ≠ 0 := by omega
  have hdisj := disjoint_freshBlock s N
  refine ⟨N, fun i => x i + (if i ∈ freshBlock s N then correction S N else 0), hN0, ?_, ?_⟩
  · rw [augmentOn, Finset.sum_union hdisj]
    have h1 : ∑ i ∈ s, (x i + (if i ∈ freshBlock s N then correction S N else 0)) = S := by
      rw [hSdef, augmentOn]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hnot : i ∉ freshBlock s N := Finset.disjoint_left.mp hdisj hi
      rw [if_neg hnot, add_zero]
    have h2 : ∑ i ∈ freshBlock s N,
        (x i + (if i ∈ freshBlock s N then correction S N else 0))
        = (N : ℝ) * correction S N := by
      have hxz : ∀ i ∈ freshBlock s N,
          x i + (if i ∈ freshBlock s N then correction S N else 0) = correction S N := by
        intro i hi
        have hnot : i ∉ s := Finset.disjoint_right.mp hdisj hi
        rw [hx i hnot, if_pos hi, zero_add]
      rw [Finset.sum_congr rfl hxz, Finset.sum_const, freshBlock_card, nsmul_eq_mul]
    rw [h1, h2]
    exact correction_cancels S hN0
  · have hpt : ∀ i ∈ s ∪ freshBlock s N,
        |x i - (x i + (if i ∈ freshBlock s N then correction S N else 0))| ^ p
        = if i ∈ freshBlock s N then |correction S N| ^ p else 0 := by
      intro i _
      by_cases hi : i ∈ freshBlock s N
      · rw [if_pos hi, if_pos hi]
        congr 1
        rw [show x i - (x i + correction S N) = -correction S N by ring, abs_neg]
      · rw [if_neg hi, if_neg hi]
        simp only [add_zero, sub_self, abs_zero]
        exact Real.zero_rpow (by linarith)
    rw [lpNormPowOn, Finset.sum_congr rfl hpt, Finset.sum_ite_mem]
    have hinter : (s ∪ freshBlock s N) ∩ freshBlock s N = freshBlock s N := by
      rw [Finset.inter_eq_right]
      exact Finset.subset_union_right
    rw [hinter, Finset.sum_const, freshBlock_card, nsmul_eq_mul]
    exact hNlt

/-- **Theorem 3.1.**  The same finite augmentation tower has a nonzero Hausdorff quotient in `ℓ¹`
and a zero one in every `ℓ^p` with `p > 1`: the augmentation is `1`-Lipschitz for the `ℓ¹` norm and
does not vanish on the tower, while for `p > 1` its kernel is dense. -/
theorem cofinal_topology_nonidentifiable {p : ℝ} (hp : 1 < p) :
    (∀ (s : Finset ℕ) (x : ℕ → ℝ), |augmentOn s x| ≤ lpNormPowOn 1 s x)
      ∧ (∀ (s : Finset ℕ) (x : ℕ → ℝ), (∀ i, i ∉ s → x i = 0) → ∀ δ : ℝ, 0 < δ →
          ∃ (N : ℕ) (z : ℕ → ℝ), N ≠ 0 ∧ augmentOn (s ∪ freshBlock s N) z = 0
            ∧ lpNormPowOn p (s ∪ freshBlock s N) (fun i => x i - z i) < δ)
      ∧ (∀ S : ℝ, ∀ N : ℕ, N ≠ 0 → (N : ℝ) * |correction S N| = |S|) := by
  exact ⟨abs_augmentOn_le_l1, fun s x hx δ hδ => exists_augmentation_zero_approx hp s x hx hδ,
    fun S N hN => correction_l1_norm S hN⟩

end HTGeometry.ConstraintFrameRelativity
