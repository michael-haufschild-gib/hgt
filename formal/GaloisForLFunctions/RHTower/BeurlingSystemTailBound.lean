import GaloisForLFunctions.RHTower.BeurlingSystemDecomposition

/-!
# The exponential tail of a Beurling system above a threshold

The two-sided counting law bounds the number of generalized integers in every window of width
`1/x`, and on such a window the exponential weight is almost constant.  Summing the window bounds
against the geometric weights gives the tail estimate `(BF15)`

```text
∑_{|g| > T} e^{-x|g|} ≪ e^{-xT} (x^{-1} + T^θ).
```
-/

open scoped BigOperators

namespace RHTower

namespace BeurlingSystem

variable (B : BeurlingSystem)

/-- The two-sided counting law `(BF1)`. -/
def HasCountingError (κ C θ : ℝ) : Prop :=
  ∀ X : ℝ, 1 ≤ X → |(B.countBall X : ℝ) - κ * X| ≤ C * X ^ θ

/-- The window index of a generalized integer above the threshold. -/
noncomputable def layerIndex (T x : ℝ) (g : Multiset B.Label) : ℕ :=
  ⌈(B.intNorm g - T) * x⌉₊ - 1

variable {B}

/-! ## Elementary bounds -/

theorem rpow_add_le_of_one_le {T s θ : ℝ} (hT : 1 ≤ T) (hs : 0 ≤ s) (hθ1 : θ ≤ 1) :
    (T + s) ^ θ ≤ T ^ θ + s := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hfac : T + s = T * (1 + s / T) := by
    field_simp
  have hone : (1 : ℝ) ≤ 1 + s / T := by
    have : 0 ≤ s / T := by positivity
    linarith
  have hpow : (1 + s / T) ^ θ ≤ 1 + s / T := by
    calc (1 + s / T) ^ θ ≤ (1 + s / T) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hone hθ1
      _ = 1 + s / T := Real.rpow_one _
  have hTpow : (0 : ℝ) < T ^ θ := Real.rpow_pos_of_pos hT0 _
  have hTsub : T ^ θ * (s / T) ≤ s := by
    have hTθ : T ^ θ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT hθ1
    rw [Real.rpow_one] at hTθ
    have hsT : 0 ≤ s / T := by positivity
    nlinarith
  calc (T + s) ^ θ = T ^ θ * (1 + s / T) ^ θ := by
        rw [hfac, Real.mul_rpow hT0.le (by linarith)]
    _ ≤ T ^ θ * (1 + s / T) := by
        exact mul_le_mul_of_nonneg_left hpow hTpow.le
    _ = T ^ θ + T ^ θ * (s / T) := by ring
    _ ≤ T ^ θ + s := by linarith

theorem countBall_sub_le {κ C θ : ℝ} (hN : B.HasCountingError κ C θ) {a b : ℝ} (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ((B.countBall b : ℝ) - (B.countBall a : ℝ)) ≤ κ * (b - a) + C * (b ^ θ + a ^ θ) := by
  have h1 := abs_le.mp (hN b (le_trans ha hab))
  have h2 := abs_le.mp (hN a ha)
  linarith [h1.2, h2.1]

/-! ## The geometric constants -/

theorem summable_expNegNat : Summable fun j : ℕ => Real.exp (-(j : ℝ)) := by
  have hrw : ∀ j : ℕ, Real.exp (-(j : ℝ)) = Real.exp (-1) ^ j := by
    intro j
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine (summable_geometric_of_lt_one (Real.exp_pos _).le ?_).congr fun j => (hrw j).symm
  exact Real.exp_lt_one_iff.mpr (by norm_num)

theorem summable_expNegNat_lin : Summable fun j : ℕ => ((j : ℝ) + 1) * Real.exp (-(j : ℝ)) := by
  have hrw : ∀ j : ℕ, ((j : ℝ) + 1) * Real.exp (-(j : ℝ)) = ((j : ℝ) + 1) * Real.exp (-1) ^ j := by
    intro j
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  have hexp1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hexp0 : (0 : ℝ) ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hr1 : ‖Real.exp (-1)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hexp1
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr1
  have h2 : Summable fun j : ℕ => ((j : ℝ) + 1) * Real.exp (-1) ^ j := by
    refine (h.add (summable_geometric_of_lt_one hexp0 hexp1)).congr fun j => ?_
    simp only [pow_one]
    ring
  exact h2.congr fun j => (hrw j).symm

/-- The geometric constant `∑ e^{-j}`. -/
noncomputable def expGeomSum : ℝ := ∑' j : ℕ, Real.exp (-(j : ℝ))

/-- The linear geometric constant `∑ (j+1) e^{-j}`. -/
noncomputable def expGeomLinSum : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) * Real.exp (-(j : ℝ))

theorem expGeomSum_nonneg : 0 ≤ expGeomSum :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

theorem expGeomLinSum_nonneg : 0 ≤ expGeomLinSum :=
  tsum_nonneg fun _ => by positivity

/-! ## The window containment -/

theorem layerIndex_bounds {T x : ℝ} (hx : 0 < x) {g : Multiset B.Label} (hg : T < B.intNorm g) :
    T + (B.layerIndex T x g : ℝ) / x < B.intNorm g ∧
      B.intNorm g ≤ T + ((B.layerIndex T x g : ℝ) + 1) / x := by
  set y : ℝ := (B.intNorm g - T) * x with hy
  have hy0 : 0 < y := by
    rw [hy]
    exact mul_pos (by linarith) hx
  have hceil : 1 ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro hzero
    have hle := Nat.le_ceil y
    rw [hzero] at hle
    simp at hle
    linarith)
  have hidx : B.layerIndex T x g = ⌈y⌉₊ - 1 := rfl
  have hlt : ((B.layerIndex T x g : ℕ) : ℝ) < y := by
    refine Nat.lt_ceil.mp ?_
    rw [hidx]
    omega
  have hle : y ≤ ((B.layerIndex T x g : ℕ) : ℝ) + 1 := by
    have hceil_le := Nat.le_ceil y
    have hcast : (⌈y⌉₊ : ℝ) = ((B.layerIndex T x g : ℕ) : ℝ) + 1 := by
      rw [hidx]
      have hsucc : (⌈y⌉₊ - 1) + 1 = ⌈y⌉₊ := by omega
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsucc.symm
    rw [hcast] at hceil_le
    exact hceil_le
  refine ⟨?_, ?_⟩
  · have hxx : (B.layerIndex T x g : ℝ) / x < B.intNorm g - T := by
      rw [div_lt_iff₀ hx]
      rw [hy] at hlt
      linarith
    linarith
  · have hxx : B.intNorm g - T ≤ ((B.layerIndex T x g : ℝ) + 1) / x := by
      rw [le_div_iff₀ hx]
      rw [hy] at hle
      linarith
    linarith


/-! ## The tail estimate -/

theorem card_layer_le (hdisc : B.IsDiscrete) {x T : ℝ} (hx : 0 < x) (j : ℕ)
    (S : Finset (Multiset B.Label)) :
    (((S.filter fun g => T < B.intNorm g).filter fun g => B.layerIndex T x g = j).card : ℝ)
      ≤ (B.countBall (T + ((j : ℝ) + 1) / x) : ℝ) - (B.countBall (T + (j : ℝ) / x) : ℝ) := by
  classical
  set a : ℝ := T + (j : ℝ) / x with ha
  set b : ℝ := T + ((j : ℝ) + 1) / x with hb
  have hab : a ≤ b := by
    have hj : (j : ℝ) / x ≤ ((j : ℝ) + 1) / x := by
      gcongr
      linarith
    rw [ha, hb]
    linarith
  have hfa := hdisc a
  have hfb := hdisc b
  have hballsub : hfa.toFinset ⊆ hfb.toFinset := by
    intro g hg
    rw [Set.Finite.mem_toFinset] at hg ⊢
    exact le_trans hg hab
  have hsubF : ((S.filter fun g => T < B.intNorm g).filter fun g => B.layerIndex T x g = j)
      ⊆ hfb.toFinset \ hfa.toFinset := by
    intro g hg
    rw [Finset.mem_filter, Finset.mem_filter] at hg
    obtain ⟨⟨-, hgT⟩, hgj⟩ := hg
    obtain ⟨hlow, hhigh⟩ := layerIndex_bounds hx hgT
    rw [hgj] at hlow hhigh
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact ⟨hhigh, not_le.mpr hlow⟩
  have hcards := Finset.card_le_card hsubF
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hballsub] at hcards
  have hca : hfa.toFinset.card = B.countBall a := by
    rw [countBall, Set.ncard_eq_toFinset_card _ hfa]
  have hcb : hfb.toFinset.card = B.countBall b := by
    rw [countBall, Set.ncard_eq_toFinset_card _ hfb]
  rw [hca, hcb] at hcards
  have hmono : B.countBall a ≤ B.countBall b := countBall_mono hdisc hab
  calc (((S.filter fun g => T < B.intNorm g).filter fun g => B.layerIndex T x g = j).card : ℝ)
      ≤ ((B.countBall b - B.countBall a : ℕ) : ℝ) := by exact_mod_cast hcards
    _ = (B.countBall b : ℝ) - (B.countBall a : ℝ) := by
        rw [Nat.cast_sub hmono]


/-- **The tail estimate `(BF15)`.**  Above the threshold the exponential Gibbs mass is controlled
by the counting error and the geometric window weights. -/
theorem tsum_tail_le (hdisc : B.IsDiscrete) {κ C θ : ℝ} (hN : B.HasCountingError κ C θ)
    (hκ : 0 ≤ κ) (hC0 : 0 ≤ C) (hθ1 : θ ≤ 1) {x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    ∑' g : Multiset B.Label, (if T < B.intNorm g then Real.exp (-x * B.intNorm g) else 0)
      ≤ Real.exp (-x * T) *
          ((κ / x + 2 * C * T ^ θ) * expGeomSum + (2 * C / x) * expGeomLinSum) := by
  classical
  set E : ℝ := Real.exp (-x * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set F : ℕ → ℝ := fun j =>
    E * ((κ / x + 2 * C * T ^ θ) * Real.exp (-(j : ℝ))
      + (2 * C / x) * (((j : ℝ) + 1) * Real.exp (-(j : ℝ)))) with hF
  have hTpow : (0 : ℝ) ≤ T ^ θ :=
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) θ).le
  have hFsummable : Summable F := by
    rw [hF]
    exact ((summable_expNegNat.mul_left _).add (summable_expNegNat_lin.mul_left _)).mul_left _
  have hFnonneg : ∀ j : ℕ, 0 ≤ F j := by
    intro j
    have h1 : 0 ≤ κ / x := by positivity
    have h2 : 0 ≤ 2 * C * T ^ θ := by positivity
    have h3 : 0 ≤ 2 * C / x := by positivity
    have h4 : 0 < Real.exp (-(j : ℝ)) := Real.exp_pos _
    have h5 : (0 : ℝ) ≤ ((j : ℝ) + 1) := by positivity
    rw [hF]
    have : 0 ≤ (κ / x + 2 * C * T ^ θ) * Real.exp (-(j : ℝ))
        + (2 * C / x) * (((j : ℝ) + 1) * Real.exp (-(j : ℝ))) := by
      have hx1 : 0 ≤ (κ / x + 2 * C * T ^ θ) * Real.exp (-(j : ℝ)) := by positivity
      have hx2 : 0 ≤ (2 * C / x) * (((j : ℝ) + 1) * Real.exp (-(j : ℝ))) := by positivity
      linarith
    nlinarith [hE0]
  have htsumF : ∑' j : ℕ, F j
      = E * ((κ / x + 2 * C * T ^ θ) * expGeomSum + (2 * C / x) * expGeomLinSum) := by
    rw [hF, tsum_mul_left,
      (summable_expNegNat.mul_left (κ / x + 2 * C * T ^ θ)).tsum_add
        (summable_expNegNat_lin.mul_left (2 * C / x)),
      tsum_mul_left, tsum_mul_left, expGeomSum, expGeomLinSum]
  rw [← htsumF]
  refine Real.tsum_le_of_sum_le (fun g => by dsimp only; split_ifs <;> positivity) fun S => ?_
  have hrestrict : ∑ g ∈ S, (if T < B.intNorm g then Real.exp (-x * B.intNorm g) else 0)
      = ∑ g ∈ S.filter fun g => T < B.intNorm g, Real.exp (-x * B.intNorm g) :=
    (Finset.sum_filter _ _).symm
  rw [hrestrict]
  have hmaps : ∀ g ∈ S.filter fun g => T < B.intNorm g,
      B.layerIndex T x g ∈ (S.filter fun g => T < B.intNorm g).image (B.layerIndex T x) :=
    fun g hg => Finset.mem_image_of_mem _ hg
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum ?_)
    (hFsummable.sum_le_tsum _ (fun j _ => hFnonneg j))
  intro j _
  have hterm : ∀ g ∈ (S.filter fun g => T < B.intNorm g).filter
        fun g => B.layerIndex T x g = j,
      Real.exp (-x * B.intNorm g) ≤ E * Real.exp (-(j : ℝ)) := by
    intro g hg
    rw [Finset.mem_filter, Finset.mem_filter] at hg
    obtain ⟨⟨-, hgT⟩, hgj⟩ := hg
    obtain ⟨hlow, -⟩ := layerIndex_bounds hx hgT
    rw [hgj] at hlow
    rw [hE, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hxj : x * ((j : ℝ) / x) = (j : ℝ) := by field_simp
    nlinarith
  have hcount := card_layer_le (T := T) hdisc hx j S
  have hstep : (((S.filter fun g => T < B.intNorm g).filter
      fun g => B.layerIndex T x g = j).card : ℝ)
      ≤ κ / x + 2 * C * T ^ θ + 2 * C * ((j : ℝ) + 1) / x := by
    have ha1 : (1 : ℝ) ≤ T + (j : ℝ) / x := by
      have : (0 : ℝ) ≤ (j : ℝ) / x := by positivity
      linarith
    have hab : T + (j : ℝ) / x ≤ T + ((j : ℝ) + 1) / x := by
      have hj : (j : ℝ) / x ≤ ((j : ℝ) + 1) / x := by
        gcongr
        linarith
      linarith
    have hdiff := countBall_sub_le hN ha1 hab
    have hb : (T + ((j : ℝ) + 1) / x) ^ θ ≤ T ^ θ + ((j : ℝ) + 1) / x :=
      rpow_add_le_of_one_le hT (by positivity) hθ1
    have hbA : (T + (j : ℝ) / x) ^ θ ≤ T ^ θ + (j : ℝ) / x :=
      rpow_add_le_of_one_le hT (by positivity) hθ1
    have hwidth : (T + ((j : ℝ) + 1) / x) - (T + (j : ℝ) / x) = 1 / x := by
      field_simp
      ring
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hxinv : (0 : ℝ) < 1 / x := by positivity
    have hcombine : κ * ((T + ((j : ℝ) + 1) / x) - (T + (j : ℝ) / x))
        + C * ((T + ((j : ℝ) + 1) / x) ^ θ + (T + (j : ℝ) / x) ^ θ)
        ≤ κ / x + 2 * C * T ^ θ + 2 * C * ((j : ℝ) + 1) / x := by
      rw [hwidth]
      have hxle : (j : ℝ) / x ≤ ((j : ℝ) + 1) / x := by
        gcongr
        linarith
      have hCb : C * ((T + ((j : ℝ) + 1) / x) ^ θ + (T + (j : ℝ) / x) ^ θ)
          ≤ C * ((T ^ θ + ((j : ℝ) + 1) / x) + (T ^ θ + (j : ℝ) / x)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        linarith
      have hfin : C * ((T ^ θ + ((j : ℝ) + 1) / x) + (T ^ θ + (j : ℝ) / x))
          ≤ 2 * C * T ^ θ + 2 * C * ((j : ℝ) + 1) / x := by
        have hmul : C * ((j : ℝ) / x) ≤ C * (((j : ℝ) + 1) / x) :=
          mul_le_mul_of_nonneg_left hxle hC0
        have hdiv : 2 * C * ((j : ℝ) + 1) / x = C * (((j : ℝ) + 1) / x) + C * (((j : ℝ) + 1) / x) := by
          field_simp
          ring
        rw [hdiv]
        nlinarith
      have hκx : κ * (1 / x) = κ / x := by
        field_simp
      linarith
    linarith [le_trans hcount hdiff]
  calc ∑ g ∈ (S.filter fun g => T < B.intNorm g).filter fun g => B.layerIndex T x g = j,
        Real.exp (-x * B.intNorm g)
      ≤ ∑ g ∈ (S.filter fun g => T < B.intNorm g).filter fun g => B.layerIndex T x g = j,
          E * Real.exp (-(j : ℝ)) := Finset.sum_le_sum hterm
    _ = (((S.filter fun g => T < B.intNorm g).filter fun g => B.layerIndex T x g = j).card : ℝ)
          * (E * Real.exp (-(j : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (κ / x + 2 * C * T ^ θ + 2 * C * ((j : ℝ) + 1) / x) * (E * Real.exp (-(j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right hstep ?_
        positivity
    _ = F j := by
        rw [hF]
        field_simp


/-! ## The higher-large-prime remainder -/

theorem intNorm_le_of_le {s t : Multiset B.Label} (h : s ≤ t) : B.intNorm s ≤ B.intNorm t := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  rw [intNorm_add]
  have h1 : 1 ≤ B.intNorm u := B.one_le_intNorm u
  have h2 : 0 < B.intNorm s := B.intNorm_pos s
  nlinarith

/-- Two large labels already push the norm above the square of the cutoff. -/
theorem sq_lt_intNorm_of_two_le_largeCount {z : ℝ} (hz : 0 ≤ z) {g : Multiset B.Label}
    (hg : 2 ≤ B.largeCount z g) : z ^ 2 < B.intNorm g := by
  classical
  have hcard : 2 ≤ (g.filter fun p => z < B.labelNorm p).card := hg
  obtain ⟨p, L', hL1⟩ : ∃ p L', (g.filter fun p => z < B.labelNorm p) = p ::ₘ L' := by
    rcases (g.filter fun p => z < B.labelNorm p).empty_or_exists_mem with hempty | ⟨p, hp⟩
    · rw [hempty] at hcard
      simp at hcard
    · exact ⟨p, _, (Multiset.cons_erase hp).symm⟩
  have hcard' : 1 ≤ L'.card := by
    rw [hL1, Multiset.card_cons] at hcard
    omega
  obtain ⟨q, L'', hL2⟩ : ∃ q L'', L' = q ::ₘ L'' := by
    rcases L'.empty_or_exists_mem with hempty | ⟨q, hq⟩
    · rw [hempty] at hcard'
      simp at hcard'
    · exact ⟨q, _, (Multiset.cons_erase hq).symm⟩
  have hple : p ::ₘ q ::ₘ L'' ≤ g := by
    rw [← hL2, ← hL1]
    exact Multiset.filter_le _ g
  have hp : z < B.labelNorm p := by
    have hmem : p ∈ g.filter fun r => z < B.labelNorm r := by
      rw [hL1]
      exact Multiset.mem_cons_self p _
    exact (Multiset.mem_filter.mp hmem).2
  have hq : z < B.labelNorm q := by
    have hmem : q ∈ g.filter fun r => z < B.labelNorm r := by
      rw [hL1, hL2]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self q _)
    exact (Multiset.mem_filter.mp hmem).2
  have hpair : B.intNorm (p ::ₘ q ::ₘ L'') ≤ B.intNorm g := intNorm_le_of_le hple
  have hval : B.intNorm (p ::ₘ q ::ₘ L'')
      = B.labelNorm p * (B.labelNorm q * B.intNorm L'') := by
    rw [intNorm_cons, intNorm_cons]
  have hL'' : 1 ≤ B.intNorm L'' := B.one_le_intNorm L''
  have hqpos : 0 < B.labelNorm q := lt_trans zero_lt_one (B.one_lt_labelNorm q)
  have hppos : 0 < B.labelNorm p := lt_trans zero_lt_one (B.one_lt_labelNorm p)
  have hz2 : z ^ 2 = z * z := by ring
  have h1 : z * z ≤ z * B.labelNorm q := by nlinarith
  have h2 : z * B.labelNorm q < B.labelNorm p * B.labelNorm q := by nlinarith
  have hmid : B.labelNorm p * B.labelNorm q
      ≤ B.labelNorm p * (B.labelNorm q * B.intNorm L'') := by nlinarith
  rw [hz2]
  linarith [hpair, hval]

/-- **The higher-large-prime remainder is a tail sum.** -/
theorem abs_higherLargeSum_le_tsum (hdisc : B.IsDiscrete) {C' : ℝ}
    (hC' : B.HasLinearCounting C') {x z : ℝ} (hx : 0 < x) (hz : 0 ≤ z) :
    |B.higherLargeSum z x|
      ≤ ∑' g : Multiset B.Label,
          (if z ^ 2 < B.intNorm g then Real.exp (-x * B.intNorm g) else 0) := by
  classical
  have hsum1 : Summable fun g : Multiset B.Label =>
      if 2 ≤ B.largeCount z g then B.gibbsTerm x g else 0 :=
    summable_gibbsTerm_indicator hdisc hC' hx _
  rw [higherLargeSum, ← Real.norm_eq_abs]
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · refine (summable_expNegNorm hdisc hC' hx).of_norm_bounded ?_
    intro g
    by_cases hg : 2 ≤ B.largeCount z g
    · rw [if_pos hg, norm_norm]
      exact norm_gibbsTerm_le x g
    · rw [if_neg hg, norm_norm, norm_zero]
      exact (Real.exp_pos _).le
  · refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro g
      by_cases hg : 2 ≤ B.largeCount z g
      · rw [if_pos hg, if_pos (sq_lt_intNorm_of_two_le_largeCount hz hg)]
        exact norm_gibbsTerm_le x g
      · rw [if_neg hg, norm_zero]
        by_cases hg2 : z ^ 2 < B.intNorm g
        · rw [if_pos hg2]
          exact (Real.exp_pos _).le
        · rw [if_neg hg2]
    · refine (summable_expNegNorm hdisc hC' hx).of_norm_bounded ?_
      intro g
      by_cases hg : 2 ≤ B.largeCount z g
      · rw [if_pos hg, norm_norm]
        exact norm_gibbsTerm_le x g
      · rw [if_neg hg, norm_norm, norm_zero]
        exact (Real.exp_pos _).le
    · refine (summable_expNegNorm hdisc hC' hx).of_nonneg_of_le ?_ ?_
      · intro g
        by_cases hg : z ^ 2 < B.intNorm g
        · rw [if_pos hg]
          exact (Real.exp_pos _).le
        · rw [if_neg hg]
      · intro g
        by_cases hg : z ^ 2 < B.intNorm g
        · rw [if_pos hg]
        · rw [if_neg hg]
          exact (Real.exp_pos _).le

/-- **The critical higher-large-prime bound `(BF6)`, structural form.**  The remainder is bounded by
the tail estimate at the threshold `z²`. -/
theorem abs_higherLargeSum_le (hdisc : B.IsDiscrete) {κ C θ : ℝ}
    (hN : B.HasCountingError κ C θ) {C' : ℝ} (hC' : B.HasLinearCounting C') (hκ : 0 ≤ κ)
    (hC0 : 0 ≤ C) (hθ1 : θ ≤ 1) {x z : ℝ} (hx : 0 < x) (hz : 1 ≤ z) :
    |B.higherLargeSum z x|
      ≤ Real.exp (-x * z ^ 2) *
          ((κ / x + 2 * C * (z ^ 2) ^ θ) * expGeomSum + (2 * C / x) * expGeomLinSum) := by
  refine le_trans (abs_higherLargeSum_le_tsum hdisc hC' hx (by linarith)) ?_
  refine tsum_tail_le hdisc hN hκ hC0 hθ1 hx ?_
  nlinarith


/-! ## The endpoint bound -/

theorem mul_exp_neg_antitone {Y y : ℝ} (hY : 0 ≤ Y) (hy : Y ≤ y) :
    (y + 1) * Real.exp (-y) ≤ (Y + 1) * Real.exp (-Y) := by
  have ht0 : 0 ≤ y - Y := by linarith
  have h1t : 0 < 1 + (y - Y) := by linarith
  have hexp : Real.exp (-y) = Real.exp (-Y) * Real.exp (-(y - Y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hEpos : 0 < Real.exp (-Y) := Real.exp_pos _
  have hinv : Real.exp (-(y - Y)) ≤ 1 / (1 + (y - Y)) := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ h1t ?_
    linarith [Real.add_one_le_exp (y - Y)]
  have hkey : (y + 1) / (1 + (y - Y)) ≤ Y + 1 := by
    rw [div_le_iff₀ h1t]
    nlinarith
  calc (y + 1) * Real.exp (-y)
      = (y + 1) * (Real.exp (-Y) * Real.exp (-(y - Y))) := by rw [hexp]
    _ ≤ (y + 1) * (Real.exp (-Y) * (1 / (1 + (y - Y)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact mul_le_mul_of_nonneg_left hinv hEpos.le
    _ = ((y + 1) / (1 + (y - Y))) * Real.exp (-Y) := by ring
    _ ≤ (Y + 1) * Real.exp (-Y) := mul_le_mul_of_nonneg_right hkey hEpos.le

theorem rpow_le_add_one {y θ : ℝ} (hy : 0 ≤ y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : y ^ θ ≤ y + 1 := by
  rcases le_or_gt y 1 with h | h
  · have hle : y ^ θ ≤ 1 := Real.rpow_le_one hy h hθ0
    linarith
  · have hle : y ^ θ ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hθ1
    rw [Real.rpow_one] at hle
    linarith

theorem exp_neg_half_log_inv {x : ℝ} (hx : 0 < x) :
    Real.exp (-((1 : ℝ) / 2 * Real.log (1 / x))) = x ^ ((1 : ℝ) / 2) := by
  rw [Real.rpow_def_of_pos hx, Real.log_div one_ne_zero (ne_of_gt hx), Real.log_one]
  congr 1
  ring

/-- **The critical remainder bound `(BF6)`, explicit form.**  Under the seam condition `(BF5)` the
higher-large-prime remainder splits into an `x^{-1/2}` term and a term with a logarithmic factor
and a strictly smaller power. -/
theorem abs_higherLargeSum_le_explicit (hdisc : B.IsDiscrete) {κ C θ : ℝ}
    (hN : B.HasCountingError κ C θ) {C' : ℝ} (hC' : B.HasLinearCounting C') (hκ : 0 ≤ κ)
    (hC0 : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {x z : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hz : 1 ≤ z)
    (hBF5 : (1 : ℝ) / 2 * Real.log (1 / x) ≤ x * z ^ 2) :
    |B.higherLargeSum z x|
      ≤ (κ * expGeomSum + 2 * C * expGeomLinSum) * x ^ (-((1 : ℝ) / 2))
        + 2 * C * expGeomSum * ((1 : ℝ) / 2 * Real.log (1 / x) + 1) * x ^ ((1 : ℝ) / 2 - θ) := by
  set Y : ℝ := (1 : ℝ) / 2 * Real.log (1 / x) with hY
  set y : ℝ := x * z ^ 2 with hy
  have hxne : x ≠ 0 := ne_of_gt hx
  have hY0 : 0 ≤ Y := by
    rw [hY]
    have : (1 : ℝ) ≤ 1 / x := (one_le_div hx).mpr hx1
    have hlog : 0 ≤ Real.log (1 / x) := Real.log_nonneg this
    linarith
  have hyY : Y ≤ y := hBF5
  have hy0 : 0 ≤ y := le_trans hY0 hyY
  have hxhalf : Real.exp (-Y) = x ^ ((1 : ℝ) / 2) := exp_neg_half_log_inv hx
  have hexpy : Real.exp (-y) ≤ x ^ ((1 : ℝ) / 2) := by
    rw [← hxhalf]
    exact Real.exp_le_exp.mpr (by linarith)
  have hz2 : z ^ 2 = y / x := by
    rw [hy]
    field_simp
  have hz2pow : (z ^ 2) ^ θ = y ^ θ * x ^ (-θ) := by
    rw [hz2, Real.div_rpow hy0 hx.le, Real.rpow_neg hx.le, div_eq_mul_inv]
  have hyexp : y ^ θ * Real.exp (-y) ≤ (Y + 1) * x ^ ((1 : ℝ) / 2) := by
    have h1 : y ^ θ * Real.exp (-y) ≤ (y + 1) * Real.exp (-y) := by
      have hexppos : 0 < Real.exp (-y) := Real.exp_pos _
      exact mul_le_mul_of_nonneg_right (rpow_le_add_one hy0 hθ0 hθ1) hexppos.le
    have h2 : (y + 1) * Real.exp (-y) ≤ (Y + 1) * Real.exp (-Y) :=
      mul_exp_neg_antitone hY0 hyY
    rw [hxhalf] at h2
    linarith
  have hmain := abs_higherLargeSum_le hdisc hN hC' hκ hC0 hθ1 hx hz
  have hxpow : x ^ ((1 : ℝ) / 2) / x = x ^ (-((1 : ℝ) / 2)) := by
    have hinvx : x⁻¹ = x ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hx.le, Real.rpow_one]
    rw [div_eq_mul_inv, hinvx, ← Real.rpow_add hx]
    norm_num
  refine le_trans hmain ?_
  rw [show -x * z ^ 2 = -y from by rw [hy]; ring]
  have hE0 : 0 ≤ expGeomSum := expGeomSum_nonneg
  have hE0' : 0 ≤ expGeomLinSum := expGeomLinSum_nonneg
  have hexppos : 0 < Real.exp (-y) := Real.exp_pos _
  have hsplit : Real.exp (-y) *
      ((κ / x + 2 * C * (z ^ 2) ^ θ) * expGeomSum + 2 * C / x * expGeomLinSum)
      = (κ * expGeomSum + 2 * C * expGeomLinSum) * (Real.exp (-y) / x)
        + 2 * C * expGeomSum * ((z ^ 2) ^ θ * Real.exp (-y)) := by
    field_simp
    ring
  rw [hsplit]
  have hterm1 : (κ * expGeomSum + 2 * C * expGeomLinSum) * (Real.exp (-y) / x)
      ≤ (κ * expGeomSum + 2 * C * expGeomLinSum) * x ^ (-((1 : ℝ) / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hxpow]
    gcongr
  have hterm2 : 2 * C * expGeomSum * ((z ^ 2) ^ θ * Real.exp (-y))
      ≤ 2 * C * expGeomSum * ((Y + 1) * x ^ ((1 : ℝ) / 2 - θ)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hz2pow]
    have hcalc : y ^ θ * x ^ (-θ) * Real.exp (-y) = (y ^ θ * Real.exp (-y)) * x ^ (-θ) := by ring
    rw [hcalc]
    have hxθ : (0 : ℝ) < x ^ (-θ) := Real.rpow_pos_of_pos hx _
    have := mul_le_mul_of_nonneg_right hyexp hxθ.le
    refine le_trans this ?_
    rw [mul_assoc, ← Real.rpow_add hx]
    have : (1 : ℝ) / 2 + -θ = (1 : ℝ) / 2 - θ := by ring
    rw [this]
  linarith [hterm1, hterm2]


/-- **The critical remainder bound `(BF6)`.**  Under the seam condition `(BF5)` the
higher-large-prime remainder is `O(x^{-1/2})` as `x ↓ 0`. -/
theorem eventually_abs_higherLargeSum_le (hdisc : B.IsDiscrete) {κ C θ : ℝ}
    (hN : B.HasCountingError κ C θ) {C' : ℝ} (hC' : B.HasLinearCounting C') (hκ : 0 ≤ κ)
    (hC0 : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ z : ℝ, 1 ≤ z → (1 : ℝ) / 2 * Real.log (1 / x) ≤ x * z ^ 2 →
        |B.higherLargeSum z x|
          ≤ (κ * expGeomSum + 2 * C * expGeomLinSum + 1) * x ^ (-((1 : ℝ) / 2)) := by
  have hr : 0 < 1 - θ := by linarith
  have hpow : Filter.Tendsto (fun x : ℝ => x ^ (1 - θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hlog := Real.tendsto_log_nhdsGT_zero
    have hmul : Filter.Tendsto (fun x : ℝ => (1 - θ) * Real.log x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atBot :=
      Filter.Tendsto.const_mul_atBot hr hlog
    have hexp := Real.tendsto_exp_atBot.comp hmul
    refine hexp.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    rw [Function.comp_apply, Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hlogmul := tendsto_log_mul_rpow_nhdsGT_zero hr
  have hlim : Filter.Tendsto
      (fun x : ℝ => 2 * C * expGeomSum * ((1 : ℝ) / 2 * Real.log (1 / x) + 1) * x ^ (1 - θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcombo := ((hlogmul.const_mul (-(C * expGeomSum))).add
      (hpow.const_mul (2 * C * expGeomSum)))
    have hzero : -(C * expGeomSum) * 0 + 2 * C * expGeomSum * 0 = 0 := by ring
    rw [hzero] at hcombo
    refine hcombo.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.log_div one_ne_zero (ne_of_gt hx0), Real.log_one]
    ring
  have hsmall : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      2 * C * expGeomSum * ((1 : ℝ) / 2 * Real.log (1 / x) + 1) * x ^ (1 - θ) ≤ 1 :=
    hlim.eventually_le_const (by norm_num)
  filter_upwards [hsmall, Ioo_mem_nhdsGT one_pos] with x hxsmall hxmem z hz hBF5
  obtain ⟨hx0, hx1⟩ := hxmem
  have hexp := abs_higherLargeSum_le_explicit hdisc hN hC' hκ hC0 hθ0 hθ1.le hx0 hx1.le hz hBF5
  have hsplit : x ^ ((1 : ℝ) / 2 - θ) = x ^ (1 - θ) * x ^ (-((1 : ℝ) / 2)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [hsplit] at hexp
  have hpos : (0 : ℝ) < x ^ (-((1 : ℝ) / 2)) := Real.rpow_pos_of_pos hx0 _
  nlinarith [hexp, hxsmall, hpos]

end BeurlingSystem

end RHTower
