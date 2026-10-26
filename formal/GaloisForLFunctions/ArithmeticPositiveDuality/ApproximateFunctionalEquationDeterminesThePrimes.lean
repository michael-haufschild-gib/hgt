import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationNearCounting
import GaloisForLFunctions.ArithmeticPositiveDuality.BeurlingRiemannFunctionalEquationRigidity

/-!
# An approximate functional equation determines the primes up to height `‖g‖₁^{-1/2}`

Positive-measure rigidity identifies a countable Beurling system whose zeta function satisfies
Riemann's functional equation: its generalized integers are the positive integers and its primes
are the rational primes (`beurlingSystem_rigidity_of_theta_relation`). Here the functional equation
fails on the critical line by `Γ_ℝ(s) g(Im s / 2)`, and the conclusion survives up to a height set
by the defect.

**Theorem** (`beurling_primes_of_critical_line_defect`). Let `B` be a countable Beurling system with
`Σ_x |x|^{-3/2} < ∞` whose zeta function satisfies the hypotheses of
`integral_sinc_sq_le_of_critical_line_defect` with defect `g`, and put `M = ‖g‖₁`,
`ρ = √(3πM/2)`. If `N ≥ 4` and `400 N² M ≤ 1`, then
* every generalized integer `x` with `|x| ≤ N` lies within `ρ|x|` of an integer;
* for every `1 ≤ m ≤ N - 2` exactly one generalized integer has norm within `1/8` of `m`;
* the Beurling primes of norm `< N - 3/2` correspond bijectively to the rational primes `≤ N - 2`,
  each within `ρN` of its partner.

The primes are the logarithm of the integer data, and they are stable: a defect `M` fixes them up
to height `≍ M^{-1/2}`.

**Proof.**
* An atom of norm `u` has `sinc²(πu) ≤ ∫ sinc² dν ≤ (6/π) M`, and `|sin πu| ≥ 2 dist(u, ℤ)`.
* Every unit tent mass is `2 Re β` up to `8M` (`abs_integral_unitTent_sub_le_of_critical_line_defect`,
  `defectKernelConst ≤ 4`). With all atoms within `1/8` of integers, the tent at `n` counts the
  atoms rounding to `n`, up to `1/8` of the neighbouring counts.
* No prime has norm near `1`: its first power past `3/2` would lie in `[3/2, 27/16)`. So only the
  empty integer rounds to `1`, `2 Re β ≈ 1`, and every count `2 ≤ m ≤ N - 2` is one.
* Rounding is multiplicative on generalized integers of norm `≤ N`. A prime rounds to a prime, since
  a factorization of its round would split the singleton; a rational prime is the round of a
  singleton, since a nontrivial split would factor it.
-/

open Complex MeasureTheory Filter Topology Set Function
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open GaloisForLFunctions.HTGeometry

/-! ## 1. The constants -/

/-- `Γ(1/4) = 4 Γ(5/4) ≤ 4`, by convexity of `Γ` between `Γ(1) = Γ(2) = 1`. -/
theorem Gamma_one_quarter_le_four : Real.Gamma (1 / 4) ≤ 4 := by
  have h := Real.Gamma_add_one (s := (1 / 4 : ℝ)) (by norm_num)
  have hconv := Real.convexOn_Gamma.2 (by norm_num : (1 : ℝ) ∈ Ioi 0)
    (by norm_num : (2 : ℝ) ∈ Ioi 0) (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (3 / 4 : ℝ) + 1 / 4 = 1)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at hconv
  rw [show (3 / 4 : ℝ) * 1 + 1 / 4 * 2 = 1 / 4 + 1 by norm_num, h] at hconv
  linarith

theorem defectKernelConst_nonneg : 0 ≤ defectKernelConst :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.Gamma_pos_of_pos (by norm_num)).le)

theorem defectKernelConst_le_four : defectKernelConst ≤ 4 := by
  unfold defectKernelConst
  have h1 : (4 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have h2 : Real.pi ^ (-(1 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have hG0 : 0 ≤ Real.Gamma (1 / 4) := (Real.Gamma_pos_of_pos (by norm_num)).le
  calc (4 : ℝ) ^ (-(1 / 4 : ℝ)) * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4))
      ≤ 1 * (1 * 4) :=
        mul_le_mul h1 (mul_le_mul h2 Gamma_one_quarter_le_four hG0 zero_le_one)
          (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) hG0) zero_le_one
    _ = 4 := by norm_num

/-- The tent-mass constant of `abs_integral_unitTent_sub_le_of_critical_line_defect` is at most `8`. -/
theorem tentConst_le_eight : 18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2 ≤ 8 := by
  have hpi := Real.pi_gt_three
  have hκ := defectKernelConst_le_four
  have hκ0 := defectKernelConst_nonneg
  have h1 : 18 / Real.pi ≤ 6 := by rw [div_le_iff₀ (by positivity)]; linarith
  have h2 : 4 * defectKernelConst / Real.pi ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-! ## 2. Distance to the integers -/

/-- Jordan's inequality on the nearest-integer residue: `2 |u - round u| ≤ |sin (π u)|`. -/
theorem two_mul_abs_sub_round_le_abs_sin (u : ℝ) :
    2 * |u - round u| ≤ |Real.sin (Real.pi * u)| := by
  have hpi := Real.pi_pos
  set t : ℝ := u - round u with ht
  have ht2 : |t| ≤ 1 / 2 := abs_sub_round u
  have hsin : Real.sin (Real.pi * u) = (-1) ^ (round u) * Real.sin (Real.pi * t) := by
    rw [← Real.sin_add_int_mul_pi]
    congr 1
    rw [ht]
    ring
  have key : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 2 * s ≤ Real.sin (Real.pi * s) := by
    intro s hs0 hs1
    have h := Real.mul_le_sin (x := Real.pi * s) (by positivity) (by nlinarith)
    rwa [← mul_assoc, div_mul_cancel₀ _ hpi.ne'] at h
  rw [hsin, abs_mul, abs_neg_one_zpow, one_mul]
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0]
    have := key t h0 (by rwa [abs_of_nonneg h0] at ht2)
    rw [abs_of_nonneg (by linarith)]
    exact this
  · rw [abs_of_neg h0]
    have := key (-t) (by linarith) (by rw [abs_of_neg h0] at ht2; exact ht2)
    rw [show Real.pi * -t = -(Real.pi * t) by ring, Real.sin_neg] at this
    rw [abs_of_neg (by linarith)]
    linarith

/-- An off-lattice weight `sinc²(πu) ≤ S` at `u ≥ 1` places `u` within `√(π²S/4) u` of an
integer. -/
theorem abs_sub_round_le_of_sinc_sq_le {u S : ℝ} (hu : 1 ≤ u)
    (h : (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ≤ S) :
    |u - round u| ≤ Real.sqrt (Real.pi ^ 2 / 4 * S) * u := by
  have hpi := Real.pi_pos
  have hu0 : 0 < u := by linarith
  have h1 := two_mul_abs_sub_round_le_abs_sin u
  have hS : 0 ≤ S := le_trans (sq_nonneg _) h
  have h3 : Real.sin (Real.pi * u) ^ 2 ≤ S * (Real.pi * u) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)] at h
    exact h
  have h2 : (2 * |u - round u|) ^ 2 ≤ Real.sin (Real.pi * u) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rwa [sq_abs] at this
  have h4 : |u - round u| ^ 2 ≤ Real.pi ^ 2 / 4 * S * u ^ 2 := by nlinarith
  calc |u - round u| = Real.sqrt (|u - round u| ^ 2) := (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ Real.sqrt (Real.pi ^ 2 / 4 * S * u ^ 2) := Real.sqrt_le_sqrt h4
    _ = Real.sqrt (Real.pi ^ 2 / 4 * S) * u := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu0.le]

/-- Two integers at real distance `< 1` are equal. -/
theorem int_eq_of_abs_sub_lt_one {m k : ℤ} (h : |(m : ℝ) - k| < 1) : m = k := by
  have h' : |m - k| < 1 := by exact_mod_cast h
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp h')

/-! ## 3. The integer measure of a Beurling system -/

variable (B : RHTower.BeurlingSystem)

theorem beurlingSystemIntegerMeasure_eq_sum_smul :
    beurlingSystemIntegerMeasure B =
      Measure.sum (fun x : B.Integer => (1 : ℝ≥0∞) • Measure.dirac (B.intNorm x)) := by
  unfold beurlingSystemIntegerMeasure; congr 1; ext x : 1; simp

theorem integral_beurlingSystemIntegerMeasure_eq_tsum [Countable B.Label] (f : ℝ → ℝ) :
    ∫ u, f u ∂beurlingSystemIntegerMeasure B = ∑' x : B.Integer, f (B.intNorm x) := by
  rw [beurlingSystemIntegerMeasure_eq_sum_smul, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  exact tsum_congr fun _ => by rw [ENNReal.toReal_one, one_smul]

theorem integrable_rpow_beurlingSystemIntegerMeasure [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ))) :
    Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (beurlingSystemIntegerMeasure B) := by
  rw [beurlingSystemIntegerMeasure_eq_sum_smul]
  refine integrable_sum_dirac (fun _ => ENNReal.one_ne_top) (hBsum.congr fun x => ?_)
  rw [ENNReal.toReal_one, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (B.intNorm_pos x).le _)]

/-- A nonnegative integrable function is at least its value at any atom. -/
theorem le_integral_beurlingSystemIntegerMeasure {f : ℝ → ℝ} (hf0 : ∀ u, 0 ≤ f u)
    (hfi : Integrable f (beurlingSystemIntegerMeasure B)) (x : B.Integer) :
    f (B.intNorm x) ≤ ∫ u, f u ∂beurlingSystemIntegerMeasure B := by
  have hle : Measure.dirac (B.intNorm x) ≤ beurlingSystemIntegerMeasure B := by
    unfold beurlingSystemIntegerMeasure
    exact Measure.le_sum (fun x : B.Integer => Measure.dirac (B.intNorm x)) x
  have h := integral_mono_measure hle (Eventually.of_forall fun u => hf0 u) hfi
  rwa [integral_dirac] at h

/-- Finitely many generalized integers have norm at most `X`. -/
theorem finite_intNorm_le (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    (X : ℝ) : {x : B.Integer | B.intNorm x ≤ X}.Finite := by
  by_cases hX : 1 ≤ X
  · have hpos : 0 < X ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hev := hBsum.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
    refine (Filter.eventually_cofinite.mp hev).subset fun x hx => ?_
    simp only [Set.mem_setOf_eq, not_lt]
    exact Real.rpow_le_rpow_of_nonpos (B.intNorm_pos x) hx (by norm_num)
  · exact Set.finite_empty.subset fun x hx => absurd ((B.one_le_intNorm x).trans hx) hX

theorem intNorm_le_intNorm_add (x y : B.Integer) : B.intNorm x ≤ B.intNorm (x + y) := by
  rw [B.intNorm_add]
  exact le_mul_of_one_le_right (B.intNorm_pos x).le (B.one_le_intNorm y)

theorem labelNorm_le_intNorm_of_mem {p : B.Label} {x : B.Integer} (hp : p ∈ x) :
    B.labelNorm p ≤ B.intNorm x := by
  classical
  rw [← Multiset.cons_erase hp, ← Multiset.singleton_add, ← B.intNorm_singleton p]
  exact intNorm_le_intNorm_add B _ _

/-! ## 4. Rounding the atoms -/

section Rounding

variable {B} {N : ℕ} {ρ : ℝ}
  (hnear : ∀ x : B.Integer, B.intNorm x ≤ N →
    |B.intNorm x - round (B.intNorm x)| ≤ ρ * B.intNorm x)
  (hρ0 : 0 ≤ ρ) (hρ : N * ρ ≤ 1 / 8)
include hnear hρ0 hρ

theorem abs_sub_round_le_eighth {x : B.Integer} (hx : B.intNorm x ≤ N) :
    |B.intNorm x - round (B.intNorm x)| ≤ 1 / 8 :=
  (hnear x hx).trans (by nlinarith [B.intNorm_pos x])

omit hnear hρ0 hρ in
theorem one_le_round_intNorm (x : B.Integer) : 1 ≤ round (B.intNorm x) := by
  have h := abs_sub_round (B.intNorm x)
  have h1 := B.one_le_intNorm x
  have : (0 : ℝ) < round (B.intNorm x) := by linarith [(abs_le.mp h).2]
  exact_mod_cast this

/-- **No prime near `1`.** Only the empty integer rounds to `1`: a label of norm in `(1, 9/8]`
would have a power of norm in `[3/2, 27/16)`, at distance `≥ 5/16` from the integers. -/
theorem eq_zero_of_round_intNorm_eq_one (hN : 4 ≤ N) {x : B.Integer} (hx : B.intNorm x ≤ N)
    (h1 : round (B.intNorm x) = 1) : x = 0 := by
  by_contra hx0
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hx0
  have hx8 : B.intNorm x ≤ 9 / 8 := by
    have := abs_sub_round_le_eighth hnear hρ0 hρ hx
    rw [h1, Int.cast_one] at this
    linarith [(abs_le.mp this).2]
  have hp1 := B.one_lt_labelNorm p
  have hp8 : B.labelNorm p ≤ 9 / 8 := (labelNorm_le_intNorm_of_mem B hp).trans hx8
  classical
  have hex : ∃ j : ℕ, 3 / 2 ≤ B.labelNorm p ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) hp1
    exact ⟨j, hj.le⟩
  set j := Nat.find hex with hj
  have hjge : 3 / 2 ≤ B.labelNorm p ^ j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hjge
    norm_num at hjge
  have hjlt : B.labelNorm p ^ (j - 1) < 3 / 2 := by
    have := Nat.find_min hex (show j - 1 < j by omega)
    exact not_le.mp this
  have hjup : B.labelNorm p ^ j < 27 / 16 := by
    have e : B.labelNorm p ^ j = B.labelNorm p ^ (j - 1) * B.labelNorm p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
    rw [e]
    have hpow0 : 0 ≤ B.labelNorm p ^ (j - 1) := pow_nonneg (by linarith) _
    nlinarith
  set y : B.Integer := Multiset.replicate j p
  have hy : B.intNorm y = B.labelNorm p ^ j := B.intNorm_replicate p j
  have hyN : B.intNorm y ≤ N := by
    rw [hy]
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hnr := abs_sub_round_le_eighth hnear hρ0 hρ hyN
  rw [hy] at hnr
  obtain ⟨hlo, hhi⟩ := abs_le.mp hnr
  have hr1 : (1 : ℝ) < round (B.labelNorm p ^ j) := by linarith
  have hr2 : (round (B.labelNorm p ^ j) : ℝ) < 2 := by linarith
  have hr1' : (1 : ℤ) < round (B.labelNorm p ^ j) := by exact_mod_cast hr1
  have hr2' : round (B.labelNorm p ^ j) < (2 : ℤ) := by exact_mod_cast hr2
  omega

theorem two_le_round_intNorm (hN : 4 ≤ N) {x : B.Integer} (hx : B.intNorm x ≤ N) (hx0 : x ≠ 0) :
    2 ≤ round (B.intNorm x) := by
  have h1 := one_le_round_intNorm x
  rcases eq_or_lt_of_le h1 with h | h
  · exact absurd (eq_zero_of_round_intNorm_eq_one hnear hρ0 hρ hN hx h.symm) hx0
  · omega

omit hρ0 hρ in
/-- `|x| ≤ round|x| / (1 - ρ)` for atoms of norm `≤ N`. -/
theorem intNorm_mul_one_sub_le {x : B.Integer} (hx : B.intNorm x ≤ N) :
    B.intNorm x * (1 - ρ) ≤ round (B.intNorm x) := by
  have := hnear x hx
  linarith [(abs_le.mp this).2]

/-- **Rounding is multiplicative** on generalized integers of norm `≤ N`:
`|XY - round X · round Y| ≤ ρXY(2 + ρ)` and `|XY - round(XY)| ≤ ρXY`, with `ρXY ≤ 1/8`. -/
theorem round_intNorm_add {x y : B.Integer} (hxy : B.intNorm (x + y) ≤ N) :
    round (B.intNorm (x + y)) = round (B.intNorm x) * round (B.intNorm y) := by
  have hxN : B.intNorm x ≤ N := (intNorm_le_intNorm_add B x y).trans hxy
  have hyN : B.intNorm y ≤ N := by
    have h := intNorm_le_intNorm_add B y x
    rw [add_comm] at h
    exact h.trans hxy
  have hA := hnear x hxN
  have hB := hnear y hyN
  have hC := hnear (x + y) hxy
  have hX1 := B.one_le_intNorm x
  have hY1 := B.one_le_intNorm y
  rw [B.intNorm_add] at hC hxy ⊢
  generalize B.intNorm x = X at hA hC hxy hX1 ⊢
  generalize B.intNorm y = Y at hB hC hxy hY1 ⊢
  have hρ1 : ρ ≤ 1 / 8 := by
    have hN1 : (1 : ℝ) ≤ N := by nlinarith
    nlinarith
  have hXYρ : X * Y * ρ ≤ 1 / 8 := by nlinarith
  have hY0 : 0 ≤ Y := by linarith
  have hA' := abs_le.mp hA
  have ha0 : 0 ≤ (round X : ℝ) := by nlinarith [hA'.2]
  have ha' : (round X : ℝ) ≤ X + ρ * X := by linarith [hA'.1]
  have hdiff : |X * Y - (round X : ℝ) * (round Y : ℝ)| ≤ X * Y * ρ * (2 + ρ) := by
    have e : X * Y - (round X : ℝ) * (round Y : ℝ) =
        (X - round X) * Y + (round X : ℝ) * (Y - round Y) := by ring
    rw [e]
    calc |(X - round X) * Y + (round X : ℝ) * (Y - round Y)|
        ≤ |X - round X| * Y + (round X : ℝ) * |Y - round Y| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hY0, abs_of_nonneg ha0]
      _ ≤ (ρ * X) * Y + (X + ρ * X) * (ρ * Y) :=
          add_le_add (mul_le_mul_of_nonneg_right hA hY0)
            (mul_le_mul ha' hB (abs_nonneg _) (by nlinarith))
      _ = X * Y * ρ * (2 + ρ) := by ring
  have hfin : |((round (X * Y) : ℤ) : ℝ) - ((round X * round Y : ℤ) : ℝ)| < 1 := by
    push_cast
    have e2 : (round (X * Y) : ℝ) - (round X : ℝ) * (round Y : ℝ) =
        (X * Y - (round X : ℝ) * (round Y : ℝ)) - (X * Y - round (X * Y)) := by ring
    have h3 : X * Y * ρ * (2 + ρ) + ρ * (X * Y) ≤ 1 / 8 * (3 + 1 / 8) := by
      have e3 : X * Y * ρ * (2 + ρ) + ρ * (X * Y) = X * Y * ρ * (3 + ρ) := by ring
      rw [e3]
      exact mul_le_mul hXYρ (by linarith) (by linarith) (by norm_num)
    rw [e2]
    calc |(X * Y - (round X : ℝ) * (round Y : ℝ)) - (X * Y - round (X * Y))|
        ≤ |X * Y - (round X : ℝ) * (round Y : ℝ)| + |X * Y - (round (X * Y) : ℝ)| := abs_sub _ _
      _ ≤ X * Y * ρ * (2 + ρ) + ρ * (X * Y) := add_le_add hdiff hC
      _ < 1 := by linarith
  exact int_eq_of_abs_sub_lt_one hfin

end Rounding

/-! ## 5. Counting by tent masses -/

/-- A unit tent at an integer `n` against a point within `1/8` of the integer `r`: at most one if
`r = n`, at most `1/8` if `r = n ± 1`, and zero otherwise. -/
theorem unitTent_le_indicator {u : ℝ} {r n : ℤ} (hu : |u - r| ≤ 1 / 8) :
    unitTent n u ≤ (if r = n then 1 else 0) +
      1 / 8 * ((if r = n - 1 then 1 else 0) + (if r = n + 1 then 1 else 0)) := by
  have hT1 := unitTent_le_one (n : ℝ) u
  have hA : (0 : ℝ) ≤ if r = n then 1 else 0 := by split_ifs <;> norm_num
  have hB : (0 : ℝ) ≤ if r = n - 1 then 1 else 0 := by split_ifs <;> norm_num
  have hC : (0 : ℝ) ≤ if r = n + 1 then 1 else 0 := by split_ifs <;> norm_num
  obtain ⟨h1, h2⟩ := abs_le.mp hu
  rcases lt_trichotomy r n with hlt | heq | hgt
  · by_cases hr : r = n - 1
    · have hrr : (r : ℝ) = n - 1 := by rw [hr]; push_cast; ring
      have hT : unitTent n u ≤ 1 / 8 := by
        unfold unitTent
        refine max_le (by norm_num) ?_
        rw [abs_of_neg (by linarith)]
        linarith
      rw [if_pos hr]
      linarith
    · have hr2 : (r : ℝ) ≤ n - 2 := by
        have : r ≤ n - 2 := by omega
        exact_mod_cast this
      rw [unitTent_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)]
      positivity
  · rw [if_pos heq]
    linarith
  · by_cases hr : r = n + 1
    · have hrr : (r : ℝ) = n + 1 := by rw [hr]; push_cast; ring
      have hT : unitTent n u ≤ 1 / 8 := by
        unfold unitTent
        refine max_le (by norm_num) ?_
        rw [abs_of_pos (by linarith)]
        linarith
      rw [if_pos hr]
      linarith
    · have hr2 : (n : ℝ) + 2 ≤ r := by
        have : n + 2 ≤ r := by omega
        exact_mod_cast this
      rw [unitTent_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)]
      positivity

theorem le_unitTent_of_near {u : ℝ} {n : ℤ} (hu : |u - n| ≤ 1 / 8) : 7 / 8 ≤ unitTent n u :=
  le_max_of_le_right (by linarith [abs_le.mp hu])

/-- **Counts from tent masses.** If the tent mass `τ n` at each `1 ≤ n ≤ N - 1` is `c` up to
`η ≤ 1/16`, bounds the count `cnt n` of atoms rounding to `n` as `(7/8) cnt n ≤ τ n ≤
cnt n + (cnt (n-1) + cnt (n+1))/8`, and `cnt 0 = 0`, `cnt 1 = 1`, `τ 1 ≥ 1`, then every count at
`2 ≤ m ≤ N - 2` is one. -/
theorem cnt_eq_one_of_tent {N : ℤ} {cnt : ℤ → ℕ} {τ : ℤ → ℝ} {c η : ℝ} (hη : η ≤ 1 / 16)
    (h0 : cnt 0 = 0) (h1 : cnt 1 = 1) (hτ1 : 1 ≤ τ 1)
    (hlow : ∀ n : ℤ, 1 ≤ n → n + 1 ≤ N → 7 / 8 * (cnt n : ℝ) ≤ τ n)
    (hup : ∀ n : ℤ, 1 ≤ n → n + 1 ≤ N →
      τ n ≤ cnt n + 1 / 8 * ((cnt (n - 1) : ℝ) + cnt (n + 1)))
    (hτ : ∀ n : ℤ, 1 ≤ n → n + 1 ≤ N → |τ n - c| ≤ η) (hN : 4 ≤ N) :
    ∀ m : ℤ, 2 ≤ m → m + 2 ≤ N → cnt m = 1 := by
  have hτ1c := abs_le.mp (hτ 1 le_rfl (by omega))
  have hc_lo : 1 - η ≤ c := by linarith
  -- `cnt 2 ≤ 1`.
  have hcnt2 : cnt 2 ≤ 1 := by
    have hl := hlow 2 (by norm_num) (by omega)
    have h2c := abs_le.mp (hτ 2 (by norm_num) (by omega))
    have hu := hup 1 le_rfl (by omega)
    rw [show (1 : ℤ) - 1 = 0 by norm_num, h0, h1, show (1 : ℤ) + 1 = 2 by norm_num] at hu
    have : (cnt 2 : ℝ) < 2 := by push_cast at hu; linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hc_hi : c ≤ 9 / 8 + η := by
    have hu := hup 1 le_rfl (by omega)
    rw [show (1 : ℤ) - 1 = 0 by norm_num, h0, h1, show (1 : ℤ) + 1 = 2 by norm_num] at hu
    have : (cnt 2 : ℝ) ≤ 1 := by exact_mod_cast hcnt2
    push_cast at hu
    linarith
  -- Every count at `2 ≤ m ≤ N - 1` is at most one.
  have hle : ∀ m : ℤ, 2 ≤ m → m + 1 ≤ N → cnt m ≤ 1 := by
    intro m hm hmN
    have hl := hlow m (by omega) hmN
    have hmc := abs_le.mp (hτ m (by omega) hmN)
    have : (cnt m : ℝ) < 2 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  intro m hm hmN
  refine le_antisymm (hle m hm (by omega)) ?_
  have hu := hup m (by omega) (by omega)
  have hmc := abs_le.mp (hτ m (by omega) (by omega))
  have hprev : (cnt (m - 1) : ℝ) ≤ 1 := by
    rcases eq_or_lt_of_le hm with h | h
    · rw [← h, show (2 : ℤ) - 1 = 1 by norm_num, h1]; norm_num
    · exact_mod_cast hle (m - 1) (by omega) (by omega)
  have hnext : (cnt (m + 1) : ℝ) ≤ 1 := by exact_mod_cast hle (m + 1) (by omega) (by omega)
  have : (0 : ℝ) < cnt m := by linarith
  exact_mod_cast this

/-! ## 6. The primes -/

/-- The tent mass at an integer `n` with `n + 1 ≤ N` is the finite sum over the atoms of norm
`≤ N`. -/
theorem integral_unitTent_eq_sum_of_le (B : RHTower.BeurlingSystem) [Countable B.Label]
    {S : Finset B.Integer} {N : ℝ} (hS : ∀ x, x ∉ S → N < B.intNorm x) {n : ℝ}
    (hn : n + 1 ≤ N) :
    ∫ u, unitTent n u ∂beurlingSystemIntegerMeasure B = ∑ x ∈ S, unitTent n (B.intNorm x) := by
  rw [integral_beurlingSystemIntegerMeasure_eq_tsum]
  refine tsum_eq_sum fun x hx => unitTent_eq_zero ?_
  have := hS x hx
  rw [abs_of_pos (by linarith)]
  linarith

/-- **An approximate functional equation determines the primes.** Let `B` be a countable Beurling
system with `Σ_x |x|^{-3/2} < ∞`, and let `E` be continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic
inside and `O(1/(1 + t²))`, with `Γ_ℝ(s) ζ_B(s) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2` and
`E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + Γ_ℝ(s) g(Im s / 2)` on `Re s = 1/2`, with `g`
measurable, polynomially bounded and integrable. If `N ≥ 4` and `400 N² ‖g‖₁ ≤ 1`, then with
`ρ = √(3π ‖g‖₁ / 2)`: every generalized integer of norm `≤ N` lies within `ρ|x|` of an integer;
each `1 ≤ m ≤ N - 2` is within `1/8` of exactly one generalized integer; and the Beurling primes of
norm `< N - 3/2` are in bijection with the rational primes `≤ N - 2`, each within `ρN` of its
partner. -/
theorem beurling_primes_of_critical_line_defect (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng) (hgi : Integrable g)
    {N : ℕ} (hN : 4 ≤ N) (hsmall : 400 * (N : ℝ) ^ 2 * ∫ t, ‖g t‖ ≤ 1) :
    (∀ x : B.Integer, |B.intNorm x - round (B.intNorm x)| ≤
      Real.sqrt (3 * Real.pi / 2 * ∫ t, ‖g t‖) * B.intNorm x) ∧
    (∀ m : ℕ, 1 ≤ m → m + 2 ≤ N → ∃! x : B.Integer, |B.intNorm x - m| ≤ 1 / 8) ∧
    Nonempty {e : {p : B.Label // B.labelNorm p < N - 3 / 2} ≃ {q : ℕ // q.Prime ∧ q + 2 ≤ N} //
      ∀ p, |B.labelNorm p.1 - (e p : ℕ)| ≤ Real.sqrt (3 * Real.pi / 2 * ∫ t, ‖g t‖) * N} := by
  classical
  have hpi := Real.pi_pos
  set M : ℝ := ∫ t, ‖g t‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hMsmall : M ≤ 1 / 6400 := by
    have hN2 : (16 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2 (by norm_num : (0 : ℝ) ≤ 400))
      hM0
    linarith
  -- The analytic inputs: off-lattice mass and tent masses.
  have hsupp := beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom := integrable_rpow_beurlingSystemIntegerMeasure B hBsum
  have hmom2 := integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom
  have hR' : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s *
      measureDirichlet (beurlingSystemIntegerMeasure B) s = E s + β * Complex.Gammaℝ (s - 1) :=
    fun s hs => by rw [measureDirichlet_beurlingSystemIntegerMeasure]; exact hR s hs
  have hS := integral_sinc_sq_le_of_critical_line_defect hsupp hmom hEc hEd hdecay hR' hC hgm hgb
    hgi
  have hsinc : Integrable (fun u : ℝ => (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2)
      (beurlingSystemIntegerMeasure B) := by
    refine (hmom2.const_mul (1 / Real.pi ^ 2)).mono' (Measurable.aestronglyMeasurable
      (by fun_prop)) ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, mul_pow, one_div_mul_one_div]
    exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (by positivity)
  -- Every atom is near an integer.
  set ρ : ℝ := Real.sqrt (3 * Real.pi / 2 * M) with hρdef
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hnear_all : ∀ x : B.Integer,
      |B.intNorm x - round (B.intNorm x)| ≤ ρ * B.intNorm x := by
    intro x
    have h := le_integral_beurlingSystemIntegerMeasure B (fun u => sq_nonneg _) hsinc x
    have h2 := abs_sub_round_le_of_sinc_sq_le (B.one_le_intNorm x) (h.trans hS)
    have e : Real.pi ^ 2 / 4 * (6 / Real.pi * M) = 3 * Real.pi / 2 * M := by field_simp; ring
    rwa [e] at h2
  have hnear : ∀ x : B.Integer, B.intNorm x ≤ N →
      |B.intNorm x - round (B.intNorm x)| ≤ ρ * B.intNorm x := fun x _ => hnear_all x
  have hρN : (N : ℝ) * ρ ≤ 1 / 8 := by
    have hsq : 3 * Real.pi / 2 * M * (N : ℝ) ^ 2 ≤ (1 / 8) ^ 2 := by
      have hpi4 := Real.pi_lt_d2
      have hMN : M * (N : ℝ) ^ 2 ≤ 1 / 400 := by linarith
      have h0 : 0 ≤ M * (N : ℝ) ^ 2 := by positivity
      nlinarith
    have e : (N : ℝ) * ρ = Real.sqrt (3 * Real.pi / 2 * M * (N : ℝ) ^ 2) := by
      show (N : ℝ) * Real.sqrt (3 * Real.pi / 2 * M) = _
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg N), mul_comm]
    rw [e]
    calc Real.sqrt (3 * Real.pi / 2 * M * (N : ℝ) ^ 2) ≤ Real.sqrt ((1 / 8) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = 1 / 8 := Real.sqrt_sq (by norm_num)
  -- The finite set of atoms of norm `≤ N` and the counts by round.
  set S : Finset B.Integer := (finite_intNorm_le B hBsum N).toFinset with hSdef
  have hmemS : ∀ x, x ∈ S ↔ B.intNorm x ≤ N := fun x => by simp [hSdef]
  have hnotS : ∀ x, x ∉ S → (N : ℝ) < B.intNorm x := fun x hx => by
    rw [hmemS] at hx; exact not_le.mp hx
  set cnt : ℤ → ℕ := fun m => (S.filter fun x => round (B.intNorm x) = m).card with hcnt
  set τ : ℤ → ℝ := fun n => ∫ u, unitTent n u ∂beurlingSystemIntegerMeasure B with hτdef
  have hτsum : ∀ n : ℤ, n + 1 ≤ N → τ n = ∑ x ∈ S, unitTent n (B.intNorm x) := by
    intro n hn
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    exact integral_unitTent_eq_sum_of_le B hnotS hn'
  have hup : ∀ n : ℤ, 1 ≤ n → n + 1 ≤ N →
      τ n ≤ cnt n + 1 / 8 * ((cnt (n - 1) : ℝ) + cnt (n + 1)) := by
    intro n _ hnN
    rw [hτsum n hnN]
    calc ∑ x ∈ S, unitTent n (B.intNorm x)
        ≤ ∑ x ∈ S, ((if round (B.intNorm x) = n then (1 : ℝ) else 0) + 1 / 8 *
            ((if round (B.intNorm x) = n - 1 then 1 else 0) +
              (if round (B.intNorm x) = n + 1 then 1 else 0))) :=
          Finset.sum_le_sum fun x hx => unitTent_le_indicator
            (abs_sub_round_le_eighth hnear hρ0 hρN ((hmemS x).mp hx))
      _ = cnt n + 1 / 8 * ((cnt (n - 1) : ℝ) + cnt (n + 1)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
            Finset.sum_boole, Finset.sum_boole, Finset.sum_boole]
  have hlow : ∀ n : ℤ, 1 ≤ n → n + 1 ≤ N → 7 / 8 * (cnt n : ℝ) ≤ τ n := by
    intro n _ hnN
    rw [hτsum n hnN]
    calc 7 / 8 * (cnt n : ℝ) = ∑ x ∈ S, (7 / 8 * if round (B.intNorm x) = n then (1 : ℝ) else 0) := by
          rw [← Finset.mul_sum, Finset.sum_boole]
      _ ≤ ∑ x ∈ S, unitTent n (B.intNorm x) := by
          refine Finset.sum_le_sum fun x hx => ?_
          split_ifs with h
          · rw [mul_one]
            have := abs_sub_round_le_eighth hnear hρ0 hρN ((hmemS x).mp hx)
            rw [h] at this
            exact le_unitTent_of_near this
          · rw [mul_zero]; exact unitTent_nonneg _ _
  have h0 : cnt 0 = 0 := by
    simp only [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ h
    have := one_le_round_intNorm x
    omega
  have hfilter1 : (S.filter fun x => round (B.intNorm x) = 1) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, h1⟩
      exact eq_zero_of_round_intNorm_eq_one hnear hρ0 hρN hN ((hmemS x).mp hx) h1
    · rintro rfl
      refine ⟨(hmemS 0).mpr (by rw [B.intNorm_zero]; linarith), ?_⟩
      rw [B.intNorm_zero]; exact round_one
  have h1 : cnt 1 = 1 := by simp only [hcnt, hfilter1, Finset.card_singleton]
  have hτ1 : 1 ≤ τ 1 := by
    rw [hτsum 1 (by omega)]
    have h0S : (0 : B.Integer) ∈ S := (hmemS 0).mpr (by rw [B.intNorm_zero]; linarith)
    have := Finset.single_le_sum (f := fun x => unitTent ((1 : ℤ) : ℝ) (B.intNorm x))
      (fun x _ => unitTent_nonneg _ _) h0S
    simp only [B.intNorm_zero, Int.cast_one] at this ⊢
    refine le_trans (le_of_eq ?_) this
    simp [unitTent]
  have hη : (18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2) * M ≤ 1 / 16 := by
    have h8 := tentConst_le_eight
    have hK0 : 0 ≤ 18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2 := by
      have := defectKernelConst_nonneg; positivity
    calc (18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2) * M ≤ 8 * (1 / 6400) :=
          mul_le_mul h8 hMsmall hM0 (by norm_num)
      _ ≤ 1 / 16 := by norm_num
  have hτ : ∀ n : ℤ, 1 ≤ n → n + 1 ≤ N →
      |τ n - 2 * β.re| ≤ (18 / Real.pi + 4 * defectKernelConst / Real.pi ^ 2) * M := by
    intro n hn _
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact abs_integral_unitTent_sub_le_of_critical_line_defect hsupp hmom hEc hEd hdecay hR' hC
      hgm hgb hgi hn'
  have hcnt1 : ∀ m : ℤ, 2 ≤ m → m + 2 ≤ N → cnt m = 1 :=
    cnt_eq_one_of_tent hη h0 h1 hτ1 hlow hup hτ (by exact_mod_cast hN)
  -- Exactly one atom of norm `≤ N` rounds to each `1 ≤ m ≤ N - 2`.
  have hU : ∀ m : ℤ, 1 ≤ m → m + 2 ≤ N →
      ∃! x : B.Integer, B.intNorm x ≤ N ∧ round (B.intNorm x) = m := by
    intro m hm hmN
    have hc : cnt m = 1 := by
      rcases eq_or_lt_of_le hm with h | h
      · rw [← h]; exact h1
      · exact hcnt1 m (by omega) hmN
    obtain ⟨x₀, hx₀⟩ := Finset.card_eq_one.mp hc
    have hmem : x₀ ∈ S.filter fun x => round (B.intNorm x) = m := by rw [hx₀]; simp
    rw [Finset.mem_filter] at hmem
    refine ⟨x₀, ⟨(hmemS x₀).mp hmem.1, hmem.2⟩, fun y hy => ?_⟩
    have hmy : y ∈ S.filter fun x => round (B.intNorm x) = m :=
      Finset.mem_filter.mpr ⟨(hmemS y).mpr hy.1, hy.2⟩
    rw [hx₀, Finset.mem_singleton] at hmy
    exact hmy
  have hround_ne_one : ∀ x : B.Integer, x ≠ 0 → B.intNorm x ≤ N → 2 ≤ round (B.intNorm x) :=
    fun x hx0 hx => two_le_round_intNorm hnear hρ0 hρN hN hx hx0
  have hnear8 : ∀ x : B.Integer, B.intNorm x ≤ N → |B.intNorm x - round (B.intNorm x)| ≤ 1 / 8 :=
    fun x hx => abs_sub_round_le_eighth hnear hρ0 hρN hx
  refine ⟨hnear_all, ?_, ?_⟩
  · -- Generalized integers.
    intro m hm hmN
    obtain ⟨x₀, ⟨hx₀N, hx₀r⟩, hx₀u⟩ := hU m (by exact_mod_cast hm) (by exact_mod_cast hmN)
    refine ⟨x₀, ?_, fun y hy => hx₀u y ?_⟩
    · have := hnear8 x₀ hx₀N
      rwa [hx₀r, Int.cast_natCast] at this
    · have hmN' : (m : ℝ) + 2 ≤ N := by exact_mod_cast hmN
      have hyN : B.intNorm y ≤ N := by linarith [(abs_le.mp hy).2]
      refine ⟨hyN, int_eq_of_abs_sub_lt_one ?_⟩
      have h8 := hnear8 y hyN
      rw [Int.cast_natCast]
      calc |(round (B.intNorm y) : ℝ) - m|
          = |(B.intNorm y - m) - (B.intNorm y - round (B.intNorm y))| := by ring_nf
        _ ≤ |B.intNorm y - m| + |B.intNorm y - round (B.intNorm y)| := abs_sub _ _
        _ < 1 := by linarith
  · -- Primes.
    have hsingleN : ∀ p : B.Label, B.labelNorm p < N - 3 / 2 → B.intNorm {p} ≤ N := by
      intro p hp; rw [B.intNorm_singleton]; linarith
    have hround_p : ∀ p : B.Label, B.labelNorm p < N - 3 / 2 →
        2 ≤ round (B.labelNorm p) ∧ round (B.labelNorm p) + 2 ≤ N := by
      intro p hp
      have h2 := hround_ne_one {p} (Multiset.singleton_ne_zero p) (hsingleN p hp)
      rw [B.intNorm_singleton] at h2
      refine ⟨h2, ?_⟩
      have h8 := hnear8 {p} (hsingleN p hp)
      rw [B.intNorm_singleton] at h8
      have hlt : (round (B.labelNorm p) : ℝ) < N - 1 := by linarith [(abs_le.mp h8).1]
      have hlt' : round (B.labelNorm p) < (N : ℤ) - 1 := by exact_mod_cast hlt
      omega
    -- A product of two rounds `≤ N - 2` is the round of a sum of norm `≤ N`.
    have hprod : ∀ a b : ℤ, 1 ≤ a → 1 ≤ b → a * b + 2 ≤ N →
        ∃ y : B.Integer, B.intNorm y ≤ N ∧ round (B.intNorm y) = a * b ∧
          ∃ ya yb : B.Integer, y = ya + yb ∧ round (B.intNorm ya) = a ∧
            round (B.intNorm yb) = b := by
      intro a b ha hb hab
      have haN : a + 2 ≤ N := by nlinarith
      have hbN : b + 2 ≤ N := by nlinarith
      obtain ⟨ya, ⟨hyaN, hyar⟩, -⟩ := hU a ha haN
      obtain ⟨yb, ⟨hybN, hybr⟩, -⟩ := hU b hb hbN
      have hA := intNorm_mul_one_sub_le hnear hyaN
      have hB := intNorm_mul_one_sub_le hnear hybN
      rw [hyar] at hA
      rw [hybr] at hB
      have hρ1 : ρ ≤ 1 / 32 := by nlinarith
      have hP0 : 0 ≤ B.intNorm ya * (1 - ρ) := by nlinarith [B.one_le_intNorm ya]
      have hQ0 : 0 ≤ B.intNorm yb * (1 - ρ) := by nlinarith [B.one_le_intNorm yb]
      have hab' : ((a * b : ℤ) : ℝ) + 2 ≤ N := by exact_mod_cast hab
      push_cast at hab'
      have hPQ : B.intNorm ya * B.intNorm yb * (1 - ρ) ^ 2 ≤ (N : ℝ) - 2 := by
        have := mul_le_mul hA hB hQ0 (by linarith)
        nlinarith
      have hsumN : B.intNorm (ya + yb) ≤ N := by
        rw [B.intNorm_add]
        by_contra hcon
        push Not at hcon
        have h1 : (1 - 2 * ρ) * N < (1 - 2 * ρ) * (B.intNorm ya * B.intNorm yb) :=
          mul_lt_mul_of_pos_left hcon (by linarith)
        have h2 : (1 - 2 * ρ) * (B.intNorm ya * B.intNorm yb) ≤
            B.intNorm ya * B.intNorm yb * (1 - ρ) ^ 2 := by
          have : 0 ≤ B.intNorm ya * B.intNorm yb := by
            have := B.intNorm_pos ya; have := B.intNorm_pos yb; positivity
          nlinarith [sq_nonneg ρ]
        nlinarith
      refine ⟨ya + yb, hsumN, ?_, ya, yb, rfl, hyar, hybr⟩
      rw [round_intNorm_add hnear hρ0 hρN hsumN, hyar, hybr]
    have hne_zero : ∀ y : B.Integer, B.intNorm y ≤ N → 2 ≤ round (B.intNorm y) → y ≠ 0 := by
      rintro y - h rfl
      rw [B.intNorm_zero, round_one] at h
      norm_num at h
    -- The forward map.
    have hfwd : ∀ p : {p : B.Label // B.labelNorm p < N - 3 / 2},
        (round (B.labelNorm p.1)).toNat.Prime ∧ (round (B.labelNorm p.1)).toNat + 2 ≤ N := by
      rintro ⟨p, hp⟩
      obtain ⟨h2, hN2⟩ := hround_p p hp
      set r := round (B.labelNorm p) with hr
      have hr0 : (r.toNat : ℤ) = r := Int.toNat_of_nonneg (by omega)
      refine ⟨?_, by omega⟩
      rw [Nat.prime_def_lt]
      refine ⟨by omega, fun m hm hdvd => ?_⟩
      obtain ⟨k, hk⟩ := hdvd
      by_contra hm1
      have hm0 : m ≠ 0 := by rintro rfl; omega
      have hm2 : 2 ≤ m := by omega
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hk' | hk'
        · interval_cases k <;> omega
        · exact hk'
      obtain ⟨y, hyN, hyr, ya, yb, rfl, hyar, hybr⟩ :=
        hprod m k (by omega) (by omega) (by
          have : ((m * k : ℕ) : ℤ) = (m : ℤ) * k := by push_cast; ring
          rw [← this, ← hk, hr0]; omega)
      -- `ya + yb` and `{p}` both round to `r`.
      have hyr' : round (B.intNorm (ya + yb)) = r := by
        rw [hyr, ← hr0, hk]; push_cast; ring
      have hpN := hsingleN p hp
      obtain ⟨z, -, hz⟩ := hU r (by omega) hN2
      have h1' := hz (ya + yb) ⟨hyN, hyr'⟩
      have h2' := hz {p} ⟨hpN, by rw [B.intNorm_singleton]⟩
      have heq : ya + yb = {p} := h1'.trans h2'.symm
      have hya0 := hne_zero ya ((intNorm_le_intNorm_add B ya yb).trans hyN) (by rw [hyar]; omega)
      have hyb0 : yb ≠ 0 := by
        have h := intNorm_le_intNorm_add B yb ya
        rw [add_comm] at h
        exact hne_zero yb (h.trans hyN) (by rw [hybr]; omega)
      have hcard := congrArg Multiset.card heq
      rw [Multiset.card_add, Multiset.card_singleton] at hcard
      have := Multiset.card_pos.mpr hya0
      have := Multiset.card_pos.mpr hyb0
      omega
    let f : {p : B.Label // B.labelNorm p < N - 3 / 2} → {q : ℕ // q.Prime ∧ q + 2 ≤ N} :=
      fun p => ⟨(round (B.labelNorm p.1)).toNat, hfwd p⟩
    have hf_round : ∀ p, ((f p : ℕ) : ℤ) = round (B.labelNorm p.1) := fun p =>
      Int.toNat_of_nonneg (by have := (hround_p p.1 p.2).1; omega)
    have hinj : Function.Injective f := by
      rintro ⟨p, hp⟩ ⟨p', hp'⟩ hpp
      have h := congrArg (fun q : {q : ℕ // q.Prime ∧ q + 2 ≤ N} => ((q : ℕ) : ℤ)) hpp
      simp only [hf_round] at h
      obtain ⟨h2, hN2⟩ := hround_p p hp
      obtain ⟨z, -, hz⟩ := hU (round (B.labelNorm p)) (by omega) hN2
      have e1 := hz {p} ⟨hsingleN p hp, by rw [B.intNorm_singleton]⟩
      have e2 := hz {p'} ⟨hsingleN p' hp', by rw [B.intNorm_singleton, h]⟩
      exact Subtype.ext (Multiset.singleton_inj.mp (e1.trans e2.symm))
    have hsurj : Function.Surjective f := by
      rintro ⟨q, hq, hqN⟩
      have hq2 := hq.two_le
      obtain ⟨x, ⟨hxN, hxr⟩, -⟩ := hU q (by exact_mod_cast hq.one_lt.le) (by exact_mod_cast hqN)
      have hx0 : x ≠ 0 := hne_zero x hxN (by rw [hxr]; exact_mod_cast hq2)
      have hcard1 : Multiset.card x = 1 := by
        by_contra hc
        obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hx0
        have hsplit : x = {p} + x.erase p := by
          rw [Multiset.singleton_add, Multiset.cons_erase hp]
        have hy0 : x.erase p ≠ 0 := by
          intro h0
          rw [h0, add_zero] at hsplit
          rw [hsplit, Multiset.card_singleton] at hc
          exact hc rfl
        have hxN' : B.intNorm ({p} + x.erase p) ≤ N := by rw [← hsplit]; exact hxN
        have hmul := round_intNorm_add hnear hρ0 hρN hxN'
        rw [← hsplit, hxr] at hmul
        have hpN : B.intNorm {p} ≤ N := (intNorm_le_intNorm_add B _ _).trans hxN'
        have hyN : B.intNorm (x.erase p) ≤ N := by
          have h := intNorm_le_intNorm_add B (x.erase p) {p}
          rw [add_comm] at h
          exact h.trans hxN'
        have ha := hround_ne_one {p} (Multiset.singleton_ne_zero p) hpN
        have hb := hround_ne_one (x.erase p) hy0 hyN
        set a := round (B.intNorm {p})
        set b := round (B.intNorm (x.erase p))
        have hq' : q = a.toNat * b.toNat := by
          have : ((a.toNat * b.toNat : ℕ) : ℤ) = a * b := by
            push_cast; rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
          omega
        exact Nat.not_prime_mul (by omega) (by omega) (hq' ▸ hq)
      obtain ⟨p, rfl⟩ := Multiset.card_eq_one.mp hcard1
      have hpr : round (B.labelNorm p) = q := by rw [← B.intNorm_singleton]; exact hxr
      have hplt : B.labelNorm p < N - 3 / 2 := by
        have h8 := hnear8 {p} hxN
        rw [B.intNorm_singleton, hpr] at h8
        have hqN' : (q : ℝ) + 2 ≤ N := by exact_mod_cast hqN
        push_cast at h8
        linarith [(abs_le.mp h8).2]
      refine ⟨⟨p, hplt⟩, Subtype.ext ?_⟩
      show (round (B.labelNorm p)).toNat = q
      rw [hpr]; simp
    refine ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun p => ?_⟩⟩
    show |B.labelNorm p.1 - ((f p : ℕ) : ℝ)| ≤ ρ * N
    have hcast : ((f p : ℕ) : ℝ) = (round (B.labelNorm p.1) : ℝ) := by
      rw [← hf_round p]; push_cast; rfl
    rw [hcast]
    have h := hnear_all {p.1}
    rw [B.intNorm_singleton] at h
    have hpN : B.labelNorm p.1 ≤ N := by linarith [p.2]
    exact h.trans (mul_le_mul_of_nonneg_left hpN hρ0)

end GaloisForLFunctions.ArithmeticPositiveDuality
