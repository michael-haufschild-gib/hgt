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

end GaloisForLFunctions.ArithmeticPositiveDuality
