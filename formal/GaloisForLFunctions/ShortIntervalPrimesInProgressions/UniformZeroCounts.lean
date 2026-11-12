import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LocalZeroCount
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterSumsInShortWindows

/-!
# Zero counts and zero sums, uniformly in the modulus

For a primitive nonprincipal `χ` modulo `N`:

* **Reflection.** `ρ ↦ 1 − ρ` is a bijection, with multiplicity, from the zeros of `Λ(s, χ)` onto
  those of `Λ(s, χ⁻¹)` (`reflectZero`): the functional equation writes `Λ(·, χ)` as a nonvanishing
  entire factor times `Λ(1 − ·, χ⁻¹)`.
* **All zeros near a height.** The zeros with `|Im ρ − t| ≤ 1` number at most
  `2 C_N log(|t| + 3)`, `C_N = (log(162N) + 1)/log(39/37)` (`ncard_zeros_near_le`): the zeros with
  `Re ρ ≥ ½` by Jensen's formula, the others by reflection.
* **Zero sums.** If `x^{Re ρ − 1} ≤ E` for every zero with `|Im ρ| ≤ T + 1`, then
  `Σ_ρ x^{β−1} min(1, Y/(|ρ||1−ρ|)) ≤ 4C_N((T+1) log(T+3) E + 4Y/√T)` (`tsum_zeroShortWeight_le_uniform`):
  the zeros are grouped by `⌊|Im ρ|⌋`, and `Σ_{m > T} m^{−3/2} ≤ 2/√T` telescopes.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-! ### Reflection -/

/-- The reflection `z ↦ −z − 3` of the anchored variable, i.e. `ρ ↦ 1 − ρ`. -/
def reflectAnchor (z : ℂ) : ℂ := -z - 3

theorem reflectAnchor_reflectAnchor (z : ℂ) : reflectAnchor (reflectAnchor z) = z := by
  simp [reflectAnchor]

/-- The functional equation in the anchored variable:
`Λ(z + 2, χ) = N^{−z − 3/2} ε Λ(−z − 1, χ⁻¹)`. -/
theorem shiftedL_eq_reflect (hprim : χ.IsPrimitive) (z : ℂ) :
    shiftedL χ z = ((N : ℂ) ^ (-z - 3 / 2) * χ.rootNumber) * shiftedL χ⁻¹ (reflectAnchor z) := by
  have h := hprim.completedLFunction_one_sub (-z - 1)
  rw [show (1 : ℂ) - (-z - 1) = z + 2 by ring] at h
  rw [shiftedL, h, shiftedL, reflectAnchor, show -z - 3 + 2 = -z - 1 by ring,
    show -z - 1 - 1 / 2 = -z - 3 / 2 by ring]

theorem analyticOrderAt_shiftedL_reflect (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (z : ℂ) :
    analyticOrderAt (shiftedL χ) z = analyticOrderAt (shiftedL χ⁻¹) (reflectAnchor z) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set u : ℂ → ℂ := fun w => (N : ℂ) ^ (-w - 3 / 2) * χ.rootNumber with hu
  have hfeq : shiftedL χ = u * (shiftedL χ⁻¹ ∘ reflectAnchor) := by
    funext w
    simp only [Pi.mul_apply, Function.comp, hu]
    exact shiftedL_eq_reflect hprim w
  have hua : AnalyticAt ℂ u z := by
    have : Differentiable ℂ u := by
      intro w
      exact ((differentiableAt_id.neg.sub_const _).const_cpow (Or.inl hN0)).mul_const _
    exact this.analyticAt z
  have hu0 : u z ≠ 0 :=
    mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hN0)) (rootNumber_ne_zero hχ hprim)
  have hrefl : AnalyticAt ℂ reflectAnchor z := by
    unfold reflectAnchor
    fun_prop
  have hderiv : deriv reflectAnchor z ≠ 0 := by
    have : deriv reflectAnchor z = -1 := by
      unfold reflectAnchor
      simp
    rw [this]
    norm_num
  have hga : AnalyticAt ℂ (shiftedL χ⁻¹ ∘ reflectAnchor) z :=
    (analyticOnNhd_shiftedL (inv_ne_one hχ) _ (mem_univ _)).comp hrefl
  rw [hfeq, analyticOrderAt_mul hua hga,
    analyticOrderAt_eq_zero.mpr (Or.inr hu0), zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hrefl hderiv]

theorem divisor_shiftedL_reflect (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (z : ℂ) :
    MeromorphicOn.divisor (shiftedL χ) univ z
      = MeromorphicOn.divisor (shiftedL χ⁻¹) univ (reflectAnchor z) := by
  rw [divisor_univ_eq_analyticOrder (analyticOnNhd_shiftedL hχ),
    divisor_univ_eq_analyticOrder (analyticOnNhd_shiftedL (inv_ne_one hχ)),
    analyticOrderAt_shiftedL_reflect hχ hprim]

/-- The reflection of the zero supports. -/
def reflectSupport (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    ZeroSupport (shiftedL χ) ≃ ZeroSupport (shiftedL χ⁻¹) where
  toFun w := ⟨reflectAnchor w, by
    have := w.2
    simp only [Function.mem_support] at this ⊢
    rwa [← divisor_shiftedL_reflect hχ hprim]⟩
  invFun w := ⟨reflectAnchor w, by
    have := w.2
    simp only [Function.mem_support] at this ⊢
    rwa [divisor_shiftedL_reflect hχ hprim, reflectAnchor_reflectAnchor]⟩
  left_inv w := Subtype.ext (reflectAnchor_reflectAnchor _)
  right_inv w := Subtype.ext (reflectAnchor_reflectAnchor _)

/-- **Reflection of the zeros.** `ρ ↦ 1 − ρ` from the zeros of `Λ(·, χ)` onto those of
`Λ(·, χ⁻¹)`, with multiplicity. -/
def reflectZero (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) : LZero χ ≃ LZero χ⁻¹ :=
  Equiv.sigmaCongr (reflectSupport hχ hprim) fun w =>
    finCongr (by rw [divisor_shiftedL_reflect hχ hprim]; rfl)

theorem reflectZero_point (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (q : LZero χ) :
    (reflectZero hχ hprim q).point = 1 - q.point := by
  show ((reflectSupport hχ hprim q.1 : ZeroSupport (shiftedL χ⁻¹)) : ℂ) + 2 = 1 - ((q.1 : ℂ) + 2)
  simp only [reflectSupport, Equiv.coe_fn_mk, reflectAnchor]
  ring

/-! ### Counting -/

/-- **All zeros near a height.** -/
theorem ncard_zeros_near_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℝ) :
    {q : LZero χ | |q.point.im - t| ≤ 1}.Finite ∧
      ({q : LZero χ | |q.point.im - t| ≤ 1}.ncard : ℝ)
        ≤ 2 * localCountConst N * Real.log (|t| + 3) := by
  set A := {q : LZero χ | 1 / 2 ≤ q.point.re ∧ |q.point.im - t| ≤ 1} with hA
  set B := {q : LZero χ | q.point.re < 1 / 2 ∧ |q.point.im - t| ≤ 1} with hB
  set B' := {q : LZero χ⁻¹ | 1 / 2 ≤ q.point.re ∧ |q.point.im - (-t)| ≤ 1} with hB'
  obtain ⟨hAfin, hAcard⟩ := card_zeros_near_le_explicit hχ t
  obtain ⟨hB'fin, hB'card⟩ := card_zeros_near_le_explicit (inv_ne_one hχ) (-t)
  rw [abs_neg] at hB'card
  have himg : (reflectZero hχ hprim) '' B ⊆ B' := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    rw [hB', mem_setOf_eq, reflectZero_point]
    simp only [sub_re, one_re, sub_im, one_im, zero_sub]
    constructor
    · linarith
    · rw [show -q.point.im - -t = -(q.point.im - t) by ring, abs_neg]
      exact hq2
  have hBfin : B.Finite :=
    Finite.of_finite_image (hB'fin.subset himg) (reflectZero hχ hprim).injective.injOn
  have hBcard : (B.ncard : ℝ) ≤ B'.ncard := by
    rw [← ncard_image_of_injective B (reflectZero hχ hprim).injective]
    exact_mod_cast ncard_le_ncard himg hB'fin
  have hunion : {q : LZero χ | |q.point.im - t| ≤ 1} = A ∪ B := by
    ext q
    simp only [hA, hB, mem_setOf_eq, mem_union]
    constructor
    · intro h
      rcases le_or_gt (1 / 2) q.point.re with h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact Or.inr ⟨h', h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  rw [hunion]
  refine ⟨hAfin.union hBfin, ?_⟩
  calc ((A ∪ B).ncard : ℝ) ≤ (A.ncard : ℝ) + B.ncard := by
        exact_mod_cast ncard_union_le A B
    _ ≤ localCountConst N * Real.log (|t| + 3) + localCountConst N * Real.log (|t| + 3) :=
        add_le_add hAcard (hBcard.trans hB'card)
    _ = 2 * localCountConst N * Real.log (|t| + 3) := by ring

/-- The zeros with `⌊|Im ρ|⌋ = m`. -/
theorem ncard_zeros_floor_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (m : ℕ) :
    {q : LZero χ | ⌊|q.point.im|⌋₊ = m}.Finite ∧
      ({q : LZero χ | ⌊|q.point.im|⌋₊ = m}.ncard : ℝ)
        ≤ 4 * localCountConst N * Real.log (m + 3) := by
  obtain ⟨h1f, h1c⟩ := ncard_zeros_near_le hχ hprim (m : ℝ)
  obtain ⟨h2f, h2c⟩ := ncard_zeros_near_le hχ hprim (-(m : ℝ))
  have hsub : {q : LZero χ | ⌊|q.point.im|⌋₊ = m}
      ⊆ {q : LZero χ | |q.point.im - m| ≤ 1} ∪ {q : LZero χ | |q.point.im - (-(m : ℝ))| ≤ 1} := by
    intro q hq
    rw [mem_setOf_eq] at hq
    have hlo : (m : ℝ) ≤ |q.point.im| := by
      rw [← hq]
      exact Nat.floor_le (abs_nonneg _)
    have hhi : |q.point.im| < m + 1 := by
      rw [← hq]
      exact Nat.lt_floor_add_one _
    rcases le_or_gt 0 q.point.im with h | h
    · left
      rw [mem_setOf_eq, abs_le]
      rw [abs_of_nonneg h] at hlo hhi
      constructor <;> linarith
    · right
      rw [mem_setOf_eq, abs_le]
      rw [abs_of_neg h] at hlo hhi
      constructor <;> linarith
  have hfin := h1f.union h2f
  refine ⟨hfin.subset hsub, ?_⟩
  have habs : |(-(m : ℝ))| = m := by rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
  rw [habs] at h2c
  rw [abs_of_nonneg (Nat.cast_nonneg m)] at h1c
  calc (({q : LZero χ | ⌊|q.point.im|⌋₊ = m}).ncard : ℝ)
      ≤ ((({q : LZero χ | |q.point.im - m| ≤ 1} ∪
          {q : LZero χ | |q.point.im - (-(m : ℝ))| ≤ 1})).ncard : ℝ) := by
        exact_mod_cast ncard_le_ncard hsub hfin
    _ ≤ (({q : LZero χ | |q.point.im - m| ≤ 1}).ncard : ℝ)
        + (({q : LZero χ | |q.point.im - (-(m : ℝ))| ≤ 1}).ncard : ℝ) := by
        exact_mod_cast ncard_union_le _ _
    _ ≤ 4 * localCountConst N * Real.log (m + 3) := by linarith

/-! ### Zero sums -/

/-- `m^{−3/2} ≤ 2(1/√(m−1) − 1/√m)` for `m ≥ 2`. -/
theorem rpow_neg_three_halves_le {m : ℝ} (hm : 2 ≤ m) :
    m ^ (-(3 / 2 : ℝ)) ≤ 2 * (1 / Real.sqrt (m - 1) - 1 / Real.sqrt m) := by
  have hm1 : 0 < m - 1 := by linarith
  set a := Real.sqrt (m - 1) with ha_def
  set b := Real.sqrt m with hb_def
  have ha : 0 < a := Real.sqrt_pos.mpr hm1
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hsqa : a ^ 2 = m - 1 := Real.sq_sqrt hm1.le
  have hsqb : b ^ 2 = m := Real.sq_sqrt (by linarith)
  have hpow : m ^ (-(3 / 2 : ℝ)) = 1 / (m * b) := by
    rw [Real.rpow_neg (by linarith), show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
  have key : (b - a) * (b + a) = 1 := by nlinarith
  rw [hpow, div_le_iff₀ (by positivity)]
  have e : 2 * (1 / a - 1 / b) * (m * b) = 2 * (b - a) * m / a := by
    field_simp
  rw [e, le_div_iff₀ ha, one_mul]
  nlinarith [mul_nonneg (sq_nonneg (b - a)) (by positivity : (0 : ℝ) ≤ 2 * b + a)]

/-- `Σ_{T < m ≤ M} m^{−3/2} ≤ 2/√T`. -/
theorem sum_Ioc_rpow_neg_three_halves_le {T : ℕ} (hT : 1 ≤ T) (M : ℕ) :
    ∑ m ∈ Finset.Ioc T M, (m : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 / Real.sqrt T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hinv : ∀ M : ℕ, T ≤ M → ∑ m ∈ Finset.Ioc T M, (m : ℝ) ^ (-(3 / 2 : ℝ))
      ≤ 2 * (1 / Real.sqrt T - 1 / Real.sqrt M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ioc_succ_top (by omega)]
      have hM2 : (2 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ M := by exact_mod_cast (le_trans hT hM)
        push_cast
        linarith
      have h := rpow_neg_three_halves_le hM2
      rw [show ((M + 1 : ℕ) : ℝ) - 1 = M by push_cast; ring] at h
      linarith
  rcases le_or_gt T M with hTM | hTM
  · refine (hinv M hTM).trans ?_
    have : 0 ≤ 1 / Real.sqrt M := by positivity
    rw [show 2 / Real.sqrt T = 2 * (1 / Real.sqrt T) by ring]
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- `log(m + 3) ≤ 4√m` for `m ≥ 1`. -/
theorem log_add_three_le_four_sqrt {m : ℝ} (hm : 1 ≤ m) : Real.log (m + 3) ≤ 4 * Real.sqrt m := by
  have h1 : Real.log (m + 3) ≤ 2 * Real.sqrt (m + 3) := by
    have hs : 0 < Real.sqrt (m + 3) := Real.sqrt_pos.mpr (by linarith)
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt (by linarith)] at this
    linarith
  have h2 : Real.sqrt (m + 3) ≤ 2 * Real.sqrt m := by
    rw [show 2 * Real.sqrt m = Real.sqrt (4 * m) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith

/-- **The zero sum, uniformly in the modulus.** -/
theorem tsum_zeroShortWeight_le_uniform (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {x Y E : ℝ}
    (hx : 1 ≤ x) (hY : 0 ≤ Y) (hE0 : 0 ≤ E) {T : ℕ} (hT : 1 ≤ T)
    (hE : ∀ q : LZero χ, |q.point.im| ≤ T + 1 → x ^ (q.point.re - 1) ≤ E) :
    ∑' q : LZero χ, RHTower.zeroShortWeight x Y q.point
      ≤ 4 * localCountConst N * ((T + 1) * Real.log (T + 3) * E + 8 * Y / Real.sqrt T) := by
  classical
  have hC : 0 ≤ localCountConst N :=
    localCountConst_nonneg (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hsum := summable_zeroShortWeight hχ hprim (x := x) hx hY
  set fl : LZero χ → ℕ := fun q => ⌊|q.point.im|⌋₊ with hfl
  set bnd : ℕ → ℝ := fun m => if m ≤ T then E else Y * (m : ℝ) ^ (-(2 : ℝ)) with hbnd
  have hw : ∀ q : LZero χ, RHTower.zeroShortWeight x Y q.point ≤ bnd (fl q) := by
    intro q
    have hre := zero_re_mem hχ hprim q
    have hx1 : x ^ (q.point.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
    have hx0 : 0 ≤ x ^ (q.point.re - 1) := Real.rpow_nonneg (by linarith) _
    unfold RHTower.zeroShortWeight
    simp only [hbnd]
    split_ifs with hm
    · have hγ : |q.point.im| ≤ T + 1 := by
        have := Nat.lt_floor_add_one (|q.point.im|)
        have hmR : ((fl q : ℕ) : ℝ) ≤ T := by exact_mod_cast hm
        simp only [hfl] at hmR
        linarith
      calc x ^ (q.point.re - 1) * min 1 (Y / (‖q.point‖ * ‖1 - q.point‖))
          ≤ x ^ (q.point.re - 1) * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hx0
        _ ≤ E := by rw [mul_one]; exact hE q hγ
    · have hm1 : (1 : ℝ) ≤ fl q := by
        have : 1 ≤ fl q := by omega
        exact_mod_cast this
      have hmγ : ((fl q : ℕ) : ℝ) ≤ |q.point.im| := Nat.floor_le (abs_nonneg _)
      have h1 : |q.point.im| ≤ ‖q.point‖ := Complex.abs_im_le_norm _
      have h2 : |q.point.im| ≤ ‖1 - q.point‖ := by
        have := Complex.abs_im_le_norm (1 - q.point)
        simpa [sub_im, abs_neg] using this
      have hprod : ((fl q : ℕ) : ℝ) ^ (2 : ℝ) ≤ ‖q.point‖ * ‖1 - q.point‖ := by
        rw [Real.rpow_two, sq]
        exact mul_le_mul (hmγ.trans h1) (hmγ.trans h2) (by positivity) (norm_nonneg _)
      have hmpos : (0 : ℝ) < ((fl q : ℕ) : ℝ) ^ (2 : ℝ) := by positivity
      calc x ^ (q.point.re - 1) * min 1 (Y / (‖q.point‖ * ‖1 - q.point‖))
          ≤ 1 * (Y / (‖q.point‖ * ‖1 - q.point‖)) :=
            mul_le_mul hx1 (min_le_right _ _) (le_min zero_le_one (by positivity)) zero_le_one
        _ ≤ Y * ((fl q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
            rw [one_mul, Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
            exact div_le_div_of_nonneg_left hY hmpos hprod
  refine hsum.tsum_le_of_sum_le fun F => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem fl hq)]
  have hfiber : ∀ m ∈ F.image fl, ∑ q ∈ F with fl q = m, RHTower.zeroShortWeight x Y q.point
      ≤ 4 * localCountConst N * Real.log (m + 3) * bnd m := by
    intro m _
    obtain ⟨hfin, hcard⟩ := ncard_zeros_floor_le hχ hprim m
    have hbnd0 : 0 ≤ bnd m := by
      simp only [hbnd]
      split_ifs
      · exact hE0
      · positivity
    calc ∑ q ∈ F with fl q = m, RHTower.zeroShortWeight x Y q.point
        ≤ ∑ q ∈ F with fl q = m, bnd m := Finset.sum_le_sum fun q hq => by
          rw [← (Finset.mem_filter.mp hq).2]
          exact hw q
      _ = ((F.filter fun q => fl q = m).card : ℝ) * bnd m := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (({q : LZero χ | ⌊|q.point.im|⌋₊ = m}).ncard : ℝ) * bnd m := by
          refine mul_le_mul_of_nonneg_right ?_ hbnd0
          have hsub : ((F.filter fun q => fl q = m) : Set (LZero χ))
              ⊆ {q : LZero χ | ⌊|q.point.im|⌋₊ = m} := fun q hq =>
            (Finset.mem_filter.mp hq).2
          rw [← Set.ncard_coe_finset]
          exact_mod_cast Set.ncard_le_ncard hsub hfin
      _ ≤ 4 * localCountConst N * Real.log (m + 3) * bnd m :=
          mul_le_mul_of_nonneg_right hcard hbnd0
  refine (Finset.sum_le_sum hfiber).trans ?_
  set g : ℕ → ℝ := fun m => 4 * localCountConst N * Real.log (m + 3) * bnd m with hg
  have hg0 : ∀ m, 0 ≤ g m := by
    intro m
    simp only [hg, hbnd]
    have : 0 ≤ Real.log ((m : ℝ) + 3) := Real.log_nonneg (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    split_ifs
    · positivity
    · positivity
  set Mx := (F.image fl).sup id with hMx
  have hsub : F.image fl ⊆ Finset.range (T + 1) ∪ Finset.Ioc T Mx := by
    intro m hm
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    have : m ≤ Mx := Finset.le_sup (f := id) hm
    omega
  calc ∑ m ∈ F.image fl, g m ≤ ∑ m ∈ Finset.range (T + 1) ∪ Finset.Ioc T Mx, g m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hg0 m
    _ = ∑ m ∈ Finset.range (T + 1), g m + ∑ m ∈ Finset.Ioc T Mx, g m := by
        have hdisj : Disjoint (Finset.range (T + 1)) (Finset.Ioc T Mx) := by
          rw [Finset.disjoint_left]
          intro m h1 h2
          rw [Finset.mem_range] at h1
          rw [Finset.mem_Ioc] at h2
          omega
        exact Finset.sum_union hdisj
    _ ≤ 4 * localCountConst N * ((T + 1) * Real.log (T + 3) * E)
        + 4 * localCountConst N * (8 * Y / Real.sqrt T) := by
        refine add_le_add ?_ ?_
        · calc ∑ m ∈ Finset.range (T + 1), g m
              ≤ ∑ _m ∈ Finset.range (T + 1), 4 * localCountConst N * Real.log (T + 3) * E := by
                refine Finset.sum_le_sum fun m hm => ?_
                have hmT : m ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
                simp only [hg, hbnd, if_pos hmT]
                have hlog : Real.log ((m : ℝ) + 3) ≤ Real.log ((T : ℝ) + 3) :=
                  Real.log_le_log (by positivity) (by
                    have : (m : ℝ) ≤ T := by exact_mod_cast hmT
                    linarith)
                have h4 : 0 ≤ 4 * localCountConst N := by positivity
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog h4) hE0
            _ = 4 * localCountConst N * ((T + 1) * Real.log (T + 3) * E) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                push_cast
                ring
        · calc ∑ m ∈ Finset.Ioc T Mx, g m
              ≤ ∑ m ∈ Finset.Ioc T Mx, 4 * localCountConst N * (4 * Y * (m : ℝ) ^ (-(3 / 2 : ℝ))) := by
                refine Finset.sum_le_sum fun m hm => ?_
                have hmT : T < m := (Finset.mem_Ioc.mp hm).1
                have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
                simp only [hg, hbnd, if_neg (show ¬ m ≤ T by omega)]
                have hlog := log_add_three_le_four_sqrt hm1
                have hsq : Real.sqrt (m : ℝ) * (m : ℝ) ^ (-(2 : ℝ)) = (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
                  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
                  norm_num
                have hpos : 0 ≤ (m : ℝ) ^ (-(2 : ℝ)) := by positivity
                calc 4 * localCountConst N * Real.log ((m : ℝ) + 3) * (Y * (m : ℝ) ^ (-(2 : ℝ)))
                    ≤ 4 * localCountConst N * (4 * Real.sqrt m) * (Y * (m : ℝ) ^ (-(2 : ℝ))) := by
                      gcongr
                  _ = 4 * localCountConst N * (4 * Y * (Real.sqrt m * (m : ℝ) ^ (-(2 : ℝ)))) := by
                      ring
                  _ = _ := by rw [hsq]
            _ = 4 * localCountConst N * (4 * Y) * ∑ m ∈ Finset.Ioc T Mx, (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun m _ => ?_
                ring
            _ ≤ 4 * localCountConst N * (4 * Y) * (2 / Real.sqrt T) :=
                mul_le_mul_of_nonneg_left (sum_Ioc_rpow_neg_three_halves_le hT Mx) (by positivity)
            _ = 4 * localCountConst N * (8 * Y / Real.sqrt T) := by ring
    _ = 4 * localCountConst N * ((T + 1) * Real.log (T + 3) * E + 8 * Y / Real.sqrt T) := by
        ring

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
