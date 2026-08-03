import Mathlib

/-!
# How often a nondecreasing function can jump

A nondecreasing function has a total increase, and every place where it rises by at least `c` over a
step of length `l` consumes part of that budget.  Averaging the increment over the interval turns
this into a measure bound: the set of `x` in `[a, A]` at which `T(x + l) - T(x) >= c` has Lebesgue
measure at most `l (T(A + l) - T(a)) / c`.

The proof is Chebyshev's inequality applied to the nonnegative increment `x -> T(x + l) - T(x)`,
whose integral over `[a, A]` telescopes: translating the first term shows it equals
`int_A^{A+l} T - int_a^{a+l} T`, and monotonicity bounds that by `l (T(A + l) - T(a))`.

This is the quantitative form of "a monotone function is differentiable almost everywhere" that a
Wiman--Valiron argument needs: it controls the modulus of continuity of the central index at a fixed
scale, which no doubling lemma can do.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.Nevanlinna

variable {T : ℝ → ℝ}

/-- The increment of a nondecreasing function over a positive step is nonnegative. -/
private theorem increment_nonneg (hmono : Monotone T) {l : ℝ} (hl : 0 ≤ l) (x : ℝ) :
    0 ≤ T (x + l) - T x :=
  sub_nonneg.mpr (hmono (by linarith))

/-- **The increment integral telescopes.**  Shifting the first term turns the integral of the
increment into the difference of the integrals over the two end blocks. -/
theorem integral_increment_eq (hmono : Monotone T) {a A l : ℝ} (_haA : a ≤ A) (_hl : 0 ≤ l) :
    ∫ x in a..A, (T (x + l) - T x)
      = (∫ x in A..(A + l), T x) - ∫ x in a..(a + l), T x := by
  have hint : ∀ u v : ℝ, IntervalIntegrable T volume u v := fun u v =>
    (hmono.monotoneOn _).intervalIntegrable
  have hshift : IntervalIntegrable (fun x => T (x + l)) volume a A := by
    have := (hint (a + l) (A + l)).comp_add_right l
    simpa using this
  rw [intervalIntegral.integral_sub hshift (hint a A)]
  have hcomp : ∫ x in a..A, T (x + l) = ∫ x in (a + l)..(A + l), T x := by
    simp
  rw [hcomp]
  have h1 : (∫ x in a..(a + l), T x) + ∫ x in (a + l)..(A + l), T x = ∫ x in a..(A + l), T x :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have h2 : (∫ x in a..A, T x) + ∫ x in A..(A + l), T x = ∫ x in a..(A + l), T x :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  linarith

/-- The integral of the increment is at most the step length times the total rise. -/
theorem integral_increment_le (hmono : Monotone T) {a A l : ℝ} (haA : a ≤ A) (hl : 0 ≤ l) :
    (∫ x in a..A, (T (x + l) - T x)) ≤ l * (T (A + l) - T a) := by
  have hint : ∀ u v : ℝ, IntervalIntegrable T volume u v := fun u v =>
    (hmono.monotoneOn _).intervalIntegrable
  have hAl : A ≤ A + l := by linarith
  have hal : a ≤ a + l := by linarith
  have hup : (∫ x in A..(A + l), T x) ≤ l * T (A + l) := by
    have h := intervalIntegral.integral_mono_on (f := T) (g := fun _ => T (A + l))
      hAl (hint _ _) intervalIntegrable_const (fun x hx => hmono hx.2)
    rw [intervalIntegral.integral_const] at h
    simpa [smul_eq_mul] using h
  have hlow : l * T a ≤ ∫ x in a..(a + l), T x := by
    have h := intervalIntegral.integral_mono_on (f := fun _ => T a) (g := T)
      hal intervalIntegrable_const (hint _ _) (fun x hx => hmono hx.1)
    rw [intervalIntegral.integral_const] at h
    simpa [smul_eq_mul] using h
  rw [integral_increment_eq hmono haA hl]
  linarith

/-- **The jump-set measure bound.**  For a nondecreasing `T`, the set of points of `[a, A]` where
`T` rises by at least `c` over a step of length `l` has measure at most `l (T(A+l) - T(a)) / c`. -/
theorem volume_increment_ge_le (hmono : Monotone T) {a A l c : ℝ}
    (haA : a ≤ A) (hl : 0 ≤ l) (hc : 0 < c) :
    (volume {x ∈ Icc a A | c ≤ T (x + l) - T x}).toReal ≤ l * (T (A + l) - T a) / c := by
  classical
  set g : ℝ → ℝ := fun x => T (x + l) - T x with hg
  set E : Set ℝ := {x ∈ Icc a A | c ≤ g x} with hE
  have hmeasT : Measurable T := hmono.measurable
  have hmeasg : Measurable g := (hmeasT.comp (measurable_id.add_const l)).sub hmeasT
  have hEmeas : MeasurableSet E :=
    (measurableSet_Icc).inter (hmeasg (measurableSet_Ici (a := c)))
  have hEsub : E ⊆ Icc a A := fun x hx => hx.1
  have hEfin : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hEsub)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hgnn : ∀ x, 0 ≤ g x := fun x => increment_nonneg hmono hl x
  have hint : ∀ u v : ℝ, IntervalIntegrable T volume u v := fun u v =>
    (hmono.monotoneOn _).intervalIntegrable
  have hshift : IntervalIntegrable (fun x => T (x + l)) volume a A := by
    have := (hint (a + l) (A + l)).comp_add_right l
    simpa using this
  have hgint : IntegrableOn g (Icc a A) volume := by
    have h : IntervalIntegrable g volume a A := hshift.sub (hint a A)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haA] at h
    exact h
  have hgintE : IntegrableOn g E volume := hgint.mono_set hEsub
  -- Chebyshev on `E`
  have hlow : (volume E).toReal * c ≤ ∫ x in E, g x := by
    have hfin : IsFiniteMeasure (volume.restrict E) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_ne le_top hEfin
    have hconst : IntegrableOn (fun _ : ℝ => c) E volume := integrable_const c
    have h := setIntegral_mono_on hconst hgintE hEmeas (fun x hx => hx.2)
    rw [setIntegral_const] at h
    simpa [measureReal_def, smul_eq_mul] using h
  -- and comparison with the whole interval
  have hIcc : ∫ x in E, g x ≤ ∫ x in Icc a A, g x := by
    refine setIntegral_mono_set hgint (Filter.Eventually.of_forall hgnn) ?_
    exact Filter.Eventually.of_forall hEsub
  have hIccval : ∫ x in Icc a A, g x = ∫ x in a..A, g x := by
    rw [intervalIntegral.integral_of_le haA, ← integral_Icc_eq_integral_Ioc]
  have htotal : (∫ x in a..A, g x) ≤ l * (T (A + l) - T a) :=
    integral_increment_le hmono haA hl
  have hchain : (volume E).toReal * c ≤ l * (T (A + l) - T a) := by
    calc (volume E).toReal * c ≤ ∫ x in E, g x := hlow
      _ ≤ ∫ x in Icc a A, g x := hIcc
      _ = ∫ x in a..A, g x := hIccval
      _ ≤ l * (T (A + l) - T a) := htotal
  rw [le_div_iff₀ hc]
  exact hchain

/-- The jump-set bound in extended-real form. -/
theorem volume_increment_ge_le' (hmono : Monotone T) {a A l c : ℝ}
    (haA : a ≤ A) (hl : 0 ≤ l) (hc : 0 < c) :
    volume {x ∈ Icc a A | c ≤ T (x + l) - T x}
      ≤ ENNReal.ofReal (l * (T (A + l) - T a) / c) := by
  have hEsub : {x ∈ Icc a A | c ≤ T (x + l) - T x} ⊆ Icc a A := fun x hx => hx.1
  have hEfin : volume {x ∈ Icc a A | c ≤ T (x + l) - T x} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hEsub)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hEfin]
  exact ENNReal.ofReal_le_ofReal (volume_increment_ge_le hmono haA hl hc)

/-! ## All scales at once

Running the jump bound along the dyadic scales `H / 2^j` with tolerances weighted by a summable
sequence gives a single exceptional set outside which the function is Lipschitz at every dyadic
scale, with a constant that degrades only by the chosen weight. -/

/-- **The dyadic jump set is small.**  If the tolerance at scale `H / 2^j` is `Lambda w j` times the
scale, the union over all scales of the sets where the tolerance is exceeded has measure at most
`(T(A + H) - T(a)) / Lambda` times the sum of the reciprocal weights. -/
theorem volume_dyadic_jump_le (hmono : Monotone T) {a A H Λ : ℝ} (haA : a ≤ A) (hH : 0 < H)
    (hΛ : 0 < Λ) {w : ℕ → ℝ} (hw : ∀ j, 0 < w j) (hwsum : Summable fun j => (w j)⁻¹) :
    volume {x ∈ Icc a A |
        ∃ j : ℕ, Λ * w j * (H / 2 ^ j) ≤ T (x + H / 2 ^ j) - T x}
      ≤ ENNReal.ofReal ((T (A + H) - T a) / Λ * ∑' j : ℕ, (w j)⁻¹) := by
  classical
  set S : ℕ → Set ℝ := fun j =>
    {x ∈ Icc a A | Λ * w j * (H / 2 ^ j) ≤ T (x + H / 2 ^ j) - T x} with hS
  have hcover : {x ∈ Icc a A |
      ∃ j : ℕ, Λ * w j * (H / 2 ^ j) ≤ T (x + H / 2 ^ j) - T x} ⊆ ⋃ j, S j := by
    rintro x ⟨hx, j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hx, hj⟩
  have hrise : (0 : ℝ) ≤ T (A + H) - T a :=
    sub_nonneg.mpr (hmono (by linarith))
  have hstep : ∀ j : ℕ, volume (S j) ≤ ENNReal.ofReal ((T (A + H) - T a) / Λ * (w j)⁻¹) := by
    intro j
    have hpow : (0 : ℝ) < 2 ^ j := by positivity
    have hl : (0 : ℝ) ≤ H / 2 ^ j := by positivity
    have hlH : H / 2 ^ j ≤ H :=
      div_le_self hH.le (one_le_pow₀ (by norm_num))
    have hc : 0 < Λ * w j * (H / 2 ^ j) := by
      have := hw j
      positivity
    refine le_trans (volume_increment_ge_le' hmono haA hl hc) (ENNReal.ofReal_le_ofReal ?_)
    have hmono' : T (A + H / 2 ^ j) - T a ≤ T (A + H) - T a := by
      have : T (A + H / 2 ^ j) ≤ T (A + H) := hmono (by linarith)
      linarith
    have hlpos : (0 : ℝ) < H / 2 ^ j := by positivity
    calc H / 2 ^ j * (T (A + H / 2 ^ j) - T a) / (Λ * w j * (H / 2 ^ j))
        ≤ H / 2 ^ j * (T (A + H) - T a) / (Λ * w j * (H / 2 ^ j)) := by
          gcongr
      _ = (T (A + H) - T a) / Λ * (w j)⁻¹ := by
          field_simp
  have hsum : volume (⋃ j, S j) ≤ ∑' j : ℕ, volume (S j) := measure_iUnion_le _
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (T (A + H) - T a) / Λ * (w j)⁻¹ := by
    intro j
    have := (hw j).le
    positivity
  have hsummable : Summable fun j : ℕ => (T (A + H) - T a) / Λ * (w j)⁻¹ :=
    hwsum.mul_left _
  calc volume {x ∈ Icc a A |
        ∃ j : ℕ, Λ * w j * (H / 2 ^ j) ≤ T (x + H / 2 ^ j) - T x}
      ≤ volume (⋃ j, S j) := measure_mono hcover
    _ ≤ ∑' j : ℕ, volume (S j) := hsum
    _ ≤ ∑' j : ℕ, ENNReal.ofReal ((T (A + H) - T a) / Λ * (w j)⁻¹) :=
        ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal (∑' j : ℕ, (T (A + H) - T a) / Λ * (w j)⁻¹) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn hsummable).symm
    _ = ENNReal.ofReal ((T (A + H) - T a) / Λ * ∑' j : ℕ, (w j)⁻¹) := by
        rw [tsum_mul_left]

/-- **From dyadic scales to all scales.**  If the increment beats the tolerance at every dyadic
scale `H / 2^j`, then at an arbitrary scale `u <= H` it beats twice the tolerance carried by the
first dyadic scale above `u`; the index `j` is pinned down by `2^j u <= H`. -/
theorem exists_dyadic_index_increment_le (hmono : Monotone T) {x H Λ : ℝ} (hH : 0 < H)
    {w : ℕ → ℝ}
    (hgood : ∀ j : ℕ, T (x + H / 2 ^ j) - T x < Λ * w j * (H / 2 ^ j))
    {u : ℝ} (hu : 0 < u) (huH : u ≤ H) :
    ∃ j : ℕ, (2 : ℝ) ^ j * u ≤ H ∧ T (x + u) - T x < 2 * (Λ * w j) * u := by
  classical
  have hex : ∃ j : ℕ, H / 2 ^ (j + 1) < u := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hu hH) (by norm_num : (1 : ℝ) / 2 < 1)
    have hnpos : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, lt_div_iff₀ hH] at hn
      nlinarith
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨m, ?_⟩
    have hpow : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    rw [div_lt_iff₀ hpow]
    have hrw : ((1 : ℝ) / 2) ^ (m + 1) = 1 / 2 ^ (m + 1) := by
      rw [div_pow, one_pow]
    rw [hrw, div_lt_div_iff₀ hpow hH] at hn
    nlinarith
  refine ⟨Nat.find hex, ?_, ?_⟩
  · have hle : u ≤ H / 2 ^ Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0, pow_zero, div_one]; exact huH
      · have hnot := Nat.find_min hex (Nat.pred_lt hpos.ne')
        have hp1 : (Nat.find hex).pred + 1 = Nat.find hex := by
          rw [Nat.pred_eq_sub_one]; omega
        rw [hp1] at hnot
        exact not_lt.mp hnot
    have hpow : (0 : ℝ) < 2 ^ Nat.find hex := by positivity
    rw [le_div_iff₀ hpow] at hle
    linarith [hle]
  · have hspec := Nat.find_spec hex
    have hpow : (0 : ℝ) < 2 ^ (Nat.find hex + 1) := by positivity
    have hhalf : H / 2 ^ Nat.find hex < 2 * u := by
      have : H / 2 ^ (Nat.find hex + 1) * 2 = H / 2 ^ Nat.find hex := by
        rw [pow_succ, ← div_div, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      linarith [(mul_lt_mul_of_pos_right hspec (by norm_num : (0 : ℝ) < 2))]
    have hstep : T (x + u) - T x ≤ T (x + H / 2 ^ Nat.find hex) - T x := by
      have hle : u ≤ H / 2 ^ Nat.find hex := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
        · rw [h0, pow_zero, div_one]; exact huH
        · have hnot := Nat.find_min hex (Nat.pred_lt hpos.ne')
          have hp1 : (Nat.find hex).pred + 1 = Nat.find hex := by
            rw [Nat.pred_eq_sub_one]; omega
          rw [hp1] at hnot
          exact not_lt.mp hnot
      have := hmono (show x + u ≤ x + H / 2 ^ Nat.find hex by linarith)
      linarith
    have hg := hgood (Nat.find hex)
    rcases le_or_gt (Λ * w (Nat.find hex)) 0 with hneg | hposΛ
    · exfalso
      have hpow0 : (0 : ℝ) < H / 2 ^ Nat.find hex := by positivity
      have hnn : (0 : ℝ) ≤ T (x + H / 2 ^ Nat.find hex) - T x :=
        sub_nonneg.mpr (hmono (by linarith))
      nlinarith
    · nlinarith

/-- **A point where no dyadic scale jumps.**  If the exceptional measure is smaller than the length
of the sampling interval, some point of the interval survives every dyadic scale. -/
theorem exists_good_point_of_measure_lt (hmono : Monotone T) {a A H Λ : ℝ} (haA : a ≤ A)
    (hH : 0 < H) (hΛ : 0 < Λ) {w : ℕ → ℝ} (hw : ∀ j, 0 < w j)
    (hwsum : Summable fun j : ℕ => (w j)⁻¹)
    (hsmall : (T (A + H) - T a) / Λ * ∑' j : ℕ, (w j)⁻¹ < A - a) :
    ∃ x ∈ Icc a A, ∀ j : ℕ, T (x + H / 2 ^ j) - T x < Λ * w j * (H / 2 ^ j) := by
  classical
  set E : Set ℝ := {x ∈ Icc a A |
      ∃ j : ℕ, Λ * w j * (H / 2 ^ j) ≤ T (x + H / 2 ^ j) - T x} with hE
  have hbound := volume_dyadic_jump_le hmono haA hH hΛ hw hwsum
  have hnn : (0 : ℝ) ≤ (T (A + H) - T a) / Λ * ∑' j : ℕ, (w j)⁻¹ := by
    have hrise : (0 : ℝ) ≤ T (A + H) - T a := sub_nonneg.mpr (hmono (by linarith))
    have hsum : (0 : ℝ) ≤ ∑' j : ℕ, (w j)⁻¹ :=
      tsum_nonneg fun j => (inv_pos.mpr (hw j)).le
    positivity
  have hlt : ENNReal.ofReal ((T (A + H) - T a) / Λ * ∑' j : ℕ, (w j)⁻¹)
      < ENNReal.ofReal (A - a) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).mpr hsmall
  have hnsub : ¬ (Icc a A ⊆ E) := by
    intro hsub
    have hle := le_trans (measure_mono hsub) hbound
    rw [Real.volume_Icc] at hle
    exact absurd hle (not_le.mpr hlt)
  obtain ⟨x, hxIcc, hxE⟩ := Set.not_subset.mp hnsub
  refine ⟨x, hxIcc, fun j => ?_⟩
  by_contra hj
  exact hxE ⟨hxIcc, j, not_lt.mp hj⟩

/-- **A point that is Lipschitz at every scale below `H`.**  Combining the exceptional-measure bound
with the passage from dyadic to arbitrary scales: at the surviving point the increment over any step
`u <= H` is at most twice the tolerance carried by the dyadic scale just above `u`. -/
theorem exists_good_point_increment_le (hmono : Monotone T) {a A H Λ : ℝ} (haA : a ≤ A)
    (hH : 0 < H) (hΛ : 0 < Λ) {w : ℕ → ℝ} (hw : ∀ j, 0 < w j)
    (hwsum : Summable fun j : ℕ => (w j)⁻¹)
    (hsmall : (T (A + H) - T a) / Λ * ∑' j : ℕ, (w j)⁻¹ < A - a) :
    ∃ x ∈ Icc a A, ∀ u : ℝ, 0 < u → u ≤ H →
      ∃ j : ℕ, (2 : ℝ) ^ j * u ≤ H ∧ T (x + u) - T x < 2 * (Λ * w j) * u := by
  obtain ⟨x, hx, hgood⟩ :=
    exists_good_point_of_measure_lt hmono haA hH hΛ hw hwsum hsmall
  exact ⟨x, hx, fun u hu huH => exists_dyadic_index_increment_le hmono hH hgood hu huH⟩

end GaloisForLFunctions.Nevanlinna
