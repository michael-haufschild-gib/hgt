import GaloisForLFunctions.RHTower.CCMSawtoothDilationMean
import GaloisForLFunctions.RHTower.EulerMaclaurinSawtooth
import GaloisForLFunctions.RHTower.SawtoothFourierSeries
import GaloisForLFunctions.RHTower.CCMEndpointFourierJet
import Mathlib.NumberTheory.ZetaValues

/-!
# Poisson summation for a `C²` source truncated to an interval

A source that is `C²` on `[a, b]` and zero outside has a Fourier transform of size exactly `1/y`,
because the endpoint values `h a`, `h b` do not vanish.  Poisson summation for such a source is
therefore a **conditionally** convergent statement: the transform series converges only as a limit of
partial sums, and no dominated-convergence argument reaches it.  Mathlib's Poisson summation
theorems all require decay strictly faster than `1/y` on both sides, so they do not apply.

This module proves the identity unconditionally, by the route that keeps the conditional part
finite-dimensional.  The three ingredients are:

* **Euler–Maclaurin with arbitrary real endpoints** (`em1`).  Summing samples of a `C¹` function over
  `(α, β]` equals its integral plus a sawtooth remainder plus two explicit endpoint terms
  `g β · saw β - g α · saw α`.  Those two terms are exactly the jump contributions, and they carry
  the whole conditional part of the final series.
* **A second integration by parts against the periodic primitive** (`em2`).  The sawtooth remainder
  is traded for the continuous kernel `sawPrimitive`, whose cosine series is absolutely convergent.
* **The two Fourier series**: the conditionally convergent sine series for `sawUnit`
  (`tendsto_sum_sawtoothSine`) for the two endpoint terms, and the absolutely convergent cosine
  series for `sawPrimitive` (`hasSum_cos_div_sq`) for the remainder.

Recombining term by term through the twice-integrated endpoint formula produces the transform
samples, which is Poisson summation.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set Filter Finset Topology

/-! ## The periodic primitive of the sawtooth -/

/-- The `1`-periodic primitive of `sawUnit`, normalised to vanish at the integers. -/
def sawPrimitive (x : ℝ) : ℝ := (Int.fract x - Int.fract x ^ 2) / 2

theorem sawPrimitive_intCast (m : ℤ) : sawPrimitive (m : ℝ) = 0 := by
  simp [sawPrimitive]

theorem sawPrimitive_add_intCast (x : ℝ) (m : ℤ) : sawPrimitive (x + m) = sawPrimitive x := by
  simp [sawPrimitive, Int.fract_add_intCast]

theorem abs_sawPrimitive_le (x : ℝ) : |sawPrimitive x| ≤ 1 / 8 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have hsq := sq_nonneg (Int.fract x - 1 / 2)
  rw [abs_le]
  constructor <;> · rw [sawPrimitive]; nlinarith

theorem measurable_sawPrimitive : Measurable sawPrimitive := by
  unfold sawPrimitive
  exact (measurable_fract.sub (measurable_fract.pow_const 2)).div_const 2

/-- On a closed unit cell the periodic primitive is the local second Bernoulli half, up to sign.
The identity holds at **both** endpoints, because that half vanishes at both. -/
theorem sawPrimitive_eq_neg_bernoulliHalf (k : ℤ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ)) ((k : ℝ) + 1)) :
    sawPrimitive x = -bernoulliHalf k x := by
  rcases eq_or_lt_of_le hx.2 with heq | hlt
  · have hxk : x = ((k + 1 : ℤ) : ℝ) := by push_cast; exact heq
    rw [hxk, sawPrimitive_intCast]
    rw [show ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 by push_cast; ring, bernoulliHalf_right]
    ring
  · have hfl : ⌊x⌋ = k := by
      rw [Int.floor_eq_iff]
      exact ⟨hx.1, hlt⟩
    have hf : Int.fract x = x - (k : ℝ) := by rw [Int.fract, hfl]
    rw [sawPrimitive, bernoulliHalf, hf]
    ring

/-- **The absolutely convergent cosine series of the periodic primitive.**  This is the `k = 1` case
of the Bernoulli Fourier expansion, rewritten through `sawPrimitive`.  Unlike the sine series of
`sawUnit`, this one converges absolutely, which is what makes the remainder term of Euler–Maclaurin
interchangeable with the sum. -/
theorem hasSum_cos_div_sq (x : ℝ) :
    HasSum (fun n : ℕ => Real.cos (2 * Real.pi * n * x) / (n : ℝ) ^ 2)
      (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive x)) := by
  have hmem : Int.fract x ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hml := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hmem
  have hfac : ((2 * 1 : ℕ).factorial : ℝ) = 2 := by norm_num
  have hbern : Polynomial.eval (Int.fract x)
      (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1)))
      = Int.fract x ^ 2 - Int.fract x + 1 / 6 := by
    simp [Polynomial.bernoulli, Finset.sum_range_succ]
    ring
  rw [hfac, hbern] at hml
  have hval : ((-1 : ℝ)) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / 2 *
      (Int.fract x ^ 2 - Int.fract x + 1 / 6)
      = 2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive x) := by
    rw [sawPrimitive]; ring
  rw [hval] at hml
  refine hml.congr_fun fun n => ?_
  have hper : Real.cos (2 * Real.pi * (n : ℝ) * Int.fract x)
      = Real.cos (2 * Real.pi * (n : ℝ) * x) := by
    have hrw : 2 * Real.pi * (n : ℝ) * Int.fract x
        = 2 * Real.pi * (n : ℝ) * x + ((-(n * ⌊x⌋) : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [Int.fract]; push_cast; ring
    rw [hrw, Real.cos_add_int_mul_two_pi]
  rw [hper, show (2 * 1 : ℕ) = 2 from rfl]
  ring

/-! ## Integrability of the two kernels against an integrable factor -/

theorem intervalIntegrable_bdd_mul {a b : ℝ} {w φ : ℝ → ℝ} {C : ℝ}
    (hw : Measurable w) (hwb : ∀ x, ‖w x‖ ≤ C) (h : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun x => w x * φ x) volume a b :=
  ⟨h.1.bdd_mul hw.aestronglyMeasurable (Filter.Eventually.of_forall hwb),
    h.2.bdd_mul hw.aestronglyMeasurable (Filter.Eventually.of_forall hwb)⟩

theorem intervalIntegrable_sawUnit_mul {a b : ℝ} {φ : ℝ → ℝ}
    (h : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun x => sawUnit x * φ x) volume a b :=
  intervalIntegrable_bdd_mul measurable_sawUnit
    (fun x => by rw [Real.norm_eq_abs]; exact abs_sawUnit_le x) h

theorem intervalIntegrable_sawPrimitive_mul {a b : ℝ} {φ : ℝ → ℝ}
    (h : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun x => sawPrimitive x * φ x) volume a b :=
  intervalIntegrable_bdd_mul measurable_sawPrimitive
    (fun x => by rw [Real.norm_eq_abs]; exact abs_sawPrimitive_le x) h

/-! ## Euler–Maclaurin with arbitrary real endpoints -/

/-- On a cell the sawtooth is the affine ramp `k + 1/2 - x`. -/
theorem sawUnit_eq_of_cell {k : ℤ} {x : ℝ} (h1 : (k : ℝ) ≤ x) (h2 : x < (k : ℝ) + 1) :
    sawUnit x = (k : ℝ) + 1 / 2 - x := by
  have hfl : ⌊x⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨h1, h2⟩
  rw [sawUnit, Int.fract, hfl]
  ring

/-- The Euler–Maclaurin identity on one cell.  The whole content is a single integration by parts
against the affine ramp; the endpoint weights `saw β`, `saw α` absorb the two half-cells. -/
theorem em1_cell (k : ℤ) {α β : ℝ} (hα : (k : ℝ) ≤ α) (hab : α ≤ β) (hβ : β ≤ (k : ℝ) + 1)
    {g g' : ℝ → ℝ} (hd : ∀ x ∈ Icc α β, HasDerivAt g (g' x) x)
    (hi : IntervalIntegrable g' volume α β) :
    (∑ m ∈ Finset.Ioc ⌊α⌋ ⌊β⌋, g (m : ℝ))
      = g β * sawUnit β - g α * sawUnit α + (∫ x in α..β, g x)
        - ∫ x in α..β, sawUnit x * g' x := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hαlt : α < (k : ℝ) + 1 := lt_of_lt_of_le hlt hβ
  have hflα : ⌊α⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨hα, hαlt⟩
  have huIcc : uIcc α β = Icc α β := uIcc_of_le hab
  have hdu : ∀ x ∈ uIcc α β, HasDerivAt g (g' x) x := by rw [huIcc]; exact hd
  have hgc : ContinuousOn g (uIcc α β) := by
    rw [huIcc]
    exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hgi : IntervalIntegrable g volume α β := hgc.intervalIntegrable
  -- the sawtooth integral against the affine ramp
  have hramp : (∫ x in α..β, sawUnit x * g' x)
      = ∫ x in α..β, ((k : ℝ) + 1 / 2 - x) * g' x := by
    refine integral_congr_of_Ioo hab fun x hx => ?_
    rw [sawUnit_eq_of_cell (le_trans hα hx.1.le) (lt_of_lt_of_le hx.2 hβ)]
  have hu : ∀ x ∈ uIcc α β, HasDerivAt (fun t : ℝ => (k : ℝ) + 1 / 2 - t) (-1) x := by
    intro x _
    simpa using (hasDerivAt_id x).const_sub ((k : ℝ) + 1 / 2)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => (k : ℝ) + 1 / 2 - t) (u' := fun _ : ℝ => (-1 : ℝ))
    (v := g) (v' := g') hu hdu (intervalIntegrable_const) hi
  have hneg : (∫ x in α..β, (-1 : ℝ) * g x) = -∫ x in α..β, g x := by
    rw [intervalIntegral.integral_const_mul]; ring
  rw [hneg] at hibp
  rw [hramp, hibp]
  have hsawα : sawUnit α = (k : ℝ) + 1 / 2 - α := sawUnit_eq_of_cell hα hαlt
  rcases eq_or_lt_of_le hβ with hβeq | hβlt
  · -- the right endpoint is the next integer: the cell contributes its sample
    have hflβ : ⌊β⌋ = k + 1 := by
      rw [hβeq]
      rw [show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    have hIoc : Finset.Ioc ⌊α⌋ ⌊β⌋ = {k + 1} := by
      rw [hflα, hflβ]
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    have hsawβ : sawUnit β = 1 / 2 := by
      rw [hβeq, show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, sawUnit,
        Int.fract_intCast]
      ring
    have hgβ : g ((k + 1 : ℤ) : ℝ) = g β := by
      rw [show ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 by push_cast; ring, ← hβeq]
    rw [hIoc, Finset.sum_singleton, hgβ, hsawβ, hsawα, hβeq]
    ring
  · -- the cell is strictly inside: no sample, and the identity is the integration by parts
    have hflβ : ⌊β⌋ = k := by rw [Int.floor_eq_iff]; exact ⟨le_trans hα hab, hβlt⟩
    have hIoc : Finset.Ioc ⌊α⌋ ⌊β⌋ = (∅ : Finset ℤ) := by
      rw [hflα, hflβ]; simp
    have hsawβ : sawUnit β = (k : ℝ) + 1 / 2 - β :=
      sawUnit_eq_of_cell (le_trans hα hab) hβlt
    rw [hIoc, Finset.sum_empty, hsawβ, hsawα]
    ring

theorem em1_aux : ∀ (n : ℕ) {α β : ℝ}, (⌊β⌋ - ⌊α⌋).toNat = n → α ≤ β →
    ∀ {g g' : ℝ → ℝ}, (∀ x ∈ Icc α β, HasDerivAt g (g' x) x) →
      IntervalIntegrable g' volume α β →
      (∑ m ∈ Finset.Ioc ⌊α⌋ ⌊β⌋, g (m : ℝ))
        = g β * sawUnit β - g α * sawUnit α + (∫ x in α..β, g x)
          - ∫ x in α..β, sawUnit x * g' x := by
  intro n
  induction n with
  | zero =>
    intro α β hn hab g g' hd hi
    have hfle : ⌊α⌋ ≤ ⌊β⌋ := Int.floor_le_floor hab
    have hfeq : ⌊β⌋ = ⌊α⌋ := by omega
    have hβlt : β < (⌊α⌋ : ℝ) + 1 := by
      rw [← hfeq]; exact Int.lt_floor_add_one β
    exact em1_cell ⌊α⌋ (Int.floor_le α) hab hβlt.le hd hi
  | succ n ih =>
    intro α β hn hab g g' hd hi
    set k : ℤ := ⌊α⌋ with hk
    set γ : ℝ := (k : ℝ) + 1 with hγ
    have hstep : ⌊α⌋ + 1 ≤ ⌊β⌋ := by omega
    have hαγ : α ≤ γ := (Int.lt_floor_add_one α).le
    have hγβ : γ ≤ β := by
      refine le_trans ?_ (Int.floor_le β)
      rw [hγ]
      have : ((k + 1 : ℤ) : ℝ) ≤ (⌊β⌋ : ℝ) := by exact_mod_cast hstep
      simpa using this
    have hflγ : ⌊γ⌋ = k + 1 := by
      rw [hγ, show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    have hsubγ : Icc α γ ⊆ Icc α β := Icc_subset_Icc le_rfl hγβ
    have hsubβ : Icc γ β ⊆ Icc α β := Icc_subset_Icc hαγ le_rfl
    have hi1 : IntervalIntegrable g' volume α γ :=
      hi.mono_set (by rw [uIcc_of_le hαγ, uIcc_of_le hab]; exact hsubγ)
    have hi2 : IntervalIntegrable g' volume γ β :=
      hi.mono_set (by rw [uIcc_of_le hγβ, uIcc_of_le hab]; exact hsubβ)
    have hcell := em1_cell k (Int.floor_le α) hαγ (le_of_eq hγ.symm)
      (fun x hx => hd x (hsubγ hx)) hi1
    have hrest := ih (α := γ) (β := β) (by rw [hflγ]; omega) hγβ
      (fun x hx => hd x (hsubβ hx)) hi2
    -- glue the two cells
    have hgc : ContinuousOn g (Icc α β) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have hgi1 : IntervalIntegrable g volume α γ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hαγ]
      exact hgc.mono hsubγ
    have hgi2 : IntervalIntegrable g volume γ β := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hγβ]
      exact hgc.mono hsubβ
    have hsi1 := intervalIntegrable_sawUnit_mul hi1
    have hsi2 := intervalIntegrable_sawUnit_mul hi2
    have hsum : (∑ m ∈ Finset.Ioc ⌊α⌋ ⌊γ⌋, g (m : ℝ)) + ∑ m ∈ Finset.Ioc ⌊γ⌋ ⌊β⌋, g (m : ℝ)
        = ∑ m ∈ Finset.Ioc ⌊α⌋ ⌊β⌋, g (m : ℝ) := by
      have hdisj : Disjoint (Finset.Ioc ⌊α⌋ ⌊γ⌋) (Finset.Ioc ⌊γ⌋ ⌊β⌋) := by
        refine Finset.disjoint_left.mpr fun m h1 h2 => ?_
        simp only [Finset.mem_Ioc] at h1 h2
        omega
      rw [← Finset.sum_union hdisj,
        Finset.Ioc_union_Ioc_eq_Ioc (by rw [hflγ, hk]; omega) (by rw [hflγ]; omega)]
    rw [← hsum, hcell, hrest,
      ← intervalIntegral.integral_add_adjacent_intervals hgi1 hgi2,
      ← intervalIntegral.integral_add_adjacent_intervals hsi1 hsi2]
    ring

/-- **Euler–Maclaurin with arbitrary real endpoints.**  For `g` of class `C¹` on `[α, β]`,

```text
∑_{α < m ≤ β} g(m) = g β · saw β - g α · saw α + ∫_α^β g - ∫_α^β saw(x) g'(x) dx.
```

The two endpoint terms are what makes this valid at non-integer endpoints; at integer endpoints they
collapse to the trapezoid weights. -/
theorem em1 {α β : ℝ} (hab : α ≤ β) {g g' : ℝ → ℝ}
    (hd : ∀ x ∈ Icc α β, HasDerivAt g (g' x) x) (hi : IntervalIntegrable g' volume α β) :
    (∑ m ∈ Finset.Ioc ⌊α⌋ ⌊β⌋, g (m : ℝ))
      = g β * sawUnit β - g α * sawUnit α + (∫ x in α..β, g x)
        - ∫ x in α..β, sawUnit x * g' x :=
  em1_aux _ rfl hab hd hi

/-! ## The second integration by parts, against the periodic primitive -/

theorem em2_cell (k : ℤ) {α β : ℝ} (hα : (k : ℝ) ≤ α) (hab : α ≤ β) (hβ : β ≤ (k : ℝ) + 1)
    {φ φ' : ℝ → ℝ} (hd : ∀ x ∈ Icc α β, HasDerivAt φ (φ' x) x)
    (hi : IntervalIntegrable φ' volume α β) :
    (∫ x in α..β, sawUnit x * φ x)
      = sawPrimitive β * φ β - sawPrimitive α * φ α
        - ∫ x in α..β, sawPrimitive x * φ' x := by
  have hsub : Icc α β ⊆ Icc ((k : ℝ)) ((k : ℝ) + 1) := Icc_subset_Icc hα hβ
  have huIcc : uIcc α β = Icc α β := uIcc_of_le hab
  have hdu : ∀ x ∈ uIcc α β, HasDerivAt φ (φ' x) x := by rw [huIcc]; exact hd
  have hP : ∀ x ∈ Icc α β, sawPrimitive x = -bernoulliHalf k x :=
    fun x hx => sawPrimitive_eq_neg_bernoulliHalf k (hsub hx)
  have hu : ∀ x ∈ uIcc α β,
      HasDerivAt (fun t : ℝ => -bernoulliHalf k t) ((k : ℝ) + 1 / 2 - x) x := by
    intro x _
    have h := (hasDerivAt_bernoulliHalf k x).fun_neg
    have hval : -(x - (k : ℝ) - 1 / 2) = (k : ℝ) + 1 / 2 - x := by ring
    rw [← hval]
    exact h
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => -bernoulliHalf k t) (u' := fun x : ℝ => (k : ℝ) + 1 / 2 - x)
    (v := φ) (v' := φ') hu hdu
    ((by fun_prop : Continuous fun x : ℝ => (k : ℝ) + 1 / 2 - x).intervalIntegrable _ _) hi
  have hL : (∫ x in α..β, sawPrimitive x * φ' x)
      = ∫ x in α..β, (fun t : ℝ => -bernoulliHalf k t) x * φ' x := by
    refine integral_congr_of_Ioo hab fun x hx => ?_
    rw [hP x ⟨hx.1.le, hx.2.le⟩]
  have hR : (∫ x in α..β, sawUnit x * φ x)
      = ∫ x in α..β, ((k : ℝ) + 1 / 2 - x) * φ x := by
    refine integral_congr_of_Ioo hab fun x hx => ?_
    rw [sawUnit_eq_of_cell (le_trans hα hx.1.le) (lt_of_lt_of_le hx.2 hβ)]
  rw [hR, hL]
  rw [hP β ⟨hab, le_rfl⟩, hP α ⟨le_rfl, hab⟩]
  linarith [hibp]

theorem em2_aux : ∀ (n : ℕ) {α β : ℝ}, (⌊β⌋ - ⌊α⌋).toNat = n → α ≤ β →
    ∀ {φ φ' : ℝ → ℝ}, (∀ x ∈ Icc α β, HasDerivAt φ (φ' x) x) →
      IntervalIntegrable φ' volume α β →
      (∫ x in α..β, sawUnit x * φ x)
        = sawPrimitive β * φ β - sawPrimitive α * φ α
          - ∫ x in α..β, sawPrimitive x * φ' x := by
  intro n
  induction n with
  | zero =>
    intro α β hn hab φ φ' hd hi
    have hfle : ⌊α⌋ ≤ ⌊β⌋ := Int.floor_le_floor hab
    have hfeq : ⌊β⌋ = ⌊α⌋ := by omega
    have hβlt : β < (⌊α⌋ : ℝ) + 1 := by rw [← hfeq]; exact Int.lt_floor_add_one β
    exact em2_cell ⌊α⌋ (Int.floor_le α) hab hβlt.le hd hi
  | succ n ih =>
    intro α β hn hab φ φ' hd hi
    set k : ℤ := ⌊α⌋ with hk
    set γ : ℝ := (k : ℝ) + 1 with hγ
    have hstep : ⌊α⌋ + 1 ≤ ⌊β⌋ := by omega
    have hαγ : α ≤ γ := (Int.lt_floor_add_one α).le
    have hγβ : γ ≤ β := by
      refine le_trans ?_ (Int.floor_le β)
      rw [hγ]
      have : ((k + 1 : ℤ) : ℝ) ≤ (⌊β⌋ : ℝ) := by exact_mod_cast hstep
      simpa using this
    have hflγ : ⌊γ⌋ = k + 1 := by
      rw [hγ, show (k : ℝ) + 1 = ((k + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]
    have hsubγ : Icc α γ ⊆ Icc α β := Icc_subset_Icc le_rfl hγβ
    have hsubβ : Icc γ β ⊆ Icc α β := Icc_subset_Icc hαγ le_rfl
    have hi1 : IntervalIntegrable φ' volume α γ :=
      hi.mono_set (by rw [uIcc_of_le hαγ, uIcc_of_le hab]; exact hsubγ)
    have hi2 : IntervalIntegrable φ' volume γ β :=
      hi.mono_set (by rw [uIcc_of_le hγβ, uIcc_of_le hab]; exact hsubβ)
    have hcell := em2_cell k (Int.floor_le α) hαγ (le_of_eq hγ.symm)
      (fun x hx => hd x (hsubγ hx)) hi1
    have hrest := ih (α := γ) (β := β) (by rw [hflγ]; omega) hγβ
      (fun x hx => hd x (hsubβ hx)) hi2
    have hφc : ContinuousOn φ (Icc α β) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have hφi1 : IntervalIntegrable φ volume α γ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hαγ]; exact hφc.mono hsubγ
    have hφi2 : IntervalIntegrable φ volume γ β := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hγβ]; exact hφc.mono hsubβ
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_sawUnit_mul hφi1) (intervalIntegrable_sawUnit_mul hφi2),
      hcell, hrest,
      ← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_sawPrimitive_mul hi1) (intervalIntegrable_sawPrimitive_mul hi2)]
    ring

/-- **The sawtooth remainder against the periodic primitive, at arbitrary real endpoints.**  The
kernel `sawPrimitive` is continuous and `1`-periodic, so the integration by parts has no interior
boundary contributions; only the two endpoints survive. -/
theorem em2 {α β : ℝ} (hab : α ≤ β) {φ φ' : ℝ → ℝ}
    (hd : ∀ x ∈ Icc α β, HasDerivAt φ (φ' x) x) (hi : IntervalIntegrable φ' volume α β) :
    (∫ x in α..β, sawUnit x * φ x)
      = sawPrimitive β * φ β - sawPrimitive α * φ α
        - ∫ x in α..β, sawPrimitive x * φ' x :=
  em2_aux _ rfl hab hd hi

/-! ## The value of the sawtooth sine series off the lattice -/

theorem sawWave_add_int_mul_two_pi (x : ℝ) (k : ℤ) :
    sawWave (x + (k : ℝ) * (2 * Real.pi)) = sawWave x := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have harg : (x + (k : ℝ) * (2 * Real.pi)) / (2 * Real.pi) = x / (2 * Real.pi) + (k : ℝ) := by
    field_simp
  rw [sawWave, sawWave, harg, sawUnit_add_intCast]

/-- **The sawtooth sine series, at every angle off the lattice.**  The corpus already has the
convergence and the uniform bound; this identifies the limit, which is what a substitution of the
form `θ = 2π b / u` needs. -/
theorem tendsto_sum_sawtoothSine_of_ne {θ : ℝ} (hθ : ∀ k : ℤ, θ ≠ (k : ℝ) * (2 * Real.pi)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, Real.sin ((n : ℝ) * θ) / (n : ℝ)) atTop
      (𝓝 (sawWave θ)) := by
  obtain ⟨k, θ', hθ', hsum⟩ := exists_mem_Ioo_sub_int_mul_two_pi hθ
  have hval : sawWave θ = sawWave θ' := by rw [hsum, sawWave_add_int_mul_two_pi]
  rw [hval]
  refine (tendsto_sum_sawtoothSine hθ').congr fun N => ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hsum, sawtoothSine_periodic θ' k n]

/-! ## The twice-integrated endpoint formula at arbitrary endpoints -/

/-- The twice-integrated cosine transform on an arbitrary interval.  This is the corpus's endpoint
jet identity with both endpoints free and with the hypotheses localised to `[a, b]`. -/
theorem integral_mul_cos_twice_ibp_gen {a b y : ℝ} (hy : y ≠ 0) (hab : a ≤ b)
    {f f' f'' : ℝ → ℝ}
    (hd1 : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hd2 : ∀ x ∈ Icc a b, HasDerivAt f' (f'' x) x)
    (hi2 : IntervalIntegrable f'' volume a b) :
    (∫ x in a..b, f x * Real.cos (2 * Real.pi * x * y))
      = (f b * Real.sin (2 * Real.pi * b * y) - f a * Real.sin (2 * Real.pi * a * y))
          / (2 * Real.pi * y)
        + (f' b * Real.cos (2 * Real.pi * b * y) - f' a * Real.cos (2 * Real.pi * a * y))
          / (4 * Real.pi ^ 2 * y ^ 2)
        - (1 / (4 * Real.pi ^ 2 * y ^ 2)) * ∫ x in a..b, f'' x * Real.cos (2 * Real.pi * x * y) := by
  have hne := two_pi_mul_ne_zero hy
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hd1u : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x := by rw [huIcc]; exact hd1
  have hd2u : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x := by rw [huIcc]; exact hd2
  have hf'c : ContinuousOn f' (uIcc a b) := by
    rw [huIcc]
    exact fun x hx => (hd2 x hx).continuousAt.continuousWithinAt
  have hi1 : IntervalIntegrable f' volume a b := hf'c.intervalIntegrable
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := f') (v := fun t : ℝ => Real.sin (2 * Real.pi * t * y) / (2 * Real.pi * y))
    (v' := fun x : ℝ => Real.cos (2 * Real.pi * x * y))
    hd1u (fun x _ => hasDerivAt_sinScaled hy x) hi1
    ((continuous_cosScaled y).intervalIntegrable _ _)
  have hibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f') (u' := f'') (v := fun t : ℝ => -Real.cos (2 * Real.pi * t * y) / (2 * Real.pi * y))
    (v' := fun x : ℝ => Real.sin (2 * Real.pi * x * y))
    hd2u (fun x _ => hasDerivAt_negCosScaled hy x) hi2
    ((continuous_sinScaled y).intervalIntegrable _ _)
  have hpull1 : (∫ x in a..b, f' x * (Real.sin (2 * Real.pi * x * y) / (2 * Real.pi * y)))
      = (1 / (2 * Real.pi * y)) * ∫ x in a..b, f' x * Real.sin (2 * Real.pi * x * y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    field_simp
  have hpull2 : (∫ x in a..b, f'' x * (-Real.cos (2 * Real.pi * x * y) / (2 * Real.pi * y)))
      = -(1 / (2 * Real.pi * y)) * ∫ x in a..b, f'' x * Real.cos (2 * Real.pi * x * y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    field_simp
  rw [hpull1] at hibp1
  rw [hpull2] at hibp2
  rw [hibp1, hibp2]
  field_simp
  ring

/-! ## The absolutely convergent remainder series -/

/-- **The remainder interchange.**  The `1/n²` cosine samples of an integrable weight sum to the
integral of that weight against the periodic primitive.  The series is absolutely convergent, so the
interchange is dominated convergence with the dominating function `‖w‖ / n²`. -/
theorem hasSum_integral_cos_div_sq {a b u : ℝ} (hab : a ≤ b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b)) :
    HasSum (fun n : ℕ =>
        (∫ t in a..b, w t * Real.cos (2 * Real.pi * t * ((n : ℝ) / u))) / (n : ℝ) ^ 2)
      (∫ t in a..b, w t * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (t / u)))) := by
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  set F : ℕ → ℝ → ℝ := fun n t =>
    w t * Real.cos (2 * Real.pi * t * ((n : ℝ) / u)) / (n : ℝ) ^ 2 with hF
  have hwi : IntegrableOn w (Ioc a b) volume := by
    have : IntervalIntegrable w volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hab]; exact hw
    exact this.1
  have hwμ : Integrable w μ := hwi
  have hFint : ∀ n : ℕ, Integrable (F n) μ := by
    intro n
    have hb : Integrable (fun t : ℝ => Real.cos (2 * Real.pi * t * ((n : ℝ) / u)) * w t) μ :=
      hwμ.bdd_mul (Measurable.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    have hcomm : (fun t : ℝ => Real.cos (2 * Real.pi * t * ((n : ℝ) / u)) * w t)
        = fun t : ℝ => w t * Real.cos (2 * Real.pi * t * ((n : ℝ) / u)) := by
      funext t; ring
    rw [hcomm] at hb
    exact hb.div_const _
  have hKnn : 0 ≤ ∫ t, ‖w t‖ ∂μ := integral_nonneg fun t => norm_nonneg _
  have hnormle : ∀ n : ℕ, (∫ t, ‖F n t‖ ∂μ) ≤ (∫ t, ‖w t‖ ∂μ) / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hF]
      norm_num
    have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hptw : ∀ t, ‖F n t‖ ≤ ‖w t‖ / (n : ℝ) ^ 2 := by
      intro t
      have habs : |Real.cos (2 * Real.pi * t * ((n : ℝ) / u))| ≤ 1 := Real.abs_cos_le_one _
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := le_of_lt hnpos
      simp only [hF, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hnn]
      gcongr
      nlinarith [abs_nonneg (w t)]
    calc (∫ t, ‖F n t‖ ∂μ) ≤ ∫ t, ‖w t‖ / (n : ℝ) ^ 2 ∂μ :=
          integral_mono (hFint n).norm (hwμ.norm.div_const _) hptw
      _ = (∫ t, ‖w t‖ ∂μ) / (n : ℝ) ^ 2 := integral_div _ _
  have hsummable : Summable fun n : ℕ => ∫ t, ‖F n t‖ ∂μ := by
    have hdom : Summable fun n : ℕ => (∫ t, ‖w t‖ ∂μ) / (n : ℝ) ^ 2 := by
      have hml := summable_one_div_sq.mul_left (∫ t, ‖w t‖ ∂μ)
      exact hml.congr fun n => by ring
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hnormle hdom
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hsummable
  have htsum : ∀ t, (∑' n : ℕ, F n t) = w t * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (t / u))) := by
    intro t
    have h := (hasSum_cos_div_sq (t / u)).mul_left (w t)
    have heq : (fun n : ℕ => w t * (Real.cos (2 * Real.pi * (n : ℝ) * (t / u)) / (n : ℝ) ^ 2))
        = fun n : ℕ => F n t := by
      funext n
      simp only [hF]
      rw [show 2 * Real.pi * (n : ℝ) * (t / u) = 2 * Real.pi * t * ((n : ℝ) / u) by ring]
      ring
    rw [heq] at h
    exact h.tsum_eq
  simp only [htsum] at hmain
  have hcast : ∀ n : ℕ, (∫ t, F n t ∂μ)
      = (∫ t in a..b, w t * Real.cos (2 * Real.pi * t * ((n : ℝ) / u))) / (n : ℝ) ^ 2 := by
    intro n
    rw [intervalIntegral.integral_of_le hab, hμ]
    exact integral_div _ _
  have hcast2 : (∫ t, w t * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (t / u))) ∂μ)
      = ∫ t in a..b, w t * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (t / u))) := by
    rw [intervalIntegral.integral_of_le hab]
  rw [hcast2] at hmain
  exact hmain.congr_fun fun n => (hcast n).symm

/-! ## The arithmetic side of the identity -/

/-- **Euler–Maclaurin for a dilated `C²` source.**  Summing `h` over the lattice `uℤ` inside `[a, b]`
produces the integral, the two endpoint sawtooth terms, and a remainder against the continuous
periodic primitive.  Everything on the right is either explicit or absolutely convergent once the two
Fourier series are inserted. -/
theorem em_dilated {a b u : ℝ} (hab : a ≤ b) (hu : 0 < u) {h h' h'' : ℝ → ℝ}
    (hd1 : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hd2 : ∀ x ∈ Icc a b, HasDerivAt h' (h'' x) x)
    (hc2 : ContinuousOn h'' (Icc a b)) :
    (∑ m ∈ Finset.Ioc ⌊a / u⌋ ⌊b / u⌋, h ((m : ℝ) * u))
      = (1 / u) * (∫ t in a..b, h t)
        + h b * sawUnit (b / u) - h a * sawUnit (a / u)
        - u * (sawPrimitive (b / u) * h' b) + u * (sawPrimitive (a / u) * h' a)
        + u * ∫ t in a..b, sawPrimitive (t / u) * h'' t := by
  have hune : u ≠ 0 := hu.ne'
  have hau : a / u * u = a := div_mul_cancel₀ a hune
  have hbu : b / u * u = b := div_mul_cancel₀ b hune
  have hαβ : a / u ≤ b / u := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hab (inv_pos.mpr hu).le
  have hmaps : ∀ x ∈ Icc (a / u) (b / u), x * u ∈ Icc a b := by
    intro x hx
    refine ⟨?_, ?_⟩
    · calc a = a / u * u := hau.symm
        _ ≤ x * u := mul_le_mul_of_nonneg_right hx.1 hu.le
    · calc x * u ≤ b / u * u := mul_le_mul_of_nonneg_right hx.2 hu.le
        _ = b := hbu
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * u) u x := fun x => by
    simpa using (hasDerivAt_id x).mul_const u
  -- the dilated function and its two derivatives
  have hdg : ∀ x ∈ Icc (a / u) (b / u),
      HasDerivAt (fun y : ℝ => h (y * u)) (u * h' (x * u)) x := by
    intro x hx
    have hcomp := (hd1 (x * u) (hmaps x hx)).comp x (hlin x)
    rw [show u * h' (x * u) = h' (x * u) * u from by ring]
    exact hcomp
  have hdg' : ∀ x ∈ Icc (a / u) (b / u),
      HasDerivAt (fun y : ℝ => u * h' (y * u)) (u ^ 2 * h'' (x * u)) x := by
    intro x hx
    have hcomp := (hd2 (x * u) (hmaps x hx)).comp x (hlin x)
    have := hcomp.const_mul u
    rw [show u ^ 2 * h'' (x * u) = u * (h'' (x * u) * u) from by ring]
    exact this
  have hcontg' : ContinuousOn (fun y : ℝ => u * h' (y * u)) (Icc (a / u) (b / u)) := by
    intro x hx
    exact ((hdg' x hx).continuousAt).continuousWithinAt
  have hcontg'' : ContinuousOn (fun y : ℝ => u ^ 2 * h'' (y * u)) (Icc (a / u) (b / u)) := by
    refine ContinuousOn.mul continuousOn_const ?_
    exact hc2.comp (by fun_prop) hmaps
  have hig' : IntervalIntegrable (fun y : ℝ => u * h' (y * u)) volume (a / u) (b / u) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hαβ]; exact hcontg'
  have hig'' : IntervalIntegrable (fun y : ℝ => u ^ 2 * h'' (y * u)) volume (a / u) (b / u) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hαβ]; exact hcontg''
  have hem1 := em1 hαβ hdg hig'
  have hem2 := em2 hαβ hdg' hig''
  -- change of variables in the two integrals
  have hcv1 : (∫ x in (a / u)..(b / u), h (x * u)) = u⁻¹ * ∫ t in a..b, h t := by
    rw [intervalIntegral.integral_comp_mul_right h hune, hau, hbu, smul_eq_mul]
  have hcv2 : (∫ x in (a / u)..(b / u), sawPrimitive x * (u ^ 2 * h'' (x * u)))
      = u⁻¹ * (u ^ 2 * ∫ t in a..b, sawPrimitive (t / u) * h'' t) := by
    obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, ∀ t, G t = u ^ 2 * (sawPrimitive (t / u) * h'' t) :=
      ⟨_, fun _ => rfl⟩
    have h1 : (∫ x in (a / u)..(b / u), sawPrimitive x * (u ^ 2 * h'' (x * u)))
        = ∫ x in (a / u)..(b / u), G (x * u) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hGdef, mul_div_cancel_right₀ x hune]
      ring
    have h2 := intervalIntegral.integral_comp_mul_right G hune (a := a / u) (b := b / u)
    rw [hau, hbu, smul_eq_mul] at h2
    have h3 : (∫ x in a..b, G x) = u ^ 2 * ∫ t in a..b, sawPrimitive (t / u) * h'' t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun x _ => hGdef x
    rw [h1, h2, h3]
  rw [hem2, hcv1, hcv2, hbu, hau] at hem1
  rw [hem1]
  field_simp
  ring

/-! ## The Fourier side, split into its two convergence regimes -/

/-- The endpoint sine part of the transform series.  This is the conditionally convergent half: term
by term it is a harmonic series, and only the sawtooth identity makes it converge. -/
theorem tendsto_sum_endpointSine {a b u Ha Hb : ℝ} (hu : 0 < u)
    (hna : ∀ k : ℤ, a / u ≠ (k : ℝ)) (hnb : ∀ k : ℤ, b / u ≠ (k : ℝ)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (Hb * Real.sin (2 * Real.pi * b * ((n : ℝ) / u))
          - Ha * Real.sin (2 * Real.pi * a * ((n : ℝ) / u))) / (Real.pi * (n : ℝ))) atTop
      (𝓝 (Hb * sawUnit (b / u) - Ha * sawUnit (a / u))) := by
  have hune : u ≠ 0 := hu.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hoff : ∀ c : ℝ, (∀ k : ℤ, c / u ≠ (k : ℝ)) →
      ∀ k : ℤ, 2 * Real.pi * c / u ≠ (k : ℝ) * (2 * Real.pi) := by
    intro c hc k hk
    refine hc k ?_
    refine mul_left_cancel₀ (ne_of_gt h2pi) ?_
    rw [show (2 * Real.pi) * (c / u) = 2 * Real.pi * c / u from by ring, hk]
    ring
  have hterm : ∀ N : ℕ, (∑ n ∈ Finset.range N,
        (Hb * Real.sin (2 * Real.pi * b * ((n : ℝ) / u))
          - Ha * Real.sin (2 * Real.pi * a * ((n : ℝ) / u))) / (Real.pi * (n : ℝ)))
      = (Hb / Real.pi) * (∑ n ∈ Finset.range N,
            Real.sin ((n : ℝ) * (2 * Real.pi * b / u)) / (n : ℝ))
        - (Ha / Real.pi) * (∑ n ∈ Finset.range N,
            Real.sin ((n : ℝ) * (2 * Real.pi * a / u)) / (n : ℝ)) := by
    intro N
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show 2 * Real.pi * b * ((n : ℝ) / u) = (n : ℝ) * (2 * Real.pi * b / u) from by ring,
      show 2 * Real.pi * a * ((n : ℝ) / u) = (n : ℝ) * (2 * Real.pi * a / u) from by ring]
    ring
  have hval : (Hb / Real.pi) * sawWave (2 * Real.pi * b / u)
      - (Ha / Real.pi) * sawWave (2 * Real.pi * a / u)
      = Hb * sawUnit (b / u) - Ha * sawUnit (a / u) := by
    rw [sawWave, sawWave, show 2 * Real.pi * b / u / (2 * Real.pi) = b / u from by field_simp,
      show 2 * Real.pi * a / u / (2 * Real.pi) = a / u from by field_simp]
    field_simp
  rw [← hval]
  refine (Tendsto.sub ((tendsto_sum_sawtoothSine_of_ne (hoff b hnb)).const_mul (Hb / Real.pi))
    ((tendsto_sum_sawtoothSine_of_ne (hoff a hna)).const_mul (Ha / Real.pi))).congr
    fun N => (hterm N).symm

/-- The endpoint cosine part of the transform series, together with the second-derivative
remainder.  This is the absolutely convergent half. -/
theorem hasSum_endpointCos {a b u : ℝ} (hab : a ≤ b) (hu : 0 < u) {h' h'' : ℝ → ℝ}
    (hd2 : ∀ x ∈ Icc a b, HasDerivAt h' (h'' x) x) (hc2 : ContinuousOn h'' (Icc a b)) :
    HasSum (fun n : ℕ => (u / (2 * Real.pi ^ 2)) *
        ((h' b * Real.cos (2 * Real.pi * b * ((n : ℝ) / u))
          - h' a * Real.cos (2 * Real.pi * a * ((n : ℝ) / u))
          - ∫ t in a..b, h'' t * Real.cos (2 * Real.pi * t * ((n : ℝ) / u))) / (n : ℝ) ^ 2))
      (u * (-(sawPrimitive (b / u) * h' b) + sawPrimitive (a / u) * h' a
        + ∫ t in a..b, sawPrimitive (t / u) * h'' t)) := by
  have hune : u ≠ 0 := hu.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hi2 : IntervalIntegrable h'' volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [huIcc]; exact hc2
  have hFTC : (∫ t in a..b, h'' t) = h' b - h' a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hi2
    rw [huIcc]; exact hd2
  have hmeasP : Measurable fun t : ℝ => sawPrimitive (t / u) :=
    measurable_sawPrimitive.comp (measurable_id.div_const u)
  have hiP : IntervalIntegrable (fun t : ℝ => sawPrimitive (t / u) * h'' t) volume a b :=
    intervalIntegrable_bdd_mul hmeasP
      (fun t => by rw [Real.norm_eq_abs]; exact abs_sawPrimitive_le _) hi2
  -- the three absolutely convergent series
  have hSb := hasSum_cos_div_sq (b / u)
  have hSa := hasSum_cos_div_sq (a / u)
  have hSI := hasSum_integral_cos_div_sq (u := u) hab hc2 (w := h'')
  have hargb : ∀ n : ℕ, Real.cos (2 * Real.pi * (n : ℝ) * (b / u))
      = Real.cos (2 * Real.pi * b * ((n : ℝ) / u)) := fun n => by
    rw [show 2 * Real.pi * (n : ℝ) * (b / u) = 2 * Real.pi * b * ((n : ℝ) / u) from by ring]
  have harga : ∀ n : ℕ, Real.cos (2 * Real.pi * (n : ℝ) * (a / u))
      = Real.cos (2 * Real.pi * a * ((n : ℝ) / u)) := fun n => by
    rw [show 2 * Real.pi * (n : ℝ) * (a / u) = 2 * Real.pi * a * ((n : ℝ) / u) from by ring]
  have hSb' : HasSum (fun n : ℕ => Real.cos (2 * Real.pi * b * ((n : ℝ) / u)) / (n : ℝ) ^ 2)
      (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (b / u))) :=
    hSb.congr_fun fun n => by rw [hargb n]
  have hSa' : HasSum (fun n : ℕ => Real.cos (2 * Real.pi * a * ((n : ℝ) / u)) / (n : ℝ) ^ 2)
      (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (a / u))) :=
    hSa.congr_fun fun n => by rw [harga n]
  have hcomb := (((hSb'.mul_left (h' b)).sub (hSa'.mul_left (h' a))).sub hSI).mul_left
    (u / (2 * Real.pi ^ 2))
  -- the remainder integral, split
  have hsplit : (∫ t in a..b, h'' t * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (t / u))))
      = 2 * Real.pi ^ 2 * (1 / 12) * (h' b - h' a)
        - 2 * Real.pi ^ 2 * ∫ t in a..b, sawPrimitive (t / u) * h'' t := by
    have hcongr : (∫ t in a..b, h'' t * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (t / u))))
        = ∫ t in a..b, (2 * Real.pi ^ 2 * (1 / 12) * h'' t
            - 2 * Real.pi ^ 2 * (sawPrimitive (t / u) * h'' t)) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [hcongr, intervalIntegral.integral_sub (hi2.const_mul _) (hiP.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hFTC]
  rw [hsplit] at hcomb
  have hvalue : (u / (2 * Real.pi ^ 2)) *
      (h' b * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (b / u)))
        - h' a * (2 * Real.pi ^ 2 * (1 / 12 - sawPrimitive (a / u)))
        - (2 * Real.pi ^ 2 * (1 / 12) * (h' b - h' a)
            - 2 * Real.pi ^ 2 * ∫ t in a..b, sawPrimitive (t / u) * h'' t))
      = u * (-(sawPrimitive (b / u) * h' b) + sawPrimitive (a / u) * h' a
        + ∫ t in a..b, sawPrimitive (t / u) * h'' t) := by
    field_simp
    ring
  rw [hvalue] at hcomb
  refine hcomb.congr_fun fun n => ?_
  ring

/-! ## The term identity -/

/-- One transform sample, expanded through the twice-integrated endpoint formula and rescaled by the
Poisson factor `2/u`.  The two summands are exactly the two convergence regimes. -/
theorem cosTransform_term {a b u m : ℝ} (hab : a ≤ b) (hu : 0 < u) (hm : 0 < m)
    {h h' h'' : ℝ → ℝ}
    (hd1 : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hd2 : ∀ x ∈ Icc a b, HasDerivAt h' (h'' x) x)
    (hc2 : ContinuousOn h'' (Icc a b)) :
    (2 / u) * (∫ t in a..b, h t * Real.cos (2 * Real.pi * t * (m / u)))
      = (h b * Real.sin (2 * Real.pi * b * (m / u))
          - h a * Real.sin (2 * Real.pi * a * (m / u))) / (Real.pi * m)
        + (u / (2 * Real.pi ^ 2)) *
            ((h' b * Real.cos (2 * Real.pi * b * (m / u))
              - h' a * Real.cos (2 * Real.pi * a * (m / u))
              - ∫ t in a..b, h'' t * Real.cos (2 * Real.pi * t * (m / u))) / m ^ 2) := by
  have hune : u ≠ 0 := hu.ne'
  have hmne : m ≠ 0 := hm.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hy : m / u ≠ 0 := div_ne_zero hmne hune
  have hi2 : IntervalIntegrable h'' volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]; exact hc2
  rw [integral_mul_cos_twice_ibp_gen hy hab hd1 hd2 hi2]
  field_simp
  ring

/-! ## Poisson summation -/

/-- **Poisson summation for a `C²` source truncated to `[a, b]`** (equation `(5)` of the card, with
the zero mode separated).  The lattice sum of the source equals the mean `u^{-1}∫f` plus the limit of
the symmetric transform partial sums; the limit exists but the series is not absolutely convergent,
which is why the statement is a `Tendsto` and not a `HasSum`.

The two hypotheses `a/u ∉ ℤ`, `b/u ∉ ℤ` are the card's "for almost every `v`": they say that no
lattice point sits exactly on an endpoint, which is where the periodisation is discontinuous. -/
theorem tendsto_sum_cosTransform {a b u : ℝ} (hab : a ≤ b) (hu : 0 < u)
    (hna : ∀ k : ℤ, a / u ≠ (k : ℝ)) (hnb : ∀ k : ℤ, b / u ≠ (k : ℝ))
    {h h' h'' : ℝ → ℝ}
    (hd1 : ∀ x ∈ Icc a b, HasDerivAt h (h' x) x)
    (hd2 : ∀ x ∈ Icc a b, HasDerivAt h' (h'' x) x)
    (hc2 : ContinuousOn h'' (Icc a b)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (2 / u) * ∫ t in a..b, h t * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u))) atTop
      (𝓝 ((∑ m ∈ Finset.Ioc ⌊a / u⌋ ⌊b / u⌋, h ((m : ℝ) * u))
        - (1 / u) * ∫ t in a..b, h t)) := by
  classical
  -- the two halves of the series
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, ∀ n : ℕ, A n =
      (h b * Real.sin (2 * Real.pi * b * ((n : ℝ) / u))
        - h a * Real.sin (2 * Real.pi * a * ((n : ℝ) / u))) / (Real.pi * (n : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, ∀ n : ℕ, B n = (u / (2 * Real.pi ^ 2)) *
      ((h' b * Real.cos (2 * Real.pi * b * ((n : ℝ) / u))
        - h' a * Real.cos (2 * Real.pi * a * ((n : ℝ) / u))
        - ∫ t in a..b, h'' t * Real.cos (2 * Real.pi * t * ((n : ℝ) / u))) / (n : ℝ) ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hA0 : A 0 = 0 := by rw [hA]; norm_num
  have hB0 : B 0 = 0 := by rw [hB]; norm_num
  have hlimA : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, A n) atTop
      (𝓝 (h b * sawUnit (b / u) - h a * sawUnit (a / u))) :=
    (tendsto_sum_endpointSine hu hna hnb).congr fun N => by
      exact Finset.sum_congr rfl fun n _ => (hA n).symm
  have hlimB : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, B n) atTop
      (𝓝 (u * (-(sawPrimitive (b / u) * h' b) + sawPrimitive (a / u) * h' a
        + ∫ t in a..b, sawPrimitive (t / u) * h'' t))) := by
    refine (hasSum_endpointCos hab hu hd2 hc2).tendsto_sum_nat.congr fun N => ?_
    exact Finset.sum_congr rfl fun n _ => (hB n).symm
  -- shifting the index by one costs nothing, because both first terms vanish
  have hshift : ∀ (f : ℕ → ℝ), f 0 = 0 → ∀ N : ℕ,
      (∑ n ∈ Finset.range N, f (n + 1)) = ∑ n ∈ Finset.range (N + 1), f n := by
    intro f hf0 N
    rw [Finset.sum_range_succ' f N, hf0, add_zero]
  have hlimA' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, A (n + 1)) atTop
      (𝓝 (h b * sawUnit (b / u) - h a * sawUnit (a / u))) := by
    refine (hlimA.comp (tendsto_add_atTop_nat 1)).congr fun N => ?_
    exact (hshift A hA0 N).symm
  have hlimB' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, B (n + 1)) atTop
      (𝓝 (u * (-(sawPrimitive (b / u) * h' b) + sawPrimitive (a / u) * h' a
        + ∫ t in a..b, sawPrimitive (t / u) * h'' t))) := by
    refine (hlimB.comp (tendsto_add_atTop_nat 1)).congr fun N => ?_
    exact (hshift B hB0 N).symm
  -- the term identity
  have hterm : ∀ n : ℕ,
      (2 / u) * (∫ t in a..b, h t * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)))
        = A (n + 1) + B (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hA, hB, hcast]
    exact cosTransform_term hab hu hpos hd1 hd2 hc2
  -- assemble
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N,
      (2 / u) * ∫ t in a..b, h t * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)))
      = (∑ n ∈ Finset.range N, A (n + 1)) + ∑ n ∈ Finset.range N, B (n + 1) := by
    intro N
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => hterm n
  have hgoal : (∑ m ∈ Finset.Ioc ⌊a / u⌋ ⌊b / u⌋, h ((m : ℝ) * u))
      - (1 / u) * (∫ t in a..b, h t)
      = (h b * sawUnit (b / u) - h a * sawUnit (a / u))
        + u * (-(sawPrimitive (b / u) * h' b) + sawPrimitive (a / u) * h' a
          + ∫ t in a..b, sawPrimitive (t / u) * h'' t) := by
    rw [em_dilated hab hu hd1 hd2 hc2]
    ring
  rw [hgoal]
  exact (hlimA'.add hlimB').congr fun N => (hsum N).symm

/-! ## The even source: the positive-half form of the identity -/

/-- A symmetric lattice window, folded onto its positive half. -/
theorem sum_Ioc_symm {M : ℤ} (hM : 0 ≤ M) {f : ℤ → ℝ} (hf : ∀ m : ℤ, f (-m) = f m) :
    (∑ m ∈ Finset.Ioc (-M - 1) M, f m) = f 0 + 2 * ∑ m ∈ Finset.Icc 1 M, f m := by
  have hdisj : Disjoint (Finset.Ioc (-M - 1) (-1)) (Finset.Ioc (-1 : ℤ) M) := by
    refine Finset.disjoint_left.mpr fun m h1 h2 => ?_
    simp only [Finset.mem_Ioc] at h1 h2
    omega
  have hsplit : (∑ m ∈ Finset.Ioc (-M - 1) M, f m)
      = (∑ m ∈ Finset.Ioc (-M - 1) (-1), f m) + ∑ m ∈ Finset.Ioc (-1 : ℤ) M, f m := by
    rw [← Finset.sum_union hdisj, Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
  have hleft : Finset.Ioc (-M - 1) (-1) = Finset.Icc (-M) (-1) := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hrefl : (∑ m ∈ Finset.Icc (-M) (-1), f m) = ∑ m ∈ Finset.Icc 1 M, f m := by
    have hmap : (Finset.Icc 1 M).map (Equiv.neg ℤ).toEmbedding = Finset.Icc (-M) (-1) := by
      ext m
      simp only [Finset.mem_map, Finset.mem_Icc, Equiv.coe_toEmbedding, Equiv.neg_apply]
      constructor
      · rintro ⟨k, hk, rfl⟩; omega
      · intro hm; exact ⟨-m, by omega, by omega⟩
    rw [← hmap, Finset.sum_map]
    exact Finset.sum_congr rfl fun m _ => hf m
  have hright : (∑ m ∈ Finset.Ioc (-1 : ℤ) M, f m) = f 0 + ∑ m ∈ Finset.Icc 1 M, f m := by
    have hins : Finset.Ioc (-1 : ℤ) M = insert 0 (Finset.Icc 1 M) := by
      ext m; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert (by simp)]
  rw [hsplit, hleft, hrefl, hright]
  ring

/-- **Equation (2).**  For an even `C²` source of total integral zero, the CCM arithmetic sum of the
source over the positive half of the lattice `uℤ` equals the transform tail plus the zero-mode
correction:

```text
sqrt(u) sum_(m>=1) f(mu) = (1/sqrt u) sum_(n>=1) Ff(n/u) - sqrt(u) f(0)/2,
```

which with `u = 1/v` is the card's `E(f)(1/v) = sqrt(v) sum_(n>=1) Ff(nv) - f(0)/(2 sqrt v)`.  The
transform is the real cosine transform, which for an even source is the whole Fourier transform. -/
theorem tendsto_poissonHalfSum {lam u : ℝ} (hlam : 0 < lam) (hu : 0 < u)
    (hnl : ∀ k : ℤ, lam / u ≠ (k : ℝ))
    {h h' h'' : ℝ → ℝ} (heven : ∀ x, h (-x) = h x)
    (hd1 : ∀ x ∈ Icc (-lam) lam, HasDerivAt h (h' x) x)
    (hd2 : ∀ x ∈ Icc (-lam) lam, HasDerivAt h' (h'' x) x)
    (hc2 : ContinuousOn h'' (Icc (-lam) lam))
    (hzero : (∫ t in (-lam)..lam, h t) = 0) :
    Tendsto (fun N : ℕ => (1 / Real.sqrt u) * ∑ n ∈ Finset.range N,
        ∫ t in (-lam)..lam, h t * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u))) atTop
      (𝓝 (Real.sqrt u * (∑ m ∈ Finset.Icc 1 ⌊lam / u⌋, h ((m : ℝ) * u))
        + Real.sqrt u * h 0 / 2)) := by
  have hune : u ≠ 0 := hu.ne'
  have hsq : Real.sqrt u ≠ 0 := Real.sqrt_ne_zero'.mpr hu
  have hab : -lam ≤ lam := by linarith
  have hna : ∀ k : ℤ, (-lam) / u ≠ (k : ℝ) := by
    intro k hk
    refine hnl (-k) ?_
    have hflip : lam / u = -((-lam) / u) := by ring
    rw [hflip, hk]
    push_cast
    ring
  have h5 := tendsto_sum_cosTransform hab hu hna hnl hd1 hd2 hc2
  rw [hzero, mul_zero, sub_zero] at h5
  -- fold the two-sided lattice sum
  have hM : (0 : ℤ) ≤ ⌊lam / u⌋ := Int.le_floor.mpr (by push_cast; positivity)
  have hfl : ⌊(-lam) / u⌋ = -⌊lam / u⌋ - 1 := by
    rw [neg_div]
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · push_cast; linarith [Int.lt_floor_add_one (lam / u)]
    · push_cast
      have h1 : ((⌊lam / u⌋ : ℤ) : ℝ) ≤ lam / u := Int.floor_le _
      have h2 : ((⌊lam / u⌋ : ℤ) : ℝ) ≠ lam / u := fun hc => hnl ⌊lam / u⌋ hc.symm
      have := lt_of_le_of_ne h1 h2
      linarith
  have hfold : (∑ m ∈ Finset.Ioc ⌊(-lam) / u⌋ ⌊lam / u⌋, h ((m : ℝ) * u))
      = h 0 + 2 * ∑ m ∈ Finset.Icc 1 ⌊lam / u⌋, h ((m : ℝ) * u) := by
    rw [hfl]
    have hsymm := sum_Ioc_symm hM (f := fun m : ℤ => h ((m : ℝ) * u)) fun m => by
      rw [show (((-m : ℤ) : ℝ)) * u = -((m : ℝ) * u) from by push_cast; ring, heven]
    simpa using hsymm
  rw [hfold] at h5
  -- rescale
  have hscaled := h5.const_mul (u / 2 * (1 / Real.sqrt u))
  have hlhs : ∀ N : ℕ, (u / 2 * (1 / Real.sqrt u)) * (∑ n ∈ Finset.range N,
      (2 / u) * ∫ t in (-lam)..lam, h t * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)))
      = (1 / Real.sqrt u) * ∑ n ∈ Finset.range N,
        ∫ t in (-lam)..lam, h t * Real.cos (2 * Real.pi * t * (((n : ℝ) + 1) / u)) := by
    intro N
    rw [← Finset.mul_sum, ← mul_assoc]
    congr 1
    field_simp
  have hvalue : (u / 2 * (1 / Real.sqrt u))
      * (h 0 + 2 * ∑ m ∈ Finset.Icc 1 ⌊lam / u⌋, h ((m : ℝ) * u))
      = Real.sqrt u * (∑ m ∈ Finset.Icc 1 ⌊lam / u⌋, h ((m : ℝ) * u))
        + Real.sqrt u * h 0 / 2 := by
    have hsqsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
    have hrw : u / 2 * (1 / Real.sqrt u) = Real.sqrt u / 2 := by
      nth_rewrite 1 [← hsqsq]
      field_simp
    rw [hrw]
    ring
  rw [hvalue] at hscaled
  exact hscaled.congr hlhs

end GaloisForLFunctions.RHTower

end
