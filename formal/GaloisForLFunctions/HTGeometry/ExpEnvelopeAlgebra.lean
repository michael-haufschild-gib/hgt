import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The exponential block envelope on the integer lattice

Block estimates for an operator with an exponentially localized kernel are inequalities between a
sequence and its *exponential envelope*

`(E_μ a)_n = Σ_{m ∈ ℤ} e^{-μ|n-m|} a_m`.

Stated in `ℝ≥0∞` the envelope needs no summability hypothesis, so its algebra is unconditional:
it is monotone, it dominates its argument, and — the fact the localization argument turns on — it is
almost idempotent.  The composition is not bounded by the same envelope, because the diagonal is
summed over; but

`|n-m| + |m-j| ≥ max(|n-j|, |n-m|) ≥ (|n-j| + |n-m|)/2`

splits the double kernel into a half-rate kernel in `(n,j)` times a half-rate kernel in `(n,m)`, and
the second is summable.  Hence `E_μ ∘ E_μ ≤ S · E_{μ/2}` with `S = Σ_{k ∈ ℤ} e^{-μ|k|/2}`, which is
exactly what is needed to absorb an envelope term against a growing coefficient.
-/

open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The exponential block kernel on the integer lattice. -/
def expKernel (μ : ℝ) (n m : ℤ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-μ * |(n : ℝ) - m|))

/-- The exponential block envelope of a sequence. -/
def expEnvelopeZ (μ : ℝ) (a : ℤ → ℝ≥0∞) (n : ℤ) : ℝ≥0∞ := ∑' m : ℤ, expKernel μ n m * a m

@[simp] theorem expKernel_self (μ : ℝ) (n : ℤ) : expKernel μ n n = 1 := by
  rw [expKernel, sub_self, abs_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one]

theorem expKernel_pos (μ : ℝ) (n m : ℤ) : 0 < expKernel μ n m := by
  rw [expKernel]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem expKernel_symm (μ : ℝ) (n m : ℤ) : expKernel μ n m = expKernel μ m n := by
  rw [expKernel, expKernel, abs_sub_comm]

/-- The envelope dominates its argument. -/
theorem le_expEnvelopeZ (μ : ℝ) (a : ℤ → ℝ≥0∞) (n : ℤ) : a n ≤ expEnvelopeZ μ a n := by
  have hterm : a n = expKernel μ n n * a n := by rw [expKernel_self, one_mul]
  rw [expEnvelopeZ, hterm]
  exact ENNReal.le_tsum n

/-- The envelope is monotone. -/
theorem expEnvelopeZ_mono {μ : ℝ} {a b : ℤ → ℝ≥0∞} (hab : ∀ m, a m ≤ b m) (n : ℤ) :
    expEnvelopeZ μ a n ≤ expEnvelopeZ μ b n :=
  ENNReal.tsum_le_tsum fun m => mul_le_mul' le_rfl (hab m)

/-- The envelope is additive. -/
theorem expEnvelopeZ_add (μ : ℝ) (a b : ℤ → ℝ≥0∞) (n : ℤ) :
    expEnvelopeZ μ (fun m => a m + b m) n = expEnvelopeZ μ a n + expEnvelopeZ μ b n := by
  rw [expEnvelopeZ, expEnvelopeZ, expEnvelopeZ, ← ENNReal.tsum_add]
  exact tsum_congr fun m => by rw [mul_add]

/-- The envelope commutes with a constant multiple. -/
theorem expEnvelopeZ_const_mul (μ : ℝ) (c : ℝ≥0∞) (a : ℤ → ℝ≥0∞) (n : ℤ) :
    expEnvelopeZ μ (fun m => c * a m) n = c * expEnvelopeZ μ a n := by
  rw [expEnvelopeZ, expEnvelopeZ,
    show (∑' m : ℤ, expKernel μ n m * (c * a m))
        = ∑' m : ℤ, c * (expKernel μ n m * a m) from tsum_congr fun m => by ring,
    ENNReal.tsum_mul_left]

/-! ## The half-rate splitting -/

/-- **The double kernel splits at half rate.**  The triangle inequality bounds the composed kernel
by a half-rate kernel in the endpoints times a half-rate kernel in the intermediate point. -/
theorem expKernel_mul_le_half {μ : ℝ} (hμ : 0 ≤ μ) (n m j : ℤ) :
    expKernel μ n m * expKernel μ m j ≤ expKernel (μ / 2) n j * expKernel (μ / 2) n m := by
  have htri : |(n : ℝ) - j| ≤ |(n : ℝ) - m| + |(m : ℝ) - j| := by
    have := abs_sub_le (n : ℝ) (m : ℝ) (j : ℝ)
    exact this
  have hkey : (μ / 2) * |(n : ℝ) - j| + (μ / 2) * |(n : ℝ) - m|
      ≤ μ * |(n : ℝ) - m| + μ * |(m : ℝ) - j| := by
    have h1 : (μ / 2) * |(n : ℝ) - j| ≤ (μ / 2) * (|(n : ℝ) - m| + |(m : ℝ) - j|) :=
      mul_le_mul_of_nonneg_left htri (by linarith)
    have h2 : (0 : ℝ) ≤ (μ / 2) * |(m : ℝ) - j| :=
      mul_nonneg (by linarith) (abs_nonneg _)
    linarith
  rw [expKernel, expKernel, expKernel, expKernel,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-! ## Summability of the kernel row -/

theorem summable_exp_neg_abs_int_expEnvelopeAlgebra {ν : ℝ} (hν : 0 < ν) :
    Summable fun k : ℤ => Real.exp (-ν * |(k : ℝ)|) := by
  have hr : Real.exp (-ν) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hr0 : (0 : ℝ) ≤ Real.exp (-ν) := (Real.exp_pos _).le
  have hgeo : Summable fun k : ℕ => (Real.exp (-ν)) ^ k :=
    summable_geometric_of_lt_one hr0 hr
  refine Summable.of_nat_of_neg (f := fun k : ℤ => Real.exp (-ν * |(k : ℝ)|)) ?_ ?_
  · refine hgeo.congr fun k => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    ring
  · refine hgeo.congr fun k => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    ring

/-- The kernel row has finite mass. -/
theorem tsum_expKernel_ne_top {ν : ℝ} (hν : 0 < ν) (n : ℤ) :
    (∑' m : ℤ, expKernel ν n m) ≠ ⊤ := by
  have hsum : Summable fun m : ℤ => Real.exp (-ν * |(n : ℝ) - m|) := by
    have hbase := summable_exp_neg_abs_int_expEnvelopeAlgebra hν
    have hshift := (Equiv.subLeft n).summable_iff (f := fun k : ℤ =>
      Real.exp (-ν * |(k : ℝ)|))
    refine (hshift.mpr hbase).congr fun m => ?_
    show Real.exp (-ν * |((n - m : ℤ) : ℝ)|) = Real.exp (-ν * |(n : ℝ) - m|)
    push_cast
    ring_nf
  have hnn : ∀ m : ℤ, 0 ≤ Real.exp (-ν * |(n : ℝ) - m|) := fun m => (Real.exp_pos _).le
  have heq : (∑' m : ℤ, expKernel ν n m)
      = ENNReal.ofReal (∑' m : ℤ, Real.exp (-ν * |(n : ℝ) - m|)) := by
    simp only [expKernel]
    exact (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm
  rw [heq]
  exact ENNReal.ofReal_ne_top

/-- **The envelope is almost idempotent.**  Composing two envelopes of rate `μ` costs the finite
row mass of the half-rate kernel and drops the rate to `μ/2`. -/
theorem expEnvelopeZ_comp_le {μ : ℝ} (hμ : 0 < μ) (a : ℤ → ℝ≥0∞) (n : ℤ) :
    expEnvelopeZ μ (expEnvelopeZ μ a) n
      ≤ (∑' m : ℤ, expKernel (μ / 2) n m) * expEnvelopeZ (μ / 2) a n := by
  have hstep : expEnvelopeZ μ (expEnvelopeZ μ a) n
      = ∑' m : ℤ, ∑' j : ℤ, expKernel μ n m * (expKernel μ m j * a j) := by
    rw [expEnvelopeZ]
    exact tsum_congr fun m => by rw [expEnvelopeZ, ENNReal.tsum_mul_left]
  have hbound : ∀ m j : ℤ, expKernel μ n m * (expKernel μ m j * a j)
      ≤ expKernel (μ / 2) n m * (expKernel (μ / 2) n j * a j) := by
    intro m j
    have hk := expKernel_mul_le_half hμ.le n m j
    calc expKernel μ n m * (expKernel μ m j * a j)
        = (expKernel μ n m * expKernel μ m j) * a j := by ring
      _ ≤ (expKernel (μ / 2) n j * expKernel (μ / 2) n m) * a j := mul_le_mul' hk le_rfl
      _ = expKernel (μ / 2) n m * (expKernel (μ / 2) n j * a j) := by ring
  calc expEnvelopeZ μ (expEnvelopeZ μ a) n
      = ∑' m : ℤ, ∑' j : ℤ, expKernel μ n m * (expKernel μ m j * a j) := hstep
    _ ≤ ∑' m : ℤ, ∑' j : ℤ, expKernel (μ / 2) n m * (expKernel (μ / 2) n j * a j) :=
        ENNReal.tsum_le_tsum fun m => ENNReal.tsum_le_tsum fun j => hbound m j
    _ = ∑' m : ℤ, expKernel (μ / 2) n m * expEnvelopeZ (μ / 2) a n := by
        exact tsum_congr fun m => by rw [expEnvelopeZ, ENNReal.tsum_mul_left]
    _ = (∑' m : ℤ, expKernel (μ / 2) n m) * expEnvelopeZ (μ / 2) a n := by
        rw [ENNReal.tsum_mul_right]

/-! ## The mixed-rate composition and absorption -/

/-- The total mass of a kernel row. -/
def expRowMass (ρ : ℝ) : ℝ≥0∞ := ∑' k : ℤ, expKernel ρ k 0

theorem tsum_expKernel_eq_rowMass (ρ : ℝ) (j : ℤ) :
    (∑' m : ℤ, expKernel ρ m j) = expRowMass ρ := by
  rw [expRowMass, ← (Equiv.addRight j).tsum_eq (fun m : ℤ => expKernel ρ m j)]
  refine tsum_congr fun k => ?_
  simp only [Equiv.coe_addRight]
  rw [expKernel, expKernel]
  congr 2
  push_cast
  ring_nf

theorem expRowMass_ne_top {ρ : ℝ} (hρ : 0 < ρ) : expRowMass ρ ≠ ⊤ := by
  have h : expRowMass ρ = ∑' m : ℤ, expKernel ρ 0 m := by
    rw [expRowMass]
    exact tsum_congr fun k => expKernel_symm ρ k 0
  rw [h]
  exact tsum_expKernel_ne_top hρ 0

/-- **The mixed-rate kernel splitting.**  A slow outer kernel composed with a fast inner one keeps
the slow rate between the endpoints and leaves the rate difference on the intermediate point. -/
theorem expKernel_mul_le_mixed {ν μ : ℝ} (hν : 0 ≤ ν) (n m j : ℤ) :
    expKernel ν n m * expKernel μ m j ≤ expKernel ν n j * expKernel (μ - ν) m j := by
  have htri : |(n : ℝ) - j| ≤ |(n : ℝ) - m| + |(m : ℝ) - j| := abs_sub_le _ _ _
  have hkey : ν * |(n : ℝ) - j| + (μ - ν) * |(m : ℝ) - j|
      ≤ ν * |(n : ℝ) - m| + μ * |(m : ℝ) - j| := by
    have h1 : ν * |(n : ℝ) - j| ≤ ν * (|(n : ℝ) - m| + |(m : ℝ) - j|) :=
      mul_le_mul_of_nonneg_left htri hν
    linarith [h1]
  rw [expKernel, expKernel, expKernel, expKernel,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-- **The mixed-rate composition bound.**  Composing a rate-`μ` envelope inside a strictly slower
rate-`ν` envelope costs only the finite row mass of the difference rate, and does **not** degrade
the outer rate. -/
theorem expEnvelopeZ_comp_le_mixed {ν μ : ℝ} (hν : 0 ≤ ν) (a : ℤ → ℝ≥0∞) (n : ℤ) :
    expEnvelopeZ ν (expEnvelopeZ μ a) n ≤ expRowMass (μ - ν) * expEnvelopeZ ν a n := by
  have hstep : expEnvelopeZ ν (expEnvelopeZ μ a) n
      = ∑' m : ℤ, ∑' j : ℤ, expKernel ν n m * (expKernel μ m j * a j) := by
    rw [expEnvelopeZ]
    exact tsum_congr fun m => by rw [expEnvelopeZ, ENNReal.tsum_mul_left]
  have hbound : ∀ m j : ℤ, expKernel ν n m * (expKernel μ m j * a j)
      ≤ expKernel (μ - ν) m j * (expKernel ν n j * a j) := by
    intro m j
    have hk := expKernel_mul_le_mixed (ν := ν) (μ := μ) hν n m j
    calc expKernel ν n m * (expKernel μ m j * a j)
        = (expKernel ν n m * expKernel μ m j) * a j := by ring
      _ ≤ (expKernel ν n j * expKernel (μ - ν) m j) * a j := mul_le_mul' hk le_rfl
      _ = expKernel (μ - ν) m j * (expKernel ν n j * a j) := by ring
  calc expEnvelopeZ ν (expEnvelopeZ μ a) n
      = ∑' m : ℤ, ∑' j : ℤ, expKernel ν n m * (expKernel μ m j * a j) := hstep
    _ ≤ ∑' m : ℤ, ∑' j : ℤ, expKernel (μ - ν) m j * (expKernel ν n j * a j) :=
        ENNReal.tsum_le_tsum fun m => ENNReal.tsum_le_tsum fun j => hbound m j
    _ = ∑' j : ℤ, ∑' m : ℤ, expKernel (μ - ν) m j * (expKernel ν n j * a j) := ENNReal.tsum_comm
    _ = ∑' j : ℤ, expRowMass (μ - ν) * (expKernel ν n j * a j) := by
        refine tsum_congr fun j => ?_
        rw [ENNReal.tsum_mul_right, tsum_expKernel_eq_rowMass]
    _ = expRowMass (μ - ν) * expEnvelopeZ ν a n := by
        rw [expEnvelopeZ, ENNReal.tsum_mul_left]

/-- **Absorption of an envelope term against a small coefficient.**  If a sequence is dominated by
a source plus a small multiple of its own fast envelope, then its slow envelope is at most twice
the slow envelope of the source. -/
theorem expEnvelopeZ_absorb {ν μ : ℝ} (hν : 0 ≤ ν)
    {f α : ℤ → ℝ≥0∞} {b : ℝ≥0∞} {n : ℤ}
    (hpt : ∀ m, f m ≤ α m + b * expEnvelopeZ μ f m)
    (hfin : expEnvelopeZ ν f n ≠ ⊤)
    (hsmall : b * expRowMass (μ - ν) ≤ 1 / 2) :
    expEnvelopeZ ν f n ≤ 2 * expEnvelopeZ ν α n := by
  set x : ℝ≥0∞ := expEnvelopeZ ν f n with hx
  set y : ℝ≥0∞ := expEnvelopeZ ν α n with hy
  have hchain : x ≤ y + x / 2 := by
    have h1 : x ≤ expEnvelopeZ ν (fun m => α m + b * expEnvelopeZ μ f m) n :=
      expEnvelopeZ_mono hpt n
    rw [expEnvelopeZ_add, expEnvelopeZ_const_mul] at h1
    have h2 : b * expEnvelopeZ ν (expEnvelopeZ μ f) n
        ≤ b * (expRowMass (μ - ν) * x) :=
      mul_le_mul' le_rfl (expEnvelopeZ_comp_le_mixed hν f n)
    have h3 : b * (expRowMass (μ - ν) * x) = (b * expRowMass (μ - ν)) * x := by ring
    have h4 : (b * expRowMass (μ - ν)) * x ≤ (1 / 2 : ℝ≥0∞) * x :=
      mul_le_mul' hsmall le_rfl
    have h5 : (1 / 2 : ℝ≥0∞) * x = x / 2 := by
      rw [one_div, div_eq_mul_inv, mul_comm]
    calc x ≤ y + b * expEnvelopeZ ν (expEnvelopeZ μ f) n := h1
      _ ≤ y + (b * expRowMass (μ - ν)) * x := by rw [← h3]; exact add_le_add le_rfl h2
      _ ≤ y + (1 / 2 : ℝ≥0∞) * x := add_le_add le_rfl h4
      _ = y + x / 2 := by rw [h5]
  have hhalfne : x / 2 ≠ ⊤ := by
    intro h
    exact hfin (by simpa [ENNReal.div_eq_top] using h)
  have hhalf : x / 2 ≤ y := by
    have hsplit : x / 2 + x / 2 = x := ENNReal.add_halves x
    have hle : x / 2 + x / 2 ≤ y + x / 2 := by rw [hsplit]; exact hchain
    exact ENNReal.le_of_add_le_add_right hhalfne hle
  calc x = x / 2 + x / 2 := (ENNReal.add_halves x).symm
    _ ≤ y + y := add_le_add hhalf hhalf
    _ = 2 * y := by ring


/-! ## Absorbing a linear weight by dropping the rate -/

/-- `(1+t)e^{-εt} ≤ 1/ε` for `t ≥ 0` and `0 < ε ≤ 1`. -/
theorem one_add_mul_exp_neg_le {ε t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-ε * t) ≤ 1 / ε := by
  have hlin : 1 + ε * t ≤ Real.exp (ε * t) := by
    have := Real.add_one_le_exp (ε * t)
    linarith
  have hpos : (0 : ℝ) < 1 + ε * t := by positivity
  have hexp : Real.exp (-ε * t) ≤ 1 / (1 + ε * t) := by
    rw [show -ε * t = -(ε * t) by ring, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos hlin
  have hstep : (1 + t) * Real.exp (-ε * t) ≤ (1 + t) / (1 + ε * t) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hexp (by linarith)
  refine hstep.trans ?_
  rw [div_le_div_iff₀ hpos hε]
  nlinarith [ht, hε1, hε]

/-- **A linear weight costs only a drop in rate.** -/
theorem expKernel_mul_linear_le {ν ν' : ℝ} (hε : 0 < ν - ν') (hε1 : ν - ν' ≤ 1) (n m : ℤ) :
    expKernel ν n m * ENNReal.ofReal (1 + |(n : ℝ) - m|)
      ≤ ENNReal.ofReal (1 / (ν - ν')) * expKernel ν' n m := by
  have ht : (0 : ℝ) ≤ |(n : ℝ) - m| := abs_nonneg _
  have hkey : Real.exp (-ν * |(n : ℝ) - m|) * (1 + |(n : ℝ) - m|)
      ≤ (1 / (ν - ν')) * Real.exp (-ν' * |(n : ℝ) - m|) := by
    have hsplit : Real.exp (-ν * |(n : ℝ) - m|)
        = Real.exp (-ν' * |(n : ℝ) - m|) * Real.exp (-(ν - ν') * |(n : ℝ) - m|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    have hbound := one_add_mul_exp_neg_le hε hε1 ht
    have hexp0 : (0 : ℝ) ≤ Real.exp (-ν' * |(n : ℝ) - m|) := (Real.exp_pos _).le
    calc Real.exp (-ν' * |(n : ℝ) - m|) * Real.exp (-(ν - ν') * |(n : ℝ) - m|)
          * (1 + |(n : ℝ) - m|)
        = Real.exp (-ν' * |(n : ℝ) - m|)
            * ((1 + |(n : ℝ) - m|) * Real.exp (-(ν - ν') * |(n : ℝ) - m|)) := by ring
      _ ≤ Real.exp (-ν' * |(n : ℝ) - m|) * (1 / (ν - ν')) :=
          mul_le_mul_of_nonneg_left hbound hexp0
      _ = (1 / (ν - ν')) * Real.exp (-ν' * |(n : ℝ) - m|) := by ring
  rw [expKernel, expKernel, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (ν - ν'))]
  exact ENNReal.ofReal_le_ofReal hkey

/-- **The weighted envelope bound.**  A weight growing at most linearly in the block distance is
absorbed by dropping the envelope rate, at the cost of the reciprocal rate gap. -/
theorem expEnvelopeZ_weighted_le {ν ν' : ℝ} (hε : 0 < ν - ν') (hε1 : ν - ν' ≤ 1)
    {w : ℤ → ℝ≥0∞} {K : ℝ≥0∞} {n : ℤ}
    (hw : ∀ m, w m ≤ K * ENNReal.ofReal (1 + |(n : ℝ) - m|)) (y : ℤ → ℝ≥0∞) :
    expEnvelopeZ ν (fun m => w m * y m) n
      ≤ (K * ENNReal.ofReal (1 / (ν - ν'))) * expEnvelopeZ ν' y n := by
  have hterm : ∀ m : ℤ, expKernel ν n m * (w m * y m)
      ≤ (K * ENNReal.ofReal (1 / (ν - ν'))) * (expKernel ν' n m * y m) := by
    intro m
    calc expKernel ν n m * (w m * y m)
        ≤ expKernel ν n m * ((K * ENNReal.ofReal (1 + |(n : ℝ) - m|)) * y m) :=
          mul_le_mul' le_rfl (mul_le_mul' (hw m) le_rfl)
      _ = K * ((expKernel ν n m * ENNReal.ofReal (1 + |(n : ℝ) - m|)) * y m) := by ring
      _ ≤ K * ((ENNReal.ofReal (1 / (ν - ν')) * expKernel ν' n m) * y m) :=
          mul_le_mul' le_rfl (mul_le_mul' (expKernel_mul_linear_le hε hε1 n m) le_rfl)
      _ = (K * ENNReal.ofReal (1 / (ν - ν'))) * (expKernel ν' n m * y m) := by ring
  calc expEnvelopeZ ν (fun m => w m * y m) n
      ≤ ∑' m : ℤ, (K * ENNReal.ofReal (1 / (ν - ν'))) * (expKernel ν' n m * y m) :=
        ENNReal.tsum_le_tsum hterm
    _ = (K * ENNReal.ofReal (1 / (ν - ν'))) * expEnvelopeZ ν' y n := by
        rw [ENNReal.tsum_mul_left, expEnvelopeZ]


/-! ## The envelope preserves exponential decay -/

/-- The kernel against an exponentially decaying weight. -/
theorem expKernel_mul_exp_le {μ δ : ℝ} (hδ : 0 ≤ δ) (n m : ℤ) {C : ℝ} (hC : 0 ≤ C) :
    expKernel μ n m * ENNReal.ofReal (C * Real.exp (-δ * (m : ℝ)))
      ≤ ENNReal.ofReal (C * Real.exp (-δ * (n : ℝ))) * expKernel (μ - δ) n m := by
  have hkey : -μ * |(n : ℝ) - m| + -δ * (m : ℝ)
      ≤ -δ * (n : ℝ) + -(μ - δ) * |(n : ℝ) - m| := by
    have h : δ * ((n : ℝ) - m) ≤ δ * |(n : ℝ) - m| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hδ
    nlinarith [h]
  rw [expKernel, expKernel, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C * Real.exp (-δ * (n : ℝ)))]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (-μ * |(n : ℝ) - m|) * (C * Real.exp (-δ * (m : ℝ)))
      = C * Real.exp (-μ * |(n : ℝ) - m| + -δ * (m : ℝ)) := by
        rw [Real.exp_add]
        ring
    _ ≤ C * Real.exp (-δ * (n : ℝ) + -(μ - δ) * |(n : ℝ) - m|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) hC
    _ = C * Real.exp (-δ * (n : ℝ)) * Real.exp (-(μ - δ) * |(n : ℝ) - m|) := by
        rw [Real.exp_add]
        ring

/-- **The envelope preserves exponential decay at any rate strictly below its own**, at the cost of
the row mass of the rate difference. -/
theorem expEnvelopeZ_le_of_exp_decay {μ δ : ℝ} (hδ : 0 ≤ δ) {a : ℤ → ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ m : ℤ, a m ≤ ENNReal.ofReal (C * Real.exp (-δ * (m : ℝ)))) (n : ℤ) :
    expEnvelopeZ μ a n
      ≤ ENNReal.ofReal (C * Real.exp (-δ * (n : ℝ))) * expRowMass (μ - δ) := by
  calc expEnvelopeZ μ a n
      ≤ ∑' m : ℤ, expKernel μ n m * ENNReal.ofReal (C * Real.exp (-δ * (m : ℝ))) :=
        ENNReal.tsum_le_tsum fun m => mul_le_mul' le_rfl (ha m)
    _ ≤ ∑' m : ℤ, ENNReal.ofReal (C * Real.exp (-δ * (n : ℝ))) * expKernel (μ - δ) n m :=
        ENNReal.tsum_le_tsum fun m => expKernel_mul_exp_le hδ n m hC
    _ = ENNReal.ofReal (C * Real.exp (-δ * (n : ℝ))) * ∑' m : ℤ, expKernel (μ - δ) n m := by
        rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (C * Real.exp (-δ * (n : ℝ))) * expRowMass (μ - δ) := by
        congr 1
        rw [← tsum_expKernel_eq_rowMass (μ - δ) n]
        exact tsum_congr fun m => expKernel_symm (μ - δ) n m

end GaloisForLFunctions.HTGeometry
