import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Subexponential growth on the integers

Two-sided subexponential bounds are preserved by translations, reflection,
finite sums, and scalar multiplication. These closure laws control finite
column combinations without imposing separate bounds on translated data.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Growth slower than every positive exponential in the absolute integer argument. -/
def HasSubexponentialIntegerGrowth (f : ℤ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℤ, ‖f z‖ ≤ C * Real.exp (ε * |(z : ℝ)|)

namespace HasSubexponentialIntegerGrowth

theorem const (v : E) : HasSubexponentialIntegerGrowth (fun _ : ℤ => v) := by
  intro ε hε
  refine ⟨‖v‖, norm_nonneg _, fun z => ?_⟩
  have he : 1 ≤ Real.exp (ε * |(z : ℝ)|) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hε.le (abs_nonneg _))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg v)

/-- A pointwise norm bound transfers subexponential growth. -/
theorem of_norm_le {f : ℤ → E} {g : ℤ → F} (hf : HasSubexponentialIntegerGrowth f)
    (h : ∀ z, ‖g z‖ ≤ ‖f z‖) : HasSubexponentialIntegerGrowth g := by
  intro ε hε
  obtain ⟨C, hC, hfC⟩ := hf ε hε
  exact ⟨C, hC, fun z => (h z).trans (hfC z)⟩

theorem add {f g : ℤ → E} (hf : HasSubexponentialIntegerGrowth f)
    (hg : HasSubexponentialIntegerGrowth g) : HasSubexponentialIntegerGrowth (fun z => f z + g z) := by
  intro ε hε
  obtain ⟨C, hC, hfC⟩ := hf ε hε
  obtain ⟨D, hD, hgD⟩ := hg ε hε
  refine ⟨C + D, add_nonneg hC hD, fun z => ?_⟩
  calc
    ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C * Real.exp (ε * |(z : ℝ)|) + D * Real.exp (ε * |(z : ℝ)|) :=
      add_le_add (hfC z) (hgD z)
    _ = _ := (add_mul _ _ _).symm

theorem neg {f : ℤ → E} (hf : HasSubexponentialIntegerGrowth f) :
    HasSubexponentialIntegerGrowth (fun z => -f z) := by
  apply hf.of_norm_le
  intro z
  exact le_of_eq (norm_neg _)

theorem sub {f g : ℤ → E} (hf : HasSubexponentialIntegerGrowth f)
    (hg : HasSubexponentialIntegerGrowth g) : HasSubexponentialIntegerGrowth (fun z => f z - g z) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem norm {f : ℤ → E} (hf : HasSubexponentialIntegerGrowth f) :
    HasSubexponentialIntegerGrowth (fun z => ‖f z‖) :=
  hf.of_norm_le (fun z => le_of_eq (norm_norm (f z)))

theorem reflect {f : ℤ → E} (hf : HasSubexponentialIntegerGrowth f) :
    HasSubexponentialIntegerGrowth (fun z => f (-z)) := by
  intro ε hε
  obtain ⟨C, hC, hfC⟩ := hf ε hε
  refine ⟨C, hC, fun z => ?_⟩
  simpa only [Int.cast_neg, abs_neg] using hfC (-z)

/-- A fixed translation changes only the multiplicative bound. -/
theorem translate {f : ℤ → E} (hf : HasSubexponentialIntegerGrowth f) (a : ℤ) :
    HasSubexponentialIntegerGrowth (fun z => f (a + z)) := by
  intro ε hε
  obtain ⟨C, hC, hfC⟩ := hf ε hε
  refine ⟨C * Real.exp (ε * |(a : ℝ)|), mul_nonneg hC (Real.exp_pos _).le, fun z => ?_⟩
  calc
    ‖f (a + z)‖ ≤ C * Real.exp (ε * |((a + z : ℤ) : ℝ)|) := hfC (a + z)
    _ ≤ C * Real.exp (ε * (|(a : ℝ)| + |(z : ℝ)|)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      rw [Int.cast_add]
      have hs : |(a : ℝ) + (z : ℝ)| ≤ |(a : ℝ)| + |(z : ℝ)| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (a : ℝ) (z : ℝ)
      exact mul_le_mul_of_nonneg_left hs hε.le
    _ = _ := by rw [mul_add, Real.exp_add, mul_assoc]

theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : ℤ → E} (hf : HasSubexponentialIntegerGrowth f) (a : 𝕜) :
    HasSubexponentialIntegerGrowth (fun z => a • f z) := by
  intro ε hε
  obtain ⟨C, hC, hfC⟩ := hf ε hε
  refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, fun z => ?_⟩
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hfC z) (norm_nonneg _)

/-- Every finite sum retains a bound for each positive exponential rate. -/
theorem sum {ι : Type*} [Fintype ι] {f : ι → ℤ → E}
    (hf : ∀ i, HasSubexponentialIntegerGrowth (f i)) :
    HasSubexponentialIntegerGrowth (fun z => ∑ i, f i z) := by
  intro ε hε
  choose C hC hfC using fun i => hf i ε hε
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun z => ?_⟩
  calc
    ‖∑ i, f i z‖ ≤ ∑ i, ‖f i z‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * Real.exp (ε * |(z : ℝ)|) := Finset.sum_le_sum fun i _ => hfC i z
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Coordinatewise subexponential bounds control a finite Euclidean vector. -/
theorem euclidean {ι : Type*} [Fintype ι] {f : ℤ → EuclideanSpace ℂ ι}
    (hf : ∀ i, HasSubexponentialIntegerGrowth (fun z => f z i)) :
    HasSubexponentialIntegerGrowth f := by
  classical
  have hs (i : ι) : HasSubexponentialIntegerGrowth
      (fun z => (PiLp.single 2 i (f z i) : EuclideanSpace ℂ ι)) := by
    apply (hf i).of_norm_le
    intro z
    exact le_of_eq (PiLp.norm_single 2 (fun _ : ι => ℂ) i (f z i))
  have he (z : ℤ) : (∑ i, PiLp.single 2 i (f z i)) = f z := by
    apply PiLp.ext
    intro j
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
    simp
  simpa only [he] using sum hs

#print axioms translate
#print axioms euclidean

end HasSubexponentialIntegerGrowth
end GaloisForLFunctions.HTGeometry
