import GaloisForLFunctions.HTGeometry.BohrMultiFejerMultiplier
import GaloisForLFunctions.HTGeometry.BohrFejerConvergence

/-!
# The Bochner–Fejér operator

Convolution against the multi-dimensional Fejér kernel is a norm-contraction — the kernel is
nonnegative with mean one — and it acts diagonally on the characters whose frequencies are integer
combinations of the base, multiplying each by its Fejér multiplier.  Since the multipliers tend to
one, the operator converges to the identity on trigonometric polynomials with frequencies in the
base's integer span, uniformly in `t`.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- A character splits over a translation of its argument. -/
theorem expChar_add_arg (mu u t : ℝ) : expChar mu (u + t) = expChar mu u * expChar mu t := by
  simp only [expChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Continuity descends through the real-to-complex coercion. -/
theorem continuous_of_ofReal {g : ℝ → ℝ} (h : Continuous fun u => ((g u : ℝ) : ℂ)) :
    Continuous g := by
  have hre : g = fun u => (((g u : ℝ) : ℂ)).re := by
    funext u
    rw [Complex.ofReal_re]
  rw [hre]
  exact Complex.continuous_re.comp h

/-- Almost periodicity descends through the real-to-complex coercion. -/
theorem isBohrAlmostPeriodic_of_ofReal {g : ℝ → ℝ}
    (h : HTGeometry.IsBohrAlmostPeriodic fun u => ((g u : ℝ) : ℂ)) :
    HTGeometry.IsBohrAlmostPeriodic g := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := h ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hx := hτ x
  rw [← Complex.ofReal_sub, Complex.norm_real] at hx
  exact hx

/-- The real form of the multi-dimensional Fejér kernel. -/
def multiFejerKernelReal {ι : Type*} [Fintype ι] (β : ι → ℝ) (N : ι → ℕ) (u : ℝ) : ℝ :=
  ∏ j : ι, ‖fejerSum (β j) (N j) u‖ ^ 2 / ((N j : ℝ) + 1)

theorem multiFejerKernel_eq_real {ι : Type*} [Fintype ι] (β : ι → ℝ) (N : ι → ℕ) (u : ℝ) :
    multiFejerKernel β N u = ((multiFejerKernelReal β N u : ℝ) : ℂ) :=
  multiFejerKernel_eq_ofReal β N u

theorem multiFejerKernelReal_nonneg {ι : Type*} [Fintype ι] (β : ι → ℝ) (N : ι → ℕ) (u : ℝ) :
    0 ≤ multiFejerKernelReal β N u :=
  multiFejerKernel_nonneg β N u

theorem continuous_multiFejerKernelReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (N : ι → ℕ) : Continuous (multiFejerKernelReal β N) := by
  refine continuous_of_ofReal ?_
  have h : (fun u => ((multiFejerKernelReal β N u : ℝ) : ℂ)) = multiFejerKernel β N :=
    funext fun u => (multiFejerKernel_eq_real β N u).symm
  rw [h]
  exact continuous_multiFejerKernel β N

theorem isBohrAlmostPeriodic_multiFejerKernelReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (N : ι → ℕ) : HTGeometry.IsBohrAlmostPeriodic (multiFejerKernelReal β N) := by
  refine isBohrAlmostPeriodic_of_ofReal ?_
  have h : (fun u => ((multiFejerKernelReal β N u : ℝ) : ℂ)) = multiFejerKernel β N :=
    funext fun u => (multiFejerKernel_eq_real β N u).symm
  rw [h]
  exact isBohrAlmostPeriodic_multiFejerKernel β N

/-- The real form of the multi-dimensional kernel has mean one. -/
theorem bohrMean_multiFejerKernelReal {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → ℝ}
    (hind : LinearIndependent ℚ β) (N : ι → ℕ) :
    bohrMean (multiFejerKernelReal β N) = 1 := by
  have h := bohrMean_multiFejerKernel hind N
  have hcast : bohrMean (fun u => ((multiFejerKernelReal β N u : ℝ) : ℂ))
      = ((bohrMean (multiFejerKernelReal β N) : ℝ) : ℂ) :=
    bohrMean_ofReal (continuous_multiFejerKernelReal β N)
      (isBohrAlmostPeriodic_multiFejerKernelReal β N)
  rw [funext fun u => multiFejerKernel_eq_real β N u, hcast] at h
  exact_mod_cast h

/-- **The Bochner–Fejér operator is a contraction.**  A uniform bound on the function bounds every
convolution against the kernel. -/
theorem norm_bohrMean_translate_mul_multiFejerKernel_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → ℝ} (hind : LinearIndependent ℚ β) (N : ι → ℕ) {g : ℝ → ℂ} (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (t : ℝ) :
    ‖bohrMean (fun u => g (u + t) * multiFejerKernel β N u)‖ ≤ B := by
  classical
  have hgtc : Continuous fun u : ℝ => g (u + t) := hgc.comp (continuous_id.add continuous_const)
  have hgta : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => g (u + t) :=
    isBohrAlmostPeriodic_comp_add_const hga t
  have hKc : Continuous (multiFejerKernel β N) := continuous_multiFejerKernel β N
  have hKa : HTGeometry.IsBohrAlmostPeriodic (multiFejerKernel β N) :=
    isBohrAlmostPeriodic_multiFejerKernel β N
  have hprodc : Continuous fun u : ℝ => g (u + t) * multiFejerKernel β N u := hgtc.mul hKc
  have hproda : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => g (u + t) * multiFejerKernel β N u :=
    isBohrAlmostPeriodic_mul hgtc hgta hKc hKa
  refine le_trans (norm_bohrMean_le_bohrMean_norm hprodc hproda) ?_
  have hnormeq : ∀ u : ℝ, ‖g (u + t) * multiFejerKernel β N u‖
      = ‖g (u + t)‖ * multiFejerKernelReal β N u := by
    intro u
    rw [norm_mul, multiFejerKernel_eq_real, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (multiFejerKernelReal_nonneg β N u)]
  have hnormc : Continuous fun u : ℝ => ‖g (u + t) * multiFejerKernel β N u‖ := hprodc.norm
  have hnorma : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ =>
      ‖g (u + t) * multiFejerKernel β N u‖ := isBohrAlmostPeriodic_norm_real hproda
  have hboundc : Continuous fun u : ℝ => B * multiFejerKernelReal β N u :=
    continuous_const.mul (continuous_multiFejerKernelReal β N)
  have hbounda : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => B * multiFejerKernelReal β N u :=
    isBohrAlmostPeriodic_const_mul_real B (isBohrAlmostPeriodic_multiFejerKernelReal β N)
  refine le_trans (bohrMean_le_bohrMean hnormc hnorma hboundc hbounda ?_) ?_
  · intro u
    rw [hnormeq u]
    exact mul_le_mul_of_nonneg_right (hB _) (multiFejerKernelReal_nonneg β N u)
  · rw [bohrMean_const_mul_real B (continuous_multiFejerKernelReal β N)
      (isBohrAlmostPeriodic_multiFejerKernelReal β N), bohrMean_multiFejerKernelReal hind N,
      mul_one]

/-- **Diagonal action on characters.**  The operator multiplies a character whose frequency is an
integer combination of the base by its Fejér multiplier. -/
theorem bohrMean_translate_expChar_mul_multiFejerKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → ℝ} (hind : LinearIndependent ℚ β) (N : ι → ℕ) (m : ι → ℤ)
    (hm : ∀ j, (m j).natAbs ≤ N j) (t : ℝ) :
    bohrMean (fun u => expChar (∑ j : ι, (m j : ℝ) * β j) (u + t) * multiFejerKernel β N u)
      = ((fejerMultiplier N m : ℝ) : ℂ) * expChar (∑ j : ι, (m j : ℝ) * β j) t := by
  classical
  set lam : ℝ := ∑ j : ι, (m j : ℝ) * β j with hlam
  have hKc : Continuous (multiFejerKernel β N) := continuous_multiFejerKernel β N
  have hKa : HTGeometry.IsBohrAlmostPeriodic (multiFejerKernel β N) :=
    isBohrAlmostPeriodic_multiFejerKernel β N
  have hc : Continuous fun u : ℝ => expChar lam u * multiFejerKernel β N u :=
    (continuous_expChar lam).mul hKc
  have ha : HTGeometry.IsBohrAlmostPeriodic fun u : ℝ => expChar lam u * multiFejerKernel β N u :=
    isBohrAlmostPeriodic_mul (continuous_expChar lam) (isBohrAlmostPeriodic_expChar lam) hKc hKa
  have hfun : (fun u => expChar lam (u + t) * multiFejerKernel β N u)
      = fun u => expChar lam t * (expChar lam u * multiFejerKernel β N u) := by
    funext u
    rw [expChar_add_arg]
    ring
  rw [hfun, bohrMean_const_mul _ hc ha, bohrMean_expChar_mul_multiFejerKernel hind N m hm]
  ring

/-- The Fejér multiplier is nonnegative. -/
theorem fejerMultiplier_nonneg {ι : Type*} [Fintype ι] (N : ι → ℕ) (m : ι → ℤ)
    (hm : ∀ j, (m j).natAbs ≤ N j) : 0 ≤ fejerMultiplier N m := by
  refine Finset.prod_nonneg fun j _ => ?_
  have hN : (0 : ℝ) < (N j : ℝ) + 1 := by positivity
  have hle : ((m j).natAbs : ℝ) ≤ (N j : ℝ) := by exact_mod_cast hm j
  rw [sub_nonneg, div_le_one hN]
  linarith

/-- The Fejér multiplier is at most one. -/
theorem fejerMultiplier_le_one {ι : Type*} [Fintype ι] (N : ι → ℕ) (m : ι → ℤ)
    (hm : ∀ j, (m j).natAbs ≤ N j) : fejerMultiplier N m ≤ 1 := by
  refine Finset.prod_le_one (fun j _ => ?_) (fun j _ => ?_)
  · have hN : (0 : ℝ) < (N j : ℝ) + 1 := by positivity
    have hle : ((m j).natAbs : ℝ) ≤ (N j : ℝ) := by exact_mod_cast hm j
    rw [sub_nonneg, div_le_one hN]
    linarith
  · have : (0 : ℝ) ≤ ((m j).natAbs : ℝ) / ((N j : ℝ) + 1) := by positivity
    linarith

/-- A product of numbers in `[0,1]` is not far below one. -/
theorem one_sub_prod_le_sum_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    1 - ∏ i ∈ s, x i ≤ ∑ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hp0 : 0 ≤ ∏ i ∈ s, x i := Finset.prod_nonneg fun i _ => h0 i
      have hp1 : ∏ i ∈ s, x i ≤ 1 := Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i)
      nlinarith [ih, h0 a, h1 a, hp0, hp1,
        mul_nonneg (sub_nonneg.mpr (h1 a)) (sub_nonneg.mpr hp1)]

/-- **The multipliers tend to one.**  The defect of the Fejér multiplier is at most the sum of the
relative sizes of the integer coordinates. -/
theorem one_sub_fejerMultiplier_le {ι : Type*} [Fintype ι] (N : ι → ℕ) (m : ι → ℤ)
    (hm : ∀ j, (m j).natAbs ≤ N j) :
    1 - fejerMultiplier N m ≤ ∑ j : ι, ((m j).natAbs : ℝ) / ((N j : ℝ) + 1) := by
  have hx0 : ∀ j : ι, 0 ≤ 1 - ((m j).natAbs : ℝ) / ((N j : ℝ) + 1) := by
    intro j
    have hN : (0 : ℝ) < (N j : ℝ) + 1 := by positivity
    have hle : ((m j).natAbs : ℝ) ≤ (N j : ℝ) := by exact_mod_cast hm j
    rw [sub_nonneg, div_le_one hN]
    linarith
  have hx1 : ∀ j : ι, 1 - ((m j).natAbs : ℝ) / ((N j : ℝ) + 1) ≤ 1 := by
    intro j
    have : (0 : ℝ) ≤ ((m j).natAbs : ℝ) / ((N j : ℝ) + 1) := by positivity
    linarith
  have h := one_sub_prod_le_sum_one_sub (Finset.univ : Finset ι)
    (fun j => 1 - ((m j).natAbs : ℝ) / ((N j : ℝ) + 1)) hx0 hx1
  rw [fejerMultiplier]
  refine le_trans h (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

end GaloisForLFunctions
