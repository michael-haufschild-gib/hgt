import GaloisForLFunctions.HTGeometry.MultivariateEntireVanishingPower

/-!
# Strip boundedness of line-entire sources

A source is *strip bounded* when every horizontal polystrip `{x : ∀ c, |Im (x c)| ≤ V}` carries a
uniform bound — no growth at all in the real directions.  This is exactly the growth clause a
Poincare series over a *real* lattice needs: the lattice translates of a compact set stay inside one
fixed polystrip, so a strip bound is a genuine uniform bound along the whole lattice and the decay
has to come from the Gaussian damping alone.

The class is closed under sums, differences, products, powers, finite products and finite sums, and
scalar multiples, and contains the constants.  Its one-variable companion contains `sin` and the
normalized sinc.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The elementary sine bound

`HTGeometry.norm_csin_le_exp_abs_im` in `WaveTraceSpectrum` is the same estimate, but that module
imports all of Mathlib and therefore cannot be a base dependency of the quasi-Abelian chain. -/

theorem norm_complexSin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h1 : ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ ≤
      ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ := norm_sub_le _ _
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp, Complex.mul_I_re, Complex.neg_im, neg_neg]
  have h3 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp, Complex.mul_I_re]
  have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h4]
  rw [h2, h3] at h1
  have hle : Real.exp z.im + Real.exp (-z.im) ≤ 2 * Real.exp |z.im| := by
    rcases abs_cases z.im with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      have : Real.exp (-z.im) ≤ Real.exp z.im := by
        refine Real.exp_le_exp.mpr ?_
        rcases abs_cases z.im with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [abs_nonneg z.im, he]
      linarith
    · rw [he]
      have : Real.exp z.im ≤ Real.exp (-z.im) := by
        refine Real.exp_le_exp.mpr ?_
        rcases abs_cases z.im with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith [abs_nonneg z.im, he]
      linarith
  have hdiv : ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ / 2
      ≤ Real.exp |z.im| := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith [h1, hle]
  exact hdiv

/-! ## The one-variable class -/

/-- A one-variable function is strip bounded when each horizontal strip carries a uniform bound. -/
def StripBoundedOne (phi : ℂ → ℂ) : Prop :=
  ∀ V : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ V → ‖phi z‖ ≤ C

/-! ## The multivariate class -/

/-- A line-entire source is strip bounded when each horizontal polystrip carries a uniform bound. -/
def StripBounded {d : ℕ} (f : MultivariateEntire d) : Prop :=
  ∀ V : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℂ, (∀ c, |(x c).im| ≤ V) → ‖f.1 x‖ ≤ C

theorem stripBounded_of_apply_eq_const {d : ℕ} {f : MultivariateEntire d} {a : ℂ}
    (h : ∀ x, f.1 x = a) : StripBounded f :=
  fun _ => ⟨‖a‖, norm_nonneg _, fun x _ => le_of_eq (by rw [h x])⟩

theorem StripBounded.mul {d : ℕ} {f g : MultivariateEntire d}
    (hf : StripBounded f) (hg : StripBounded g) :
    StripBounded (multivariateEntireMul f g) := by
  intro V
  obtain ⟨Cf, hCf0, hCf⟩ := hf V
  obtain ⟨Cg, hCg0, hCg⟩ := hg V
  refine ⟨Cf * Cg, mul_nonneg hCf0 hCg0, fun x hx => ?_⟩
  rw [multivariateEntireMul_apply, norm_mul]
  exact mul_le_mul (hCf x hx) (hCg x hx) (norm_nonneg _) hCf0

theorem StripBounded.pow {d : ℕ} {f : MultivariateEntire d} (hf : StripBounded f) (n : ℕ) :
    StripBounded (multivariateEntirePow f n) := by
  intro V
  obtain ⟨C, hC0, hC⟩ := hf V
  refine ⟨C ^ n, pow_nonneg hC0 n, fun x hx => ?_⟩
  rw [multivariateEntirePow_apply, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x hx) n

theorem StripBounded.add {d : ℕ} {f g : MultivariateEntire d}
    (hf : StripBounded f) (hg : StripBounded g) : StripBounded (f + g) := by
  intro V
  obtain ⟨Cf, hCf0, hCf⟩ := hf V
  obtain ⟨Cg, hCg0, hCg⟩ := hg V
  refine ⟨Cf + Cg, by linarith, fun x hx => ?_⟩
  have hval : (f + g).1 x = f.1 x + g.1 x := rfl
  rw [hval]
  exact le_trans (norm_add_le _ _) (add_le_add (hCf x hx) (hCg x hx))

theorem StripBounded.sub {d : ℕ} {f g : MultivariateEntire d}
    (hf : StripBounded f) (hg : StripBounded g) : StripBounded (f - g) := by
  intro V
  obtain ⟨Cf, hCf0, hCf⟩ := hf V
  obtain ⟨Cg, hCg0, hCg⟩ := hg V
  refine ⟨Cf + Cg, by linarith, fun x hx => ?_⟩
  have hval : (f - g).1 x = f.1 x - g.1 x := rfl
  rw [hval]
  exact le_trans (norm_sub_le _ _) (add_le_add (hCf x hx) (hCg x hx))

theorem StripBounded.smul {d : ℕ} {f : MultivariateEntire d} (hf : StripBounded f) (c : ℂ) :
    StripBounded (c • f) := by
  intro V
  obtain ⟨C, hC0, hC⟩ := hf V
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC0, fun x hx => ?_⟩
  have hval : (c • f).1 x = c * f.1 x := rfl
  rw [hval, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)

theorem StripBounded.finsetProd {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MultivariateEntire d) (hf : ∀ i ∈ s, StripBounded (f i)) :
    StripBounded (multivariateEntireFinsetProd s f) := by
  intro V
  classical
  have hchoice : ∀ i ∈ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℂ,
      (∀ c, |(x c).im| ≤ V) → ‖(f i).1 x‖ ≤ C := fun i hi => hf i hi V
  choose! C hC0 hC using hchoice
  refine ⟨∏ i ∈ s, C i, Finset.prod_nonneg fun i hi => hC0 i hi, fun x hx => ?_⟩
  have hval : (multivariateEntireFinsetProd s f).1 x = ∏ i ∈ s, (f i).1 x := rfl
  rw [hval, norm_prod]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => hC i hi x hx)

theorem StripBounded.finsetSum {d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MultivariateEntire d) (hf : ∀ i ∈ s, StripBounded (f i)) :
    StripBounded (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine stripBounded_of_apply_eq_const (a := 0) fun x => ?_
      simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine StripBounded.add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end

end GaloisForLFunctions.HTGeometry
