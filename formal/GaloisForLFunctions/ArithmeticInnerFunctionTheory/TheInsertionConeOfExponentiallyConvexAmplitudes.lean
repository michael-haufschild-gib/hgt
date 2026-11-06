import GaloisForLFunctions.CompletedArithmeticForms.EisensteinDivisorTrace

/-!
# Prime insertion preserves exponentially convex amplitudes

The insertion of a prime with step `ℓ = log p` and phase `θ` is the operator

`(T_{θ,ℓ} f)(x) = Σ_k U_k(cos θ) f(x + kℓ)`,

the inverse of the second difference `1 − 2 cos θ σ + σ²`, `σ` the shift by `ℓ`. Since
`U_k(cos θ) = Σ_{r+s=k} e^{i(r−s)θ}`, the value `(T f)(x)` is the Hermitian form of the Hankel kernel
`f(x + u + v)` on the vector `e^{irθ}` at the points `u = rℓ` (`ofReal_insertion_eq_tsum_pairs`).

So the cone of **exponentially convex** amplitudes, those with every Hermitian Hankel form
nonnegative, is carried into itself by every insertion at every phase
(`IsExpConvexFrom.insertion`), and its members have nonnegative insertions (`IsExpConvexFrom.nonneg`). This is
the cone on which phases play no role. Laplace mixtures of `e^{−sx}` lie in it (`isExpConvexFrom_exp`,
`IsExpConvexFrom.add`).

On the exponential decay class, which is preserved (`ExpDecayFrom.insertion`), the insertion is well
defined, with no restriction on the phase.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

noncomputable section

/-! ### The Chebyshev character -/

/-- `U_k(cos θ) = Σ_{r+s=k} e^{i(r−s)θ}`. -/
theorem ofReal_cosSum_eq_sum_antidiagonal (θ : ℝ) (k : ℕ) :
    (cosSum θ k : ℂ) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) := by
  set A : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) with hA
  have hswap : A = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      Complex.exp ((-(((p.1 : ℝ) - (p.2 : ℝ)) * θ) : ℝ) * I) := by
    rw [hA, ← Finset.Nat.sum_antidiagonal_swap]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 3
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have h2 : 2 * A = 2 * (cosSum θ k : ℂ) := by
    have e : A + A = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        (2 : ℂ) * (Real.cos (((p.1 : ℝ) - (p.2 : ℝ)) * θ) : ℂ) := by
      nth_rewrite 2 [hswap]
      rw [hA, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Complex.ofReal_cos, Complex.cos]
      push_cast
      have : -(((p.1 : ℂ) - (p.2 : ℂ)) * (θ : ℂ)) * I = -(((p.1 : ℂ) - (p.2 : ℂ)) * (θ : ℂ) * I) := by
        ring
      rw [this]
      ring_nf
    rw [two_mul, e, ← Finset.mul_sum]
    congr 1
    rw [cosSum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.cast_sub hj']
    congr 2
    ring
  exact (mul_left_cancel₀ two_ne_zero h2).symm

theorem abs_cosSum_le (θ : ℝ) (k : ℕ) : |cosSum θ k| ≤ (k : ℝ) + 1 := by
  rw [cosSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun j _ => Real.abs_cos_le_one _).trans ?_
  simp

/-! ### Exponential decay -/

/-- Exponential decay at rate `κ` on `[x₀, ∞)`. -/
def ExpDecayFrom (x₀ κ : ℝ) (f : ℝ → ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x)

/-- The insertion of a step `ℓ` at the phase `θ`. -/
def insertion (θ ℓ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∑' k : ℕ, cosSum θ k * f (x + k * ℓ)

section Decay

variable {x₀ κ ℓ θ C : ℝ} {f : ℝ → ℝ}

theorem exp_neg_lt_one (hq : 0 < κ * ℓ) : Real.exp (-(κ * ℓ)) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The geometric majorant of the pair sum. -/
theorem summable_geometric_pairs (hq : 0 < κ * ℓ) :
    Summable (fun p : ℕ × ℕ => Real.exp (-(κ * ℓ)) ^ p.1 * Real.exp (-(κ * ℓ)) ^ p.2) := by
  have hg := summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_lt_one hq)
  exact hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)

theorem abs_shift_le (hC : ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x)) (hℓ : 0 ≤ ℓ) {x : ℝ}
    (hx : x₀ ≤ x) (n : ℕ) :
    |f (x + n * ℓ)| ≤ C * Real.exp (-κ * x) * Real.exp (-(κ * ℓ)) ^ n := by
  have h := hC (x + n * ℓ) (by have : 0 ≤ (n : ℝ) * ℓ := by positivity
                               linarith)
  have e : Real.exp (-κ * (x + n * ℓ)) = Real.exp (-κ * x) * Real.exp (-(κ * ℓ)) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [e, ← mul_assoc] at h
  exact h

theorem summable_pairs (hκ : 0 < κ) (hℓ : 0 < ℓ) (hC : ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x))
    {x : ℝ} (hx : x₀ ≤ x) (θ : ℝ) :
    Summable (fun p : ℕ × ℕ => Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) *
      (f (x + ((p.1 + p.2 : ℕ) : ℝ) * ℓ) : ℂ)) := by
  have hm := (summable_geometric_pairs (κ := κ) (ℓ := ℓ) (mul_pos hκ hℓ)).mul_left
    (C * Real.exp (-κ * x))
  refine Summable.of_norm_bounded hm fun p => ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_shift_le hC hℓ.le hx (p.1 + p.2)).trans (le_of_eq ?_)
  rw [pow_add]

/-- The insertion is the Hermitian form of the Hankel kernel on the vector `e^{irθ}`. -/
theorem ofReal_insertion_eq_tsum_pairs (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hC : ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x)) {x : ℝ} (hx : x₀ ≤ x) (θ : ℝ) :
    ((insertion θ ℓ f x : ℝ) : ℂ) = ∑' p : ℕ × ℕ,
      Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) *
        (f (x + ((p.1 + p.2 : ℕ) : ℝ) * ℓ) : ℂ) := by
  have hs := summable_pairs (θ := θ) hκ hℓ hC hx
  set g : ℕ × ℕ → ℂ := fun p => Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) *
    (f (x + ((p.1 + p.2 : ℕ) : ℝ) * ℓ) : ℂ) with hg
  have eq1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq g
  have hs' : Summable (fun c => g (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ) c)) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hs
  rw [← eq1, Summable.tsum_sigma' (fun n => (hasSum_fintype _).summable) hs']
  rw [insertion, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [tsum_fintype]
  change _ = ∑ c : ↥(Finset.HasAntidiagonal.antidiagonal k), g (c : ℕ × ℕ)
  rw [Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal k) g]
  simp only [hg]
  have e : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) *
        (f (x + ((p.1 + p.2 : ℕ) : ℝ) * ℓ) : ℂ) =
      Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) * (f (x + (k : ℝ) * ℓ) : ℂ) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul, ← ofReal_cosSum_eq_sum_antidiagonal]
  push_cast
  rfl

theorem summable_insertion (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hC : ∀ x, x₀ ≤ x → |f x| ≤ C * Real.exp (-κ * x)) {x : ℝ} (hx : x₀ ≤ x) (θ : ℝ) :
    Summable (fun k : ℕ => cosSum θ k * f (x + k * ℓ)) := by
  have hq0 := exp_neg_lt_one (mul_pos hκ hℓ)
  have hq : ‖Real.exp (-(κ * ℓ))‖ < 1 := by
    rwa [Real.norm_of_nonneg (Real.exp_pos _).le]
  have h0 := summable_geometric_of_lt_one (Real.exp_pos _).le hq0
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have hm := (h1.add h0).mul_left (C * Real.exp (-κ * x))
  refine Summable.of_norm_bounded hm fun k => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h2 := abs_shift_le hC hℓ.le hx k
  have h3 := abs_cosSum_le θ k
  have hC0 : 0 ≤ C * Real.exp (-κ * x) * Real.exp (-(κ * ℓ)) ^ k :=
    (abs_nonneg _).trans h2
  calc |cosSum θ k| * |f (x + k * ℓ)| ≤ ((k : ℝ) + 1) *
        (C * Real.exp (-κ * x) * Real.exp (-(κ * ℓ)) ^ k) :=
        mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_one]; ring

/-- **The decay class is preserved by every insertion.** -/
theorem ExpDecayFrom.insertion (hκ : 0 < κ) (hℓ : 0 < ℓ) (hf : ExpDecayFrom x₀ κ f) (θ : ℝ) :
    ExpDecayFrom x₀ κ (insertion θ ℓ f) := by
  obtain ⟨C, hC0, hC⟩ := hf
  have hq0 := exp_neg_lt_one (mul_pos hκ hℓ)
  have hq : ‖Real.exp (-(κ * ℓ))‖ < 1 := by
    rwa [Real.norm_of_nonneg (Real.exp_pos _).le]
  have h0 := summable_geometric_of_lt_one (Real.exp_pos _).le hq0
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  set D : ℝ := ∑' k : ℕ, (((k : ℝ) ^ 1 * Real.exp (-(κ * ℓ)) ^ k) + Real.exp (-(κ * ℓ)) ^ k) with hD
  have hsD := h1.add h0
  have hD0 : 0 ≤ D := tsum_nonneg fun k => by positivity
  refine ⟨C * D, by positivity, fun x hx => ?_⟩
  have hs := summable_insertion (θ := θ) hκ hℓ hC hx
  have hdef : GaloisForLFunctions.ArithmeticInnerFunctionTheory.insertion θ ℓ f x =
      ∑' k : ℕ, cosSum θ k * f (x + k * ℓ) := rfl
  rw [hdef, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  have hmaj : Summable fun k : ℕ => (((k : ℝ) ^ 1 * Real.exp (-(κ * ℓ)) ^ k) +
      Real.exp (-(κ * ℓ)) ^ k) * (C * Real.exp (-κ * x)) := hsD.mul_right _
  have hle : ∑' k : ℕ, ‖cosSum θ k * f (x + k * ℓ)‖ ≤ ∑' k : ℕ, (((k : ℝ) ^ 1 *
      Real.exp (-(κ * ℓ)) ^ k) + Real.exp (-(κ * ℓ)) ^ k) * (C * Real.exp (-κ * x)) := by
    refine hs.norm.tsum_le_tsum (fun k => ?_) hmaj
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h2 := abs_shift_le hC hℓ.le hx k
    have h3 := abs_cosSum_le θ k
    calc |cosSum θ k| * |f (x + k * ℓ)| ≤ ((k : ℝ) + 1) *
          (C * Real.exp (-κ * x) * Real.exp (-(κ * ℓ)) ^ k) :=
          mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      _ = _ := by rw [pow_one]; ring
  refine hle.trans (le_of_eq ?_)
  rw [tsum_mul_right, hD]
  ring

end Decay

/-! ### The cone -/

/-- `f` is **exponentially convex** on `[x₀, ∞)`: every Hermitian Hankel form
`Σ c_i c̄_j f(x₀ + t_i + t_j)`, `t_i ≥ 0`, is nonnegative. -/
def IsExpConvexFrom (x₀ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (ι : Type) (S : Finset ι) (t : ι → ℝ) (c : ι → ℂ), (∀ i ∈ S, 0 ≤ t i) →
    0 ≤ (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * (f (x₀ + t i + t j) : ℂ)).re

variable {x₀ κ ℓ : ℝ} {f g : ℝ → ℝ}

/-- An exponentially convex amplitude is nonnegative. -/
theorem IsExpConvexFrom.nonneg (hf : IsExpConvexFrom x₀ f) {x : ℝ} (hx : x₀ ≤ x) : 0 ≤ f x := by
  have h := hf Unit {()} (fun _ => (x - x₀) / 2) (fun _ => 1) (fun _ _ => by linarith)
  simp only [Finset.sum_singleton, map_one, mul_one, one_mul, Complex.ofReal_re] at h
  have e : x₀ + (x - x₀) / 2 + (x - x₀) / 2 = x := by ring
  rwa [e] at h

theorem IsExpConvexFrom.add (hf : IsExpConvexFrom x₀ f) (hg : IsExpConvexFrom x₀ g) :
    IsExpConvexFrom x₀ (fun x => f x + g x) := by
  intro ι S t c ht
  have h1 := hf ι S t c ht
  have h2 := hg ι S t c ht
  have e : (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * ((f (x₀ + t i + t j) + g (x₀ + t i + t j) : ℝ) : ℂ)) =
      (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * (f (x₀ + t i + t j) : ℂ)) +
        ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * (g (x₀ + t i + t j) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, Complex.add_re]
  linarith

theorem IsExpConvexFrom.const_mul (hf : IsExpConvexFrom x₀ f) {a : ℝ} (ha : 0 ≤ a) :
    IsExpConvexFrom x₀ (fun x => a * f x) := by
  intro ι S t c ht
  have h1 := hf ι S t c ht
  have e : (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * ((a * f (x₀ + t i + t j) : ℝ) : ℂ)) =
      (a : ℂ) * ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * (f (x₀ + t i + t j) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg ha h1

/-- An exponential is exponentially convex. -/
theorem isExpConvexFrom_exp (x₀ s : ℝ) : IsExpConvexFrom x₀ (fun x => Real.exp (-s * x)) := by
  intro ι S t c _
  set w : ℂ := ∑ i ∈ S, c i * (Real.exp (-s * t i) : ℂ) with hw
  have e : (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) * ((Real.exp (-s * (x₀ + t i + t j)) : ℝ) : ℂ)) =
      (Real.exp (-s * x₀) : ℂ) * (w * conj w) := by
    rw [hw, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : Real.exp (-s * (x₀ + t i + t j)) =
        Real.exp (-s * x₀) * (Real.exp (-s * t i) * Real.exp (-s * t j)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [e1]
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, Complex.mul_conj, Complex.ofReal_re]
  exact mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)

/-- **A Laplace mixture is exponentially convex.** -/
theorem isExpConvexFrom_laplace {μ : MeasureTheory.Measure ℝ} (x₀ : ℝ)
    (hμ : ∀ x, x₀ ≤ x → MeasureTheory.Integrable (fun s => Real.exp (-s * x)) μ) :
    IsExpConvexFrom x₀ (fun x => ∫ s, Real.exp (-s * x) ∂μ) := by
  intro ι S t c ht
  have hmem : ∀ i ∈ S, ∀ j ∈ S, x₀ ≤ x₀ + t i + t j := fun i hi j hj => by
    have := ht i hi
    have := ht j hj
    linarith
  have hre : (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) *
        ((∫ s, Real.exp (-s * (x₀ + t i + t j)) ∂μ : ℝ) : ℂ)).re =
      ∫ s, (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) *
        ((Real.exp (-s * (x₀ + t i + t j)) : ℝ) : ℂ)).re ∂μ := by
    simp only [Complex.re_sum, Complex.re_mul_ofReal]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [MeasureTheory.integral_const_mul]
      · exact fun j hj => (hμ _ (hmem i hi j hj)).const_mul _
    · exact fun i hi => MeasureTheory.integrable_finsetSum _ fun j hj =>
        (hμ _ (hmem i hi j hj)).const_mul _
  rw [hre]
  refine MeasureTheory.integral_nonneg fun s => ?_
  exact isExpConvexFrom_exp x₀ s ι S t c ht

/-- **The cone is carried into itself by every insertion at every phase.** -/
theorem IsExpConvexFrom.insertion (hκ : 0 < κ) (hℓ : 0 < ℓ) (hf : IsExpConvexFrom x₀ f)
    (hd : ExpDecayFrom x₀ κ f) (θ : ℝ) : IsExpConvexFrom x₀ (insertion θ ℓ f) := by
  obtain ⟨C, -, hC⟩ := hd
  intro ι S t c ht
  have hmem : ∀ i ∈ S, ∀ j ∈ S, x₀ ≤ x₀ + t i + t j := fun i hi j hj => by
    have := ht i hi
    have := ht j hj
    linarith
  -- the pair expansion of the form
  set G : ℕ × ℕ → ℂ := fun p => ∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) *
    (Complex.exp ((((p.1 : ℝ) - (p.2 : ℝ)) * θ : ℝ) * I) *
      (f (x₀ + t i + t j + ((p.1 + p.2 : ℕ) : ℝ) * ℓ) : ℂ)) with hG
  have hsum : HasSum G (∑ i ∈ S, ∑ j ∈ S, c i * conj (c j) *
      ((GaloisForLFunctions.ArithmeticInnerFunctionTheory.insertion θ ℓ f (x₀ + t i + t j) : ℝ) : ℂ)) := by
    refine hasSum_sum fun i hi => hasSum_sum fun j hj => ?_
    have hs := summable_pairs (θ := θ) hκ hℓ hC (hmem i hi j hj)
    have he := ofReal_insertion_eq_tsum_pairs (θ := θ) hκ hℓ hC (hmem i hi j hj)
    rw [he]
    exact hs.hasSum.mul_left _
  have hlim : Tendsto (fun R : ℕ => Finset.range R ×ˢ Finset.range R) atTop
      (atTop : Filter (Finset (ℕ × ℕ))) := by
    refine tendsto_atTop_finset_of_monotone (fun a b hab => ?_) fun p => ?_
    · exact Finset.product_subset_product (Finset.range_mono hab) (Finset.range_mono hab)
    · refine ⟨max p.1 p.2 + 1, ?_⟩
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (le_max_left _ _), Nat.lt_succ_of_le (le_max_right _ _)⟩
  have htend := (Complex.continuous_re.tendsto _).comp (hsum.comp hlim)
  refine ge_of_tendsto' htend fun R => ?_
  -- the partial sums are Hankel forms at the points `t_i + rℓ`
  have hform := hf (ι × ℕ) (S ×ˢ Finset.range R) (fun q => t q.1 + q.2 * ℓ)
    (fun q => c q.1 * Complex.exp (((q.2 : ℝ) * θ : ℝ) * I)) (fun q hq => by
      have h1 := ht q.1 (Finset.mem_product.mp hq).1
      have h2 : 0 ≤ (q.2 : ℝ) * ℓ := by positivity
      linarith)
  have e : ∑ q ∈ S ×ˢ Finset.range R, ∑ q' ∈ S ×ˢ Finset.range R,
      (c q.1 * Complex.exp (((q.2 : ℝ) * θ : ℝ) * I)) *
        conj (c q'.1 * Complex.exp (((q'.2 : ℝ) * θ : ℝ) * I)) *
        (f (x₀ + (t q.1 + q.2 * ℓ) + (t q'.1 + q'.2 * ℓ)) : ℂ) =
      ∑ p ∈ Finset.range R ×ˢ Finset.range R, G p := by
    simp only [Finset.sum_product, hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 : ∀ i ∈ S, (∑ j ∈ S, ∑ s ∈ Finset.range R,
        (c i * Complex.exp (((r : ℝ) * θ : ℝ) * I)) *
          conj (c j * Complex.exp (((s : ℝ) * θ : ℝ) * I)) *
          (f (x₀ + (t i + r * ℓ) + (t j + s * ℓ)) : ℂ)) =
        ∑ s ∈ Finset.range R, ∑ j ∈ S,
        (c i * Complex.exp (((r : ℝ) * θ : ℝ) * I)) *
          conj (c j * Complex.exp (((s : ℝ) * θ : ℝ) * I)) *
          (f (x₀ + (t i + r * ℓ) + (t j + s * ℓ)) : ℂ) := fun i _ => Finset.sum_comm
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have earg : x₀ + (t i + r * ℓ) + (t j + s * ℓ) =
        x₀ + t i + t j + ((r + s : ℕ) : ℝ) * ℓ := by
      push_cast
      ring
    rw [earg, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    have ee : Complex.exp ((((r : ℝ) - (s : ℝ)) * θ : ℝ) * I) =
        Complex.exp (((r : ℝ) * θ : ℝ) * I) * Complex.exp (((s : ℝ) * θ : ℝ) * -I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [ee]
    ring
  rw [e] at hform
  simpa only [Function.comp_apply] using hform

/-- A nonnegative insertion at every phase. -/
theorem IsExpConvexFrom.insertion_nonneg (hκ : 0 < κ) (hℓ : 0 < ℓ) (hf : IsExpConvexFrom x₀ f)
    (hd : ExpDecayFrom x₀ κ f) (θ : ℝ) {x : ℝ} (hx : x₀ ≤ x) :
    0 ≤ GaloisForLFunctions.ArithmeticInnerFunctionTheory.insertion θ ℓ f x :=
  (hf.insertion hκ hℓ hd θ).nonneg hx

/-! ### Finite lists of insertions -/

/-- The composite insertion along a list of (phase, step) pairs. -/
def insertAll : List (ℝ × ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | a :: L, f => insertion a.1 a.2 (insertAll L f)

/-- **Every finite composite insertion of an exponentially convex amplitude is nonnegative**: the cone
has positive spectrum at every phase, on every set of primes. -/
theorem IsExpConvexFrom.insertAll (hκ : 0 < κ) (hf : IsExpConvexFrom x₀ f) (hd : ExpDecayFrom x₀ κ f)
    (L : List (ℝ × ℝ)) (hL : ∀ a ∈ L, 0 < a.2) :
    IsExpConvexFrom x₀ (GaloisForLFunctions.ArithmeticInnerFunctionTheory.insertAll L f) ∧
      ExpDecayFrom x₀ κ (GaloisForLFunctions.ArithmeticInnerFunctionTheory.insertAll L f) := by
  induction L with
  | nil => exact ⟨hf, hd⟩
  | cons a L ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => hL b (List.mem_cons_of_mem _ hb)
    have ha := hL a List.mem_cons_self
    exact ⟨IsExpConvexFrom.insertion hκ ha h1 h2 a.1, ExpDecayFrom.insertion hκ ha h2 a.1⟩

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
