import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Moment bounds cap the off-line depth

An `L`-polynomial `L(u) = ∏_{α ∈ s} (1 - α u)` (the shape of the `L`-function of a curve over a
finite field, with inverse roots `s`) has its zeros `1/α` strictly inside the disc `|u| < r`
exactly for the *deep* inverse roots `|α| r > 1`.

* **Jensen ceiling** (`depthProduct_le`): `∏_{|α| r > 1} |α| r ≤ max_{|u| = r} |L(u)|`. The deep
  factors are reflected across the circle, which keeps `|L|` on the circle and removes the zeros
  from the disc; the maximum principle at `u = 0` then reads off the depth product.
* **Moments** (`depthProduct_le_of_moment`): a weighted `2k`-th moment bound on the circle over a
  finite family gives each member the depth bound `(M / w)^{1/(2k)}`.
* **Sharpness** (`depthProduct_offLinePair`, `norm_offLinePair_le`): inserting an off-line pair
  of depths `ρ > 1` and `ρ⁻¹` multiplies the depth product by `ρ` and the circle maximum by at
  most `(1 + ρ)(1 + ρ⁻¹)`.

So moment information certifies zero location only through the depth product, and a factor
independent of the degree hides any fixed number of off-line pairs. Generating functions of
moments (finite, affine or Kac–Moody multiple Dirichlet series) read exponential growth rates in
the degree, so their domains of holomorphy and natural boundaries cannot detect such pairs.
-/

open Complex Metric

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MomentDepth

noncomputable section

/-- The `L`-polynomial `∏_{α ∈ s} (1 - α u)` with inverse roots `s`. -/
def invRootPoly (s : Multiset ℂ) (u : ℂ) : ℂ :=
  (s.map fun α => 1 - α * u).prod

/-- Inverse roots of depth greater than one at radius `r`: the zero `1/α` lies in `|u| < r`. -/
def deepRoots (s : Multiset ℂ) (r : ℝ) : Multiset ℂ :=
  s.filter fun α => 1 < ‖α‖ * r

/-- The depth product `∏ |α| r` over the deep inverse roots. -/
def depthProduct (s : Multiset ℂ) (r : ℝ) : ℝ :=
  ((deepRoots s r).map fun α => ‖α‖ * r).prod

theorem norm_multiset_prod_map {ι : Type*} (m : Multiset ι) (f : ι → ℂ) :
    ‖(m.map f).prod‖ = (m.map fun i => ‖f i‖).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih]

theorem differentiable_multiset_prod_map {ι : Type*} (m : Multiset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) :
    Differentiable ℂ fun u => (m.map fun i => f i u).prod := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact differentiable_const _
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (hf a).mul ih

/-- Reflecting a factor across the circle `|u| = r` keeps its modulus there. -/
theorem norm_reflect_eq {α u : ℂ} {r : ℝ} (hr : 0 < r) (hu : ‖u‖ = r) :
    ‖(starRingEnd ℂ) α * r - u / r‖ = ‖1 - α * u‖ := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsq : (r : ℂ) ^ 2 = u * (starRingEnd ℂ) u := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    push_cast
    ring
  have key : (starRingEnd ℂ) α * r - u / r = u * (starRingEnd ℂ) (α * u - 1) / r := by
    rw [eq_div_iff hr0, sub_mul, div_mul_cancel₀ u hr0, map_sub, map_mul, map_one]
    linear_combination (starRingEnd ℂ) α * hsq
  rw [key, norm_div, norm_mul, Complex.norm_conj, hu, Complex.norm_real,
    Real.norm_of_nonneg hr.le, norm_sub_rev]
  field_simp

/-- **Jensen ceiling.** The maximum of `|L|` on the circle `|u| = r` bounds the depth product. -/
theorem depthProduct_le {s : Multiset ℂ} {r B : ℝ} (hr : 0 < r)
    (hB : ∀ u : ℂ, ‖u‖ = r → ‖invRootPoly s u‖ ≤ B) :
    depthProduct s r ≤ B := by
  classical
  set D := deepRoots s r with hD
  set O := s.filter (fun α => ¬ 1 < ‖α‖ * r) with hO
  set G : ℂ → ℂ := fun u =>
    (O.map fun α => 1 - α * u).prod * (D.map fun α => (starRingEnd ℂ) α * r - u / r).prod
    with hGdef
  have hG : Differentiable ℂ G :=
    (differentiable_multiset_prod_map O (fun α u => 1 - α * u) fun α => by fun_prop).mul
      (differentiable_multiset_prod_map D (fun α u => (starRingEnd ℂ) α * r - u / r)
        fun α => by fun_prop)
  have hsplit : ∀ u, invRootPoly s u =
      (O.map fun α => 1 - α * u).prod * (D.map fun α => 1 - α * u).prod := by
    intro u
    rw [invRootPoly, ← Multiset.prod_add, ← Multiset.map_add, hO, hD, deepRoots, add_comm,
      Multiset.filter_add_not]
  have hcircle : ∀ u : ℂ, ‖u‖ = r → ‖G u‖ = ‖invRootPoly s u‖ := by
    intro u hu
    rw [hsplit u, hGdef, norm_mul, norm_mul, norm_multiset_prod_map, norm_multiset_prod_map,
      norm_multiset_prod_map D (fun α => 1 - α * u)]
    congr 1
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => norm_reflect_eq hr hu)
  have hmax : ‖G 0‖ ≤ B := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
      hG.diffContOnCl ?_ (subset_closure (mem_ball_self hr))
    intro z hz
    rw [frontier_ball (0 : ℂ) hr.ne', mem_sphere_zero_iff_norm] at hz
    rw [hcircle z hz]
    exact hB z hz
  have hG0 : ‖G 0‖ = depthProduct s r := by
    rw [hGdef, norm_mul, norm_multiset_prod_map, norm_multiset_prod_map, depthProduct, ← hD]
    have h1 : (O.map fun α => ‖1 - α * 0‖) = O.map fun _ => (1 : ℝ) :=
      Multiset.map_congr rfl fun α _ => by simp
    have h2 : (D.map fun α => ‖(starRingEnd ℂ) α * r - 0 / r‖) = D.map fun α => ‖α‖ * r :=
      Multiset.map_congr rfl fun α _ => by
        rw [zero_div, sub_zero, norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg hr.le]
    rw [h1, h2, Multiset.map_const', Multiset.prod_replicate, one_pow, one_mul]
  rw [← hG0]
  exact hmax

/-- **Moments bound the depth.** A weighted `2k`-th moment bound on the circle over a finite
family gives each member of positive weight the depth bound `(M / w)^{1/(2k)}`. -/
theorem depthProduct_le_of_moment {ι : Type*} (S : Finset ι) (s : ι → Multiset ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) {r M : ℝ} (hr : 0 < r) {k : ℕ} (hk : 0 < k)
    (hM : ∀ u : ℂ, ‖u‖ = r → ∑ i ∈ S, w i * ‖invRootPoly (s i) u‖ ^ (2 * k) ≤ M)
    {i₀ : ι} (hi₀ : i₀ ∈ S) (hw₀ : 0 < w i₀) :
    depthProduct (s i₀) r ≤ (M / w i₀) ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
  refine depthProduct_le hr fun u hu => ?_
  set x := ‖invRootPoly (s i₀) u‖ with hx
  have hsingle : w i₀ * x ^ (2 * k) ≤ M :=
    (Finset.single_le_sum (f := fun i => w i * ‖invRootPoly (s i) u‖ ^ (2 * k))
      (fun i hi => mul_nonneg (hw i hi) (by positivity)) hi₀).trans (hM u hu)
  have hpow : x ^ (2 * k) ≤ M / w i₀ := by
    rw [le_div_iff₀ hw₀]
    linarith
  have hn : (2 * k : ℕ) ≠ 0 := by omega
  calc x = (x ^ (2 * k)) ^ (((2 * k : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (norm_nonneg _) hn).symm
    _ ≤ (M / w i₀) ^ (((2 * k : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- An off-line pair of depths `ρ` and `ρ⁻¹` costs the circle maximum at most
`(1 + ρ)(1 + ρ⁻¹)`, uniformly in the rest of the polynomial. -/
theorem norm_offLinePair_le {s : Multiset ℂ} {α β u : ℂ} {r ρ : ℝ} (hu : ‖u‖ = r)
    (hα : ‖α‖ * r = ρ) (hβ : ‖β‖ * r = ρ⁻¹) :
    ‖invRootPoly (α ::ₘ β ::ₘ s) u‖ ≤ (1 + ρ) * (1 + ρ⁻¹) * ‖invRootPoly s u‖ := by
  have h1 : ‖1 - α * u‖ ≤ 1 + ρ :=
    (norm_sub_le _ _).trans (by rw [norm_one, norm_mul, hu, hα])
  have h2 : ‖1 - β * u‖ ≤ 1 + ρ⁻¹ :=
    (norm_sub_le _ _).trans (by rw [norm_one, norm_mul, hu, hβ])
  have h1' : 0 ≤ 1 + ρ := (norm_nonneg _).trans h1
  simp only [invRootPoly, Multiset.map_cons, Multiset.prod_cons, norm_mul]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul h1 h2 (norm_nonneg _) h1') (norm_nonneg _)

/-- The inserted pair is genuinely off-line: it multiplies the depth product by exactly `ρ`. -/
theorem depthProduct_offLinePair {s : Multiset ℂ} {α β : ℂ} {r ρ : ℝ} (hρ : 1 < ρ)
    (hα : ‖α‖ * r = ρ) (hβ : ‖β‖ * r = ρ⁻¹) :
    depthProduct (α ::ₘ β ::ₘ s) r = ρ * depthProduct s r := by
  have hβ' : ¬ 1 < ‖β‖ * r := by
    rw [hβ]
    exact not_lt.mpr (inv_le_one_of_one_le₀ hρ.le)
  rw [depthProduct, deepRoots,
    Multiset.filter_cons_of_pos (p := fun γ : ℂ => 1 < ‖γ‖ * r) _ (by rw [hα]; exact hρ),
    Multiset.filter_cons_of_neg (p := fun γ : ℂ => 1 < ‖γ‖ * r) s hβ', Multiset.map_cons,
    Multiset.prod_cons, hα]
  rfl

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MomentDepth
