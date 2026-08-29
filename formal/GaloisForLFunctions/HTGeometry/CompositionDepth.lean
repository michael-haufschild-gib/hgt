import GaloisForLFunctions.HTGeometry.CompositionGrowthHeight
import GaloisForLFunctions.HTGeometry.AffineExponentialCascadeGrowth
import GaloisForLFunctions.HTGeometry.AffineExponentialCascadeOrder

/-!
# Positive-lower-order composition depth

`cd₊(F)` is the largest number of positive-lower-order entire factors in a decomposition of `F`
into entire maps; polynomial and affine factors are allowed in the decomposition but do not count.

The growth-depth lemma — each counted factor raises the iterated-exponential growth height by one,
each uncounted nonconstant factor raises it by zero — turns the corpus's upper bound
`¬ GrowthHeightAtLeast (entireCascade (affExp a b c) (m+1)) (m+2)` into
`cd₊(F_{m+1}) = m+1` for the affine-exponential cascade.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- **Positive-lower-order composition depth at least `k`.**  `F` factors as an `m`-fold
composition of nonconstant entire maps, at least `k` of which have positive lower order. -/
def CompositionDepthAtLeast (F : ℂ → ℂ) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (f : ℕ → ℂ → ℂ) (S : Finset ℕ),
    (∀ i, Differentiable ℂ (f i)) ∧
    (∀ i, ∃ z₁ z₂ : ℂ, f i z₁ ≠ f i z₂) ∧
    S ⊆ Finset.range m ∧ (∀ i ∈ S, PositiveLowerOrder (f i)) ∧
    k ≤ S.card ∧ ∀ z, F z = entireCascade f m z

theorem differentiable_entireCascade_of_differentiable {f : ℕ → ℂ → ℂ} (hdiff : ∀ i, Differentiable ℂ (f i))
    (n : ℕ) : Differentiable ℂ (entireCascade f n) := by
  induction n with
  | zero => simpa [entireCascade] using differentiable_id
  | succ n ihn => exact (hdiff n).comp ihn

theorem growthHeightAtLeast_id : GrowthHeightAtLeast (id : ℂ → ℂ) 0 := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : (0 : ℝ) ≤ r := by linarith
  refine ⟨(r : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  · simp only [iterExp_zero, id]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    calc r ^ (1 / 2 : ℝ) ≤ r ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
      _ = r := Real.rpow_one r

/-- **The growth-depth lemma.**  A cascade whose factors are nonconstant entire maps has growth
height at least the number of factors with positive lower order. -/
theorem growthHeightAtLeast_entireCascade {f : ℕ → ℂ → ℂ}
    (hdiff : ∀ i, Differentiable ℂ (f i)) (hnc : ∀ i, ∃ z₁ z₂ : ℂ, f i z₁ ≠ f i z₂) :
    ∀ (m : ℕ) (S : Finset ℕ), S ⊆ Finset.range m → (∀ i ∈ S, PositiveLowerOrder (f i)) →
      GrowthHeightAtLeast (entireCascade f m) S.card := by
  intro m
  induction m with
  | zero =>
      intro S hS _
      have hSe : S = ∅ := by
        rw [← Finset.subset_empty]
        simpa using hS
      rw [hSe]
      simpa using growthHeightAtLeast_id
  | succ m ih =>
      intro S hS hpos
      have hS' : S.erase m ⊆ Finset.range m := by
        intro i hi
        have h1 := Finset.mem_of_mem_erase hi
        have h2 : i ≠ m := Finset.ne_of_mem_erase hi
        have h3 := hS h1
        rw [Finset.mem_range] at h3 ⊢
        omega
      have hposS' : ∀ i ∈ S.erase m, PositiveLowerOrder (f i) :=
        fun i hi => hpos i (Finset.mem_of_mem_erase hi)
      have hIH := ih (S.erase m) hS' hposS'
      have hdiffC : Differentiable ℂ (entireCascade f m) := differentiable_entireCascade_of_differentiable hdiff m
      by_cases hm : m ∈ S
      · have hcard : S.card = (S.erase m).card + 1 := by
          rw [Finset.card_erase_of_mem hm]
          have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hm⟩
          omega
        rw [hcard]
        exact growthHeightAtLeast_comp_add (hdiff m) hdiffC (hpos m hm) hIH
      · have hcard : S.card = (S.erase m).card := by
          rw [Finset.erase_eq_of_notMem hm]
        rw [hcard]
        have hstep := growthHeightAtLeast_comp_add (hdiff m) hdiffC
          (growthHeightAtLeast_zero_of_nonconstant (hdiff m) (hnc m)) hIH
        have heq : (S.erase m).card + 0 = (S.erase m).card := Nat.add_zero _
        rw [← heq]
        exact hstep

theorem growthHeightAtLeast_of_compositionDepth {F : ℂ → ℂ} {k : ℕ}
    (h : CompositionDepthAtLeast F k) : GrowthHeightAtLeast F k := by
  obtain ⟨m, f, S, hdiff, hnc, hS, hpos, hk, hFeq⟩ := h
  have hF : F = entireCascade f m := funext hFeq
  rw [hF]
  exact (growthHeightAtLeast_entireCascade hdiff hnc m S hS hpos).mono hk


/-! ## The affine-exponential cascade -/

theorem differentiable_affExp (a b c : ℕ → ℂ) (j : ℕ) : Differentiable ℂ (affExp a b c j) := by
  unfold affExp
  fun_prop

theorem nonconstant_affExp {a b c : ℕ → ℂ} {j : ℕ} (hb : b j ≠ 0) (hc : c j ≠ 0) :
    ∃ z₁ z₂ : ℂ, affExp a b c j z₁ ≠ affExp a b c j z₂ := by
  refine ⟨0, (Real.pi : ℂ) * Complex.I / c j, fun h => hb ?_⟩
  have hval : c j * ((Real.pi : ℂ) * Complex.I / c j) = (Real.pi : ℂ) * Complex.I := by
    field_simp
  simp only [affExp, mul_zero, Complex.exp_zero, mul_one, hval, Complex.exp_pi_mul_I] at h
  linear_combination h / 2

/-- **Every affine-exponential factor has positive lower order.** -/
theorem positiveLowerOrder_affExp {a b c : ℕ → ℂ} {j : ℕ} (hb : b j ≠ 0) (hc : c j ≠ 0) :
    PositiveLowerOrder (affExp a b c j) := by
  set K : ℝ := ‖c j‖ with hKdef
  have hK0 : 0 < K := norm_pos_iff.mpr hc
  set B : ℝ := ‖b j‖ with hBdef
  have hB0 : 0 < B := norm_pos_iff.mpr hb
  refine ⟨1 / 2, by norm_num, ?_⟩
  have hlin : Tendsto (fun r : ℝ => r * K / 2) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun x => ⟨2 * |x| / K + 2 * |x| + 1, fun r hr => ?_⟩
    have h1 : |x| ≤ r * K / 2 := by
      have h2 : 2 * |x| / K ≤ r := by
        have := abs_nonneg x
        nlinarith [hr, hK0, abs_nonneg x]
      rw [div_le_iff₀ hK0] at h2
      linarith
    calc x ≤ |x| := le_abs_self x
      _ ≤ r * K / 2 := h1
  have hexp : Tendsto (fun r : ℝ => Real.exp (r * K / 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hev1 : ∀ᶠ r : ℝ in atTop, 2 / K ≤ r ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 2)).eventually_ge_atTop _
  filter_upwards [hev1, hexp.eventually_ge_atTop (2 / B), hexp.eventually_ge_atTop ‖a j‖,
    eventually_gt_atTop (0 : ℝ)] with r hr hrB hra hr0
  have hKC : (K : ℂ) ≠ 0 := by
    simpa using ne_of_gt hK0
  refine ⟨(r : ℂ) * (starRingEnd ℂ) (c j) / (K : ℂ), ?_, ?_⟩
  · rw [norm_div, norm_mul, RCLike.norm_conj, ← hKdef]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0.le]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK0.le]
    rw [mul_div_assoc, div_self (ne_of_gt hK0), mul_one]
  · -- the exponent becomes the real number `r * K`
    have hmulconj : c j * ((starRingEnd ℂ) (c j)) = ((K ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, hKdef, Complex.sq_norm]
    have harg : c j * ((r : ℂ) * (starRingEnd ℂ) (c j) / (K : ℂ)) = ((r * K : ℝ) : ℂ) := by
      have hstep : c j * ((r : ℂ) * (starRingEnd ℂ) (c j) / (K : ℂ))
          = (r : ℂ) * (c j * (starRingEnd ℂ) (c j)) / (K : ℂ) := by ring
      rw [hstep, hmulconj]
      push_cast
      field_simp
    have hnormexp : ‖Complex.exp (((r * K : ℝ)) : ℂ)‖ = Real.exp (r * K) := by
      rw [Complex.norm_exp]
      simp
    have hsplit : Real.exp (r * K) = Real.exp (r * K / 2) * Real.exp (r * K / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hrp : (0 : ℝ) < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr0 _
    have hsq : r ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) = r := by
      rw [← Real.rpow_add hr0]
      norm_num
    have hhalf : r ^ (1 / 2 : ℝ) ≤ r * K / 2 := by
      rw [div_le_iff₀ hK0] at hr
      nlinarith [hr, hrp, hsq, hK0]
    have hexppos : (0 : ℝ) < Real.exp (r * K / 2) := Real.exp_pos _
    have hB2 : 2 ≤ B * Real.exp (r * K / 2) := by
      rw [div_le_iff₀ hB0] at hrB
      linarith
    have hlow : Real.exp (r * K / 2) ≤ B * Real.exp (r * K) - ‖a j‖ := by
      rw [hsplit]
      nlinarith [hB2, hexppos, hra]
    have hnorm : B * Real.exp (r * K) - ‖a j‖ ≤ ‖affExp a b c j
        ((r : ℂ) * (starRingEnd ℂ) (c j) / (K : ℂ))‖ := by
      have hval : affExp a b c j ((r : ℂ) * (starRingEnd ℂ) (c j) / (K : ℂ))
          = a j + b j * Complex.exp (((r * K : ℝ)) : ℂ) := by
        rw [affExp, harg]
      rw [hval]
      have h1 := norm_sub_norm_le (b j * Complex.exp (((r * K : ℝ)) : ℂ)) (-(a j))
      have h2 : b j * Complex.exp (((r * K : ℝ)) : ℂ) - (-(a j))
          = a j + b j * Complex.exp (((r * K : ℝ)) : ℂ) := by ring
      rw [h2, norm_neg, norm_mul, hnormexp, ← hBdef] at h1
      linarith
    have hgoal : iterExp 1 (r ^ (1 / 2 : ℝ)) = Real.exp (r ^ (1 / 2 : ℝ)) := by
      rw [iterExp_succ, iterExp_zero]
    rw [hgoal]
    calc Real.exp (r ^ (1 / 2 : ℝ)) ≤ Real.exp (r * K / 2) := Real.exp_le_exp.mpr hhalf
      _ ≤ B * Real.exp (r * K) - ‖a j‖ := hlow
      _ ≤ _ := hnorm

/-- **The displayed factorization.**  A length-`m+1` affine-exponential cascade has composition
depth at least `m+1`. -/
theorem compositionDepthAtLeast_affExpCascade {a b c : ℕ → ℂ}
    (hb : ∀ j, b j ≠ 0) (hc : ∀ j, c j ≠ 0) (m : ℕ) :
    CompositionDepthAtLeast (entireCascade (affExp a b c) (m + 1)) (m + 1) :=
  ⟨m + 1, affExp a b c, Finset.range (m + 1),
    fun i => differentiable_affExp a b c i,
    fun i => nonconstant_affExp (hb i) (hc i),
    Finset.Subset.refl _,
    fun i _ => positiveLowerOrder_affExp (hb i) (hc i),
    by simp, fun z => rfl⟩

/-- **No deeper factorization.**  The corpus growth bound forbids composition depth `m+2`. -/
theorem not_compositionDepthAtLeast_affExpCascade (a b c : ℕ → ℂ) (m : ℕ) :
    ¬ CompositionDepthAtLeast (entireCascade (affExp a b c) (m + 1)) (m + 2) := fun h =>
  not_growthHeightAtLeast_affExpCascade a b c m (growthHeightAtLeast_of_compositionDepth h)

/-- **`cd₊(F_n) = n` for the affine-exponential cascade.** -/
theorem compositionDepth_affExpCascade {a b c : ℕ → ℂ}
    (hb : ∀ j, b j ≠ 0) (hc : ∀ j, c j ≠ 0) (m : ℕ) :
    CompositionDepthAtLeast (entireCascade (affExp a b c) (m + 1)) (m + 1) ∧
      ¬ CompositionDepthAtLeast (entireCascade (affExp a b c) (m + 1)) (m + 2) :=
  ⟨compositionDepthAtLeast_affExpCascade hb hc m,
    not_compositionDepthAtLeast_affExpCascade a b c m⟩


/-- **Card capstone.**  Every `n`-fold composition of affine-exponential maps
`f_j(w) = a_j + b_j exp(c_j w)` has minimal algebraic-differential order and positive-lower-order
composition depth both exactly `n`.  Only `b_j ≠ 0` and `c_j ≠ 0` are needed: the card's reality and
positivity assumptions on `a_j, b_j, c_j` are not used. -/
theorem exactOrder_and_compositionDepth_affExpCascade {a b c : ℕ → ℂ}
    (hb : ∀ j, b j ≠ 0) (hc : ∀ j, c j ≠ 0) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (affExp a b c) (m + 1)) (m + 1) ∧
      CompositionDepthAtLeast (entireCascade (affExp a b c) (m + 1)) (m + 1) ∧
      ¬ CompositionDepthAtLeast (entireCascade (affExp a b c) (m + 1)) (m + 2) :=
  ⟨exactDifferentialOrder_affExpCascade hb hc m,
    compositionDepthAtLeast_affExpCascade hb hc m,
    not_compositionDepthAtLeast_affExpCascade a b c m⟩

theorem affExp_eq_exp (j : ℕ) :
    affExp (fun _ => 0) (fun _ => 1) (fun _ => 1) j = Complex.exp := by
  funext w
  simp [affExp]

/-- **The iterated exponential.**  `E_1 = exp`, `E_{n+1} = exp ∘ E_n` has
`ord_DA(E_n) = cd₊(E_n) = n`. -/
theorem exactOrder_and_compositionDepth_expTower (m : ℕ) :
    ExactDifferentialOrder (entireCascade (fun _ => Complex.exp) (m + 1)) (m + 1) ∧
      CompositionDepthAtLeast (entireCascade (fun _ => Complex.exp) (m + 1)) (m + 1) ∧
      ¬ CompositionDepthAtLeast (entireCascade (fun _ => Complex.exp) (m + 1)) (m + 2) := by
  have hfun : (fun _ : ℕ => Complex.exp) = affExp (fun _ => 0) (fun _ => 1) (fun _ => 1) := by
    funext j
    exact (affExp_eq_exp j).symm
  rw [hfun]
  exact exactOrder_and_compositionDepth_affExpCascade (fun _ => one_ne_zero)
    (fun _ => one_ne_zero) m

end GaloisForLFunctions.HTGeometry
