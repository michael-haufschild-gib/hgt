import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Euler-product and density bounds for free multiplicative monoids

* **Finite Euler bound.** For weights `0 ≤ e_i < 1` and any finite family `Φ` of exponent
  vectors supported in `F`: `Σ_{f ∈ Φ} Π_{i ∈ F} e_i^{f_i} ≤ Π_{i ∈ F} (1 − e_i)^{−1}`. Induction
  on `F`, sorting `Φ` by the exponent of the new index.
* **Exponential form.** If `0 ≤ e_i ≤ ½`, then `Π (1 − e_i)^{−1} ≤ exp(Σ (e_i + 2e_i²))`.
* **Relative density.** If every interval `[x, x+R]`, `x ≥ 1`, contains a value of `v`, then
  for `1 < σ ≤ 2` some finite set of values has `Σ v^{−σ} ≥ 1/(18 max(R,1)² (σ−1))`. Pick one
  value in each `[2jR, 2jR+R]`, compare with `Σ j^{−σ}`, and use the integral test.
-/

noncomputable section

namespace RHTower.FreeMonoidEuler

variable {ι : Type*} [DecidableEq ι]

/-- **Finite Euler bound.** -/
theorem sum_prod_pow_le_prod_inv (e : ι → ℝ) (he0 : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i < 1)
    (F : Finset ι) :
    ∀ Φ : Finset (ι →₀ ℕ), (∀ f ∈ Φ, f.support ⊆ F) →
      ∑ f ∈ Φ, ∏ i ∈ F, e i ^ f i ≤ ∏ i ∈ F, (1 - e i)⁻¹ := by
  induction F using Finset.induction_on with
  | empty =>
    intro Φ hΦ
    simp only [Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : Φ ⊆ {0} := fun f hf => by
      have := hΦ f hf
      rw [Finset.subset_empty, Finsupp.support_eq_empty] at this
      simp [this]
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    exact_mod_cast this
  | insert a F ha ih =>
    intro Φ hΦ
    have hgeom : ∀ K : Finset ℕ, ∑ k ∈ K, e a ^ k ≤ (1 - e a)⁻¹ := fun K => by
      rw [← tsum_geometric_of_lt_one (he0 a) (he1 a)]
      exact (summable_geometric_of_lt_one (he0 a) (he1 a)).sum_le_tsum K
        (fun k _ => pow_nonneg (he0 a) k)
    have hP : 0 ≤ ∏ i ∈ F, (1 - e i)⁻¹ :=
      Finset.prod_nonneg fun i _ => inv_nonneg.mpr (by linarith [he1 i])
    rw [← Finset.sum_fiberwise_of_maps_to (t := Φ.image fun f => f a) (g := fun f => f a)
      (fun f hf => Finset.mem_image_of_mem _ hf)]
    rw [Finset.prod_insert ha]
    calc ∑ k ∈ Φ.image (fun f => f a), ∑ f ∈ Φ with f a = k, ∏ i ∈ insert a F, e i ^ f i
        = ∑ k ∈ Φ.image (fun f => f a), e a ^ k * ∑ f ∈ Φ with f a = k, ∏ i ∈ F, e i ^ f i := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun f hf => ?_
          rw [Finset.prod_insert ha, (Finset.mem_filter.mp hf).2]
      _ ≤ ∑ k ∈ Φ.image (fun f => f a), e a ^ k * ∏ i ∈ F, (1 - e i)⁻¹ := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (pow_nonneg (he0 a) k)
          have hinj : Set.InjOn (Finsupp.erase a)
              ((Φ.filter fun f => f a = k : Finset (ι →₀ ℕ)) : Set (ι →₀ ℕ)) := by
            intro f hf f' hf' heq
            ext i
            by_cases hi : i = a
            · subst hi
              rw [(Finset.mem_filter.mp hf).2, (Finset.mem_filter.mp hf').2]
            · have := congrArg (fun h : ι →₀ ℕ => h i) heq
              simpa [Finsupp.erase_ne hi] using this
          have hsum : ∑ f ∈ Φ with f a = k, ∏ i ∈ F, e i ^ f i =
              ∑ h ∈ (Φ.filter fun f => f a = k).image (Finsupp.erase a), ∏ i ∈ F, e i ^ h i := by
            rw [Finset.sum_image hinj]
            refine Finset.sum_congr rfl fun f _ => Finset.prod_congr rfl fun i hi => ?_
            rw [Finsupp.erase_ne (by rintro rfl; exact ha hi)]
          rw [hsum]
          apply ih
          intro h hh
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hh
          rw [Finsupp.support_erase]
          intro i hi
          have hi' := Finset.mem_erase.mp hi
          have := hΦ f (Finset.mem_filter.mp hf).1 hi'.2
          rcases Finset.mem_insert.mp this with h | h
          · exact absurd h hi'.1
          · exact h
      _ = (∑ k ∈ Φ.image (fun f => f a), e a ^ k) * ∏ i ∈ F, (1 - e i)⁻¹ := by
          rw [Finset.sum_mul]
      _ ≤ (1 - e a)⁻¹ * ∏ i ∈ F, (1 - e i)⁻¹ := mul_le_mul_of_nonneg_right (hgeom _) hP

/-- `(1 − e)^{−1} ≤ exp(e + 2e²)` for `0 ≤ e ≤ ½`. -/
theorem inv_one_sub_le_exp {e : ℝ} (he : e ≤ 1 / 2) :
    (1 - e)⁻¹ ≤ Real.exp (e + 2 * e ^ 2) := by
  have hpos : 0 < 1 - e := by linarith
  rw [← Real.exp_log (inv_pos.mpr hpos)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv]
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (1 - e)⁻¹ - 1 ≤ e + 2 * e ^ 2 := by
    have : (1 - e)⁻¹ - 1 = e / (1 - e) := by field_simp; ring
    rw [this, div_le_iff₀ hpos]
    nlinarith
  linarith

omit [DecidableEq ι] in
/-- **Exponential form of the Euler bound.** -/
theorem prod_inv_le_exp_sum (F : Finset ι) (e : ι → ℝ) (he : ∀ i ∈ F, e i ≤ 1 / 2) :
    ∏ i ∈ F, (1 - e i)⁻¹ ≤ Real.exp (∑ i ∈ F, (e i + 2 * e i ^ 2)) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun i hi => inv_nonneg.mpr (by linarith [he i hi]))
    fun i hi => inv_one_sub_le_exp (he i hi)

/-- `Σ_{j=1}^{J} j^{−σ} ≥ (1 − (J+1)^{1−σ})/(σ−1)` (integral test). -/
theorem sum_rpow_neg_ge (J : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    (1 - ((J : ℝ) + 1) ^ (1 - σ)) / (σ - 1) ≤
      ∑ i ∈ Finset.range J, ((1 : ℝ) + i) ^ (-σ) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc 1 (1 + (J : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hint := hanti.integral_le_sum
  rw [integral_rpow (Or.inr ⟨by linarith, by
    simp only [Set.mem_uIcc, not_or, not_and, not_le]
    constructor <;> intro h <;> linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]⟩)] at hint
  have e1 : -σ + 1 = 1 - σ := by ring
  rw [e1, Real.one_rpow] at hint
  have hden : 1 - σ ≠ 0 := by linarith
  have : (1 - ((J : ℝ) + 1) ^ (1 - σ)) / (σ - 1) = ((1 + (J : ℝ)) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [add_comm (1 : ℝ) J, div_eq_div_iff (by linarith) hden]
    ring
  rw [this]
  exact hint

/-- **Relative density gives `ζ`-growth.** -/
theorem exists_sum_rpow_ge {α : Type*} (v : α → ℝ) {R : ℝ}
    (hR : ∀ x : ℝ, 1 ≤ x → ∃ a, x ≤ v a ∧ v a ≤ x + R) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    ∃ Φ : Finset α, 1 / (18 * (max R 1) ^ 2 * (σ - 1)) ≤ ∑ a ∈ Φ, v a ^ (-σ) := by
  classical
  set R' := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'R : R ≤ R' := le_max_left _ _
  -- the chosen values
  have hchoose : ∀ j : ℕ, ∃ a, 2 * ((j : ℝ) + 1) * R' ≤ v a ∧
      v a ≤ 2 * ((j : ℝ) + 1) * R' + R' := by
    intro j
    obtain ⟨a, h1, h2⟩ := hR (2 * ((j : ℝ) + 1) * R') (by
      have : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      nlinarith)
    exact ⟨a, h1, by linarith⟩
  choose a ha using hchoose
  have hainj : Function.Injective a := by
    intro j j' hjj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h' : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
      have := (ha j).2; have := (ha j').1; rw [hjj'] at *; nlinarith
    · have h' : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
      have := (ha j').2; have := (ha j).1; rw [hjj'] at *; nlinarith
  -- the number of values used
  have htend : Filter.Tendsto (fun J : ℕ => ((J : ℝ) + 1) ^ (1 - σ)) Filter.atTop (nhds 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < σ - 1 by linarith)).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    refine this.congr fun J => ?_
    simp only [Function.comp]
    rw [show -(σ - 1) = 1 - σ by ring]
  obtain ⟨J, hJ⟩ := (htend.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  refine ⟨(Finset.range J).image a, ?_⟩
  rw [Finset.sum_image fun x _ y _ h => hainj h]
  have hvpos : ∀ j, 0 < v (a j) := fun j => by
    have := (ha j).1; have : (0 : ℝ) < 2 * ((j : ℝ) + 1) * R' := by positivity
    linarith
  -- each term
  have hterm : ∀ j ∈ Finset.range J, (3 * R') ^ (-σ) * ((1 : ℝ) + j) ^ (-σ) ≤ v (a j) ^ (-σ) := by
    intro j _
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow_of_nonpos (hvpos j) _ (by linarith)
    have := (ha j).2
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hsum := sum_rpow_neg_ge J hσ
  have h3R : (3 * R') ^ (-(2 : ℝ)) ≤ (3 * R') ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h3R2 : (3 * R') ^ (-(2 : ℝ)) = 1 / (9 * R' ^ 2) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]; field_simp; ring
  have hhalf : 1 / (2 * (σ - 1)) ≤ ∑ i ∈ Finset.range J, ((1 : ℝ) + i) ^ (-σ) := by
    refine le_trans ?_ hsum
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  calc 1 / (18 * R' ^ 2 * (σ - 1))
      = (3 * R') ^ (-(2 : ℝ)) * (1 / (2 * (σ - 1))) := by
        rw [h3R2]; field_simp; ring
    _ ≤ (3 * R') ^ (-σ) * ∑ i ∈ Finset.range J, ((1 : ℝ) + i) ^ (-σ) :=
        mul_le_mul h3R hhalf (by positivity) (by positivity)
    _ = ∑ i ∈ Finset.range J, (3 * R') ^ (-σ) * ((1 : ℝ) + i) ^ (-σ) := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range J, v (a j) ^ (-σ) := Finset.sum_le_sum hterm

end RHTower.FreeMonoidEuler
