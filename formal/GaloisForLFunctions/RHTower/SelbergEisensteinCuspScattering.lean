import GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount
import GaloisForLFunctions.RHTower.TotientMulLSeries

open Complex LSeries
open scoped MatrixGroups LSeries.notation ArithmeticFunction.Moebius

/-!
# The row-count Dirichlet series at the cusp `σ∞` and its continuation

With `count_σ(c) = [c ≡ σ₁₀ (N)] H_N(|c|)` (`countσ_eq`) and `H_N = (μχ_N) ⍟ id`, the series
`Σ_c (c²)^{-s} count_σ(c)` equals `L(H_N Φ_σ, 2s)` with `Φ_σ = δ_{σ₁₀} + δ_{-σ₁₀}` on `ℤ/N` (`tsum_weight_eq`).
Splitting the Möbius variable `e` (coprime to `N`) by its unit class `u` turns `Φ_σ(em)` into `Φ_σ(u m)`, so
`L(H_N Φ_σ, w) = Σ_{u ∈ (ℤ/N)^×} L(μχ_N δ_u, w) · L(Φ_σ(u ·), w - 1)` (`LSeries_H_mul`), a finite sum of products of
an absolutely convergent series and a periodic (Hurwitz-type) `L`-function. This defines `D_σ(s)`
(`tsum_weight_eq_Dσ`), holomorphic on `Re s > 1/2` except at `s = 1` (`differentiableAt_Dσ`): the Dirichlet-series part of
the scattering entry `φ_{∞, σ∞}(s)` of `Γ(N)`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering
open GaloisForLFunctions.RHTower.SelbergEisensteinCusp GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount
  GaloisForLFunctions.RHTower.TotientMulMoebius GaloisForLFunctions.RHTower.TotientMulLSeries

variable (N : ℕ) [NeZero N]

/-- `μ(n)[(n,N)=1][n ≡ u (N)]`. -/
noncomputable def muChiU (u : (ZMod N)ˣ) (n : ℕ) : ℂ := muChi N n * if ((n : ZMod N) = u) then 1 else 0

/-- `x ↦ Φ(u x)`. -/
def PhiU (Φ : ZMod N → ℂ) (u : (ZMod N)ˣ) : ZMod N → ℂ := fun x => Φ ((u : ZMod N) * x)

/-- `m Φ(u m)`. -/
noncomputable def gU (Φ : ZMod N → ℂ) (u : (ZMod N)ˣ) (m : ℕ) : ℂ := (m : ℂ) * PhiU N Φ u m

omit [NeZero N] in
theorem muChi_eq_zero {e : ℕ} (h : ¬ e.Coprime N) : muChi N e = 0 := by
  simp [muChi, ArithmeticFunction.pmul_apply, chi, h]

theorem muChi_mul_eq_sum (Φ : ZMod N → ℂ) (e m : ℕ) :
    muChi N e * ((m : ℂ) * Φ ((e * m : ℕ) : ZMod N)) = ∑ u : (ZMod N)ˣ, muChiU N u e * gU N Φ u m := by
  classical
  by_cases hco : e.Coprime N
  · set u0 := ZMod.unitOfCoprime e hco
    have hu0 : ((u0 : ZMod N)) = e := ZMod.coe_unitOfCoprime e hco
    have hiff : ∀ u : (ZMod N)ˣ, ((e : ZMod N) = u) ↔ u = u0 := by
      intro u; rw [← hu0]; constructor
      · intro h; exact Units.ext h.symm
      · intro h; rw [h]
    simp only [muChiU, gU, PhiU, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp_rw [hiff]
    rw [Finset.sum_ite_eq' Finset.univ u0, if_pos (Finset.mem_univ _), hu0]
    push_cast; ring
  · simp [muChiU, muChi_eq_zero N hco]

theorem H_mul_eq_sum (Φ : ZMod N → ℂ) (n : ℕ) :
    (H N n : ℂ) * Φ n = ∑ u : (ZMod N)ˣ, (muChiU N u ⍟ gU N Φ u) n := by
  rw [H_eq_conv]
  simp only [LSeries.convolution_def, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hn : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← muChi_mul_eq_sum, hn]
  ring

omit [NeZero N] in
theorem norm_muChiU_le (u : (ZMod N)ˣ) (n : ℕ) : ‖muChiU N u n‖ ≤ 1 := by
  unfold muChiU
  rw [norm_mul]
  split_ifs
  · rw [norm_one, mul_one]; exact norm_muChi_le N n
  · rw [norm_zero, mul_zero]; exact zero_le_one

omit [NeZero N] in
theorem summable_muChiU (u : (ZMod N)ˣ) {w : ℂ} (hw : 1 < w.re) : LSeriesSummable (muChiU N u) w :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hw ⟨1, fun n _ => by
    rw [sub_self, Real.rpow_zero, mul_one]; exact norm_muChiU_le N u n⟩

omit [NeZero N] in
theorem term_gU (Φ : ZMod N → ℂ) (u : (ZMod N)ˣ) (w : ℂ) (n : ℕ) :
    LSeries.term (gU N Φ u) w n = LSeries.term (fun m : ℕ => PhiU N Φ u m) (w - 1) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', gU, cpow_sub _ _ hn0, cpow_one]
    field_simp

theorem summable_gU (Φ : ZMod N → ℂ) (u : (ZMod N)ˣ) {w : ℂ} (hw : 2 < w.re) : LSeriesSummable (gU N Φ u) w := by
  have h := ZMod.LSeriesSummable_of_one_lt_re (PhiU N Φ u) (s := w - 1) (by simp; linarith)
  unfold LSeriesSummable at h ⊢
  exact h.congr (fun n => (term_gU N Φ u w n).symm)

theorem LSeries_gU (Φ : ZMod N → ℂ) (u : (ZMod N)ˣ) {w : ℂ} (hw : 2 < w.re) :
    LSeries (gU N Φ u) w = ZMod.LFunction (PhiU N Φ u) (w - 1) := by
  rw [ZMod.LFunction_eq_LSeries _ (by simp; linarith)]
  unfold LSeries
  exact tsum_congr (term_gU N Φ u w)

/-- **`L(H_N Φ, w) = Σ_{u ∈ (ℤ/N)^×} L(μχ_N δ_u, w) · L(Φ(u ·), w - 1)`** for `Re w > 2`. -/
theorem LSeries_H_mul (Φ : ZMod N → ℂ) {w : ℂ} (hw : 2 < w.re) :
    LSeries (fun n => (H N n : ℂ) * Φ n) w =
      ∑ u : (ZMod N)ˣ, LSeries (muChiU N u) w * ZMod.LFunction (PhiU N Φ u) (w - 1) := by
  have e : (fun n => (H N n : ℂ) * Φ n) = ∑ u : (ZMod N)ˣ, (muChiU N u ⍟ gU N Φ u) := by
    funext n; rw [H_mul_eq_sum, Finset.sum_apply]
  rw [e, LSeries_sum (fun u _ => ?_)]
  · apply Finset.sum_congr rfl
    intro u _
    rw [LSeries_convolution' (summable_muChiU N u (by linarith)) (summable_gU N Φ u hw), LSeries_gU N Φ u hw]
  · exact LSeriesSummable.convolution (summable_muChiU N u (by linarith)) (summable_gU N Φ u hw)

variable (σ : SL(2, ℤ))

/-- The class indicator `Φ_σ = δ_{σ₁₀} + δ_{-σ₁₀}` on `ℤ/N`. -/
def PhiS : ZMod N → ℂ := fun x =>
  (if x = ((σ 1 0 : ℤ) : ZMod N) then 1 else 0) + (if x = -((σ 1 0 : ℤ) : ZMod N) then 1 else 0)

theorem countσ_eq {c : ℤ} (hc : c ≠ 0) :
    (countσ N σ c : ℂ) = if (c : ZMod N) = σ 1 0 then (H N c.natAbs : ℂ) else 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hφ : (N.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have h := countσ_mul_totient N σ hc
  have hH := totient_mul_eq N hN c.natAbs
  rw [mul_comm N] at hH
  split_ifs with hcl
  · rw [if_pos hcl] at h
    have h' : ((countσ N σ c * N.totient : ℕ) : ℂ) = (N.totient : ℂ) * (H N c.natAbs : ℂ) := by
      rw [h]; exact_mod_cast hH
    push_cast at h'
    exact mul_right_cancel₀ hφ (by rw [h']; ring)
  · rw [if_neg hcl] at h
    have := (mul_eq_zero.mp h).resolve_right (Nat.totient_pos.mpr hN).ne'
    simp [this]

theorem sq_cpow_neg (s : ℂ) {n : ℕ} (hn : 0 < n) :
    ((((n : ℝ)) ^ 2 : ℝ) : ℂ) ^ (-s) = 1 / (n : ℂ) ^ (2 * s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (((n : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hnR 2).ne'
  rw [cpow_def_of_ne_zero h2, cpow_def_of_ne_zero hn0, ← ofReal_natCast, ← ofReal_log (pow_pos hnR 2).le,
    ← ofReal_log hnR.le, Real.log_pow, one_div, ← Complex.exp_neg]
  congr 1; push_cast; ring

/-- **The row-count Dirichlet series** (`Re s > 1`): `Σ_c (c²)^{-s} count_σ(c) = L(H_N Φ_σ, 2s)`. -/
theorem tsum_weight_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' c : ℤ, (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ) =
      LSeries (fun n => (H N n : ℂ) * PhiS N σ n) (2 * s) := by
  set g : ℤ → ℂ := fun c => (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ)
  have hg : Summable g := by
    refine Summable.of_norm_bounded (summable_weight N σ hs) (fun c => ?_)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity) (by simp; linarith)]
    simp
  have h := hg.hasSum.nat_add_neg
  have hg0 : g 0 = 0 := by simp [g, countσ_zero]
  rw [hg0, add_zero] at h
  unfold LSeries
  refine (h.congr_fun (fun n => ?_)).tsum_eq.symm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hg0]
  have hc : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc' : (-(n : ℤ)) ≠ 0 := neg_ne_zero.mpr hc
  simp only [g]
  rw [countσ_eq N σ hc, countσ_eq N σ hc', LSeries.term_of_ne_zero hn.ne']
  simp only [Int.cast_neg, Int.cast_natCast, neg_sq, Int.natAbs_neg, Int.natAbs_natCast]
  rw [sq_cpow_neg s hn]
  unfold PhiS
  have e : ((-(n : ZMod N)) = ((σ 1 0 : ℤ) : ZMod N)) ↔ ((n : ZMod N) = -((σ 1 0 : ℤ) : ZMod N)) :=
    neg_eq_iff_eq_neg
  simp only [e]
  split_ifs <;> ring

/-- **The continued row-count series** `D_σ(s) = Σ_{u ∈ (ℤ/N)^×} L(μχ_N δ_u, 2s) · L(Φ_σ(u ·), 2s - 1)`. -/
noncomputable def Dσ (s : ℂ) : ℂ :=
  ∑ u : (ZMod N)ˣ, LSeries (muChiU N u) (2 * s) * ZMod.LFunction (PhiU N (PhiS N σ) u) (2 * s - 1)

theorem tsum_weight_eq_Dσ {s : ℂ} (hs : 1 < s.re) :
    ∑' c : ℤ, (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * (countσ N σ c : ℂ) = Dσ N σ s := by
  rw [tsum_weight_eq N σ hs, LSeries_H_mul N _ (by simp; linarith), Dσ]

omit [NeZero N] in
theorem differentiableAt_LSeries_muChiU (u : (ZMod N)ˣ) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun s : ℂ => LSeries (muChiU N u) (2 * s)) s := by
  have habs : LSeries.abscissaOfAbsConv (muChiU N u) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy => summable_muChiU N u (by simpa using hy))
  have hmem : (2 * s) ∈ {w : ℂ | LSeries.abscissaOfAbsConv (muChiU N u) < (w.re : EReal)} := by
    simp only [Set.mem_setOf_eq]
    refine lt_of_le_of_lt habs ?_
    have : (1 : ℝ) < (2 * s).re := by simp; linarith
    exact_mod_cast this
  have hopen : IsOpen {w : ℂ | LSeries.abscissaOfAbsConv (muChiU N u) < (w.re : EReal)} :=
    isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)
  exact ((LSeries_differentiableOn (muChiU N u)).differentiableAt (hopen.mem_nhds hmem)).comp s
    ((differentiable_id.const_mul 2) s)

/-- **Meromorphic continuation of the row-count series**: `D_σ` is holomorphic on `Re s > 1/2`, `s ≠ 1`. -/
theorem differentiableAt_Dσ {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (Dσ N σ) s := by
  unfold Dσ
  have : (fun s => ∑ u : (ZMod N)ˣ, LSeries (muChiU N u) (2 * s) *
      ZMod.LFunction (PhiU N (PhiS N σ) u) (2 * s - 1)) =
      ∑ u : (ZMod N)ˣ, fun s => LSeries (muChiU N u) (2 * s) * ZMod.LFunction (PhiU N (PhiS N σ) u) (2 * s - 1) := by
    funext s; simp
  rw [this]
  refine DifferentiableAt.sum (fun u _ => ?_)
  refine (differentiableAt_LSeries_muChiU N u hs).mul ?_
  refine (ZMod.differentiableAt_LFunction _ _ (Or.inl ?_)).comp s (((differentiable_id.const_mul 2).sub_const 1) s)
  intro h; apply hs1; linear_combination h / 2

end GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering
