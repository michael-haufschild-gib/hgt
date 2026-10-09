import GaloisForLFunctions.RHTower.LeeYangFirstZeroLaw
import GaloisForLFunctions.RHTower.LeeYangRestrictionZeroCount
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Every multiaffine Lee–Yang field of frequency `λ` forces a real zero within `π/λ`

Let `L` be a Lee–Yang datum (no zero of `P` or of its reflection `P^♯` on the open polydisk) and
let `j` be a variable in which `P` is affine (`deg_{u_j} P = 1`), for instance a spin-½ site of an
Ising-type system on any graph with any couplings.  Then the restriction
`f(t) = P(e^{−iλ₁t}, …, e^{−iλₙt})` vanishes at some real `t` with `|t| ≤ π/λ_j`
(`LeeYangDatum.exists_restr_eq_zero`).

**Proof.**  Split `P = A + u_j B` (`eval_update_affine`).  Below the axis all fields lie in the
polydisk, so `A ≠ 0` and `|B| ≤ |A|`.  Above the axis all fields lie outside the closed polydisk;
the reflection identity gives `B = U · conj P^♯(…, v_j = 0, …) ≠ 0` and forbids a root of
`A + yB` with `|y| > 1`, so `|A| ≤ |B|`.  On the axis `|A| = |B|` by continuity, and the first-zero
law for inner splittings applies.

**Consequence for `Ξ`** (`not_tendstoUniformlyOn_leeYang_XiC`).  A Lee–Yang datum with a multiaffine
field of integer frequency `log n`, `n ≥ 2`, vanishes within `π/log 2 < √32`, where `Ξ` has no real
zero.  So no normalized family of such restrictions converges to `E · Ξ` uniformly on
`[−π/log 2, π/log 2]`: integer-anchored Lee–Yang producers of `Ξ` do not exist, on any graph.
-/

open Complex Set Filter Topology Finset

namespace RHTower.LeeYangCount

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Affine dependence on one variable -/

theorem prod_pow_update (α : ι →₀ ℕ) (v : ι → ℂ) (j : ι) (y : ℂ) :
    ∏ k, Function.update v j y k ^ α k = y ^ α j * ∏ k ∈ univ \ {j}, v k ^ α k := by
  have h : (fun k => Function.update v j y k ^ α k) =
      Function.update (fun k => v k ^ α k) j (y ^ α j) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [h, Finset.prod_update_of_mem (mem_univ j)]

theorem eval_update_affine (P : MvPolynomial ι ℂ) (j : ι) (hP : P.degreeOf j ≤ 1)
    (v : ι → ℂ) (y : ℂ) :
    MvPolynomial.eval (Function.update v j y) P =
      MvPolynomial.eval (Function.update v j 0) P +
        y * (MvPolynomial.eval (Function.update v j 1) P -
          MvPolynomial.eval (Function.update v j 0) P) := by
  simp only [MvPolynomial.eval_eq', prod_pow_update]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hαj : α j ≤ 1 := (MvPolynomial.monomial_le_degreeOf j hα).trans hP
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hαj with h | h
  · rw [h]; simp
  · rw [h]; simp; ring

theorem degreeOf_dualPoly_le_one {P : MvPolynomial ι ℂ} {j : ι} (hj : P.degreeOf j = 1) :
    (dualPoly P).degreeOf j ≤ 1 := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  have hsub := MvPolynomial.support_sum (s := P.support)
    (f := fun α => MvPolynomial.monomial (degVec P - α) ((starRingEnd ℂ) (MvPolynomial.coeff α P)))
  rw [dualPoly] at hm
  obtain ⟨α, -, hα⟩ := Finset.mem_biUnion.mp (hsub hm)
  have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hα)
  rw [hm', Finsupp.tsub_apply, degVec_apply, hj]
  exact Nat.sub_le 1 _

omit [Fintype ι] [DecidableEq ι] in
theorem differentiable_eval_comp {v : ℂ → ι → ℂ} (hv : ∀ k, Differentiable ℂ fun t => v t k)
    (P : MvPolynomial ι ℂ) : Differentiable ℂ fun t => MvPolynomial.eval (v t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.fun_mul (hv i)

namespace LeeYangDatum

variable (L : LeeYangDatum ι)

/-- The field vector `u(t)`. -/
def fieldVec (t : ℂ) : ι → ℂ := fun k => L.field k t

/-- The constant part `A(t) = P(u(t)) |_{u_j = 0}`. -/
def splitA (j : ι) (t : ℂ) : ℂ := MvPolynomial.eval (Function.update (L.fieldVec t) j 0) L.P

/-- The linear coefficient `B(t)` of `u_j`. -/
def splitB (j : ι) (t : ℂ) : ℂ :=
  MvPolynomial.eval (Function.update (L.fieldVec t) j 1) L.P - L.splitA j t

theorem eval_update_fieldVec (j : ι) (hj : L.P.degreeOf j ≤ 1) (t y : ℂ) :
    MvPolynomial.eval (Function.update (L.fieldVec t) j y) L.P = L.splitA j t + y * L.splitB j t :=
  eval_update_affine L.P j hj _ y

theorem restr_eq_split (j : ι) (hj : L.P.degreeOf j ≤ 1) (t : ℂ) :
    L.restr t = L.splitA j t + L.splitB j t * L.field j t := by
  have h := L.eval_update_fieldVec j hj t (L.field j t)
  have hself : Function.update (L.fieldVec t) j (L.field j t) = L.fieldVec t :=
    Function.update_eq_self j (L.fieldVec t)
  rw [hself] at h
  rw [restr, mul_comm]
  exact h

theorem differentiable_fieldVec_update (j : ι) (y : ℂ) (k : ι) :
    Differentiable ℂ fun t => Function.update (L.fieldVec t) j y k := by
  by_cases hk : k = j
  · subst hk; simp
  · simp only [Function.update_of_ne hk, fieldVec, field]
    fun_prop

theorem differentiable_splitA (j : ι) : Differentiable ℂ (L.splitA j) :=
  differentiable_eval_comp (L.differentiable_fieldVec_update j 0) L.P

theorem differentiable_splitB (j : ι) : Differentiable ℂ (L.splitB j) :=
  (differentiable_eval_comp (L.differentiable_fieldVec_update j 1) L.P).sub
    (L.differentiable_splitA j)

omit [DecidableEq ι] in
theorem norm_field_lt_one {k : ι} {z : ℂ} (hz : z.im < 0) : ‖L.field k z‖ < 1 := by
  rw [L.norm_field, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (mul_neg_of_pos_of_neg (L.freq_pos k) hz)

omit [DecidableEq ι] in
theorem one_lt_norm_field {k : ι} {z : ℂ} (hz : 0 < z.im) : 1 < ‖L.field k z‖ := by
  rw [L.norm_field, Real.one_lt_exp_iff]
  exact mul_pos (L.freq_pos k) hz

theorem update_mem_disk {z : ℂ} (hz : z.im < 0) (j : ι) {y : ℂ} (hy : ‖y‖ < 1) (k : ι) :
    ‖Function.update (L.fieldVec z) j y k‖ < 1 := by
  by_cases hk : k = j
  · subst hk; simpa using hy
  · rw [Function.update_of_ne hk]; exact L.norm_field_lt_one hz

/-- **Below the axis.** `A ≠ 0` and `|B| ≤ |A|`. -/
theorem splitA_ne_zero_and_norm_splitB_le (j : ι) (hj : L.P.degreeOf j ≤ 1) {z : ℂ}
    (hz : z.im < 0) : L.splitA j z ≠ 0 ∧ ‖L.splitB j z‖ ≤ ‖L.splitA j z‖ := by
  have hA : L.splitA j z ≠ 0 :=
    L.disk _ (L.update_mem_disk hz j (by simp))
  refine ⟨hA, ?_⟩
  by_contra hlt
  push Not at hlt
  have hB : L.splitB j z ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.mpr (norm_nonneg _))
  set y := -(L.splitA j z / L.splitB j z) with hy
  have hynorm : ‖y‖ < 1 := by
    rw [hy, norm_neg, norm_div, div_lt_one (norm_pos_iff.mpr hB)]
    exact hlt
  apply L.disk _ (L.update_mem_disk hz j hynorm)
  rw [L.eval_update_fieldVec j hj, hy]
  field_simp
  ring

/-! ## Above the axis, through the reflected polynomial -/

omit [DecidableEq ι] in
theorem fieldVec_ne_zero (t : ℂ) (k : ι) : L.fieldVec t k ≠ 0 := L.field_ne_zero k t

/-- The reflection identity on the line through `u_j`: for `y ≠ 0`,
`P(…, y, …) = y U · conj P^♯(…, (conj y)⁻¹, …)` with `w = (conj u)⁻¹`. -/
theorem eval_update_reflect (j : ι) (hj : L.P.degreeOf j = 1) (t : ℂ) {y : ℂ} (hy : y ≠ 0) :
    MvPolynomial.eval (Function.update (L.fieldVec t) j y) L.P =
      y * (∏ k ∈ univ \ {j}, L.fieldVec t k ^ L.P.degreeOf k) *
        (starRingEnd ℂ) (MvPolynomial.eval
          (Function.update (fun k => ((starRingEnd ℂ) (L.fieldVec t k))⁻¹) j ((starRingEnd ℂ) y)⁻¹)
          (dualPoly L.P)) := by
  have hnz : ∀ k, Function.update (L.fieldVec t) j y k ≠ 0 := fun k => by
    by_cases hk : k = j
    · subst hk; simpa using hy
    · rw [Function.update_of_ne hk]; exact L.fieldVec_ne_zero t k
  rw [eval_eq_prod_mul_conj_dual L.P hnz]
  have hpt : (fun k => ((starRingEnd ℂ) (Function.update (L.fieldVec t) j y k))⁻¹) =
      Function.update (fun k => ((starRingEnd ℂ) (L.fieldVec t k))⁻¹) j ((starRingEnd ℂ) y)⁻¹ := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [hpt]
  have hprod := prod_pow_update (degVec L.P) (L.fieldVec t) j y
  simp only [degVec_apply, hj, pow_one] at hprod
  rw [hprod]

/-- **Above the axis.** `|A| ≤ |B|`. -/
theorem norm_splitA_le_norm_splitB (j : ι) (hj : L.P.degreeOf j = 1) {z : ℂ} (hz : 0 < z.im) :
    ‖L.splitA j z‖ ≤ ‖L.splitB j z‖ := by
  set w : ι → ℂ := fun k => ((starRingEnd ℂ) (L.fieldVec z k))⁻¹ with hw
  have hwin : ∀ k, ‖w k‖ < 1 := fun k => by
    rw [hw]
    simp only [norm_inv, Complex.norm_conj]
    exact inv_lt_one_of_one_lt₀ (L.one_lt_norm_field hz)
  have hdin : ∀ {r : ℂ}, ‖r‖ < 1 → ∀ k, ‖Function.update w j r k‖ < 1 := fun hr k => by
    by_cases hk : k = j
    · subst hk; simpa using hr
    · rw [Function.update_of_ne hk]; exact hwin k
  set U := ∏ k ∈ univ \ {j}, L.fieldVec z k ^ L.P.degreeOf k with hU
  have hU0 : U ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (L.fieldVec_ne_zero z k)
  have hdual1 : (dualPoly L.P).degreeOf j ≤ 1 := degreeOf_dualPoly_le_one hj
  set Q0 := MvPolynomial.eval (Function.update w j 0) (dualPoly L.P)
  set Q1 := MvPolynomial.eval (Function.update w j 1) (dualPoly L.P)
  have hQaff : ∀ r : ℂ, MvPolynomial.eval (Function.update w j r) (dualPoly L.P) =
      Q0 + r * (Q1 - Q0) := fun r => eval_update_affine (dualPoly L.P) j hdual1 w r
  -- `A + yB = yU conj Q0 + U conj (Q1 − Q0)` for `y ≠ 0`
  have hline : ∀ y : ℂ, y ≠ 0 → L.splitA j z + y * L.splitB j z =
      y * U * (starRingEnd ℂ) Q0 + U * (starRingEnd ℂ) (Q1 - Q0) := by
    intro y hy
    rw [← L.eval_update_fieldVec j hj.le z y, L.eval_update_reflect j hj z hy, hQaff, ← hU]
    rw [map_add, map_mul, map_inv₀, Complex.conj_conj]
    field_simp
  have hB : L.splitB j z = U * (starRingEnd ℂ) Q0 := by
    have h1 := hline 1 one_ne_zero
    have h2 := hline 2 two_ne_zero
    linear_combination h2 - h1
  have hQ0 : Q0 ≠ 0 := L.dualDisk _ (hdin (by simp))
  have hB0 : L.splitB j z ≠ 0 := by
    rw [hB]; exact mul_ne_zero hU0 ((map_ne_zero _).mpr hQ0)
  by_contra hlt
  push Not at hlt
  set y := -(L.splitA j z / L.splitB j z) with hy
  have hynorm : 1 < ‖y‖ := by
    rw [hy, norm_neg, norm_div, one_lt_div (norm_pos_iff.mpr hB0)]
    exact hlt
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hynorm; linarith
  have hroot : MvPolynomial.eval (Function.update (L.fieldVec z) j y) L.P = 0 := by
    rw [L.eval_update_fieldVec j hj.le, hy]
    field_simp
    ring
  rw [L.eval_update_reflect j hj z hy0] at hroot
  have hin : ‖((starRingEnd ℂ) y)⁻¹‖ < 1 := by
    rw [norm_inv, Complex.norm_conj]; exact inv_lt_one_of_one_lt₀ hynorm
  have hP := L.dualDisk _ (hdin hin)
  exact mul_ne_zero (mul_ne_zero hy0 hU0) ((map_ne_zero _).mpr hP) hroot

/-- **On the axis.** `|B(t)| = |A(t)|`. -/
theorem norm_splitB_eq_norm_splitA (j : ι) (hj : L.P.degreeOf j = 1) (t : ℝ) :
    ‖L.splitB j t‖ = ‖L.splitA j t‖ := by
  have hcA := (L.differentiable_splitA j).continuous
  have hcB := (L.differentiable_splitB j).continuous
  have hpath : ∀ σ : ℝ, Tendsto (fun s : ℝ => (t : ℂ) + (σ * s : ℝ) * I) (𝓝[>] 0) (𝓝 (t : ℂ)) := by
    intro σ
    have h : Continuous fun s : ℝ => (t : ℂ) + (σ * s : ℝ) * I := by fun_prop
    have h0 := h.tendsto 0
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hlimA : ∀ σ : ℝ, Tendsto (fun s : ℝ => ‖L.splitA j ((t : ℂ) + (σ * s : ℝ) * I)‖)
      (𝓝[>] 0) (𝓝 ‖L.splitA j t‖) := fun σ =>
    (continuous_norm.tendsto _).comp ((hcA.tendsto _).comp (hpath σ))
  have hlimB : ∀ σ : ℝ, Tendsto (fun s : ℝ => ‖L.splitB j ((t : ℂ) + (σ * s : ℝ) * I)‖)
      (𝓝[>] 0) (𝓝 ‖L.splitB j t‖) := fun σ =>
    (continuous_norm.tendsto _).comp ((hcB.tendsto _).comp (hpath σ))
  apply le_antisymm
  · refine le_of_tendsto_of_tendsto (hlimB (-1)) (hlimA (-1)) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have him : ((t : ℂ) + ((-1) * s : ℝ) * I).im < 0 := by
      simp; linarith [show (0 : ℝ) < s from hs]
    exact (L.splitA_ne_zero_and_norm_splitB_le j hj.le him).2
  · refine le_of_tendsto_of_tendsto (hlimA 1) (hlimB 1) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have him : 0 < ((t : ℂ) + ((1 : ℝ) * s : ℝ) * I).im := by
      simp; exact hs
    exact L.norm_splitA_le_norm_splitB j hj him

/-- **First-zero law for Lee–Yang data.**  A field `u_j` in which `P` is affine forces a real
zero of the restriction within `π/λ_j`. -/
theorem exists_restr_eq_zero (j : ι) (hj : L.P.degreeOf j = 1) :
    ∃ t ∈ Icc (-(Real.pi / L.freq j)) (Real.pi / L.freq j), L.restr (t : ℂ) = 0 := by
  obtain ⟨t, ht, h⟩ := RHTower.LeeYangFirstZero.exists_zero_of_innerSplit (L.freq_pos j)
    (L.differentiable_splitA j) (L.differentiable_splitB j)
    (fun z hz => L.splitA_ne_zero_and_norm_splitB_le j hj.le hz)
    (fun t => L.norm_splitB_eq_norm_splitA j hj t)
  refine ⟨t, ht, ?_⟩
  rw [L.restr_eq_split j hj.le]
  exact h

/-- **Zero-gap law for Lee–Yang data.**  Every window `[t₀ − π/λ_j, t₀ + π/λ_j]` contains a real
zero of the restriction: consecutive real zeros are at most `2π/λ_j` apart. -/
theorem exists_restr_eq_zero_near (j : ι) (hj : L.P.degreeOf j = 1) (t₀ : ℝ) :
    ∃ t ∈ Icc (t₀ - Real.pi / L.freq j) (t₀ + Real.pi / L.freq j), L.restr (t : ℂ) = 0 := by
  obtain ⟨t, ht, h⟩ := RHTower.LeeYangFirstZero.exists_zero_of_innerSplit_near (L.freq_pos j)
    (L.differentiable_splitA j) (L.differentiable_splitB j)
    (fun z hz => L.splitA_ne_zero_and_norm_splitB_le j hj.le hz)
    (fun t => L.norm_splitB_eq_norm_splitA j hj t) t₀
  refine ⟨t, ht, ?_⟩
  rw [L.restr_eq_split j hj.le]
  exact h

end LeeYangDatum

/-! ## No integer-anchored Lee–Yang producer of `Ξ` -/

theorem sq_le_thirtyTwo_of_abs_le_pi_div_log_two {t : ℝ} (ht : |t| ≤ Real.pi / Real.log 2) :
    t ^ 2 ≤ 32 := by
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log 2 := by linarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have h1 : |t| * Real.log 2 ≤ Real.pi := (le_div_iff₀ hlogpos).mp ht
  have h2 : |t| < 5 := by nlinarith [abs_nonneg t]
  have h3 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  nlinarith [abs_nonneg t]

theorem XiC_ne_zero_of_abs_le_pi_div_log_two {t : ℝ} (ht : |t| ≤ Real.pi / Real.log 2) :
    XiC (t : ℂ) ≠ 0 := by
  show xi ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0
  apply xi_ne_zero_of_im_sq_le
  simpa using sq_le_thirtyTwo_of_abs_le_pi_div_log_two ht

theorem continuous_XiC_ofReal' : Continuous fun t : ℝ => XiC (t : ℂ) :=
  continuous_iff_continuousAt.mpr fun x =>
    (XiC_analytic (x : ℂ) (Set.mem_univ _)).continuousAt.comp Complex.continuous_ofReal.continuousAt

/-- **Integer-anchored Lee–Yang producers of `Ξ` do not exist.**  Let `(L_i)` be Lee–Yang data,
each with a field `j_i` of frequency at least `log 2` in which `P_i` is affine.  For any
normalizers `e_i` and any continuous zero-free `E` on `[−π/log 2, π/log 2]`, the normalized
restrictions `e_i · f_i` do not converge to `E · Ξ` uniformly there. -/
theorem not_tendstoUniformlyOn_leeYang_XiC {κ : Type*} {l : Filter κ} [l.NeBot]
    {ι : κ → Type*} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (L : ∀ i, LeeYangDatum (ι i)) (j : ∀ i, ι i) (hj : ∀ i, (L i).P.degreeOf (j i) = 1)
    (hfreq : ∀ i, Real.log 2 ≤ (L i).freq (j i)) (e : κ → ℝ → ℂ) {E : ℝ → ℂ}
    (hE : ContinuousOn E (Icc (-(Real.pi / Real.log 2)) (Real.pi / Real.log 2)))
    (hE0 : ∀ t ∈ Icc (-(Real.pi / Real.log 2)) (Real.pi / Real.log 2), E t ≠ 0) :
    ¬ TendstoUniformlyOn (fun i t => e i t * (L i).restr (t : ℂ)) (fun t => E t * XiC (t : ℂ)) l
      (Icc (-(Real.pi / Real.log 2)) (Real.pi / Real.log 2)) := by
  intro hU
  have hlogpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set S := Icc (-(Real.pi / Real.log 2)) (Real.pi / Real.log 2) with hS
  have hT : 0 ≤ Real.pi / Real.log 2 := div_nonneg Real.pi_pos.le hlogpos.le
  have hne : S.Nonempty := ⟨0, by rw [hS]; constructor <;> linarith⟩
  have hXi : ∀ t ∈ S, XiC (t : ℂ) ≠ 0 := fun t ht =>
    XiC_ne_zero_of_abs_le_pi_div_log_two (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hcont : ContinuousOn (fun t => ‖E t * XiC (t : ℂ)‖) S :=
    (hE.mul continuous_XiC_ofReal'.continuousOn).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  have hm : 0 < ‖E t₀ * XiC (t₀ : ℂ)‖ := norm_pos_iff.mpr (mul_ne_zero (hE0 t₀ ht₀) (hXi t₀ ht₀))
  obtain ⟨i, hi⟩ := (Metric.tendstoUniformlyOn_iff.mp hU _ hm).exists
  obtain ⟨t, ht, hz⟩ := (L i).exists_restr_eq_zero (j i) (hj i)
  have hsub : Real.pi / (L i).freq (j i) ≤ Real.pi / Real.log 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le hlogpos (hfreq i)
  have htS : t ∈ S := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlt := hi t htS
  simp only [hz, mul_zero, dist_zero_right] at hlt
  exact absurd (isMinOn_iff.mp hmin t htS) (not_le.mpr hlt)

end

end RHTower.LeeYangCount
