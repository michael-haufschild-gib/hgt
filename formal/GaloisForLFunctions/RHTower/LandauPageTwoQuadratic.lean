import GaloisForLFunctions.RHTower.QuadraticCharacterFourfoldProduct
import GaloisForLFunctions.RHTower.ChenGuptaLiPoleAvoidingConductorStrip
import GaloisForLFunctions.RHTower.ZetaThreeFourOne
import Mathlib.Analysis.Complex.Liouville

/-!
# Landau–Page for two quadratic characters: the pole pays for at most one nearby real zero

Let `χ₁ ≠ χ₂` be primitive quadratic characters modulo `N` with real zeros `β₁, β₂ ≤ 1`.  Put
`δ = max(1−β₁, 1−β₂)` and `σ = 1 + δ`.  The fourfold product

`F(σ) = L(σ,1_N) L(σ,χ₁) L(σ,χ₂) L(σ,χ₁χ₂)`

is at least `(2 − π²/6)³` by the nonnegativity of its logarithmic derivative, while each factor is
bounded above: the trivial factor by the pole `1/δ + 2`, the two character factors by `2δ·M_N`
through the mean value theorem and a Cauchy estimate on the conductor-uniform strip bound, and the
product factor by `3N` through summation by parts.  Comparing the two bounds forces

`δ ≥ (2 − π²/6)³ / (18 · M_N² · N)`,

with `M_N = 1728 · C · N²` explicit.  So at most one of the two characters has a real zero within
that distance of `1`: the single unit of pole share is spent by the first zero.  This is the
integer-valued conclusion of the share ledger at the pole, the only place where the ratio of a
zero's share to the pole's share tends to one.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- The conductor-uniform derivative bound `M_N = 1728 · C · N²` on `[3/4, 5/4]`. -/
def landauPageDerivativeBound (N : ℕ) : ℝ :=
  1728 * cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ)

/-- The Landau–Page width `(2 − π²/6)³ / (18 · M_N² · N)`. -/
def landauPageWidth (N : ℕ) : ℝ :=
  (2 - Real.pi ^ 2 / 6) ^ 3 / (18 * landauPageDerivativeBound N ^ 2 * N)

theorem one_le_cglDirichletLRightEdgeConstant : 1 ≤ cglDirichletLRightEdgeConstant := by
  unfold cglDirichletLRightEdgeConstant
  have : 0 ≤ ∑' n : ℕ, (((n : ℝ)) ^ (2 : ℝ))⁻¹ := tsum_nonneg fun n => by positivity
  linarith

theorem landauPageDerivativeBound_ge {N : ℕ} [NeZero N] : 1728 ≤ landauPageDerivativeBound N := by
  unfold landauPageDerivativeBound
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hC := one_le_cglDirichletLRightEdgeConstant
  have hprod : (1 : ℝ) * 1 ≤ cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ) :=
    mul_le_mul hC hN2 (by norm_num) (by linarith)
  nlinarith

theorem landauPageDerivativeBound_pos {N : ℕ} [NeZero N] : 0 < landauPageDerivativeBound N :=
  lt_of_lt_of_le (by norm_num) landauPageDerivativeBound_ge

theorem landauPageWidth_pos {N : ℕ} [NeZero N] : 0 < landauPageWidth N := by
  unfold landauPageWidth
  have := landauPageDerivativeBound_pos (N := N)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hc := two_sub_pi_sq_div_six_pos
  positivity

theorem two_sub_pi_sq_div_six_le_one : 2 - Real.pi ^ 2 / 6 ≤ 1 := by
  have := Real.pi_gt_three
  nlinarith

theorem landauPageWidth_le_quarter {N : ℕ} [NeZero N] : landauPageWidth N ≤ 1 / 4 := by
  unfold landauPageWidth
  have hM := landauPageDerivativeBound_ge (N := N)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hc := two_sub_pi_sq_div_six_pos
  have hc1 := two_sub_pi_sq_div_six_le_one
  have hnum : (2 - Real.pi ^ 2 / 6) ^ 3 ≤ 1 := by
    have h0 : 0 ≤ 2 - Real.pi ^ 2 / 6 := hc.le
    calc (2 - Real.pi ^ 2 / 6) ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ h0 hc1 3
      _ = 1 := by norm_num
  have hden : 4 ≤ 18 * landauPageDerivativeBound N ^ 2 * N := by nlinarith
  rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith

/-! ## The Cauchy estimate on the conductor-uniform strip -/

/-- The strip bound `‖L(z,χ)‖ ≤ 4·C·N²·‖z − 4‖³` specialised to `‖z − 4‖ ≤ 6`. -/
theorem norm_LFunction_le_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (hprim : χ.IsPrimitive) {z : ℂ} (hzl : (-3 / 2 : ℝ) ≤ z.re) (hzr : z.re ≤ 2)
    (hz4 : ‖z - 4‖ ≤ 6) :
    ‖DirichletCharacter.LFunction χ z‖ ≤ 864 * cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ) := by
  let P : CGLLemma62PrimitiveCharacter := ⟨⟨N, NeZero.pos N⟩, χ, hne, hprim⟩
  have h := norm_primitiveLFunction_conductorUniform_strip_le P z hzl hzr
  have hC := one_le_cglDirichletLRightEdgeConstant
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by positivity
  have h6 : ‖z - 4‖ ^ 3 ≤ 216 := by
    calc ‖z - 4‖ ^ 3 ≤ 6 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hz4 3
      _ = 216 := by norm_num
  calc ‖DirichletCharacter.LFunction χ z‖
      ≤ (4 * cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ)) * ‖z - 4‖ ^ 3 := h
    _ ≤ (4 * cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ)) * 216 := by
        apply mul_le_mul_of_nonneg_left h6
        positivity
    _ = 864 * cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ) := by ring

/-- Cauchy estimate: on the real segment `[3/4, 5/4]` the derivative is bounded by `M_N`. -/
theorem norm_deriv_LFunction_le_of_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (hprim : χ.IsPrimitive) {x : ℝ} (hx1 : 3 / 4 ≤ x) (hx2 : x ≤ 5 / 4) :
    ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤ landauPageDerivativeBound N := by
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hne
  have hdc : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (ball (x : ℂ) (1 / 2)) :=
    hdiff.diffContOnCl
  have hK : ∀ z ∈ sphere (x : ℂ) (1 / 2), ‖DirichletCharacter.LFunction χ z‖
      ≤ 864 * cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre : |(z - (x : ℂ)).re| ≤ 1 / 2 := by
      rw [← hz]
      exact Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have hre' := abs_le.mp hre
    refine norm_LFunction_le_of_primitive hne hprim (by linarith [hre'.1]) (by linarith [hre'.2]) ?_
    calc ‖z - 4‖ = ‖(z - (x : ℂ)) + ((x : ℂ) - 4)‖ := by ring_nf
      _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ) - 4‖ := norm_add_le _ _
      _ = 1 / 2 + |x - 4| := by
          rw [hz]
          congr 1
          rw [show ((x : ℂ) - 4) = ((x - 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_eq_abs]
      _ ≤ 6 := by
          rw [abs_of_nonpos (by linarith)]
          linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 2) hdc hK
  calc ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖
      ≤ 864 * cglDirichletLRightEdgeConstant * (N : ℝ) ^ (2 : ℝ) / (1 / 2) := h
    _ = landauPageDerivativeBound N := by
        unfold landauPageDerivativeBound
        ring

/-- Mean value theorem from a real zero: `‖L(σ,χ)‖ ≤ M_N (σ − β)` for `3/4 ≤ β ≤ σ ≤ 5/4`. -/
theorem norm_LFunction_le_of_real_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (hprim : χ.IsPrimitive) {β σ : ℝ} (hβ : 3 / 4 ≤ β) (hβσ : β ≤ σ)
    (hσ : σ ≤ 5 / 4) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ ≤ landauPageDerivativeBound N * (σ - β) := by
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hne
  set g : ℝ → ℂ := fun t => DirichletCharacter.LFunction χ (t : ℂ) with hg
  have hgderiv : ∀ t : ℝ, HasDerivAt g (deriv (DirichletCharacter.LFunction χ) (t : ℂ)) t :=
    fun t => (hdiff (t : ℂ)).hasDerivAt.comp_ofReal
  have hdiffOn : ∀ t ∈ Set.Icc β σ, DifferentiableAt ℝ g t :=
    fun t _ => (hgderiv t).differentiableAt
  have hbound : ∀ t ∈ Set.Icc β σ, ‖deriv g t‖ ≤ landauPageDerivativeBound N := by
    intro t ht
    rw [(hgderiv t).deriv]
    exact norm_deriv_LFunction_le_of_primitive hne hprim (by linarith [ht.1]) (by linarith [ht.2])
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiffOn hbound (convex_Icc β σ)
    (Set.left_mem_Icc.mpr hβσ) (Set.right_mem_Icc.mpr hβσ)
  have hgβ : g β = 0 := hzero
  rw [hgβ, sub_zero] at h
  calc ‖DirichletCharacter.LFunction χ (σ : ℂ)‖ = ‖g σ‖ := rfl
    _ ≤ landauPageDerivativeBound N * ‖σ - β‖ := h
    _ = landauPageDerivativeBound N * (σ - β) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-! ## The pole factor -/

/-- The trivial character factor is bounded by the pole: `‖L(1+δ, 1_N)‖ ≤ 1/δ + 2`. -/
theorem norm_LFunction_one_le_pole {N : ℕ} [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ((1 + δ : ℝ) : ℂ)‖ ≤ 1 / δ + 2 := by
  have hne1 : ((1 + δ : ℝ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hrw : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ((1 + δ : ℝ) : ℂ)
      = DirichletCharacter.LFunctionTrivChar N ((1 + δ : ℝ) : ℂ) := rfl
  rw [hrw, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne1, norm_mul]
  have hprod : ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-((1 + δ : ℝ) : ℂ)))‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun p _ => norm_nonneg _) (fun p hp => ?_)
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    have hcpow : (p : ℂ) ^ (-((1 + δ : ℝ) : ℂ)) = (((p : ℝ) ^ (-(1 + δ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp0.le]
      push_cast
      rfl
    rw [hcpow]
    have hr0 : 0 ≤ (p : ℝ) ^ (-(1 + δ)) := Real.rpow_nonneg hp0.le _
    have hr1 : (p : ℝ) ^ (-(1 + δ)) ≤ 1 := by
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
      exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    rw [show (1 : ℂ) - (((p : ℝ) ^ (-(1 + δ)) : ℝ) : ℂ) = ((1 - (p : ℝ) ^ (-(1 + δ)) : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have hzeta : ‖riemannZeta ((1 + δ : ℝ) : ℂ)‖ ≤ 1 / δ + 2 := by
    have h := abs_riemannZeta_one_add_le hδ
    have hcast : ((1 + δ : ℝ) : ℂ) = (1 : ℂ) + (δ : ℂ) := by push_cast; ring
    rw [hcast]
    exact h
  calc ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-((1 + δ : ℝ) : ℂ)))‖
        * ‖riemannZeta ((1 + δ : ℝ) : ℂ)‖
      ≤ 1 * (1 / δ + 2) := by
        apply mul_le_mul hprod hzeta (norm_nonneg _) (by norm_num)
    _ = 1 / δ + 2 := one_mul _

/-! ## The theorem -/

/-- A real zero of `L(·,χ)` for nontrivial `χ` lies strictly left of `1`. -/
theorem lt_one_of_LFunction_real_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {β : ℝ} (hβ : β ≤ 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    β < 1 := by
  rcases lt_or_eq_of_le hβ with h | h
  · exact h
  · exfalso
    subst h
    have := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (s := (1 : ℂ))
      (by norm_num)
    exact this (by simpa using hzero)

/-- **Landau–Page for two quadratic characters.**  If two distinct primitive quadratic characters
modulo `N` have real zeros `β₁, β₂ ≤ 1`, then at least one of them is at distance at least
`landauPageWidth N` from `1`. -/
theorem landau_page_two_quadratic {N : ℕ} [NeZero N] {χ₁ χ₂ : DirichletCharacter ℂ N}
    (h₁ : χ₁.IsQuadratic) (h₂ : χ₂.IsQuadratic) (h₁ne : χ₁ ≠ 1) (h₂ne : χ₂ ≠ 1)
    (h₁p : χ₁.IsPrimitive) (h₂p : χ₂.IsPrimitive) (hne : χ₁ ≠ χ₂)
    {β₁ β₂ : ℝ} (hb₁ : β₁ ≤ 1) (hb₂ : β₂ ≤ 1)
    (hz₁ : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0)
    (hz₂ : DirichletCharacter.LFunction χ₂ (β₂ : ℂ) = 0) :
    landauPageWidth N ≤ max (1 - β₁) (1 - β₂) := by
  by_contra hcon
  have hcon' : max (1 - β₁) (1 - β₂) < landauPageWidth N := not_le.mp hcon
  set δ : ℝ := max (1 - β₁) (1 - β₂) with hδ
  have hβ₁ : β₁ < 1 := lt_one_of_LFunction_real_zero h₁ne hb₁ hz₁
  have hβ₂ : β₂ < 1 := lt_one_of_LFunction_real_zero h₂ne hb₂ hz₂
  have hδpos : 0 < δ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hδq : δ ≤ 1 / 4 := le_trans hcon'.le landauPageWidth_le_quarter
  have hδ₁ : 1 - β₁ ≤ δ := le_max_left _ _
  have hδ₂ : 1 - β₂ ≤ δ := le_max_right _ _
  set σ : ℝ := 1 + δ with hσ
  have hσ1 : 1 < σ := by rw [hσ]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσ]; linarith
  -- the product character is nontrivial
  have hprod_ne : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply hne
    have hinv : χ₂⁻¹ = χ₂ := h₂.inv
    calc χ₁ = χ₁ * χ₂ * χ₂⁻¹ := by rw [mul_inv_cancel_right]
      _ = χ₂ := by rw [h, one_mul, hinv]
  -- lower bound
  have hlow := fourfoldRe_ge h₁ h₂ hσ1 hσ2
  -- upper bounds on the four factors
  have hM := landauPageDerivativeBound_pos (N := N)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hA : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) (σ : ℂ)‖ ≤ 1 / δ + 2 := by
    rw [hσ]
    exact norm_LFunction_one_le_pole hδpos
  have hB : ‖DirichletCharacter.LFunction χ₁ (σ : ℂ)‖ ≤ landauPageDerivativeBound N * (2 * δ) := by
    have h := norm_LFunction_le_of_real_zero h₁ne h₁p (β := β₁) (σ := σ) (by linarith)
      (by linarith) (by linarith) hz₁
    calc ‖DirichletCharacter.LFunction χ₁ (σ : ℂ)‖ ≤ landauPageDerivativeBound N * (σ - β₁) := h
      _ ≤ landauPageDerivativeBound N * (2 * δ) := by
          apply mul_le_mul_of_nonneg_left _ hM.le
          rw [hσ]
          linarith
  have hC : ‖DirichletCharacter.LFunction χ₂ (σ : ℂ)‖ ≤ landauPageDerivativeBound N * (2 * δ) := by
    have h := norm_LFunction_le_of_real_zero h₂ne h₂p (β := β₂) (σ := σ) (by linarith)
      (by linarith) (by linarith) hz₂
    calc ‖DirichletCharacter.LFunction χ₂ (σ : ℂ)‖ ≤ landauPageDerivativeBound N * (σ - β₂) := h
      _ ≤ landauPageDerivativeBound N * (2 * δ) := by
          apply mul_le_mul_of_nonneg_left _ hM.le
          rw [hσ]
          linarith
  have hD : ‖DirichletCharacter.LFunction (χ₁ * χ₂) (σ : ℂ)‖ ≤ 3 * N :=
    norm_LFunction_le_three_mul_modulus (χ₁ * χ₂) hprod_ne hσ1
  -- the real value is at most the norm of the product
  have hre : fourfoldRe χ₁ χ₂ σ ≤ ‖fourfoldProduct χ₁ χ₂ (σ : ℂ)‖ := Complex.re_le_norm _
  have hnorm : ‖fourfoldProduct χ₁ χ₂ (σ : ℂ)‖
      = ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) (σ : ℂ)‖
        * ‖DirichletCharacter.LFunction χ₁ (σ : ℂ)‖ * ‖DirichletCharacter.LFunction χ₂ (σ : ℂ)‖
        * ‖DirichletCharacter.LFunction (χ₁ * χ₂) (σ : ℂ)‖ := by
    unfold fourfoldProduct
    rw [norm_mul, norm_mul, norm_mul]
  have hup : ‖fourfoldProduct χ₁ χ₂ (σ : ℂ)‖
      ≤ (1 / δ + 2) * (landauPageDerivativeBound N * (2 * δ))
        * (landauPageDerivativeBound N * (2 * δ)) * (3 * N) := by
    rw [hnorm]
    have h0 : 0 ≤ (1 / δ + 2) := by positivity
    have h1 : 0 ≤ landauPageDerivativeBound N * (2 * δ) := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul hA hB (norm_nonneg _) h0) hC (norm_nonneg _)
      (mul_nonneg h0 h1)) hD (norm_nonneg _) (mul_nonneg (mul_nonneg h0 h1) h1)
  -- combine: `c₀ ≤ 12 δ M² N (1 + 2δ) ≤ 18 δ M² N`
  have hkey : (2 - Real.pi ^ 2 / 6) ^ 3 ≤ 18 * landauPageDerivativeBound N ^ 2 * N * δ := by
    have hchain := le_trans hlow (le_trans hre hup)
    have hexp : (1 / δ + 2) * (landauPageDerivativeBound N * (2 * δ))
        * (landauPageDerivativeBound N * (2 * δ)) * (3 * N)
        = 12 * landauPageDerivativeBound N ^ 2 * N * δ * (1 + 2 * δ) := by
      field_simp
      ring
    rw [hexp] at hchain
    have h2δ : 1 + 2 * δ ≤ 3 / 2 := by linarith
    have hpos : 0 ≤ 12 * landauPageDerivativeBound N ^ 2 * N * δ := by positivity
    calc (2 - Real.pi ^ 2 / 6) ^ 3
        ≤ 12 * landauPageDerivativeBound N ^ 2 * N * δ * (1 + 2 * δ) := hchain
      _ ≤ 12 * landauPageDerivativeBound N ^ 2 * N * δ * (3 / 2) :=
          mul_le_mul_of_nonneg_left h2δ hpos
      _ = 18 * landauPageDerivativeBound N ^ 2 * N * δ := by ring
  -- hence `δ ≥ landauPageWidth N`, contradicting `hcon`
  have hwidth : landauPageWidth N ≤ δ := by
    unfold landauPageWidth
    rw [div_le_iff₀ (by positivity)]
    linarith
  exact absurd hwidth (not_le.mpr hcon')

end

end RHTower
