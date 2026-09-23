import GaloisForLFunctions.RHTower.DirichletLRegularizedEdges
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# The analytic hypotheses of Phragmén–Lindelöf for the regularized L-function

Three inputs remain for `PhragmenLindelof.vertical_strip` applied to `f = L(·,χ)/(s-4)³` on
`-2 < Re s < 3`: differentiability on the strip with continuity on its closure, and the
double-exponential growth condition along `|Im s| → ∞`.

The growth condition is generous: the order-one envelope gives `exp (B (5+|t|)²)`, and a quadratic
is eventually dominated by `exp (|t|/3)`, whose rate `1/3` is below the required `π/5`.
-/

open Complex Filter
open scoped Topology

namespace RHTower

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- The cubic term of the exponential series dominates a shifted square. -/
theorem eventually_sq_le_exp {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∀ᶠ u : ℝ in atTop, (c + u) ^ (2 : ℕ) ≤ Real.exp (b * u) := by
  have hser : ∀ x : ℝ, 0 ≤ x → x ^ (3 : ℕ) / 6 ≤ Real.exp x := by
    intro x hx
    have h := Real.sum_le_exp_of_nonneg hx 4
    simp [Finset.sum_range_succ, Nat.factorial] at h
    nlinarith [h, hx, sq_nonneg x]
  filter_upwards [eventually_ge_atTop (max |c| (max (24 / b ^ (3 : ℕ)) 1))] with u hu
  have hc : |c| ≤ u := le_trans (le_max_left _ _) hu
  have hbig : 24 / b ^ (3 : ℕ) ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hu
  have hu0 : (0 : ℝ) < u := by linarith
  have hcle : c ≤ u := le_trans (le_abs_self c) hc
  have hcge : -u ≤ c := by linarith [neg_abs_le c]
  have h1 : (c + u) ^ (2 : ℕ) ≤ 4 * u ^ (2 : ℕ) := by nlinarith
  have hb3 : (0 : ℝ) < b ^ (3 : ℕ) := by positivity
  have hbu : 24 ≤ b ^ (3 : ℕ) * u := by
    rw [div_le_iff₀ hb3] at hbig
    linarith
  have h2 : 4 * u ^ (2 : ℕ) ≤ (b * u) ^ (3 : ℕ) / 6 := by nlinarith [hbu, hu0, sq_nonneg u]
  have h3 : (b * u) ^ (3 : ℕ) / 6 ≤ Real.exp (b * u) := hser (b * u) (by positivity)
  linarith

/-- Away from `4`, the regularized function is holomorphic. -/
theorem differentiableAt_regularized {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {z : ℂ}
    (hz : z.re ≤ 3) :
    DifferentiableAt ℂ (fun w : ℂ => DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ)) z := by
  have hne : z - 4 ≠ 0 := by
    intro h
    have hz4 : z = 4 := by linear_combination h
    rw [hz4] at hz
    norm_num at hz
  exact ((DirichletCharacter.differentiable_LFunction hχ) z).div
    (((differentiable_id.sub_const 4).pow 3) z) (pow_ne_zero 3 hne)

/-- **Differentiability on the strip and continuity on its closure.** -/
theorem diffContOnCl_regularized {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DiffContOnCl ℂ (fun w : ℂ => DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ))
      (Complex.re ⁻¹' Set.Ioo (-2 : ℝ) 3) := by
  have hclosure : closure (Complex.re ⁻¹' Set.Ioo (-2 : ℝ) 3)
      ⊆ Complex.re ⁻¹' Set.Icc (-2 : ℝ) 3 :=
    closure_minimal (fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
      (isClosed_Icc.preimage Complex.continuous_re)
  refine ⟨fun z hz => (differentiableAt_regularized hχ (le_of_lt hz.2)).differentiableWithinAt,
    fun z hz => ?_⟩
  exact (differentiableAt_regularized hχ (hclosure hz).2).continuousAt.continuousWithinAt

/-- **The Phragmén–Lindelöf growth condition.**  Along `|Im s| → ∞` inside the strip the
regularized function is dominated by `exp (B exp (|t|/3))`, and `1/3 < π/5`. -/
theorem isBigO_regularized {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ c < Real.pi / (3 - (-2 : ℝ)), ∃ B : ℝ,
      (fun w : ℂ => DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ))
        =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo (-2 : ℝ) 3)]
        fun w : ℂ => Real.exp (B * Real.exp (c * |w.im|)) := by
  obtain ⟨B₁, hB₁, hgrow⟩ := exists_growth_LFunction_strip hχ
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_sq_le_exp (b := (1 : ℝ) / 3) (by norm_num) (5 : ℝ))
  refine ⟨1 / 3, ?_, B₁, ?_⟩
  · rw [show (3 : ℝ) - (-2) = 5 by norm_num, lt_div_iff₀ (by norm_num : (0 : ℝ) < 5)]
    linarith [Real.two_le_pi]
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    rw [Filter.eventually_inf_principal]
    have hmem : {w : ℂ | max T 2 ≤ |w.im|} ∈
        comap (_root_.abs ∘ Complex.im) (atTop : Filter ℝ) :=
      Filter.mem_comap.mpr ⟨Set.Ici (max T 2), Filter.Ici_mem_atTop _, fun w hw => hw⟩
    refine Filter.eventually_iff.mpr (Filter.mem_of_superset hmem ?_)
    intro w hw hstrip
    have hwT : T ≤ |w.im| := le_trans (le_max_left _ _) hw
    have hw2 : (2 : ℝ) ≤ |w.im| := le_trans (le_max_right _ _) hw
    have hre1 : (-2 : ℝ) ≤ w.re := le_of_lt hstrip.1
    have hre2 : w.re ≤ 3 := le_of_lt hstrip.2
    -- the divisor has modulus at least one
    have hd1 : (1 : ℝ) ≤ ‖w - 4‖ := by
      have h := Complex.abs_re_le_norm (w - 4)
      rw [Complex.sub_re] at h
      have : |w.re - 4| = 4 - w.re := by
        rw [abs_of_nonpos (by linarith)]; ring
      rw [show ((4 : ℂ)).re = 4 by norm_num, this] at h
      linarith
    have hdiv : ‖DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ)‖
        ≤ ‖DirichletCharacter.LFunction χ w‖ := by
      rw [norm_div, norm_pow]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [one_le_pow₀ hd1 (n := 3), norm_nonneg (DirichletCharacter.LFunction χ w)]
    -- the order-one envelope, expressed in `|Im w|`
    have hnormw : ‖w‖ ≤ 3 + |w.im| := by
      refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
      have : |w.re| ≤ 3 := abs_le.mpr ⟨by linarith, hre2⟩
      linarith
    have hlog : Real.log (2 + ‖w‖) ≤ 5 + |w.im| := by
      have hpos : (0 : ℝ) < 2 + ‖w‖ := by positivity
      have h := Real.log_le_sub_one_of_pos hpos
      linarith
    have hshape : B₁ * (1 + ‖w‖) * Real.log (2 + ‖w‖) ≤ B₁ * (5 + |w.im|) ^ (2 : ℕ) := by
      have hlognn : 0 ≤ Real.log (2 + ‖w‖) :=
        Real.log_nonneg (by linarith [norm_nonneg w])
      have h1 : (1 + ‖w‖) ≤ 5 + |w.im| := by linarith
      have s1 : (1 + ‖w‖) * Real.log (2 + ‖w‖) ≤ (5 + |w.im|) * Real.log (2 + ‖w‖) :=
        mul_le_mul_of_nonneg_right h1 hlognn
      have s2 : (5 + |w.im|) * Real.log (2 + ‖w‖) ≤ (5 + |w.im|) * (5 + |w.im|) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have hprod : (1 + ‖w‖) * Real.log (2 + ‖w‖) ≤ (5 + |w.im|) ^ (2 : ℕ) := by nlinarith [s1, s2]
      nlinarith [mul_le_mul_of_nonneg_left hprod hB₁.le]
    have hsq : (5 + |w.im|) ^ (2 : ℕ) ≤ Real.exp (1 / 3 * |w.im|) := by
      exact hT |w.im| hwT
    calc ‖DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ)‖
        ≤ ‖DirichletCharacter.LFunction χ w‖ := hdiv
      _ ≤ Real.exp (B₁ * (1 + ‖w‖) * Real.log (2 + ‖w‖)) := hgrow w hre1 hre2 hw2
      _ ≤ Real.exp (B₁ * (5 + |w.im|) ^ (2 : ℕ)) := Real.exp_le_exp.mpr hshape
      _ ≤ Real.exp (B₁ * Real.exp (1 / 3 * |w.im|)) := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsq hB₁.le)
      _ = 1 * ‖Real.exp (B₁ * Real.exp (1 / 3 * |w.im|))‖ := by
          rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **Polynomial growth of `L` across the strip.**  Phragmén–Lindelöf applied to the regularized
function: the bound valid on both edges propagates to the whole closed strip, and multiplying back
by `(s-4)³` gives a cubic bound for the L-function itself. -/
theorem bound_LFunction_strip {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, -2 ≤ z.re → z.re ≤ 3 →
      ‖DirichletCharacter.LFunction χ z‖ ≤ C * ‖z - 4‖ ^ (3 : ℕ) := by
  obtain ⟨C, hC, hr, hl⟩ := exists_bound_regularized_edges hχ hprim
  refine ⟨C, hC, fun z h1 h2 => ?_⟩
  have hPL := PhragmenLindelof.vertical_strip
    (f := fun w : ℂ => DirichletCharacter.LFunction χ w / (w - 4) ^ (3 : ℕ))
    (a := (-2 : ℝ)) (b := (3 : ℝ)) (C := C) (z := z)
    (diffContOnCl_regularized hχ) (isBigO_regularized hχ) hl hr h1 h2
  have hne : z - 4 ≠ 0 := by
    intro h
    have hz4 : z = 4 := by linear_combination h
    rw [hz4] at h2
    norm_num at h2
  have hpos : (0 : ℝ) < ‖z - 4‖ ^ (3 : ℕ) := by
    have : (0 : ℝ) < ‖z - 4‖ := norm_pos_iff.mpr hne
    positivity
  rw [norm_div, norm_pow, div_le_iff₀ hpos] at hPL
  exact hPL

end RHTower
