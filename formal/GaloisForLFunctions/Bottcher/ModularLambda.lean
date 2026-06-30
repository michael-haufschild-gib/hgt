/-
# The modular lambda function — the three-value Montel keystone (construction begun)

The sole remaining input to three-value Montel (via `normal_of_omitting_lift`) is the universal
covering `μ : ℍ → ℂ∖{0,1}` — the **modular lambda** `λ(τ) = (θ₂/θ₃)⁴`, Hauptmodul for `Γ(2)`. This file
begins its construction on mathlib's Jacobi theta functions.

Theta constants (nullwerte) from `jacobiTheta₂ z τ = ∑ exp(2πi n z + πi n² τ)`:
* `θ₃(τ) = jacobiTheta₂ 0 τ`              (`= ∑ exp(πi n² τ)`)
* `θ₄(τ) = jacobiTheta₂ (1/2) τ`          (`= ∑ (-1)ⁿ exp(πi n² τ)`)
* `θ₂(τ) = exp(πiτ/4)·jacobiTheta₂ (τ/2) τ` (`= ∑ exp(πi(n+½)²τ)`)
and `λ = (θ₂/θ₃)⁴`.

DONE here (axiom-clean): definitions; holomorphy of `θ₂, θ₃, θ₄` and of `λ` (off `θ₃ = 0`);
`θ₂, θ₃, θ₄ ≠ 0` and `λ` omits `0` on the fundamental domain `{im ≥ 4/5}`; the full `T` and `S`
transformation laws and the `SL(2,ℤ)`-modularity of the product `θ₂θ₃θ₄` (non-vanishing is `S`- and
`T`-invariant). REMAINING toward the covering: (a) connect the product modularity to
`exists_smul_mem_fd` (`SL(2,ℤ)` reduction to `𝒟 ⊆ {im ≥ √3/2}`) ⟹ `θ₃ ≠ 0` on all `ℍ`; (b) the
**Jacobi quartic identity** `θ₃⁴ = θ₂⁴ + θ₄⁴` (⟹ `1-λ = (θ₄/θ₃)⁴` ⟹ `λ` omits `1`); (c) the `Γ(2)`
fundamental-domain/Hauptmodul argument ⟹ `λ` is a covering `ℍ → ℂ∖{0,1}` ⟹ `normal_of_omitting_lift`.

New file (Montel/Julia lane — three-value Montel keystone). General; Mathlib only.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic

open Complex
open scoped Real

namespace Bottcher

/-- The theta constant `θ₃(τ) = ∑ exp(πi n² τ) = jacobiTheta₂ 0 τ` (the λ-denominator base). -/
noncomputable def thetaThree (τ : ℂ) : ℂ := jacobiTheta₂ 0 τ

/-- The theta constant `θ₄(τ) = ∑ (-1)ⁿ exp(πi n² τ) = jacobiTheta₂ (1/2) τ`. -/
noncomputable def thetaFour (τ : ℂ) : ℂ := jacobiTheta₂ (1/2) τ

/-- The theta constant `θ₂(τ) = ∑ exp(πi(n+1/2)²τ) = exp(πiτ/4)·jacobiTheta₂ (τ/2) τ` (λ-numerator base). -/
noncomputable def thetaTwo (τ : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- **The modular lambda function** `λ(τ) = (θ₂(τ)/θ₃(τ))⁴` — the Hauptmodul for `Γ(2)`, conjecturally
the universal covering `ℍ → ℂ∖{0,1}` whose covering property is the keystone of the three-value Montel
theorem (via `normal_of_omitting_lift`). -/
noncomputable def modularLambda (τ : ℂ) : ℂ := (thetaTwo τ / thetaThree τ) ^ 4

/-- `θ₃` is holomorphic on the upper half plane. -/
theorem differentiableAt_thetaThree {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ thetaThree τ :=
  differentiableAt_jacobiTheta₂_snd 0 hτ

/-- `θ₄` is holomorphic on the upper half plane. -/
theorem differentiableAt_thetaFour {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ thetaFour τ :=
  differentiableAt_jacobiTheta₂_snd (1/2) hτ

/-- `θ₂` is holomorphic on the upper half plane (uses the **joint** holomorphy of `jacobiTheta₂`
through `τ ↦ (τ/2, τ)`). -/
theorem differentiableAt_thetaTwo {τ : ℂ} (hτ : 0 < τ.im) : DifferentiableAt ℂ thetaTwo τ := by
  unfold thetaTwo
  have hg : DifferentiableAt ℂ (fun t : ℂ => (t / 2, t)) τ :=
    (differentiableAt_id.div_const 2).prodMk differentiableAt_id
  have hjoint : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (τ / 2, τ) :=
    (hasFDerivAt_jacobiTheta₂ (τ / 2) hτ).differentiableAt
  have hinner : DifferentiableAt ℂ (fun t => jacobiTheta₂ (t / 2) t) τ :=
    DifferentiableAt.comp (f := fun t : ℂ => (t / 2, t))
      (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) τ hjoint hg
  have hexp : DifferentiableAt ℂ (fun t : ℂ => Complex.exp ((Real.pi : ℂ) * I * t / 4)) τ := by
    fun_prop
  exact hexp.mul hinner

/-- **`λ` is holomorphic on `ℍ` wherever `θ₃ ≠ 0`** — the modular lambda is a holomorphic function
into `ℂ` there. (Non-vanishing of `θ₃` on all of `ℍ` is one of the remaining theta facts.) -/
theorem differentiableAt_modularLambda {τ : ℂ} (hτ : 0 < τ.im) (hne : thetaThree τ ≠ 0) :
    DifferentiableAt ℂ modularLambda τ := by
  unfold modularLambda
  exact ((differentiableAt_thetaTwo hτ).div (differentiableAt_thetaThree hτ) hne).pow 4

/-- **`θ₃ ≠ 0` for `im τ ≥ 4/5`.** From the explicit tail bound `‖θ₃ - 1‖ ≤ 2/(1-e^{-π·im τ})·e^{-π·im τ}`
(`norm_jacobiTheta_sub_one_le`): for `im τ ≥ 4/5` (using `π > 3`, `e^{12/5} > 3`) the bound is `< 1`, so
`θ₃` cannot be `0`. The threshold `4/5 < √3/2` **covers the theta-group fundamental domain**
`{|τ| ≥ 1, |re τ| ≤ 1} ⊆ {im ≥ √3/2}` — the precondition for transporting non-vanishing to all of `ℍ`
by the `S, T²` modular transformations (`jacobiTheta_S_smul`, `jacobiTheta_T_sq_smul`). -/
theorem thetaThree_ne_zero_of_im_ge {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) : thetaThree τ ≠ 0 := by
  have hτ0 : 0 < τ.im := by linarith
  have hb := norm_jacobiTheta_sub_one_le hτ0
  have hπ : (3 : ℝ) < π := Real.pi_gt_three
  set e := Real.exp (-π * τ.im) with he_def
  have he_pos : 0 < e := Real.exp_pos _
  have hle : -π * τ.im ≤ -(12 / 5) := by
    nlinarith [hπ, hτ, mul_nonneg (by linarith : (0:ℝ) ≤ π - 3) (by linarith : (0:ℝ) ≤ τ.im - 4/5)]
  have he3 : e < 1 / 3 := by
    rw [he_def]
    have hmono : Real.exp (-π * τ.im) ≤ Real.exp (-(12 / 5)) := Real.exp_le_exp.mpr hle
    have hk : (3 : ℝ) < Real.exp (12 / 5) := by
      have h2 : (3 : ℝ) ≤ Real.exp 2 := by nlinarith [Real.add_one_le_exp (2 : ℝ)]
      have h24 : Real.exp 2 < Real.exp (12 / 5) := Real.exp_lt_exp.mpr (by norm_num)
      linarith
    have hlt13 : Real.exp (-(12 / 5)) < 1 / 3 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
    linarith
  have h1e : 0 < 1 - e := by linarith
  have hRHS : 2 / (1 - e) * e < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h1e]; nlinarith [he3, he_pos]
  have hlt : ‖jacobiTheta τ - 1‖ < 1 := lt_of_le_of_lt hb hRHS
  have heq : thetaThree τ = jacobiTheta τ := by
    unfold thetaThree; exact (jacobiTheta_eq_jacobiTheta₂ τ).symm
  rw [heq]; intro h0; rw [h0] at hlt; simp at hlt

/-- **`λ` is holomorphic on `{im τ ≥ 4/5}`** unconditionally (holomorphy + `θ₃ ≠ 0` there). -/
theorem differentiableAt_modularLambda_of_im_ge {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    DifferentiableAt ℂ modularLambda τ :=
  differentiableAt_modularLambda (by linarith) (thetaThree_ne_zero_of_im_ge hτ)

/-- **`θ₄(τ) = θ₃(τ+1) = jacobiTheta(τ+1)`** — the `τ ↦ τ+1` shift swaps `θ₃ ↔ θ₄` (term-by-term,
since `cexp(πi n²) = cexp(πi n)` as `n² ≡ n mod 2`). -/
theorem thetaFour_eq (τ : ℂ) : thetaFour τ = jacobiTheta (τ + 1) := by
  unfold thetaFour
  rw [jacobiTheta_eq_jacobiTheta₂]
  unfold jacobiTheta₂
  refine tsum_congr (fun n => ?_)
  simp only [jacobiTheta₂_term]
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (n : ℤ) ^ 2 - n = 2 * k := by
    obtain ⟨m, hm⟩ := Int.even_mul_succ_self (n - 1)
    exact ⟨m, by linear_combination hm⟩
  have hcast : ((n : ℂ)) ^ 2 - (n : ℂ) = 2 * (k : ℂ) := by exact_mod_cast hk
  refine ⟨-k, ?_⟩
  push_cast
  linear_combination (-(↑Real.pi : ℂ) * I) * hcast

/-- **`θ₄ ≠ 0` for `im τ ≥ 4/5`** — via `θ₄(τ) = jacobiTheta(τ+1)` and the `θ₃` bound at `τ+1`
(`im (τ+1) = im τ`). So two of the three theta constants are non-vanishing on the fundamental domain. -/
theorem thetaFour_ne_zero_of_im_ge {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) : thetaFour τ ≠ 0 := by
  rw [thetaFour_eq]
  have him : (4 : ℝ) / 5 ≤ (τ + 1).im := by
    simp only [Complex.add_im, Complex.one_im, add_zero]; exact hτ
  have h := thetaThree_ne_zero_of_im_ge him
  rwa [show thetaThree (τ + 1) = jacobiTheta (τ + 1) from by
    unfold thetaThree; exact (jacobiTheta_eq_jacobiTheta₂ _).symm] at h

/-- **`θ₂ ≠ 0 ⟺ jacobiTheta₂(τ/2,τ) ≠ 0`** — the prefactor `exp(πiτ/4)` is never zero, so θ₂
non-vanishing reduces to that of the `(τ/2)`-theta. (Its leading `n = 0, -1` terms are both `1`, so
the series is `2 + tail`; the remaining work is the tail bound `‖tail‖ < 2` on the fundamental domain.) -/
theorem thetaTwo_ne_zero_iff (τ : ℂ) : thetaTwo τ ≠ 0 ↔ jacobiTheta₂ (τ / 2) τ ≠ 0 := by
  unfold thetaTwo
  rw [mul_ne_zero_iff, and_iff_right (Complex.exp_ne_zero _)]

/-- The `n = 0` term of `jacobiTheta₂(τ/2,τ)` is `1`. -/
theorem jacobiTheta₂_half_term_zero (τ : ℂ) : jacobiTheta₂_term 0 (τ / 2) τ = 1 := by
  simp [jacobiTheta₂_term]

/-- The `n = -1` term of `jacobiTheta₂(τ/2,τ)` is `1` (`(n²+n)|_{n=-1} = 0`). -/
theorem jacobiTheta₂_half_term_negone (τ : ℂ) : jacobiTheta₂_term (-1) (τ / 2) τ = 1 := by
  have h : jacobiTheta₂_term (-1) (τ / 2) τ = Complex.exp 0 := by
    unfold jacobiTheta₂_term; congr 1; push_cast; ring
  rw [h, Complex.exp_zero]

/-- **Norm of the `(τ/2)`-theta term**: `‖jacobiTheta₂_term n (τ/2) τ‖ = exp(-π(n²+n)·im τ)`.
Since `n²+n = n(n+1) ≥ |n|` for `n ∉ {0,-1}`, the tail `∑_{n∉{0,-1}}` is bounded by a geometric series
(`< 2` on the fundamental domain), giving `jacobiTheta₂(τ/2,τ) ≠ 0` and hence `θ₂ ≠ 0` — the last step
to the theta-constant trio. -/
theorem norm_jacobiTheta₂_half_term (τ : ℂ) (n : ℤ) :
    ‖jacobiTheta₂_term n (τ / 2) τ‖ = Real.exp (-Real.pi * ((n : ℝ) ^ 2 + n) * τ.im) := by
  rw [jacobiTheta₂_term, Complex.norm_exp]
  congr 1
  have h1 : (2 * ↑Real.pi * I * ↑n * (τ / 2) + ↑Real.pi * I * (↑n) ^ 2 * τ)
      = ((Real.pi * ((n : ℝ) ^ 2 + n) : ℝ) : ℂ) * (I * τ) := by push_cast; ring
  rw [h1, Complex.re_ofReal_mul, show (I * τ).re = -τ.im from by simp [Complex.mul_re]]
  ring_nf

/-- **`n² + n ≥ |n|` for `n ≠ -1`** — the exponent comparison collapsing the `(τ/2)`-theta tail
`∑ exp(-π(n²+n)·im τ)` (over `n ∉ {0,-1}`) into a geometric series `∑ exp(-π|n|·im τ)`, the last
analytic input to `θ₂ ≠ 0` on the fundamental domain. (Fails only at `n = -1`, where `n²+n = 0 < 1`.) -/
theorem sq_add_self_ge_abs (n : ℤ) (hn : n ≠ -1) : |(n : ℝ)| ≤ (n : ℝ) ^ 2 + n := by
  by_cases h : 0 ≤ n
  · rw [abs_of_nonneg (by exact_mod_cast h : (0 : ℝ) ≤ (n : ℝ))]; nlinarith [sq_nonneg (n : ℝ)]
  · have hn2 : n ≤ -2 := by omega
    have hr : (n : ℝ) ≤ -2 := by exact_mod_cast hn2
    rw [abs_of_neg (by exact_mod_cast (by omega : n < 0) : (n : ℝ) < 0)]; nlinarith [hr]

/-- **`θ₂ ≠ 0` for `im τ ≥ 4/5`.** `θ₂ ≠ 0 ⟺ jacobiTheta₂(τ/2,τ) ≠ 0 = 2 + tail`; the tail is bounded
(via the term norm, `n²+n ≥ |n|`, and the two-sided geometric series) by `∑_{n:ℤ} r^|n| < 2`
(`r = exp(-π·imτ) < 1/3`), so the value stays within distance `< 2` of `2` and cannot be `0`. With
`θ₃ ≠ 0` and `θ₄ ≠ 0`, **all three theta constants are non-vanishing on the fundamental domain.** -/
theorem thetaTwo_ne_zero_of_im_ge {τ : ℂ} (hτ : (4:ℝ)/5 ≤ τ.im) : thetaTwo τ ≠ 0 := by
  rw [thetaTwo_ne_zero_iff]
  have hτ0 : 0 < τ.im := by linarith
  set r : ℝ := Real.exp (-Real.pi * τ.im) with hr_def
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr13 : r < 1/3 := by
    have hπ : (3:ℝ) < Real.pi := Real.pi_gt_three
    have hle : -Real.pi * τ.im ≤ -(12/5) := by
      nlinarith [hπ, hτ, mul_nonneg (by linarith:(0:ℝ)≤Real.pi-3) (by linarith:(0:ℝ)≤τ.im-4/5)]
    have hk : (3:ℝ) < Real.exp (12/5) := by
      have h2 : (3:ℝ) ≤ Real.exp 2 := by nlinarith [Real.add_one_le_exp (2:ℝ)]
      linarith [Real.exp_lt_exp.mpr (show (2:ℝ) < 12/5 by norm_num)]
    rw [hr_def]
    calc Real.exp (-Real.pi * τ.im) ≤ Real.exp (-(12/5)) := Real.exp_le_exp.mpr hle
      _ < 1/3 := by rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
  -- geometric majorant
  have hr1 : r < 1 := by linarith
  have h1r : 0 < 1 - r := by linarith
  have hnat : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hgsum : Summable (fun n : ℤ => r ^ n.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]; exact ⟨by simpa using hnat, by simpa using hnat⟩
  have hgbound : ∑' n : ℤ, r ^ n.natAbs < 2 := by
    have heven : (fun n : ℤ => r ^ n.natAbs).Even := fun n => by simp only [Int.natAbs_neg]
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hgsum]
    have hpnat : (∑' n : ℕ+, r ^ ((n : ℤ)).natAbs) = r / (1 - r) := by
      have h1 : (∑' n : ℕ+, r ^ ((n : ℤ)).natAbs) = ∑' n : ℕ+, r ^ ((n : ℕ)) := by
        apply tsum_congr; intro n; simp
      rw [h1, tsum_pnat_eq_tsum_succ (f := fun k => r ^ k),
        show (fun n : ℕ => r ^ (n + 1)) = (fun n => r * r ^ n) from by funext n; rw [pow_succ]; ring,
        tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
    rw [hpnat, show ((0 : ℤ)).natAbs = 0 from rfl, pow_zero]
    have hfrac : r / (1 - r) < 1 / 2 := by rw [div_lt_iff₀ h1r]; linarith
    simp only [nsmul_eq_mul]; linarith
  -- term function f and indicator c
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (τ/2) τ with hf_def
  have hfsum : Summable f := (summable_jacobiTheta₂_term_iff (τ/2) τ).mpr hτ0
  set c : ℤ → ℂ := fun n => if n = 0 ∨ n = -1 then 1 else 0 with hc_def
  have hcHS : HasSum c (∑ i ∈ ({0, -1} : Finset ℤ), c i) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn; rw [hc_def]; simp only; rw [if_neg]; rintro (rfl | rfl) <;> simp at hn
  have hc_tsum : ∑' n, c n = 2 := by
    rw [hcHS.tsum_eq, Finset.sum_pair (show (0:ℤ) ≠ -1 by norm_num)]; norm_num [hc_def]
  have hcsum : Summable c := hcHS.summable
  -- per-term bound ‖f n - c n‖ ≤ r^natAbs
  have hbound : ∀ n : ℤ, ‖f n - c n‖ ≤ r ^ n.natAbs := by
    intro n
    by_cases h : n = 0 ∨ n = -1
    · rcases h with rfl | rfl
      · rw [hf_def, hc_def]; simp only [jacobiTheta₂_half_term_zero]; norm_num
      · rw [hf_def, hc_def]; simp only [jacobiTheta₂_half_term_negone]; norm_num; positivity
    · have hc0 : c n = 0 := by rw [hc_def]; simp only; rw [if_neg h]
      rw [hc0, sub_zero, hf_def, norm_jacobiTheta₂_half_term]
      have hne : n ≠ -1 := fun he => h (Or.inr he)
      have hcomp : |(n:ℝ)| ≤ (n:ℝ)^2 + n := sq_add_self_ge_abs n hne
      have habs : (n.natAbs : ℝ) = |(n:ℝ)| := by rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [hr_def, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hpt : 0 < Real.pi * τ.im := mul_pos Real.pi_pos hτ0
      nlinarith [hcomp, habs, hpt]
  have hfcsum : Summable (fun n => ‖f n - c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgsum
  have hkey : ‖jacobiTheta₂ (τ/2) τ - 2‖ < 2 := by
    have hjt : jacobiTheta₂ (τ/2) τ = ∑' n, f n := rfl
    have he : jacobiTheta₂ (τ/2) τ - 2 = ∑' n, (f n - c n) := by
      rw [hjt, Summable.tsum_sub hfsum hcsum, hc_tsum]
    rw [he]
    calc ‖∑' n, (f n - c n)‖ ≤ ∑' n, ‖f n - c n‖ := norm_tsum_le_tsum_norm hfcsum
      _ ≤ ∑' n : ℤ, r ^ n.natAbs := Summable.tsum_mono hfcsum hgsum hbound
      _ < 2 := hgbound
  intro h0
  rw [h0] at hkey
  norm_num at hkey

/-- **`λ ≠ 0` on `{im τ ≥ 4/5}` — "λ omits `0`".** Since `λ = (θ₂/θ₃)⁴` with `θ₂ ≠ 0` and `θ₃ ≠ 0` on
the fundamental domain, `λ` is non-zero there. (Omitting `1` needs the Jacobi quartic identity
`θ₃⁴ = θ₂⁴ + θ₄⁴` ⟹ `1 - λ = (θ₄/θ₃)⁴`, still ahead.) -/
theorem modularLambda_ne_zero_of_im_ge {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) : modularLambda τ ≠ 0 := by
  unfold modularLambda
  exact pow_ne_zero 4 (div_ne_zero (thetaTwo_ne_zero_of_im_ge hτ) (thetaThree_ne_zero_of_im_ge hτ))

/-- **`θ₃(τ+1) = θ₄(τ)`** — the `T : τ ↦ τ+1` transformation swaps `θ₃ ↔ θ₄`. -/
theorem thetaThree_add_one (τ : ℂ) : thetaThree (τ + 1) = thetaFour τ := by
  unfold thetaThree
  rw [← jacobiTheta_eq_jacobiTheta₂, ← thetaFour_eq]

/-- **`θ₄(τ+1) = θ₃(τ)`** — `T` swaps `θ₄ ↔ θ₃` (via `θ₄ = jacobiTheta(·+1)` and `jacobiTheta_two_add`). -/
theorem thetaFour_add_one (τ : ℂ) : thetaFour (τ + 1) = thetaThree τ := by
  rw [thetaFour_eq, show τ + 1 + 1 = 2 + τ by ring, jacobiTheta_two_add]
  unfold thetaThree; exact jacobiTheta_eq_jacobiTheta₂ τ

/-- **`θ₃(τ+2) = θ₃(τ)`** — `T²` fixes `θ₃` (two `T`-swaps `θ₃→θ₄→θ₃`). -/
theorem thetaThree_add_two (τ : ℂ) : thetaThree (τ + 2) = thetaThree τ := by
  rw [show τ + 2 = (τ + 1) + 1 by ring, thetaThree_add_one, thetaFour_add_one]

/-- **`θ₂(τ) = ∑ exp(πi(n+½)²τ)`** — the clean series form of `θ₂` (pull `exp(πiτ/4)` into the sum). -/
theorem thetaTwo_eq_tsum (τ : ℂ) :
    thetaTwo τ = ∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * I * ((n : ℂ) + 1/2) ^ 2 * τ) := by
  unfold thetaTwo
  rw [jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [jacobiTheta₂_term, ← Complex.exp_add]; congr 1; ring

/-- **`θ₂(τ+1) = exp(πi/4)·θ₂(τ)`** — the `T` action on `θ₂` (term factor `exp(πi(n+½)²) = exp(πi/4)`,
since `n²+n` is even). -/
theorem thetaTwo_add_one (τ : ℂ) :
    thetaTwo (τ + 1) = Complex.exp ((Real.pi : ℂ) * I / 4) * thetaTwo τ := by
  rw [thetaTwo_eq_tsum, thetaTwo_eq_tsum, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (n : ℤ) ^ 2 + n = 2 * k := by
    obtain ⟨m, hm⟩ := Int.even_mul_succ_self n
    exact ⟨m, by linear_combination hm⟩
  have hcast : ((n : ℂ)) ^ 2 + (n : ℂ) = 2 * (k : ℂ) := by exact_mod_cast hk
  exact ⟨k, by linear_combination ((↑Real.pi : ℂ) * I) * hcast⟩

/-- **`(θ₂θ₃θ₄)(τ+1) = exp(πi/4)·(θ₂θ₃θ₄)(τ)`** — the product is `T`-modular with a non-zero multiplier
(`θ₂→exp(πi/4)θ₂`, `θ₃↔θ₄`). This is the `T`-half of "`θ₂θ₃θ₄` is `SL(2,ℤ)`-modular", the route that
transports non-vanishing from the fundamental domain to all of `ℍ` (`exists_smul_mem_fd`). -/
theorem thetaProduct_add_one (τ : ℂ) :
    thetaTwo (τ + 1) * thetaThree (τ + 1) * thetaFour (τ + 1)
      = Complex.exp ((Real.pi : ℂ) * I / 4) * (thetaTwo τ * thetaThree τ * thetaFour τ) := by
  rw [thetaTwo_add_one, thetaThree_add_one, thetaFour_add_one]; ring

/-- **`θ₃(-1/τ) = (-Iτ)^{1/2}·θ₃(τ)`** — the `S : τ ↦ -1/τ` action on `θ₃`, from the `jacobiTheta₂`
functional equation at `z = 0`. (`S` fixes `θ₃` up to the automorphy factor `(-Iτ)^{1/2}`.) -/
theorem thetaThree_S (τ : ℂ) (hτ : τ ≠ 0) :
    thetaThree (-1/τ) = (-I*τ)^(1/2:ℂ) * thetaThree τ := by
  unfold thetaThree
  have hFE := jacobiTheta₂_functional_equation 0 τ
  rw [show ((0:ℂ))^2 = 0 by ring, show ((0:ℂ))/τ = 0 by simp] at hFE
  simp only [neg_mul, mul_zero, zero_div, Complex.exp_zero, mul_one] at hFE
  have hmul : -I * τ ≠ 0 := mul_ne_zero (by simp) hτ
  have hne : (-I*τ)^(1/2:ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num : (1/2:ℂ) ≠ 0)).mpr hmul
  rw [hFE]; field_simp

/-- **`θ₄(-1/τ) = (I/τ)^{-1/2}·θ₂(τ)`** — the `S` action swaps `θ₄ → θ₂` (FE at `z=1/2`). -/
theorem thetaFour_S (τ : ℂ) (hτ : τ ≠ 0) :
    thetaFour (-1/τ) = 1/(I/τ)^(1/2:ℂ) * thetaTwo τ := by
  unfold thetaFour
  have h1 : (-I * (-1 / τ)) = I / τ := by ring
  have h2 : ((1 : ℂ) / 2) / (-1 / τ) = -(τ / 2) := by field_simp
  have h3 : (-1 : ℂ) / (-1 / τ) = τ := by field_simp
  have h4 : (-↑Real.pi * I * ((1 : ℂ) / 2) ^ 2 / (-1 / τ)) = ↑Real.pi * I * τ / 4 := by
    field_simp; ring
  have hFE := jacobiTheta₂_functional_equation (1 / 2) (-1 / τ)
  rw [h1, h2, h3, h4, jacobiTheta₂_neg_left] at hFE
  rw [hFE]; unfold thetaTwo; ring

/-- **`θ₂(-1/τ) = (I/τ)^{-1/2}·θ₄(τ)`** — the `S` action swaps `θ₂ → θ₄` (FE at `z=-1/(2τ)`). -/
theorem thetaTwo_S (τ : ℂ) (hτ : τ ≠ 0) :
    thetaTwo (-1/τ) = 1/(I/τ)^(1/2:ℂ) * thetaFour τ := by
  unfold thetaTwo
  have hz : ((-1/τ)/2 : ℂ) = -1/(2*τ) := by field_simp
  rw [hz]
  have h1 : (-I * (-1 / τ)) = I / τ := by ring
  have h2 : ((-1/(2*τ)) / (-1 / τ)) = 1/2 := by field_simp
  have h3 : (-1 : ℂ) / (-1 / τ) = τ := by field_simp
  have h4 : (-↑Real.pi * I * (-1/(2*τ)) ^ 2 / (-1 / τ)) = ↑Real.pi * I / (4*τ) := by
    field_simp; ring
  have hFE := jacobiTheta₂_functional_equation (-1/(2*τ)) (-1 / τ)
  rw [h1, h2, h3, h4] at hFE
  rw [hFE]
  show Complex.exp (↑Real.pi * I * (-1/τ) / 4) *
    (1/(I/τ)^(1/2:ℂ) * Complex.exp (↑Real.pi * I / (4*τ)) * thetaFour τ)
    = 1/(I/τ)^(1/2:ℂ) * thetaFour τ
  rw [show Complex.exp (↑Real.pi * I * (-1/τ) / 4) * (1/(I/τ)^(1/2:ℂ) * Complex.exp (↑Real.pi * I / (4*τ)) * thetaFour τ)
    = (Complex.exp (↑Real.pi * I * (-1/τ) / 4) * Complex.exp (↑Real.pi * I / (4*τ))) * (1/(I/τ)^(1/2:ℂ) * thetaFour τ) by ring,
    ← Complex.exp_add, show (↑Real.pi * I * (-1/τ) / 4 + ↑Real.pi * I / (4*τ) : ℂ) = 0 by field_simp; ring,
    Complex.exp_zero, one_mul]

/-- **`(θ₂θ₃θ₄)(-1/τ) = M·(θ₂θ₃θ₄)(τ)`** — the product is `S`-modular (`θ₂↔θ₄` swap, `θ₃` fixed,
each up to a non-zero automorphy factor). -/
theorem thetaProduct_S (τ : ℂ) (hτ : τ ≠ 0) :
    thetaTwo (-1/τ) * thetaThree (-1/τ) * thetaFour (-1/τ)
      = (1/(I/τ)^(1/2:ℂ) * (-I*τ)^(1/2:ℂ) * (1/(I/τ)^(1/2:ℂ)))
          * (thetaTwo τ * thetaThree τ * thetaFour τ) := by
  rw [thetaTwo_S τ hτ, thetaThree_S τ hτ, thetaFour_S τ hτ]; ring

/-- The `S`-multiplier of the product `θ₂θ₃θ₄` is non-zero. -/
theorem thetaProduct_S_mul_ne_zero (τ : ℂ) (hτ : τ ≠ 0) :
    (1/(I/τ)^(1/2:ℂ) * (-I*τ)^(1/2:ℂ) * (1/(I/τ)^(1/2:ℂ))) ≠ 0 := by
  have hmul : -I * τ ≠ 0 := mul_ne_zero (by simp) hτ
  have hIτ : I / τ ≠ 0 := div_ne_zero (by simp) hτ
  have hc1 : (-I * τ) ^ (1/2:ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hmul
  have hc2 : (I / τ) ^ (1/2:ℂ) ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hIτ
  exact mul_ne_zero (mul_ne_zero (one_div_ne_zero hc2) hc1) (one_div_ne_zero hc2)

/-- **`(θ₂θ₃θ₄)(-1/τ) ≠ 0 ⟺ (θ₂θ₃θ₄)(τ) ≠ 0`** — `S`-invariance of the product's non-vanishing. With
the `T`-version (`thetaProduct_add_one`) this transports `θ₂θ₃θ₄ ≠ 0` (hence `θ₃ ≠ 0`) across `SL(2,ℤ)`. -/
theorem thetaProduct_ne_zero_neg_inv_iff (τ : ℂ) (hτ : τ ≠ 0) :
    (thetaTwo (-1/τ) * thetaThree (-1/τ) * thetaFour (-1/τ) ≠ 0)
      ↔ (thetaTwo τ * thetaThree τ * thetaFour τ ≠ 0) := by
  rw [thetaProduct_S τ hτ, mul_ne_zero_iff, and_iff_right (thetaProduct_S_mul_ne_zero τ hτ)]

/-- **`θ₂θ₃θ₄ ≠ 0` for `im τ ≥ 4/5`** — the product is non-vanishing on the fundamental domain (each
factor is, by the trio). This is the base case the `SL(2,ℤ)` transport (`thetaProduct_add_one`,
`thetaProduct_ne_zero_neg_inv_iff`, `exists_smul_mem_fd`) propagates to all of `ℍ` ⟹ `θ₃ ≠ 0` on `ℍ`. -/
theorem thetaProduct_ne_zero_of_im_ge {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    thetaTwo τ * thetaThree τ * thetaFour τ ≠ 0 :=
  mul_ne_zero (mul_ne_zero (thetaTwo_ne_zero_of_im_ge hτ) (thetaThree_ne_zero_of_im_ge hτ))
    (thetaFour_ne_zero_of_im_ge hτ)

/-- **`(θ₂θ₃θ₄)(τ+1) ≠ 0 ⟺ (θ₂θ₃θ₄)(τ) ≠ 0`** — `T`-invariance of the product's non-vanishing (the
multiplier `exp(πi/4)` is non-zero). Together with `thetaProduct_ne_zero_neg_inv_iff` (the `S`-version),
the non-vanishing of `θ₂θ₃θ₄` is invariant under both `SL(2,ℤ)` generators. -/
theorem thetaProduct_ne_zero_add_one_iff (τ : ℂ) :
    (thetaTwo (τ + 1) * thetaThree (τ + 1) * thetaFour (τ + 1) ≠ 0)
      ↔ (thetaTwo τ * thetaThree τ * thetaFour τ ≠ 0) := by
  rw [thetaProduct_add_one, mul_ne_zero_iff, and_iff_right (Complex.exp_ne_zero _)]

end Bottcher

/-! ## `θ₃ ≠ 0` on all of `ℍ` via the `SL(2,ℤ)` descent

The non-vanishing of the theta product `θ₂θ₃θ₄`, established on the fundamental-domain strip
`{im ≥ 4/5}`, propagates to the whole upper half-plane: the product is invariant under the two
generators `S : τ ↦ -1/τ` and `T : τ ↦ τ+1` (`thetaProduct_ne_zero_neg_inv_iff`,
`thetaProduct_ne_zero_add_one_iff`), hence under all of `SL(2,ℤ) = ⟨S,T⟩`
(`SpecialLinearGroup.SL2Z_generators`), and every `τ ∈ ℍ` reduces into `𝒟 ⊆ {im ≥ √3/2}` by
`ModularGroup.exists_smul_mem_fd`. Consequence: `θ₃ ≠ 0` everywhere on `ℍ`, so `λ = (θ₂/θ₃)⁴` is
holomorphic on the whole upper half-plane (no `im ≥ 4/5` restriction). -/

open UpperHalfPlane ModularGroup
open scoped Modular MatrixGroups

namespace Bottcher

/-- The product `θ₂θ₃θ₄` non-vanishing is invariant under the full `SL(2,ℤ)` action: proved by
`Subgroup.closure_induction` over `SL(2,ℤ) = ⟨S,T⟩`, with the two generator cases supplied by the
`S`- and `T`-invariance iffs `thetaProduct_ne_zero_neg_inv_iff` / `thetaProduct_ne_zero_add_one_iff`,
the multiplicative case by `mul_smul`, and the inverse case by `smul_inv_smul`. -/
theorem thetaProduct_ne_zero_smul_iff (g : SL(2, ℤ)) (z : ℍ) :
    (thetaTwo (↑(g • z)) * thetaThree (↑(g • z)) * thetaFour (↑(g • z)) ≠ 0)
      ↔ (thetaTwo (↑z) * thetaThree (↑z) * thetaFour (↑z) ≠ 0) := by
  have hmem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction generalizing z with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
        have hcoe : ((ModularGroup.S • z : ℍ) : ℂ) = -1 / (z : ℂ) := by
          rw [modular_S_smul, UpperHalfPlane.coe_mk]; simp [neg_div, one_div, inv_neg]
        rw [hcoe]; exact thetaProduct_ne_zero_neg_inv_iff (z : ℂ) hz0
      · have hcoe : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
          rw [modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
        rw [hcoe]; exact thetaProduct_ne_zero_add_one_iff (z : ℂ)
  | one => rw [one_smul]
  | mul x y _ _ ihx ihy => rw [mul_smul]; exact (ihx (y • z)).trans (ihy z)
  | inv x _ ihx =>
      have h := ihx (x⁻¹ • z); rw [smul_inv_smul] at h; exact h.symm

/-- **`θ₂θ₃θ₄` never vanishes on the upper half-plane.** Any `τ` with `im τ > 0` is `SL(2,ℤ)`-
equivalent to a point of the fundamental domain `𝒟` (`exists_smul_mem_fd`), where `im ≥ √3/2 ≥ 4/5`
forces the product non-zero (`thetaProduct_ne_zero_of_im_ge`); the product's `SL(2,ℤ)`-invariance
(`thetaProduct_ne_zero_smul_iff`) transports this back to `τ`. -/
theorem thetaProduct_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    thetaTwo τ * thetaThree τ * thetaFour τ ≠ 0 := by
  set z : ℍ := ⟨τ, hτ⟩ with hz
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have him : (4 : ℝ) / 5 ≤ ((g • z : ℍ) : ℂ).im := by
    rw [UpperHalfPlane.coe_im]
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • z).im_pos
    nlinarith [hpos, h3]
  have hfd : thetaTwo (↑(g • z)) * thetaThree (↑(g • z)) * thetaFour (↑(g • z)) ≠ 0 :=
    thetaProduct_ne_zero_of_im_ge him
  have := (thetaProduct_ne_zero_smul_iff g z).mp hfd
  simpa [hz, UpperHalfPlane.coe_mk] using this

/-- **`θ₃` never vanishes on the upper half-plane.** Immediate from `thetaProduct_ne_zero_of_im_pos`
(`θ₃` is a factor of the non-vanishing product). This removes the `im ≥ 4/5` restriction from
`thetaThree_ne_zero_of_im_ge`, so the modular `λ = (θ₂/θ₃)⁴` is holomorphic on **all** of `ℍ`. -/
theorem thetaThree_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : thetaThree τ ≠ 0 := by
  have h := thetaProduct_ne_zero_of_im_pos hτ
  exact fun h0 => h (by rw [h0]; ring)

end Bottcher

namespace Bottcher

/-- **`θ₂` never vanishes on the upper half-plane** (factor of the non-vanishing product). -/
theorem thetaTwo_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : thetaTwo τ ≠ 0 := by
  have h := thetaProduct_ne_zero_of_im_pos hτ
  exact fun h0 => h (by rw [h0]; ring)

/-- **`λ` is holomorphic on all of `ℍ`.** With `θ₃ ≠ 0` everywhere
(`thetaThree_ne_zero_of_im_pos`), the quotient `λ = (θ₂/θ₃)⁴` is differentiable at every `τ` with
`im τ > 0` — the `im ≥ 4/5` restriction of `differentiableAt_modularLambda_of_im_ge` is gone. -/
theorem differentiableAt_modularLambda_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ modularLambda τ :=
  differentiableAt_modularLambda hτ (thetaThree_ne_zero_of_im_pos hτ)

/-- **`λ` omits `0` on all of `ℍ`.** Both `θ₂` and `θ₃` are non-vanishing on the whole upper
half-plane, so `λ = (θ₂/θ₃)⁴ ≠ 0` everywhere — the first of the two omitted values `{0,1}` of the
modular `λ`, now without the fundamental-domain restriction. -/
theorem modularLambda_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : modularLambda τ ≠ 0 := by
  unfold modularLambda
  exact pow_ne_zero 4 (div_ne_zero (thetaTwo_ne_zero_of_im_pos hτ) (thetaThree_ne_zero_of_im_pos hτ))

end Bottcher

/-! ## Value-transforms of the modular `λ` under the generators `S`, `T`

The theta `S`/`T`-laws push down to the **values** of `λ = (θ₂/θ₃)⁴`. Under `S : τ ↦ -1/τ` the
common automorphy factor cancels to fourth power 1, swapping `θ₂ ↔ θ₄`, giving `λ(-1/τ) = (θ₄/θ₃)⁴`;
under `T : τ ↦ τ+1` the factor `exp(πi/4)⁴ = -1` gives `λ(τ+1) = -(θ₂/θ₄)⁴`. These are the value-
level half of the anharmonic action `λ ↦ {λ, 1-λ, 1/λ, …}`; combined with the (still-open) Jacobi
quartic identity `θ₃⁴ = θ₂⁴ + θ₄⁴` they become `λ(-1/τ) = 1-λ(τ)` and `λ(τ+1) = λ/(λ-1)`, which turn
`λ`-omits-`0` (already proved on all `ℍ`) into `λ`-omits-`1`. -/

namespace Bottcher

/-- **`S`-transform of `λ`-values: `λ(-1/τ) = (θ₄/θ₃)⁴`.** From the theta `S`-laws
`thetaTwo_S`, `thetaThree_S` (`θ₂ ↦ θ₄`, `θ₃ ↦ θ₃` up to the factor `√(I/τ)`, `√(-Iτ)`): the
combined factor squares to `(I/τ)(-Iτ) = 1`, so its fourth power is `1` and `λ(-1/τ)` reduces to
`(θ₄/θ₃)⁴`. No quartic identity needed — pure `S`-automorphy. -/
theorem modularLambda_S {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda (-1/τ) = (thetaFour τ / thetaThree τ) ^ 4 := by
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτ; simp at hτ
  have hθ3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have hIτ : Complex.I / τ ≠ 0 := div_ne_zero Complex.I_ne_zero hτ0
  have hmIτ : -Complex.I * τ ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hτ0
  unfold modularLambda
  rw [thetaTwo_S τ hτ0, thetaThree_S τ hτ0]
  set P := ((Complex.I / τ) ^ (1/2 : ℂ)) with hP
  set Q := ((-Complex.I * τ) ^ (1/2 : ℂ)) with hQ
  have hPne : P ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hIτ
  have hQne : Q ≠ 0 :=
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hmIτ
  have hP2 : P ^ 2 = Complex.I / τ := by
    rw [hP, pow_two, ← Complex.cpow_add _ _ hIτ, show (1/2 : ℂ) + 1/2 = 1 by norm_num,
      Complex.cpow_one]
  have hQ2 : Q ^ 2 = -Complex.I * τ := by
    rw [hQ, pow_two, ← Complex.cpow_add _ _ hmIτ, show (1/2 : ℂ) + 1/2 = 1 by norm_num,
      Complex.cpow_one]
  have hPQ4 : (P * Q) ^ 4 = 1 := by
    have h2 : (P * Q) ^ 2 = 1 := by
      rw [mul_pow, hP2, hQ2]
      have he : (Complex.I / τ) * (-Complex.I * τ) = -(Complex.I ^ 2) * (τ / τ) := by ring
      rw [he, Complex.I_sq, div_self hτ0]; norm_num
    calc (P * Q) ^ 4 = ((P * Q) ^ 2) ^ 2 := by ring
      _ = (1 : ℂ) ^ 2 := by rw [h2]
      _ = 1 := one_pow 2
  have hbase : (1 : ℂ) / P * thetaFour τ / (Q * thetaThree τ)
      = thetaFour τ / (P * Q * thetaThree τ) := by
    field_simp
  rw [hbase, div_pow, mul_pow, hPQ4, one_mul, ← div_pow]

/-- **`T`-transform of `λ`-values: `λ(τ+1) = -(θ₂/θ₄)⁴`.** From `thetaTwo_add_one`
(`θ₂ ↦ exp(πi/4)·θ₂`) and `thetaThree_add_one` (`θ₃ ↦ θ₄`): the prefactor `exp(πi/4)⁴ = exp(πi) = -1`.
Purely algebraic — holds for every `τ`. -/
theorem modularLambda_T (τ : ℂ) :
    modularLambda (τ + 1) = -(thetaTwo τ / thetaFour τ) ^ 4 := by
  unfold modularLambda
  rw [thetaTwo_add_one, thetaThree_add_one]
  have hexp : (Complex.exp ((Real.pi : ℂ) * Complex.I / 4)) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, show ((4 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 4) = (Real.pi : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.exp_pi_mul_I
  rw [mul_div_assoc, mul_pow, hexp, neg_one_mul]

end Bottcher
