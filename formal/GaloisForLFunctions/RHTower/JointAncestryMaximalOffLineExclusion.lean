import GaloisForLFunctions.RHTower.JointAncestryTwistedKroneckerDomination
import GaloisForLFunctions.RHTower.JointAncestryPrimeSumComparison

/-!
# A maximal off-line zero excludes JAS positivity below `σ = 1 + δ`

Suppose some Xi zero `ρ₀ = β₀ + iγ₀` has the largest distance `δ₀ = |β₀ - 1/2| > 0` from the critical
line among all Xi zeros.  Then the dressed JAS aggregate is not positive semidefinite for any
`σ < 1 + δ₀`.

Proof.  Test the aggregate with the Bernoulli family at the twisted Kronecker point
`z_p = e^{iφ} p^{iγ₀}` of `ρ₀` over all primes `p ≤ N`.  Each zero `ρ = β + iγ` contributes
`∏_{p ≤ N} G(r₁(β), r₂(β), φ + (γ₀ - γ) log p) / (ρ(1-ρ))`.

* `ρ₀` and `1 - ρ̄₀` contribute `Re(w₀ G)` each; the twist `φ` is chosen so that this equals
  `-|w₀| |G|`, and it is small, so `|G|` keeps essentially its full Kronecker amplitude.
* A zero with smaller distance from the line has radii `p^{-α'}`, `α' > α = β₀ + c`, and
  `Σ p^{-α'} = o(Σ p^{-α})`.
* A zero with the same distance at another height sees the phases `(γ₀ - γ) log p`; by the prime
  number theorem `|Σ_{p ≤ N} p^{-α} e^{iΔ log p}| ≤ κ Σ_{p ≤ N} p^{-α}` with `κ < 1`.
* By maximality every zero has Bernoulli product at most `∏ (2 + r₁ + r₂)`, so the zeros outside a
  finite set contribute at most their total weight times `2|G|`.

For `N` large the dominant pair outweighs everything else and the Bernoulli form is negative.

So positivity of the dressed aggregate below `σ = 1` forces either RH or an off-line zero set whose
distances from the critical line have no largest element.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## Twisted values at another height -/

theorem jasTwistedPoint_shift (ρ q : ℂ) (φ : ℝ) (p : Nat.Primes) :
    jasTwistedPoint ρ φ p = jasTwistedPoint q (φ + (ρ.im - q.im) * Real.log p) p := by
  unfold jasTwistedPoint jasKroneckerPoint
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem jasDressedBernoulli_twisted_general (ρ q : ℂ) (c φ : ℝ) (p : Nat.Primes) :
    jasDressedBernoulli q c p (jasTwistedPoint ρ φ p) =
      jasTwistedValue (jasR1 (q + c) p) (jasR2 (q - c) p) (φ + (ρ.im - q.im) * Real.log p) := by
  rw [jasTwistedPoint_shift ρ q, jasDressedBernoulli_twisted]

theorem jasTwistedValue_swap (r₁ r₂ φ : ℝ) :
    jasTwistedValue r₂ r₁ φ = conj (jasTwistedValue r₁ r₂ φ) := by
  apply Complex.ext
  · rw [Complex.conj_re, re_jasTwistedValue, re_jasTwistedValue]; ring
  · rw [Complex.conj_im, im_jasTwistedValue, im_jasTwistedValue]; ring

theorem norm_jasTwistedValue_le_add {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (φ : ℝ) :
    ‖jasTwistedValue r₁ r₂ φ‖ ≤ 2 + r₁ + r₂ := by
  have e₁ : ‖(r₁ : ℂ) * cexp ((φ : ℂ) * I)‖ = r₁ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg h₁]
  have e₂ : ‖(r₂ : ℂ) * cexp (((-φ : ℝ) : ℂ) * I)‖ = r₂ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg h₂]
  calc ‖jasTwistedValue r₁ r₂ φ‖
      ≤ ‖(2 : ℂ) + (r₁ : ℂ) * cexp ((φ : ℂ) * I)‖ + ‖(r₂ : ℂ) * cexp (((-φ : ℝ) : ℂ) * I)‖ :=
        norm_add_le _ _
    _ ≤ ‖(2 : ℂ)‖ + ‖(r₁ : ℂ) * cexp ((φ : ℂ) * I)‖ + ‖(r₂ : ℂ) * cexp (((-φ : ℝ) : ℂ) * I)‖ := by
        gcongr; exact norm_add_le _ _
    _ = 2 + r₁ + r₂ := by rw [e₁, e₂]; norm_num

/-- `|G(r₁, r₂, ψ)| ≤ 2 + (r₁ + r₂) cos ψ + (r₁ - r₂)² / (2m)` when `2 - r₁ - r₂ ≥ m > 0`. -/
theorem norm_jasTwistedValue_le_cos {r₁ r₂ m : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) (hm : 0 < m)
    (hm' : m ≤ 2 - r₁ - r₂) (ψ : ℝ) :
    ‖jasTwistedValue r₁ r₂ ψ‖ ≤ 2 + (r₁ + r₂) * Real.cos ψ + (r₁ - r₂) ^ 2 / (2 * m) := by
  set a := 2 + (r₁ + r₂) * Real.cos ψ with ha
  have hcos := Real.neg_one_le_cos ψ
  have ham : m ≤ a := by rw [ha]; nlinarith
  have hsq : ‖jasTwistedValue r₁ r₂ ψ‖ ^ 2 ≤ a ^ 2 + (r₁ - r₂) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, re_jasTwistedValue, im_jasTwistedValue]
    have := Real.sin_sq_le_one ψ
    nlinarith [sq_nonneg (r₁ - r₂)]
  have hX : 0 ≤ a + (r₁ - r₂) ^ 2 / (2 * m) := by
    have : 0 ≤ (r₁ - r₂) ^ 2 / (2 * m) := by positivity
    linarith
  rw [← sq_le_sq₀ (norm_nonneg _) hX]
  refine hsq.trans ?_
  have hb : 0 ≤ (r₁ - r₂) ^ 2 / (2 * m) := by positivity
  have : (r₁ - r₂) ^ 2 ≤ 2 * a * ((r₁ - r₂) ^ 2 / (2 * m)) := by
    rw [show 2 * a * ((r₁ - r₂) ^ 2 / (2 * m)) = (a / m) * (r₁ - r₂) ^ 2 by field_simp]
    have : 1 ≤ a / m := by rw [le_div_iff₀ hm]; linarith
    nlinarith [sq_nonneg (r₁ - r₂)]
  nlinarith

theorem two_add_mul_cos_le_norm_jasTwistedValue (r₁ r₂ φ : ℝ) :
    2 + (r₁ + r₂) * Real.cos φ ≤ ‖jasTwistedValue r₁ r₂ φ‖ := by
  rw [← re_jasTwistedValue]; exact Complex.re_le_norm _

/-! ## Product comparisons -/

theorem exp_sub_sq_le_one_add {v : ℝ} (h0 : 0 ≤ v) : Real.exp (v - v ^ 2) ≤ 1 + v := by
  have hx : v - v ^ 2 < 1 := by nlinarith
  have h := Real.one_sub_le_exp_neg (v - v ^ 2)
  have hpos : 0 < 1 - (v - v ^ 2) := by linarith
  have hexp : Real.exp (v - v ^ 2) * (1 - (v - v ^ 2)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h (Real.exp_pos (v - v ^ 2)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    linarith
  have hv3 : 1 ≤ (1 + v) * (1 - (v - v ^ 2)) := by nlinarith [pow_nonneg h0 3]
  nlinarith [Real.exp_pos (v - v ^ 2)]

/-- `|∏ F| ≤ exp(Σ (u - v + v²)) |∏ G|` when `|G_p| ≥ 2(1 + v_p)`, `v_p ≥ 0`, and
`|F_p| ≤ 2(1 + u_p)`. -/
theorem norm_prod_le_exp_mul_norm_prod {ι : Type*} (P : Finset ι) (F G : ι → ℂ) (u v : ι → ℝ)
    (hv0 : ∀ i ∈ P, 0 ≤ v i) (hG : ∀ i ∈ P, 2 * (1 + v i) ≤ ‖G i‖)
    (hF : ∀ i ∈ P, ‖F i‖ ≤ 2 * (1 + u i)) :
    ‖∏ i ∈ P, F i‖ ≤ Real.exp (∑ i ∈ P, (u i - v i + v i ^ 2)) * ‖∏ i ∈ P, G i‖ := by
  rw [norm_prod, norm_prod, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => ?_
  have h1 : ‖F i‖ ≤ 2 * Real.exp (u i) := (hF i hi).trans (by
    have := Real.add_one_le_exp (u i); linarith)
  have h2 : 2 * Real.exp (v i - v i ^ 2) ≤ ‖G i‖ :=
    (mul_le_mul_of_nonneg_left (exp_sub_sq_le_one_add (hv0 i hi)) (by norm_num)).trans
      (hG i hi)
  calc ‖F i‖ ≤ 2 * Real.exp (u i) := h1
    _ = Real.exp (u i - v i + v i ^ 2) * (2 * Real.exp (v i - v i ^ 2)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (u i - v i + v i ^ 2) * ‖G i‖ := by gcongr

/-- `∏ (2 + a_p) ≤ exp(Σ a_p (1 - cos φ)/2) |∏ G_p|` when `|G_p| ≥ 2 + a_p cos φ`. -/
theorem prod_two_add_le_exp_mul_norm_prod {ι : Type*} (P : Finset ι) (G : ι → ℂ) (a : ι → ℝ)
    {φ : ℝ} (hc0 : 0 ≤ Real.cos φ) (ha : ∀ i ∈ P, 0 ≤ a i)
    (hG : ∀ i ∈ P, 2 + a i * Real.cos φ ≤ ‖G i‖) :
    ∏ i ∈ P, (2 + a i) ≤ Real.exp (∑ i ∈ P, a i * (1 - Real.cos φ) / 2) * ‖∏ i ∈ P, G i‖ := by
  rw [norm_prod, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i hi => by have := ha i hi; positivity) fun i hi => ?_
  have hc1 := Real.cos_le_one φ
  have hai := ha i hi
  have h1 : 1 + a i * (1 - Real.cos φ) / 2 ≤ Real.exp (a i * (1 - Real.cos φ) / 2) := by
    have := Real.add_one_le_exp (a i * (1 - Real.cos φ) / 2); linarith
  have h2 : 2 + a i ≤ (1 + a i * (1 - Real.cos φ) / 2) * (2 + a i * Real.cos φ) := by
    nlinarith [mul_nonneg (mul_nonneg hai hai) (mul_nonneg hc0 (sub_nonneg.mpr hc1))]
  calc 2 + a i ≤ (1 + a i * (1 - Real.cos φ) / 2) * (2 + a i * Real.cos φ) := h2
    _ ≤ Real.exp (a i * (1 - Real.cos φ) / 2) * ‖G i‖ := by
        apply mul_le_mul h1 (hG i hi) (by nlinarith) (Real.exp_pos _).le

/-! ## Radii -/

theorem jasR1_add_jasR2_eq (q : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasR1 (q + c) p + jasR2 (q - c) p =
      Real.exp (-(1 / 2 + c) * Real.log p) * (2 * Real.cosh ((1 / 2 - q.re) * Real.log p)) := by
  rw [jasR1_dressed, jasR2_dressed, Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero, mul_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> ring

/-- The radius sum grows with the distance from the critical line. -/
theorem jasR1_add_jasR2_le_of_abs_le {q ρ : ℂ} (h : |q.re - 1 / 2| ≤ |ρ.re - 1 / 2|) (c : ℝ)
    (p : Nat.Primes) :
    jasR1 (q + c) p + jasR2 (q - c) p ≤ jasR1 (ρ + c) p + jasR2 (ρ - c) p := by
  rw [jasR1_add_jasR2_eq, jasR1_add_jasR2_eq]
  gcongr
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos (log_prime_pos p), abs_sub_comm (1 / 2),
    abs_sub_comm (1 / 2)]
  exact mul_le_mul_of_nonneg_right h (log_prime_pos p).le

theorem jasR1_add_jasR2_le_two_mul (q : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasR1 (q + c) p + jasR2 (q - c) p ≤
      2 * Real.exp (-(1 / 2 - |q.re - 1 / 2| + c) * Real.log p) := by
  rw [jasR1_dressed, jasR2_dressed]
  have hl := (log_prime_pos p).le
  have e1 : Real.exp (-(q.re + c) * Real.log p) ≤
      Real.exp (-(1 / 2 - |q.re - 1 / 2| + c) * Real.log p) :=
    Real.exp_le_exp.mpr (by nlinarith [neg_abs_le (q.re - 1 / 2)])
  have e2 : Real.exp (-(1 - q.re + c) * Real.log p) ≤
      Real.exp (-(1 / 2 - |q.re - 1 / 2| + c) * Real.log p) :=
    Real.exp_le_exp.mpr (by nlinarith [le_abs_self (q.re - 1 / 2)])
  linarith

/-! ## The twist -/

/-- A total phase `θ ≤ Σ (r₁ - r₂)/4` is reached by a twist with `sin φ · Σ (r₁ - r₂) ≤ 4θ`. -/
theorem exists_jasTwist {P : Finset Nat.Primes} {r₁ r₂ : Nat.Primes → ℝ}
    (h₂ : ∀ p, 0 ≤ r₂ p) (h₁₂ : ∀ p, r₂ p ≤ r₁ p) (h₁ : ∀ p, r₁ p < 1) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ (∑ p ∈ P, (r₁ p - r₂ p)) / 4) :
    ∃ φ : ℝ, 0 ≤ φ ∧ φ ≤ Real.pi / 2 ∧
      ∑ p ∈ P, (jasTwistedValue (r₁ p) (r₂ p) φ).arg = θ ∧
      Real.sin φ * ∑ p ∈ P, (r₁ p - r₂ p) ≤ 4 * θ := by
  set Θ : ℝ → ℝ := fun φ => ∑ p ∈ P, (jasTwistedValue (r₁ p) (r₂ p) φ).arg with hΘ
  have hr₁0 : ∀ p, 0 ≤ r₁ p := fun p => (h₂ p).trans (h₁₂ p)
  have hcont : Continuous Θ :=
    continuous_finsetSum _ fun p _ =>
      continuous_arg_jasTwistedValue (hr₁0 p) (h₁ p) (h₂ p) ((h₁₂ p).trans_lt (h₁ p))
  have hΘ0 : Θ 0 = 0 := Finset.sum_eq_zero fun p _ => jasTwistedValue_zero_arg _ _ (hr₁0 p) (h₂ p)
  have hge : ∀ φ, 0 ≤ φ → φ ≤ Real.pi / 2 → Real.sin φ * (∑ p ∈ P, (r₁ p - r₂ p)) / 4 ≤ Θ φ := by
    intro φ h0 h1
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun p _ => ?_
    have := arg_jasTwistedValue_ge (hr₁0 p) (h₁ p) (h₂ p) (h₁₂ p) h0 h1
    linarith [show Real.sin φ * (r₁ p - r₂ p) / 4 = (r₁ p - r₂ p) * Real.sin φ / 4 by ring]
  have htop : θ ≤ Θ (Real.pi / 2) := by
    have := hge (Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl
    rw [Real.sin_pi_div_two, one_mul] at this
    linarith
  obtain ⟨φ, ⟨h0, h1⟩, hφ⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] :
    (0 : ℝ) ≤ Real.pi / 2) hcont.continuousOn ⟨by rw [hΘ0]; exact hθ0, htop⟩
  refine ⟨φ, h0, h1, hφ, ?_⟩
  have := hge φ h0 h1
  rw [hφ] at this
  linarith

/-- A small twist: `(1 - cos φ) S ≤ 64π² / (g² S)` when `sin φ · Σ (r₁ - r₂) ≤ 8π` and
`Σ (r₁ - r₂) ≥ g S`. -/
theorem one_sub_cos_mul_le {φ S T g : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ Real.pi / 2) (hg : 0 < g)
    (hS : 0 < S) (hT : g * S ≤ T) (hsin : Real.sin φ * T ≤ 8 * Real.pi) :
    (1 - Real.cos φ) * S ≤ 64 * Real.pi ^ 2 / (g ^ 2 * S) := by
  have hc0 : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hs0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hT0 : 0 < T := lt_of_lt_of_le (mul_pos hg hS) hT
  have hsinle : Real.sin φ ≤ 8 * Real.pi / (g * S) := by
    rw [le_div_iff₀ (mul_pos hg hS)]
    nlinarith
  have hcs : 1 - Real.cos φ ≤ Real.sin φ ^ 2 := by
    have := Real.cos_sq_add_sin_sq φ
    have := Real.cos_le_one φ
    nlinarith
  have hsq : Real.sin φ ^ 2 ≤ (8 * Real.pi / (g * S)) ^ 2 := by
    exact pow_le_pow_left₀ hs0 hsinle 2
  calc (1 - Real.cos φ) * S ≤ (8 * Real.pi / (g * S)) ^ 2 * S := by gcongr; linarith
    _ = 64 * Real.pi ^ 2 / (g ^ 2 * S) := by field_simp; ring

/-! ## Competitors -/

theorem sq_mul_div_two_le {r x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (r * x / 2) ^ 2 ≤ r ^ 2 / 4 := by
  have hx : x ^ 2 ≤ 1 := by nlinarith
  rw [div_pow, mul_pow]
  nlinarith [sq_nonneg r]

/-- Competitors closer to the critical line: radii `≤ p^{-α'}` with `α' > α`. -/
theorem eventually_jasHead_le_of_lt {α α' g : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hαα' : α < α')
    (hg : 0 < g) {η : ℝ} (hη : 0 < η) {r₁ r₂ : Nat.Primes → ℝ}
    (hr₁ : ∀ p, r₁ p = Real.exp (-α * Real.log p)) (hr₂ : ∀ p, 0 ≤ r₂ p)
    (F : ℝ → Nat.Primes → ℂ) (hF : ∀ φ p, ‖F φ p‖ ≤ 2 * (1 + Real.exp (-α' * Real.log p))) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      g * jasPrimeRpowSum α N ≤ ∑ p ∈ jasPrimesUpTo N, (r₁ p - r₂ p) →
      Real.sin φ * ∑ p ∈ jasPrimesUpTo N, (r₁ p - r₂ p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesUpTo N, F φ p‖ ≤
        η * ‖∏ p ∈ jasPrimesUpTo N, jasTwistedValue (r₁ p) (r₂ p) φ‖ := by
  set T₀ := max 1 (max (64 * Real.pi ^ 2 / g ^ 2) (2 + 4 * |Real.log η|)) with hT₀
  filter_upwards [eventually_jasPrimeRpowSum_le hα1.le hαα' (ε := 1 / 8) (by norm_num),
    eventually_jasPrimeRpowSum_le hα1.le (show α < 2 * α by linarith) (ε := 1 / 2) (by norm_num),
    (tendsto_jasPrimeRpowSum_atTop hα1.le).eventually_ge_atTop T₀] with N h1 h2 h3
  intro φ h0 hφ1 hT hsin
  set S := jasPrimeRpowSum α N with hS
  have hS1 : 1 ≤ S := (le_max_left _ _).trans h3
  have hS0 : 0 < S := by linarith
  have hSg : 64 * Real.pi ^ 2 / g ^ 2 ≤ S := ((le_max_left _ _).trans (le_max_right _ _)).trans h3
  have hSη : 2 + 4 * |Real.log η| ≤ S := ((le_max_right _ _).trans (le_max_right _ _)).trans h3
  have hc0 : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
  have hc1 := Real.cos_le_one φ
  have hr₁0 : ∀ p, 0 ≤ r₁ p := fun p => by rw [hr₁]; exact (Real.exp_pos _).le
  have hr₁1 : ∀ p, r₁ p ≤ 1 := fun p => by
    rw [hr₁, Real.exp_le_one_iff]; nlinarith [log_prime_pos p]
  have hcos := one_sub_cos_mul_le h0 hφ1 hg hS0 hT hsin
  have hcos1 : (1 - Real.cos φ) * S ≤ 1 := by
    refine hcos.trans ?_
    rw [div_le_one (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hSg
    linarith
  have hsumr₁ : ∑ p ∈ jasPrimesUpTo N, r₁ p = S := by
    rw [hS, jasPrimeRpowSum]; exact Finset.sum_congr rfl fun p _ => hr₁ p
  have hsumsq : ∑ p ∈ jasPrimesUpTo N, r₁ p ^ 2 = jasPrimeRpowSum (2 * α) N := by
    rw [jasPrimeRpowSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hr₁, sq, ← Real.exp_add]; congr 1; ring
  refine (norm_prod_le_exp_mul_norm_prod _ (F φ) (fun p => jasTwistedValue (r₁ p) (r₂ p) φ)
    (fun p => Real.exp (-α' * Real.log p))
    (fun p => r₁ p * Real.cos φ / 2) (fun p _ => by have := hr₁0 p; positivity)
    (fun p _ => ?_) (fun p _ => hF φ p)).trans ?_
  · have := two_add_mul_cos_le_norm_jasTwistedValue (r₁ p) (r₂ p) φ
    nlinarith [hr₂ p]
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hexp : ∑ p ∈ jasPrimesUpTo N, (Real.exp (-α' * Real.log p) - r₁ p * Real.cos φ / 2 +
        (r₁ p * Real.cos φ / 2) ^ 2) ≤ -S / 4 + 1 / 2 := by
      have hv2 : ∀ p, (r₁ p * Real.cos φ / 2) ^ 2 ≤ r₁ p ^ 2 / 4 := fun p =>
        sq_mul_div_two_le hc0 hc1
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have e1 : ∑ p ∈ jasPrimesUpTo N, Real.exp (-α' * Real.log p) = jasPrimeRpowSum α' N := rfl
      have e2 : ∑ p ∈ jasPrimesUpTo N, r₁ p * Real.cos φ / 2 = Real.cos φ * S / 2 := by
        rw [← hsumr₁, Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun p _ => by ring
      have e3 : ∑ p ∈ jasPrimesUpTo N, (r₁ p * Real.cos φ / 2) ^ 2 ≤ S / 8 := by
        calc _ ≤ ∑ p ∈ jasPrimesUpTo N, r₁ p ^ 2 / 4 := Finset.sum_le_sum fun p _ => hv2 p
          _ = jasPrimeRpowSum (2 * α) N / 4 := by rw [← Finset.sum_div, hsumsq]
          _ ≤ S / 8 := by linarith
      rw [e1, e2]
      nlinarith
    have hlog : -S / 4 + 1 / 2 ≤ Real.log η := by
      have := neg_abs_le (Real.log η)
      linarith
    calc Real.exp _ ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr (hexp.trans hlog)
      _ = η := Real.exp_log hη

/-- Competitors at the same distance from the line and another height. -/
theorem eventually_jasHead_le_of_twist {α α₂ Δ g m : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hαα₂ : α < α₂) (hΔ : Δ ≠ 0) (hg : 0 < g) (hm : 0 < m) {η : ℝ} (hη : 0 < η)
    {r₁ r₂ : Nat.Primes → ℝ} (hr₁ : ∀ p, r₁ p = Real.exp (-α * Real.log p))
    (hr₂ : ∀ p, r₂ p = Real.exp (-α₂ * Real.log p)) (F : ℝ → Nat.Primes → ℂ)
    (hF : ∀ φ p, ‖F φ p‖ ≤ 2 + (r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) +
      (r₁ p - r₂ p) ^ 2 / (2 * m)) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      g * jasPrimeRpowSum α N ≤ ∑ p ∈ jasPrimesUpTo N, (r₁ p - r₂ p) →
      Real.sin φ * ∑ p ∈ jasPrimesUpTo N, (r₁ p - r₂ p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesUpTo N, F φ p‖ ≤
        η * ‖∏ p ∈ jasPrimesUpTo N, jasTwistedValue (r₁ p) (r₂ p) φ‖ := by
  obtain ⟨κ, hκ1, hκev⟩ := exists_twisted_jasPrimeRpowSum_le hα0 hα1 hΔ
  set ε := (1 - κ) / (3 + 1 / m) with hε
  have hε0 : 0 < ε := by rw [hε]; apply div_pos (by linarith); positivity
  set T₀ := max 1 (max (64 * Real.pi ^ 2 / g ^ 2) ((2 + 4 * |Real.log η|) / (1 - κ))) with hT₀
  filter_upwards [hκev, eventually_jasPrimeRpowSum_le hα1.le hαα₂ hε0,
    eventually_jasPrimeRpowSum_le hα1.le (show α < 2 * α by linarith) hε0,
    (tendsto_jasPrimeRpowSum_atTop hα1.le).eventually_ge_atTop T₀] with N hK h1 h2 h3
  intro φ h0 hφ1 hT hsin
  set S := jasPrimeRpowSum α N with hS
  have hS1 : 1 ≤ S := (le_max_left _ _).trans h3
  have hS0 : 0 < S := by linarith
  have hSg : 64 * Real.pi ^ 2 / g ^ 2 ≤ S := ((le_max_left _ _).trans (le_max_right _ _)).trans h3
  have hSη : (2 + 4 * |Real.log η|) / (1 - κ) ≤ S :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans h3
  have hc0 : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hφ1⟩
  have hc1 := Real.cos_le_one φ
  have hr₁0 : ∀ p, 0 ≤ r₁ p := fun p => by rw [hr₁]; exact (Real.exp_pos _).le
  have hr₂0 : ∀ p, 0 ≤ r₂ p := fun p => by rw [hr₂]; exact (Real.exp_pos _).le
  have hr₂₁ : ∀ p, r₂ p ≤ r₁ p := fun p => by
    rw [hr₁, hr₂]; exact Real.exp_le_exp.mpr (by nlinarith [log_prime_pos p])
  have hcos := one_sub_cos_mul_le h0 hφ1 hg hS0 hT hsin
  have hcos1 : (1 - Real.cos φ) * S ≤ 1 := by
    refine hcos.trans ?_
    rw [div_le_one (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hSg
    linarith
  have hsumr₁ : ∑ p ∈ jasPrimesUpTo N, r₁ p = S := by
    rw [hS, jasPrimeRpowSum]; exact Finset.sum_congr rfl fun p _ => hr₁ p
  have hsumr₂ : ∑ p ∈ jasPrimesUpTo N, r₂ p = jasPrimeRpowSum α₂ N := by
    rw [jasPrimeRpowSum]; exact Finset.sum_congr rfl fun p _ => hr₂ p
  have hsumsq : ∑ p ∈ jasPrimesUpTo N, r₁ p ^ 2 = jasPrimeRpowSum (2 * α) N := by
    rw [jasPrimeRpowSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hr₁, sq, ← Real.exp_add]; congr 1; ring
  -- the oscillating sum
  have hosc : ∑ p ∈ jasPrimesUpTo N, r₁ p * Real.cos (φ + Δ * Real.log p) ≤ κ * S := by
    have hterm : ∀ p : Nat.Primes, r₁ p * Real.cos (φ + Δ * Real.log p) =
        (cexp ((φ : ℂ) * I) * ((Real.exp (-α * Real.log p) : ℂ) *
          cexp (((Δ * Real.log p : ℝ) : ℂ) * I))).re := by
      intro p
      rw [mul_left_comm, ← Complex.exp_add, ← hr₁,
        show (φ : ℂ) * I + ((Δ * Real.log p : ℝ) : ℂ) * I = ((φ + Δ * Real.log p : ℝ) : ℂ) * I by
          push_cast; ring, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    rw [Finset.sum_congr rfl fun p _ => hterm p, ← Complex.re_sum, ← Finset.mul_sum]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hK
  refine (norm_prod_le_exp_mul_norm_prod _ (F φ) (fun p => jasTwistedValue (r₁ p) (r₂ p) φ)
    (fun p => ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2)
    (fun p => r₁ p * Real.cos φ / 2) (fun p _ => by have := hr₁0 p; positivity)
    (fun p _ => ?_) (fun p _ => by have := hF φ p; linarith)).trans ?_
  · have := two_add_mul_cos_le_norm_jasTwistedValue (r₁ p) (r₂ p) φ
    nlinarith [hr₂0 p]
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hu : ∀ p, ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2
        ≤ r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p / 2 + r₁ p ^ 2 / (4 * m) := by
      intro p
      have hc := Real.cos_le_one (φ + Δ * Real.log p)
      have h2 : r₂ p * Real.cos (φ + Δ * Real.log p) ≤ r₂ p := by nlinarith [hr₂0 p]
      have h3 : (r₁ p - r₂ p) ^ 2 ≤ r₁ p ^ 2 := by nlinarith [hr₂0 p, hr₂₁ p]
      have h4 : (r₁ p - r₂ p) ^ 2 / (2 * m) ≤ r₁ p ^ 2 / (2 * m) :=
        div_le_div_of_nonneg_right h3 (by positivity)
      have h5 : r₁ p ^ 2 / (2 * m) / 2 = r₁ p ^ 2 / (4 * m) := by field_simp; ring
      calc ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2
          = r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p * Real.cos (φ + Δ * Real.log p) / 2 +
              (r₁ p - r₂ p) ^ 2 / (2 * m) / 2 := by ring
        _ ≤ r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p / 2 + r₁ p ^ 2 / (2 * m) / 2 := by
            linarith
        _ = _ := by rw [h5]
    have hv2 : ∀ p, (r₁ p * Real.cos φ / 2) ^ 2 ≤ r₁ p ^ 2 / 4 := fun p =>
      sq_mul_div_two_le hc0 hc1
    have hexp : ∑ p ∈ jasPrimesUpTo N,
        (((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2 -
          r₁ p * Real.cos φ / 2 + (r₁ p * Real.cos φ / 2) ^ 2) ≤ -(1 - κ) * S / 4 + 1 / 2 := by
      have hU : ∑ p ∈ jasPrimesUpTo N,
          ((r₁ p + r₂ p) * Real.cos (φ + Δ * Real.log p) + (r₁ p - r₂ p) ^ 2 / (2 * m)) / 2 ≤
          κ * S / 2 + ε * S / 2 + ε * S / (4 * m) := by
        calc _ ≤ ∑ p ∈ jasPrimesUpTo N, (r₁ p * Real.cos (φ + Δ * Real.log p) / 2 + r₂ p / 2 +
              r₁ p ^ 2 / (4 * m)) := Finset.sum_le_sum fun p _ => hu p
          _ = (∑ p ∈ jasPrimesUpTo N, r₁ p * Real.cos (φ + Δ * Real.log p)) / 2 +
              (∑ p ∈ jasPrimesUpTo N, r₂ p) / 2 + (∑ p ∈ jasPrimesUpTo N, r₁ p ^ 2) / (4 * m) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div,
                Finset.sum_div]
          _ ≤ κ * S / 2 + ε * S / 2 + ε * S / (4 * m) := by
              rw [hsumr₂, hsumsq]
              gcongr
      have hV : ∑ p ∈ jasPrimesUpTo N, r₁ p * Real.cos φ / 2 = Real.cos φ * S / 2 := by
        rw [← hsumr₁, Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun p _ => by ring
      have hV2 : ∑ p ∈ jasPrimesUpTo N, (r₁ p * Real.cos φ / 2) ^ 2 ≤ ε * S / 4 := by
        calc _ ≤ ∑ p ∈ jasPrimesUpTo N, r₁ p ^ 2 / 4 := Finset.sum_le_sum fun p _ => hv2 p
          _ = jasPrimeRpowSum (2 * α) N / 4 := by rw [← Finset.sum_div, hsumsq]
          _ ≤ ε * S / 4 := by linarith
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hV]
      have hεm : ε * S / 2 + ε * S / (4 * m) + ε * S / 4 ≤ (1 - κ) * S / 4 := by
        have : ε * (3 + 1 / m) = 1 - κ := by rw [hε]; field_simp
        have e : ε * S / 2 + ε * S / (4 * m) + ε * S / 4 = ε * (3 + 1 / m) * S / 4 := by
          field_simp; ring
        rw [e, this]
      linarith
    have hlog : -(1 - κ) * S / 4 + 1 / 2 ≤ Real.log η := by
      have hk : 0 < 1 - κ := by linarith
      rw [div_le_iff₀ hk] at hSη
      have := neg_abs_le (Real.log η)
      linarith
    calc Real.exp _ ≤ Real.exp (Real.log η) := Real.exp_le_exp.mpr (hexp.trans hlog)
      _ = η := Real.exp_log hη

/-! ## The dominant zero -/

/-- Gap constant `1 - 2^{-(1 - 2β)}`. -/
def jasGap (ρ : ℂ) : ℝ := 1 - Real.exp (-(1 - 2 * ρ.re) * Real.log 2)

/-- Lower bound `2 - 2·2^{-(β+c)}` for `2 - r₁ - r₂`. -/
def jasMargin (ρ : ℂ) (c : ℝ) : ℝ := 2 - 2 * Real.exp (-(ρ.re + c) * Real.log 2)

theorem log_two_le_log_prime (p : Nat.Primes) : Real.log 2 ≤ Real.log p :=
  Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)

theorem jasGap_pos {ρ : ℂ} (hβ : ρ.re < 1 / 2) : 0 < jasGap ρ := by
  have : Real.exp (-(1 - 2 * ρ.re) * Real.log 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)])
  rw [jasGap]; linarith

theorem jasMargin_pos {ρ : ℂ} {c : ℝ} (hα : 0 < ρ.re + c) : 0 < jasMargin ρ c := by
  have : Real.exp (-(ρ.re + c) * Real.log 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)])
  rw [jasMargin]; linarith

theorem jasR1_dressed_lt_one {ρ : ℂ} {c : ℝ} (hα : 0 < ρ.re + c) (p : Nat.Primes) :
    jasR1 (ρ + c) p < 1 := by
  rw [jasR1_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]

theorem jasR2_dressed_le_jasR1 {ρ : ℂ} {c : ℝ} (hβ : ρ.re ≤ 1 / 2) (p : Nat.Primes) :
    jasR2 (ρ - c) p ≤ jasR1 (ρ + c) p := by
  rw [jasR1_dressed, jasR2_dressed]; exact Real.exp_le_exp.mpr (by nlinarith [log_prime_pos p])

theorem jasGap_mul_le {ρ : ℂ} (hβ : ρ.re < 1 / 2) (c : ℝ) (p : Nat.Primes) :
    jasGap ρ * jasR1 (ρ + c) p ≤ jasR1 (ρ + c) p - jasR2 (ρ - c) p := by
  have hsplit : jasR2 (ρ - c) p = jasR1 (ρ + c) p * Real.exp (-(1 - 2 * ρ.re) * Real.log p) := by
    rw [jasR1_dressed, jasR2_dressed, ← Real.exp_add]; congr 1; ring
  have hle : Real.exp (-(1 - 2 * ρ.re) * Real.log p) ≤ Real.exp (-(1 - 2 * ρ.re) * Real.log 2) :=
    Real.exp_le_exp.mpr (by nlinarith [log_two_le_log_prime p])
  have h0 : 0 ≤ jasR1 (ρ + c) p := by rw [jasR1_dressed]; exact (Real.exp_pos _).le
  rw [hsplit, jasGap]
  nlinarith

theorem jasMargin_le {ρ : ℂ} {c : ℝ} (hβ : ρ.re ≤ 1 / 2) (hα : 0 ≤ ρ.re + c) (p : Nat.Primes) :
    jasMargin ρ c ≤ 2 - jasR1 (ρ + c) p - jasR2 (ρ - c) p := by
  have h1 : jasR1 (ρ + c) p ≤ Real.exp (-(ρ.re + c) * Real.log 2) := by
    rw [jasR1_dressed]
    have := log_two_le_log_prime p
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h2 := jasR2_dressed_le_jasR1 (c := c) hβ p
  rw [jasMargin]; linarith

theorem jasPrimeRpowSum_dressed (ρ : ℂ) (c : ℝ) (N : ℕ) :
    jasPrimeRpowSum (ρ.re + c) N = ∑ p ∈ jasPrimesUpTo N, jasR1 (ρ + c) p :=
  Finset.sum_congr rfl fun p _ => (jasR1_dressed ρ c p).symm

theorem jasGap_mul_sum_le {ρ : ℂ} (hβ : ρ.re < 1 / 2) (c : ℝ) (N : ℕ) :
    jasGap ρ * jasPrimeRpowSum (ρ.re + c) N ≤
      ∑ p ∈ jasPrimesUpTo N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) := by
  rw [jasPrimeRpowSum_dressed, Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ => jasGap_mul_le hβ c p

/-- A competitor zero is eventually negligible at the twisted Kronecker points of `ρ`. -/
theorem eventually_jasCompetitor_le {ρ q : ℂ} {c η : ℝ} (hβ0 : 0 < ρ.re) (hβ : ρ.re < 1 / 2)
    (hc0 : 0 ≤ c) (hα1 : ρ.re + c < 1) (hη : 0 < η) (hq : |q.re - 1 / 2| ≤ 1 / 2 - ρ.re)
    (hqD : ¬ (q.im = ρ.im ∧ |q.re - 1 / 2| = 1 / 2 - ρ.re)) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      jasGap ρ * jasPrimeRpowSum (ρ.re + c) N ≤
        ∑ p ∈ jasPrimesUpTo N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) →
      Real.sin φ * ∑ p ∈ jasPrimesUpTo N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesUpTo N, jasDressedBernoulli q c p (jasTwistedPoint ρ φ p)‖ ≤
        η * ‖∏ p ∈ jasPrimesUpTo N,
          jasTwistedValue (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) φ‖ := by
  have hα0 : 0 < ρ.re + c := by linarith
  have hr₁ : ∀ p, jasR1 (ρ + c) p = Real.exp (-(ρ.re + c) * Real.log p) := jasR1_dressed ρ c
  have hR1 : ∀ p, 0 ≤ jasR1 (q + c) p := fun p => by rw [jasR1_dressed]; exact (Real.exp_pos _).le
  have hR2 : ∀ p, 0 ≤ jasR2 (q - c) p := fun p => by rw [jasR2_dressed]; exact (Real.exp_pos _).le
  have hr₂0 : ∀ p, 0 ≤ jasR2 (ρ - c) p := fun p => by
    rw [jasR2_dressed]; exact (Real.exp_pos _).le
  rcases lt_or_eq_of_le hq with hlt | heq
  · refine eventually_jasHead_le_of_lt hα0 hα1 (α' := 1 / 2 - |q.re - 1 / 2| + c) (by linarith)
      (jasGap_pos hβ) hη hr₁ hr₂0 _ fun φ p => ?_
    rw [jasDressedBernoulli_twisted_general]
    refine (norm_jasTwistedValue_le_add (hR1 p) (hR2 p) _).trans ?_
    have := jasR1_add_jasR2_le_two_mul q c p
    linarith
  · have him : q.im ≠ ρ.im := fun h => hqD ⟨h, heq⟩
    have hr₂ : ∀ p, jasR2 (ρ - c) p = Real.exp (-(1 - ρ.re + c) * Real.log p) := jasR2_dressed ρ c
    refine eventually_jasHead_le_of_twist hα0 hα1 (by linarith) (Δ := ρ.im - q.im)
      (sub_ne_zero.mpr (Ne.symm him)) (jasGap_pos hβ) (jasMargin_pos hα0) hη hr₁ hr₂ _
      fun φ p => ?_
    rw [jasDressedBernoulli_twisted_general]
    have hm := jasMargin_le (c := c) hβ.le hα0.le p
    have hr₁0 : 0 ≤ jasR1 (ρ + c) p := by rw [hr₁]; exact (Real.exp_pos _).le
    rcases (abs_eq (by linarith : (0 : ℝ) ≤ 1 / 2 - ρ.re)).mp heq with h | h
    · have e1 : jasR1 (q + c) p = jasR2 (ρ - c) p := by
        rw [jasR1_dressed, jasR2_dressed]; congr 2; linarith
      have e2 : jasR2 (q - c) p = jasR1 (ρ + c) p := by
        rw [jasR1_dressed, jasR2_dressed]; congr 2; linarith
      rw [e1, e2]
      have := norm_jasTwistedValue_le_cos (r₁ := jasR2 (ρ - c) p) (r₂ := jasR1 (ρ + c) p)
        (hr₂0 p) hr₁0 (jasMargin_pos hα0) (by linarith) (φ + (ρ.im - q.im) * Real.log p)
      rw [add_comm (jasR2 (ρ - c) p), show (jasR2 (ρ - c) p - jasR1 (ρ + c) p) ^ 2 =
        (jasR1 (ρ + c) p - jasR2 (ρ - c) p) ^ 2 by ring] at this
      exact this
    · have e1 : jasR1 (q + c) p = jasR1 (ρ + c) p := by
        rw [jasR1_dressed, jasR1_dressed]; congr 2; linarith
      have e2 : jasR2 (q - c) p = jasR2 (ρ - c) p := by
        rw [jasR2_dressed, jasR2_dressed]; congr 2; linarith
      rw [e1, e2]
      exact norm_jasTwistedValue_le_cos hr₁0 (hr₂0 p) (jasMargin_pos hα0) hm _

/-- The zeros outside a finite set are bounded by `∏ (2 + r₁ + r₂) ≤ 2 |G|` eventually. -/
theorem eventually_jasTail_le {ρ : ℂ} {c : ℝ} (hβ : ρ.re < 1 / 2) (hα1 : ρ.re + c < 1) :
    ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ → φ ≤ Real.pi / 2 →
      Real.sin φ * ∑ p ∈ jasPrimesUpTo N, (jasR1 (ρ + c) p - jasR2 (ρ - c) p) ≤ 8 * Real.pi →
      ∏ p ∈ jasPrimesUpTo N, (2 + (jasR1 (ρ + c) p + jasR2 (ρ - c) p)) ≤
        2 * ‖∏ p ∈ jasPrimesUpTo N, jasTwistedValue (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) φ‖ := by
  have hg := jasGap_pos hβ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [(tendsto_jasPrimeRpowSum_atTop hα1.le).eventually_ge_atTop
    (max 1 (64 * Real.pi ^ 2 / (jasGap ρ ^ 2 * Real.log 2)))] with N hN
  intro φ h0 h1 hsin
  have hS0 : 0 < jasPrimeRpowSum (ρ.re + c) N := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hN)
  have hc0' : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩
  have hcos := one_sub_cos_mul_le h0 h1 hg hS0 (jasGap_mul_sum_le hβ c N) hsin
  have hr₁0 : ∀ p, 0 ≤ jasR1 (ρ + c) p := fun p => by rw [jasR1_dressed]; exact (Real.exp_pos _).le
  have hr₂0 : ∀ p, 0 ≤ jasR2 (ρ - c) p := fun p => by rw [jasR2_dressed]; exact (Real.exp_pos _).le
  refine (prod_two_add_le_exp_mul_norm_prod _ _ (fun p => jasR1 (ρ + c) p + jasR2 (ρ - c) p) hc0'
    (fun p _ => by linarith [hr₁0 p, hr₂0 p])
    (fun p _ => two_add_mul_cos_le_norm_jasTwistedValue _ _ _)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hsum : ∑ p ∈ jasPrimesUpTo N, (jasR1 (ρ + c) p + jasR2 (ρ - c) p) * (1 - Real.cos φ) / 2 ≤
      (1 - Real.cos φ) * jasPrimeRpowSum (ρ.re + c) N := by
    have hc1 := Real.cos_le_one φ
    calc _ ≤ ∑ p ∈ jasPrimesUpTo N, jasR1 (ρ + c) p * (1 - Real.cos φ) :=
          Finset.sum_le_sum fun p _ => by
            have := jasR2_dressed_le_jasR1 (c := c) hβ.le p
            nlinarith [hr₂0 p]
      _ = (1 - Real.cos φ) * jasPrimeRpowSum (ρ.re + c) N := by
          rw [jasPrimeRpowSum_dressed, ← Finset.sum_mul, mul_comm]
  have hlg : (1 - Real.cos φ) * jasPrimeRpowSum (ρ.re + c) N ≤ Real.log 2 := by
    refine hcos.trans ?_
    have hS' : 64 * Real.pi ^ 2 / (jasGap ρ ^ 2 * Real.log 2) ≤ jasPrimeRpowSum (ρ.re + c) N :=
      (le_max_right _ _).trans hN
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hS'
    linarith
  calc Real.exp _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (hsum.trans hlg)
    _ = 2 := Real.exp_log (by norm_num)

theorem re_mul_prod_eq_neg_of_sum_arg {P : Finset Nat.Primes} {f : Nat.Primes → ℂ} {w : ℂ}
    (h : ∑ p ∈ P, (f p).arg = Real.pi - w.arg) :
    (w * ∏ p ∈ P, f p).re = -(‖w‖ * ‖∏ p ∈ P, f p‖) := by
  rw [norm_prod, prod_eq_prod_norm_mul_exp_sum_arg, h]
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I w]
  have e : (‖w‖ : ℂ) * cexp ((w.arg : ℂ) * I) *
      (((∏ p ∈ P, ‖f p‖ : ℝ) : ℂ) * cexp (((Real.pi - w.arg : ℝ) : ℂ) * I)) =
      -(((‖w‖ * ∏ p ∈ P, ‖f p‖ : ℝ)) : ℂ) := by
    rw [mul_mul_mul_comm, ← Complex.exp_add,
      show (w.arg : ℂ) * I + ((Real.pi - w.arg : ℝ) : ℂ) * I = (Real.pi : ℂ) * I by
        push_cast; ring, Complex.exp_pi_mul_I]
    push_cast
    ring
  rw [e, Complex.neg_re, Complex.ofReal_re]

/-- The dominant pair: a zero at the height of `ρ` and at the same distance from the line
contributes `Re(G/(ρ(1-ρ)))`. -/
theorem re_jasDominant_term {ρ q : ℂ} {c φ : ℝ} (P : Finset Nat.Primes) (him : q.im = ρ.im)
    (habs : |q.re - 1 / 2| = |ρ.re - 1 / 2|) :
    ((∏ p ∈ P, jasDressedBernoulli q c p (jasTwistedPoint ρ φ p)) / (q * (1 - q))).re =
      (1 / (ρ * (1 - ρ)) *
        ∏ p ∈ P, jasTwistedValue (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) φ).re := by
  rcases abs_eq_abs.mp habs with h | h
  · have hq : q = ρ := Complex.ext (by linarith) him
    subst hq
    rw [Finset.prod_congr rfl fun p _ => jasDressedBernoulli_twisted q c φ p, one_div_mul_eq_div]
  · have hq : q = 1 - conj ρ := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
      · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; rw [him]; ring
    have hX : ∀ p, jasDressedBernoulli q c p (jasTwistedPoint ρ φ p) =
        conj (jasTwistedValue (jasR1 (ρ + c) p) (jasR2 (ρ - c) p) φ) := by
      intro p
      rw [jasDressedBernoulli_twisted_general, ← jasTwistedValue_swap, him, sub_self, zero_mul,
        add_zero]
      have e1 : jasR1 (q + c) p = jasR2 (ρ - c) p := by
        rw [jasR1_dressed, jasR2_dressed]; congr 2; linarith
      have e2 : jasR2 (q - c) p = jasR1 (ρ + c) p := by
        rw [jasR1_dressed, jasR2_dressed]; congr 2; linarith
      rw [e1, e2]
    rw [Finset.prod_congr rfl fun p _ => hX p, ← map_prod, hq]
    have e : (1 - conj ρ) * (1 - (1 - conj ρ)) = conj (ρ * (1 - ρ)) := by
      simp only [map_mul, map_sub, map_one]; ring
    rw [e, ← map_div₀, Complex.conj_re, one_div_mul_eq_div]

/-- Every zero no farther from the line than `ρ` has Bernoulli product at most
`∏ (2 + r₁ + r₂)`. -/
theorem norm_prod_jasDressedBernoulli_le {ρ q : ℂ} {c φ : ℝ} (P : Finset Nat.Primes)
    (hq : |q.re - 1 / 2| ≤ |ρ.re - 1 / 2|) :
    ‖∏ p ∈ P, jasDressedBernoulli q c p (jasTwistedPoint ρ φ p)‖ ≤
      ∏ p ∈ P, (2 + (jasR1 (ρ + c) p + jasR2 (ρ - c) p)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
  rw [jasDressedBernoulli_twisted_general]
  refine (norm_jasTwistedValue_le_add (by rw [jasR1_dressed]; exact (Real.exp_pos _).le)
    (by rw [jasR2_dressed]; exact (Real.exp_pos _).le) _).trans ?_
  have := jasR1_add_jasR2_le_of_abs_le hq c p
  linarith

/-- Assembly: a dominant negative part beats a small finite remainder and a small tail. -/
theorem re_tsum_neg_of_dominant {ι : Type*} {term : ι → ℂ} (hsumm : Summable term)
    (F : Finset ι) (D : ι → Prop) [DecidablePred D] {A : ℝ} (hA : 0 < A)
    (hD : (∑ i ∈ F.filter D, term i).re ≤ -A)
    (hH : ‖∑ i ∈ F.filter (fun i => ¬ D i), term i‖ ≤ A / 4)
    (htail : ‖∑' i : {x // x ∉ F}, term i‖ ≤ A / 4) : (∑' i, term i).re < 0 := by
  rw [← hsumm.sum_add_tsum_subtype_compl F, ← Finset.sum_filter_add_sum_filter_not F D,
    Complex.add_re, Complex.add_re]
  have h1 := Complex.re_le_norm (∑ i ∈ F.filter (fun i => ¬ D i), term i)
  have h2 := Complex.re_le_norm (∑' i : {x // x ∉ F}, term i)
  linarith

/-- **Maximal off-line zero, `β₀ < 1/2`.** -/
theorem not_jasDressedPSD_of_maximal_offLine_of_lt (q₀ : XiZeroCopy) (hβ : (q₀.1 : ℂ).re < 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasDressedPSD σ := by
  classical
  intro hPSD
  have hβ0 : 0 < (q₀.1 : ℂ).re := (xi_divisor_support_re_mem_open_unit q₀.1).1
  have habs : |(q₀.1 : ℂ).re - 1 / 2| = 1 / 2 - (q₀.1 : ℂ).re := by
    rw [abs_of_neg (by linarith)]; ring
  rw [habs] at hσ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max σ (1 / 2) - 1 / 2 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; linarith [le_max_right σ (1 / 2)]
  have hα1 : (q₀.1 : ℂ).re + c < 1 := by
    have : max σ (1 / 2) < 1 + (1 / 2 - (q₀.1 : ℂ).re) := max_lt hσ (by linarith)
    rw [hc]; linarith
  have hα0 : 0 < (q₀.1 : ℂ).re + c := by linarith
  have hPSD' : JasDressedPSD (1 / 2 + c) :=
    hPSD.mono (by rw [hc]; linarith [le_max_left σ (1 / 2)])
  have hρ0 : (q₀.1 : ℂ) ≠ 0 := fun h => by rw [h] at hβ0; simp at hβ0
  have hρ1 : 1 - (q₀.1 : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨w₀, hw₀⟩ : ∃ w : ℂ, w = 1 / ((q₀.1 : ℂ) * (1 - (q₀.1 : ℂ))) := ⟨_, rfl⟩
  have hw₀n : 0 < ‖w₀‖ :=
    norm_pos_iff.mpr (by rw [hw₀]; exact one_div_ne_zero (mul_ne_zero hρ0 hρ1))
  obtain ⟨wq, hwq⟩ : ∃ wq : XiZeroCopy → ℝ,
      wq = fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := ⟨_, rfl⟩
  have hwq0 : ∀ q, 0 ≤ wq q := fun q => by rw [hwq]; exact norm_nonneg _
  have hwsum : Summable wq := by rw [hwq]; exact summable_inv_mul_one_sub.norm
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q, wq q := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact tsum_nonneg hwq0
  have hη0 : 0 < ‖w₀‖ / (4 * (W + 1)) := by positivity
  obtain ⟨F, hFtail, hq₀F⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, wq q) < ‖w₀‖ / 8 ∧ q₀ ∈ F := by
    have h1 := (tendsto_tsum_compl_atTop_zero wq).eventually
      (gt_mem_nhds (show (0 : ℝ) < ‖w₀‖ / 8 by positivity))
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, {q₀} ⊆ F := eventually_ge_atTop {q₀}
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    exact ⟨F, hF1, hF2 (Finset.mem_singleton_self q₀)⟩
  let D : XiZeroCopy → Prop := fun q =>
    (q.1 : ℂ).im = (q₀.1 : ℂ).im ∧ |(q.1 : ℂ).re - 1 / 2| = 1 / 2 - (q₀.1 : ℂ).re
  have hhead : ∀ q ∈ F.filter (fun q => ¬ D q), ∀ᶠ N in atTop, ∀ φ : ℝ, 0 ≤ φ →
      φ ≤ Real.pi / 2 →
      jasGap (q₀.1 : ℂ) * jasPrimeRpowSum ((q₀.1 : ℂ).re + c) N ≤
        ∑ p ∈ jasPrimesUpTo N, (jasR1 ((q₀.1 : ℂ) + c) p - jasR2 ((q₀.1 : ℂ) - c) p) →
      Real.sin φ * ∑ p ∈ jasPrimesUpTo N,
          (jasR1 ((q₀.1 : ℂ) + c) p - jasR2 ((q₀.1 : ℂ) - c) p) ≤ 8 * Real.pi →
      ‖∏ p ∈ jasPrimesUpTo N, jasDressedBernoulli (q.1 : ℂ) c p (jasTwistedPoint (q₀.1 : ℂ) φ p)‖ ≤
        ‖w₀‖ / (4 * (W + 1)) * ‖∏ p ∈ jasPrimesUpTo N,
          jasTwistedValue (jasR1 ((q₀.1 : ℂ) + c) p) (jasR2 ((q₀.1 : ℂ) - c) p) φ‖ :=
    fun q hq => eventually_jasCompetitor_le hβ0 hβ hc0 hα1 hη0 (habs ▸ hmax q)
      (Finset.mem_filter.mp hq).2
  obtain ⟨N, hNhead, hNtail, hNsize⟩ :=
    (((Filter.eventually_all_finset _).mpr hhead).and ((eventually_jasTail_le hβ hα1).and
      ((tendsto_jasPrimeRpowSum_atTop hα1.le).eventually_ge_atTop
        (8 * Real.pi / jasGap (q₀.1 : ℂ))))).exists
  have hTN := jasGap_mul_sum_le hβ c N
  have hgN : 8 * Real.pi ≤ jasGap (q₀.1 : ℂ) * jasPrimeRpowSum ((q₀.1 : ℂ).re + c) N := by
    rw [div_le_iff₀ (jasGap_pos hβ)] at hNsize; linarith
  have hθ0 : 0 ≤ Real.pi - w₀.arg := by linarith [Complex.arg_le_pi w₀]
  have hθ2 : Real.pi - w₀.arg < 2 * Real.pi := by linarith [Complex.neg_pi_lt_arg w₀]
  obtain ⟨φ, hφ0, hφ1, hΘ, hsinθ⟩ := exists_jasTwist (P := jasPrimesUpTo N)
    (r₁ := fun p => jasR1 ((q₀.1 : ℂ) + c) p) (r₂ := fun p => jasR2 ((q₀.1 : ℂ) - c) p)
    (fun p => by rw [jasR2_dressed]; exact (Real.exp_pos _).le)
    (fun p => jasR2_dressed_le_jasR1 hβ.le p) (fun p => jasR1_dressed_lt_one hα0 p) hθ0
    (by linarith)
  have hsin8 : Real.sin φ * ∑ p ∈ jasPrimesUpTo N,
      (jasR1 ((q₀.1 : ℂ) + c) p - jasR2 ((q₀.1 : ℂ) - c) p) ≤ 8 * Real.pi := by linarith
  -- the Bernoulli test at the twisted Kronecker point
  have hB := jasBernoulliAggregate_nonneg hPSD' (jasPrimesUpTo N) (jasTwistedPoint (q₀.1 : ℂ) φ)
  rw [show (1 / 2 + c - 1 / 2 : ℝ) = c by ring] at hB
  obtain ⟨T, hT⟩ : ∃ T : XiZeroCopy → ℂ, T = fun q =>
      (∏ p ∈ jasPrimesUpTo N, jasDressedBernoulli (q.1 : ℂ) c p (jasTwistedPoint (q₀.1 : ℂ) φ p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := ⟨_, rfl⟩
  have hBT : 0 ≤ (∑' q, T q).re := by rw [hT]; exact hB
  obtain ⟨G, hG⟩ : ∃ G : ℂ, G = ∏ p ∈ jasPrimesUpTo N,
      jasTwistedValue (jasR1 ((q₀.1 : ℂ) + c) p) (jasR2 ((q₀.1 : ℂ) - c) p) φ := ⟨_, rfl⟩
  have hG0 : 0 < ‖G‖ := by
    rw [hG]
    refine norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun p _ => fun h0 => ?_)
    have hr1 : 0 ≤ jasR1 ((q₀.1 : ℂ) + c) p := by rw [jasR1_dressed]; exact (Real.exp_pos _).le
    have hr2 : 0 ≤ jasR2 ((q₀.1 : ℂ) - c) p := by rw [jasR2_dressed]; exact (Real.exp_pos _).le
    have := re_jasTwistedValue_pos hr1 (jasR1_dressed_lt_one hα0 p) hr2
      ((jasR2_dressed_le_jasR1 (c := c) hβ.le p).trans_lt (jasR1_dressed_lt_one hα0 p)) φ
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have halign : (w₀ * G).re = -(‖w₀‖ * ‖G‖) := by
    rw [hG]; exact re_mul_prod_eq_neg_of_sum_arg hΘ
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = ∏ p ∈ jasPrimesUpTo N,
      (2 + (jasR1 ((q₀.1 : ℂ) + c) p + jasR2 ((q₀.1 : ℂ) - c) p)) := ⟨_, rfl⟩
  have hterm_norm : ∀ q : XiZeroCopy, ‖T q‖ ≤ Bd * wq q := by
    intro q
    rw [hT, hwq, hBd]
    simp only
    rw [div_eq_mul_one_div, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_prod_jasDressedBernoulli_le (ρ := (q₀.1 : ℂ))
      (q := (q.1 : ℂ)) (c := c) (φ := φ) (jasPrimesUpTo N) (hmax q)) (norm_nonneg _)
  have hsumm : Summable T := Summable.of_norm_bounded (hwsum.mul_left Bd) hterm_norm
  have hBG : Bd ≤ 2 * ‖G‖ := by rw [hBd, hG]; exact hNtail φ hφ0 hφ1 hsin8
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]
    refine Finset.prod_nonneg fun p _ => ?_
    have h1 : 0 ≤ jasR1 ((q₀.1 : ℂ) + c) p := by rw [jasR1_dressed]; exact (Real.exp_pos _).le
    have h2 : 0 ≤ jasR2 ((q₀.1 : ℂ) - c) p := by rw [jasR2_dressed]; exact (Real.exp_pos _).le
    linarith
  refine absurd hBT (not_le.mpr (re_tsum_neg_of_dominant hsumm F D (A := ‖w₀‖ * ‖G‖)
    (mul_pos hw₀n hG0) ?_ ?_ ?_))
  · -- the dominant pair
    have hDpart : ∀ q ∈ F.filter D, (T q).re = (w₀ * G).re := by
      intro q hq
      obtain ⟨him, habsq⟩ := (Finset.mem_filter.mp hq).2
      rw [hT]
      exact (re_jasDominant_term _ him (habsq.trans habs.symm)).trans (by rw [hw₀, hG])
    rw [Complex.re_sum, Finset.sum_congr rfl hDpart, Finset.sum_const, nsmul_eq_mul, halign]
    have hcard : (1 : ℝ) ≤ ((F.filter D).card : ℝ) := by
      have hq₀D : q₀ ∈ F.filter D := Finset.mem_filter.mpr ⟨hq₀F, show D q₀ from ⟨rfl, habs⟩⟩
      exact_mod_cast Finset.card_pos.mpr ⟨q₀, hq₀D⟩
    have : 0 ≤ ‖w₀‖ * ‖G‖ := by positivity
    nlinarith
  · -- the competitors in the finite set
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ q ∈ F.filter (fun q => ¬ D q), ‖T q‖ ≤ wq q * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) := by
      intro q hq
      have h1 := hNhead q hq φ hφ0 hφ1 hTN hsin8
      rw [← hG] at h1
      rw [hT, hwq]
      simp only
      rw [div_eq_mul_one_div, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    calc ∑ q ∈ F.filter (fun q => ¬ D q), ‖T q‖
        ≤ ∑ q ∈ F.filter (fun q => ¬ D q), wq q * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) :=
          Finset.sum_le_sum hle
      _ = (∑ q ∈ F.filter (fun q => ¬ D q), wq q) * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) := by
          rw [Finset.sum_mul]
      _ ≤ W * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) := by
          gcongr
          rw [hW]
          exact hwsum.sum_le_tsum _ fun q _ => hwq0 q
      _ ≤ ‖w₀‖ * ‖G‖ / 4 := by
          have : W / (W + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
          calc W * (‖w₀‖ / (4 * (W + 1)) * ‖G‖) = W / (W + 1) * (‖w₀‖ * ‖G‖ / 4) := by
                field_simp
            _ ≤ 1 * (‖w₀‖ * ‖G‖ / 4) := by gcongr
            _ = ‖w₀‖ * ‖G‖ / 4 := one_mul _
  · -- the tail
    have hs1 : Summable (fun q : {x // x ∉ F} => ‖T q‖) := hsumm.norm.subtype _
    have hs2 : Summable (fun q : {x // x ∉ F} => Bd * wq q) := (hwsum.mul_left Bd).subtype _
    calc ‖∑' q : {x // x ∉ F}, T q‖ ≤ ∑' q : {x // x ∉ F}, ‖T q‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : {x // x ∉ F}, Bd * wq q := Summable.tsum_le_tsum (fun q => hterm_norm q) hs1 hs2
      _ = Bd * ∑' q : {x // x ∉ F}, wq q := tsum_mul_left
      _ ≤ (2 * ‖G‖) * (‖w₀‖ / 8) :=
          mul_le_mul hBG hFtail.le (tsum_nonneg fun q => hwq0 q) (by positivity)
      _ = ‖w₀‖ * ‖G‖ / 4 := by ring

/-- **A maximal off-line zero excludes JAS positivity below `σ = 1 + δ`.**  If a Xi zero `ρ₀` off
the critical line maximizes `|Re ρ - 1/2|` over all Xi zeros, then the dressed aggregate is not
positive semidefinite for any `σ < 1 + |Re ρ₀ - 1/2|`. -/
theorem not_jasDressedPSD_of_maximal_offLine (q₀ : XiZeroCopy) (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) : ¬ JasDressedPSD σ := by
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · exact not_jasDressedPSD_of_maximal_offLine_of_lt q₀ hlt hmax hσ
  · have hval : (((xiZeroCopyReflectEquiv q₀).1 : ℂ)) = 1 - (q₀.1 : ℂ) := rfl
    have habs : |((xiZeroCopyReflectEquiv q₀).1 : ℂ).re - 1 / 2| = |(q₀.1 : ℂ).re - 1 / 2| := by
      rw [hval, Complex.sub_re, Complex.one_re, show 1 - (q₀.1 : ℂ).re - 1 / 2 =
        -((q₀.1 : ℂ).re - 1 / 2) by ring, abs_neg]
    exact not_jasDressedPSD_of_maximal_offLine_of_lt (xiZeroCopyReflectEquiv q₀)
      (by rw [hval, Complex.sub_re, Complex.one_re]; linarith) (fun q => habs ▸ hmax q)
      (habs ▸ hσ)

/-- **JAS positivity forbids a largest off-line distance.**  If the dressed aggregate is positive
semidefinite at `σ`, then every off-line Xi zero at distance greater than `σ - 1` from the
critical line is strictly exceeded in distance by another Xi zero. -/
theorem exists_farther_zero_of_jasDressedPSD {σ : ℝ} (h : JasDressedPSD σ) (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2) (hfar : σ - 1 < |(q₀.1 : ℂ).re - 1 / 2|) :
    ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| := by
  by_contra hno
  push Not at hno
  exact not_jasDressedPSD_of_maximal_offLine q₀ hoff hno (by linarith) h

end

end RHTower
