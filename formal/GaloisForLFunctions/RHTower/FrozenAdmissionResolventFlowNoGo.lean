import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The three-atom positive resolvent flow and frozen-admission source sign

A positive resolvent flow is the moment functional

```text
L_{t,ε}(f) = x₁ f(x₁) + ε (x₂ f(x₂) + x₃ f(x₃)),   x_i = (t + d_i)⁻¹,
```

whose moments obey the exact shifted-moment law `s'(k) = -(k+1) s(k+1)` and whose degree-two
Hankel block is positive definite for all positive parameters.  The odd current
`J_t(A) = L_t(A X A)` has derivative `-Q_t(A)` with the adaptive source
`Q_t(A) = 2 L_t((XA) X (X A' + A))`.

For a degree-one admission `A = X - α` the source is positive at the *current* canonical
admission `α = s(1)/s(0)` and strictly negative at a *frozen* canonical admission taken from a
nearby mass.  Finite positivity, canonical admission and the exact moment flow therefore do not
control the frozen-admission source sign.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- One node of the resolvent flow. -/
def farNode (d t : ℝ) : ℝ := (t + d)⁻¹

/-- The three-atom positive resolvent-flow functional. -/
def farFunctional (d₁ d₂ d₃ ε t : ℝ) (f : ℝ → ℝ) : ℝ :=
  farNode d₁ t * f (farNode d₁ t)
    + ε * (farNode d₂ t * f (farNode d₂ t) + farNode d₃ t * f (farNode d₃ t))

/-- The moments of the flow. -/
def farMoment (d₁ d₂ d₃ ε t : ℝ) (k : ℕ) : ℝ :=
  farFunctional d₁ d₂ d₃ ε t (fun x => x ^ k)

theorem farNode_pos {d t : ℝ} (hd : 0 < d) (ht : 0 < t) : 0 < farNode d t := by
  rw [farNode]
  positivity

theorem farMoment_eq (d₁ d₂ d₃ ε t : ℝ) (k : ℕ) :
    farMoment d₁ d₂ d₃ ε t k
      = farNode d₁ t ^ (k + 1)
        + ε * (farNode d₂ t ^ (k + 1) + farNode d₃ t ^ (k + 1)) := by
  rw [farMoment, farFunctional]
  ring

/-! ## The exact shifted-moment law -/

theorem hasDerivAt_farNode_pow {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => farNode d s ^ (n + 1))
      (-((n : ℝ) + 1) * farNode d t ^ (n + 2)) t := by
  have hne : t + d ≠ 0 := by positivity
  have hbase : HasDerivAt (fun s : ℝ => s + d) 1 t := (hasDerivAt_id t).add_const d
  have hinv : HasDerivAt (fun s : ℝ => (s + d)⁻¹) (-1 / (t + d) ^ 2) t := hbase.inv hne
  have hpow := hinv.pow (n + 1)
  have hval : ((n : ℕ) + 1 : ℝ) * (t + d)⁻¹ ^ (n + 1 - 1) * (-1 / (t + d) ^ 2)
      = -((n : ℝ) + 1) * ((t + d)⁻¹) ^ (n + 2) := by
    have hsimp : (n : ℕ) + 1 - 1 = n := by omega
    have hpow2 : ((t + d)⁻¹) ^ (n + 2) = ((t + d)⁻¹) ^ n * (1 / (t + d) ^ 2) := by
      rw [pow_add, one_div, ← inv_pow]
    rw [hsimp, hpow2]
    ring
  rw [farNode]
  push_cast at hpow hval ⊢
  rw [← hval]
  exact hpow

/-- **The exact shifted-moment law** `s'(k) = -(k+1) s(k+1)`. -/
theorem hasDerivAt_farMoment {d₁ d₂ d₃ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (ε : ℝ) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt (fun s : ℝ => farMoment d₁ d₂ d₃ ε s k)
      (-((k : ℝ) + 1) * farMoment d₁ d₂ d₃ ε t (k + 1)) t := by
  have h₁ := hasDerivAt_farNode_pow hd₁ ht k
  have h₂ := hasDerivAt_farNode_pow hd₂ ht k
  have h₃ := hasDerivAt_farNode_pow hd₃ ht k
  have hsum := (h₁.add ((h₂.add h₃).const_mul ε))
  have hfun : (fun s : ℝ => farMoment d₁ d₂ d₃ ε s k)
      = fun s : ℝ => farNode d₁ s ^ (k + 1)
          + ε * (farNode d₂ s ^ (k + 1) + farNode d₃ s ^ (k + 1)) := by
    funext s
    exact farMoment_eq d₁ d₂ d₃ ε s k
  rw [hfun]
  have hval : -((k : ℝ) + 1) * farMoment d₁ d₂ d₃ ε t (k + 1)
      = -((k : ℝ) + 1) * farNode d₁ t ^ (k + 2)
        + ε * (-((k : ℝ) + 1) * farNode d₂ t ^ (k + 2)
          + -((k : ℝ) + 1) * farNode d₃ t ^ (k + 2)) := by
    rw [farMoment_eq]
    ring
  rw [hval]
  exact hsum

/-! ## Strict positivity of the degree-two chamber -/

theorem farNode_injective {d d' t : ℝ} (h : farNode d t = farNode d' t) : d = d' := by
  rw [farNode, farNode, inv_eq_iff_eq_inv, inv_inv] at h
  linarith

/-- **Strict positivity of the whole degree-two Hankel chamber.**  A nonzero quadratic cannot
vanish at the three distinct nodes. -/
theorem farFunctional_sq_pos {d₁ d₂ d₃ ε t : ℝ} (hd₁ : 0 < t + d₁) (hd₂ : 0 < t + d₂)
    (hd₃ : 0 < t + d₃) (hε : 0 < ε) (h₁₂ : d₁ ≠ d₂) (h₁₃ : d₁ ≠ d₃) (h₂₃ : d₂ ≠ d₃)
    {c₀ c₁ c₂ : ℝ} (hc : ¬(c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0)) :
    0 < farFunctional d₁ d₂ d₃ ε t (fun x => (c₀ + c₁ * x + c₂ * x ^ 2) ^ 2) := by
  set x₁ := farNode d₁ t with hx₁
  set x₂ := farNode d₂ t with hx₂
  set x₃ := farNode d₃ t with hx₃
  have hx₁0 : 0 < x₁ := by rw [hx₁, farNode]; positivity
  have hx₂0 : 0 < x₂ := by rw [hx₂, farNode]; positivity
  have hx₃0 : 0 < x₃ := by rw [hx₃, farNode]; positivity
  have hne₁₂ : x₁ ≠ x₂ := fun h => h₁₂ (farNode_injective h)
  have hne₁₃ : x₁ ≠ x₃ := fun h => h₁₃ (farNode_injective h)
  have hne₂₃ : x₂ ≠ x₃ := fun h => h₂₃ (farNode_injective h)
  set q : ℝ → ℝ := fun x => c₀ + c₁ * x + c₂ * x ^ 2 with hq
  have h1 : 0 ≤ x₁ * q x₁ ^ 2 := by positivity
  have h2 : 0 ≤ x₂ * q x₂ ^ 2 := by positivity
  have h3 : 0 ≤ x₃ * q x₃ ^ 2 := by positivity
  have hnonneg : 0 ≤ farFunctional d₁ d₂ d₃ ε t (fun x => q x ^ 2) := by
    rw [farFunctional]
    have hεpos : 0 ≤ ε * (x₂ * q x₂ ^ 2 + x₃ * q x₃ ^ 2) := by positivity
    linarith
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · exfalso
    -- all three values vanish, hence the quadratic is zero
    rw [farFunctional] at hzero
    have hsum0 : x₁ * q x₁ ^ 2 + ε * (x₂ * q x₂ ^ 2 + x₃ * q x₃ ^ 2) = 0 := hzero.symm
    have hεnn : 0 ≤ ε * (x₂ * q x₂ ^ 2 + x₃ * q x₃ ^ 2) := by positivity
    have hsplit := (add_eq_zero_iff_of_nonneg h1 hεnn).mp hsum0
    have hz1 : x₁ * q x₁ ^ 2 = 0 := hsplit.1
    have htail : x₂ * q x₂ ^ 2 + x₃ * q x₃ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hsplit.2 with h | h
      · exact absurd h (ne_of_gt hε)
      · exact h
    have hsplit2 := (add_eq_zero_iff_of_nonneg h2 h3).mp htail
    have hz2 : x₂ * q x₂ ^ 2 = 0 := hsplit2.1
    have hz3 : x₃ * q x₃ ^ 2 = 0 := hsplit2.2
    have hq1 : q x₁ = 0 := by
      rcases mul_eq_zero.mp hz1 with h | h
      · exact absurd h (ne_of_gt hx₁0)
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hq2 : q x₂ = 0 := by
      rcases mul_eq_zero.mp hz2 with h | h
      · exact absurd h (ne_of_gt hx₂0)
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hq3 : q x₃ = 0 := by
      rcases mul_eq_zero.mp hz3 with h | h
      · exact absurd h (ne_of_gt hx₃0)
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [hq] at hq1 hq2 hq3
    have hd12 : (x₁ - x₂) * (c₁ + c₂ * (x₁ + x₂)) = 0 := by linear_combination hq1 - hq2
    have hd13 : (x₁ - x₃) * (c₁ + c₂ * (x₁ + x₃)) = 0 := by linear_combination hq1 - hq3
    have hs12 : c₁ + c₂ * (x₁ + x₂) = 0 := by
      rcases mul_eq_zero.mp hd12 with h | h
      · exact absurd (by linarith : x₁ = x₂) hne₁₂
      · exact h
    have hs13 : c₁ + c₂ * (x₁ + x₃) = 0 := by
      rcases mul_eq_zero.mp hd13 with h | h
      · exact absurd (by linarith : x₁ = x₃) hne₁₃
      · exact h
    have hc₂ : c₂ = 0 := by
      have hdiff : c₂ * (x₂ - x₃) = 0 := by linarith
      rcases mul_eq_zero.mp hdiff with h | h
      · exact h
      · exact absurd (by linarith : x₂ = x₃) hne₂₃
    have hc₁ : c₁ = 0 := by
      rw [hc₂] at hs12
      linarith
    have hc₀ : c₀ = 0 := by
      rw [hc₁, hc₂] at hq1
      linarith
    exact hc ⟨hc₀, hc₁, hc₂⟩
  · exact hpos

/-! ## Odd current, adaptive source, and canonical admission -/

/-- The odd current `J_t(X - α) = L_t((X-α) X (X-α))`. -/
def farOddCurrent (d₁ d₂ d₃ ε t α : ℝ) : ℝ :=
  farFunctional d₁ d₂ d₃ ε t (fun x => x * (x - α) ^ 2)

/-- The adaptive completed source `Q_t(X-α) = 2 L_t((X(X-α)) X (X + (X-α)))`. -/
def farSource (d₁ d₂ d₃ ε t α : ℝ) : ℝ :=
  2 * farFunctional d₁ d₂ d₃ ε t (fun x => x ^ 2 * (x - α) * (2 * x - α))

/-- The canonical degree-one admission coefficient `α = s(1)/s(0)`. -/
def farAlpha (d₁ d₂ d₃ ε t : ℝ) : ℝ :=
  farMoment d₁ d₂ d₃ ε t 1 / farMoment d₁ d₂ d₃ ε t 0

/-- The admitted norm `h₁ = L_t((X-α)²)`. -/
def farNorm (d₁ d₂ d₃ ε t α : ℝ) : ℝ :=
  farFunctional d₁ d₂ d₃ ε t (fun x => (x - α) ^ 2)

theorem farSource_eq (d₁ d₂ d₃ ε t α : ℝ) :
    farSource d₁ d₂ d₃ ε t α
      = 2 * (farNode d₁ t ^ 3 * (farNode d₁ t - α) * (2 * farNode d₁ t - α)
        + ε * (farNode d₂ t ^ 3 * (farNode d₂ t - α) * (2 * farNode d₂ t - α)
          + farNode d₃ t ^ 3 * (farNode d₃ t - α) * (2 * farNode d₃ t - α))) := by
  rw [farSource, farFunctional]
  ring

theorem farOddCurrent_eq (d₁ d₂ d₃ ε t α : ℝ) :
    farOddCurrent d₁ d₂ d₃ ε t α
      = farNode d₁ t ^ 2 * (farNode d₁ t - α) ^ 2
        + ε * (farNode d₂ t ^ 2 * (farNode d₂ t - α) ^ 2
          + farNode d₃ t ^ 2 * (farNode d₃ t - α) ^ 2) := by
  rw [farOddCurrent, farFunctional]
  ring

/-! ## The odd-current flow law -/

theorem hasDerivAt_farNode {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => farNode d s) (-(farNode d t ^ 2)) t := by
  have hne : t + d ≠ 0 := by positivity
  have hbase : HasDerivAt (fun s : ℝ => s + d) 1 t := (hasDerivAt_id t).add_const d
  have hinv : HasDerivAt (fun s : ℝ => (s + d)⁻¹) (-1 / (t + d) ^ 2) t := hbase.inv hne
  refine hinv.congr_deriv ?_
  rw [farNode, inv_pow, neg_div, one_div]

theorem hasDerivAt_farNodeCurrent {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) (α : ℝ) :
    HasDerivAt (fun s : ℝ => farNode d s ^ 2 * (farNode d s - α) ^ 2)
      (-(2 * farNode d t ^ 3 * (farNode d t - α) * (2 * farNode d t - α))) t := by
  have hu := hasDerivAt_farNode hd ht
  have h1 := hu.pow 2
  have h2 := (hu.sub_const α).pow 2
  refine (h1.mul h2).congr_deriv ?_
  simp only [Pi.pow_apply]
  push_cast
  ring

/-- **The odd-current flow law** `d/dt J_t(A) = -Q_t(A)` at a frozen admission `A = X - α`. -/
theorem hasDerivAt_farOddCurrent {d₁ d₂ d₃ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (ε : ℝ) {t : ℝ} (ht : 0 < t) (α : ℝ) :
    HasDerivAt (fun s : ℝ => farOddCurrent d₁ d₂ d₃ ε s α)
      (-farSource d₁ d₂ d₃ ε t α) t := by
  have h₁ := hasDerivAt_farNodeCurrent hd₁ ht α
  have h₂ := hasDerivAt_farNodeCurrent hd₂ ht α
  have h₃ := hasDerivAt_farNodeCurrent hd₃ ht α
  have hsum := h₁.add ((h₂.add h₃).const_mul ε)
  have hfun : (fun s : ℝ => farOddCurrent d₁ d₂ d₃ ε s α)
      = fun s : ℝ => farNode d₁ s ^ 2 * (farNode d₁ s - α) ^ 2
          + ε * (farNode d₂ s ^ 2 * (farNode d₂ s - α) ^ 2
            + farNode d₃ s ^ 2 * (farNode d₃ s - α) ^ 2) := by
    funext s
    exact farOddCurrent_eq d₁ d₂ d₃ ε s α
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [farSource_eq]
  ring

/-- **Transgression is the negative derivative of the odd-current difference** of two frozen
admissions. -/
theorem hasDerivAt_farOddCurrent_sub {d₁ d₂ d₃ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (ε : ℝ) {t : ℝ} (ht : 0 < t) (α β : ℝ) :
    HasDerivAt (fun s : ℝ => farOddCurrent d₁ d₂ d₃ ε s α - farOddCurrent d₁ d₂ d₃ ε s β)
      (-(farSource d₁ d₂ d₃ ε t α - farSource d₁ d₂ d₃ ε t β)) t := by
  refine ((hasDerivAt_farOddCurrent hd₁ hd₂ hd₃ ε ht α).sub
    (hasDerivAt_farOddCurrent hd₁ hd₂ hd₃ ε ht β)).congr_deriv ?_
  ring

/-! ## The exact affine displacement law -/

/-- **Admission mismatch is an affine odd-Jacobi displacement**, not a norm distance. -/
theorem farOddCurrent_sub_farOddCurrent_alpha (d₁ d₂ d₃ ε t α : ℝ)
    (hW : farMoment d₁ d₂ d₃ ε t 0 ≠ 0) :
    farOddCurrent d₁ d₂ d₃ ε t α - farOddCurrent d₁ d₂ d₃ ε t (farAlpha d₁ d₂ d₃ ε t)
      = 2 * farNorm d₁ d₂ d₃ ε t (farAlpha d₁ d₂ d₃ ε t) * (farAlpha d₁ d₂ d₃ ε t - α)
        + (farAlpha d₁ d₂ d₃ ε t - α) ^ 2 * farMoment d₁ d₂ d₃ ε t 1 := by
  simp only [farOddCurrent, farNorm, farAlpha, farMoment, farFunctional] at hW ⊢
  field_simp at hW ⊢
  ring

/-! ## Sign of the frozen source -/

theorem farAlpha_zero (d₁ d₂ d₃ a : ℝ) (ha : 0 < a) (hd₁ : 0 < d₁) :
    farAlpha d₁ d₂ d₃ 0 a = farNode d₁ a := by
  have hpos : 0 < farNode d₁ a := farNode_pos hd₁ ha
  have hne : farNode d₁ a ≠ 0 := ne_of_gt hpos
  simp only [farAlpha, farMoment, farFunctional, zero_mul, add_zero, pow_one, pow_zero, mul_one]
  rw [mul_div_assoc, div_self hne, mul_one]

/-- **The frozen-admission source is strictly negative** in the transgression window
`y + d₁ < 2(a + d₁)`, `0 < a < y`, at the degenerate weight `ε = 0`. -/
theorem farSource_frozen_neg_zero {d₁ d₂ d₃ a y : ℝ} (hd₁ : 0 < d₁) (ha : 0 < a) (hay : a < y)
    (hwindow : y + d₁ < 2 * (a + d₁)) :
    farSource d₁ d₂ d₃ 0 y (farNode d₁ a) < 0 := by
  have hy : 0 < y := lt_trans ha hay
  have hxy : 0 < farNode d₁ y := farNode_pos hd₁ hy
  have hxa : 0 < farNode d₁ a := farNode_pos hd₁ ha
  have hya : 0 < y + d₁ := by linarith
  have haa : 0 < a + d₁ := by linarith
  have hlt : farNode d₁ y < farNode d₁ a := by
    rw [farNode, farNode]
    exact (inv_lt_inv₀ hya haa).mpr (by linarith)
  have hgt : farNode d₁ a < 2 * farNode d₁ y := by
    rw [farNode, farNode]
    have hM : (0 : ℝ) < (a + d₁) * (y + d₁) := by positivity
    have h1 : (a + d₁)⁻¹ * ((a + d₁) * (y + d₁)) = y + d₁ := by field_simp
    have h2 : 2 * (y + d₁)⁻¹ * ((a + d₁) * (y + d₁)) = 2 * (a + d₁) := by
      field_simp
    have hstep : (a + d₁)⁻¹ * ((a + d₁) * (y + d₁))
        < 2 * (y + d₁)⁻¹ * ((a + d₁) * (y + d₁)) := by
      rw [h1, h2]
      exact hwindow
    exact lt_of_mul_lt_mul_right hstep hM.le
  rw [farSource_eq]
  simp only [zero_mul, add_zero]
  have hfac : farNode d₁ y - farNode d₁ a < 0 := by linarith
  have hfac2 : 0 < 2 * farNode d₁ y - farNode d₁ a := by linarith
  have hcube : 0 < farNode d₁ y ^ 3 := by positivity
  have hprod : farNode d₁ y ^ 3 * (farNode d₁ y - farNode d₁ a) < 0 :=
    mul_neg_of_pos_of_neg hcube hfac
  have hprod2 : farNode d₁ y ^ 3 * (farNode d₁ y - farNode d₁ a)
      * (2 * farNode d₁ y - farNode d₁ a) < 0 := mul_neg_of_neg_of_pos hprod hfac2
  linarith

/-! ## Sign of the current source -/

theorem farSource_current_pos {d₁ d₂ d₃ ε y : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hε : 0 < ε) (hy : 0 < y) (h₁₂ : d₁ ≠ d₂) :
    0 < farSource d₁ d₂ d₃ ε y (farAlpha d₁ d₂ d₃ ε y) := by
  set x₁ := farNode d₁ y with hx₁
  set x₂ := farNode d₂ y with hx₂
  set x₃ := farNode d₃ y with hx₃
  have hx₁0 : 0 < x₁ := farNode_pos hd₁ hy
  have hx₂0 : 0 < x₂ := farNode_pos hd₂ hy
  have hx₃0 : 0 < x₃ := farNode_pos hd₃ hy
  have hne₁₂ : x₁ ≠ x₂ := fun h => h₁₂ (farNode_injective h)
  set W : ℝ := x₁ + ε * (x₂ + x₃) with hWdef
  have hW0 : 0 < W := by rw [hWdef]; positivity
  have hmom0 : farMoment d₁ d₂ d₃ ε y 0 = W := by
    rw [farMoment, farFunctional, hWdef]
    ring
  have hmom1 : farMoment d₁ d₂ d₃ ε y 1 = x₁ ^ 2 + ε * (x₂ ^ 2 + x₃ ^ 2) := by
    rw [farMoment, farFunctional]
    ring
  set α : ℝ := farAlpha d₁ d₂ d₃ ε y with hα
  have hαW : α * W = x₁ ^ 2 + ε * (x₂ ^ 2 + x₃ ^ 2) := by
    rw [hα, farAlpha, hmom0, hmom1]
    field_simp
  -- split the source into the admitted square and the monotone pairing
  have hsplit : farSource d₁ d₂ d₃ ε y α
      = 2 * (x₁ ^ 3 * (x₁ - α) ^ 2 + ε * (x₂ ^ 3 * (x₂ - α) ^ 2 + x₃ ^ 3 * (x₃ - α) ^ 2))
        + 2 * (x₁ ^ 4 * (x₁ - α) + ε * (x₂ ^ 4 * (x₂ - α) + x₃ ^ 4 * (x₃ - α))) := by
    rw [farSource_eq]
    ring
  -- the monotone pairing is nonnegative
  have hpair : (x₁ ^ 4 * (x₁ - α) + ε * (x₂ ^ 4 * (x₂ - α) + x₃ ^ 4 * (x₃ - α))) * W
      = ε * (x₁ * x₂ * ((x₁ ^ 3 - x₂ ^ 3) * (x₁ - x₂)))
        + ε * (x₁ * x₃ * ((x₁ ^ 3 - x₃ ^ 3) * (x₁ - x₃)))
        + ε ^ 2 * (x₂ * x₃ * ((x₂ ^ 3 - x₃ ^ 3) * (x₂ - x₃))) := by
    rw [hWdef]
    linear_combination (-(x₁ ^ 4 + ε * (x₂ ^ 4 + x₃ ^ 4))) * hαW
  have hmono : ∀ u v : ℝ, 0 < u → 0 < v → 0 ≤ (u ^ 3 - v ^ 3) * (u - v) := by
    intro u v hu hv
    nlinarith [sq_nonneg (u - v), sq_nonneg (u + v), mul_pos hu hv]
  have hpairnn : 0 ≤ x₁ ^ 4 * (x₁ - α) + ε * (x₂ ^ 4 * (x₂ - α) + x₃ ^ 4 * (x₃ - α)) := by
    have h12 := hmono x₁ x₂ hx₁0 hx₂0
    have h13 := hmono x₁ x₃ hx₁0 hx₃0
    have h23 := hmono x₂ x₃ hx₂0 hx₃0
    have t1 : 0 ≤ ε * (x₁ * x₂ * ((x₁ ^ 3 - x₂ ^ 3) * (x₁ - x₂))) := by positivity
    have t2 : 0 ≤ ε * (x₁ * x₃ * ((x₁ ^ 3 - x₃ ^ 3) * (x₁ - x₃))) := by positivity
    have t3 : 0 ≤ ε ^ 2 * (x₂ * x₃ * ((x₂ ^ 3 - x₃ ^ 3) * (x₂ - x₃))) := by positivity
    have hmul : 0 ≤ (x₁ ^ 4 * (x₁ - α) + ε * (x₂ ^ 4 * (x₂ - α) + x₃ ^ 4 * (x₃ - α))) * W := by
      rw [hpair]
      linarith
    exact (mul_nonneg_iff_of_pos_right hW0).mp hmul
  -- the admitted square is strictly positive
  have hnotboth : x₁ - α ≠ 0 ∨ x₂ - α ≠ 0 := by
    rcases eq_or_ne (x₁ - α) 0 with h1 | h1
    · exact Or.inr fun h2 => hne₁₂ (by linarith [h1, h2])
    · exact Or.inl h1
  have hsqpos :
      0 < x₁ ^ 3 * (x₁ - α) ^ 2 + ε * (x₂ ^ 3 * (x₂ - α) ^ 2 + x₃ ^ 3 * (x₃ - α) ^ 2) := by
    rcases hnotboth with h | h
    · have hpos : 0 < x₁ ^ 3 * (x₁ - α) ^ 2 := by positivity
      have h2 : 0 ≤ ε * (x₂ ^ 3 * (x₂ - α) ^ 2 + x₃ ^ 3 * (x₃ - α) ^ 2) := by positivity
      linarith
    · have hpos : 0 < ε * (x₂ ^ 3 * (x₂ - α) ^ 2) := by positivity
      have h1 : 0 ≤ x₁ ^ 3 * (x₁ - α) ^ 2 := by positivity
      have h3 : 0 ≤ ε * (x₃ ^ 3 * (x₃ - α) ^ 2) := by positivity
      have hsum : ε * (x₂ ^ 3 * (x₂ - α) ^ 2 + x₃ ^ 3 * (x₃ - α) ^ 2)
          = ε * (x₂ ^ 3 * (x₂ - α) ^ 2) + ε * (x₃ ^ 3 * (x₃ - α) ^ 2) := by ring
      rw [hsum]
      linarith
  rw [hsplit]
  linarith

/-! ## The sign reversal survives a positive weight -/

theorem continuousAt_farAlpha {d₁ d₂ d₃ a : ℝ} (hd₁ : 0 < d₁) (ha : 0 < a) :
    ContinuousAt (fun ε : ℝ => farAlpha d₁ d₂ d₃ ε a) 0 := by
  have hpos : 0 < farNode d₁ a := farNode_pos hd₁ ha
  have hden : ContinuousAt (fun ε : ℝ => farMoment d₁ d₂ d₃ ε a 0) 0 := by
    simp only [farMoment, farFunctional]
    fun_prop
  have hnum : ContinuousAt (fun ε : ℝ => farMoment d₁ d₂ d₃ ε a 1) 0 := by
    simp only [farMoment, farFunctional]
    fun_prop
  have hden0 : farMoment d₁ d₂ d₃ 0 a 0 ≠ 0 := by
    simp only [farMoment, farFunctional, zero_mul, add_zero, pow_zero, mul_one]
    exact ne_of_gt hpos
  exact hnum.div hden hden0

/-- **The frozen-admission source stays negative for all small positive weights.** -/
theorem eventually_farSource_frozen_neg {d₁ d₂ d₃ a y : ℝ} (hd₁ : 0 < d₁) (ha : 0 < a)
    (hay : a < y) (hwindow : y + d₁ < 2 * (a + d₁)) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      farSource d₁ d₂ d₃ ε y (farAlpha d₁ d₂ d₃ ε a) < 0 := by
  have hzero : farSource d₁ d₂ d₃ 0 y (farAlpha d₁ d₂ d₃ 0 a) < 0 := by
    rw [farAlpha_zero d₁ d₂ d₃ a ha hd₁]
    exact farSource_frozen_neg_zero hd₁ ha hay hwindow
  have halpha := continuousAt_farAlpha (d₂ := d₂) (d₃ := d₃) hd₁ ha
  have hpoly : Continuous fun p : ℝ × ℝ =>
      2 * (farNode d₁ y ^ 3 * (farNode d₁ y - p.2) * (2 * farNode d₁ y - p.2)
        + p.1 * (farNode d₂ y ^ 3 * (farNode d₂ y - p.2) * (2 * farNode d₂ y - p.2)
          + farNode d₃ y ^ 3 * (farNode d₃ y - p.2) * (2 * farNode d₃ y - p.2))) := by
    fun_prop
  have heq : (fun ε : ℝ => farSource d₁ d₂ d₃ ε y (farAlpha d₁ d₂ d₃ ε a))
      = fun ε : ℝ =>
        2 * (farNode d₁ y ^ 3 * (farNode d₁ y - farAlpha d₁ d₂ d₃ ε a)
              * (2 * farNode d₁ y - farAlpha d₁ d₂ d₃ ε a)
          + ε * (farNode d₂ y ^ 3 * (farNode d₂ y - farAlpha d₁ d₂ d₃ ε a)
                * (2 * farNode d₂ y - farAlpha d₁ d₂ d₃ ε a)
            + farNode d₃ y ^ 3 * (farNode d₃ y - farAlpha d₁ d₂ d₃ ε a)
                * (2 * farNode d₃ y - farAlpha d₁ d₂ d₃ ε a))) := by
    funext ε
    exact farSource_eq d₁ d₂ d₃ ε y _
  have hcont : ContinuousAt (fun ε : ℝ => farSource d₁ d₂ d₃ ε y (farAlpha d₁ d₂ d₃ ε a)) 0 := by
    rw [heq]
    exact hpoly.continuousAt.comp (continuousAt_id.prodMk halpha)
  have hev : ∀ᶠ ε in nhds (0 : ℝ),
      farSource d₁ d₂ d₃ ε y (farAlpha d₁ d₂ d₃ ε a) < 0 :=
    hcont.eventually (gt_mem_nhds hzero)
  exact hev.filter_mono nhdsWithin_le_nhds

/-- **The frozen-admission resolvent-flow no-go.**  There is a positive weight for which the whole
degree-two Hankel chamber of the three-atom flow is positive definite, the current canonical
source is strictly positive, and the canonical source frozen at the nearby smaller mass `a` is
strictly negative.  Finite positivity, canonical admission and the exact shifted-moment law
therefore cannot sign the frozen source. -/
theorem exists_frozen_admission_source_sign_reversal {d₁ d₂ d₃ a y : ℝ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (h₁₂ : d₁ ≠ d₂) (h₁₃ : d₁ ≠ d₃) (h₂₃ : d₂ ≠ d₃)
    (ha : 0 < a) (hay : a < y) (hwindow : y + d₁ < 2 * (a + d₁)) :
    ∃ ε > 0,
      (∀ c₀ c₁ c₂ : ℝ, ¬(c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0) →
          0 < farFunctional d₁ d₂ d₃ ε y (fun x => (c₀ + c₁ * x + c₂ * x ^ 2) ^ 2))
        ∧ 0 < farSource d₁ d₂ d₃ ε y (farAlpha d₁ d₂ d₃ ε y)
        ∧ farSource d₁ d₂ d₃ ε y (farAlpha d₁ d₂ d₃ ε a) < 0 := by
  have hy : 0 < y := lt_trans ha hay
  have hev := eventually_farSource_frozen_neg (d₂ := d₂) (d₃ := d₃) hd₁ ha hay hwindow
  have hmem : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hε
  obtain ⟨ε, hfrozen, hεpos⟩ := (hev.and hmem).exists
  refine ⟨ε, hεpos, fun c₀ c₁ c₂ hc => ?_, ?_, hfrozen⟩
  · exact farFunctional_sq_pos (by positivity) (by positivity) (by positivity) hεpos
      h₁₂ h₁₃ h₂₃ hc
  · exact farSource_current_pos hd₁ hd₂ hd₃ hεpos hy h₁₂

/-! ## The moving-admission connection -/

theorem farMoment_pos {d₁ d₂ d₃ ε t : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (hε : 0 ≤ ε) (ht : 0 < t) (k : ℕ) : 0 < farMoment d₁ d₂ d₃ ε t k := by
  have h₁ := farNode_pos hd₁ ht
  have h₂ := farNode_pos hd₂ ht
  have h₃ := farNode_pos hd₃ ht
  rw [farMoment_eq]
  have hp₁ : 0 < farNode d₁ t ^ (k + 1) := by positivity
  have hp₂ : 0 ≤ ε * (farNode d₂ t ^ (k + 1) + farNode d₃ t ^ (k + 1)) := by positivity
  linarith

/-- The canonical admission moves with velocity `(s(1)² - 2 s(2) s(0))/s(0)²`. -/
theorem hasDerivAt_farAlpha {d₁ d₂ d₃ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => farAlpha d₁ d₂ d₃ ε s)
      ((farMoment d₁ d₂ d₃ ε t 1 ^ 2
          - 2 * farMoment d₁ d₂ d₃ ε t 2 * farMoment d₁ d₂ d₃ ε t 0)
        / farMoment d₁ d₂ d₃ ε t 0 ^ 2) t := by
  have h0 := hasDerivAt_farMoment hd₁ hd₂ hd₃ ε ht 0
  have h1 := hasDerivAt_farMoment hd₁ hd₂ hd₃ ε ht 1
  have hden : farMoment d₁ d₂ d₃ ε t 0 ≠ 0 :=
    ne_of_gt (farMoment_pos hd₁ hd₂ hd₃ hε ht 0)
  refine (h1.div h0 hden).congr_deriv ?_
  push_cast
  field_simp
  ring

/-- The odd pairing of the canonical admission is its admitted norm. -/
theorem farFunctional_mul_sub_farAlpha {d₁ d₂ d₃ ε t : ℝ}
    (hden : farMoment d₁ d₂ d₃ ε t 0 ≠ 0) :
    farFunctional d₁ d₂ d₃ ε t (fun x => x * (x - farAlpha d₁ d₂ d₃ ε t))
      = farNorm d₁ d₂ d₃ ε t (farAlpha d₁ d₂ d₃ ε t) := by
  simp only [farFunctional, farNorm, farAlpha, farMoment] at hden ⊢
  field_simp at hden ⊢
  ring

theorem hasDerivAt_farNodeMovingCurrent {d : ℝ} (hd : 0 < d) {t : ℝ} (ht : 0 < t)
    {A : ℝ → ℝ} {A' : ℝ} (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s : ℝ => farNode d s ^ 2 * (farNode d s - A s) ^ 2)
      (-(2 * farNode d t ^ 3 * (farNode d t - A t) * (2 * farNode d t - A t))
        - 2 * A' * (farNode d t ^ 2 * (farNode d t - A t))) t := by
  have hu := hasDerivAt_farNode hd ht
  have h1 := hu.pow 2
  have h2 := (hu.sub hA).pow 2
  refine (h1.mul h2).congr_deriv ?_
  simp only [Pi.pow_apply, Pi.sub_apply]
  push_cast
  ring

/-- **The moving canonical current retains the admission connection.**  Differentiating the odd
current along the *moving* canonical admission produces the frozen source together with the
admission-velocity connection term. -/
theorem hasDerivAt_farOddCurrent_moving {d₁ d₂ d₃ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hd₃ : 0 < d₃) {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => farOddCurrent d₁ d₂ d₃ ε s (farAlpha d₁ d₂ d₃ ε s))
      (-farSource d₁ d₂ d₃ ε t (farAlpha d₁ d₂ d₃ ε t)
        - 2 * ((farMoment d₁ d₂ d₃ ε t 1 ^ 2
            - 2 * farMoment d₁ d₂ d₃ ε t 2 * farMoment d₁ d₂ d₃ ε t 0)
          / farMoment d₁ d₂ d₃ ε t 0 ^ 2)
          * farNorm d₁ d₂ d₃ ε t (farAlpha d₁ d₂ d₃ ε t)) t := by
  have hden : farMoment d₁ d₂ d₃ ε t 0 ≠ 0 :=
    ne_of_gt (farMoment_pos hd₁ hd₂ hd₃ hε ht 0)
  have hA := hasDerivAt_farAlpha hd₁ hd₂ hd₃ hε ht
  have h₁ := hasDerivAt_farNodeMovingCurrent hd₁ ht hA
  have h₂ := hasDerivAt_farNodeMovingCurrent hd₂ ht hA
  have h₃ := hasDerivAt_farNodeMovingCurrent hd₃ ht hA
  have hsum := h₁.add ((h₂.add h₃).const_mul ε)
  have hfun : (fun s : ℝ => farOddCurrent d₁ d₂ d₃ ε s (farAlpha d₁ d₂ d₃ ε s))
      = fun s : ℝ => farNode d₁ s ^ 2 * (farNode d₁ s - farAlpha d₁ d₂ d₃ ε s) ^ 2
          + ε * (farNode d₂ s ^ 2 * (farNode d₂ s - farAlpha d₁ d₂ d₃ ε s) ^ 2
            + farNode d₃ s ^ 2 * (farNode d₃ s - farAlpha d₁ d₂ d₃ ε s) ^ 2) := by
    funext s
    exact farOddCurrent_eq d₁ d₂ d₃ ε s _
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [farSource_eq, ← farFunctional_mul_sub_farAlpha hden, farFunctional]
  ring

/-- **The exact displacement flow law.**  The frozen/current odd-current displacement moves by the
source difference plus the admission connection. -/
theorem hasDerivAt_farOddCurrent_displacement {d₁ d₂ d₃ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hd₃ : 0 < d₃) {ε : ℝ} (hε : 0 ≤ ε) {t : ℝ} (ht : 0 < t) (α : ℝ) :
    HasDerivAt (fun s : ℝ =>
        farOddCurrent d₁ d₂ d₃ ε s α - farOddCurrent d₁ d₂ d₃ ε s (farAlpha d₁ d₂ d₃ ε s))
      (-(farSource d₁ d₂ d₃ ε t α - farSource d₁ d₂ d₃ ε t (farAlpha d₁ d₂ d₃ ε t))
        + 2 * ((farMoment d₁ d₂ d₃ ε t 1 ^ 2
            - 2 * farMoment d₁ d₂ d₃ ε t 2 * farMoment d₁ d₂ d₃ ε t 0)
          / farMoment d₁ d₂ d₃ ε t 0 ^ 2)
          * farNorm d₁ d₂ d₃ ε t (farAlpha d₁ d₂ d₃ ε t)) t := by
  have hfrozen := hasDerivAt_farOddCurrent hd₁ hd₂ hd₃ ε ht α
  have hmoving := hasDerivAt_farOddCurrent_moving hd₁ hd₂ hd₃ hε ht
  refine (hfrozen.sub hmoving).congr_deriv ?_
  ring

end

end RHTower
