import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The local geometry of a reflection pair

The Rosati trace of a cycle splits over the reflection pairs `{ρ, ρ* = 1 − ρ̄}` of its spectrum.
In the coordinates `(u, v) = (ĝ(ρ), ĝ(ρ*))` the contribution of an off-line pair is the
**hyperbolic** form `h(u, v) = 2 Re(u v̄)` of signature `(1, 1)` (`localForm`). A multiplicative
correspondence acts on the fibre diagonally by its symbol; for the Hecke operator at `p` the symbol
is `β = p^{ρ − ½}` at `ρ` and `p^{ρ* − ½} = β̄⁻¹` at `ρ*` (`heckeSymbol_reflect`), an isometry of
`h` (`localForm_boost`).

* **Boosts force half-blindness** (`mul_conj_eq_zero_of_cyclic_nonneg`). If `|β| ≠ 1` the two
  symbols differ, the cyclic span of a fibre vector is the whole plane in the coordinates
  `(a + bβ, a + bβ̄⁻¹)`, and positivity of `h` on it forces `u v̄ = 0`.
* **Rotations constrain nothing more** (`cyclic_nonneg_iff_of_norm_eq_one`). If `|β| = 1` both
  symbols agree, and cyclic positivity is `Re(u v̄) ≥ 0`: positive non-isotropic fibres survive.
* **The Hecke symbol is a boost exactly off the line** (`norm_heckeSymbol_eq_one_iff`), so positivity
  along one Hecke orbit is half-blind at every off-line pair and free at critical zeros
  (`mul_conj_eq_zero_of_heckeCyclic_nonneg`).
* **Finite configurations** (`halfBlind_iff_cyclicForm_nonneg`): for a finite reflection-symmetric
  spectrum and a separating symbol, positivity of the form on the whole cyclic span of one vector
  is equivalent to half-blindness at every off-line pair (Lagrange interpolation).

Real even tests carry a **real** fibre: `ĝ(ρ*) = conj ĝ(ρ)` (`mellinAt_reflect_of_even`), so the
fibre is `z = ĝ(ρ) ∈ ℂ ≅ ℝ²` with the form `2 Re(z²)`, again of signature `(1, 1)`
(`localForm_conj`). The symmetric Hecke operator `g ↦ g(· − log p) + g(· + log p)` acts by the
symbol `w = p^{ρ−½} + p^{½−ρ}` (`mellinAt_symHecke`).

* **The resonance law** (`eq_zero_of_symCyclic_nonneg`, `symCyclic_nonneg_iff_of_im_eq_zero`). If `w`
  is not real, positivity on the real cyclic span forces `z = 0`; if `w` is real it is
  `Re(z²) ≥ 0`, which admits non-isotropic fibres. `Im w = 2 sinh((σ − ½) log p) sin(γ log p)`
  (`symHeckeSymbol_im`): an off-line `ρ` is **resonant** at `p` iff `γ log p ∈ πℤ`.
* **Two primes kill resonance** (`not_resonant_at_two_primes`). A non-real `ρ` is resonant at no
  more than one prime, since `p^a ≠ q^b`; a real `ρ` is resonant at every prime. So the symmetric
  Hecke operators at two primes force every real even fibre at a non-real off-line zero to vanish
  (`eq_zero_of_two_prime_symCyclic_nonneg`).

These are local laws: they say what positivity forces on a fibre that a carrier can isolate.
Multiplicative symmetry is hyperbolic at every off-line pair, which is why every multiplicative
positivity theorem ends in blindness, half-blindness or isotropy; positivity beyond isotropy needs
a local symmetry that is elliptic there, and the only elliptic Hecke fibres off the line are the
resonant ones, which a second prime removes.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-! ### The local form and boosts -/

/-- The **local form** of a reflection pair, `h(u, v) = 2 Re(u v̄)`, in the coordinates
`(ĝ(ρ), ĝ(ρ*))`. -/
def localForm (u v : ℂ) : ℝ := 2 * (u * conj v).re

/-- The local form is indefinite: `h(1, −1) = −2`. -/
theorem localForm_one_neg_one : localForm 1 (-1) = -2 := by
  simp [localForm]

/-- **Diagonal symbols `(β, β̄⁻¹)` are isometries of the local form.** -/
theorem localForm_boost {β : ℂ} (hβ : β ≠ 0) (u v : ℂ) :
    localForm (β * u) ((conj β)⁻¹ * v) = localForm u v := by
  have h : β * u * conj ((conj β)⁻¹ * v) = u * conj v := by
    rw [map_mul, map_inv₀, Complex.conj_conj]
    field_simp
  rw [localForm, localForm, h]

/-- The two symbols of a boost coincide exactly on the unit circle. -/
theorem eq_conj_inv_iff_norm_eq_one {β : ℂ} (hβ : β ≠ 0) : β = (conj β)⁻¹ ↔ ‖β‖ = 1 := by
  have hc : conj β ≠ 0 := (map_ne_zero _).mpr hβ
  have h1 : β = (conj β)⁻¹ ↔ β * conj β = 1 := by
    constructor
    · intro h; nth_rewrite 1 [h]; exact inv_mul_cancel₀ hc
    · intro h; exact eq_inv_of_mul_eq_one_left h
  rw [h1, Complex.mul_conj, ← Complex.ofReal_one, Complex.ofReal_inj, Complex.normSq_eq_norm_sq]
  exact pow_eq_one_iff_of_nonneg (norm_nonneg β) two_ne_zero

/-- **A boost forces half-blindness.** If `|β| ≠ 1` and the local form is nonnegative on the span
of `(x, y)` and its image `(βx, β̄⁻¹y)`, then `x ȳ = 0`. -/
theorem mul_conj_eq_zero_of_cyclic_nonneg {β : ℂ} (hβ0 : β ≠ 0) (hβ : ‖β‖ ≠ 1) {x y : ℂ}
    (h : ∀ a b : ℂ, 0 ≤ localForm ((a + b * β) * x) ((a + b * (conj β)⁻¹) * y)) :
    x * conj y = 0 := by
  set μ := (conj β)⁻¹
  have hd : β - μ ≠ 0 := sub_ne_zero.mpr fun he => hβ ((eq_conj_inv_iff_norm_eq_one hβ0).mp he)
  set c := x * conj y with hc
  -- solve `a + bβ = 1`, `a + bμ = −c`
  have h1 : (1 - (1 + c) / (β - μ) * β) + (1 + c) / (β - μ) * β = 1 := by ring
  have h2 : (1 - (1 + c) / (β - μ) * β) + (1 + c) / (β - μ) * μ = -c := by
    field_simp; ring
  have key : localForm (1 * x) (-c * y) = -2 * Complex.normSq c := by
    rw [localForm, one_mul, map_mul, map_neg,
      show x * (-(conj c) * conj y) = -(c * conj c) by rw [hc]; ring, Complex.mul_conj,
      Complex.neg_re, Complex.ofReal_re]
    ring
  have := h (1 - (1 + c) / (β - μ) * β) ((1 + c) / (β - μ))
  rw [h1, h2, key] at this
  have hn : Complex.normSq c = 0 := by
    have := Complex.normSq_nonneg c
    linarith
  exact Complex.normSq_eq_zero.mp hn

/-- **A rotation constrains only the sign.** If `|β| = 1`, positivity on the cyclic span is
`Re(x ȳ) ≥ 0`. -/
theorem cyclic_nonneg_iff_of_norm_eq_one {β : ℂ} (hβ : ‖β‖ = 1) {x y : ℂ} :
    (∀ a b : ℂ, 0 ≤ localForm ((a + b * β) * x) ((a + b * (conj β)⁻¹) * y)) ↔
      0 ≤ (x * conj y).re := by
  have hβ0 : β ≠ 0 := by intro h; simp [h] at hβ
  have he : (conj β)⁻¹ = β := ((eq_conj_inv_iff_norm_eq_one hβ0).mpr hβ).symm
  simp only [he]
  have key : ∀ l : ℂ, localForm (l * x) (l * y) = 2 * Complex.normSq l * (x * conj y).re := by
    intro l
    rw [localForm, map_mul, show l * x * (conj l * conj y) = (Complex.normSq l : ℂ) * (x * conj y) by
      rw [← Complex.mul_conj]; ring, Complex.re_ofReal_mul]
    ring
  constructor
  · intro h
    have := h 1 0
    rw [zero_mul, add_zero, key, Complex.normSq_one] at this
    linarith
  · intro h a b
    rw [key]
    exact mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) h

/-! ### The Hecke symbol -/

/-- The **Hecke symbol** `p^{s − ½} = exp((s − ½) log p)` by which translation by `log p` acts on
the transform at `s`. -/
def heckeSymbol (p : ℝ) (s : ℂ) : ℂ := Complex.exp ((s - 1 / 2) * Real.log p)

theorem heckeSymbol_ne_zero (p : ℝ) (s : ℂ) : heckeSymbol p s ≠ 0 := Complex.exp_ne_zero _

/-- **The reflection law**: the symbol at `ρ* = 1 − ρ̄` is `β̄⁻¹`. -/
theorem heckeSymbol_reflect (p : ℝ) (s : ℂ) :
    heckeSymbol p (1 - conj s) = (conj (heckeSymbol p s))⁻¹ := by
  rw [heckeSymbol, heckeSymbol, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  ring

theorem norm_heckeSymbol (p : ℝ) (s : ℂ) :
    ‖heckeSymbol p s‖ = Real.exp ((s.re - 1 / 2) * Real.log p) := by
  rw [heckeSymbol, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The Hecke symbol is a boost exactly off the critical line.** -/
theorem norm_heckeSymbol_eq_one_iff {p : ℝ} (hp : 1 < p) (s : ℂ) :
    ‖heckeSymbol p s‖ = 1 ↔ s.re = 1 / 2 := by
  have hl : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  rw [norm_heckeSymbol, Real.exp_eq_one_iff, mul_eq_zero, sub_eq_zero]
  simp [hl]

/-- **Positivity along one Hecke orbit is half-blind at every off-line pair.** -/
theorem mul_conj_eq_zero_of_heckeCyclic_nonneg {p : ℝ} (hp : 1 < p) {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2)
    {x y : ℂ}
    (h : ∀ a b : ℂ, 0 ≤ localForm ((a + b * heckeSymbol p ρ) * x)
      ((a + b * heckeSymbol p (1 - conj ρ)) * y)) :
    x * conj y = 0 := by
  rw [heckeSymbol_reflect] at h
  exact mul_conj_eq_zero_of_cyclic_nonneg (heckeSymbol_ne_zero p ρ)
    (fun h1 => hρ ((norm_heckeSymbol_eq_one_iff hp ρ).mp h1)) h

/-! ### Finite configurations -/

section Finite

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The form `Σ_k m_k Re(P(τ_k) g_k · conj(P(τ_{k*}) g_{k*}))` of the cyclic vector `P(T) g` on a
finite spectrum `κ` with reflection `k ↦ k*`, multiplicities `m` and symbol `τ`. -/
def cyclicForm (refl : κ → κ) (m : κ → ℝ) (τ g : κ → ℂ) (P : Polynomial ℂ) : ℝ :=
  ∑ k, m k * ((P.eval (τ k) * g k) * conj (P.eval (τ (refl k)) * g (refl k))).re

/-- **Finite orientation law.** On a finite reflection-symmetric spectrum with positive
multiplicities and a separating symbol, the form is nonnegative on the whole cyclic span of `g`
iff `g` is half-blind at every off-line pair. -/
theorem halfBlind_iff_cyclicForm_nonneg {refl : κ → κ} (hrefl : Function.Involutive refl)
    {m : κ → ℝ} (hm : ∀ k, 0 < m k) (hmr : ∀ k, m (refl k) = m k) {τ : κ → ℂ}
    (hτ : Function.Injective τ) (g : κ → ℂ) :
    (∀ P, 0 ≤ cyclicForm refl m τ g P) ↔ ∀ k, refl k ≠ k → g k * conj (g (refl k)) = 0 := by
  constructor
  · intro h k hk
    set c := g k * conj (g (refl k)) with hc
    -- the interpolating polynomial with value `1` at `τ k`, `−c` at `τ k*`, `0` elsewhere
    set r : κ → ℂ := fun j => if j = k then 1 else if j = refl k then -c else 0
    set P := Lagrange.interpolate Finset.univ τ r
    have hP : ∀ j, P.eval (τ j) = r j := fun j =>
      Lagrange.eval_interpolate_at_node r (hτ.injOn) (Finset.mem_univ j)
    have hk' : k ≠ refl k := fun h' => hk h'.symm
    have rk : r k = 1 := by simp [r]
    have rk' : r (refl k) = -c := by simp [r, hk]
    have hsum : cyclicForm refl m τ g P = 2 * m k * (-(Complex.normSq c)) := by
      rw [cyclicForm, Fintype.sum_eq_add k (refl k) hk']
      · rw [hrefl k]
        simp only [hP]
        rw [rk, rk', hmr]
        have e1 : (1 * g k * conj (-c * g (refl k))).re = -(Complex.normSq c) := by
          rw [map_mul, map_neg, show 1 * g k * (-(conj c) * conj (g (refl k))) = -(c * conj c) by
            rw [hc]; ring, Complex.mul_conj, Complex.neg_re, Complex.ofReal_re]
        have e2 : (-c * g (refl k) * conj (1 * g k)).re = -(Complex.normSq c) := by
          rw [map_mul, map_one, one_mul, show -c * g (refl k) * conj (g k) = -(c * conj c) by
            rw [hc, map_mul, Complex.conj_conj]; ring, Complex.mul_conj, Complex.neg_re,
            Complex.ofReal_re]
        rw [e1, e2]; ring
      · intro j hj
        have h1 : r j = 0 := by simp [r, hj.1, hj.2]
        rw [hP, h1, zero_mul, zero_mul, Complex.zero_re, mul_zero]
    have := h P
    rw [hsum] at this
    have hc : Complex.normSq c ≤ 0 := by nlinarith [hm k, Complex.normSq_nonneg c]
    exact Complex.normSq_eq_zero.mp (le_antisymm hc (Complex.normSq_nonneg c))
  · intro h P
    refine Finset.sum_nonneg fun k _ => mul_nonneg (hm k).le ?_
    by_cases hk : refl k = k
    · rw [hk, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _
    · rw [map_mul, show P.eval (τ k) * g k * (conj (P.eval (τ (refl k))) * conj (g (refl k))) =
        P.eval (τ k) * conj (P.eval (τ (refl k))) * (g k * conj (g (refl k))) by ring, h k hk,
        mul_zero, Complex.zero_re]

end Finite

/-! ### Real even fibres and the resonance law -/

/-- On a real even fibre the value at `ρ*` is `conj z`, and the local form is `2 Re(z²)`. -/
theorem localForm_conj (z : ℂ) : localForm z (conj z) = 2 * (z * z).re := by
  rw [localForm, Complex.conj_conj]

/-- **A non-real symbol forces blindness of a real fibre.** If `w ∉ ℝ` and `2 Re(((a + bw) z)²) ≥ 0`
for all real `a, b`, then `z = 0`. -/
theorem eq_zero_of_symCyclic_nonneg {w : ℂ} (hw : w.im ≠ 0) {z : ℂ}
    (h : ∀ a b : ℝ, 0 ≤ localForm ((a + b * w) * z) (conj ((a + b * w) * z))) : z = 0 := by
  -- choose `a + bw = I · conj z`, so that `(a + bw) z = I |z|²`
  have hl : ((z.im - z.re / w.im * w.re : ℝ) : ℂ) + ((z.re / w.im : ℝ) : ℂ) * w = I * conj z := by
    apply Complex.ext
    · simp
    · simp; field_simp
  have := h (z.im - z.re / w.im * w.re) (z.re / w.im)
  rw [localForm_conj, hl, show I * conj z * z = I * (Complex.normSq z : ℂ) by
    rw [mul_assoc, mul_comm (conj z), Complex.mul_conj]] at this
  have hre : (I * (Complex.normSq z : ℂ) * (I * (Complex.normSq z : ℂ))).re =
      -(Complex.normSq z) ^ 2 := by
    simp [Complex.mul_re, pow_two]
  rw [hre] at this
  have : Complex.normSq z = 0 := by nlinarith [Complex.normSq_nonneg z]
  exact Complex.normSq_eq_zero.mp this

/-- **A real symbol constrains only the phase**: positivity on the real cyclic span is
`Re(z²) ≥ 0`. -/
theorem symCyclic_nonneg_iff_of_im_eq_zero {w : ℂ} (hw : w.im = 0) {z : ℂ} :
    (∀ a b : ℝ, 0 ≤ localForm ((a + b * w) * z) (conj ((a + b * w) * z))) ↔ 0 ≤ (z * z).re := by
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, w = r := ⟨w.re, Complex.ext (by simp) (by simp [hw])⟩
  have key : ∀ a b : ℝ, localForm ((a + b * (r : ℂ)) * z) (conj ((a + b * (r : ℂ)) * z)) =
      2 * (a + b * r) ^ 2 * (z * z).re := by
    intro a b
    rw [localForm_conj, show ((a : ℂ) + b * (r : ℂ)) * z * (((a : ℂ) + b * (r : ℂ)) * z) =
      (((a + b * r) ^ 2 : ℝ) : ℂ) * (z * z) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  constructor
  · intro h
    have := h 1 0
    rw [key] at this
    simp only [zero_mul, add_zero, one_pow, mul_one] at this
    linarith
  · intro h a b
    rw [key]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) h

/-- The **symmetric Hecke symbol** `p^{s−½} + p^{½−s}` of `g ↦ g(· − log p) + g(· + log p)`. -/
def symHeckeSymbol (p : ℝ) (s : ℂ) : ℂ := heckeSymbol p s + heckeSymbol p (1 - s)

/-- `Im(p^{s−½} + p^{½−s}) = 2 sinh((σ − ½) log p) sin(γ log p)`. -/
theorem symHeckeSymbol_im (p : ℝ) (s : ℂ) :
    (symHeckeSymbol p s).im =
      2 * Real.sinh ((s.re - 1 / 2) * Real.log p) * Real.sin (s.im * Real.log p) := by
  simp only [symHeckeSymbol, heckeSymbol, Complex.add_im, Complex.exp_im]
  have h1 : ((s - 1 / 2) * (Real.log p : ℂ)).re = (s.re - 1 / 2) * Real.log p := by
    simp [Complex.mul_re]
  have h2 : ((s - 1 / 2) * (Real.log p : ℂ)).im = s.im * Real.log p := by simp [Complex.mul_im]
  have h3 : ((1 - s - 1 / 2) * (Real.log p : ℂ)).re = -((s.re - 1 / 2) * Real.log p) := by
    simp [Complex.mul_re]; ring
  have h4 : ((1 - s - 1 / 2) * (Real.log p : ℂ)).im = -(s.im * Real.log p) := by
    simp [Complex.mul_im]
  rw [h1, h2, h3, h4, Real.sin_neg, Real.sinh_eq]
  ring

/-- **Resonance.** For `p > 1`, the symmetric symbol is real iff `Re s = ½` or `sin(γ log p) = 0`. -/
theorem symHeckeSymbol_im_eq_zero_iff {p : ℝ} (hp : 1 < p) (s : ℂ) :
    (symHeckeSymbol p s).im = 0 ↔ s.re = 1 / 2 ∨ Real.sin (s.im * Real.log p) = 0 := by
  have hl : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  rw [symHeckeSymbol_im, mul_eq_zero, mul_eq_zero]
  simp only [two_ne_zero, false_or]
  have : Real.sinh ((s.re - 1 / 2) * Real.log p) = 0 ↔ s.re = 1 / 2 := by
    rw [← Real.sinh_zero, Real.sinh_injective.eq_iff, mul_eq_zero, sub_eq_zero]
    simp [hl]
  rw [this]

/-- **A non-real point is resonant at no more than one prime.** If `γ ≠ 0` then `γ log p` and
`γ log q` are not both in `πℤ` for distinct primes `p, q`. -/
theorem not_resonant_at_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {γ : ℝ}
    (hγ : γ ≠ 0) : ¬ (Real.sin (γ * Real.log p) = 0 ∧ Real.sin (γ * Real.log q) = 0) := by
  rintro ⟨h1, h2⟩
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h1
  obtain ⟨l, hl⟩ := Real.sin_eq_zero_iff.mp h2
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  -- `l · log p = k · log q`
  have hrel : (l : ℝ) * Real.log p = k * Real.log q := by
    have : γ * ((l : ℝ) * Real.log p - k * Real.log q) = 0 := by
      have e : γ * ((l : ℝ) * Real.log p - k * Real.log q) =
          (l : ℝ) * (γ * Real.log p) - k * (γ * Real.log q) := by ring
      rw [e, ← hk, ← hl]; ring
    have := (mul_eq_zero.mp this).resolve_left hγ
    linarith
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : γ * Real.log p = 0 := by rw [← hk]; simp
    exact (mul_ne_zero hγ hlp.ne') this
  -- absolute values: `|l| log p = |k| log q`
  have habs : ((l.natAbs : ℕ) : ℝ) * Real.log p = ((k.natAbs : ℕ) : ℝ) * Real.log q := by
    have := congrArg abs hrel
    rw [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq] at this
    simpa [Nat.cast_natAbs, Int.cast_abs] using this
  have hpow : ((p ^ l.natAbs : ℕ) : ℝ) = ((q ^ k.natAbs : ℕ) : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    push_cast
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hp0 _)) (Set.mem_Ioi.mpr (pow_pos hq0 _))
    rw [Real.log_pow, Real.log_pow, habs]
  have hpow' : p ^ l.natAbs = q ^ k.natAbs := by exact_mod_cast hpow
  have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk0
  have hdvd : p ∣ q ^ k.natAbs := by
    rw [← hpow']
    have hl0 : l.natAbs ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hpow'
      exact (Nat.one_lt_pow hkpos.ne' hq.one_lt).ne hpow'
    exact dvd_pow_self p hl0
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd))

/-- **Two primes force blindness of a real even fibre** at a non-real off-line point. -/
theorem eq_zero_of_two_prime_symCyclic_nonneg {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) (hγ : ρ.im ≠ 0) {z : ℂ}
    (hP : ∀ a b : ℝ, 0 ≤ localForm ((a + b * symHeckeSymbol p ρ) * z)
      (conj ((a + b * symHeckeSymbol p ρ) * z)))
    (hQ : ∀ a b : ℝ, 0 ≤ localForm ((a + b * symHeckeSymbol q ρ) * z)
      (conj ((a + b * symHeckeSymbol q ρ) * z))) : z = 0 := by
  by_cases h1 : (symHeckeSymbol p ρ).im = 0
  · have h2 : (symHeckeSymbol q ρ).im ≠ 0 := by
      intro h2
      have r1 := ((symHeckeSymbol_im_eq_zero_iff (by exact_mod_cast hp.one_lt) ρ).mp h1).resolve_left hρ
      have r2 := ((symHeckeSymbol_im_eq_zero_iff (by exact_mod_cast hq.one_lt) ρ).mp h2).resolve_left hρ
      exact not_resonant_at_two_primes hp hq hpq hγ ⟨r1, r2⟩
    exact eq_zero_of_symCyclic_nonneg h2 hQ
  · exact eq_zero_of_symCyclic_nonneg h1 hP

/-- **A real point is resonant at every prime**: the symmetric symbol is real. -/
theorem symHeckeSymbol_im_of_im_eq_zero (p : ℝ) {s : ℂ} (hs : s.im = 0) :
    (symHeckeSymbol p s).im = 0 := by
  rw [symHeckeSymbol_im, hs, zero_mul, Real.sin_zero, mul_zero]

/-! ### Fibres of real even tests -/

/-- The transform `ĝ(s) = ∫ g(u) e^{(s − ½)u} du` of a real test in logarithmic coordinates. -/
def mellinAt (g : ℝ → ℝ) (s : ℂ) : ℂ := ∫ u, (g u : ℂ) * Complex.exp ((s - 1 / 2) * u)

/-- **A real even test has real fibres**: `ĝ(1 − s̄) = conj ĝ(s)`. -/
theorem mellinAt_reflect_of_even {g : ℝ → ℝ} (hg : ∀ u, g (-u) = g u) (s : ℂ) :
    mellinAt g (1 - conj s) = conj (mellinAt g s) := by
  rw [mellinAt, mellinAt, ← integral_conj, ← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hg, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_sub, map_div₀, map_one,
    map_ofNat, Complex.ofReal_neg]
  congr 2
  ring

theorem integrable_mellinAt {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (s : ℂ) :
    Integrable fun u => (g u : ℂ) * Complex.exp ((s - 1 / 2) * u) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_ofReal.comp hg).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  · exact (hgc.comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_right

/-- **Translation by `L` multiplies the transform by `e^{(s − ½)L}`.** -/
theorem mellinAt_translate (g : ℝ → ℝ) (L : ℝ) (s : ℂ) :
    mellinAt (fun u => g (u - L)) s = Complex.exp ((s - 1 / 2) * L) * mellinAt g s := by
  rw [mellinAt, mellinAt, ← integral_add_right_eq_self
    (fun u => ((g (u - L) : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * u)) L, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [add_sub_cancel_right]
  push_cast
  rw [show (s - 1 / 2) * ((u : ℂ) + L) = (s - 1 / 2) * L + (s - 1 / 2) * u by ring, Complex.exp_add]
  ring

theorem mellinAt_add {g h : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (hhc : HasCompactSupport h) (s : ℂ) :
    mellinAt (fun u => g u + h u) s = mellinAt g s + mellinAt h s := by
  rw [mellinAt, mellinAt, mellinAt, ← integral_add (integrable_mellinAt hg hgc s)
    (integrable_mellinAt hh hhc s)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  push_cast; ring

theorem mellinAt_smul (c : ℝ) (g : ℝ → ℝ) (s : ℂ) :
    mellinAt (fun u => c * g u) s = c * mellinAt g s := by
  rw [mellinAt, mellinAt, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  push_cast; ring

/-- The symmetric Hecke translate `g(· − log p) + g(· + log p)`. -/
def symHecke (p : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := fun u => g (u - Real.log p) + g (u + Real.log p)

theorem continuous_symHecke {g : ℝ → ℝ} (hg : Continuous g) (p : ℝ) : Continuous (symHecke p g) :=
  (hg.comp (continuous_id.sub continuous_const)).add (hg.comp (continuous_id.add continuous_const))

theorem hasCompactSupport_symHecke {g : ℝ → ℝ} (hgc : HasCompactSupport g) (p : ℝ) :
    HasCompactSupport (symHecke p g) :=
  (hgc.comp_homeomorph (Homeomorph.subRight (Real.log p))).add
    (hgc.comp_homeomorph (Homeomorph.addRight (Real.log p)))

theorem symHecke_even {g : ℝ → ℝ} (hg : ∀ u, g (-u) = g u) (p : ℝ) (u : ℝ) :
    symHecke p g (-u) = symHecke p g u := by
  simp only [symHecke]
  rw [show -u - Real.log p = -(u + Real.log p) by ring, show -u + Real.log p = -(u - Real.log p) by
    ring, hg, hg, add_comm]

/-- **The symmetric Hecke operator acts on transforms by its symbol.** -/
theorem mellinAt_symHecke {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (p : ℝ)
    (s : ℂ) : mellinAt (symHecke p g) s = symHeckeSymbol p s * mellinAt g s := by
  have c1 : Continuous fun u => g (u - Real.log p) := hg.comp (continuous_id.sub continuous_const)
  have c2 : Continuous fun u => g (u - -Real.log p) := hg.comp (continuous_id.sub continuous_const)
  have hsub : HasCompactSupport fun u => g (u - Real.log p) :=
    hgc.comp_homeomorph (Homeomorph.subRight (Real.log p))
  have hadd : HasCompactSupport fun u => g (u - -Real.log p) :=
    hgc.comp_homeomorph (Homeomorph.subRight (-Real.log p))
  have e : symHecke p g = fun u => g (u - Real.log p) + g (u - -Real.log p) := by
    funext u; simp [symHecke, sub_neg_eq_add]
  rw [e, mellinAt_add c1 hsub c2 hadd, mellinAt_translate, mellinAt_translate,
    symHeckeSymbol, heckeSymbol, heckeSymbol, add_mul]
  congr 3
  push_cast; ring

/-- **The resonance law for real even tests.** Let `g` be a continuous compactly supported even
real test, `p > 1`, and `ρ` off the line with `sin(Im ρ · log p) ≠ 0`. If the local form of the
pair `{ρ, ρ*}` is nonnegative on the transforms of every combination `a g + b T_p g` of `g` and its
symmetric Hecke translate, then `ĝ(ρ) = 0`. -/
theorem mellinAt_eq_zero_of_symHecke_local_nonneg {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {p : ℝ} (hp : 1 < p) {ρ : ℂ}
    (hρ : ρ.re ≠ 1 / 2) (hres : Real.sin (ρ.im * Real.log p) ≠ 0)
    (h : ∀ a b : ℝ, 0 ≤ localForm (mellinAt (fun u => a * g u + b * symHecke p g u) ρ)
      (mellinAt (fun u => a * g u + b * symHecke p g u) (1 - conj ρ))) :
    mellinAt g ρ = 0 := by
  have hw : (symHeckeSymbol p ρ).im ≠ 0 := by
    rw [Ne, symHeckeSymbol_im_eq_zero_iff hp]; tauto
  refine eq_zero_of_symCyclic_nonneg hw fun a b => ?_
  have hcomb : ∀ s, mellinAt (fun u => a * g u + b * symHecke p g u) s =
      ((a : ℂ) + b * symHeckeSymbol p s) * mellinAt g s := by
    intro s
    have c1 : Continuous fun u => a * g u := continuous_const.mul hg
    have k1 : HasCompactSupport fun u => a * g u := hgc.mul_left
    have c2 : Continuous fun u => b * symHecke p g u := continuous_const.mul (continuous_symHecke hg p)
    have k2 : HasCompactSupport fun u => b * symHecke p g u := (hasCompactSupport_symHecke hgc p).mul_left
    rw [mellinAt_add c1 k1 c2 k2, mellinAt_smul, mellinAt_smul, mellinAt_symHecke hg hgc]
    ring
  have heven' : ∀ u, (a * g (-u) + b * symHecke p g (-u)) = a * g u + b * symHecke p g u := by
    intro u; rw [heven, symHecke_even heven]
  have := h a b
  rw [mellinAt_reflect_of_even heven', hcomb] at this
  exact this

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
