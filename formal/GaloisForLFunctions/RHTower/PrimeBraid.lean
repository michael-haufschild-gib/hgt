/-
The diagonal prime orbit as an infinite, collision-free braid over a pinned window, and the
min-log law for its pairwise linking.

For a fixed real part `σ > 0` the strands `t ↦ u_n(t) = n^{-(σ + it)} = exp(-(σ + it)·log n)`
trace, as the height `t` varies, an infinite family of nowhere-zero curves ordered by radius
`‖u_n(t)‖ = exp(-σ·log n)`: a larger prime sits on a strictly smaller circle.  Two strands never
meet at a common height — their moduli differ — so the family is a collision-free braid, one
strand per prime, for every pinned window (`strand_apart`).

The linking of two strands is measured by the argument increment of their difference over the
window `[0,T]` (`angleIncr`, the imaginary part of the endpoint difference of any continuous
logarithm).  A single strand advances its argument linearly, `angleIncr (u_n) 0 T = -T·log n`
(`strand_angleIncr`).  For a *pair* `p < q` the difference factors as
`u_p - u_q = u_p·(1 - w)` with `w = u_q/u_p` of constant modulus `(p/q)^σ < 1`; the second factor
therefore stays in the open right half-plane, so `arg(1 - w)` never leaves `(-π/2, π/2)` and its
net contribution across the two endpoints is strictly below `π`.  Hence the linking equals that of
the dominant (larger-radius = smaller-prime) strand up to an error strictly less than `π`:

  `|angleIncr (u_p - u_q) 0 T + T·log p| < π`   (`braid_linking_min_law`).

Equivalently the linking form reads `-T·log(min p q)` (`braid_linking_min_law'`): the multiplicative
rate lattice `{log n}` carries a tropical (min-plus) structure — the smaller generator dominates —
realized here as *exact* braid topology at every finite window, not as an asymptotic limit.
-/
import GaloisForLFunctions.RHTower.WindingNumber

open Complex

namespace RHTower

/-! ### §1 The argument increment of a path -/

/-- The **argument increment** of a path `γ` over `[a,b]`: the imaginary part of the endpoint
difference of the canonical continuous logarithm.  For a nonvanishing continuous `γ` this is the
net angle swept, branch-independent by `contLog_increment_indep`. -/
noncomputable def angleIncr (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  (contLog γ b).im - (contLog γ a).im

/-! ### §2 The prime strands -/

/-- The `n`-th prime strand at real part `σ` and height `t`: `n^{-(σ + it)}`, written through the
exponential so it is manifestly nowhere zero and entire in `t`. -/
noncomputable def strand (n : ℕ) (σ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(((σ : ℂ) + (t : ℂ) * Complex.I)) * (Real.log n : ℂ))

/-- The strand's modulus is its radius `n^{-σ} = exp(-σ·log n)`, constant in the height `t`: the
real part of the exponent is `-σ·log n`. -/
theorem strand_norm (n : ℕ) (σ t : ℝ) : ‖strand n σ t‖ = Real.exp (-(σ * Real.log n)) := by
  rw [strand, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Each strand is nowhere zero: it is an exponential. -/
theorem strand_ne_zero (n : ℕ) (σ t : ℝ) : strand n σ t ≠ 0 := Complex.exp_ne_zero _

/-- Each strand is continuous in the height. -/
theorem strand_continuous (n : ℕ) (σ : ℝ) : Continuous (strand n σ) := by
  unfold strand; fun_prop

/-- **Collision-free braid.**  At every pinned height `t`, distinct ordered primes `1 < p < q`
occupy distinct strands: their moduli `exp(-σ·log p) ≠ exp(-σ·log q)` differ, since `σ > 0` and
`log` is strictly monotone.  Two strands never meet, so the whole family is one collision-free
braid, one strand per prime. -/
theorem strand_apart {p q : ℕ} (hp : 1 < p) (hpq : p < q) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    strand p σ t ≠ strand q σ t := by
  intro h
  have hnorm : ‖strand p σ t‖ = ‖strand q σ t‖ := by rw [h]
  rw [strand_norm, strand_norm] at hnorm
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpq' : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  have hlog : Real.log p < Real.log q := Real.log_lt_log hpr hpq'
  have hmul : σ * Real.log p < σ * Real.log q := mul_lt_mul_of_pos_left hlog hσ
  have hlt : Real.exp (-(σ * Real.log q)) < Real.exp (-(σ * Real.log p)) :=
    Real.exp_lt_exp.mpr (by linarith)
  rw [hnorm] at hlt
  exact lt_irrefl _ hlt

/-! ### §3 The linking of a single strand -/

/-- **A single strand winds linearly.**  The argument increment of the `n`-th strand over `[0,T]`
is `-T·log n`: the explicit continuous logarithm `t ↦ -(σ + it)·log n` has imaginary part
`-t·log n`, transported to `contLog` by branch-independence. -/
theorem strand_angleIncr (n : ℕ) (hn : 1 < n) (σ T : ℝ) :
    angleIncr (strand n σ) 0 T = -(T * Real.log n) := by
  have _ := hn
  set L : ℝ → ℂ := fun t => -(((σ : ℂ) + (t : ℂ) * Complex.I)) * (Real.log n : ℂ) with hL_def
  have hLcont : Continuous L := by rw [hL_def]; fun_prop
  have hLexp : ∀ t, Complex.exp (L t) = strand n σ t := fun t => rfl
  obtain ⟨hclc, hcle⟩ := contLog_spec (strand_continuous n σ) (fun t => strand_ne_zero n σ t)
  have hind := contLog_increment_indep hLcont hclc
    (fun t => (hLexp t).trans (hcle t).symm) 0 T
  have hangle : angleIncr (strand n σ) 0 T = (L T).im - (L 0).im := by
    have h := congrArg Complex.im hind
    rw [Complex.sub_im, Complex.sub_im] at h
    exact h.symm
  rw [hangle]
  have hLim : ∀ t : ℝ, (L t).im = -(t * Real.log n) := by
    intro t
    rw [hL_def]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hLim, hLim]; ring

/-! ### §4 The min-log law for pairwise linking -/

/-- **The min-log law.**  For ordered primes `1 < p < q` and `σ > 0`, the pairwise linking of the
strands `p` and `q` over a pinned window `[0,T]` equals the linking of the dominant strand `p`
(the larger radius, smaller prime) up to an error strictly below `π`:

  `|angleIncr (u_p - u_q) 0 T + T·log p| < π`.

Mechanism: `u_p - u_q = u_p·(1 - w)` with `w = u_q/u_p` of constant modulus `(p/q)^σ < 1`.  The
factor `1 - w` has strictly positive real part, so `arg(1 - w) ∈ (-π/2, π/2)`; the explicit
continuous logarithm `t ↦ -(σ + it)·log p + log(1 - w(t))` of the difference therefore has
imaginary increment `-T·log p + (arg(1 - w(T)) - arg(1 - w(0)))`, and the parenthesized term is a
difference of two angles each below `π/2` in absolute value, hence strictly below `π`. -/
theorem braid_linking_min_law {p q : ℕ} (hp : 1 < p) (hpq : p < q) {σ : ℝ} (hσ : 0 < σ)
    {T : ℝ} (hT : 0 ≤ T) :
    |angleIncr (fun t => strand p σ t - strand q σ t) 0 T + T * Real.log p| < Real.pi := by
  have _ := hT
  set w : ℝ → ℂ := fun t => strand q σ t / strand p σ t with hw_def
  have hp0 : ∀ t, strand p σ t ≠ 0 := fun t => strand_ne_zero p σ t
  have hlog : Real.log p < Real.log q := by
    have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hpq' : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
    exact Real.log_lt_log hpr hpq'
  have hw_lt1 : ∀ t, ‖w t‖ < 1 := by
    intro t
    have hpos : 0 < ‖strand p σ t‖ := norm_pos_iff.mpr (hp0 t)
    have hqp : ‖strand q σ t‖ < ‖strand p σ t‖ := by
      rw [strand_norm, strand_norm]
      apply Real.exp_lt_exp.mpr
      have hmul := mul_lt_mul_of_pos_left hlog hσ
      linarith
    rw [hw_def]; simp only []
    rw [norm_div, div_lt_one hpos]
    exact hqp
  have hRe_pos : ∀ t, 0 < (1 - w t).re := by
    intro t
    have h1 : (w t).re ≤ ‖w t‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    have h2 := hw_lt1 t
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hne1w : ∀ t, (1 : ℂ) - w t ≠ 0 := by
    intro t hzero
    have hcontra := hRe_pos t
    rw [hzero, Complex.zero_re] at hcontra
    exact lt_irrefl 0 hcontra
  have hslit : ∀ t, (1 - w t) ∈ slitPlane := by
    intro t
    have h := mem_slitPlane_of_norm_lt_one (z := -(w t)) (by rw [norm_neg]; exact hw_lt1 t)
    rwa [show (1 : ℂ) + -(w t) = 1 - w t by ring] at h
  have hw_cont : Continuous w := by
    rw [hw_def]
    exact (strand_continuous q σ).div (strand_continuous p σ) (fun t => hp0 t)
  have hlogw_cont : Continuous (fun t => Complex.log (1 - w t)) :=
    (continuous_const.sub hw_cont).clog hslit
  set L : ℝ → ℂ := fun t => (-(((σ : ℂ) + (t : ℂ) * Complex.I)) * (Real.log p : ℂ))
      + Complex.log (1 - w t) with hL_def
  have hL_cont : Continuous L := by
    rw [hL_def]
    exact (by fun_prop : Continuous (fun t : ℝ =>
      -(((σ : ℂ) + (t : ℂ) * Complex.I)) * (Real.log p : ℂ))).add hlogw_cont
  have hL_exp : ∀ t, Complex.exp (L t) = strand p σ t - strand q σ t := by
    intro t
    have hpt := hp0 t
    rw [hL_def]; simp only []
    rw [Complex.exp_add, Complex.exp_log (hne1w t)]
    rw [show Complex.exp (-(((σ : ℂ) + (t : ℂ) * Complex.I)) * (Real.log p : ℂ)) = strand p σ t
        from rfl]
    rw [hw_def]; simp only []
    field_simp
  have hdiff_cont : Continuous (fun t => strand p σ t - strand q σ t) :=
    (strand_continuous p σ).sub (strand_continuous q σ)
  have hdiff_ne : ∀ t, strand p σ t - strand q σ t ≠ 0 := fun t h =>
    strand_apart hp hpq hσ t (sub_eq_zero.mp h)
  obtain ⟨hclc, hcle⟩ := contLog_spec hdiff_cont hdiff_ne
  have hind := contLog_increment_indep hL_cont hclc
    (fun t => (hL_exp t).trans (hcle t).symm) 0 T
  have hangle : angleIncr (fun t => strand p σ t - strand q σ t) 0 T = (L T).im - (L 0).im := by
    have h := congrArg Complex.im hind
    rw [Complex.sub_im, Complex.sub_im] at h
    exact h.symm
  have hLim : ∀ t : ℝ, (L t).im = -(t * Real.log p) + Complex.arg (1 - w t) := by
    intro t
    rw [hL_def]
    simp only [Complex.add_im, Complex.log_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hval : angleIncr (fun t => strand p σ t - strand q σ t) 0 T + T * Real.log p
      = Complex.arg (1 - w T) - Complex.arg (1 - w 0) := by
    rw [hangle, hLim, hLim]; ring
  rw [hval]
  have harg : ∀ t, |Complex.arg (1 - w t)| < Real.pi / 2 := fun t =>
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hRe_pos t))
  calc |Complex.arg (1 - w T) - Complex.arg (1 - w 0)|
      ≤ |Complex.arg (1 - w T)| + |Complex.arg (1 - w 0)| := abs_sub _ _
    _ < Real.pi := by have h1 := harg T; have h2 := harg 0; linarith

/-- **The min-log law, tropical reading.**  Rewriting `log p = log(min p q)` makes explicit that the
pairwise linking is governed by the *minimum* of the two rate-lattice generators: the smaller prime
dominates the braid's linking form, `-T·log(min p q)`, up to an error strictly below `π`. -/
theorem braid_linking_min_law' {p q : ℕ} (hp : 1 < p) (hpq : p < q) {σ : ℝ} (hσ : 0 < σ)
    {T : ℝ} (hT : 0 ≤ T) :
    |angleIncr (fun t => strand p σ t - strand q σ t) 0 T + T * Real.log (min p q)| < Real.pi := by
  rw [show min (p : ℝ) (q : ℝ) = (p : ℝ) from min_eq_left (by exact_mod_cast hpq.le)]
  exact braid_linking_min_law hp hpq hσ hT

end RHTower
