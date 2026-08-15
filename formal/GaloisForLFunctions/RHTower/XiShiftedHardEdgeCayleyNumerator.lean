import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# The Cayley numerator of a real-rooted polynomial

The hard-edge transform sends a polynomial `P` on the Cayley interval to the polynomial obtained
by clearing the denominator of

`P((a² - u)/(a² + u))`

at degree `d`.  The substitution is a real Möbius map of the sphere with the two fixed points
`a²` and `∞` interchanged by the pole at `u = -a²`, so it carries a real root to a real root and
carries the exceptional value `-1` to the degree drop.  Consequently the numerator has only real
zeros whenever `P` has.

This is the algebraic half of the hard-edge passage from a finite real-rooted characteristic
polynomial to a squared-variable Laguerre--Pólya boundary state.
-/

open Polynomial

noncomputable section

namespace RHTower

theorem norm_ofReal_sq (a : ℝ) : ‖((a : ℂ) ^ 2)‖ = a ^ 2 := by
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The degree-`d` numerator of `P((a² - u)/(a² + u))`. -/
def cayleyNumerator (a : ℝ) (d : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C (P.coeff k) * (Polynomial.C ((a : ℂ) ^ 2) - Polynomial.X) ^ k
      * (Polynomial.C ((a : ℂ) ^ 2) + Polynomial.X) ^ (d - k)

/-- Away from the pole the numerator really is the cleared substitution. -/
theorem eval_cayleyNumerator (a : ℝ) (d : ℕ) (P : Polynomial ℂ) (hd : P.natDegree ≤ d)
    (w : ℂ) (hw : (a : ℂ) ^ 2 + w ≠ 0) :
    (cayleyNumerator a d P).eval w
      = ((a : ℂ) ^ 2 + w) ^ d * P.eval (((a : ℂ) ^ 2 - w) / ((a : ℂ) ^ 2 + w)) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  rw [cayleyNumerator, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hsplit : ((a : ℂ) ^ 2 + w) ^ d
      = ((a : ℂ) ^ 2 + w) ^ k * ((a : ℂ) ^ 2 + w) ^ (d - k) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [div_pow, hsplit]
  field_simp

/-- **The Cayley numerator of a real-rooted polynomial is real-rooted.**  A zero of the numerator
is either the pole `-a²` or the image of a zero of `P`; the Möbius map is real on both sides, and
the exceptional value `-1` would force `a = 0`. -/
theorem cayleyNumerator_root_im_eq_zero (a : ℝ) (ha : a ≠ 0) (d : ℕ) (P : Polynomial ℂ)
    (hd : P.natDegree ≤ d) (hreal : ∀ ρ : ℂ, P.eval ρ = 0 → ρ.im = 0)
    {w : ℂ} (hw : (cayleyNumerator a d P).eval w = 0) : w.im = 0 := by
  have ha2 : ((a : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (by exact_mod_cast ha)
  by_cases hden : (a : ℂ) ^ 2 + w = 0
  · have hval : w = -(((a ^ 2 : ℝ)) : ℂ) := by push_cast; linear_combination hden
    rw [hval, Complex.neg_im, Complex.ofReal_im, neg_zero]
  · rw [eval_cayleyNumerator a d P hd w hden] at hw
    rcases mul_eq_zero.1 hw with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hden
    · obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ, ρ = ((a : ℂ) ^ 2 - w) / ((a : ℂ) ^ 2 + w) := ⟨_, rfl⟩
      have hPρ : P.eval ρ = 0 := by rw [hρdef]; exact h
      have hρim : ρ.im = 0 := hreal ρ hPρ
      have hmul : ρ * ((a : ℂ) ^ 2 + w) = (a : ℂ) ^ 2 - w := by
        rw [hρdef]
        field_simp
      have hρ1 : ρ + 1 ≠ 0 := by
        intro hcon
        have hρm : ρ = -1 := by linear_combination hcon
        rw [hρm] at hmul
        have h2 : (2 : ℂ) * (a : ℂ) ^ 2 = 0 := by linear_combination -hmul
        exact ha2 (by linear_combination h2 / 2)
      obtain ⟨t, hρt⟩ : ∃ t : ℝ, ρ = (t : ℂ) :=
        ⟨ρ.re, by apply Complex.ext <;> simp [hρim]⟩
      have hden' : ((t : ℂ) + 1) ≠ 0 := by rw [hρt] at hρ1; exact hρ1
      have ht1 : t + 1 ≠ 0 := by
        intro hcon
        apply hden'
        rw [← Complex.ofReal_one, ← Complex.ofReal_add, hcon, Complex.ofReal_zero]
      have hw' : w * ((t : ℂ) + 1) = (a : ℂ) ^ 2 * (1 - (t : ℂ)) := by
        rw [hρt] at hmul
        linear_combination hmul
      have hsolve : w = ((a ^ 2 * (1 - t) / (t + 1) : ℝ) : ℂ) := by
        have hcast : ((a ^ 2 * (1 - t) / (t + 1) : ℝ) : ℂ)
            = ((a : ℂ) ^ 2 * (1 - (t : ℂ))) / ((t : ℂ) + 1) := by
          push_cast
          ring
        rw [hcast, eq_div_iff hden']
        exact hw'
      rw [hsolve, Complex.ofReal_im]

/-- Locally uniform convergence transfers along the squaring map: if the squared-variable family
converges locally uniformly after substituting `u = z²`, it converges locally uniformly in `u`. -/
theorem tendstoLocallyUniformly_of_comp_sq {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (h : TendstoLocallyUniformly (fun n z => G n (z ^ 2)) (fun z => g (z ^ 2)) Filter.atTop) :
    TendstoLocallyUniformly G g Filter.atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at h ⊢
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine TendstoUniformlyOn.mono ?_ hR
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hb := h (Metric.closedBall (0 : ℂ) (Real.sqrt (max R 0))) (isCompact_closedBall _ _)
  rw [Metric.tendstoUniformlyOn_iff] at hb
  filter_upwards [hb ε hε] with n hn u hu
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ 2 = u := IsSepClosed.exists_pow_nat_eq u 2
  have hunorm : ‖u‖ ≤ max R 0 := by
    have := Metric.mem_closedBall.1 hu
    rw [dist_zero_right] at this
    exact le_trans this (le_max_left _ _)
  have hzmem : z ∈ Metric.closedBall (0 : ℂ) (Real.sqrt (max R 0)) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖z‖ ^ 2 = ‖u‖ := by rw [← hz, norm_pow]
    have hle : ‖z‖ ^ 2 ≤ max R 0 := by rw [hnorm]; exact hunorm
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg z)] at this
  have hres := hn z hzmem
  rw [hz] at hres
  exact hres

/-- **(HHWB.3) The hard-edge limit has only real zeros.**  The Cayley numerators of real-rooted
polynomials are real-rooted, and a nonzero entire locally uniform limit inherits the closed real
axis as its zero locus.  This is the Laguerre--Pólya closure step of the hard-edge passage. -/
theorem cayleyNumerator_limit_zero_im_eq_zero
    {a : ℕ → ℝ} {d : ℕ → ℕ} {P : ℕ → Polynomial ℂ} {F : ℂ → ℂ}
    (ha : ∀ n, a n ≠ 0) (hd : ∀ n, (P n).natDegree ≤ d n)
    (hreal : ∀ n, ∀ ρ : ℂ, (P n).eval ρ = 0 → ρ.im = 0)
    (hconv : TendstoLocallyUniformly
      (fun n w => (cayleyNumerator (a n) (d n) (P n)).eval w) F Filter.atTop)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    {b z : ℂ} (hb : F b ≠ 0) (hz : F z = 0) : z.im = 0 :=
  zero_mem_closed_of_tendstoLocallyUniformly hconv hF
    (Filter.Eventually.of_forall fun n =>
      Polynomial.differentiable_aeval (cayleyNumerator (a n) (d n) (P n)))
    (isClosed_eq Complex.continuous_im continuous_const)
    (Filter.Eventually.of_forall fun n _ hw =>
      cayleyNumerator_root_im_eq_zero (a n) (ha n) (d n) (P n) (hd n) (hreal n) hw)
    hb hz

/-- **(HHWB.3) with a normalization.**  Rescaling each numerator by a nonzero constant does not
move its zeros, so the same conclusion holds for the normalized hard-edge polynomials. -/
theorem scaled_cayleyNumerator_limit_zero_im_eq_zero
    {a : ℕ → ℝ} {d : ℕ → ℕ} {P : ℕ → Polynomial ℂ} {c : ℕ → ℂ} {F : ℂ → ℂ}
    (ha : ∀ n, a n ≠ 0) (hc : ∀ n, c n ≠ 0) (hd : ∀ n, (P n).natDegree ≤ d n)
    (hreal : ∀ n, ∀ ρ : ℂ, (P n).eval ρ = 0 → ρ.im = 0)
    (hconv : TendstoLocallyUniformly
      (fun n w => c n * (cayleyNumerator (a n) (d n) (P n)).eval w) F Filter.atTop)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    {b z : ℂ} (hb : F b ≠ 0) (hz : F z = 0) : z.im = 0 :=
  zero_mem_closed_of_tendstoLocallyUniformly hconv hF
    (Filter.Eventually.of_forall fun n =>
      (Polynomial.differentiable_aeval (cayleyNumerator (a n) (d n) (P n))).const_mul (c n))
    (isClosed_eq Complex.continuous_im continuous_const)
    (Filter.Eventually.of_forall fun n _ hw =>
      cayleyNumerator_root_im_eq_zero (a n) (ha n) (d n) (P n) (hd n) (hreal n)
        ((mul_eq_zero.1 hw).resolve_left (hc n)))
    hb hz

end RHTower

end
