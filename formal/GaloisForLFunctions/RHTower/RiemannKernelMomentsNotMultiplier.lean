import GaloisForLFunctions.HTGeometry.NewtonInequalities
import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound

/-!
# Multiplier sequences are log-concave; Riemann's moments are not a multiplier sequence

A real sequence `γ` is a *multiplier sequence* if `Σ a_k X^k ↦ Σ γ_k a_k X^k` maps real-rooted
polynomials to real-rooted polynomials (`IsMultiplierSeq`).  If the even moments
`b_k = ∫ u^{2k} Φ(u) du` of Riemann's kernel formed a multiplier sequence, applying it to the
coefficients of `cos` would put `Ξ` in the Laguerre–Pólya class.

* `IsMultiplierSeq.turan`: a multiplier sequence with `γ_{k+1} ≠ 0` satisfies
  `γ_{k−1} γ_{k+1} ≤ γ_k²`.  Apply `γ` to `(1 + X)^{k+1}`: the image has Newton-normalized
  coefficients `A_i = γ_{k+1−i}`, and Newton's inequality `A₀A₂ ≤ A₁²` is the claim.
* `eq_one_of_logConcave_tendsto_one`, `IsMultiplierSeq.eq_one_of_tendsto`: a positive
  multiplier sequence with `γ₀ = 1` and `γ_k → 1` is identically `1`.  So no real-rooted
  comparison function whose moments are asymptotic to those of `Ξ`, but differ from them, can
  be carried to `Ξ` by a multiplier sequence.
* `evenMoment_one_sq_lt`: for every super-exponentially decaying kernel `g`, the moments are
  strictly log-convex at `k = 1`: `b₁² < b₀ b₂`, since `b₀ b₂ − b₁² = b₀ ∫ (u² − b₁/b₀)² g`.
* `not_isMultiplierSeq_evenMoment`, `not_isMultiplierSeq_riemannMoments`: the even moments of
  such a kernel, in particular of Riemann's kernel, are not a multiplier sequence.
-/

open Polynomial Finset MeasureTheory Filter Topology
open GaloisForLFunctions.SignAlternation

namespace RHTower

noncomputable section

/-- Apply a real sequence to the coefficients of a polynomial. -/
def applySeq (γ : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree + 1), C (γ k * p.coeff k) * X ^ k

/-- A multiplier sequence maps real-rooted polynomials to real-rooted polynomials. -/
def IsMultiplierSeq (γ : ℕ → ℝ) : Prop :=
  ∀ p : ℝ[X], Hyperbolic p → Hyperbolic (applySeq γ p)

theorem coeff_applySeq (γ : ℕ → ℝ) (p : ℝ[X]) (m : ℕ) :
    (applySeq γ p).coeff m = γ m * p.coeff m := by
  classical
  unfold applySeq
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have hm : p.natDegree < m := by
      simp only [mem_range, not_lt] at h; omega
    rw [coeff_eq_zero_of_natDegree_lt hm, mul_zero]

theorem natDegree_applySeq_le (γ : ℕ → ℝ) (p : ℝ[X]) :
    (applySeq γ p).natDegree ≤ p.natDegree := by
  unfold applySeq
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))

theorem one_add_X_eq : (1 + X : ℝ[X]) = X - C (-1) := by
  rw [map_neg, map_one]; ring

theorem natDegree_one_add_X_pow (n : ℕ) : ((1 + X : ℝ[X]) ^ n).natDegree = n := by
  rw [natDegree_pow, one_add_X_eq, natDegree_X_sub_C, mul_one]

theorem hyperbolic_one_add_X_pow (n : ℕ) : Hyperbolic ((1 + X : ℝ[X]) ^ n) := by
  unfold Hyperbolic
  rw [natDegree_one_add_X_pow, one_add_X_eq, roots_pow, roots_X_sub_C, Multiset.card_nsmul,
    Multiset.card_singleton, mul_one]

/-- **Turán inequality for multiplier sequences.** -/
theorem IsMultiplierSeq.turan {γ : ℕ → ℝ} (hγ : IsMultiplierSeq γ) {k : ℕ} (hk : 1 ≤ k)
    (htop : γ (k + 1) ≠ 0) : γ (k - 1) * γ (k + 1) ≤ γ k ^ 2 := by
  set n := k + 1 with hn
  set q := applySeq γ ((1 + X : ℝ[X]) ^ n) with hq_def
  have hq : Hyperbolic q := hγ _ (hyperbolic_one_add_X_pow n)
  have hcoeff : ∀ m, q.coeff m = γ m * (n.choose m : ℝ) := fun m => by
    rw [hq_def, coeff_applySeq, coeff_one_add_X_pow]
  have hdeg : q.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact (natDegree_applySeq_le _ _).trans (natDegree_one_add_X_pow n).le
    · rw [hcoeff, Nat.choose_self, Nat.cast_one, mul_one]; exact htop
  have hA : ∀ i, i ≤ n → newtonCoeff q i = γ (n - i) := fun i hi => by
    unfold newtonCoeff
    have hc : (n.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
    rw [hdeg, hcoeff, Nat.choose_symm hi]
    field_simp
  have hnewton := newton_inequality n q hq hdeg 1 le_rfl (by omega)
  rw [hA 0 (by omega), hA 2 (by omega), hA 1 (by omega)] at hnewton
  rw [show n - 0 = k + 1 by omega, show n - 2 = k - 1 by omega, show n - 1 = k by omega]
    at hnewton
  linarith [mul_comm (γ (k - 1)) (γ (k + 1))]

/-- **Rigidity.**  A positive log-concave sequence with `γ₀ = 1` and `γ_k → 1` is identically `1`. -/
theorem eq_one_of_logConcave_tendsto_one {γ : ℕ → ℝ} (hpos : ∀ k, 0 < γ k) (h0 : γ 0 = 1)
    (hlc : ∀ k, 1 ≤ k → γ (k - 1) * γ (k + 1) ≤ γ k ^ 2) (hlim : Tendsto γ atTop (𝓝 1)) :
    ∀ k, γ k = 1 := by
  set S : ℕ → ℝ := fun k => Real.log (γ k) with hS
  set d : ℕ → ℝ := fun k => S (k + 1) - S k with hd
  have hSlim : Tendsto S atTop (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp hlim
    simpa [hS, Real.log_one, Function.comp_def] using this
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have := (hSlim.comp (tendsto_add_atTop_nat 1)).sub hSlim
    simpa [hd, Function.comp_def] using this
  have hanti : Antitone d := by
    refine antitone_nat_of_succ_le fun k => ?_
    have h := hlc (k + 1) (by omega)
    rw [show k + 1 - 1 = k by omega, show k + 1 + 1 = k + 2 by omega] at h
    have hl := Real.log_le_log (mul_pos (hpos k) (hpos (k + 2))) h
    rw [Real.log_mul (hpos k).ne' (hpos (k + 2)).ne', Real.log_pow] at hl
    simp only [hd, hS]
    rw [show k + 1 + 1 = k + 2 by omega]
    push_cast at hl
    linarith
  have hd0 : ∀ k, 0 ≤ d k := hanti.le_of_tendsto hdlim
  have hmono : Monotone S := monotone_nat_of_le_succ fun k => by
    have := hd0 k
    simp only [hd] at this
    linarith
  have hS0 : S 0 = 0 := by simp [hS, h0]
  intro k
  have hle : S k ≤ 0 := hmono.ge_of_tendsto hSlim k
  have hge : 0 ≤ S k := hS0 ▸ hmono (Nat.zero_le k)
  have hk0 : Real.log (γ k) = 0 := le_antisymm hle hge
  have := Real.exp_log (hpos k)
  rw [hk0, Real.exp_zero] at this
  exact this.symm

/-- **A multiplier sequence tending to `1` is trivial.** -/
theorem IsMultiplierSeq.eq_one_of_tendsto {γ : ℕ → ℝ} (hγ : IsMultiplierSeq γ)
    (hpos : ∀ k, 0 < γ k) (h0 : γ 0 = 1) (hlim : Tendsto γ atTop (𝓝 1)) : ∀ k, γ k = 1 :=
  eq_one_of_logConcave_tendsto_one hpos h0
    (fun _ hk => hγ.turan hk (hpos _).ne') hlim

/-- The even moments `b_k = ∫ u^{2k} g(u) du`. -/
def kernelEvenMoment (g : ℝ → ℝ) (k : ℕ) : ℝ := ∫ u, u ^ (2 * k) * g u

theorem integrable_pow_mul_of_superExp {g : ℝ → ℝ} (hg : DeBruijn.SuperExpKernel g) (m : ℕ) :
    Integrable (fun u : ℝ => u ^ m * g u) := by
  refine ((hg.integrable_mul_exp 1).const_mul (m.factorial : ℝ)).mono'
    ((continuous_pow m).mul hg.continuous).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have he := Real.pow_div_factorial_le_exp |u| (abs_nonneg u) m
  rw [div_le_iff₀ hf] at he
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_nonneg (hg.nonneg u), one_mul]
  calc |u| ^ m * g u ≤ Real.exp |u| * m.factorial * g u :=
        mul_le_mul_of_nonneg_right he (hg.nonneg u)
    _ = m.factorial * (g u * Real.exp |u|) := by ring

/-- A nonnegative continuous integrable function positive at one point has positive integral. -/
theorem integral_pos_of_continuous_nonneg {f : ℝ → ℝ} (hc : Continuous f) (hf : 0 ≤ f)
    (hi : Integrable f) {x₀ : ℝ} (hx₀ : 0 < f x₀) : 0 < ∫ u, f u := by
  rw [integral_pos_iff_support_of_nonneg hf hi]
  exact hc.isOpen_support.measure_pos volume ⟨x₀, hx₀.ne'⟩

theorem evenMoment_pos {g : ℝ → ℝ} (hg : DeBruijn.SuperExpKernel g) (k : ℕ) :
    0 < kernelEvenMoment g k := by
  have hc : Continuous (fun u : ℝ => u ^ (2 * k) * g u) := (continuous_pow _).mul hg.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.continuous_iff.mp hg.continuous 0 (g 0) hg.pos_zero
  have hx : 0 < g (ε / 2) := by
    have h := hball (ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    rw [Real.dist_eq] at h
    linarith [neg_abs_le (g (ε / 2) - g 0)]
  exact integral_pos_of_continuous_nonneg hc
    (fun u => mul_nonneg (by rw [pow_mul]; positivity) (hg.nonneg u))
    (integrable_pow_mul_of_superExp hg _) (x₀ := ε / 2) (mul_pos (by positivity) hx)

/-- **Strict log-convexity of the moments at `k = 1`:** `b₁² < b₀ b₂`. -/
theorem evenMoment_one_sq_lt {g : ℝ → ℝ} (hg : DeBruijn.SuperExpKernel g) :
    kernelEvenMoment g 1 ^ 2 < kernelEvenMoment g 0 * kernelEvenMoment g 2 := by
  set b₀ := kernelEvenMoment g 0 with hb₀
  set b₁ := kernelEvenMoment g 1 with hb₁
  set b₂ := kernelEvenMoment g 2 with hb₂
  have h0 : 0 < b₀ := evenMoment_pos hg 0
  have h1 : 0 < b₁ := evenMoment_pos hg 1
  set m := b₁ / b₀ with hm
  have hm0 : 0 < m := div_pos h1 h0
  have i0 := integrable_pow_mul_of_superExp hg 0
  have i2 := integrable_pow_mul_of_superExp hg 2
  have i4 := integrable_pow_mul_of_superExp hg 4
  have hexp : ∫ u, (u ^ 2 - m) ^ 2 * g u = b₂ - 2 * m * b₁ + m ^ 2 * b₀ := by
    have e : (fun u : ℝ => (u ^ 2 - m) ^ 2 * g u)
        = fun u => u ^ 4 * g u - (2 * m) * (u ^ 2 * g u) + m ^ 2 * (u ^ 0 * g u) := by
      funext u; ring
    have j1 : Integrable (fun u : ℝ => u ^ 4 * g u - 2 * m * (u ^ 2 * g u)) :=
      i4.sub (i2.const_mul _)
    have j2 : Integrable (fun u : ℝ => m ^ 2 * (u ^ 0 * g u)) := i0.const_mul _
    have j3 : Integrable (fun u : ℝ => 2 * m * (u ^ 2 * g u)) := i2.const_mul _
    rw [e, integral_add j1 j2, integral_sub i4 j3, integral_const_mul, integral_const_mul]
    simp only [hb₀, hb₁, hb₂, kernelEvenMoment]
  have hvar : 0 < ∫ u, (u ^ 2 - m) ^ 2 * g u := by
    have hc : Continuous (fun u : ℝ => (u ^ 2 - m) ^ 2 * g u) := by
      exact ((continuous_pow 2).sub continuous_const).pow 2 |>.mul hg.continuous
    have hi : Integrable (fun u : ℝ => (u ^ 2 - m) ^ 2 * g u) := by
      have e : (fun u : ℝ => (u ^ 2 - m) ^ 2 * g u)
          = fun u => u ^ 4 * g u - (2 * m) * (u ^ 2 * g u) + m ^ 2 * (u ^ 0 * g u) := by
        funext u; ring
      rw [e]; exact (i4.sub (i2.const_mul _)).add (i0.const_mul _)
    refine integral_pos_of_continuous_nonneg hc (fun u => mul_nonneg (sq_nonneg _) (hg.nonneg u))
      hi (x₀ := 0) ?_
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub, even_two,
      Even.neg_pow]
    exact mul_pos (pow_pos hm0 2) hg.pos_zero
  rw [hexp] at hvar
  have key : b₀ * b₂ - b₁ ^ 2 = b₀ * (b₂ - 2 * m * b₁ + m ^ 2 * b₀) := by
    rw [hm]; field_simp; ring
  nlinarith [mul_pos h0 hvar]

/-- **The moments of a super-exponential kernel are not a multiplier sequence.** -/
theorem not_isMultiplierSeq_evenMoment {g : ℝ → ℝ} (hg : DeBruijn.SuperExpKernel g) :
    ¬ IsMultiplierSeq (kernelEvenMoment g) := by
  intro hγ
  have h := hγ.turan (k := 1) le_rfl (evenMoment_pos hg 2).ne'
  have hs := evenMoment_one_sq_lt hg
  norm_num at h
  linarith

/-- **Riemann's moments are not a multiplier sequence.** -/
theorem not_isMultiplierSeq_riemannMoments : ¬ IsMultiplierSeq (kernelEvenMoment riemannKernelReal) :=
  not_isMultiplierSeq_evenMoment DeBruijn.riemannKernel_superExp

end

end RHTower
