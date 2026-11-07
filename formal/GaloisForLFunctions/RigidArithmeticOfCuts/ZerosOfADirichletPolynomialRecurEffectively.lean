import GaloisForLFunctions.RigidArithmeticOfCuts.EffectiveKroneckerAtArithmeticScale
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Zeros of a Dirichlet polynomial recur effectively

The model case of transport. A vertical translate of a Dirichlet polynomial `F` differs from `F` by phases `n^{-iτ} − 1`,
so a simultaneous return of the prime phases keeps `F(· + iτ)` uniformly close to `F` on a disc around a zero. The
minimum modulus principle then places a zero of the translate in the disc:

**Transport by minimum modulus.** If `‖G(c)‖ < ‖G(z)‖` on the circle `‖z − c‖ = r`, then `G` has a zero in the disc.

Effective Kronecker supplies the returns in every window of a fixed explicit length. So a zero of a Dirichlet polynomial
recurs with explicit gap: one in each window `[T₁, T₁ + T]`, with `log T ≍ D log R` for `R` the product of the primes
of the letters and `D ≍ |P| W²/μ²`.

The model has no tail. For `ζ` the same statement fails at every zero right of the line: prime returns keep positive
density while returns of `ζ` are rare (`exists_primeReturn_not_zetaReturn`).
-/

open Finset Complex Metric

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-! ### Returns in every window -/

/-- **Effective Kronecker in every window.** Shifting the targets by `T₁ log p` moves the height to `T₁ + t`. -/
theorem exists_height_phase_return_window {P : Finset ℕ} (D : ℕ) (hP : ∀ p ∈ P, p.Prime) (θ a : ℕ → ℝ)
    (ha : ∀ p ∈ P, 0 ≤ a p) {T : ℝ}
    (hT : 4 * ((D : ℝ) + 1) * (radicalOf P : ℝ) ^ (D + 1) * ((exponentBox P D).card : ℝ) ≤ T) (T₁ : ℝ) :
    ∃ τ ∈ Set.Icc T₁ (T₁ + T), ∑ p ∈ P, a p * (1 - Real.cos (τ * Real.log p - θ p)) ≤
      5 * (∑ p ∈ P, a p) / ((D : ℝ) + 1) := by
  obtain ⟨t, ht, h⟩ := exists_height_phase_return D hP (fun p => θ p - T₁ * Real.log p) a ha hT
  refine ⟨T₁ + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  refine le_trans (le_of_eq (sum_congr rfl fun p _ => ?_)) h
  congr 3
  ring

/-! ### Transport by minimum modulus -/

/-- **Transport by minimum modulus.** A holomorphic function smaller at the centre of a disc than on its circle has a zero
in the disc. -/
theorem exists_zero_of_norm_center_lt {G : ℂ → ℂ} (hG : Differentiable ℂ G) {c : ℂ} {r μ : ℝ} (hr : 0 < r)
    (hμ : 0 < μ) (hc : ‖G c‖ < μ) (hcircle : ∀ z, ‖z - c‖ = r → μ ≤ ‖G z‖) :
    ∃ z, ‖z - c‖ < r ∧ G z = 0 := by
  by_contra hno
  push Not at hno
  have hne : ∀ z ∈ closedBall c r, G z ≠ 0 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rcases hz.lt_or_eq with h | h
    · exact hno z h
    · intro h0
      have := hcircle z h
      rw [h0, norm_zero] at this
      linarith
  have hd : DifferentiableOn ℂ (fun z => (G z)⁻¹) (closure (ball c r)) := by
    rw [closure_ball c hr.ne']
    exact fun z hz => ((hG z).inv (hne z hz)).differentiableWithinAt
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := r))
    hd.diffContOnCl (C := μ⁻¹) (fun z hz => ?_) (subset_closure (mem_ball_self hr))
  · have hc0 : G c ≠ 0 := hne c (mem_closedBall_self hr.le)
    rw [norm_inv] at hbound
    have hpos := norm_pos_iff.mpr hc0
    have := inv_lt_inv₀ hμ hpos |>.mpr hc
    linarith
  · rw [frontier_ball c hr.ne', mem_sphere, dist_eq_norm] at hz
    rw [norm_inv]
    exact inv_anti₀ hμ (hcircle z hz)

/-! ### Phases -/

/-- The phase `n^{-iτ}`. -/
def phase (τ : ℝ) (n : ℕ) : ℂ := ((n : ℝ) : ℂ) ^ (-((τ : ℂ) * I))

theorem norm_phase (τ : ℝ) {n : ℕ} (hn : 0 < n) : ‖phase τ n‖ = 1 := by
  rw [phase, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  simp

theorem phase_mul (τ : ℝ) (a b : ℕ) : phase τ (a * b) = phase τ a * phase τ b := by
  simp only [phase]
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) _

/-- The chord of a phase. -/
theorem norm_phase_sub_one_sq (τ : ℝ) {p : ℕ} (hp : 0 < p) :
    ‖phase τ p - 1‖ ^ 2 = 2 * (1 - Real.cos (τ * Real.log p)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hne : ((p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hval : phase τ p = ((Real.cos (τ * Real.log p) : ℝ) : ℂ) - ((Real.sin (τ * Real.log p) : ℝ) : ℂ) * I := by
    rw [phase, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hp0.le]
    have h1 : ((Real.log p : ℝ) : ℂ) * (-((τ : ℂ) * I)) = ((-(τ * Real.log p) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hval, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  nlinarith [Real.sin_sq_add_cos_sq (τ * Real.log p)]

/-- A composite phase moves by at most `Ω(n)` times the bound on its prime phases. -/
theorem norm_phase_sub_one_le {τ δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p, p.Prime → p ∣ n → ‖phase τ p - 1‖ ≤ δ) :
    ‖phase τ n - 1‖ ≤ (ArithmeticFunction.cardFactors n : ℝ) * δ := by
  induction n using Nat.recOnMul with
  | zero => exact absurd hn (lt_irrefl 0)
  | one => simp [phase]
  | prime p hp =>
    rw [ArithmeticFunction.cardFactors_apply_prime hp, Nat.cast_one, one_mul]
    exact hprime p hp dvd_rfl
  | mul a b ha hb =>
    have ha0 : 0 < a := Nat.pos_of_mul_pos_right hn
    have hb0 : 0 < b := Nat.pos_of_mul_pos_left hn
    have h1 := ha ha0 fun p hp hd => hprime p hp (Dvd.dvd.mul_right hd b)
    have h2 := hb hb0 fun p hp hd => hprime p hp (Dvd.dvd.mul_left hd a)
    have hsplit : phase τ (a * b) - 1 = phase τ a * (phase τ b - 1) + (phase τ a - 1) := by
      rw [phase_mul]
      ring
    rw [hsplit, ArithmeticFunction.cardFactors_mul ha0.ne' hb0.ne']
    push_cast
    calc _ ≤ ‖phase τ a * (phase τ b - 1)‖ + ‖phase τ a - 1‖ := norm_add_le _ _
      _ = ‖phase τ b - 1‖ + ‖phase τ a - 1‖ := by rw [norm_mul, norm_phase τ ha0, one_mul]
      _ ≤ _ := by nlinarith

/-! ### The model -/

/-- A Dirichlet polynomial. -/
def dirichletPolyOf (S : Finset ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ := ∑ n ∈ S, a n * ((n : ℝ) : ℂ) ^ (-s)

theorem differentiable_dirichletPolyOf {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℂ) :
    Differentiable ℂ (dirichletPolyOf S a) := by
  unfold dirichletPolyOf
  refine Differentiable.fun_sum fun n hn => ?_
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by have := hS n hn; omega : n ≠ 0)
  exact (differentiable_neg.const_cpow (Or.inl hne)).const_mul _

/-- The translate of a term is the term times the phase. -/
theorem cpow_translate {n : ℕ} (hn : 1 ≤ n) (s : ℂ) (τ : ℝ) :
    ((n : ℝ) : ℂ) ^ (-(s + (τ : ℂ) * I)) = ((n : ℝ) : ℂ) ^ (-s) * phase τ n := by
  have hne : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [neg_add, Complex.cpow_add _ _ hne, phase]

/-- **Zeros of a Dirichlet polynomial recur effectively.** A zero `ρ` with `‖F‖ ≥ μ` on the circle of radius `r` has a
translate within `r` of `ρ + iτ`, for some `τ` in every window of a fixed length `T`. The length is explicit in the
letters of `F`, `W = Σ ‖a(n)‖ n^{r − Re ρ} Ω(n)`, and `μ`. -/
theorem exists_zero_in_every_window {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℂ) {ρ : ℂ}
    (hρ : dirichletPolyOf S a ρ = 0) {r μ : ℝ} (hr : 0 < r) (hμ : 0 < μ)
    (hcircle : ∀ s, ‖s - ρ‖ = r → μ ≤ ‖dirichletPolyOf S a s‖) :
    ∃ T : ℝ, 0 < T ∧ ∀ T₁ : ℝ, ∃ τ ∈ Set.Icc T₁ (T₁ + T), ∃ z : ℂ,
      ‖z - (ρ + (τ : ℂ) * I)‖ < r ∧ dirichletPolyOf S a z = 0 := by
  classical
  set P : Finset ℕ := S.biUnion Nat.primeFactors with hPdef
  have hP : ∀ p ∈ P, p.Prime := fun p hp => by
    obtain ⟨n, _, hn⟩ := mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hn
  set W : ℝ := ∑ n ∈ S, ‖a n‖ * ((n : ℝ) ^ (r - ρ.re) * (ArithmeticFunction.cardFactors n : ℝ)) with hW
  have hW0 : 0 ≤ W := sum_nonneg fun n _ => by positivity
  obtain ⟨D, hD⟩ := exists_nat_gt (40 * (P.card : ℝ) * W ^ 2 / μ ^ 2)
  have hDpos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hsmall : 10 * (P.card : ℝ) / ((D : ℝ) + 1) * W ^ 2 < μ ^ 2 / 4 := by
    have h1 : 40 * (P.card : ℝ) * W ^ 2 / μ ^ 2 < (D : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [div_mul_eq_mul_div, div_lt_iff₀ hDpos]
    nlinarith
  have hRpos : (0 : ℝ) < radicalOf P := by exact_mod_cast radicalOf_pos hP
  set T : ℝ := 4 * ((D : ℝ) + 1) * (radicalOf P : ℝ) ^ (D + 1) * ((exponentBox P D).card : ℝ) + 1 with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨T, hT0, fun T₁ => ?_⟩
  obtain ⟨τ, hτ, hret⟩ := exists_height_phase_return_window D hP (fun _ => 0) (fun _ => 1)
    (fun _ _ => zero_le_one) (T := T) (by rw [hT]; linarith) T₁
  simp only [sub_zero, one_mul, sum_const, nsmul_eq_mul, mul_one] at hret
  set η : ℝ := 5 * (P.card : ℝ) / ((D : ℝ) + 1) with hη
  have hη0 : 0 ≤ η := by positivity
  have hterm : ∀ p ∈ P, 1 - Real.cos (τ * Real.log p) ≤ η := by
    intro p hp
    have h1 := single_le_sum (s := P) (f := fun p : ℕ => 1 - Real.cos (τ * Real.log (p : ℝ)))
      (fun q _ => by linarith [Real.cos_le_one (τ * Real.log q)]) hp
    exact h1.trans hret
  set δ : ℝ := Real.sqrt (2 * η) with hδ
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ ^ 2 = 2 * η := Real.sq_sqrt (by positivity)
  have hprime : ∀ p ∈ P, ‖phase τ p - 1‖ ≤ δ := by
    intro p hp
    have hsq := norm_phase_sub_one_sq τ (hP p hp).pos
    have h1 := hterm p hp
    have h2 : ‖phase τ p - 1‖ ^ 2 ≤ δ ^ 2 := by
      rw [hsq, hδsq]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ0 (by norm_num)).mp h2
  have hWδ : W * δ < μ / 2 := by
    have hsq : (W * δ) ^ 2 < (μ / 2) ^ 2 := by
      have h1 : (W * δ) ^ 2 = 10 * (P.card : ℝ) / ((D : ℝ) + 1) * W ^ 2 := by
        rw [mul_pow, hδsq, hη]
        ring
      rw [h1]
      have h2 : (μ / 2) ^ 2 = μ ^ 2 / 4 := by ring
      rw [h2]
      exact hsmall
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  set F := dirichletPolyOf S a with hF
  have hFd : Differentiable ℂ F := differentiable_dirichletPolyOf hS a
  set G : ℂ → ℂ := fun s => F (s + (τ : ℂ) * I) with hG
  have hGd : Differentiable ℂ G := hFd.comp (differentiable_id.add_const _)
  have hclose : ∀ s, ‖s - ρ‖ ≤ r → ‖G s - F s‖ ≤ W * δ := by
    intro s hs
    have hre : ρ.re - r ≤ s.re := by
      have h1 := Complex.abs_re_le_norm (s - ρ)
      rw [Complex.sub_re] at h1
      have h2 := (abs_le.mp (h1.trans hs)).1
      linarith
    have hexp : ∀ n ∈ S, a n * ((n : ℝ) : ℂ) ^ (-(s + (τ : ℂ) * I)) - a n * ((n : ℝ) : ℂ) ^ (-s) =
        a n * ((n : ℝ) : ℂ) ^ (-s) * (phase τ n - 1) := by
      intro n hn
      rw [cpow_translate (hS n hn)]
      ring
    simp only [hG, hF, dirichletPolyOf]
    rw [← sum_sub_distrib, sum_congr rfl hexp, hW, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    have hn1 := hS n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    have hcpow : ‖((n : ℝ) : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (r - ρ.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have hphase : ‖phase τ n - 1‖ ≤ (ArithmeticFunction.cardFactors n : ℝ) * δ :=
      norm_phase_sub_one_le hn1 fun p hp hd => hprime p (mem_biUnion.mpr
        ⟨n, hn, Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩⟩)
    rw [norm_mul, norm_mul]
    calc ‖a n‖ * ‖((n : ℝ) : ℂ) ^ (-s)‖ * ‖phase τ n - 1‖
        ≤ ‖a n‖ * (n : ℝ) ^ (r - ρ.re) * ((ArithmeticFunction.cardFactors n : ℝ) * δ) := by gcongr
      _ = _ := by ring
  have hcenter : ‖G ρ‖ < μ / 2 := by
    have h1 := hclose ρ (by simp [hr.le])
    rw [hρ, sub_zero] at h1
    linarith
  have hcirc : ∀ z, ‖z - ρ‖ = r → μ / 2 ≤ ‖G z‖ := by
    intro z hz
    have h1 := hclose z hz.le
    have h2 := hcircle z hz
    have h3 : ‖F z‖ ≤ ‖G z‖ + ‖G z - F z‖ := by
      have := norm_sub_le (G z) (G z - F z)
      simpa using this
    linarith
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_norm_center_lt hGd hr (half_pos hμ) hcenter hcirc
  refine ⟨τ, hτ, z + (τ : ℂ) * I, ?_, hz0⟩
  have : z + (τ : ℂ) * I - (ρ + (τ : ℂ) * I) = z - ρ := by ring
  rw [this]
  exact hz

end GaloisForLFunctions.RigidArithmeticOfCuts
