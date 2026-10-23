import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheKroneckerRankDichotomy
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The zeros of an exponential polynomial recur

An **exponential polynomial** `F(s) = Σ_j c_j e^{λ_j s}` with finitely many real frequencies
(`expPoly`) is almost periodic in height with finitely many frequencies; finite Dirichlet
polynomials `Σ_{n ≤ N} a_n n^{−s}` are the case `λ = −log n`, of any Kronecker rank. Its zeros
**recur** (`expPoly_zero_recurs`): every zero `ρ` of a nonzero `F` has, for every `ε` and every
height, a zero within `ε` of `ρ + iτ` for some larger `τ`. Three steps:

* *simultaneous approximation* (`exists_large_almost_period`): there are arbitrarily large `τ`
  with `|e^{iλ_jτ} − 1| < η` for all `j`, because the orbit `k ↦ (e^{iλ_j T k})_j` in a compact
  torus has two close points;
* *translation is uniformly small* (`norm_expPoly_translate_sub_le`) on a disk for such `τ`;
* *zeros persist under small perturbation* (`exists_zero_of_near`): if `|F| ≥ m` on a circle around
  a zero of `F` and `|g − F| < m/2` on the disk, then `g` has a zero inside, by the maximum
  modulus principle for `1/g`.

Hence every zero configuration cut out by a nonzero exponential polynomial is vertically recurrent
(`verticallyRecurrent_of_expPoly`), and its Hodge defect is `0` or `∞`
(`expPoly_pontryagin_dichotomy`): a finite nonzero number of off-line zeros needs infinitely many
frequencies. The periodic case (`verticallyRecurrent_of_periodic`, the zeros of a curve) is rank
one; here the rank is arbitrary but finite.
-/

open Complex Metric Filter Topology Set
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- **Zeros persist under small perturbation.** If `F` vanishes at `ρ`, `|F| ≥ m` on the circle of
radius `r` around `ρ`, and `|g − F| < m/2` on the closed disk, then `g` vanishes in the open disk. -/
theorem exists_zero_of_near {F g : ℂ → ℂ} (hg : Differentiable ℂ g) {ρ : ℂ} {r m : ℝ}
    (hr : 0 < r) (hρ : F ρ = 0) (hm : ∀ z ∈ sphere ρ r, m ≤ ‖F z‖)
    (hclose : ∀ z ∈ closedBall ρ r, ‖g z - F z‖ < m / 2) : ∃ z ∈ ball ρ r, g z = 0 := by
  by_contra hno
  push Not at hno
  have hm0 : 0 < m := by
    have := hclose ρ (mem_closedBall_self hr.le)
    rw [hρ, sub_zero] at this
    linarith [norm_nonneg (g ρ)]
  -- on the circle `|g| > m/2`
  have hsph : ∀ z ∈ sphere ρ r, m / 2 < ‖g z‖ := fun z hz => by
    have h1 := hm z hz
    have h2 := hclose z (sphere_subset_closedBall hz)
    have h3 : ‖F z‖ ≤ ‖g z‖ + ‖g z - F z‖ := by
      calc ‖F z‖ = ‖g z - (g z - F z)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hne : ∀ z ∈ closedBall ρ r, g z ≠ 0 := fun z hz => by
    rcases eq_or_lt_of_le (mem_closedBall.mp hz) with h | h
    · have := hsph z (mem_sphere.mpr h)
      intro h0; rw [h0, norm_zero] at this; linarith
    · exact hno z (mem_ball.mpr h)
  have hcl : closure (ball ρ r) = closedBall ρ r := closure_ball ρ hr.ne'
  have hd : DiffContOnCl ℂ (fun z => (g z)⁻¹) (ball ρ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [hcl]
    exact (hg.differentiableOn).inv hne
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (C := 2 / m) (fun z hz => by
      rw [frontier_ball ρ hr.ne'] at hz
      have := hsph z hz
      rw [norm_inv]
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      linarith) (subset_closure (mem_ball_self hr))
  have hρg : ‖g ρ‖ < m / 2 := by
    have := hclose ρ (mem_closedBall_self hr.le)
    rwa [hρ, sub_zero] at this
  have hgρ : 0 < ‖g ρ‖ := norm_pos_iff.mpr (hne ρ (mem_closedBall_self hr.le))
  rw [norm_inv, inv_le_comm₀ hgρ (by positivity), inv_div] at hmax
  linarith

/-- **Simultaneous almost periods.** For finitely many real frequencies there are arbitrarily
large `τ` with `|e^{iλ_jτ} − 1| < η` for every `j`. -/
theorem exists_large_almost_period {r : ℕ} (w : Fin r → ℝ) {η : ℝ} (hη : 0 < η) (T₀ : ℝ) :
    ∃ τ > T₀, ∀ j, ‖exp (((w j * τ : ℝ) : ℂ) * I) - 1‖ < η := by
  set T₁ : ℝ := |T₀| + 1 with hT₁
  have hT₁0 : 0 < T₁ := by positivity
  set x : ℕ → (Fin r → ℂ) := fun k j => exp (((w j * (T₁ * k) : ℝ) : ℂ) * I)
  have hx : ∀ k, x k ∈ closedBall (0 : Fin r → ℂ) 1 := fun k => by
    rw [mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    simp only [x, Complex.norm_exp_ofReal_mul_I, le_refl]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin r → ℂ) 1).tendsto_subseq hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (η / 2) (by positivity)
  have hd : dist (x (φ (N + 1))) (x (φ N)) < η := by
    have h1 := hN (N + 1) (by omega)
    have h2 := hN N le_rfl
    simp only [Function.comp_apply] at h1 h2
    calc dist (x (φ (N + 1))) (x (φ N)) ≤ dist (x (φ (N + 1))) a + dist (x (φ N)) a :=
          dist_triangle_right _ _ _
      _ < η / 2 + η / 2 := add_lt_add h1 h2
      _ = η := by ring
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨T₁ * ((φ (N + 1) - φ N : ℕ) : ℝ), ?_, fun j => ?_⟩
  · have : (1 : ℝ) ≤ ((φ (N + 1) - φ N : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have : T₀ < T₁ := by rw [hT₁]; linarith [le_abs_self T₀]
    nlinarith
  · have hj : ‖x (φ (N + 1)) j - x (φ N) j‖ < η := by
      have := norm_le_pi_norm (x (φ (N + 1)) - x (φ N)) j
      rw [← dist_eq_norm] at this
      exact lt_of_le_of_lt this hd
    have hsplit : x (φ (N + 1)) j - x (φ N) j =
        x (φ N) j * (exp (((w j * (T₁ * ((φ (N + 1) - φ N : ℕ) : ℝ)) : ℝ) : ℂ) * I) - 1) := by
      simp only [x, mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      rw [Nat.cast_sub hlt.le]
      push_cast
      ring
    rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] at hj
    exact hj

/-- An exponential polynomial `Σ_j c_j e^{λ_j s}` with real frequencies. -/
def expPoly {r : ℕ} (c : Fin r → ℂ) (w : Fin r → ℝ) (s : ℂ) : ℂ := ∑ j, c j * exp (w j * s)

theorem differentiable_expPoly {r : ℕ} (c : Fin r → ℂ) (w : Fin r → ℝ) :
    Differentiable ℂ (expPoly c w) := by
  have : expPoly c w = fun s => ∑ j, c j * exp (w j * s) := rfl
  rw [this]
  fun_prop

/-- On `|s| ≤ R` the height translate differs from `F` by at most
`Σ_j |c_j| e^{|λ_j| R} |e^{iλ_jτ} − 1|`. -/
theorem norm_expPoly_translate_sub_le {r : ℕ} (c : Fin r → ℂ) (w : Fin r → ℝ) (τ : ℝ) {R : ℝ}
    {s : ℂ} (hs : ‖s‖ ≤ R) :
    ‖expPoly c w (s + I * τ) - expPoly c w s‖ ≤
      ∑ j, ‖c j‖ * Real.exp (|w j| * R) * ‖exp (((w j * τ : ℝ) : ℂ) * I) - 1‖ := by
  have hterm : ∀ j, c j * exp (w j * (s + I * τ)) - c j * exp (w j * s) =
      c j * exp (w j * s) * (exp (((w j * τ : ℝ) : ℂ) * I) - 1) := fun j => by
    rw [mul_add, Complex.exp_add]
    push_cast
    ring_nf
  rw [expPoly, expPoly, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => hterm j]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul]
  gcongr
  rw [Complex.norm_exp, Complex.re_ofReal_mul]
  refine Real.exp_le_exp.mpr ?_
  calc w j * s.re ≤ |w j| * |s.re| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ |w j| * R := by gcongr; exact (Complex.abs_re_le_norm s).trans hs

/-- **The zeros of an exponential polynomial recur.** Every zero `ρ` of a nonzero exponential
polynomial has, for every `ε > 0` and every `T₀`, a zero within `ε` of `ρ + iτ` for some
`τ > T₀`. -/
theorem expPoly_zero_recurs {r : ℕ} (c : Fin r → ℂ) (w : Fin r → ℝ)
    (hne : ∃ s, expPoly c w s ≠ 0) {ρ : ℂ} (hρ : expPoly c w ρ = 0) {ε : ℝ} (hε : 0 < ε)
    (T₀ : ℝ) : ∃ τ > T₀, ∃ ρ', expPoly c w ρ' = 0 ∧ ‖ρ' - (ρ + I * τ)‖ < ε := by
  set F := expPoly c w
  have hF := differentiable_expPoly c w
  -- the zero `ρ` is isolated
  have hiso : ∀ᶠ z in 𝓝[≠] ρ, F z ≠ 0 := by
    rcases (hF.analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨s, hs⟩ := hne
      have hA : AnalyticOnNhd ℂ F univ := fun z _ => hF.analyticAt z
      have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ρ) h
        (mem_univ s)
      exact hs this
    · exact h
  obtain ⟨r₀, hr₀, hr₀F⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hiso)
  set ρr : ℝ := min ε r₀ / 2 with hρr
  have hρr0 : 0 < ρr := by positivity
  have hρrε : ρr < ε := by have := min_le_left ε r₀; linarith
  have hρrr₀ : ρr < r₀ := by have := min_le_right ε r₀; linarith
  -- `|F|` has a positive minimum `m` on the circle of radius `ρr`
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere ρ ρr).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρr0.le) (continuous_norm.comp hF.continuous).continuousOn
  set m := ‖F z₀‖ with hm
  have hm0 : 0 < m := by
    refine norm_pos_iff.mpr (hr₀F ?_ ?_)
    · rw [mem_sphere.mp hz₀]; exact hρrr₀
    · intro h
      rw [Set.mem_singleton_iff.mp h, mem_sphere, dist_self] at hz₀
      linarith
  -- choose an almost period with total error `< m/2` on the closed disk
  set R : ℝ := ‖ρ‖ + ρr
  set K : ℝ := ∑ j, ‖c j‖ * Real.exp (|w j| * R) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => by positivity
  set η : ℝ := m / (2 * (K + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨τ, hτ, hτj⟩ := exists_large_almost_period w hη0 T₀
  have hclose : ∀ z ∈ closedBall ρ ρr, ‖F (z + I * τ) - F z‖ < m / 2 := fun z hz => by
    have hzR : ‖z‖ ≤ R := by
      have := mem_closedBall.mp hz
      calc ‖z‖ = ‖ρ + (z - ρ)‖ := by ring_nf
        _ ≤ ‖ρ‖ + ‖z - ρ‖ := norm_add_le _ _
        _ ≤ R := by rw [← dist_eq_norm]; linarith
    refine lt_of_le_of_lt (norm_expPoly_translate_sub_le c w τ hzR) ?_
    calc ∑ j, ‖c j‖ * Real.exp (|w j| * R) * ‖exp (((w j * τ : ℝ) : ℂ) * I) - 1‖
        ≤ ∑ j, ‖c j‖ * Real.exp (|w j| * R) * η :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hτj j).le (by positivity)
      _ = K * η := by rw [hK, Finset.sum_mul]
      _ < (K + 1) * η := by linarith
      _ = m / 2 := by rw [hη]; field_simp
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_near (F := F) (g := fun z => F (z + I * τ))
    (hF.comp (differentiable_id.add_const _)) hρr0 hρ (fun z hz => hmin hz) hclose
  refine ⟨τ, hτ, z + I * τ, hz0, ?_⟩
  rw [show z + I * τ - (ρ + I * τ) = z - ρ by ring, ← dist_eq_norm]
  exact lt_trans (mem_ball.mp hz) hρrε

/-- **Zero sets of exponential polynomials are vertically recurrent.** -/
theorem verticallyRecurrent_of_expPoly (Z : ZeroConfig) {r : ℕ} (c : Fin r → ℂ)
    (w : Fin r → ℝ) (hne : ∃ s, expPoly c w s ≠ 0)
    (hZ : ∀ s, s ∈ Z.carrier ↔ expPoly c w s = 0) : VerticallyRecurrent Z := by
  intro ρ hρ ε hε T
  obtain ⟨τ, hτ, ρ', hρ', hclose⟩ := expPoly_zero_recurs c w hne ((hZ ρ).mp hρ)
    (lt_min hε one_pos) (T - ρ.im + 1)
  refine ⟨ρ', (hZ ρ').mpr hρ', ?_, ?_⟩
  · have h := (Complex.abs_im_le_norm _).trans_lt (hclose.trans_le (min_le_right ε 1))
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at h
    have := (abs_lt.mp h).1
    linarith
  · have h := (Complex.abs_re_le_norm _).trans_lt (hclose.trans_le (min_le_left ε 1))
    simpa [Complex.sub_re, Complex.add_re, Complex.mul_re] using h

/-- **The Kronecker-rank dichotomy for exponential polynomials.** A tempered zero configuration cut
out by a nonzero exponential polynomial has Hodge defect `0` or `∞`. -/
theorem expPoly_pontryagin_dichotomy (Z : ZeroConfig) (hT : TemperedConfig Z) {r : ℕ}
    (c : Fin r → ℂ) (w : Fin r → ℝ) (hne : ∃ s, expPoly c w s ≠ 0)
    (hZ : ∀ s, s ∈ Z.carrier ↔ expPoly c w s = 0) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermNegIndex (zeroGram Z f) = 0) ∨
    ∀ n : ℕ, ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (zeroGram Z f) :=
  recurrent_pontryagin_dichotomy Z hT (verticallyRecurrent_of_expPoly Z c w hne hZ)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
