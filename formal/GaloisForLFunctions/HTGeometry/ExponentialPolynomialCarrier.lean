import GaloisForLFunctions.HTGeometry.JetProjectiveLimit
import GaloisForLFunctions.HTGeometry.PolynomialProjectiveBoundary

/-!
# The exponential-polynomial carrier of a one-exponential, one-logarithmic phase field

The finite jet carrier of a field carrying one recurrent exponential phase `exp(β s)` and one
logarithmic phase `s^{iθ}` is the exponential-polynomial space

```text
span_ℂ {z^m exp(k β z) : 0 ≤ m ≤ D, |k| ≤ K}.
```

It is a finite jet carrier in the sense of `JetEval`, so a tuple with translated jets in it and a
surviving modulus has a nonzero functional-projective limit there.  Dividing by `(iT)^{m₀}`, where
`m₀` is the top polynomial degree of the limit, and passing to a subsequence on which every character
`exp(i k β T)` converges, removes the polynomial jet and leaves a nonzero Laurent polynomial in
`exp(β z)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- The `W`-exponent attached to an index of the symmetric window `[-K, K]`. -/
def kIdx (K : ℕ) (i : Fin (2 * K + 1)) : ℤ := (i : ℤ) - (K : ℤ)

theorem abs_kIdx_le (K : ℕ) (i : Fin (2 * K + 1)) : |kIdx K i| ≤ (K : ℤ) := by
  have hi : (i : ℕ) ≤ 2 * K := by omega
  rw [kIdx, abs_le]
  constructor <;> omega

/-- The exponential polynomial `∑_{m,k} c_{m,k} z^m exp(k β z)`. -/
noncomputable def expPolyEval (β : ℝ) (D K : ℕ) (c : Fin (D + 1) × Fin (2 * K + 1) → ℂ) (z : ℂ) :
    ℂ :=
  ∑ p : Fin (D + 1) × Fin (2 * K + 1),
    c p * z ^ (p.1 : ℕ) * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z)

theorem norm_exp_kIdx_le {β : ℝ} {K : ℕ} (i : Fin (2 * K + 1)) {Rad : ℝ} {z : ℂ} (hz : ‖z‖ ≤ Rad) :
    ‖Complex.exp ((((kIdx K i : ℝ) * β : ℝ) : ℂ) * z)‖ ≤ Real.exp ((K : ℝ) * |β| * Rad) := by
  rw [Complex.norm_exp, Complex.re_ofReal_mul]
  refine Real.exp_le_exp.mpr ?_
  have hre : |z.re| ≤ Rad := le_trans (Complex.abs_re_le_norm z) hz
  have hk : |(kIdx K i : ℝ)| ≤ (K : ℝ) := by
    have := abs_kIdx_le K i
    have hcast : |((kIdx K i : ℤ) : ℝ)| ≤ ((K : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast this
    simpa using hcast
  calc (kIdx K i : ℝ) * β * z.re ≤ |(kIdx K i : ℝ) * β * z.re| := le_abs_self _
    _ = |(kIdx K i : ℝ)| * |β| * |z.re| := by rw [abs_mul, abs_mul]
    _ ≤ (K : ℝ) * |β| * Rad := by
        have h1 : (0 : ℝ) ≤ |(kIdx K i : ℝ)| := abs_nonneg _
        have h2 : (0 : ℝ) ≤ |β| := abs_nonneg _
        have h3 : (0 : ℝ) ≤ |z.re| := abs_nonneg _
        have hRad0 : (0 : ℝ) ≤ Rad := le_trans h3 hre
        exact mul_le_mul (mul_le_mul hk le_rfl h2 (by positivity)) hre h3 (by positivity)

/-- **The exponential-polynomial jet carrier.** -/
noncomputable def expPolyJet (β : ℝ) (D K : ℕ) : JetEval (Fin (D + 1) × Fin (2 * K + 1)) where
  ev := expPolyEval β D K
  map_smul := by
    intro a c z
    rw [expPolyEval, expPolyEval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  map_sub := by
    intro c d z
    rw [expPolyEval, expPolyEval, expPolyEval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by
      simp only [Pi.sub_apply]
      ring
  bound := by
    intro Rad hRad
    refine ⟨(Fintype.card (Fin (D + 1) × Fin (2 * K + 1)) : ℝ) * (max Rad 1) ^ D
      * Real.exp ((K : ℝ) * |β| * Rad), by positivity, ?_⟩
    intro c z hz
    rw [expPolyEval]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ p ∈ (Finset.univ : Finset (Fin (D + 1) × Fin (2 * K + 1))),
        ‖c p * z ^ (p.1 : ℕ) * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z)‖
          ≤ (max Rad 1) ^ D * Real.exp ((K : ℝ) * |β| * Rad) * ‖c‖ := by
      intro p _
      rw [norm_mul, norm_mul, norm_pow]
      have h1 : ‖c p‖ ≤ ‖c‖ := norm_le_pi_norm c p
      have h2 : ‖z‖ ^ (p.1 : ℕ) ≤ (max Rad 1) ^ D := by
        calc ‖z‖ ^ (p.1 : ℕ) ≤ (max Rad 1) ^ (p.1 : ℕ) :=
              pow_le_pow_left₀ (norm_nonneg _) (le_trans hz (le_max_left _ _)) _
          _ ≤ (max Rad 1) ^ D := pow_le_pow_right₀ (le_max_right _ _) (by omega)
      have h3 := norm_exp_kIdx_le (β := β) p.2 hz
      have h4 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * |β| * Rad) := (Real.exp_pos _).le
      calc ‖c p‖ * ‖z‖ ^ (p.1 : ℕ) * ‖Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z)‖
          ≤ ‖c‖ * (max Rad 1) ^ D * Real.exp ((K : ℝ) * |β| * Rad) := by
            refine mul_le_mul (mul_le_mul h1 h2 (by positivity) (norm_nonneg _)) h3
              (norm_nonneg _) (by positivity)
        _ = (max Rad 1) ^ D * Real.exp ((K : ℝ) * |β| * Rad) * ‖c‖ := by ring
    calc ∑ p : Fin (D + 1) × Fin (2 * K + 1),
          ‖c p * z ^ (p.1 : ℕ) * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z)‖
        ≤ ∑ _p : Fin (D + 1) × Fin (2 * K + 1),
            (max Rad 1) ^ D * Real.exp ((K : ℝ) * |β| * Rad) * ‖c‖ := Finset.sum_le_sum hterm
      _ = (Fintype.card (Fin (D + 1) × Fin (2 * K + 1)) : ℝ) * (max Rad 1) ^ D
            * Real.exp ((K : ℝ) * |β| * Rad) * ‖c‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring

/-- **Finite tuples have exponential-polynomial projective limits.**  A tuple whose translates are
approximated to order `L` by exponential polynomials of fixed degree and frequency window, and whose
modulus survives at `C · S^{-M}` with `M < L`, has a nonzero functional-projective limit in the
exponential-polynomial carrier, locally uniformly. -/
theorem exists_expPoly_projective_limit {r : ℕ} (β : ℝ) (D K : ℕ)
    {L M : ℕ} {C : ℝ} (hC : 0 < C) (hML : M < L)
    (R : Fin r → ℂ → ℂ) (S : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (coeff : Fin r → ℕ → (Fin (D + 1) × Fin (2 * K + 1) → ℂ))
    (happrox : ∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad → ∃ (K₀ : ℝ) (N : ℕ), ∀ n, N ≤ n → ∀ z : ℂ,
      ‖z‖ ≤ Rad → ‖R j (z + (S n : ℂ) * Complex.I) - expPolyEval β D K (coeff j n) z‖
        ≤ K₀ * (S n) ^ (-(L : ℝ)))
    (hsurv : ∀ᶠ n in atTop, ∃ j, C * (S n) ^ (-(M : ℝ)) ≤ ‖R j ((S n : ℂ) * Complex.I)‖) :
    ∃ (ψ : ℕ → ℕ) (ρ : ℕ → ℝ) (W : Fin r → (Fin (D + 1) × Fin (2 * K + 1) → ℂ)),
      StrictMono ψ ∧ (∀ n, 0 < ρ (ψ n)) ∧ (∃ j, W j ≠ 0) ∧
      ∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad →
        TendstoUniformlyOn
          (fun n z => ((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I))
          (fun z => expPolyEval β D K (W j) z) atTop (Metric.closedBall (0 : ℂ) Rad) :=
  exists_jet_projective_limit (expPolyJet β D K) hC hML R S hS coeff happrox hsurv


/-! ## Recession removes the polynomial jet -/

/-- The unimodular character vector attached to a height. -/
noncomputable def charVec (β : ℝ) (K : ℕ) (T : ℝ) : Fin (2 * K + 1) → ℂ :=
  fun i => Complex.exp ((((kIdx K i : ℝ) * β * T : ℝ) : ℂ) * Complex.I)

theorem norm_charVec (β : ℝ) (K : ℕ) (T : ℝ) (i : Fin (2 * K + 1)) :
    ‖charVec β K T i‖ = 1 := by
  rw [charVec, Complex.norm_exp]
  simp

theorem norm_charVec_le (β : ℝ) (K : ℕ) (T : ℝ) : ‖charVec β K T‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => le_of_eq (norm_charVec β K T i)

/-- Translating the argument by `iT` factors the exponential part into the character vector. -/
theorem expPolyEval_translate (β : ℝ) (D K : ℕ) (W : Fin (D + 1) × Fin (2 * K + 1) → ℂ)
    (T : ℝ) (z : ℂ) :
    expPolyEval β D K W (z + (T : ℂ) * Complex.I)
      = ∑ p : Fin (D + 1) × Fin (2 * K + 1),
          W p * (z + (T : ℂ) * Complex.I) ^ (p.1 : ℕ)
            * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z) * charVec β K T p.2 := by
  rw [expPolyEval]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hexp : Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * (z + (T : ℂ) * Complex.I))
      = Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z) * charVec β K T p.2 := by
    rw [charVec, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- **Recession removes the polynomial jet.**  Along a subsequence of heights on which every
character converges, dividing the translate by `(iT)^{m₀}` leaves, uniformly on every closed ball,
the top-degree Laurent polynomial in `exp(β z)`. -/
theorem exists_recession_limit (β : ℝ) (D K : ℕ) (W : Fin (D + 1) × Fin (2 * K + 1) → ℂ)
    (m₀ : Fin (D + 1)) (htop : ∀ p : Fin (D + 1) × Fin (2 * K + 1),
      (m₀ : ℕ) < (p.1 : ℕ) → W p = 0)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    ∃ (χ : ℕ → ℕ) (γ : Fin (2 * K + 1) → ℂ), StrictMono χ ∧ (∀ i, ‖γ i‖ = 1) ∧
      ∀ Rad : ℝ, 0 < Rad → TendstoUniformlyOn
        (fun n z => expPolyEval β D K W (z + (T (χ n) : ℂ) * Complex.I)
          / ((T (χ n) : ℂ) * Complex.I) ^ (m₀ : ℕ))
        (fun z => ∑ i : Fin (2 * K + 1), W (m₀, i) * γ i
          * Complex.exp ((((kIdx K i : ℝ) * β : ℝ) : ℂ) * z))
        atTop (Metric.closedBall (0 : ℂ) Rad) := by
  classical
  have hmem : ∀ n : ℕ, charVec β K (T n) ∈ Metric.closedBall (0 : Fin (2 * K + 1) → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_charVec_le β K (T n)
  obtain ⟨γ, -, χ, hχ, hχlim⟩ :=
    (isCompact_closedBall (0 : Fin (2 * K + 1) → ℂ) 1).tendsto_subseq hmem
  have hγnorm : ∀ i, ‖γ i‖ = 1 := by
    intro i
    have h0 : Tendsto (fun n => charVec β K (T (χ n)) i) atTop (nhds (γ i)) :=
      ((continuous_apply i).tendsto γ).comp hχlim
    have h1 : Tendsto (fun n => ‖charVec β K (T (χ n)) i‖) atTop (nhds ‖γ i‖) := h0.norm
    have h2 : Tendsto (fun n => ‖charVec β K (T (χ n)) i‖) atTop (nhds 1) :=
      Tendsto.congr (fun n => (norm_charVec β K (T (χ n)) i).symm) tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  refine ⟨χ, γ, hχ, hγnorm, ?_⟩
  intro Rad hRad
  set Θ : ℝ := Real.exp ((K : ℝ) * |β| * Rad) with hΘdef
  have hΘ0 : 0 < Θ := Real.exp_pos _
  set Wsum : ℝ := ∑ p : Fin (D + 1) × Fin (2 * K + 1), ‖W p‖ with hWdef
  have hWsum0 : 0 ≤ Wsum := Finset.sum_nonneg fun p _ => norm_nonneg _
  have hw : Tendsto (fun n : ℕ => ‖(T (χ n) : ℂ) * Complex.I‖) atTop atTop := by
    have heq : ∀ t : ℝ, ‖(t : ℂ) * Complex.I‖ = |t| := by
      intro t
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    simp only [heq]
    exact tendsto_abs_atTop_atTop.comp (hT.comp hχ.tendsto_atTop)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set η : ℝ := ε / (2 * (Wsum + 1) * Θ) with hηdef
  have hη0 : 0 < η := by
    rw [hηdef]
    positivity
  have hpoly : ∀ m : Fin (D + 1), ∀ᶠ n in atTop, ((m : ℕ) ≤ (m₀ : ℕ) →
      ∀ z ∈ Metric.closedBall (0 : ℂ) Rad,
        ‖(if (m : ℕ) = (m₀ : ℕ) then (1 : ℂ) else 0)
          - (z + (T (χ n) : ℂ) * Complex.I) ^ (m : ℕ)
            / ((T (χ n) : ℂ) * Complex.I) ^ (m₀ : ℕ)‖ < η) := by
    intro m
    by_cases hm : (m : ℕ) ≤ (m₀ : ℕ)
    · have hdeg : ((Polynomial.X : Polynomial ℂ) ^ (m : ℕ)).natDegree ≤ (m₀ : ℕ) := by
        rw [Polynomial.natDegree_X_pow]
        exact hm
      have hunif := tendstoUniformlyOn_translate_div_pow hw hdeg Rad
      rw [Metric.tendstoUniformlyOn_iff] at hunif
      have hcoeff : ((Polynomial.X : Polynomial ℂ) ^ (m : ℕ)).coeff (m₀ : ℕ)
          = if (m : ℕ) = (m₀ : ℕ) then (1 : ℂ) else 0 := by
        rw [Polynomial.coeff_X_pow]
        by_cases hc : (m : ℕ) = (m₀ : ℕ)
        · simp [hc]
        · simp [hc, Ne.symm hc]
      filter_upwards [hunif η hη0] with n hn _ z hz
      have h1 := hn z hz
      rw [hcoeff, Complex.dist_eq] at h1
      simpa [Polynomial.eval_pow] using h1
    · exact Filter.Eventually.of_forall fun n hcon => absurd hcon hm
  filter_upwards [Filter.eventually_all.mpr hpoly,
    (tendsto_iff_norm_sub_tendsto_zero.mp hχlim).eventually
      (gt_mem_nhds hη0)] with n hnpoly hnchar
  intro z hz
  have hzn : ‖z‖ ≤ Rad := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hz
  have hlhs : expPolyEval β D K W (z + (T (χ n) : ℂ) * Complex.I)
      / ((T (χ n) : ℂ) * Complex.I) ^ (m₀ : ℕ)
      = ∑ p : Fin (D + 1) × Fin (2 * K + 1), W p
          * ((z + (T (χ n) : ℂ) * Complex.I) ^ (p.1 : ℕ)
              / ((T (χ n) : ℂ) * Complex.I) ^ (m₀ : ℕ))
          * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z) * charVec β K (T (χ n)) p.2 := by
    rw [expPolyEval_translate, Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hrhs : (∑ i : Fin (2 * K + 1), W (m₀, i) * γ i
        * Complex.exp ((((kIdx K i : ℝ) * β : ℝ) : ℂ) * z))
      = ∑ p : Fin (D + 1) × Fin (2 * K + 1), W p
          * (if (p.1 : ℕ) = (m₀ : ℕ) then (1 : ℂ) else 0)
          * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z) * γ p.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single m₀]
    · exact Finset.sum_congr rfl fun i _ => by
        simp [mul_comm, mul_assoc, mul_left_comm]
    · intro m _ hm
      refine Finset.sum_eq_zero fun i _ => ?_
      have hne : ¬ ((m : ℕ) = (m₀ : ℕ)) := fun h => hm (Fin.ext h)
      simp only [if_neg hne]
      ring
    · intro hcon
      exact absurd (Finset.mem_univ m₀) hcon
  rw [Complex.dist_eq, hlhs, hrhs, ← Finset.sum_sub_distrib]
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin (D + 1) × Fin (2 * K + 1))),
      ‖W p * (if (p.1 : ℕ) = (m₀ : ℕ) then (1 : ℂ) else 0)
          * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z) * γ p.2
        - W p * ((z + (T (χ n) : ℂ) * Complex.I) ^ (p.1 : ℕ)
            / ((T (χ n) : ℂ) * Complex.I) ^ (m₀ : ℕ))
          * Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z) * charVec β K (T (χ n)) p.2‖
        ≤ ‖W p‖ * Θ * (2 * η) := by
    intro p _
    by_cases hp : (m₀ : ℕ) < (p.1 : ℕ)
    · rw [htop p hp]
      simp only [zero_mul, sub_zero, norm_zero]
      positivity
    · push_neg at hp
      set δ : ℂ := if (p.1 : ℕ) = (m₀ : ℕ) then (1 : ℂ) else 0 with hδdef
      set f : ℂ := (z + (T (χ n) : ℂ) * Complex.I) ^ (p.1 : ℕ)
        / ((T (χ n) : ℂ) * Complex.I) ^ (m₀ : ℕ) with hfdef
      set e : ℂ := Complex.exp ((((kIdx K p.2 : ℝ) * β : ℝ) : ℂ) * z) with hedef
      have hfactor : W p * δ * e * γ p.2 - W p * f * e * charVec β K (T (χ n)) p.2
          = W p * e * (δ * γ p.2 - f * charVec β K (T (χ n)) p.2) := by ring
      rw [hfactor, norm_mul, norm_mul]
      have hebound : ‖e‖ ≤ Θ := norm_exp_kIdx_le p.2 hzn
      have hδ1 : ‖δ‖ ≤ 1 := by
        rw [hδdef]
        by_cases hc : (p.1 : ℕ) = (m₀ : ℕ) <;> simp [hc]
      have hcn : ‖charVec β K (T (χ n)) p.2‖ = 1 := norm_charVec β K (T (χ n)) p.2
      have hdf : ‖δ - f‖ < η := hnpoly p.1 hp z hz
      have hcg : ‖charVec β K (T (χ n)) p.2 - γ p.2‖ < η := by
        have hpi := norm_le_pi_norm (charVec β K (T (χ n)) - γ) p.2
        simp only [Pi.sub_apply] at hpi
        have hnc : ‖charVec β K (T (χ n)) - γ‖ < η := hnchar
        linarith [hpi, hnc]
      have hsplit : δ * γ p.2 - f * charVec β K (T (χ n)) p.2
          = (δ - f) * charVec β K (T (χ n)) p.2
            - δ * (charVec β K (T (χ n)) p.2 - γ p.2) := by ring
      have hbd : ‖δ * γ p.2 - f * charVec β K (T (χ n)) p.2‖ ≤ 2 * η := by
        rw [hsplit]
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_mul, norm_mul, hcn, mul_one]
        have h1 : ‖δ‖ * ‖charVec β K (T (χ n)) p.2 - γ p.2‖ ≤ η := by
          calc ‖δ‖ * ‖charVec β K (T (χ n)) p.2 - γ p.2‖
              ≤ 1 * η := mul_le_mul hδ1 hcg.le (norm_nonneg _) zero_le_one
            _ = η := one_mul η
        linarith [hdf.le, h1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hebound (norm_nonneg _)) hbd
        (norm_nonneg _) (by positivity)
  refine lt_of_le_of_lt (norm_sum_le _ _) ?_
  refine lt_of_le_of_lt (Finset.sum_le_sum hterm) ?_
  have hsum : (∑ p : Fin (D + 1) × Fin (2 * K + 1), ‖W p‖ * Θ * (2 * η))
      = Wsum * Θ * (2 * η) := by
    rw [hWdef, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [hsum]
  have hΘne : Θ ≠ 0 := ne_of_gt hΘ0
  have hW1 : Wsum + 1 ≠ 0 := by positivity
  have hkey : Wsum * Θ * (2 * η) = ε * (Wsum / (Wsum + 1)) := by
    rw [hηdef]
    field_simp
  rw [hkey]
  have hfrac : Wsum / (Wsum + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  nlinarith [hfrac, hε, hWsum0]


/-! ## The carrier chain and the terminal rank -/

/-- The greatest polynomial degree occurring in a nonzero coefficient array. -/
theorem exists_top_degree {D K : ℕ} (W : Fin (D + 1) × Fin (2 * K + 1) → ℂ) (hW : W ≠ 0) :
    ∃ m₀ : Fin (D + 1), (∃ i, W (m₀, i) ≠ 0) ∧
      ∀ p : Fin (D + 1) × Fin (2 * K + 1), (m₀ : ℕ) < (p.1 : ℕ) → W p = 0 := by
  classical
  set T : Finset (Fin (D + 1)) :=
    Finset.univ.filter (fun m => ∃ i : Fin (2 * K + 1), W (m, i) ≠ 0) with hTdef
  have hTne : T.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T with hemp | h
    · exfalso
      refine hW (funext fun p => ?_)
      by_contra hp
      have hmem : p.1 ∈ T :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.2, by simpa using hp⟩⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · exact h
  refine ⟨T.max' hTne, ?_, ?_⟩
  · have hmem := T.max'_mem hTne
    exact (Finset.mem_filter.mp hmem).2
  · intro p hp
    by_contra hne
    have hmem : p.1 ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.2, by simpa using hne⟩⟩
    have hle := T.le_max' p.1 hmem
    have : (p.1 : ℕ) ≤ ((T.max' hTne : Fin (D + 1)) : ℕ) := hle
    omega

/-- **The carrier chain.**  A finite tuple with translated exponential-polynomial jets and a
surviving modulus has a nonzero functional-projective limit in `ℂ[z, exp(βz), exp(-βz)]`, and that
limit recedes to a nonzero Laurent polynomial in `exp(βz)`. -/
theorem expPoly_carrier_chain {r : ℕ} (β : ℝ) (D K : ℕ)
    {L M : ℕ} {C : ℝ} (hC : 0 < C) (hML : M < L)
    (R : Fin r → ℂ → ℂ) (S : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (coeff : Fin r → ℕ → (Fin (D + 1) × Fin (2 * K + 1) → ℂ))
    (happrox : ∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad → ∃ (K₀ : ℝ) (N : ℕ), ∀ n, N ≤ n → ∀ z : ℂ,
      ‖z‖ ≤ Rad → ‖R j (z + (S n : ℂ) * Complex.I) - expPolyEval β D K (coeff j n) z‖
        ≤ K₀ * (S n) ^ (-(L : ℝ)))
    (hsurv : ∀ᶠ n in atTop, ∃ j, C * (S n) ^ (-(M : ℝ)) ≤ ‖R j ((S n : ℂ) * Complex.I)‖)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    ∃ (ψ : ℕ → ℕ) (ρ : ℕ → ℝ) (W : Fin r → (Fin (D + 1) × Fin (2 * K + 1) → ℂ))
      (j₀ : Fin r) (m₀ : Fin (D + 1)) (χ : ℕ → ℕ) (γ : Fin (2 * K + 1) → ℂ),
      StrictMono ψ ∧ (∀ n, 0 < ρ (ψ n)) ∧ W j₀ ≠ 0 ∧
      (∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad →
        TendstoUniformlyOn
          (fun n z => ((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I))
          (fun z => expPolyEval β D K (W j) z) atTop (Metric.closedBall (0 : ℂ) Rad)) ∧
      StrictMono χ ∧ (∀ i, ‖γ i‖ = 1) ∧ (∃ i, W j₀ (m₀, i) * γ i ≠ 0) ∧
      (∀ Rad : ℝ, 0 < Rad → TendstoUniformlyOn
        (fun n z => expPolyEval β D K (W j₀) (z + (T (χ n) : ℂ) * Complex.I)
          / ((T (χ n) : ℂ) * Complex.I) ^ (m₀ : ℕ))
        (fun z => ∑ i : Fin (2 * K + 1), W j₀ (m₀, i) * γ i
          * Complex.exp ((((kIdx K i : ℝ) * β : ℝ) : ℂ) * z))
        atTop (Metric.closedBall (0 : ℂ) Rad)) := by
  obtain ⟨ψ, ρ, W, hψ, hρ, ⟨j₀, hj₀⟩, hconv⟩ :=
    exists_expPoly_projective_limit β D K hC hML R S hS coeff happrox hsurv
  obtain ⟨m₀, ⟨i₀, hi₀⟩, htop⟩ := exists_top_degree (W j₀) hj₀
  obtain ⟨χ, γ, hχ, hγ, hrec⟩ := exists_recession_limit β D K (W j₀) m₀ htop T hT
  refine ⟨ψ, ρ, W, j₀, m₀, χ, γ, hψ, hρ, hj₀, hconv, hχ, hγ, ⟨i₀, ?_⟩, hrec⟩
  have hγ0 : γ i₀ ≠ 0 := by
    intro h
    have := hγ i₀
    rw [h, norm_zero] at this
    exact zero_ne_one this
  exact mul_ne_zero hi₀ hγ0

/-! ## The terminal rational character rank -/

/-- **The frequency-rank composition.**  If the rank of a group relative to a subgroup is at most
`rel` and the subgroup has rank at most `δ`, the whole group has rank at most `δ + rel`. -/
theorem rank_le_of_relative_rank {M : Type*} [AddCommGroup M] (N : Submodule ℤ M)
    {δ rel : Cardinal} (hrel : Module.rank ℤ (M ⧸ N) ≤ rel) (hδ : Module.rank ℤ N ≤ δ) :
    Module.rank ℤ M ≤ δ + rel := by
  have hsplit : Module.rank ℤ (M ⧸ N) + Module.rank ℤ N = Module.rank ℤ M :=
    rank_quotient_add_rank_of_isDomain N
  rw [← hsplit, add_comm]
  exact add_le_add hδ hrel

end GaloisForLFunctions.HTGeometry
