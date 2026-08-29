import GaloisForLFunctions.HTGeometry.PolynomialProjectiveBoundary

/-!
# The polynomial projective boundary of a one-phase quasianalytic field

Let `E` be a coefficient field of functions on an upper half-plane whose nonzero elements, together
with their reciprocals, grow at most polynomially on upper vertical tubes, and let `u` be a phase
that stays on a fixed circle.  A finite tuple of elements of `E(u)` is normalised by clearing a
common denominator and dividing by the polynomial gcd; the residual tuple is primitive, so it
satisfies a Bezout identity over `E[U]`.

* **Bezout survival.**  The cofactors of a Bezout identity are phase polynomials with coefficients
  of polynomial growth, hence of polynomial growth themselves; evaluating the identity at the height
  `i S` therefore forces one residual component to be at least `C · S^{-M}`.
* **Finite-order survival forces a polynomial jet.**  Translated polynomial jets of a fixed degree
  bound, normalised by the maximum of their coefficients, live on the unit sphere of a fixed
  finite-dimensional space; a subsequence converges to a nonzero polynomial tuple, and the jet error
  `O(S^{-L})` with `L > M` is killed by the normalisation.

Together with the terminal one-point boundary of a polynomial tuple this gives the two-stage carrier
`E(u) → ℂ[z] → ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Polynomial

/-! ## Polynomial growth of a phase polynomial -/

/-- **A phase polynomial with coefficients of polynomial growth has polynomial growth.**  The phase
`u` stays on a fixed circle, so only the finitely many coefficients contribute to the rate. -/
theorem norm_phasePoly_le {N : ℕ} (a : ℕ → ℝ → ℂ) (u : ℝ → ℂ) {B C : ℝ} {M : ℕ}
    (hC0 : 0 ≤ C)
    (hB : ∀ S : ℝ, 1 ≤ S → ‖u S‖ ≤ B)
    (ha : ∀ k, k < N → ∀ S : ℝ, 1 ≤ S → ‖a k S‖ ≤ C * S ^ M) :
    ∀ S : ℝ, 1 ≤ S →
      ‖∑ k ∈ Finset.range N, a k S * u S ^ k‖ ≤ ((N : ℝ) * C * (max B 1) ^ N) * S ^ M := by
  intro S hS
  refine le_trans (norm_sum_le _ _) ?_
  have hmax1 : (1 : ℝ) ≤ max B 1 := le_max_right _ _
  have hterm : ∀ k ∈ Finset.range N, ‖a k S * u S ^ k‖ ≤ C * (max B 1) ^ N * S ^ M := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [norm_mul, norm_pow]
    have h1 : ‖a k S‖ ≤ C * S ^ M := ha k hk S hS
    have h2 : ‖u S‖ ^ k ≤ (max B 1) ^ N := by
      calc ‖u S‖ ^ k ≤ (max B 1) ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) (le_trans (hB S hS) (le_max_left _ _)) k
        _ ≤ (max B 1) ^ N := pow_le_pow_right₀ hmax1 (le_of_lt hk)
    have hS0 : (0 : ℝ) ≤ S := by linarith
    calc ‖a k S‖ * ‖u S‖ ^ k ≤ (C * S ^ M) * (max B 1) ^ N :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = C * (max B 1) ^ N * S ^ M := by ring
  calc ∑ k ∈ Finset.range N, ‖a k S * u S ^ k‖
      ≤ ∑ _k ∈ Finset.range N, C * (max B 1) ^ N * S ^ M := Finset.sum_le_sum hterm
    _ = (N : ℝ) * C * (max B 1) ^ N * S ^ M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-! ## Common denominator and gcd normalization -/

/-- **The gcd normalization of a phase tuple.**  Over the Euclidean ring `K[X]` a nonzero tuple
factors as its gcd times a primitive residual tuple, and the residual tuple satisfies a Bezout
identity. -/
theorem exists_primitive_normalization {K : Type*} [Field K] {r : ℕ} (P : Fin r → Polynomial K)
    (hne : ∃ j, P j ≠ 0) :
    ∃ (g : Polynomial K) (Q : Fin r → Polynomial K), g ≠ 0 ∧ (∀ j, P j = g * Q j) ∧
      ∃ A : Fin r → Polynomial K, ∑ j, A j * Q j = 1 := by
  classical
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range P))).principal
  have hmem : ∀ j, P j ∈ Ideal.span (Set.range P) := fun j => Ideal.subset_span ⟨j, rfl⟩
  have hdvd : ∀ j, g ∣ P j := by
    intro j
    have h := hmem j
    rw [hg] at h
    exact Ideal.mem_span_singleton.mp h
  choose Q hQ using hdvd
  have hg0 : g ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := hne
    exact hj (by rw [hQ j, h, zero_mul])
  refine ⟨g, Q, hg0, hQ, ?_⟩
  have hgmem : g ∈ Ideal.span (Set.range P) := by
    rw [hg]
    exact Ideal.mem_span_singleton_self g
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgmem
  refine ⟨c, ?_⟩
  have hfactor : g * (∑ j, c j * Q j) = g * 1 := by
    calc g * (∑ j, c j * Q j) = ∑ j, c j * (g * Q j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, c j * P j := Finset.sum_congr rfl fun j _ => by rw [hQ j]
      _ = g := hc
      _ = g * 1 := (mul_one g).symm
  exact mul_left_cancel₀ hg0 hfactor

/-! ## Bezout survival -/

/-- **Bezout survival.**  If a tuple satisfies a Bezout identity whose cofactors have polynomial
growth, then at every height some component of the tuple is at least an inverse power. -/
theorem exists_bezout_survival {r : ℕ} (A R : Fin r → ℝ → ℂ) {C₁ : ℝ} {M : ℕ} (hC₁ : 0 < C₁)
    (hbez : ∀ S : ℝ, 1 ≤ S → ∑ j, A j S * R j S = 1)
    (hA : ∀ S : ℝ, 1 ≤ S → ∀ j, ‖A j S‖ ≤ C₁ * S ^ M) :
    ∀ S : ℝ, 1 ≤ S → ∃ j, ((r : ℝ) * C₁)⁻¹ * (S ^ M)⁻¹ ≤ ‖R j S‖ := by
  intro S hS
  have hS0 : (0 : ℝ) < S := by linarith
  have hSM : (0 : ℝ) < S ^ M := by positivity
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin r)) with hemp | hnon
    · exfalso
      have h0 := hbez S hS
      rw [hemp, Finset.sum_empty] at h0
      exact zero_ne_one h0
    · exact hnon
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => ‖R j S‖) hne
  refine ⟨j₀, ?_⟩
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    obtain ⟨j, -⟩ := hne
    have : 0 < r := j.pos
    exact_mod_cast this
  have hchain : (1 : ℝ) ≤ (r : ℝ) * C₁ * S ^ M * ‖R j₀ S‖ := by
    have h1 : (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
    rw [h1, ← hbez S hS]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin r)),
        ‖A j S * R j S‖ ≤ C₁ * S ^ M * ‖R j₀ S‖ := by
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hA S hS j) (hj₀ j (Finset.mem_univ j)) (norm_nonneg _) (by positivity)
    calc ∑ j, ‖A j S * R j S‖ ≤ ∑ _j : Fin r, C₁ * S ^ M * ‖R j₀ S‖ :=
          Finset.sum_le_sum hterm
      _ = (r : ℝ) * C₁ * S ^ M * ‖R j₀ S‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hpos : (0 : ℝ) < (r : ℝ) * C₁ * S ^ M := by positivity
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hC₁ne : C₁ ≠ 0 := ne_of_gt hC₁
  have hSMne : S ^ M ≠ 0 := ne_of_gt hSM
  have hform : ((r : ℝ) * C₁)⁻¹ * (S ^ M)⁻¹ = 1 / ((r : ℝ) * C₁ * S ^ M) := by
    field_simp
  rw [hform, div_le_iff₀ hpos]
  linarith [hchain]

/-! ## Translated polynomial jets -/

/-- **Translated polynomial jets along a height sequence.**  Each upper translate of `b` agrees, on
every compact tube, with the evaluation of one polynomial of degree at most `d`, up to `K · S n^{-L}`
with a constant depending only on the tube radius. -/
structure TranslatedJets (b : ℂ → ℂ) (S : ℕ → ℝ) (d L : ℕ) where
  /-- The jet polynomial at each height. -/
  poly : ℕ → Polynomial ℂ
  /-- The degree bound is independent of the height. -/
  degree_le : ∀ n, (poly n).natDegree ≤ d
  /-- The jet approximates the translate to order `L` on every tube. -/
  approx : ∀ Rad : ℝ, 0 < Rad → ∃ (K : ℝ) (N : ℕ), ∀ n, N ≤ n → ∀ z : ℂ, ‖z‖ ≤ Rad →
    ‖b (z + (S n : ℂ) * Complex.I) - (poly n).eval z‖ ≤ K * (S n) ^ (-(L : ℝ))


/-! ## The polynomial functional-projective limit -/

/-- **Finite-order survival forces a polynomial jet.**  Given translated polynomial jets of a fixed
degree bound with error `O(S^{-L})` and a survival bound `C · S^{-M}` with `M < L`, a subsequence of
the normalised translates converges, uniformly on every closed ball, to a nonzero polynomial tuple of
degree at most `d`. -/
theorem exists_polynomial_projective_limit
    {r d L M : ℕ} {C : ℝ} (hC : 0 < C) (hML : M < L)
    (R : Fin r → ℂ → ℂ) (S : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (J : ∀ j, TranslatedJets (R j) S d L)
    (hsurv : ∀ᶠ n in atTop, ∃ j, C * (S n) ^ (-(M : ℝ)) ≤ ‖R j ((S n : ℂ) * Complex.I)‖) :
    ∃ (ψ : ℕ → ℕ) (ρ : ℕ → ℝ) (H : Fin r → Polynomial ℂ),
      StrictMono ψ ∧ (∀ n, 0 < ρ (ψ n)) ∧ (∃ j, H j ≠ 0) ∧ (∀ j, (H j).natDegree ≤ d) ∧
      ∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad →
        TendstoUniformlyOn
          (fun n z => ((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I))
          (fun z => (H j).eval z) atTop (Metric.closedBall (0 : ℂ) Rad) := by
  classical
  set V : ℕ → (Fin r × Fin (d + 1) → ℂ) :=
    fun n p => ((J p.1).poly n).coeff (p.2 : ℕ) with hVdef
  set ρ : ℕ → ℝ := fun n => ‖V n‖ with hρdef
  have hρeq : ∀ n, ρ n = ‖V n‖ := fun n => rfl
  have hρ0 : ∀ n, 0 ≤ ρ n := fun n => norm_nonneg _
  -- uniform jet constants on the unit tube
  choose K₁ N₁ hKN₁ using fun j => (J j).approx 1 one_pos
  set K : ℝ := ∑ j, |K₁ j| with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hKle : ∀ j, K₁ j ≤ K := by
    intro j
    calc K₁ j ≤ |K₁ j| := le_abs_self _
      _ ≤ K := Finset.single_le_sum (fun i _ => abs_nonneg (K₁ i)) (Finset.mem_univ j)
  set N₀ : ℕ := ∑ j, N₁ j with hN₀def
  have hNle : ∀ j, N₁ j ≤ N₀ := fun j =>
    Finset.single_le_sum (fun i _ => Nat.zero_le (N₁ i)) (Finset.mem_univ j)
  -- the jet error is negligible against the survival floor
  have hSpow : Tendsto (fun n => (S n) ^ ((M : ℝ) - (L : ℝ))) atTop (nhds 0) := by
    have hpos : (0 : ℝ) < (L : ℝ) - (M : ℝ) := by
      have : (M : ℝ) < (L : ℝ) := by exact_mod_cast hML
      linarith
    have h1 : Tendsto (fun x : ℝ => x ^ (-((L : ℝ) - (M : ℝ)))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hpos
    have h2 : (fun x : ℝ => x ^ (-((L : ℝ) - (M : ℝ)))) = fun x : ℝ => x ^ ((M : ℝ) - (L : ℝ)) := by
      funext x
      congr 1
      ring
    rw [h2] at h1
    exact h1.comp hS
  have hKS : Tendsto (fun n => K * (S n) ^ ((M : ℝ) - (L : ℝ))) atTop (nhds 0) := by
    have h := hSpow.const_mul K
    rwa [mul_zero] at h
  have hkey : ∀ᶠ n in atTop, 1 ≤ S n ∧ C / 2 * (S n) ^ (-(M : ℝ)) ≤ ρ n := by
    filter_upwards [hsurv, hS.eventually_ge_atTop 1, eventually_ge_atTop N₀,
      hKS.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < C / 2))] with n hn hn1 hnN hnsmall
    refine ⟨hn1, ?_⟩
    obtain ⟨j, hj⟩ := hn
    have hSn0 : (0 : ℝ) < S n := by linarith
    have happ := hKN₁ j n (le_trans (hNle j) hnN) 0 (by simp)
    rw [zero_add] at happ
    have heval : ((J j).poly n).eval 0 = ((J j).poly n).coeff 0 :=
      (Polynomial.coeff_zero_eq_eval_zero _).symm
    rw [heval] at happ
    have hcoeff : ‖((J j).poly n).coeff 0‖ ≤ ρ n := by
      have hpi : ‖V n (j, (0 : Fin (d + 1)))‖ ≤ ‖V n‖ := norm_le_pi_norm _ _
      rw [hρeq]
      simpa [hVdef] using hpi
    have htri : ‖R j ((S n : ℂ) * Complex.I)‖ ≤ ρ n + K₁ j * (S n) ^ (-(L : ℝ)) := by
      have hns := norm_sub_norm_le (R j ((S n : ℂ) * Complex.I)) (((J j).poly n).coeff 0)
      linarith [happ, hcoeff]
    have hLpos : (0 : ℝ) < (S n) ^ (-(L : ℝ)) := Real.rpow_pos_of_pos hSn0 _
    have hMpos : (0 : ℝ) < (S n) ^ (-(M : ℝ)) := Real.rpow_pos_of_pos hSn0 _
    have hKterm : K₁ j * (S n) ^ (-(L : ℝ)) ≤ K * (S n) ^ (-(L : ℝ)) :=
      mul_le_mul_of_nonneg_right (hKle j) hLpos.le
    have hsplit : (S n) ^ (-(L : ℝ)) = (S n) ^ ((M : ℝ) - (L : ℝ)) * (S n) ^ (-(M : ℝ)) := by
      rw [← Real.rpow_add hSn0]
      congr 1
      ring
    have hKsplit : K * (S n) ^ (-(L : ℝ))
        = K * (S n) ^ ((M : ℝ) - (L : ℝ)) * (S n) ^ (-(M : ℝ)) := by
      rw [hsplit]
      ring
    rw [hKsplit] at hKterm
    have hprod : K * (S n) ^ ((M : ℝ) - (L : ℝ)) * (S n) ^ (-(M : ℝ))
        < C / 2 * (S n) ^ (-(M : ℝ)) := mul_lt_mul_of_pos_right hnsmall hMpos
    linarith [hj, htri, hKterm, hprod]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hkey
  have hSge : ∀ n, n₀ ≤ n → 1 ≤ S n := fun n hn => (hn₀ n hn).1
  have hρpos : ∀ n, n₀ ≤ n → 0 < ρ n := by
    intro n hn
    have h1 := (hn₀ n hn).2
    have hSn : (0 : ℝ) < S n := by linarith [hSge n hn]
    have hMpos : (0 : ℝ) < (S n) ^ (-(M : ℝ)) := Real.rpow_pos_of_pos hSn _
    nlinarith [h1, hMpos, hC]
  -- normalised coefficient vectors on the unit ball
  set U : ℕ → (Fin r × Fin (d + 1) → ℂ) :=
    fun n => if 0 < ρ n then ((ρ n : ℂ))⁻¹ • V n else 0 with hUdef
  have hUnorm : ∀ n, n₀ ≤ n → ‖U n‖ = 1 := by
    intro n hn
    have hp := hρpos n hn
    rw [hUdef]
    simp only [if_pos hp]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, ← hρeq n,
      inv_mul_cancel₀ (ne_of_gt hp)]
  have hUmem : ∀ n, U n ∈ Metric.closedBall (0 : Fin r × Fin (d + 1) → ℂ) 1 := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases h : 0 < ρ n
    · rw [hUdef]
      simp only [if_pos h]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h, ← hρeq n,
        inv_mul_cancel₀ (ne_of_gt h)]
    · rw [hUdef]
      simp only [if_neg h, norm_zero]
      norm_num
  obtain ⟨W, -, φ, hφ, hφlim⟩ :=
    (isCompact_closedBall (0 : Fin r × Fin (d + 1) → ℂ) 1).tendsto_subseq hUmem
  set ψ : ℕ → ℕ := fun n => φ (n + n₀) with hψdef
  have hψmono : StrictMono ψ := by
    intro a b hab
    exact hφ (by omega)
  have hψge : ∀ n, n₀ ≤ ψ n := by
    intro n
    have h := hφ.le_apply (x := n + n₀)
    simp only [hψdef]
    omega
  have hψlim : Tendsto (fun n => U (ψ n)) atTop (nhds W) :=
    hφlim.comp (tendsto_add_atTop_nat n₀)
  -- the limit vector has norm one
  have hWnorm : ‖W‖ = 1 := by
    have h1 : Tendsto (fun n => ‖U (ψ n)‖) atTop (nhds ‖W‖) :=
      (continuous_norm.tendsto W).comp hψlim
    have h2 : Tendsto (fun n => ‖U (ψ n)‖) atTop (nhds 1) := by
      refine Tendsto.congr (fun n => (hUnorm (ψ n) (hψge n)).symm) tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- the limit polynomial tuple
  set H : Fin r → Polynomial ℂ :=
    fun j => ∑ k : Fin (d + 1), Polynomial.monomial (k : ℕ) (W (j, k)) with hHdef
  have hHdeg : ∀ j, (H j).natDegree ≤ d := by
    intro j
    rw [hHdef]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    exact le_trans (Polynomial.natDegree_monomial_le _) (by omega)
  have hHcoeff : ∀ (j : Fin r) (k : Fin (d + 1)), (H j).coeff (k : ℕ) = W (j, k) := by
    intro j k
    rw [hHdef, Polynomial.finset_sum_coeff, Finset.sum_eq_single k]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [Polynomial.coeff_monomial, if_neg]
      intro h
      exact hb (Fin.ext h)
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hHeval : ∀ (j : Fin r) (z : ℂ),
      (H j).eval z = ∑ k : Fin (d + 1), W (j, k) * z ^ (k : ℕ) := by
    intro j z
    rw [hHdef, Polynomial.eval_finset_sum]
    exact Finset.sum_congr rfl fun k _ => Polynomial.eval_monomial
  have hHne : ∃ j, H j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hW0 : W = 0 := by
      funext p
      obtain ⟨j, k⟩ := p
      have h1 := hHcoeff j k
      rw [hcon j] at h1
      simp only [Polynomial.coeff_zero] at h1
      exact h1.symm
    rw [hW0, norm_zero] at hWnorm
    exact zero_ne_one hWnorm
  refine ⟨ψ, ρ, H, hψmono, fun n => hρpos (ψ n) (hψge n), hHne, hHdeg, ?_⟩
  intro j Rad hRad
  obtain ⟨K₂, N₂, hKN₂⟩ := (J j).approx Rad hRad
  -- the two error terms
  set Aterm : ℕ → ℝ := fun n => 2 / C * K₂ * (S (ψ n)) ^ ((M : ℝ) - (L : ℝ)) with hAdef
  set Bterm : ℕ → ℝ :=
    fun n => ((d : ℝ) + 1) * ‖U (ψ n) - W‖ * (max Rad 1) ^ d with hBdef
  have hSψ : Tendsto (fun n => S (ψ n)) atTop atTop := hS.comp hψmono.tendsto_atTop
  have hAlim : Tendsto Aterm atTop (nhds 0) := by
    have h1 : Tendsto (fun n => (S (ψ n)) ^ ((M : ℝ) - (L : ℝ))) atTop (nhds 0) :=
      hSpow.comp hψmono.tendsto_atTop
    have h2 := h1.const_mul (2 / C * K₂)
    rw [mul_zero] at h2
    exact h2
  have hBlim : Tendsto Bterm atTop (nhds 0) := by
    have h1 : Tendsto (fun n => ‖U (ψ n) - W‖) atTop (nhds 0) := by
      rw [← tendsto_sub_nhds_zero_iff] at hψlim
      exact tendsto_zero_iff_norm_tendsto_zero.mp hψlim
    have h2 := (h1.const_mul ((d : ℝ) + 1)).mul_const ((max Rad 1) ^ d)
    rw [mul_zero, zero_mul] at h2
    exact h2
  have hsum : Tendsto (fun n => Aterm n + Bterm n) atTop (nhds 0) := by
    have := hAlim.add hBlim
    rwa [add_zero] at this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hsum.eventually (gt_mem_nhds hε),
    hψmono.tendsto_atTop.eventually (eventually_ge_atTop N₂)] with n hnε hnN₂
  intro z hz
  have hzn : ‖z‖ ≤ Rad := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact hz
  have hpos := hρpos (ψ n) (hψge n)
  have hSn : (1 : ℝ) ≤ S (ψ n) := hSge (ψ n) (hψge n)
  have hSn0 : (0 : ℝ) < S (ψ n) := by linarith
  -- jet approximation at this height
  have happ := hKN₂ (ψ n) hnN₂ z hzn
  have hMpos : (0 : ℝ) < (S (ψ n)) ^ (-(M : ℝ)) := Real.rpow_pos_of_pos hSn0 _
  have hρlow : C / 2 * (S (ψ n)) ^ (-(M : ℝ)) ≤ ρ (ψ n) := (hn₀ (ψ n) (hψge n)).2
  -- term one
  have hinv : (ρ (ψ n))⁻¹ ≤ 2 / C * (S (ψ n)) ^ ((M : ℝ)) := by
    have hlowpos : (0 : ℝ) < C / 2 * (S (ψ n)) ^ (-(M : ℝ)) := by positivity
    have h1 : (ρ (ψ n))⁻¹ ≤ (C / 2 * (S (ψ n)) ^ (-(M : ℝ)))⁻¹ := inv_anti₀ hlowpos hρlow
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_inv, inv_div, Real.rpow_neg hSn0.le, inv_inv]
  have hterm1 : ‖((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I)
      - ((ρ (ψ n) : ℂ))⁻¹ * ((J j).poly (ψ n)).eval z‖ ≤ Aterm n := by
    rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hnn : (0 : ℝ) ≤ K₂ * (S (ψ n)) ^ (-(L : ℝ)) := le_trans (norm_nonneg _) happ
    have hstep : (ρ (ψ n))⁻¹ * ‖R j (z + (S (ψ n) : ℂ) * Complex.I)
        - ((J j).poly (ψ n)).eval z‖ ≤ (ρ (ψ n))⁻¹ * (K₂ * (S (ψ n)) ^ (-(L : ℝ))) :=
      mul_le_mul_of_nonneg_left happ (by positivity)
    have hstep2 : (ρ (ψ n))⁻¹ * (K₂ * (S (ψ n)) ^ (-(L : ℝ)))
        ≤ (2 / C * (S (ψ n)) ^ ((M : ℝ))) * (K₂ * (S (ψ n)) ^ (-(L : ℝ))) :=
      mul_le_mul_of_nonneg_right hinv hnn
    have hcollapse : (2 / C * (S (ψ n)) ^ ((M : ℝ))) * (K₂ * (S (ψ n)) ^ (-(L : ℝ)))
        = Aterm n := by
      rw [hAdef]
      have : (S (ψ n)) ^ ((M : ℝ)) * (S (ψ n)) ^ (-(L : ℝ))
          = (S (ψ n)) ^ ((M : ℝ) - (L : ℝ)) := by
        rw [← Real.rpow_add hSn0, ← sub_eq_add_neg]
      calc (2 / C * (S (ψ n)) ^ ((M : ℝ))) * (K₂ * (S (ψ n)) ^ (-(L : ℝ)))
          = 2 / C * K₂ * ((S (ψ n)) ^ ((M : ℝ)) * (S (ψ n)) ^ (-(L : ℝ))) := by ring
        _ = 2 / C * K₂ * (S (ψ n)) ^ ((M : ℝ) - (L : ℝ)) := by rw [this]
    linarith [hstep, hstep2, hcollapse.le, hcollapse.ge]
  -- term two
  have hUval : ∀ k : Fin (d + 1),
      U (ψ n) (j, k) = ((ρ (ψ n) : ℂ))⁻¹ * ((J j).poly (ψ n)).coeff (k : ℕ) := by
    intro k
    rw [hUdef]
    simp only [if_pos hpos, Pi.smul_apply, smul_eq_mul, hVdef]
  have hjeteval : ((J j).poly (ψ n)).eval z
      = ∑ k : Fin (d + 1), ((J j).poly (ψ n)).coeff (k : ℕ) * z ^ (k : ℕ) := by
    rw [Polynomial.eval_eq_sum_range' (n := d + 1) (by
      have := (J j).degree_le (ψ n)
      omega)]
    exact (Fin.sum_univ_eq_sum_range (fun k => ((J j).poly (ψ n)).coeff k * z ^ k) (d + 1)).symm
  have hterm2 : ‖((ρ (ψ n) : ℂ))⁻¹ * ((J j).poly (ψ n)).eval z - (H j).eval z‖ ≤ Bterm n := by
    rw [hjeteval, hHeval, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (norm_sum_le _ _) ?_
    have hb : ∀ k ∈ (Finset.univ : Finset (Fin (d + 1))),
        ‖((ρ (ψ n) : ℂ))⁻¹ * (((J j).poly (ψ n)).coeff (k : ℕ) * z ^ (k : ℕ))
          - W (j, k) * z ^ (k : ℕ)‖ ≤ ‖U (ψ n) - W‖ * (max Rad 1) ^ d := by
      intro k _
      have hrw : ((ρ (ψ n) : ℂ))⁻¹ * (((J j).poly (ψ n)).coeff (k : ℕ) * z ^ (k : ℕ))
          - W (j, k) * z ^ (k : ℕ)
          = (U (ψ n) (j, k) - W (j, k)) * z ^ (k : ℕ) := by
        rw [hUval k]
        ring
      rw [hrw, norm_mul, norm_pow]
      have h1 : ‖U (ψ n) (j, k) - W (j, k)‖ ≤ ‖U (ψ n) - W‖ := by
        have := norm_le_pi_norm (U (ψ n) - W) (j, k)
        simpa using this
      have h2 : ‖z‖ ^ (k : ℕ) ≤ (max Rad 1) ^ d := by
        calc ‖z‖ ^ (k : ℕ) ≤ (max Rad 1) ^ (k : ℕ) :=
              pow_le_pow_left₀ (norm_nonneg _) (le_trans hzn (le_max_left _ _)) _
          _ ≤ (max Rad 1) ^ d := pow_le_pow_right₀ (le_max_right _ _) (by omega)
      exact mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    calc ∑ k : Fin (d + 1), ‖((ρ (ψ n) : ℂ))⁻¹ * (((J j).poly (ψ n)).coeff (k : ℕ) * z ^ (k : ℕ))
            - W (j, k) * z ^ (k : ℕ)‖
        ≤ ∑ _k : Fin (d + 1), ‖U (ψ n) - W‖ * (max Rad 1) ^ d := Finset.sum_le_sum hb
      _ = Bterm n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hBdef]
          push_cast
          ring
  rw [Complex.dist_eq]
  calc ‖(H j).eval z - ((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I)‖
      = ‖(((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I)
          - ((ρ (ψ n) : ℂ))⁻¹ * ((J j).poly (ψ n)).eval z)
        + (((ρ (ψ n) : ℂ))⁻¹ * ((J j).poly (ψ n)).eval z - (H j).eval z)‖ := by
        rw [norm_sub_rev]
        congr 1
        ring
    _ ≤ Aterm n + Bterm n := le_trans (norm_add_le _ _) (add_le_add hterm1 hterm2)
    _ < ε := hnε


/-! ## The carrier chain -/

/-- The survival hypothesis of the boundary theorem is the conclusion of Bezout survival read along
a height sequence. -/
theorem survival_of_bezout {r : ℕ} (A : Fin r → ℝ → ℂ) (R : Fin r → ℂ → ℂ)
    (S : ℕ → ℝ) (hS : Tendsto S atTop atTop) {C₁ : ℝ} {M : ℕ} (hC₁ : 0 < C₁)
    (hbez : ∀ T : ℝ, 1 ≤ T → ∑ j, A j T * R j ((T : ℂ) * Complex.I) = 1)
    (hA : ∀ T : ℝ, 1 ≤ T → ∀ j, ‖A j T‖ ≤ C₁ * T ^ M) :
    ∀ᶠ n in atTop, ∃ j, ((r : ℝ) * C₁)⁻¹ * (S n) ^ (-(M : ℝ))
      ≤ ‖R j ((S n : ℂ) * Complex.I)‖ := by
  have hbase := exists_bezout_survival A (fun j T => R j ((T : ℂ) * Complex.I)) hC₁ hbez hA
  filter_upwards [hS.eventually_ge_atTop 1] with n hn
  obtain ⟨j, hj⟩ := hbase (S n) hn
  refine ⟨j, ?_⟩
  have hSn0 : (0 : ℝ) ≤ S n := by linarith
  have hpow : (S n) ^ (-(M : ℝ)) = ((S n) ^ M)⁻¹ := by
    rw [Real.rpow_neg hSn0, Real.rpow_natCast]
  rw [hpow]
  exact hj

/-- The maximal degree of a nonzero polynomial tuple is realised by a nonvanishing top
coefficient. -/
theorem exists_coeff_sup_ne_zero {r : ℕ} (H : Fin r → Polynomial ℂ) (hne : ∃ j, H j ≠ 0) :
    ∃ j, (H j).coeff (Finset.univ.sup fun i => (H i).natDegree) ≠ 0 := by
  classical
  set dH : ℕ := Finset.univ.sup fun i => (H i).natDegree with hdH
  obtain ⟨j₀, hj₀⟩ := hne
  by_contra hcon
  push_neg at hcon
  have hle : (H j₀).natDegree ≤ dH :=
    Finset.le_sup (f := fun i => (H i).natDegree) (Finset.mem_univ j₀)
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- the supremum is positive, so it is attained at a nonzero polynomial
    have hpos : 0 < dH := lt_of_le_of_lt (Nat.zero_le _) hlt
    have hnonempty : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j₀, Finset.mem_univ j₀⟩
    obtain ⟨j₁, -, hj₁⟩ := Finset.exists_mem_eq_sup Finset.univ hnonempty
      (fun i => (H i).natDegree)
    have hHj₁ : H j₁ ≠ 0 := by
      intro h
      rw [h] at hj₁
      simp only [Polynomial.natDegree_zero] at hj₁
      omega
    exact (coeff_top_ne_zero_of_natDegree_eq hHj₁ hj₁.symm) (hcon j₁)
  · exact (coeff_top_ne_zero_of_natDegree_eq hj₀ heq) (hcon j₀)

/-- **A quasianalytic one-phase field has a polynomial projective boundary.**  A finite tuple with
translated polynomial jets of a fixed degree bound and Bezout survival has, after a subsequence, a
nonzero polynomial functional-projective limit, and that polynomial tuple has in turn a one-point
terminal projective boundary with a nonzero limit vector.  This is the carrier chain
`E(u) → ℂ[z] → ℂ`. -/
theorem onePhase_polynomial_projective_boundary
    {r d L M : ℕ} {C : ℝ} (hC : 0 < C) (hML : M < L)
    (R : Fin r → ℂ → ℂ) (S : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (J : ∀ j, TranslatedJets (R j) S d L)
    (hsurv : ∀ᶠ n in atTop, ∃ j, C * (S n) ^ (-(M : ℝ)) ≤ ‖R j ((S n : ℂ) * Complex.I)‖) :
    ∃ (ψ : ℕ → ℕ) (ρ : ℕ → ℝ) (H : Fin r → Polynomial ℂ) (dH : ℕ),
      StrictMono ψ ∧ (∀ n, 0 < ρ (ψ n)) ∧ (∀ j, (H j).natDegree ≤ d) ∧
      (∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad →
        TendstoUniformlyOn
          (fun n z => ((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I))
          (fun z => (H j).eval z) atTop (Metric.closedBall (0 : ℂ) Rad)) ∧
      (∃ j, (H j).coeff dH ≠ 0) ∧
      (∀ j : Fin r, ∀ Rad : ℝ,
        TendstoUniformlyOn
          (fun (T : ℝ) z => (H j).eval (z + (T : ℂ) * Complex.I) / ((T : ℂ) * Complex.I) ^ dH)
          (fun _ => (H j).coeff dH) atTop (Metric.closedBall (0 : ℂ) Rad)) := by
  classical
  obtain ⟨ψ, ρ, H, hψ, hρ, hHne, hHdeg, hconv⟩ :=
    exists_polynomial_projective_limit hC hML R S hS J hsurv
  have hlast : ∀ j : Fin r, ∀ Rad : ℝ,
      TendstoUniformlyOn
        (fun (T : ℝ) z => (H j).eval (z + (T : ℂ) * Complex.I)
          / ((T : ℂ) * Complex.I) ^ (Finset.univ.sup fun i => (H i).natDegree))
        (fun _ => (H j).coeff (Finset.univ.sup fun i => (H i).natDegree)) atTop
        (Metric.closedBall (0 : ℂ) Rad) := by
    intro j Rad
    have hw : Tendsto (fun T : ℝ => ‖(T : ℂ) * Complex.I‖) atTop atTop := by
      have heq : ∀ T : ℝ, ‖(T : ℂ) * Complex.I‖ = |T| := by
        intro T
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      simp only [heq]
      exact tendsto_abs_atTop_atTop
    exact tendstoUniformlyOn_translate_div_pow hw
      (Finset.le_sup (f := fun i => (H i).natDegree) (Finset.mem_univ j)) Rad
  exact ⟨ψ, ρ, H, Finset.univ.sup fun i => (H i).natDegree, hψ, hρ, hHdeg, hconv,
    exists_coeff_sup_ne_zero H hHne, hlast⟩

end GaloisForLFunctions.HTGeometry