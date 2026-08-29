import Mathlib.Tactic

/-!
# Functional-projective limits in a finite-dimensional jet space

A family of functions on an upper half-plane whose translates are approximated, to order `L` on every
compact tube, by the evaluations of coefficient vectors in one fixed finite-dimensional space, and
whose modulus survives at height `S^{-M}` with `M < L`, has a nonzero functional-projective limit
along a subsequence: normalising by the maximum coefficient norm puts the coefficient vectors on the
unit sphere of a finite-dimensional space, whose compactness produces the limit, and the jet error is
killed because `L > M`.

The evaluation is packaged abstractly: any linear evaluation of coefficient vectors that is bounded
on compact tubes works, so the same theorem covers polynomial jets, exponential-polynomial jets, and
any other finite jet carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- **A finite jet carrier.**  A linear evaluation of coefficient vectors, bounded on every compact
tube. -/
structure JetEval (ι : Type*) [Fintype ι] where
  /-- The evaluation of a coefficient vector as a function. -/
  ev : (ι → ℂ) → ℂ → ℂ
  /-- Homogeneity in the coefficient vector. -/
  map_smul : ∀ (a : ℂ) (c : ι → ℂ) (z : ℂ), ev (a • c) z = a * ev c z
  /-- Additivity in the coefficient vector. -/
  map_sub : ∀ (c d : ι → ℂ) (z : ℂ), ev (c - d) z = ev c z - ev d z
  /-- A tube bound linear in the coefficient norm. -/
  bound : ∀ Rad : ℝ, 0 < Rad → ∃ Θ : ℝ, 0 ≤ Θ ∧ ∀ (c : ι → ℂ) (z : ℂ), ‖z‖ ≤ Rad →
    ‖ev c z‖ ≤ Θ * ‖c‖

/-- **The functional-projective limit in a finite jet carrier.** -/
theorem exists_jet_projective_limit {r : ℕ} {ι : Type*} [Fintype ι] (E : JetEval ι)
    {L M : ℕ} {C : ℝ} (hC : 0 < C) (hML : M < L)
    (R : Fin r → ℂ → ℂ) (S : ℕ → ℝ) (hS : Tendsto S atTop atTop)
    (coeff : Fin r → ℕ → (ι → ℂ))
    (happrox : ∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad → ∃ (K : ℝ) (N : ℕ), ∀ n, N ≤ n → ∀ z : ℂ,
      ‖z‖ ≤ Rad → ‖R j (z + (S n : ℂ) * Complex.I) - E.ev (coeff j n) z‖ ≤ K * (S n) ^ (-(L : ℝ)))
    (hsurv : ∀ᶠ n in atTop, ∃ j, C * (S n) ^ (-(M : ℝ)) ≤ ‖R j ((S n : ℂ) * Complex.I)‖) :
    ∃ (ψ : ℕ → ℕ) (ρ : ℕ → ℝ) (W : Fin r → (ι → ℂ)),
      StrictMono ψ ∧ (∀ n, 0 < ρ (ψ n)) ∧ (∃ j, W j ≠ 0) ∧
      ∀ j : Fin r, ∀ Rad : ℝ, 0 < Rad →
        TendstoUniformlyOn
          (fun n z => ((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I))
          (fun z => E.ev (W j) z) atTop (Metric.closedBall (0 : ℂ) Rad) := by
  classical
  set V : ℕ → (Fin r → ι → ℂ) := fun n j => coeff j n with hVdef
  set ρ : ℕ → ℝ := fun n => ‖V n‖ with hρdef
  have hρeq : ∀ n, ρ n = ‖V n‖ := fun n => rfl
  obtain ⟨Θ₁, hΘ₁0, hΘ₁⟩ := E.bound 1 one_pos
  choose K₁ N₁ hKN₁ using fun j => happrox j 1 one_pos
  set K : ℝ := ∑ j, |K₁ j| with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hKle : ∀ j, K₁ j ≤ K := by
    intro j
    calc K₁ j ≤ |K₁ j| := le_abs_self _
      _ ≤ K := Finset.single_le_sum (fun i _ => abs_nonneg (K₁ i)) (Finset.mem_univ j)
  set N₀ : ℕ := ∑ j, N₁ j with hN₀def
  have hNle : ∀ j, N₁ j ≤ N₀ := fun j =>
    Finset.single_le_sum (fun i _ => Nat.zero_le (N₁ i)) (Finset.mem_univ j)
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
  set Θ' : ℝ := max Θ₁ 1 with hΘ'def
  have hΘ'1 : (1 : ℝ) ≤ Θ' := le_max_right _ _
  have hΘ'0 : (0 : ℝ) < Θ' := by linarith
  have hkey : ∀ᶠ n in atTop, 1 ≤ S n ∧ C / (2 * Θ') * (S n) ^ (-(M : ℝ)) ≤ ρ n := by
    filter_upwards [hsurv, hS.eventually_ge_atTop 1, eventually_ge_atTop N₀,
      hKS.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < C / 2))] with n hn hn1 hnN hnsmall
    refine ⟨hn1, ?_⟩
    obtain ⟨j, hj⟩ := hn
    have hSn0 : (0 : ℝ) < S n := by linarith
    have happ := hKN₁ j n (le_trans (hNle j) hnN) 0 (by simp)
    rw [zero_add] at happ
    have hev : ‖E.ev (coeff j n) 0‖ ≤ Θ' * ρ n := by
      have h1 := hΘ₁ (coeff j n) 0 (by simp)
      have h2 : ‖coeff j n‖ ≤ ρ n := by
        rw [hρeq]
        exact norm_le_pi_norm (V n) j
      have h3 : Θ₁ * ‖coeff j n‖ ≤ Θ' * ρ n :=
        mul_le_mul (le_max_left _ _) h2 (norm_nonneg _) hΘ'0.le
      linarith
    have htri : ‖R j ((S n : ℂ) * Complex.I)‖ ≤ Θ' * ρ n + K₁ j * (S n) ^ (-(L : ℝ)) := by
      have hns := norm_sub_norm_le (R j ((S n : ℂ) * Complex.I)) (E.ev (coeff j n) 0)
      linarith [happ, hev]
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
    -- `C X ≤ Θ' ρ + (C/2) X` gives `ρ ≥ (C/(2Θ')) X`
    have hhalf : C / 2 * (S n) ^ (-(M : ℝ)) ≤ Θ' * ρ n := by
      linarith [hj, htri, hKterm, hprod]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hhalf, hΘ'0]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hkey
  have hSge : ∀ n, n₀ ≤ n → 1 ≤ S n := fun n hn => (hn₀ n hn).1
  have hρpos : ∀ n, n₀ ≤ n → 0 < ρ n := by
    intro n hn
    have h1 := (hn₀ n hn).2
    have hSn : (0 : ℝ) < S n := by linarith [hSge n hn]
    have hMpos : (0 : ℝ) < (S n) ^ (-(M : ℝ)) := Real.rpow_pos_of_pos hSn _
    have : (0 : ℝ) < C / (2 * Θ') := by positivity
    nlinarith [h1, hMpos]
  set U : ℕ → (Fin r → ι → ℂ) :=
    fun n => if 0 < ρ n then ((ρ n : ℂ))⁻¹ • V n else 0 with hUdef
  have hUnorm : ∀ n, n₀ ≤ n → ‖U n‖ = 1 := by
    intro n hn
    have hp := hρpos n hn
    rw [hUdef]
    simp only [if_pos hp]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, ← hρeq n,
      inv_mul_cancel₀ (ne_of_gt hp)]
  have hUmem : ∀ n, U n ∈ Metric.closedBall (0 : Fin r → ι → ℂ) 1 := by
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
    (isCompact_closedBall (0 : Fin r → ι → ℂ) 1).tendsto_subseq hUmem
  set ψ : ℕ → ℕ := fun n => φ (n + n₀) with hψdef
  have hψmono : StrictMono ψ := fun a b hab => hφ (by omega)
  have hψge : ∀ n, n₀ ≤ ψ n := by
    intro n
    have h := hφ.le_apply (x := n + n₀)
    simp only [hψdef]
    omega
  have hψlim : Tendsto (fun n => U (ψ n)) atTop (nhds W) :=
    hφlim.comp (tendsto_add_atTop_nat n₀)
  have hWnorm : ‖W‖ = 1 := by
    have h1 : Tendsto (fun n => ‖U (ψ n)‖) atTop (nhds ‖W‖) :=
      (continuous_norm.tendsto W).comp hψlim
    have h2 : Tendsto (fun n => ‖U (ψ n)‖) atTop (nhds 1) :=
      Tendsto.congr (fun n => (hUnorm (ψ n) (hψge n)).symm) tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hWne : ∃ j, W j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hW0 : W = 0 := funext hcon
    rw [hW0, norm_zero] at hWnorm
    exact zero_ne_one hWnorm
  refine ⟨ψ, ρ, W, hψmono, fun n => hρpos (ψ n) (hψge n), hWne, ?_⟩
  intro j Rad hRad
  obtain ⟨K₂, N₂, hKN₂⟩ := happrox j Rad hRad
  obtain ⟨Θ₂, hΘ₂0, hΘ₂⟩ := E.bound Rad hRad
  set Aterm : ℕ → ℝ := fun n => 2 * Θ' / C * K₂ * (S (ψ n)) ^ ((M : ℝ) - (L : ℝ)) with hAdef
  set Bterm : ℕ → ℝ := fun n => Θ₂ * ‖U (ψ n) - W‖ with hBdef
  have hAlim : Tendsto Aterm atTop (nhds 0) := by
    have h1 : Tendsto (fun n => (S (ψ n)) ^ ((M : ℝ) - (L : ℝ))) atTop (nhds 0) :=
      hSpow.comp hψmono.tendsto_atTop
    have h2 := h1.const_mul (2 * Θ' / C * K₂)
    rwa [mul_zero] at h2
  have hBlim : Tendsto Bterm atTop (nhds 0) := by
    have h1 : Tendsto (fun n => ‖U (ψ n) - W‖) atTop (nhds 0) := by
      rw [← tendsto_sub_nhds_zero_iff] at hψlim
      exact tendsto_zero_iff_norm_tendsto_zero.mp hψlim
    have h2 := h1.const_mul Θ₂
    rwa [mul_zero] at h2
  have hsum : Tendsto (fun n => Aterm n + Bterm n) atTop (nhds 0) := by
    have h := hAlim.add hBlim
    rwa [add_zero] at h
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
  have happ := hKN₂ (ψ n) hnN₂ z hzn
  have hMpos : (0 : ℝ) < (S (ψ n)) ^ (-(M : ℝ)) := Real.rpow_pos_of_pos hSn0 _
  have hρlow : C / (2 * Θ') * (S (ψ n)) ^ (-(M : ℝ)) ≤ ρ (ψ n) := (hn₀ (ψ n) (hψge n)).2
  have hinv : (ρ (ψ n))⁻¹ ≤ 2 * Θ' / C * (S (ψ n)) ^ ((M : ℝ)) := by
    have hlowpos : (0 : ℝ) < C / (2 * Θ') * (S (ψ n)) ^ (-(M : ℝ)) := by positivity
    have h1 : (ρ (ψ n))⁻¹ ≤ (C / (2 * Θ') * (S (ψ n)) ^ (-(M : ℝ)))⁻¹ := inv_anti₀ hlowpos hρlow
    refine le_trans h1 (le_of_eq ?_)
    rw [mul_inv, inv_div, Real.rpow_neg hSn0.le, inv_inv]
  have hterm1 : ‖((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I)
      - ((ρ (ψ n) : ℂ))⁻¹ * E.ev (coeff j (ψ n)) z‖ ≤ Aterm n := by
    rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have hnn : (0 : ℝ) ≤ K₂ * (S (ψ n)) ^ (-(L : ℝ)) := le_trans (norm_nonneg _) happ
    have hstep : (ρ (ψ n))⁻¹ * ‖R j (z + (S (ψ n) : ℂ) * Complex.I) - E.ev (coeff j (ψ n)) z‖
        ≤ (ρ (ψ n))⁻¹ * (K₂ * (S (ψ n)) ^ (-(L : ℝ))) :=
      mul_le_mul_of_nonneg_left happ (by positivity)
    have hstep2 : (ρ (ψ n))⁻¹ * (K₂ * (S (ψ n)) ^ (-(L : ℝ)))
        ≤ (2 * Θ' / C * (S (ψ n)) ^ ((M : ℝ))) * (K₂ * (S (ψ n)) ^ (-(L : ℝ))) :=
      mul_le_mul_of_nonneg_right hinv hnn
    have hcollapse : (2 * Θ' / C * (S (ψ n)) ^ ((M : ℝ))) * (K₂ * (S (ψ n)) ^ (-(L : ℝ)))
        = Aterm n := by
      have hmul : (S (ψ n)) ^ ((M : ℝ)) * (S (ψ n)) ^ (-(L : ℝ))
          = (S (ψ n)) ^ ((M : ℝ) - (L : ℝ)) := by
        rw [← Real.rpow_add hSn0, ← sub_eq_add_neg]
      rw [hAdef]
      calc (2 * Θ' / C * (S (ψ n)) ^ ((M : ℝ))) * (K₂ * (S (ψ n)) ^ (-(L : ℝ)))
          = 2 * Θ' / C * K₂ * ((S (ψ n)) ^ ((M : ℝ)) * (S (ψ n)) ^ (-(L : ℝ))) := by ring
        _ = 2 * Θ' / C * K₂ * (S (ψ n)) ^ ((M : ℝ) - (L : ℝ)) := by rw [hmul]
    linarith [hstep, hstep2, hcollapse.le, hcollapse.ge]
  have hUval : U (ψ n) j = ((ρ (ψ n) : ℂ))⁻¹ • coeff j (ψ n) := by
    rw [hUdef]
    simp only [if_pos hpos, Pi.smul_apply, hVdef]
  have hterm2 : ‖((ρ (ψ n) : ℂ))⁻¹ * E.ev (coeff j (ψ n)) z - E.ev (W j) z‖ ≤ Bterm n := by
    have hrw : ((ρ (ψ n) : ℂ))⁻¹ * E.ev (coeff j (ψ n)) z - E.ev (W j) z
        = E.ev (U (ψ n) j - W j) z := by
      rw [E.map_sub, hUval, E.map_smul]
    rw [hrw, hBdef]
    refine le_trans (hΘ₂ _ z hzn) ?_
    refine mul_le_mul_of_nonneg_left ?_ hΘ₂0
    have hpi := norm_le_pi_norm (U (ψ n) - W) j
    simpa using hpi
  rw [Complex.dist_eq]
  calc ‖E.ev (W j) z - ((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I)‖
      = ‖(((ρ (ψ n) : ℂ))⁻¹ * R j (z + (S (ψ n) : ℂ) * Complex.I)
          - ((ρ (ψ n) : ℂ))⁻¹ * E.ev (coeff j (ψ n)) z)
        + (((ρ (ψ n) : ℂ))⁻¹ * E.ev (coeff j (ψ n)) z - E.ev (W j) z)‖ := by
        rw [norm_sub_rev]
        congr 1
        ring
    _ ≤ Aterm n + Bterm n := le_trans (norm_add_le _ _) (add_le_add hterm1 hterm2)
    _ < ε := hnε

end GaloisForLFunctions.HTGeometry
