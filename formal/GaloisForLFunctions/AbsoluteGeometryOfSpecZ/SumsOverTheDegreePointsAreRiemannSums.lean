import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheJumpFormSplitsIntoAWindowAndItsTails

/-!
# Sums over the degree points are Riemann sums

At the scale `N` the degree point `n` has the logarithmic coordinate `u_n = log(n/N)` and the mass
`1/n`, the length of the step from `u_n` to `u_{n+1}` to first order. On the window
`N < n ≤ (1 + L)N` the coordinates fill `[0, log(1 + L)]`.

* **One variable** (`tendsto_degreeSum`): for `G` continuous,
  `Σ_n G(u_n)/n → ∫_0^{log(1 + L)} G(u) du`.
* **Two variables** (`tendsto_degreePairSum`): for `Ψ` continuous on the plane,
  `Σ_m Σ_n Ψ(u_m, u_n)/(mn) → ∫_0^{log(1 + L)} ∫_0^{log(1 + L)} Ψ(u, v) dv du`.

Both are Riemann sums with mesh `1/N` in the variable `σ = n/N` (`tendsto_gridSum_interval`,
`tendsto_gridSum_square`), followed by the substitution `σ = e^u` (`integral_comp_log_div`). The
sum over the square is compared with the integral cell by cell, by uniform continuity.
-/

open Finset Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Sums on a uniform grid -/

theorem sum_Ioc_add_eq_sum_range (h : ℕ → ℝ) (N M : ℕ) :
    ∑ n ∈ Ioc N (N + M), h n = ∑ k ∈ range M, h (N + k + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (Nat.le_add_right N M), ih, Finset.sum_range_succ]

/-- Riemann sums of a continuous function on `[a, a + L]` with mesh `1/N`. -/
theorem tendsto_gridSum_interval {G : ℝ → ℝ} (hG : Continuous G) (a : ℝ) {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ range (L * N), G (a + ((k : ℝ) + 1) / N)) atTop
      (𝓝 (∫ σ in a..(a + L), G σ)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := hL'.ne'
  have hF : ContinuousOn (fun s : ℝ => G (a + L * s)) (Set.Icc 0 1) :=
    (hG.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  have hsub : Tendsto (fun N : ℕ => L * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (by omega)) tendsto_id
  have h := ((_root_.GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tendsto_riemannSum_of_continuousOn
    hF).comp hsub).const_mul (L : ℝ)
  have hint : (L : ℝ) * ∫ y in (0 : ℝ)..1, G (a + L * y) = ∫ σ in a..(a + L), G σ := by
    rw [intervalIntegral.integral_comp_add_mul (fun σ => G σ) hLne a, mul_zero, add_zero, mul_one,
      smul_eq_mul, mul_inv_cancel_left₀ hLne]
  rw [hint] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hN'.ne'
  have e1 : (L : ℝ) * (((L * N : ℕ) : ℝ))⁻¹ = (N : ℝ)⁻¹ := by
    push_cast
    field_simp
  have e2 : ∀ k : ℕ, (L : ℝ) * (((k : ℝ) + 1) / ((L * N : ℕ) : ℝ)) = ((k : ℝ) + 1) / N := fun k => by
    push_cast
    field_simp
  simp only [Function.comp_apply]
  rw [← mul_assoc, e1]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e2]

/-- **Riemann sums on a square.** For `Φ` continuous on the plane, the sums over the grid of
mesh `1/N` in `[a, a + L]²` tend to the double integral. -/
theorem tendsto_gridSum_square {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (Function.uncurry Φ)) (a : ℝ)
    (L : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2 * ∑ i ∈ range (L * N), ∑ j ∈ range (L * N),
        Φ (a + ((i : ℝ) + 1) / N) (a + ((j : ℝ) + 1) / N)) atTop
      (𝓝 (∫ σ in a..(a + L), ∫ τ in a..(a + L), Φ σ τ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : IsCompact (Set.Icc a (a + L) ×ˢ Set.Icc a (a + L)) := isCompact_Icc.prod isCompact_Icc
  have hden : (0 : ℝ) < (L : ℝ) ^ 2 + 1 := by positivity
  have hε'0 : 0 < ε / ((L : ℝ) ^ 2 + 1) := div_pos hε hden
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hΦ.continuousOn) _ hε'0
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hδ
  refine ⟨n₀ + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 n₀) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  have hNδ : 1 / (N : ℝ) < δ := by
    refine lt_of_le_of_lt ?_ hn₀
    apply one_div_le_one_div_of_le (by positivity)
    have : (n₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  -- the nodes of the grid
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, ∀ k, x k = a + (k : ℝ) / N := ⟨_, fun _ => rfl⟩
  have hx0 : x 0 = a := by rw [hx, Nat.cast_zero, zero_div, add_zero]
  have hxM : x (L * N) = a + L := by
    rw [hx]
    push_cast
    field_simp
  have hxsucc : ∀ k : ℕ, x (k + 1) = a + ((k : ℝ) + 1) / N := fun k => by
    rw [hx]
    push_cast
    ring
  have hstep : ∀ k : ℕ, x (k + 1) - x k = 1 / N := fun k => by
    rw [hx, hx]
    push_cast
    ring
  have hinv : (0 : ℝ) < 1 / N := by positivity
  have hmono : ∀ k : ℕ, x k ≤ x (k + 1) := fun k => by linarith [hstep k]
  have hmem : ∀ k, k < L * N → ∀ y ∈ Set.Icc (x k) (x (k + 1)), y ∈ Set.Icc a (a + L) := by
    intro k hk y hy
    have h1 : a ≤ x k := by
      rw [hx]
      have : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
      linarith
    have h2 : x (k + 1) ≤ a + L := by
      rw [← hxM, hx, hx]
      have hc : ((k + 1 : ℕ) : ℝ) ≤ ((L * N : ℕ) : ℝ) := by exact_mod_cast hk
      have := div_le_div_of_nonneg_right hc hN0.le
      linarith
    exact ⟨h1.trans hy.1, hy.2.trans h2⟩
  -- the double integral as a sum over the cells
  have hΦσ : ∀ σ, Continuous fun τ => Φ σ τ := fun σ =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  have hpar : ∀ c d : ℝ, Continuous fun σ => ∫ τ in c..d, Φ σ τ := fun c d =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΦ c d
  have hinner : ∀ σ, ∫ τ in a..(a + L), Φ σ τ =
      ∑ j ∈ range (L * N), ∫ τ in (x j)..(x (j + 1)), Φ σ τ := by
    intro σ
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := x) (n := L * N)
      (μ := volume) (f := fun τ => Φ σ τ) (fun k _ => (hΦσ σ).intervalIntegrable _ _)
    rw [hx0, hxM] at h
    exact h.symm
  have hcells : ∫ σ in a..(a + L), ∫ τ in a..(a + L), Φ σ τ =
      ∑ i ∈ range (L * N), ∑ j ∈ range (L * N),
        ∫ σ in (x i)..(x (i + 1)), ∫ τ in (x j)..(x (j + 1)), Φ σ τ := by
    simp_rw [hinner]
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := x) (n := L * N)
      (μ := volume)
      (f := fun σ => ∑ j ∈ range (L * N), ∫ τ in (x j)..(x (j + 1)), Φ σ τ)
      (fun k _ => (continuous_finsetSum _ fun j _ => hpar _ _).intervalIntegrable _ _)
    rw [hx0, hxM] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => (hpar _ _).intervalIntegrable _ _]
  -- each cell against its corner
  have hcell : ∀ i, i < L * N → ∀ j, j < L * N →
      |((N : ℝ)⁻¹) ^ 2 * Φ (x (i + 1)) (x (j + 1)) -
        ∫ σ in (x i)..(x (i + 1)), ∫ τ in (x j)..(x (j + 1)), Φ σ τ| ≤
        ε / ((L : ℝ) ^ 2 + 1) * ((N : ℝ)⁻¹) ^ 2 := by
    intro i hi j hj
    have hin : ∀ σ ∈ Set.Icc (x i) (x (i + 1)),
        |(∫ τ in (x j)..(x (j + 1)), Φ σ τ) - (N : ℝ)⁻¹ * Φ (x (i + 1)) (x (j + 1))| ≤
          ε / ((L : ℝ) ^ 2 + 1) * (N : ℝ)⁻¹ := by
      intro σ hσ
      have hconst : ∫ _τ in (x j)..(x (j + 1)), Φ (x (i + 1)) (x (j + 1)) =
          (N : ℝ)⁻¹ * Φ (x (i + 1)) (x (j + 1)) := by
        rw [intervalIntegral.integral_const, hstep, smul_eq_mul, one_div]
      rw [← hconst, ← intervalIntegral.integral_sub ((hΦσ σ).intervalIntegrable _ _)
        intervalIntegrable_const]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := x j) (b := x (j + 1))
        (C := ε / ((L : ℝ) ^ 2 + 1)) (f := fun τ => Φ σ τ - Φ (x (i + 1)) (x (j + 1)))
        (fun τ hτ => by
          rw [Set.uIoc_of_le (hmono j)] at hτ
          have hd : dist (σ, τ) (x (i + 1), x (j + 1)) < δ := by
            rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
            constructor
            · rw [abs_sub_comm, abs_of_nonneg (by linarith [hσ.2])]
              linarith [hσ.1, hstep i]
            · rw [abs_sub_comm, abs_of_nonneg (by linarith [hτ.2])]
              linarith [hτ.1, hstep j]
          have h := hδΦ (σ, τ) ⟨hmem i hi σ hσ, hmem j hj τ ⟨hτ.1.le, hτ.2⟩⟩
            (x (i + 1), x (j + 1))
            ⟨hmem i hi _ ⟨hmono i, le_rfl⟩, hmem j hj _ ⟨hmono j, le_rfl⟩⟩ hd
          rw [Real.dist_eq] at h
          rw [Real.norm_eq_abs]
          exact h.le)
      rw [Real.norm_eq_abs, hstep, abs_of_pos hinv, one_div] at h
      exact h
    have hconst2 : ∫ _σ in (x i)..(x (i + 1)), (N : ℝ)⁻¹ * Φ (x (i + 1)) (x (j + 1)) =
        ((N : ℝ)⁻¹) ^ 2 * Φ (x (i + 1)) (x (j + 1)) := by
      rw [intervalIntegral.integral_const, hstep, smul_eq_mul, one_div]
      ring
    rw [abs_sub_comm, ← hconst2, ← intervalIntegral.integral_sub
      ((hpar _ _).intervalIntegrable _ _) intervalIntegrable_const]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := x i) (b := x (i + 1))
      (C := ε / ((L : ℝ) ^ 2 + 1) * (N : ℝ)⁻¹)
      (f := fun σ => (∫ τ in (x j)..(x (j + 1)), Φ σ τ) - (N : ℝ)⁻¹ * Φ (x (i + 1)) (x (j + 1)))
      (fun σ hσ => by
        rw [Set.uIoc_of_le (hmono i)] at hσ
        rw [Real.norm_eq_abs]
        exact hin σ ⟨hσ.1.le, hσ.2⟩)
    rw [Real.norm_eq_abs, hstep, abs_of_pos hinv, one_div] at h
    refine h.trans (le_of_eq ?_)
    ring
  -- sum the cells
  have hsum : ((N : ℝ)⁻¹) ^ 2 * ∑ i ∈ range (L * N), ∑ j ∈ range (L * N),
        Φ (a + ((i : ℝ) + 1) / N) (a + ((j : ℝ) + 1) / N) =
      ∑ i ∈ range (L * N), ∑ j ∈ range (L * N), ((N : ℝ)⁻¹) ^ 2 * Φ (x (i + 1)) (x (j + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxsucc, hxsucc]
  rw [Real.dist_eq, hsum, hcells, ← Finset.sum_sub_distrib]
  have hbound : |∑ i ∈ range (L * N), (∑ j ∈ range (L * N),
        ((N : ℝ)⁻¹) ^ 2 * Φ (x (i + 1)) (x (j + 1)) -
      ∑ j ∈ range (L * N), ∫ σ in (x i)..(x (i + 1)), ∫ τ in (x j)..(x (j + 1)), Φ σ τ)| ≤
      ∑ _i ∈ range (L * N), ∑ _j ∈ range (L * N), ε / ((L : ℝ) ^ 2 + 1) * ((N : ℝ)⁻¹) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    exact hcell i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
  refine lt_of_le_of_lt hbound ?_
  rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
  have hval : ((L * N : ℕ) : ℝ) * (((L * N : ℕ) : ℝ) * (ε / ((L : ℝ) ^ 2 + 1) * ((N : ℝ)⁻¹) ^ 2)) =
      ε * ((L : ℝ) ^ 2 / ((L : ℝ) ^ 2 + 1)) := by
    push_cast
    field_simp
  rw [hval]
  have hlt : (L : ℝ) ^ 2 / ((L : ℝ) ^ 2 + 1) < 1 := by
    rw [div_lt_one hden]
    linarith
  calc ε * ((L : ℝ) ^ 2 / ((L : ℝ) ^ 2 + 1)) < ε * 1 := mul_lt_mul_of_pos_left hlt hε
    _ = ε := mul_one ε

/-! ### The logarithmic coordinate -/

/-- The substitution `σ = e^u` on `[1, A]`. -/
theorem integral_comp_log_div {g : ℝ → ℝ} (hg : Continuous g) {A : ℝ} (hA : 1 ≤ A) :
    ∫ σ in (1 : ℝ)..A, g (Real.log (max σ 1)) / max σ 1 = ∫ u in (0 : ℝ)..Real.log A, g u := by
  have hA0 : 0 < A := by linarith
  have h1 : ∫ u in (0 : ℝ)..Real.log A, g u =
      ∫ u in (0 : ℝ)..Real.log A, ((fun σ => g (Real.log σ) / σ) ∘ Real.exp) u * Real.exp u :=
    intervalIntegral.integral_congr fun u _ => by
      show g u = g (Real.log (Real.exp u)) / Real.exp u * Real.exp u
      rw [Real.log_exp, div_mul_cancel₀ _ (Real.exp_pos u).ne']
  have h2 : ∫ σ in (1 : ℝ)..A, g (Real.log (max σ 1)) / max σ 1 =
      ∫ σ in (1 : ℝ)..A, g (Real.log σ) / σ :=
    intervalIntegral.integral_congr fun σ hσ => by
      rw [Set.uIcc_of_le hA] at hσ
      show g (Real.log (max σ 1)) / max σ 1 = g (Real.log σ) / σ
      rw [max_eq_left hσ.1]
  have hcont : ContinuousOn (fun σ => g (Real.log σ) / σ)
      (Real.exp '' Set.uIcc 0 (Real.log A)) := by
    rintro σ ⟨x, _, rfl⟩
    have hpos := Real.exp_pos x
    exact ((hg.continuousAt.comp (Real.continuousAt_log hpos.ne')).div continuousAt_id
      hpos.ne').continuousWithinAt
  have h3 := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := Real.log A)
    (f := Real.exp) (f' := Real.exp) (g := fun σ => g (Real.log σ) / σ)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hcont
  rw [Real.exp_zero, Real.exp_log hA0] at h3
  rw [h1, h2, h3]

theorem continuous_log_max_one : Continuous fun σ : ℝ => Real.log (max σ 1) :=
  (continuous_id.max continuous_const).log fun σ =>
    (lt_of_lt_of_le one_pos (le_max_right σ 1)).ne'

theorem max_one_ne_zero (σ : ℝ) : max σ 1 ≠ 0 :=
  (lt_of_lt_of_le one_pos (le_max_right σ 1)).ne'

/-- The degree point `N + k + 1` at the scale `N`. -/
theorem cast_add_succ_div {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ((N + k + 1 : ℕ) : ℝ) / N = 1 + ((k : ℝ) + 1) / N := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  push_cast
  field_simp
  ring

theorem cast_add_succ_eq {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ((N + k + 1 : ℕ) : ℝ) = N * (1 + ((k : ℝ) + 1) / N) := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  push_cast
  field_simp
  ring

theorem one_le_one_add_div (N k : ℕ) : (1 : ℝ) ≤ 1 + ((k : ℝ) + 1) / N := by
  have : (0 : ℝ) ≤ ((k : ℝ) + 1) / N := by positivity
  linarith

/-- **Sums over the degree points of a window.** -/
theorem tendsto_degreeSum {G : ℝ → ℝ} (hG : Continuous G) {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + L * N), G (Real.log ((n : ℝ) / N)) / n) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + L), G u)) := by
  have hĜ : Continuous fun σ : ℝ => G (Real.log (max σ 1)) / max σ 1 :=
    (hG.comp continuous_log_max_one).div (continuous_id.max continuous_const) max_one_ne_zero
  have hA : (1 : ℝ) ≤ 1 + L := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have h := tendsto_gridSum_interval hĜ 1 hL
  rw [integral_comp_log_div hG hA] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_Ioc_add_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cast_add_succ_div hN, max_eq_left (one_le_one_add_div N k), cast_add_succ_eq hN,
    inv_mul_eq_div, div_div, mul_comm (N : ℝ)]

/-- **Pair sums over the degree points of a window.** -/
theorem tendsto_degreePairSum {Ψ : ℝ → ℝ → ℝ} (hΨ : Continuous (Function.uncurry Ψ)) (L : ℕ) :
    Tendsto (fun N : ℕ => ∑ m ∈ Ioc N (N + L * N), ∑ n ∈ Ioc N (N + L * N),
        Ψ (Real.log ((m : ℝ) / N)) (Real.log ((n : ℝ) / N)) / ((m : ℝ) * n)) atTop
      (𝓝 (∫ u in (0 : ℝ)..Real.log (1 + L), ∫ v in (0 : ℝ)..Real.log (1 + L), Ψ u v)) := by
  have hclamp : Continuous fun σ : ℝ => max σ 1 := continuous_id.max continuous_const
  have hΦ : Continuous (Function.uncurry fun σ τ : ℝ =>
      Ψ (Real.log (max σ 1)) (Real.log (max τ 1)) / (max σ 1 * max τ 1)) := by
    have h1 : Continuous fun p : ℝ × ℝ => Ψ (Real.log (max p.1 1)) (Real.log (max p.2 1)) :=
      hΨ.comp ((continuous_log_max_one.comp continuous_fst).prodMk
        (continuous_log_max_one.comp continuous_snd))
    have h2 : Continuous fun p : ℝ × ℝ => max p.1 1 * max p.2 1 :=
      (hclamp.comp continuous_fst).mul (hclamp.comp continuous_snd)
    exact h1.div h2 fun p => mul_ne_zero (max_one_ne_zero p.1) (max_one_ne_zero p.2)
  have hA : (1 : ℝ) ≤ 1 + L := by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hJ : Continuous fun u => ∫ v in (0 : ℝ)..Real.log (1 + L), Ψ u v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΨ 0 _
  have hin : ∀ σ : ℝ, ∫ τ in (1 : ℝ)..(1 + L),
        Ψ (Real.log (max σ 1)) (Real.log (max τ 1)) / (max σ 1 * max τ 1) =
      (∫ v in (0 : ℝ)..Real.log (1 + L), Ψ (Real.log (max σ 1)) v) / max σ 1 := by
    intro σ
    have hg : Continuous fun v => Ψ (Real.log (max σ 1)) v :=
      hΨ.comp (continuous_const.prodMk continuous_id)
    rw [← integral_comp_log_div hg hA, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    show Ψ (Real.log (max σ 1)) (Real.log (max τ 1)) / (max σ 1 * max τ 1) =
      Ψ (Real.log (max σ 1)) (Real.log (max τ 1)) / max τ 1 / max σ 1
    rw [div_div, mul_comm]
  have h := tendsto_gridSum_square hΦ 1 L
  simp_rw [hin] at h
  rw [integral_comp_log_div hJ hA] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sum_Ioc_add_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_Ioc_add_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi := one_le_one_add_div N i
  have hj := one_le_one_add_div N j
  have hi0 : (0 : ℝ) < 1 + ((i : ℝ) + 1) / N := by linarith
  have hj0 : (0 : ℝ) < 1 + ((j : ℝ) + 1) / N := by linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [cast_add_succ_div hN, cast_add_succ_div hN, max_eq_left hi, max_eq_left hj,
    cast_add_succ_eq hN, cast_add_succ_eq hN]
  generalize Ψ (Real.log (1 + ((i : ℝ) + 1) / N)) (Real.log (1 + ((j : ℝ) + 1) / N)) = X
  generalize 1 + ((i : ℝ) + 1) / N = y at hi0
  generalize 1 + ((j : ℝ) + 1) / N = z at hj0
  field_simp

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
