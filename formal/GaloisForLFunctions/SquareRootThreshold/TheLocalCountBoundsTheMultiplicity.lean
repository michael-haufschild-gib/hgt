import GaloisForLFunctions.SquareRootThreshold.CountingInputsDoNotBoundTheLocalCount

/-!
# The local count bounds the multiplicity

The disc `|ρ − (½ + δ + it)| ≤ δ` of the local count touches the critical line only at `½ + it`.
A critical zero `½ + iγ` lies in this disc at `t = γ` for every `δ`, so the local count with
constant `C` forces multiplicity `≤ C` (`mult_le_of_localCountBound`, `δ → 0`).  Bounded
multiplicity of critical zeros is not known even under the Riemann hypothesis.

**Falsifier** (`exists_zeroConfig_rvm_rh_not_localCountBound`).  Superposing on the zeros of `ζ` the
critical clusters `½ + i exp(eᵏ)` of multiplicity `⌊log γ⌋ = ⌊eᵏ⌋` (`criticalClusterConfig`) keeps
Riemann–von Mangoldt, adds no off-line zero (the off-line counts `N − N₀` are those of `ζ`, and the
configuration is critical whenever `ζ` is), changes every window count by `≤ 4 log(|T₂| + 3)`, and
violates the local count for every constant.  So the local count does not follow from the Riemann
hypothesis together with counting inputs: at the tangency point it is a multiplicity statement.
-/

open Complex Set Zeta23

namespace RHTower.LocalCountFalsifier

noncomputable section

open Classical

/-! ## The local count bounds the multiplicity -/

/-- **The local count bounds critical multiplicities.**  If the local count holds with constant `C`,
every critical zero above height `3` has multiplicity at most `C`. -/
theorem mult_le_of_localCountBound {Z : ZeroConfig} {C : ℝ} (h : LocalCountBound Z C) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) (hre : ρ.re = 1 / 2) (him : 3 ≤ ρ.im) : (Z.mult ρ : ℝ) ≤ C := by
  have hdisc : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → (Z.mult ρ : ℝ) ≤ C * (δ * Real.log ρ.im + 1) := by
    intro δ hδ0 hδ
    have hmem : ρ ∈ Metric.closedBall (((1 / 2 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I) δ := by
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have e : ρ - (((1 / 2 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I) = ((-δ : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hre]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hδ0]
    have h1 := mult_le_discCount Z hδ hρ hmem
    exact le_trans (by exact_mod_cast h1) (h δ ρ.im hδ0 hδ him)
  by_contra hlt
  push Not at hlt
  have hL : 0 < Real.log ρ.im := Real.log_pos (by linarith)
  set ε := (Z.mult ρ : ℝ) - C with hε
  have hε0 : 0 < ε := by linarith
  set δ := min (1 / 2) (ε / (2 * (|C| * Real.log ρ.im + 1))) with hδ
  have hD : 0 < 2 * (|C| * Real.log ρ.im + 1) := by positivity
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε0 hD)
  have hδ1 : δ ≤ ε / (2 * (|C| * Real.log ρ.im + 1)) := min_le_right _ _
  have key : |C| * (δ * Real.log ρ.im) < ε := by
    have h2 : δ * (2 * (|C| * Real.log ρ.im + 1)) ≤ ε := by rwa [le_div_iff₀ hD] at hδ1
    nlinarith [abs_nonneg C, mul_nonneg (abs_nonneg C) hL.le]
  have h3 := hdisc δ hδ0 (min_le_left _ _)
  have h4 : C * (δ * Real.log ρ.im) ≤ |C| * (δ * Real.log ρ.im) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  nlinarith

/-! ## Critical clusters -/

/-- `½ + i exp(eᵏ)`. -/
def criticalPoint (k : ℕ) : ℂ := ⟨1 / 2, Real.exp (Real.exp k)⟩

theorem criticalPoint_re (k : ℕ) : (criticalPoint k).re = 1 / 2 := rfl

theorem criticalPoint_im (k : ℕ) : (criticalPoint k).im = Real.exp (Real.exp k) := rfl

/-- **The critical clusters.**  At each height `exp(eᵏ)` the critical point of multiplicity
`⌊log γ⌋ = ⌊eᵏ⌋`. -/
def criticalClusterConfig : ZeroConfig where
  carrier := Set.range criticalPoint
  mult := fun ρ => ⌊Real.log ρ.im⌋₊
  one_le_mult := by
    rintro _ ⟨k, rfl⟩
    rw [criticalPoint_im, Real.log_exp]
    exact Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_exp (Nat.cast_nonneg k))
  strip := by
    rintro _ ⟨k, rfl⟩
    rw [criticalPoint_re]; constructor <;> norm_num
  reflect_mem := by
    rintro _ ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    apply Complex.ext <;> simp [reflect, criticalPoint]
    norm_num
  mult_reflect := fun ρ _ => by simp [reflect]
  finite_window := by
    intro T₁ T₂
    have hF : (Finset.range ⌈T₂⌉₊ : Set ℕ).Finite := Finset.finite_toSet _
    refine (hF.image criticalPoint).subset ?_
    rintro _ ⟨⟨k, rfl⟩, -, h2⟩
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_ceil.mpr (by rw [criticalPoint_im] at h2; linarith [le_exp_exp k])

theorem criticalClusterConfig_mult (k : ℕ) :
    criticalClusterConfig.mult (criticalPoint k) = ⌊Real.exp k⌋₊ := by
  show ⌊Real.log (criticalPoint k).im⌋₊ = _
  rw [criticalPoint_im, Real.log_exp]

/-- **The critical clusters are sparse.**  `N(T₁, T₂) ≤ 4 log(|T₂| + 3)`. -/
theorem criticalClusterConfig_N_le (T₁ T₂ : ℝ) :
    (criticalClusterConfig.N T₁ T₂ : ℝ) ≤ 4 * Real.log (|T₂| + 3) := by
  have hlog0 : 0 ≤ Real.log (|T₂| + 3) := Real.log_nonneg (by linarith [abs_nonneg T₂])
  rcases (criticalClusterConfig.window T₁ T₂).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · have : criticalClusterConfig.N T₁ T₂ = 0 := by
      simp only [ZeroConfig.N, hE, finsum_mem_empty]
    rw [this, Nat.cast_zero]; positivity
  have hT₂ : Real.exp 1 ≤ T₂ := by
    obtain ⟨⟨k, rfl⟩, -, h2⟩ := hρ₀
    rw [criticalPoint_im] at h2
    exact le_trans (Real.exp_le_exp.mpr (Real.one_le_exp (Nat.cast_nonneg k))) h2
  have hT₂0 : 0 < T₂ := lt_of_lt_of_le (Real.exp_pos 1) hT₂
  have hL1 : 1 ≤ Real.log T₂ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT₂
  set n : ℕ := ⌊Real.log (Real.log T₂)⌋₊ + 1 with hn
  set S : Finset ℂ := (Finset.range n).image criticalPoint with hS
  have hfin := criticalClusterConfig.finite_window T₁ T₂
  have hsub : hfin.toFinset ⊆ S := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨k, rfl⟩, -, h2⟩ := hρ
    rw [criticalPoint_im] at h2
    refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
    have h1 : Real.exp k ≤ Real.log T₂ := by
      rw [← Real.log_exp (Real.exp k)]; exact Real.log_le_log (Real.exp_pos _) h2
    have h3 : (k : ℝ) ≤ Real.log (Real.log T₂) := by
      rw [← Real.log_exp k]; exact Real.log_le_log (Real.exp_pos _) h1
    rw [Finset.mem_range, hn]
    have := Nat.le_floor h3
    omega
  have hN : criticalClusterConfig.N T₁ T₂ ≤ ∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ := by
    calc criticalClusterConfig.N T₁ T₂ = ∑ ρ ∈ hfin.toFinset, criticalClusterConfig.mult ρ :=
          finsum_mem_eq_finite_toFinset_sum _ hfin
      _ ≤ ∑ ρ ∈ S, criticalClusterConfig.mult ρ := Finset.sum_le_sum_of_subset hsub
      _ ≤ ∑ k ∈ Finset.range n, criticalClusterConfig.mult (criticalPoint k) :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ = ∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ :=
          Finset.sum_congr rfl fun k _ => criticalClusterConfig_mult k
  have hcast : ((∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.range n, Real.exp k := by
    push_cast
    exact Finset.sum_le_sum fun k _ => Nat.floor_le (Real.exp_pos (k : ℝ)).le
  have hexpn : Real.exp n ≤ Real.exp 1 * Real.log T₂ := by
    have hfl : (⌊Real.log (Real.log T₂)⌋₊ : ℝ) ≤ Real.log (Real.log T₂) :=
      Nat.floor_le (Real.log_nonneg hL1)
    have : Real.exp (⌊Real.log (Real.log T₂)⌋₊ : ℝ) ≤ Real.log T₂ := by
      calc _ ≤ Real.exp (Real.log (Real.log T₂)) := Real.exp_le_exp.mpr hfl
        _ = Real.log T₂ := Real.exp_log (by linarith)
    rw [hn, Nat.cast_add, Nat.cast_one, Real.exp_add, mul_comm]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos 1).le
  have hlogT : Real.log T₂ ≤ Real.log (|T₂| + 3) :=
    Real.log_le_log hT₂0 (by rw [abs_of_pos hT₂0]; linarith)
  have he := Real.exp_pos 1
  calc (criticalClusterConfig.N T₁ T₂ : ℝ)
      ≤ ((∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN
    _ ≤ 2 * Real.exp n / Real.exp 1 := hcast.trans (sum_range_exp_le n)
    _ ≤ 2 * Real.log T₂ := by rw [div_le_iff₀ he]; nlinarith
    _ ≤ 4 * Real.log (|T₂| + 3) := by linarith

/-- The critical clusters are on the line: their critical count is their count. -/
theorem criticalClusterConfig_N0 (T₁ T₂ : ℝ) :
    criticalClusterConfig.N0 T₁ T₂ = criticalClusterConfig.N T₁ T₂ := by
  have hS : criticalClusterConfig.window T₁ T₂ ∩ ZeroConfig.onLine
      = criticalClusterConfig.window T₁ T₂ := by
    refine Set.inter_eq_left.mpr ?_
    rintro _ ⟨⟨k, rfl⟩, -⟩
    exact criticalPoint_re k
  unfold ZeroConfig.N0 ZeroConfig.N
  rw [hS]

/-! ## The falsifier -/

/-- **The local count is not implied by the Riemann hypothesis with counting.**  The zeros of `ζ`
with the critical clusters satisfy Riemann–von Mangoldt, have the off-line counts of `ζ` and are all
critical when those of `ζ` are, change every window count by at most `4 log(|T₂| + 3)`, and violate
the local count for every constant. -/
theorem exists_zeroConfig_rvm_rh_not_localCountBound :
    ∃ Z' : ZeroConfig, RiemannVonMangoldt Z' ∧
      ((∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) → ∀ ρ ∈ Z'.carrier, ρ.re = 1 / 2) ∧
      (∀ T₁ T₂ : ℝ, (Z'.N T₁ T₂ : ℤ) - Z'.N0 T₁ T₂
        = (zetaZeroConfig.N T₁ T₂ : ℤ) - zetaZeroConfig.N0 T₁ T₂) ∧
      (∀ T₁ T₂ : ℝ, zetaZeroConfig.N T₁ T₂ ≤ Z'.N T₁ T₂ ∧
        (Z'.N T₁ T₂ : ℝ) ≤ zetaZeroConfig.N T₁ T₂ + 4 * Real.log (|T₂| + 3)) ∧
      ∀ C : ℝ, ¬ LocalCountBound Z' C := by
  refine ⟨superpose zetaZeroConfig criticalClusterConfig,
    riemannVonMangoldt_superpose_of_N_le riemannVonMangoldt_zeta criticalClusterConfig_N_le,
    ?_, fun T₁ T₂ => ?_, fun T₁ T₂ => ?_, fun C hC => ?_⟩
  · rintro hRH ρ (h | ⟨k, rfl⟩)
    · exact hRH ρ h
    · exact criticalPoint_re k
  · rw [N_superpose, N0_superpose, criticalClusterConfig_N0]
    push_cast; ring
  · rw [N_superpose]
    refine ⟨Nat.le_add_right _ _, ?_⟩
    rw [Nat.cast_add]
    linarith [criticalClusterConfig_N_le T₁ T₂]
  · -- a cluster of multiplicity `⌊eᵏ⌋ > C`
    obtain ⟨k, hk⟩ := exists_nat_gt (|C| + 1)
    have hmem : criticalPoint k ∈ (superpose zetaZeroConfig criticalClusterConfig).carrier :=
      Or.inr ⟨k, rfl⟩
    have him : 3 ≤ (criticalPoint k).im := by
      rw [criticalPoint_im]
      have := le_exp_exp k
      linarith [abs_nonneg C]
    have hle := mult_le_of_localCountBound hC hmem (criticalPoint_re k) him
    have hge : ⌊Real.exp k⌋₊
        ≤ (superpose zetaZeroConfig criticalClusterConfig).mult (criticalPoint k) := by
      have hc : criticalPoint k ∈ criticalClusterConfig.carrier := ⟨k, rfl⟩
      show _ ≤ (if criticalPoint k ∈ zetaZeroConfig.carrier then
          zetaZeroConfig.mult (criticalPoint k) else 0)
        + (if criticalPoint k ∈ criticalClusterConfig.carrier then
          criticalClusterConfig.mult (criticalPoint k) else 0)
      rw [if_pos hc, criticalClusterConfig_mult]
      omega
    have hfl : Real.exp k - 1 < (⌊Real.exp k⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (Real.exp k); linarith
    have hek : (k : ℝ) + 1 ≤ Real.exp k := Real.add_one_le_exp _
    have hgeR : (⌊Real.exp k⌋₊ : ℝ) ≤ (superpose zetaZeroConfig criticalClusterConfig).mult
        (criticalPoint k) := by exact_mod_cast hge
    linarith [le_abs_self C]

end

end RHTower.LocalCountFalsifier
