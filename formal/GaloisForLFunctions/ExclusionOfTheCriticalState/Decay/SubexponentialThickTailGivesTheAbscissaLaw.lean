import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests
import GaloisForLFunctions.InfiniteRankWeilTheory.TheCrudeStepAndTheCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# Subexponential growth of the confined state on a thick tail gives the abscissa law

At base `ℓ > 0` the zeros of `ξ` form the Weil tower `z_q = e^{ℓ(ρ_q − ½)}`. Left of the wall,
testing the distributional zero series of the critical state `F` against translates
`ψ_ν(u) = ψ₀(u + νℓ)` of a smooth bump `ψ₀` supported in `(−ℓ, 0)` turns the pairing with
`e^{−8u} F(u)` on `(−(ν+1)ℓ, −νℓ)` directly into a level sum of the tower with weights
`L F(z_q) ψ̂₀(z_q)`, with no Gaussian tail across the complement of the window. Every zero right of
the line is seen (`L F(z_q) ≠ 0`), and smooth interpolation on `(−ℓ, 0)` isolates any single top
coordinate from all others in a finite top layer.

* **Weighted tower transfer** (`asymptoticAbscissaLaw_of_thick_weighted_tower_bound`). Any summable
  weight family on the zero copies that keeps at least one merged weight of every isolated top
  nonzero transfers a subexponential thick-set bound to `AsymptoticAbscissaLaw`.
* **Window `L¹` and continuous `ThickLeft` receivers**
  (`asymptoticAbscissaLaw_of_thick_window_l1_bound`,
  `asymptoticAbscissaLaw_of_subexponential_thickLeft`,
  `asymptoticAbscissaLaw_of_thickLeft_subexponential`). If `F(u) e^{−8u}` is subexponential in
  window `L¹` along a thick set of tower levels, or almost everywhere on sets thick toward `−∞`,
  then `AsymptoticAbscissaLaw` holds.
* **Heated zero series receiver** (`asymptoticAbscissaLaw_of_thick_heatedState_bound`). At any fixed
  base `ℓ > 0`, choosing the heat parameter `ε > 0` along two orthogonal phases makes the heated
  weights `L F(z_q) e^{ε z_q²}` merged-nonvanishing on any isolated top; subexponential thick bounds
  on `heatedState ε F (−νℓ)` therefore also imply `AsymptoticAbscissaLaw`.
* **Contrapositive excursions and `a = 0` exclusion**
  (`exists_syndetic_state_excursions_of_not_asymptoticAbscissaLaw`,
  `no_criticalState_thick_window_bounded_of_zerosApproachLine`,
  `no_criticalState_thick_window_bounded_of_finiteOffLine`,
  `no_criticalState_thickLeft_bounded_of_zerosApproachLine`). Failure of `AsymptoticAbscissaLaw`
  forces syndetic exponential excursions of `∫ |F(u)| e^{−8u}` at every base, and under
  `ZerosApproachLine` (in particular under `FiniteOffLine`) `F(u) e^{−8u}` cannot be bounded on any
  thick set.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset Matrix
open scoped ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
open GaloisForLFunctions.InfiniteRankWeilTheory

/-! ### Continuous thick sets toward `−∞` -/

/-- A subset `E ⊆ ℝ` is **thick toward `−∞`** if it contains closed intervals `[−T − L, −T]` of
arbitrary length `L > 0` arbitrarily far to the left (`T ≥ M`). -/
def ThickLeft (E : Set ℝ) : Prop :=
  ∀ L M : ℝ, 0 < L → ∃ T : ℝ, M ≤ T ∧ Icc (-T - L) (-T) ⊆ E

theorem thickLeft_Iic (c : ℝ) : ThickLeft (Iic c) := fun L M _ =>
  ⟨max M (-c), le_max_left _ _, fun _ hu => mem_Iic.mpr (by linarith [hu.2, le_max_right M (-c)])⟩

/-- Discretizing a `ThickLeft` set at any step `ℓ > 0` produces a `Thick` set of tower levels. -/
theorem thick_of_thickLeft {E : Set ℝ} (hE : ThickLeft E) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Thick {ν : ℕ | Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)) ⊆ E} := by
  intro K N
  obtain ⟨T, hT, hsub⟩ := hE (((K + 2 : ℕ) : ℝ) * ℓ) (max 0 (((N + 1 : ℕ) : ℝ) * ℓ))
    (mul_pos (by positivity) hℓ)
  have hT0 : 0 ≤ T := (le_max_left _ _).trans hT
  have hTN : ((N + 1 : ℕ) : ℝ) * ℓ ≤ T := (le_max_right _ _).trans hT
  set M : ℕ := ⌈T / ℓ⌉₊
  have hNM : N ≤ M := by
    have hdiv : (N : ℝ) ≤ T / ℓ := (le_div_iff₀ hℓ).2 (by push_cast at hTN; nlinarith)
    exact_mod_cast hdiv.trans (Nat.le_ceil _)
  have hTM : T ≤ (M : ℝ) * ℓ := (div_le_iff₀ hℓ).1 (Nat.le_ceil _)
  have hMT : (M : ℝ) * ℓ ≤ T + ℓ := by
    have hc : (M : ℝ) ≤ T / ℓ + 1 := (Nat.ceil_lt_add_one (div_nonneg hT0 hℓ.le)).le
    have := mul_le_mul_of_nonneg_right hc hℓ.le
    rwa [add_mul, div_mul_cancel₀ _ hℓ.ne', one_mul] at this
  refine ⟨M, hNM, fun ν h1 h2 => fun u hu => hsub ⟨?_, ?_⟩⟩
  · have hνK : ((ν + 1 : ℕ) : ℝ) ≤ (M : ℝ) + ((K + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hmul := mul_le_mul_of_nonneg_right hνK hℓ.le
    push_cast at hmul hu ⊢
    linarith [hu.1]
  · have hMν : (M : ℝ) ≤ (ν : ℝ) := by exact_mod_cast (by omega)
    have hmul := mul_le_mul_of_nonneg_right hMν hℓ.le
    linarith [hu.2]

/-! ### Weighted tower receiver -/

/-- **Weighted tower receiver for `AsymptoticAbscissaLaw`.** If `b : XiZeroCopy → ℂ` is summable in
norm and every isolated top has a point whose merged `b`-weight at base `ℓ > 0` is nonzero, then
subexponential bounds on `levelSum (frobTower ℓ zetaConfig) b` along thick sets force
`AsymptoticAbscissaLaw`. -/
theorem asymptoticAbscissaLaw_of_thick_weighted_tower_bound {ℓ : ℝ} (hℓ : 0 < ℓ)
    (b : XiZeroCopy → ℂ) (hb : Summable fun q => ‖b q‖)
    (hvis : ∀ (S : Finset XiZeroCopy) (Θ Θ₂ : ℝ), S.Nonempty → 1 / 2 < Θ → Θ₂ < Θ →
      (∀ q ∈ S, (zetaConfig q).re = Θ) → (∀ q ∉ S, (zetaConfig q).re ≤ Θ₂) →
      ∃ q ∈ S, (∑ j ∈ S with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q, b j) ≠ 0)
    (hbd : ∀ a : ℝ, 0 < a → ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
      ∀ ν ∈ G, ‖levelSum (frobTower ℓ zetaConfig) b ν‖ ≤ C * Real.exp (a * ν * ℓ)) :
    RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  obtain ⟨htop_norm, hlow_norm, hlt_norm⟩ := frobTower_isolatedTop hℓ hΘ₂ hS hrest
  obtain ⟨q₀, hq₀, hq₀vis⟩ := hvis S Θ Θ₂ hSne hΘ hΘ₂ hS hrest
  obtain ⟨G, hG, C, hC⟩ := hbd ((Θ - 1 / 2) / 2) (by linarith)
  have hρR : Real.exp ((Θ - 1 / 2) / 2 * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  refine not_forall_mem_thick_norm_levelSum_le (frobTower ℓ zetaConfig) b hb S
    (Real.exp_pos _) (Real.exp_pos _).le hlt_norm hlow_norm (fun q hq _ => htop_norm q hq)
    ⟨q₀, hq₀, hq₀vis⟩ (C := C) (Real.exp_pos _).le hρR hG fun ν hν => ?_
  have := hC ν hν
  rwa [show (Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ = ν * ((Θ - 1 / 2) / 2 * ℓ) by ring,
    Real.exp_nat_mul] at this

/-! ### Smooth interpolation supported strictly inside `(−ℓ, 0)` -/

private theorem bumpTest_smooth {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ContDiff ℝ ∞ (bumpTest δ hδ t) :=
  Complex.ofRealCLM.contDiff.comp ((smallBump δ hδ).contDiff.comp (contDiff_id.sub contDiff_const))

private theorem bumpTest_eq_zero_of_abs_ge {δ : ℝ} (hδ : 0 < δ) (t u : ℝ) (hu : δ ≤ |u - t|) :
    bumpTest δ hδ t u = 0 := by
  simp only [bumpTest]
  rw [(smallBump δ hδ).zero_of_le_dist (by simpa [smallBump, Real.dist_eq] using hu),
    Complex.ofReal_zero]

private theorem laplaceTest_eq_paperFT_mul_I (ψ : ℝ → ℂ) (p : ℂ) :
    laplaceTest ψ p = paperFT ψ (I * p) := rfl

private theorem laplaceTest_bumpTest_shift {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (p : ℂ) :
    laplaceTest (bumpTest δ hδ t) p =
      Complex.exp (-(p * t)) * laplaceTest (bumpTest δ hδ 0) p := by
  rw [laplaceTest_eq_paperFT_mul_I, paperFT_bumpTest, laplaceTest_eq_paperFT_mul_I]
  congr 2
  linear_combination p * (t : ℂ) * Complex.I_mul_I

private theorem laplaceTest_sum_smul {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i)) (a : Fin n → ℂ) (p : ℂ) :
    laplaceTest (∑ i, a i • f i) p = ∑ i, a i * laplaceTest (f i) p := by
  rw [laplaceTest_eq_paperFT_mul_I, paperFT_sum_smul f hf hfc]
  rfl

/-- **Smooth interpolation on `(−ℓ, 0)`.** For every `ℓ > 0`, finitely many distinct points
`z : Fin n → ℂ` and target values `b : Fin n → ℂ`, there is a `C^∞` test `ψ` vanishing outside
`(−ℓ, 0)` with `laplaceTest ψ (z k) = b k` for every `k`. -/
theorem exists_smooth_negInterval_interpolating {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    (z : Fin n → ℂ) (hz : Function.Injective z) (b : Fin n → ℂ) :
    ∃ ψ : ℝ → ℂ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ u : ℝ, u ∉ Ioo (-ℓ) 0 → ψ u = 0) ∧ ∀ k : Fin n, laplaceTest ψ (z k) = b k := by
  classical
  have hS : 0 ≤ ∑ k, ‖z k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  set δ : ℝ := min (ℓ / 4) (1 / (4 * (1 + ∑ k, ‖z k‖)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδℓ : δ ≤ ℓ / 4 := min_le_left _ _
  have hzδ : ∀ k, ‖I * z k‖ * δ ≤ 1 / 4 := by
    intro k
    rw [norm_mul, Complex.norm_I, one_mul]
    have hk : ‖z k‖ ≤ ∑ j, ‖z j‖ := Finset.single_le_sum (fun j _ => norm_nonneg _) (mem_univ k)
    have hle : δ ≤ 1 / (4 * (1 + ∑ j, ‖z j‖)) := min_le_right _ _
    calc ‖z k‖ * δ ≤ ‖z k‖ * (1 / (4 * (1 + ∑ j, ‖z j‖))) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  set D : ℝ := 1 + ∑ k, ∑ l, ‖z k - z l‖
  have hD0 : 0 ≤ ∑ k, ∑ l, ‖z k - z l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set τ : ℝ := min (ℓ / (4 * ((n : ℝ) + 1))) (1 / D)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτℓ : τ ≤ ℓ / (4 * ((n : ℝ) + 1)) := min_le_left _ _
  have hτD : τ ≤ 1 / D := min_le_right _ _
  set t : Fin n → ℝ := fun j => -(2 * δ + (j : ℕ) * τ)
  set h : Fin n → ℂ := fun k =>
    Complex.exp (2 * (δ : ℂ) * z k) * laplaceTest (bumpTest δ hδ 0) (z k)
  have hh : ∀ k, h k ≠ 0 := fun k =>
    mul_ne_zero (Complex.exp_ne_zero _) (by
      rw [laplaceTest_eq_paperFT_mul_I]
      exact paperFT_bumpTest_zero_ne_zero hδ (hzδ k))
  set w : Fin n → ℂ := fun k => Complex.exp ((τ : ℂ) * z k)
  have hw : Function.Injective w := by
    intro k l hkl
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hkl
    have hle : ‖z k - z l‖ ≤ ∑ i, ∑ j, ‖z i - z j‖ :=
      (Finset.single_le_sum (f := fun j => ‖z k - z j‖) (fun _ _ => norm_nonneg _)
        (mem_univ l)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖z i - z j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (mem_univ k))
    have hsub : (τ : ℂ) * (z k - z l) = (m : ℂ) * (2 * Real.pi * I) := by linear_combination hm
    have hsmall : ‖(τ : ℂ) * (z k - z l)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      calc τ * ‖z k - z l‖ ≤ (1 / D) * ‖z k - z l‖ :=
            mul_le_mul_of_nonneg_right hτD (norm_nonneg _)
        _ < 1 := by
            rw [one_div_mul_eq_div, div_lt_one (by positivity)]
            dsimp [D]; linarith
    have hm0 : m = 0 := by
      by_contra hm0
      rw [hsub, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_two,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
        at hsmall
      have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
      have := Real.pi_gt_three
      nlinarith
    rw [hm0] at hsub
    simp only [Int.cast_zero, zero_mul] at hsub
    rcases mul_eq_zero.mp hsub with h0 | h0
    · exact absurd h0 (Complex.ofReal_ne_zero.mpr hτ.ne')
    · exact hz (sub_eq_zero.mp h0)
  set M : Matrix (Fin n) (Fin n) ℂ := diagonal h * vandermonde w
  have hdet : IsUnit M.det := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine Ne.isUnit (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hh k) ?_)
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr fun he => (ne_of_gt (Finset.mem_Ioi.mp hj)) (hw he)
  set a : Fin n → ℂ := M⁻¹ *ᵥ b
  have hsupp_psi : ∀ u : ℝ, u ∉ Ioo (-ℓ) 0 → (∑ j, a j • bumpTest δ hδ (t j)) u = 0 := by
    intro u hu
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    suffices bumpTest δ hδ (t j) u = 0 by rw [this, mul_zero]
    refine bumpTest_eq_zero_of_abs_ge hδ (t j) u ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨hl, hr⟩ := abs_lt.mp hlt
    have hj : ((j : ℕ) : ℝ) < (n : ℝ) + 1 := by exact_mod_cast Nat.lt_succ_of_lt j.2
    have hjτ : ((j : ℕ) : ℝ) * τ < ℓ / 4 := by
      calc ((j : ℕ) : ℝ) * τ ≤ ((j : ℕ) : ℝ) * (ℓ / (4 * ((n : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hτℓ (Nat.cast_nonneg _)
        _ < ((n : ℝ) + 1) * (ℓ / (4 * ((n : ℝ) + 1))) :=
            mul_lt_mul_of_pos_right hj (by positivity)
        _ = ℓ / 4 := by field_simp
    have hu_lo : -ℓ < u := by dsimp [t] at hl; linarith
    have hu_hi : u < 0 := by
      have : 0 ≤ ((j : ℕ) : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ.le
      dsimp [t] at hr; linarith
    exact hu ⟨hu_lo, hu_hi⟩
  refine ⟨∑ j, a j • bumpTest δ hδ (t j), ?_, ?_, hsupp_psi, ?_⟩
  · have hfn : (∑ j, a j • bumpTest δ hδ (t j)) = fun u => ∑ j, a j * bumpTest δ hδ (t j) u := by
      funext u; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfn]
    exact ContDiff.sum fun j _ => contDiff_const.mul (bumpTest_smooth hδ (t j))
  · exact HasCompactSupport.intro (isCompact_Icc (a := -ℓ) (b := 0)) fun u hu =>
      hsupp_psi u fun hm => hu ⟨hm.1.le, hm.2.le⟩
  · intro k
    rw [laplaceTest_sum_smul _ (fun j => (bumpTest_smooth hδ (t j)).continuous)
      (fun j => bumpTest_hasCompactSupport hδ (t j))]
    have hMa : M *ᵥ a = b := by
      simp only [a, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hentry : ∀ j : Fin n, a j * laplaceTest (bumpTest δ hδ (t j)) (z k) = M k j * a j := by
      intro j
      rw [laplaceTest_bumpTest_shift]
      have hexp : Complex.exp (-(z k * (t j : ℂ))) =
          Complex.exp (2 * (δ : ℂ) * z k) * w k ^ (j : ℕ) := by
        dsimp [t, w]
        rw [← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [hexp]
      simp only [M, h, Matrix.mul_apply, Matrix.diagonal_apply, vandermonde_apply, ite_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [Finset.sum_congr rfl fun j _ => hentry j]
    have := congrFun hMa k
    rwa [Matrix.mulVec, dotProduct] at this

/-! ### Shifted smooth tests along the Frobenius tower -/

private theorem laplaceTest_add_right (ψ₀ : ℝ → ℂ) (s : ℝ) (p : ℂ) :
    laplaceTest (fun u => ψ₀ (u + s)) p = Complex.exp (p * s) * laplaceTest ψ₀ p := by
  rw [laplaceTest_eq_integral, laplaceTest_eq_integral]
  set G : ℝ → ℂ := fun v => Complex.exp (p * s) * (ψ₀ v * Complex.exp (-(p * v)))
  have h1 : (fun u : ℝ => ψ₀ (u + s) * Complex.exp (-(p * u))) = fun u => G (u + s) := by
    funext u
    dsimp [G]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [h1, MeasureTheory.integral_add_right_eq_self G s]
  dsimp [G]
  exact MeasureTheory.integral_const_mul _ _

/-- **Shifted bump identity on the tower of `ζ`.** For a smooth test `ψ₀` vanishing on `(0, ∞)`
and `ℓ ≥ 0`, the level sum of `zetaTower ℓ` with weights `L F(z_q) ψ̂₀(z_q)` equals
`−a(W₀) ∫ ψ₀(u + νℓ) e^{−8u} F(u) du`. -/
theorem criticalState_levelSum_laplaceTest {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ψ₀ : ℝ → ℂ}
    (hψ₀ : ContDiff ℝ ∞ ψ₀) (hs₀ : HasCompactSupport ψ₀) (h0 : ∀ x, 0 < x → ψ₀ x = 0)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (ν : ℕ) :
    levelSum (frobTower ℓ zetaConfig)
        (fun q => negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ₀ (centredZero q))
        ν =
      -((criticalAliasCoefficient W₀ : ℂ) * statePairing F (fun u => ψ₀ (u + ν * ℓ))) := by
  let ψ : ℝ → ℂ := fun u => ψ₀ (u + ν * ℓ)
  have hψ : ContDiff ℝ ∞ ψ := hψ₀.comp (contDiff_id.add contDiff_const)
  have hs : HasCompactSupport ψ := hs₀.comp_homeomorph (Homeomorph.addRight ((ν : ℝ) * ℓ))
  have hψ_pos : ∀ x, 0 < x → ψ x = 0 := fun x hx => h0 _ (by positivity)
  have hsum := (criticalState_hasSum_zeroSeries_test_left hW hthreshold hF hψ hs hψ_pos).tsum_eq
  rw [← hsum]
  unfold levelSum
  refine tsum_congr fun q => ?_
  dsimp [ψ]
  rw [zpow_natCast, laplaceTest_add_right, frobTower_pow]
  have hcz : centredZero q = zetaConfig q - 1 / 2 := rfl
  rw [← hcz]
  have hexp : Complex.exp ((ν * ℓ : ℝ) * centredZero q) =
      Complex.exp (centredZero q * (((ν : ℝ) * ℓ : ℝ) : ℂ)) := by congr 1; push_cast; ring
  rw [hexp]
  ring

/-- Bounding `statePairing` on a window when `ψ₀` vanishes outside `(−ℓ, 0)`. -/
theorem norm_statePairing_shift_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {ψ₀ : ℝ → ℂ} {ℓ B : ℝ} (_hB : 0 ≤ B) (hbound : ∀ v, ‖ψ₀ v‖ ≤ B)
    (hsupp : ∀ v, v ∉ Ioo (-ℓ) 0 → ψ₀ v = 0) (ν : ℕ) :
    ‖statePairing F (fun u => ψ₀ (u + ν * ℓ))‖ ≤
      B * ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
        |F u| * Real.exp (-(8 * u)) := by
  set S : Set ℝ := Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ))
  set a : ℝ := -(((ν + 1 : ℕ) : ℝ) * ℓ)
  have hvan : ∀ u, u ∉ S → ψ₀ (u + ν * ℓ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ) = 0 := by
    intro u hu
    have hnot : u + ν * ℓ ∉ Ioo (-ℓ) 0 := fun hm =>
      hu ⟨by push_cast; linarith [hm.1], by linarith [hm.2]⟩
    rw [hsupp _ hnot, zero_mul]
  have heq : statePairing F (fun u => ψ₀ (u + ν * ℓ)) =
      ∫ u in S, ψ₀ (u + ν * ℓ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ) := by
    unfold statePairing
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hvan).symm
  have hint : IntegrableOn (fun u => |F u| * Real.exp (-(8 * u))) S volume := by
    have hmaj : IntegrableOn (fun u => Real.exp (-(8 * a)) * |F u|) S volume :=
      (hF.integrable.norm.const_mul _).integrableOn
    refine hmaj.mono' (hF.meas.abs.mul (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le), mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hu.1])) (abs_nonneg _)
  rw [heq, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.norm_integral_le_of_norm_le (hint.const_mul B) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    mul_comm (Real.exp _) |F u|]
  exact mul_le_mul_of_nonneg_right (hbound _) (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)

/-- Isolating one top zero of an isolated top `S` by a smooth test supported in `(−ℓ, 0)`. -/
private theorem exists_isolating_bump_on_top {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {S : Finset XiZeroCopy} {Θ : ℝ} (hSne : S.Nonempty) (hΘ : 1 / 2 < Θ)
    (hS : ∀ q ∈ S, (zetaConfig q).re = Θ) :
    ∃ (ψ₀ : ℝ → ℂ) (B : ℝ) (q₀ : XiZeroCopy),
      ContDiff ℝ ∞ ψ₀ ∧ HasCompactSupport ψ₀ ∧ (∀ v, v ∉ Ioo (-ℓ) 0 → ψ₀ v = 0) ∧
      0 ≤ B ∧ (∀ v, ‖ψ₀ v‖ ≤ B) ∧ q₀ ∈ S ∧
      (∑ j ∈ S with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀,
        negativeHalfLineLaplace (cx F) (centredZero j) * laplaceTest ψ₀ (centredZero j)) ≠ 0 := by
  classical
  obtain ⟨q₀, hq₀⟩ := hSne
  let P : Finset ℂ := S.image centredZero
  let e : Fin P.card ≃ P := P.equivFin.symm
  have hinj : Function.Injective (fun k : Fin P.card => (e k : ℂ)) := fun i j hij =>
    e.injective (Subtype.ext hij)
  let target : Fin P.card → ℂ := fun k => if (e k : ℂ) = centredZero q₀ then 1 else 0
  obtain ⟨ψ₀, hψ₀, hs₀, hsupp₀, hinterp⟩ :=
    exists_smooth_negInterval_interpolating hℓ (fun k => (e k : ℂ)) hinj target
  have hval : ∀ q ∈ S, laplaceTest ψ₀ (centredZero q) =
      if centredZero q = centredZero q₀ then 1 else 0 := by
    intro q hq
    have hmem : centredZero q ∈ P := mem_image_of_mem centredZero hq
    let k : Fin P.card := e.symm ⟨centredZero q, hmem⟩
    have hk : (e k : ℂ) = centredZero q := by simp [k]
    simpa [target, hk] using hinterp k
  obtain ⟨B₀, hB₀⟩ := hs₀.exists_bound_of_continuous hψ₀.continuous
  refine ⟨ψ₀, max B₀ 0, q₀, hψ₀, hs₀, hsupp₀, le_max_right _ _,
    fun v => (hB₀ v).trans (le_max_left _ _), hq₀, ?_⟩
  have heq_sum : (∑ j ∈ S with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀,
      negativeHalfLineLaplace (cx F) (centredZero j) * laplaceTest ψ₀ (centredZero j)) =
      ((S.filter fun j => centredZero j = centredZero q₀).card : ℂ) *
        negativeHalfLineLaplace (cx F) (centredZero q₀) := by
    have h1 : ∀ j ∈ S.filter (fun j => frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀),
        negativeHalfLineLaplace (cx F) (centredZero j) * laplaceTest ψ₀ (centredZero j) =
          if centredZero j = centredZero q₀ then
            negativeHalfLineLaplace (cx F) (centredZero q₀) else 0 := by
      intro j hj
      rw [hval j (mem_filter.1 hj).1]
      split_ifs with hz
      · rw [hz, mul_one]
      · rw [mul_zero]
    have hfil : ((S.filter fun j => frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀).filter
        fun j => centredZero j = centredZero q₀) =
        S.filter fun j => centredZero j = centredZero q₀ := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hjS, _⟩, hjz⟩; exact ⟨hjS, hjz⟩
      · rintro ⟨hjS, hjz⟩
        have hcfg : zetaConfig j = zetaConfig q₀ := by
          change (j.1 : ℂ) = (q₀.1 : ℂ)
          change (j.1 : ℂ) - 1 / 2 = (q₀.1 : ℂ) - 1 / 2 at hjz
          linear_combination hjz
        exact ⟨⟨hjS, by simp [frobTower, hcfg]⟩, hjz⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, hfil]
  rw [heq_sum]
  have hcard_pos : 0 < (S.filter fun j => centredZero j = centredZero q₀).card :=
    Finset.card_pos.2 ⟨q₀, mem_filter.2 ⟨hq₀, rfl⟩⟩
  have hre_pos : 0 ≤ (centredZero q₀).re := by
    have := hS q₀ hq₀
    change ((q₀.1 : ℂ)).re = Θ at this
    simp only [centredZero, Complex.sub_re, this]
    norm_num; linarith
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hcard_pos.ne')
    (criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF hre_pos)

/-! ### Answering E-Q5: window `L¹` and continuous `ThickLeft` receivers -/

/-- **E-Q5 (window `L¹` tower form).** If at one base `ℓ > 0` the window `L¹` mass of
`F(u) e^{−8u}` along `[−(ν+1)ℓ, −νℓ]` grows slower than every exponential on a thick set of
levels, `AsymptoticAbscissaLaw` holds unconditionally. -/
theorem asymptoticAbscissaLaw_of_thick_window_l1_bound {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ∀ a : ℝ, 0 < a → ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ, ∀ ν ∈ G,
      (∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
        |F u| * Real.exp (-(8 * u))) ≤ C * Real.exp (a * ν * ℓ)) :
    RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  obtain ⟨ψ₀, B, q₀, hψ₀, hs₀, hsupp₀, hB0, hbound, hq₀, hvis⟩ :=
    exists_isolating_bump_on_top hW hthreshold hF hℓ hSne hΘ hS
  have h0 : ∀ x, 0 < x → ψ₀ x = 0 := fun x hx =>
    hsupp₀ x fun hm => lt_irrefl (0 : ℝ) (hx.trans hm.2)
  let b : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ₀ (centredZero q)
  have hb : Summable fun q => ‖b q‖ :=
    (criticalState_hasSum_zeroSeries_test_left hW hthreshold hF hψ₀ hs₀ h0).summable.norm
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have haW : 0 < criticalAliasCoefficient W₀ := criticalAliasCoefficient_positive hW
  obtain ⟨htop_norm, hlow_norm, hlt_norm⟩ := frobTower_isolatedTop hℓ hΘ₂ hS hrest
  obtain ⟨G, hG, C, hC⟩ := h ((Θ - 1 / 2) / 2) (by linarith)
  have hρR : Real.exp ((Θ - 1 / 2) / 2 * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  refine not_forall_mem_thick_norm_levelSum_le (frobTower ℓ zetaConfig) b hb S
    (Real.exp_pos _) (Real.exp_pos _).le hlt_norm hlow_norm (fun q hq _ => htop_norm q hq)
    ⟨q₀, hq₀, hvis⟩ (C := criticalAliasCoefficient W₀ * B * max C 0)
    (Real.exp_pos _).le hρR hG fun ν hν => ?_
  rw [criticalState_levelSum_laplaceTest hW hthreshold hF hψ₀ hs₀ h0 hℓ.le ν,
    norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg haW.le]
  have hp := norm_statePairing_shift_le hd hB0 hbound hsupp₀ ν
  have hC' : C * Real.exp ((Θ - 1 / 2) / 2 * ν * ℓ) ≤
      max C 0 * Real.exp ((Θ - 1 / 2) / 2 * ν * ℓ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  calc criticalAliasCoefficient W₀ * ‖statePairing F (fun u => ψ₀ (u + ν * ℓ))‖
      ≤ criticalAliasCoefficient W₀ *
          (B * (max C 0 * Real.exp ((Θ - 1 / 2) / 2 * ν * ℓ))) :=
        mul_le_mul_of_nonneg_left
          (hp.trans (mul_le_mul_of_nonneg_left ((hC ν hν).trans hC') hB0)) haW.le
    _ = criticalAliasCoefficient W₀ * B * max C 0 *
          Real.exp ((Θ - 1 / 2) / 2 * ℓ) ^ ν := by
        rw [← Real.exp_nat_mul, show (Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ =
          ν * ((Θ - 1 / 2) / 2 * ℓ) by ring]
        ring

/-- **E-Q5 (continuous `ThickLeft` almost-everywhere form).** If for every `a > 0` there is a set
`E_a` thick toward `−∞` on which `|F(u) e^{−8u}| ≤ C_a e^{−au}` almost everywhere, then
`AsymptoticAbscissaLaw` holds unconditionally. -/
theorem asymptoticAbscissaLaw_of_subexponential_thickLeft {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (h : ∀ a : ℝ, 0 < a → ∃ (E : Set ℝ) (C : ℝ), ThickLeft E ∧
      ∀ᵐ u ∂volume, u ∈ E → |F u * Real.exp (-(8 * u))| ≤ C * Real.exp (-(a * u))) :
    RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_thick_window_l1_bound hW hthreshold hF one_pos fun a ha => ?_
  obtain ⟨E, C, hE, hae⟩ := h a ha
  refine ⟨{ν : ℕ | Icc (-(((ν + 1 : ℕ) : ℝ) * 1)) (-((ν : ℝ) * 1)) ⊆ E},
    thick_of_thickLeft hE one_pos, max C 0 * Real.exp a, fun ν hν => ?_⟩
  set S : Set ℝ := Icc (-(((ν + 1 : ℕ) : ℝ) * 1)) (-((ν : ℝ) * 1))
  have hsub : S ⊆ E := hν
  have hK0 : 0 ≤ max C 0 * Real.exp a * Real.exp (a * (ν : ℝ) * 1) := by positivity
  have haeS : ∀ᵐ u ∂(volume.restrict S),
      |F u| * Real.exp (-(8 * u)) ≤ max C 0 * Real.exp a * Real.exp (a * (ν : ℝ) * 1) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Icc] with u hu hm
    have huE : |F u * Real.exp (-(8 * u))| ≤ C * Real.exp (-(a * u)) := hu (hsub hm)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at huE
    have hexp : Real.exp (-(a * u)) ≤ Real.exp a * Real.exp (a * (ν : ℝ) * 1) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hm1 : -(((ν + 1 : ℕ) : ℝ) * 1) ≤ u := hm.1
      push_cast at hm1
      nlinarith
    calc |F u| * Real.exp (-(8 * u))
        ≤ C * Real.exp (-(a * u)) := huE
      _ ≤ max C 0 * Real.exp (-(a * u)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C 0 * (Real.exp a * Real.exp (a * (ν : ℝ) * 1)) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right _ _)
      _ = max C 0 * Real.exp a * Real.exp (a * (ν : ℝ) * 1) := by ring
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hint : IntegrableOn (fun u => |F u| * Real.exp (-(8 * u))) S volume := by
    set lo : ℝ := -(((ν + 1 : ℕ) : ℝ) * 1)
    have hmaj : IntegrableOn (fun u => Real.exp (-(8 * lo)) * |F u|) S volume :=
      (hd.integrable.norm.const_mul _).integrableOn
    refine hmaj.mono' (hd.meas.abs.mul (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le), mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hu.1])) (abs_nonneg _)
  have hconst : IntegrableOn (fun _ : ℝ => max C 0 * Real.exp a * Real.exp (a * (ν : ℝ) * 1))
      S volume := integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hmono := integral_mono_ae hint hconst haeS
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by push_cast; linarith)] at hmono
  have hlen : -((ν : ℝ) * 1) - -(((ν + 1 : ℕ) : ℝ) * 1) = 1 := by push_cast; ring
  rw [hlen, smul_eq_mul, one_mul] at hmono
  exact hmono

/-- **E-Q5 (single thick set pointwise form).** If `E ⊆ ℝ` is thick toward `−∞` and `F(u) e^{−8u}`
is subexponential along `E`, then `AsymptoticAbscissaLaw` holds unconditionally. -/
theorem asymptoticAbscissaLaw_of_thickLeft_subexponential {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {E : Set ℝ} (hE : ThickLeft E)
    (h : ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ u ∈ E, |F u * Real.exp (-(8 * u))| ≤ C * Real.exp (-(a * u))) :
    RHTower.AsymptoticAbscissaLaw :=
  asymptoticAbscissaLaw_of_subexponential_thickLeft hW hthreshold hF fun a ha => by
    obtain ⟨C, hC⟩ := h a ha
    exact ⟨E, C, hE, Eventually.of_forall hC⟩

/-! ### Heated zero series receiver -/

/-- At any base `ℓ > 0`, an isolated top has a heat parameter `ε > 0` at which the heated zero
weights `L F(z_q) e^{ε z_q²}` have nonzero merged weight. -/
theorem exists_pos_heat_mergedWeight_ne_zero {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (_hℓ : 0 < ℓ)
    {S : Finset XiZeroCopy} {Θ : ℝ} (hSne : S.Nonempty) (hΘ : 1 / 2 < Θ)
    (hS : ∀ q ∈ S, (zetaConfig q).re = Θ) :
    ∃ (ε : ℝ) (q₀ : XiZeroCopy), 0 < ε ∧ q₀ ∈ S ∧
      (∑ j ∈ S with frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀,
        negativeHalfLineLaplace (cx F) (centredZero j) *
          Complex.exp ((ε : ℂ) * centredZero j ^ 2)) ≠ 0 := by
  classical
  obtain ⟨q₀, hq₀⟩ := hSne
  set Fib := S.filter fun j => frobTower ℓ zetaConfig j = frobTower ℓ zetaConfig q₀
  have hq₀F : q₀ ∈ Fib := mem_filter.2 ⟨hq₀, rfl⟩
  obtain ⟨qₘ, hqₘF, hqₘmin⟩ :=
    Fib.exists_min_image (fun j => |(centredZero j).im|) ⟨q₀, hq₀F⟩
  set σ : ℝ := Θ - 1 / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  set γ : ℝ := |(centredZero qₘ).im|
  have hγ0 : 0 ≤ γ := abs_nonneg _
  have hre_Fib : ∀ j ∈ Fib, (centredZero j).re = σ := fun j hj => by
    have := hS j (Finset.mem_filter.1 hj).1
    change ((j.1 : ℂ)).re = Θ at this
    simp [centredZero, σ, this]
  set Min := Fib.filter fun j => |(centredZero j).im| = γ
  set High := Fib.filter fun j => γ < |(centredZero j).im|
  have hpart : Fib = Min ∪ High := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Min, High]
    constructor
    · intro hj
      rcases eq_or_lt_of_le (hqₘmin j hj) with heq | hlt
      · exact Or.inl ⟨hj, heq.symm⟩
      · exact Or.inr ⟨hj, hlt⟩
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
  have hdisj : Disjoint Min High := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    exact (ne_of_gt (Finset.mem_filter.1 h2).2) (Finset.mem_filter.1 h1).2
  -- Gap `δ > 0` separating `Min` from `High` in `Re(z²) = σ² − (Im z)²`
  obtain ⟨δ, hδ, hHigh_re⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ j ∈ High, (centredZero j ^ 2).re ≤ σ ^ 2 - γ ^ 2 - δ := by
    by_cases hH : High.Nonempty
    · obtain ⟨q₂, hq₂H, hq₂min⟩ := High.exists_min_image (fun j => |(centredZero j).im|) hH
      have hlt : γ < |(centredZero q₂).im| := (mem_filter.1 hq₂H).2
      refine ⟨|(centredZero q₂).im| ^ 2 - γ ^ 2, by nlinarith, fun j hj => ?_⟩
      have hjF : j ∈ Fib := (mem_filter.1 hj).1
      have hge : |(centredZero q₂).im| ≤ |(centredZero j).im| := hq₂min j hj
      have hsq : |(centredZero q₂).im| ^ 2 ≤ (centredZero j).im ^ 2 := by
        rw [← sq_abs ((centredZero j).im)]
        exact pow_le_pow_left₀ (by positivity) hge 2
      have hre2 : (centredZero j ^ 2).re = σ ^ 2 - (centredZero j).im ^ 2 := by
        rw [sq, Complex.mul_re, hre_Fib j hjF]; ring
      linarith
    · exact ⟨1, one_pos, fun j hj => absurd ⟨j, hj⟩ hH⟩
  set W : ℝ := ∑ j ∈ High, ‖negativeHalfLineLaplace (cx F) (centredZero j)‖
  have hW_nonneg : 0 ≤ W := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hHigh_bound : ∀ ε : ℝ, 0 ≤ ε →
      ‖∑ j ∈ High, negativeHalfLineLaplace (cx F) (centredZero j) *
          Complex.exp ((ε : ℂ) * centredZero j ^ 2)‖ ≤
        W * Real.exp (ε * (σ ^ 2 - γ ^ 2) - ε * δ) := by
    intro ε hε
    calc ‖∑ j ∈ High, negativeHalfLineLaplace (cx F) (centredZero j) *
            Complex.exp ((ε : ℂ) * centredZero j ^ 2)‖
        ≤ ∑ j ∈ High, ‖negativeHalfLineLaplace (cx F) (centredZero j)‖ *
            Real.exp (ε * (σ ^ 2 - γ ^ 2) - ε * δ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
          nlinarith [hHigh_re j hj]
      _ = W * Real.exp (ε * (σ ^ 2 - γ ^ 2) - ε * δ) := by rw [← Finset.sum_mul]
  -- Evaluate the dominant `Min` part along a sequence of `ε > 0`
  have hMin_witness : ∃ (c₀ : ℝ), 0 < c₀ ∧ ∀ M : ℝ, ∃ ε : ℝ, M ≤ ε ∧ 0 < ε ∧
      c₀ * Real.exp (ε * (σ ^ 2 - γ ^ 2)) ≤
        ‖∑ j ∈ Min, negativeHalfLineLaplace (cx F) (centredZero j) *
          Complex.exp ((ε : ℂ) * centredZero j ^ 2)‖ := by
    rcases eq_or_lt_of_le hγ0 with hγz | hγpos
    · -- `γ = 0`: every `j ∈ Min` equals `(σ : ℂ)`
      have hj_eq : ∀ j ∈ Min, centredZero j = (σ : ℂ) := by
        intro j hj
        have hjF : j ∈ Fib := (mem_filter.1 hj).1
        have him : |(centredZero j).im| = 0 := by rw [(mem_filter.1 hj).2, ← hγz]
        apply Complex.ext
        · simp [hre_Fib j hjF]
        · simpa using abs_eq_zero.mp him
      have hcard_pos : 0 < Min.card := Finset.card_pos.2 ⟨qₘ, mem_filter.2 ⟨hqₘF, rfl⟩⟩
      have hL0 : negativeHalfLineLaplace (cx F) (σ : ℂ) ≠ 0 :=
        criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF
          (by simp [hσ.le])
      set c₀ : ℝ := (Min.card : ℝ) * ‖negativeHalfLineLaplace (cx F) (σ : ℂ)‖
      refine ⟨c₀, mul_pos (Nat.cast_pos.mpr hcard_pos) (norm_pos_iff.mpr hL0), fun M => ?_⟩
      set ε : ℝ := max M 1
      refine ⟨ε, le_max_left _ _, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
      have hsum_eq : (∑ j ∈ Min, negativeHalfLineLaplace (cx F) (centredZero j) *
          Complex.exp ((ε : ℂ) * centredZero j ^ 2)) =
          (Min.card : ℂ) * negativeHalfLineLaplace (cx F) (σ : ℂ) *
            Complex.exp (((ε * σ ^ 2 : ℝ) : ℂ)) := by
        have h1 : ∀ j ∈ Min, negativeHalfLineLaplace (cx F) (centredZero j) *
            Complex.exp ((ε : ℂ) * centredZero j ^ 2) =
            negativeHalfLineLaplace (cx F) (σ : ℂ) * Complex.exp (((ε * σ ^ 2 : ℝ) : ℂ)) := by
          intro j hj
          rw [hj_eq j hj]
          congr 2
          push_cast; ring
        rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      rw [hsum_eq, ← hγz, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp,
        Complex.ofReal_re]
      simp [c₀]
    · -- `γ > 0`: split `Min` into `σ + iγ` and `σ − iγ`
      set zP : ℂ := (σ : ℂ) + (γ : ℂ) * I
      set zM : ℂ := (σ : ℂ) - (γ : ℂ) * I
      have hzPM_ne : zP ≠ zM := by
        intro he
        have := congrArg Complex.im he
        simp [zP, zM] at this
        linarith
      set MinP := Min.filter fun j => centredZero j = zP
      set MinM := Min.filter fun j => centredZero j = zM
      have hMin_union : Min = MinP ∪ MinM := by
        ext j
        simp only [Finset.mem_union, Finset.mem_filter, MinP, MinM]
        constructor
        · intro hj
          have hjF : j ∈ Fib := (Finset.mem_filter.1 hj).1
          rcases abs_eq hγpos.le |>.1 (Finset.mem_filter.1 hj).2 with him | him
          · left; refine ⟨hj, Complex.ext (by simp [zP, hre_Fib j hjF]) (by simp [zP, him])⟩
          · right; refine ⟨hj, Complex.ext (by simp [zM, hre_Fib j hjF]) (by simp [zM, him])⟩
        · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
      have hMin_disj : Disjoint MinP MinM := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        exact hzPM_ne ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
      set AP : ℂ := (MinP.card : ℂ) * negativeHalfLineLaplace (cx F) zP
      set AM : ℂ := (MinM.card : ℂ) * negativeHalfLineLaplace (cx F) zM
      have hAP_or_AM : AP ≠ 0 ∨ AM ≠ 0 := by
        have hqₘM : qₘ ∈ Min := Finset.mem_filter.2 ⟨hqₘF, rfl⟩
        rw [hMin_union, Finset.mem_union] at hqₘM
        rcases hqₘM with hP | hM
        · left
          exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.2 ⟨qₘ, hP⟩).ne')
            (criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF
              (by simp [zP, hσ.le]))
        · right
          exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_pos.2 ⟨qₘ, hM⟩).ne')
            (criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF
              (by simp [zM, hσ.le]))
      have hsum_Min : ∀ ε : ℝ,
          (∑ j ∈ Min, negativeHalfLineLaplace (cx F) (centredZero j) *
            Complex.exp ((ε : ℂ) * centredZero j ^ 2)) =
          ((Real.exp (ε * (σ ^ 2 - γ ^ 2)) : ℝ) : ℂ) *
            (AP * Complex.exp (((2 * ε * σ * γ : ℝ) : ℂ) * I) +
              AM * Complex.exp (-(((2 * ε * σ * γ : ℝ) : ℂ) * I))) := by
        intro ε
        rw [hMin_union, Finset.sum_union hMin_disj]
        have hP_eq : (∑ j ∈ MinP, negativeHalfLineLaplace (cx F) (centredZero j) *
            Complex.exp ((ε : ℂ) * centredZero j ^ 2)) =
            ((Real.exp (ε * (σ ^ 2 - γ ^ 2)) : ℝ) : ℂ) *
              (AP * Complex.exp (((2 * ε * σ * γ : ℝ) : ℂ) * I)) := by
          have h1 : ∀ j ∈ MinP, negativeHalfLineLaplace (cx F) (centredZero j) *
              Complex.exp ((ε : ℂ) * centredZero j ^ 2) =
              negativeHalfLineLaplace (cx F) zP * Complex.exp ((ε : ℂ) * zP ^ 2) :=
            fun j hj => by rw [(mem_filter.1 hj).2]
          rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
          have hzP2 : (ε : ℂ) * zP ^ 2 =
              ((ε * (σ ^ 2 - γ ^ 2) : ℝ) : ℂ) + ((2 * ε * σ * γ : ℝ) : ℂ) * I := by
            dsimp [zP]; push_cast; linear_combination (ε : ℂ) * (γ : ℂ) ^ 2 * Complex.I_sq
          rw [hzP2, Complex.exp_add, Complex.ofReal_exp]
          dsimp [AP]; ring
        have hM_eq : (∑ j ∈ MinM, negativeHalfLineLaplace (cx F) (centredZero j) *
            Complex.exp ((ε : ℂ) * centredZero j ^ 2)) =
            ((Real.exp (ε * (σ ^ 2 - γ ^ 2)) : ℝ) : ℂ) *
              (AM * Complex.exp (-(((2 * ε * σ * γ : ℝ) : ℂ) * I))) := by
          have h1 : ∀ j ∈ MinM, negativeHalfLineLaplace (cx F) (centredZero j) *
              Complex.exp ((ε : ℂ) * centredZero j ^ 2) =
              negativeHalfLineLaplace (cx F) zM * Complex.exp ((ε : ℂ) * zM ^ 2) :=
            fun j hj => by rw [(mem_filter.1 hj).2]
          rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
          have hzM2 : (ε : ℂ) * zM ^ 2 =
              ((ε * (σ ^ 2 - γ ^ 2) : ℝ) : ℂ) + -(((2 * ε * σ * γ : ℝ) : ℂ) * I) := by
            dsimp [zM]; push_cast; linear_combination (ε : ℂ) * (γ : ℂ) ^ 2 * Complex.I_sq
          rw [hzM2, Complex.exp_add, Complex.ofReal_exp]
          dsimp [AM]; ring
        rw [hP_eq, hM_eq, mul_add]
      have hne_both : AP + AM ≠ 0 ∨ AP - AM ≠ 0 := by
        by_contra hboth
        push Not at hboth
        obtain ⟨h1, h2⟩ := hboth
        have hA1 : AP = 0 := by linear_combination (h1 + h2) / 2
        have hA2 : AM = 0 := by linear_combination (h1 - h2) / 2
        exact hAP_or_AM.elim (fun h => h hA1) (fun h => h hA2)
      have hden_pos : 0 < 2 * σ * γ := by positivity
      rcases hne_both with hsum_ne | hdiff_ne
      · refine ⟨‖AP + AM‖, norm_pos_iff.mpr hsum_ne, fun M => ?_⟩
        set k : ℕ := ⌈max 0 M * (2 * σ * γ) / (2 * Real.pi)⌉₊ + 1
        set ε : ℝ := (k : ℝ) * (2 * Real.pi) / (2 * σ * γ)
        have hk_pos : 0 < k := Nat.succ_pos _
        have hε_pos : 0 < ε := by positivity
        have hMε : M ≤ ε := by
          have h1 : max 0 M * (2 * σ * γ) / (2 * Real.pi) ≤ (k : ℝ) := by
            have := Nat.le_ceil (max 0 M * (2 * σ * γ) / (2 * Real.pi))
            dsimp [k]; push_cast; linarith
          have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 2 * Real.pi)
          rw [div_mul_cancel₀ _ (by positivity)] at h2
          have h3 := (le_div_iff₀ hden_pos).2 h2
          exact (le_max_right 0 M).trans h3
        refine ⟨ε, hMε, hε_pos, ?_⟩
        have hθ : 2 * ε * σ * γ = (k : ℤ) * (2 * Real.pi) := by
          dsimp [ε]; push_cast; field_simp
        rw [hsum_Min ε, hθ]
        have hexp1 : Complex.exp ((((k : ℤ) * (2 * Real.pi) : ℝ) : ℂ) * I) = 1 := by
          have : ((((k : ℤ) * (2 * Real.pi) : ℝ) : ℂ) * I) = ((k : ℤ) : ℂ) * (2 * Real.pi * I) := by
            push_cast; ring
          rw [this]
          exact Complex.exp_int_mul_two_pi_mul_I k
        have hexp2 : Complex.exp (-((((k : ℤ) * (2 * Real.pi) : ℝ) : ℂ) * I)) = 1 := by
          rw [Complex.exp_neg, hexp1, inv_one]
        rw [hexp1, hexp2, mul_one, mul_one, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      · refine ⟨‖AP - AM‖, norm_pos_iff.mpr hdiff_ne, fun M => ?_⟩
        set k : ℕ := ⌈max 0 M * (2 * σ * γ) / (2 * Real.pi)⌉₊ + 1
        set ε : ℝ := ((k : ℝ) * (2 * Real.pi) + Real.pi / 2) / (2 * σ * γ)
        have hε_pos : 0 < ε := by positivity
        have hMε : M ≤ ε := by
          have h1 : max 0 M * (2 * σ * γ) / (2 * Real.pi) ≤ (k : ℝ) := by
            have := Nat.le_ceil (max 0 M * (2 * σ * γ) / (2 * Real.pi))
            dsimp [k]; push_cast; linarith
          have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 2 * Real.pi)
          rw [div_mul_cancel₀ _ (by positivity)] at h2
          have h2' : max 0 M * (2 * σ * γ) ≤ (k : ℝ) * (2 * Real.pi) + Real.pi / 2 := by
            linarith [Real.pi_pos]
          exact (le_max_right 0 M).trans ((le_div_iff₀ hden_pos).2 h2')
        refine ⟨ε, hMε, hε_pos, ?_⟩
        have hθ : 2 * ε * σ * γ = (k : ℤ) * (2 * Real.pi) + Real.pi / 2 := by
          dsimp [ε]; push_cast; field_simp
        rw [hsum_Min ε, hθ]
        have hexpI : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
          rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
          simp
        have hexp1 : Complex.exp (((((k : ℤ) * (2 * Real.pi) + Real.pi / 2 : ℝ) : ℂ)) * I) = I := by
          have : (((((k : ℤ) * (2 * Real.pi) + Real.pi / 2 : ℝ) : ℂ)) * I) =
              ((k : ℤ) : ℂ) * (2 * Real.pi * I) + ((Real.pi / 2 : ℝ) : ℂ) * I := by
            push_cast; ring
          rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
          exact hexpI
        have hexp2 : Complex.exp (-(((((k : ℤ) * (2 * Real.pi) + Real.pi / 2 : ℝ) : ℂ)) * I)) = -I := by
          rw [Complex.exp_neg, hexp1, inv_I]
        rw [hexp1, hexp2]
        have hcalc : AP * I + AM * -I = (AP - AM) * I := by ring
        rw [hcalc, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_I, mul_one, mul_comm]
  obtain ⟨c₀, hc₀, hexε⟩ := hMin_witness
  -- Pick `ε` large enough that `W * e^{-ε δ} ≤ c₀ / 2`
  set M_req : ℝ := (Real.log ((2 * W + 1) / c₀) + 1) / δ
  obtain ⟨ε, hMε, hε_pos, hMin_ge⟩ := hexε M_req
  refine ⟨ε, q₀, hε_pos, hq₀, ?_⟩
  change (∑ j ∈ Fib, _) ≠ 0
  rw [hpart, Finset.sum_union hdisj]
  intro hzero
  have hnorm_eq : ‖∑ j ∈ Min, negativeHalfLineLaplace (cx F) (centredZero j) *
        Complex.exp ((ε : ℂ) * centredZero j ^ 2)‖ =
      ‖∑ j ∈ High, negativeHalfLineLaplace (cx F) (centredZero j) *
        Complex.exp ((ε : ℂ) * centredZero j ^ 2)‖ := by
    have : (∑ j ∈ Min, negativeHalfLineLaplace (cx F) (centredZero j) *
        Complex.exp ((ε : ℂ) * centredZero j ^ 2)) =
      -(∑ j ∈ High, negativeHalfLineLaplace (cx F) (centredZero j) *
        Complex.exp ((ε : ℂ) * centredZero j ^ 2)) := eq_neg_of_add_eq_zero_left hzero
    rw [this, norm_neg]
  have hHb := hHigh_bound ε hε_pos.le
  rw [← hnorm_eq] at hHb
  have hle_exp : c₀ * Real.exp (ε * (σ ^ 2 - γ ^ 2)) ≤
      W * Real.exp (ε * (σ ^ 2 - γ ^ 2) - ε * δ) := hMin_ge.trans hHb
  rw [show ε * (σ ^ 2 - γ ^ 2) - ε * δ = ε * (σ ^ 2 - γ ^ 2) + -(ε * δ) by ring,
    Real.exp_add] at hle_exp
  have hc_le : c₀ ≤ W * Real.exp (-(ε * δ)) := by
    have hpos := Real.exp_pos (ε * (σ ^ 2 - γ ^ 2))
    nlinarith
  have hεδ : Real.log ((2 * W + 1) / c₀) + 1 ≤ ε * δ := (div_le_iff₀ hδ).1 hMε
  have hexp_lt : W * Real.exp (-(ε * δ)) < c₀ := by
    have hpos_arg : 0 < (2 * W + 1) / c₀ := by positivity
    have h1 : Real.exp (-(ε * δ)) ≤ Real.exp (-Real.log ((2 * W + 1) / c₀)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg (Real.log ((2 * W + 1) / c₀)), Real.exp_log hpos_arg, inv_div] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hW_nonneg
    have h3 : W * (c₀ / (2 * W + 1)) < c₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  linarith

/-- **E-Q5 (heated zero series / `heatedState` form).** At any base `ℓ > 0`, if for every `ε > 0`
and `a > 0` the heated state `heatedState ε F (−νℓ)` grows at most `C e^{aνℓ}` along a thick set
of levels, then `AsymptoticAbscissaLaw` holds unconditionally. -/
theorem asymptoticAbscissaLaw_of_thick_heatedState_bound {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (h : ∀ ε a : ℝ, 0 < ε → 0 < a → ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
      ∀ ν ∈ G, |heatedState ε F (-((ν : ℝ) * ℓ))| ≤ C * Real.exp (a * ν * ℓ)) :
    RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  obtain ⟨ε, q₀, hε, hq₀, hvis⟩ :=
    exists_pos_heat_mergedWeight_ne_zero hW hthreshold hF hℓ hSne hΘ hS
  let b : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * Complex.exp ((ε : ℂ) * centredZero q ^ 2)
  have hb : Summable fun q => ‖b q‖ := by
    have hs := (criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε 0).summable.norm
    refine hs.congr fun q => ?_
    simp [b, stateHeatSymbol]
  obtain ⟨htop_norm, hlow_norm, hlt_norm⟩ := frobTower_isolatedTop hℓ hΘ₂ hS hrest
  obtain ⟨G₀, hG₀, C, hC⟩ := h ε ((Θ - 1 / 2) / 2) hε (by linarith)
  set n₀ : ℕ := ⌈4 * ε / ℓ⌉₊ + 1
  have hG : Thick (G₀ ∩ Ici n₀) := thick_inter_Ici hG₀ n₀
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have haW : 0 < criticalAliasCoefficient W₀ := criticalAliasCoefficient_positive hW
  set K_err : ℝ := rayL2Norm (unitLeftDatum W₀ hd) *
      ((2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε))
  have hK_nonneg : 0 ≤ K_err := by
    dsimp [K_err]
    exact mul_nonneg (rayL2Norm_nonneg _) (by positivity)
  have hρR : Real.exp ((Θ - 1 / 2) / 2 * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  refine not_forall_mem_thick_norm_levelSum_le (frobTower ℓ zetaConfig) b hb S
    (Real.exp_pos _) (Real.exp_pos _).le hlt_norm hlow_norm (fun q hq _ => htop_norm q hq)
    ⟨q₀, hq₀, hvis⟩ (C := criticalAliasCoefficient W₀ * (max C 0 + K_err))
    (Real.exp_pos _).le hρR hG fun ν ⟨hνG, hνn⟩ => ?_
  have hT : -((ν : ℝ) * ℓ) ≤ -(4 * ε) := by
    have hn : (n₀ : ℝ) ≤ (ν : ℝ) := by exact_mod_cast (mem_Ici.mp hνn)
    have hc : 4 * ε / ℓ ≤ (n₀ : ℝ) := by
      have := Nat.le_ceil (4 * ε / ℓ)
      dsimp [n₀]; push_cast; linarith
    have hmul := mul_le_mul_of_nonneg_right (hc.trans hn) hℓ.le
    rw [div_mul_cancel₀ _ hℓ.ne'] at hmul
    linarith
  have hrem := criticalState_heatedState_add_zeroSeries_le hW hthreshold hF hε hT
  have hser : (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
      stateHeatSymbol ε (-((ν : ℝ) * ℓ)) (centredZero q)) =
      levelSum (frobTower ℓ zetaConfig) b ν := by
    unfold levelSum
    refine tsum_congr fun q => ?_
    dsimp [b, stateHeatSymbol]
    rw [zpow_natCast, frobTower_pow, show centredZero q = zetaConfig q - 1 / 2 from rfl, mul_assoc,
      ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [hser] at hrem
  have hk_le : stateHeatKernel ε (-((ν : ℝ) * ℓ)) ≤
      (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) := by
    unfold stateHeatKernel
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
    have : 0 ≤ (-((ν : ℝ) * ℓ)) ^ 2 / (4 * ε) := by positivity
    linarith
  have hrem' : ‖((heatedState ε F (-((ν : ℝ) * ℓ)) : ℝ) : ℂ) +
      (criticalAliasCoefficient W₀ : ℂ)⁻¹ * levelSum (frobTower ℓ zetaConfig) b ν‖ ≤ K_err :=
    hrem.trans (mul_le_mul_of_nonneg_left hk_le (rayL2Norm_nonneg _))
  have ha0 : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr haW.ne'
  have hid : levelSum (frobTower ℓ zetaConfig) b ν =
      (criticalAliasCoefficient W₀ : ℂ) *
        ((((heatedState ε F (-((ν : ℝ) * ℓ)) : ℝ) : ℂ) +
          (criticalAliasCoefficient W₀ : ℂ)⁻¹ * levelSum (frobTower ℓ zetaConfig) b ν) -
          ((heatedState ε F (-((ν : ℝ) * ℓ)) : ℝ) : ℂ)) := by
    rw [mul_sub, mul_add, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    ring
  have htri : ‖levelSum (frobTower ℓ zetaConfig) b ν‖ ≤
      criticalAliasCoefficient W₀ * (K_err + |heatedState ε F (-((ν : ℝ) * ℓ))|) := by
    rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg haW.le]
    refine mul_le_mul_of_nonneg_left ?_ haW.le
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hrem']
  have hexp1 : 1 ≤ Real.exp ((Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ) :=
    Real.one_le_exp (by positivity)
  have hC' : |heatedState ε F (-((ν : ℝ) * ℓ))| ≤
      max C 0 * Real.exp ((Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ) :=
    (hC ν hνG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hK' : K_err ≤ K_err * Real.exp ((Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ) :=
    le_mul_of_one_le_right hK_nonneg hexp1
  calc ‖levelSum (frobTower ℓ zetaConfig) b ν‖
      ≤ criticalAliasCoefficient W₀ *
          ((max C 0 + K_err) * Real.exp ((Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ)) := by
        refine htri.trans (mul_le_mul_of_nonneg_left ?_ haW.le)
        nlinarith
    _ = criticalAliasCoefficient W₀ * (max C 0 + K_err) *
          Real.exp ((Θ - 1 / 2) / 2 * ℓ) ^ ν := by
        rw [← Real.exp_nat_mul, show (Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ =
          ν * ((Θ - 1 / 2) / 2 * ℓ) by ring]
        ring

/-! ### Contrapositive syndetic excursions and `a = 0` exclusion corollaries -/

/-- **Contrapositive syndetic excursion law.** If `AsymptoticAbscissaLaw` fails, then a critical
half-line ground state `F` exists at a finite threshold `W₀ > 0`, and there exist `k ≥ 1` and
`a > 0` such that at **every** base `ℓ > 0` and for every `C : ℝ`, beyond some level every window
of `k` consecutive levels contains `ν` with
`C e^{aνℓ} < ∫_{−(ν+1)ℓ}^{−νℓ} |F(u)| e^{−8u} du`. -/
theorem exists_syndetic_state_excursions_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∃ k : ℕ, 0 < k ∧ ∃ a : ℝ, 0 < a ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ C : ℝ,
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + k ∧
          C * Real.exp (a * ν * ℓ) <
            ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
              |F u| * Real.exp (-(8 * u)) := by
  have hnotRH : ¬ RiemannHypothesis := fun hRH =>
    hnot (RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.1 hRH).2
  obtain ⟨W₀, F, hW, hthreshold, hF⟩ :=
    (riemannHypothesis_or_exists_criticalHalfLineGroundState).resolve_left hnotRH
  rw [asymptoticAbscissaLaw_zetaConfig_iff, not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  refine ⟨W₀, F, hW, hthreshold, hF, S.card, hSne.card_pos, (Θ - 1 / 2) / 2, by linarith,
    fun ℓ hℓ C => ?_⟩
  obtain ⟨ψ₀, B, q₀, hψ₀, hs₀, hsupp₀, hB0, hbound, hq₀, hvis⟩ :=
    exists_isolating_bump_on_top hW hthreshold hF hℓ hSne hΘ hS
  have h0 : ∀ x, 0 < x → ψ₀ x = 0 := fun x hx =>
    hsupp₀ x fun hm => lt_irrefl (0 : ℝ) (hx.trans hm.2)
  let b : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ₀ (centredZero q)
  have hb : Summable fun q => ‖b q‖ :=
    (criticalState_hasSum_zeroSeries_test_left hW hthreshold hF hψ₀ hs₀ h0).summable.norm
  obtain ⟨htop_norm, hlow_norm, hlt_norm⟩ := frobTower_isolatedTop hℓ hΘ₂ hS hrest
  have haW : 0 < criticalAliasCoefficient W₀ := criticalAliasCoefficient_positive hW
  set K : ℝ := criticalAliasCoefficient W₀ * (B + 1)
  have hK : 0 < K := by positivity
  have hρR : Real.exp ((Θ - 1 / 2) / 2 * ℓ) < Real.exp (ℓ * (Θ - 1 / 2)) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  obtain ⟨M₀, hM₀⟩ := eventually_forall_window_exists_lt_norm_levelSum (frobTower ℓ zetaConfig) b
    hb S (Real.exp_pos _) (Real.exp_pos _).le hlt_norm hlow_norm (fun q hq _ => htop_norm q hq)
    ⟨q₀, hq₀, hvis⟩ (C := K * max C 0) (Real.exp_pos _).le hρR
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨ν, h1, h2, h3⟩ := hM₀ M hM
  have hk_le : (S.image (frobTower ℓ zetaConfig)).card ≤ S.card := Finset.card_image_le
  refine ⟨ν, h1, by omega, ?_⟩
  rw [criticalState_levelSum_laplaceTest hW hthreshold hF hψ₀ hs₀ h0 hℓ.le ν,
    norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg haW.le,
    ← Real.exp_nat_mul, show ↑ν * ((Θ - 1 / 2) / 2 * ℓ) = (Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ by ring]
    at h3
  have hp := norm_statePairing_shift_le hd (by linarith : 0 ≤ B + 1)
    (fun v => (hbound v).trans (by linarith)) hsupp₀ ν
  have h4 : K * max C 0 * Real.exp ((Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ) <
      K * ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
        |F u| * Real.exp (-(8 * u)) :=
    h3.trans_le (by
      dsimp [K]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp haW.le)
  have h5 : max C 0 * Real.exp ((Θ - 1 / 2) / 2 * (ν : ℝ) * ℓ) <
      ∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
        |F u| * Real.exp (-(8 * u)) := by
    rw [mul_assoc] at h4
    exact lt_of_mul_lt_mul_left h4 hK.le
  exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le).trans_lt h5

/-- No critical state exists under `RiemannHypothesis`. -/
private theorem false_of_riemannHypothesis_of_threshold (hRH : RiemannHypothesis) {W₀ : ℝ}
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) : False := by
  have htop : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = ⊤ := by
    refine le_antisymm le_top (le_iInf fun A => le_iInf fun hA => ?_)
    rw [riemannHypothesis_iff_windowThreshold_eq_top.1 hRH A hA]
  rw [htop] at hthreshold
  exact EReal.top_ne_coe W₀ hthreshold

/-- **Under `ZerosApproachLine`, no critical state has bounded window `L¹` mass on a thick set.** -/
theorem no_criticalState_thick_window_bounded_of_zerosApproachLine
    (hZAL : RHTower.BacklundConverse.ZerosApproachLine) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : Set ℕ} (hG : Thick G) {C : ℝ}
    (hbd : ∀ ν ∈ G, (∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
      |F u| * Real.exp (-(8 * u))) ≤ C) : False := by
  have hAAL : RHTower.AsymptoticAbscissaLaw :=
    asymptoticAbscissaLaw_of_thick_window_l1_bound hW hthreshold hF hℓ fun a ha =>
      ⟨G, hG, max C 0, fun ν hν => (hbd ν hν).trans
        ((le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _)
          (Real.one_le_exp (by positivity))))⟩
  exact false_of_riemannHypothesis_of_threshold
    (RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.2 ⟨hZAL, hAAL⟩)
    hthreshold

/-- **Under `FiniteOffLine`, no critical state has bounded window `L¹` mass on a thick set.** -/
theorem no_criticalState_thick_window_bounded_of_finiteOffLine
    (hfin : GaloisForLFunctions.InfiniteRankWeilTheory.FiniteOffLine) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : Set ℕ} (hG : Thick G) {C : ℝ}
    (hbd : ∀ ν ∈ G, (∫ u in Icc (-(((ν + 1 : ℕ) : ℝ) * ℓ)) (-((ν : ℝ) * ℓ)),
      |F u| * Real.exp (-(8 * u))) ≤ C) : False :=
  no_criticalState_thick_window_bounded_of_zerosApproachLine
    (zerosApproachLine_of_finiteOffLine hfin) hW hthreshold hF hℓ hG hbd

/-- **Under `ZerosApproachLine`, no critical state has `|F(u) e^{−8u}|` bounded on a `ThickLeft`
set.** -/
theorem no_criticalState_thickLeft_bounded_of_zerosApproachLine
    (hZAL : RHTower.BacklundConverse.ZerosApproachLine) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {E : Set ℝ} (hE : ThickLeft E) {C : ℝ}
    (hbd : ∀ᵐ u ∂volume, u ∈ E → |F u * Real.exp (-(8 * u))| ≤ C) : False := by
  have hAAL : RHTower.AsymptoticAbscissaLaw :=
    asymptoticAbscissaLaw_of_subexponential_thickLeft hW hthreshold hF fun a ha =>
      ⟨E, max C 0, hE, by
        filter_upwards [hbd] with u hu hm
        by_cases hu0 : u ≤ 0
        · exact (hu hm).trans ((le_max_left _ _).trans
            (le_mul_of_one_le_right (le_max_right _ _)
              (Real.one_le_exp (by nlinarith))))
        · push Not at hu0
          have h0 : F u = 0 := (criticalHalfLineEnergyDomain_of_groundState hF).support u hu0.le
          rw [h0, zero_mul, abs_zero]
          positivity⟩
  exact false_of_riemannHypothesis_of_threshold
    (RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.2 ⟨hZAL, hAAL⟩)
    hthreshold

end GaloisForLFunctions.ExclusionOfTheCriticalState
