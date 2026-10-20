import GaloisForLFunctions.SquareRootThreshold.CrystalVariationalPrinciple

/-!
# The relaxed Hodge exponent of a periodic configuration is twice its maximal depth

The relaxed Hodge index with exponent `θ` (`RHTower.RelaxedHodgeIndexAtLevel Z θ a`) asks
`Re W(f, f) ≥ −e^{θa} ∫|f|²` on polar-constrained tests of aperture `a`. For the off-line lattice
the threshold exponent is `2δ` (`RelaxedHodgeExponentOfOffLineLattices`). This module shows that
the same holds for every periodic configuration, with `δ` replaced by the maximal depth
`d_max = max_r d_r`.

**Setting.** A lag-lattice configuration with Hermitian symbol
`D(m) = Σ_r 2cosh(d_r mℓ) z_r^m` (`m ≥ 0`), `P` distinct unit nodes `z_r`, depths `d_r ≥ 0`, one of
them positive. This covers periodic off-line patterns (`z_r = e^{2πiθ_r}`) and periodic depth
profiles on a lattice (`z_r = e^{2πir/P}`, on-line residues allowed).

* **Above `2d_max`** (`toeplitz_floor_eventually_of_gt`). By Gershgorin every mode is at most
  `2P e^{d_max |m|ℓ}`, so the Weil floor at aperture `a` is at least `−4P(2a + ℓ) e^{2d_max a}`.
* **Below `2d_max`** (`not_toeplitz_floor_eventually_of_lt`). The deepest nodes dominate the modes,
  and their power sums cannot all be small on `|S|` consecutive exponents
  (`exists_powerSum_window_lower`: compactness of the torus and Lagrange interpolation,
  `eq_zero_of_moments_eq_zero`). So some mode `m ∈ [n − P, n)` has `|D(m)| ≥ c e^{d_max mℓ}`, and the
  `2 × 2` minor at `{0, m}` puts the floor below `2P − c' e^{2d_max a}`.

**Exponent law** (`patternConfig_relaxedHodge_eventually_of_lt`,
`patternConfig_not_relaxedHodge_eventually_of_lt`, `profileConfig_relaxedHodge_eventually_of_lt`,
`profileConfig_not_relaxedHodge_eventually_of_lt`). For `θ > 2d_max` the relaxed index holds at all
large levels (even on unconstrained tests); for `θ < 2d_max` it fails at all large levels, by
polar-constrained tests, with any constant in front of `e^{θa}`. The exponent of the relaxed Hodge
index reads off exactly the maximal depth, whatever the shape of the periodic configuration.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Power sums of distinct unit nodes on windows -/

/-- **Lagrange.** If `Σ_r w_r z_r^j = 0` for `j < |ι|` and the nodes are distinct, `w = 0`. -/
theorem eq_zero_of_moments_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ℂ)
    (hinj : Function.Injective z) (w : ι → ℂ)
    (h : ∀ j : ℕ, j < Fintype.card ι → ∑ r, w r * z r ^ j = 0) (r₀ : ι) : w r₀ = 0 := by
  set Q : Polynomial ℂ := ∏ r ∈ Finset.univ.erase r₀, (Polynomial.X - Polynomial.C (z r))
    with hQ
  have hdeg : Q.natDegree < Fintype.card ι := by
    refine lt_of_le_of_lt (Polynomial.natDegree_prod_le _ _) ?_
    refine lt_of_le_of_lt (Finset.sum_le_sum fun r _ => Polynomial.natDegree_X_sub_C_le (z r)) ?_
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    have := Fintype.card_pos_iff.mpr ⟨r₀⟩
    omega
  have heval : ∀ x : ℂ, Q.eval x = ∑ j ∈ Finset.range (Fintype.card ι), Q.coeff j * x ^ j :=
    fun x => Polynomial.eval_eq_sum_range' hdeg x
  have hsum : ∑ r, w r * Q.eval (z r) = 0 := by
    simp_rw [heval, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [show ∑ r, w r * (Q.coeff j * z r ^ j) = Q.coeff j * ∑ r, w r * z r ^ j by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring,
      h j (Finset.mem_range.mp hj), mul_zero]
  have hvan : ∀ r, r ≠ r₀ → Q.eval (z r) = 0 := fun r hr => by
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩) (by simp)
  rw [Finset.sum_eq_single r₀ (fun r _ hr => by rw [hvan r hr, mul_zero]) (by simp)] at hsum
  have hQ0 : Q.eval (z r₀) ≠ 0 := by
    rw [hQ, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun r hr => ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hr).1 (hinj h).symm
  exact (mul_eq_zero.mp hsum).resolve_right hQ0

/-- **Power sums on windows.** For distinct unit nodes there is `c > 0` such that every window of
`|ι|` consecutive exponents contains one with `|Σ_r z_r^m| ≥ c`. -/
theorem exists_powerSum_window_lower {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (z : ι → ℂ) (hz : ∀ r, ‖z r‖ = 1) (hinj : Function.Injective z) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ j : ℕ, j < Fintype.card ι ∧ c ≤ ‖∑ r, z r ^ (k + j)‖ := by
  set K : Set (ι → ℂ) := Set.univ.pi fun _ => Metric.sphere (0 : ℂ) 1 with hKdef
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_sphere 0 1
  have hKne : K.Nonempty := ⟨fun _ => 1, fun r _ => by simp⟩
  set F : (ι → ℂ) → ℝ := fun w => ∑ j ∈ Finset.range (Fintype.card ι), ‖∑ r, w r * z r ^ j‖
    with hFdef
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun j _ => ?_
    exact (continuous_finsetSum _ fun r _ => (continuous_apply r).mul continuous_const).norm
  obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hKne hF.continuousOn
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hpos : 0 < F w₀ := by
    by_contra hle
    push Not at hle
    have hzero : F w₀ = 0 := le_antisymm hle (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hall : ∀ j, j < Fintype.card ι → ∑ r, w₀ r * z r ^ j = 0 := fun j hj =>
      norm_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).mp hzero j
        (Finset.mem_range.mpr hj))
    obtain ⟨r₀⟩ := (inferInstance : Nonempty ι)
    have h0 := eq_zero_of_moments_eq_zero z hinj w₀ hall r₀
    have h1 : ‖w₀ r₀‖ = 1 := by
      have := hw₀ r₀ (Set.mem_univ _)
      simpa using this
    rw [h0, norm_zero] at h1
    norm_num at h1
  refine ⟨F w₀ / Fintype.card ι, by positivity, fun k => ?_⟩
  have hmem : (fun r => z r ^ k) ∈ K := fun r _ => by simp [norm_pow, hz r]
  have hk : F w₀ ≤ F (fun r => z r ^ k) := isMinOn_iff.mp hmin _ hmem
  by_contra hcon
  push Not at hcon
  have hlt : F (fun r => z r ^ k) < F w₀ := by
    calc F (fun r => z r ^ k) = ∑ j ∈ Finset.range (Fintype.card ι), ‖∑ r, z r ^ (k + j)‖ := by
          simp only [hFdef, pow_add]
      _ < ∑ _j ∈ Finset.range (Fintype.card ι), F w₀ / Fintype.card ι :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hcard.ne')
            fun j hj => hcon j (Finset.mem_range.mp hj)
      _ = F w₀ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  linarith

/-! ### Floors of cosh-weighted periodic symbols -/

/-- A Toeplitz floor `μ` bounds every mode: `μ ≤ Re D(0) − |D(m)|` for `1 ≤ m < n`. -/
theorem floor_le_diagonal_sub_mode {D : ℤ → ℂ} (hD : ∀ m, D (-m) = conj (D m)) {n : ℕ} {μ : ℝ}
    (hT : ∀ c : Fin n → ℂ, μ * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D n c).re) {m : ℕ} (hm1 : 1 ≤ m)
    (hmn : m < n) : μ ≤ (D 0).re - ‖D m‖ := by
  have hE : ∀ k, shiftSymbol D μ (-k) = conj (shiftSymbol D μ k) := by
    intro k
    simp only [shiftSymbol, lagDelta, neg_eq_zero, map_sub, map_mul, Complex.conj_ofReal, hD]
    split_ifs <;> simp
  have hT' : ∀ c : Fin n → ℂ, 0 ≤ (toeplitzForm (shiftSymbol D μ) n c).re := fun c => by
    rw [toeplitzForm_shiftSymbol, Complex.sub_re, Complex.ofReal_re]
    linarith [hT c]
  have h1 := norm_le_of_toeplitzForm_nonneg hE hT' hm1 hmn
  have h2 : shiftSymbol D μ m = D m := by
    simp only [shiftSymbol, lagDelta]
    rw [if_neg (by exact_mod_cast (by omega : m ≠ 0)), mul_zero, sub_zero]
  have h3 : (shiftSymbol D μ 0).re = (D 0).re - μ := by
    simp [shiftSymbol, lagDelta]
  rw [h2, h3] at h1
  linarith

/-- The data of a cosh-weighted periodic symbol `D(m) = Σ_r 2cosh(d_r mℓ) z_r^m`. -/
structure CoshSymbolData (ℓ : ℝ) (D : ℤ → ℂ) (P : ℕ) where
  /-- depths -/
  d : Fin P → ℝ
  /-- nodes -/
  z : Fin P → ℂ
  hd0 : ∀ r, 0 ≤ d r
  hpos : ∃ r, 0 < d r
  hz : ∀ r, ‖z r‖ = 1
  hinj : Function.Injective z
  herm : ∀ m, D (-m) = conj (D m)
  modes : ∀ m : ℕ, D m = ∑ r, ((2 * Real.cosh (d r * (m * ℓ)) : ℝ) : ℂ) * z r ^ m

namespace CoshSymbolData

variable {ℓ : ℝ} {D : ℤ → ℂ} {P : ℕ} (S : CoshSymbolData ℓ D P)
include S

theorem hP : 0 < P := by
  obtain ⟨r, -⟩ := S.hpos
  exact Fin.pos r

/-- The maximal depth. -/
def dmax : ℝ := Finset.univ.sup' ⟨⟨0, S.hP⟩, Finset.mem_univ _⟩ S.d

theorem le_dmax (r : Fin P) : S.d r ≤ S.dmax := Finset.le_sup' S.d (Finset.mem_univ r)

theorem dmax_pos : 0 < S.dmax := by
  obtain ⟨r, hr⟩ := S.hpos
  exact lt_of_lt_of_le hr (S.le_dmax r)

theorem zero_re : (D 0).re = 2 * P := by
  have := S.modes 0
  simp only [Nat.cast_zero, zero_mul, mul_zero, Real.cosh_zero, pow_zero, mul_one] at this
  rw [this, Complex.re_sum]
  simp only [Complex.ofReal_re, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Every mode is at most `2P e^{d_max |m|ℓ}`. -/
theorem norm_mode_le (hℓ : 0 < ℓ) (m : ℤ) :
    ‖D m‖ ≤ 2 * P * Real.exp (S.dmax * (|(m : ℝ)| * ℓ)) := by
  have hnat : ∀ k : ℕ, ‖D k‖ ≤ 2 * P * Real.exp (S.dmax * (k * ℓ)) := by
    intro k
    rw [S.modes k]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ r, ‖((2 * Real.cosh (S.d r * (k * ℓ)) : ℝ) : ℂ) * S.z r ^ k‖
        ≤ ∑ _r : Fin P, 2 * Real.exp (S.dmax * (k * ℓ)) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [norm_mul, norm_pow, S.hz r, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
          have hx : 0 ≤ S.d r * (k * ℓ) := mul_nonneg (S.hd0 r) (by positivity)
          have h1 : Real.cosh (S.d r * (k * ℓ)) ≤ Real.exp (S.d r * (k * ℓ)) := by
            rw [Real.cosh_eq]
            have := Real.exp_le_exp.mpr (by linarith : -(S.d r * (k * ℓ)) ≤ S.d r * (k * ℓ))
            linarith
          have h2 : Real.exp (S.d r * (k * ℓ)) ≤ Real.exp (S.dmax * (k * ℓ)) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (S.le_dmax r) (by positivity))
          linarith
      _ = 2 * P * Real.exp (S.dmax * (k * ℓ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    exact hnat k
  · rw [S.herm, Complex.norm_conj, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (by positivity)]
    exact hnat k

/-- **Deepest nodes dominate.** There are `c > 0` and `K₀` such that every window `[k, k + P)`,
`k ≥ K₀`, contains a mode with `|D(m)| ≥ c e^{d_max mℓ}`. -/
theorem exists_mode_lower (hℓ : 0 < ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → ∃ m : ℕ, k ≤ m ∧ m < k + P ∧
      c * Real.exp (S.dmax * (m * ℓ)) ≤ ‖D m‖ := by
  classical
  set T : Finset (Fin P) := Finset.univ.filter fun r => S.d r = S.dmax with hT
  obtain ⟨r₀, -, hr₀⟩ := Finset.exists_mem_eq_sup' ⟨⟨0, S.hP⟩, Finset.mem_univ _⟩ S.d
  haveI : Nonempty T := ⟨⟨r₀, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hr₀.symm⟩⟩⟩
  obtain ⟨c₀, hc₀, hwin⟩ := exists_powerSum_window_lower (fun i : T => S.z i)
    (fun i => S.hz i) (fun i j h => Subtype.ext (S.hinj h))
  -- a uniform gap below the maximal depth
  obtain ⟨g, hg, hgap⟩ : ∃ g : ℝ, 0 < g ∧ ∀ r, r ∉ T → S.d r ≤ S.dmax - g := by
    by_cases hc : (Finset.univ.filter fun r => r ∉ T).Nonempty
    · refine ⟨(Finset.univ.filter fun r => r ∉ T).inf' hc fun r => S.dmax - S.d r, ?_,
        fun r hr => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro r hr
        rw [Finset.mem_filter, hT, Finset.mem_filter] at hr
        have := lt_of_le_of_ne (S.le_dmax r) fun h => hr.2 ⟨Finset.mem_univ _, h⟩
        linarith
      · have := Finset.inf'_le (fun r => S.dmax - S.d r)
          (show r ∈ Finset.univ.filter fun r => r ∉ T by
            rw [Finset.mem_filter]; exact ⟨Finset.mem_univ r, hr⟩)
        linarith
    · refine ⟨1, one_pos, fun r hr => absurd ⟨r, show r ∈ Finset.univ.filter fun r => r ∉ T by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ r, hr⟩⟩ hc⟩
  obtain ⟨a₁, ha₁⟩ := exists_exp_neg_le (by positivity : 0 < g * ℓ)
    (by positivity : 0 < c₀ / (4 * (P + 1)))
  refine ⟨c₀ / 2, by positivity, ⌈max a₁ 0⌉₊, fun k hk => ?_⟩
  obtain ⟨j, hj, hjc⟩ := hwin k
  have hjP : j < P := lt_of_lt_of_le hj (by
    rw [Fintype.card_coe]; exact (Finset.card_filter_le _ _).trans (by simp))
  refine ⟨k + j, by omega, by omega, ?_⟩
  set m := k + j with hm
  have hmk : a₁ ≤ (m : ℝ) := by
    have : (⌈max a₁ 0⌉₊ : ℝ) ≤ m := by exact_mod_cast (by omega : ⌈max a₁ 0⌉₊ ≤ m)
    linarith [Nat.le_ceil (max a₁ 0), le_max_left a₁ 0]
  -- split the mode into the deepest nodes and the rest
  have hsplit : D m = ((2 * Real.cosh (S.dmax * (m * ℓ)) : ℝ) : ℂ) * ∑ i : T, S.z i ^ m +
      ∑ r ∈ Finset.univ.filter (fun r => r ∉ T),
        ((2 * Real.cosh (S.d r * (m * ℓ)) : ℝ) : ℂ) * S.z r ^ m := by
    rw [S.modes m, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => r ∈ T),
      Finset.sum_coe_sort T (fun r => S.z r ^ m), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr (by ext r; simp) fun r hr => ?_
    rw [Finset.mem_filter] at hr
    have : S.d r = S.dmax := by simpa [hT] using hr.2
    rw [this]
  have hE : 0 < Real.exp (S.dmax * (m * ℓ)) := Real.exp_pos _
  have hmain : c₀ * Real.exp (S.dmax * (m * ℓ)) ≤
      ‖((2 * Real.cosh (S.dmax * (m * ℓ)) : ℝ) : ℂ) * ∑ i : T, S.z i ^ m‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : Real.exp (S.dmax * (m * ℓ)) ≤ 2 * Real.cosh (S.dmax * (m * ℓ)) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(S.dmax * (m * ℓ)))]
    have h2 : c₀ ≤ ‖∑ i : T, S.z i ^ m‖ := hjc
    nlinarith [norm_nonneg (∑ i : T, S.z i ^ m)]
  have hrest : ‖∑ r ∈ Finset.univ.filter (fun r => r ∉ T),
      ((2 * Real.cosh (S.d r * (m * ℓ)) : ℝ) : ℂ) * S.z r ^ m‖ ≤
        c₀ / 2 * Real.exp (S.dmax * (m * ℓ)) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ r ∈ Finset.univ.filter (fun r => r ∉ T),
        ‖((2 * Real.cosh (S.d r * (m * ℓ)) : ℝ) : ℂ) * S.z r ^ m‖ ≤
          2 * Real.exp ((S.dmax - g) * (m * ℓ)) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      rw [norm_mul, norm_pow, S.hz r, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have hx : 0 ≤ S.d r * (m * ℓ) := mul_nonneg (S.hd0 r) (by positivity)
      have h1 : Real.cosh (S.d r * (m * ℓ)) ≤ Real.exp (S.d r * (m * ℓ)) := by
        rw [Real.cosh_eq]
        have := Real.exp_le_exp.mpr (by linarith : -(S.d r * (m * ℓ)) ≤ S.d r * (m * ℓ))
        linarith
      have h2 : Real.exp (S.d r * (m * ℓ)) ≤ Real.exp ((S.dmax - g) * (m * ℓ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hgap r hr.2) (by positivity))
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter (fun r => r ∉ T)).card : ℝ) ≤ P := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    have hsplitE : Real.exp ((S.dmax - g) * (m * ℓ)) =
        Real.exp (-(g * ℓ * m)) * Real.exp (S.dmax * (m * ℓ)) := by
      rw [← Real.exp_add]; ring_nf
    have hsmall := ha₁ m hmk
    rw [hsplitE]
    have hP1 : (0 : ℝ) < P + 1 := by positivity
    rw [le_div_iff₀ (by positivity)] at hsmall
    have h3 : Real.exp (-(g * ℓ * m)) * (4 * (P + 1)) ≤ c₀ := hsmall
    have h4 := Real.exp_pos (-(g * ℓ * m))
    have hc0 : (0 : ℝ) ≤ ((Finset.univ.filter (fun r => r ∉ T)).card : ℝ) := Nat.cast_nonneg _
    have h5 : ((Finset.univ.filter (fun r => r ∉ T)).card : ℝ) * (2 * Real.exp (-(g * ℓ * m))) ≤
        c₀ / 2 := by nlinarith
    calc ((Finset.univ.filter (fun r => r ∉ T)).card : ℝ) *
          (2 * (Real.exp (-(g * ℓ * m)) * Real.exp (S.dmax * (m * ℓ))))
        = (((Finset.univ.filter (fun r => r ∉ T)).card : ℝ) * (2 * Real.exp (-(g * ℓ * m)))) *
            Real.exp (S.dmax * (m * ℓ)) := by ring
      _ ≤ c₀ / 2 * Real.exp (S.dmax * (m * ℓ)) := mul_le_mul_of_nonneg_right h5 hE.le
  rw [hsplit]
  have := norm_sub_norm_le (((2 * Real.cosh (S.dmax * (m * ℓ)) : ℝ) : ℂ) * ∑ i : T, S.z i ^ m)
    (-(∑ r ∈ Finset.univ.filter (fun r => r ∉ T),
      ((2 * Real.cosh (S.d r * (m * ℓ)) : ℝ) : ℂ) * S.z r ^ m))
  rw [norm_neg, sub_neg_eq_add] at this
  linarith

/-- **Above twice the maximal depth.** For `θ > 2d_max`, eventually in `a` the Toeplitz floor of
size `⌈2a/ℓ⌉` is at least `−e^{θa}/ℓ`. -/
theorem toeplitz_floor_eventually_of_gt (hℓ : 0 < ℓ) {θ : ℝ} (hθ : 2 * S.dmax < θ) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀, ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ,
      -(Real.exp (θ * a) / ℓ) * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast S.hP
  obtain ⟨a₁, ha₁⟩ := exists_linear_le_exp (sub_pos.mpr hθ) (div_pos one_pos (by linarith) :
    (0 : ℝ) < 1 / (4 * (P : ℝ))) ℓ
  refine ⟨max a₁ 1, fun a ha => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ha)
  generalize hn : ⌈2 * a / ℓ⌉₊ = n
  intro c
  have hnhi : (n : ℝ) * ℓ < 2 * a + ℓ := by
    have h2 : (n : ℝ) < 2 * a / ℓ + 1 := by
      rw [← hn]; exact Nat.ceil_lt_add_one (by positivity)
    have : (2 * a / ℓ + 1) * ℓ = 2 * a + ℓ := by field_simp
    nlinarith
  have hG := re_toeplitzForm_ge D c
  have hsum : ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, ‖D m‖ ≤
      2 * n * (2 * P * Real.exp (2 * S.dmax * a)) := by
    calc ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, ‖D m‖
        ≤ ∑ _m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, 2 * P * Real.exp (2 * S.dmax * a) := by
          refine Finset.sum_le_sum fun m hm => (S.norm_mode_le hℓ m).trans ?_
          rw [Finset.mem_erase, Finset.mem_Ioo] at hm
          have hm' : (|(m : ℝ)|) * ℓ ≤ 2 * a := by
            have : (|(m : ℝ)|) ≤ n - 1 := by
              rw [← Int.cast_abs]
              have : |m| ≤ (n : ℤ) - 1 := abs_le.mpr ⟨by omega, by omega⟩
              exact_mod_cast this
            have hnlt : ((n : ℝ) - 1) * ℓ < 2 * a := by
              have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * a / ℓ)
              rw [hn] at this
              have h2 : (n : ℝ) - 1 < 2 * a / ℓ := by linarith
              rwa [lt_div_iff₀ hℓ] at h2
            nlinarith
          have := S.dmax_pos
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
      _ ≤ 2 * n * (2 * P * Real.exp (2 * S.dmax * a)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          have : ((Finset.Ioo (-(n : ℤ)) n).erase 0).card ≤ 2 * n := by
            refine (Finset.card_erase_le).trans ?_
            rw [Int.card_Ioo]
            omega
          exact_mod_cast this
  have hlin := ha₁ a (le_trans (le_max_left _ _) ha)
  have hexp : Real.exp (θ * a) = Real.exp ((θ - 2 * S.dmax) * a) * Real.exp (2 * S.dmax * a) := by
    rw [← Real.exp_add]; ring_nf
  have hc : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hD0 : 0 ≤ (D 0).re := by rw [S.zero_re]; positivity
  have key : 2 * n * (2 * P * Real.exp (2 * S.dmax * a)) ≤ Real.exp (θ * a) / ℓ := by
    have hE := Real.exp_pos (2 * S.dmax * a)
    have h1 : 4 * P * (2 * a + ℓ) ≤ Real.exp ((θ - 2 * S.dmax) * a) := by
      rw [show 1 / (4 * P) * Real.exp ((θ - 2 * S.dmax) * a) =
        Real.exp ((θ - 2 * S.dmax) * a) / (4 * P) by ring, le_div_iff₀ (by positivity)] at hlin
      linarith
    have h2 : 4 * P * n * ℓ ≤ Real.exp ((θ - 2 * S.dmax) * a) := by nlinarith
    rw [le_div_iff₀ hℓ, hexp]
    nlinarith
  have hlow : -(Real.exp (θ * a) / ℓ) ≤ (D 0).re -
      ∑ m ∈ (Finset.Ioo (-(n : ℤ)) n).erase 0, ‖D m‖ := by linarith
  exact (mul_le_mul_of_nonneg_right hlow hc).trans hG

/-- **Below twice the maximal depth.** For `θ < 2d_max` and `C > 0`, eventually in `a` the Toeplitz
floor of size `⌈2a/ℓ⌉` is not `−C e^{θa}/ℓ`. -/
theorem not_toeplitz_floor_eventually_of_lt (hℓ : 0 < ℓ) {θ C : ℝ} (hθ : θ < 2 * S.dmax)
    (hC : 0 < C) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀, ¬ ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ,
      -(C * Real.exp (θ * a) / ℓ) * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re := by
  obtain ⟨c, hc, K₀, hK₀⟩ := S.exists_mode_lower hℓ
  set c' := c * Real.exp (-(S.dmax * (P * ℓ))) with hc'
  have hc'0 : 0 < c' := by positivity
  obtain ⟨a₁, ha₁⟩ := exists_linear_le_exp (by linarith [S.dmax_pos] : 0 < 2 * S.dmax)
    (by positivity : 0 < c' / 2) (2 * P + 1)
  obtain ⟨a₂, ha₂⟩ := exists_exp_neg_le (sub_pos.mpr hθ) (by positivity : 0 < c' * ℓ / (2 * C))
  refine ⟨max (max a₁ a₂) ((K₀ + P + 2) * ℓ), fun a ha hT => ?_⟩
  have ha1 : a₁ ≤ a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ha
  have ha2 : a₂ ≤ a := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ha
  have ha3 : (K₀ + P + 2) * ℓ ≤ a := le_trans (le_max_right _ _) ha
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha3
  set n := ⌈2 * a / ℓ⌉₊ with hn
  have hnlo : 2 * a ≤ n * ℓ := by
    have := Nat.le_ceil (2 * a / ℓ)
    rwa [div_le_iff₀ hℓ] at this
  have hnK : K₀ + P + 1 ≤ n := by
    have : ((K₀ + P + 1 : ℕ) : ℝ) < n := by
      have h1 : ((K₀ + P + 1 : ℕ) : ℝ) * ℓ < n * ℓ := by push_cast; nlinarith
      exact lt_of_mul_lt_mul_right h1 hℓ.le
    exact_mod_cast this.le
  obtain ⟨m, hm1, hm2, hmode⟩ := hK₀ (n - P) (by omega)
  have hP : 0 < P := S.hP
  have hfl := floor_le_diagonal_sub_mode S.herm hT (m := m) (by omega) (by omega)
  rw [S.zero_re] at hfl
  -- `e^{d_max mℓ} ≥ e^{−d_max Pℓ} e^{2 d_max a}`
  have hm_lo : 2 * a - P * ℓ ≤ m * ℓ := by
    have : ((n - P : ℕ) : ℝ) ≤ m := by exact_mod_cast hm1
    rw [Nat.cast_sub (by omega)] at this
    nlinarith
  have hE : c' * Real.exp (2 * S.dmax * a) ≤ c * Real.exp (S.dmax * (m * ℓ)) := by
    rw [hc', mul_assoc, ← Real.exp_add]
    gcongr
    nlinarith [S.dmax_pos]
  have hlin := ha₁ a ha1
  have hexp := ha₂ a ha2
  have hθa : C * Real.exp (θ * a) / ℓ ≤ c' / 2 * Real.exp (2 * S.dmax * a) := by
    have : Real.exp (θ * a) = Real.exp (-((2 * S.dmax - θ) * a)) * Real.exp (2 * S.dmax * a) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, div_le_iff₀ hℓ]
    rw [le_div_iff₀ (by positivity)] at hexp
    have := Real.exp_pos (2 * S.dmax * a)
    nlinarith
  linarith

end CoshSymbolData

/-! ### Periodic off-line patterns -/

/-- The cosh data of a periodic off-line pattern. -/
def patternCoshData {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P) (θ d : Fin P → ℝ)
    (hd0 : ∀ r, 0 < d r)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j') :
    CoshSymbolData ℓ (patternSymbol ℓ (scaledOffset ℓ θ) d) P where
  d := d
  z := phasePoint θ
  hd0 := fun r => (hd0 r).le
  hpos := ⟨⟨0, hP⟩, hd0 _⟩
  hz := fun r => by rw [phasePoint, show 2 * π * I * (θ r : ℂ) = ((2 * π * θ r : ℝ) : ℂ) * I by
    push_cast; ring]; exact Complex.norm_exp_ofReal_mul_I _
  hinj := phasePoint_injective hθ
  herm := patternSymbol_neg ℓ _ d
  modes := fun m => patternSymbol_scaledOffset hℓ θ d m

/-- **Relaxed exponent of a pattern, from above.** For `θ' > 2 max_r d_r` a periodic off-line
pattern satisfies `Re W(f, f) ≥ −e^{θ'a} ∫|f|²` on all tests of aperture `a`, for all large `a`. -/
theorem patternConfig_relaxedHodge_eventually_of_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P)
    (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j') {θ' : ℝ}
    (hθ' : 2 * (patternCoshData hℓ hP θ d hd0 hθ).dmax < θ') :
    ∃ a₀ : ℝ, ∀ a ≥ a₀,
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        -(Real.exp (θ' * a) * ∫ u, ‖f u‖ ^ 2) ≤
          ((patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1).W f f).re) ∧
      RelaxedHodgeIndexAtLevel (patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1) θ' a := by
  obtain ⟨a₀, ha₀⟩ := (patternCoshData hℓ hP θ d hd0 hθ).toeplitz_floor_eventually_of_gt hℓ hθ'
  refine ⟨a₀, fun a ha => ?_⟩
  have hall : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      -(Real.exp (θ' * a) * ∫ u, ‖f u‖ ^ 2) ≤
        ((patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1).W f f).re := by
    intro f hf hfs
    have h := weil_floor_of_toeplitz_floor _ hℓ _ (fun _ hf hfs =>
      W_patternConfig hℓ _ d hd0 hd1 (scaledOffset_injective hℓ hθ) hf
        (hasCompactSupport_of_tsupport_subset_Icc hfs)) _ (ha₀ a ha) hf hfs
    rw [show ℓ * -(Real.exp (θ' * a) / ℓ) = -Real.exp (θ' * a) by field_simp] at h
    linarith
  exact ⟨hall, fun f hf hfs _ _ => hall f hf hfs⟩

/-- **Relaxed exponent of a pattern, from below.** For `θ' < 2 max_r d_r` and `C > 0`, at every
large aperture some polar-constrained test has `Re W(f, f) < −C e^{θ'a} ∫|f|²`. -/
theorem patternConfig_not_relaxedHodge_eventually_of_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ}
    (hP : 0 < P) (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j') {θ' C : ℝ}
    (hθ' : θ' < 2 * (patternCoshData hℓ hP θ d hd0 hθ).dmax) (hC : 0 < C) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀, ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
        ((patternConfig hℓ (scaledOffset ℓ θ) d hd0 hd1).W f f).re <
          -(C * Real.exp (θ' * a) * ∫ u, ‖f u‖ ^ 2) := by
  obtain ⟨a₀, ha₀⟩ :=
    (patternCoshData hℓ hP θ d hd0 hθ).not_toeplitz_floor_eventually_of_lt hℓ hθ' hC
  refine ⟨max a₀ 1, fun a ha => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ha)
  by_contra hcon
  push Not at hcon
  apply ha₀ a (le_trans (le_max_left _ _) ha)
  refine toeplitz_floor_of_hodge_floor _ hℓ _ (fun _ hf hfs =>
    W_patternConfig hℓ _ d hd0 hd1 (scaledOffset_injective hℓ hθ) hf
      (hasCompactSupport_of_tsupport_subset_Icc hfs)) ha0 _ fun f hf hfs hp hm => ?_
  have := hcon f hf hfs hp hm
  rw [show ℓ * -(C * Real.exp (θ' * a) / ℓ) = -(C * Real.exp (θ' * a)) by field_simp]
  linarith

/-! ### Periodic depth profiles -/

/-- The cosh data of a periodic depth profile with an off-line residue. -/
def profileCoshData {L : ℝ} {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r)
    (hpos : ∃ r, 0 < d r) : CoshSymbolData (L / P) (depthSymbol L d) P where
  d := d
  z := fun r => cexp (2 * π * I * (r : ℕ) / P)
  hd0 := hd0
  hpos := hpos
  hz := fun r => by
    rw [show 2 * π * I * ((r : ℕ) : ℂ) / P = ((2 * π * (r : ℕ) / P : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  hinj := by
    intro r r' h
    have hζ := Complex.isPrimitiveRoot_exp P hP.ne'
    have h1 : cexp (2 * π * I / P) ^ (r : ℕ) = cexp (2 * π * I / P) ^ (r' : ℕ) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      convert h using 2 <;> ring
    exact Fin.ext (hζ.pow_inj r.isLt r'.isLt h1)
  herm := depthSymbol_neg L d
  modes := fun m => depthSymbol_nat_eq L d m

/-- **Relaxed exponent of a profile, from above.** -/
theorem profileConfig_relaxedHodge_eventually_of_lt {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) (hpos : ∃ r, 0 < d r)
    {θ : ℝ} (hθ : 2 * (profileCoshData (L := L) hP d hd0 hpos).dmax < θ) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀,
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        -(Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2) ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) ∧
      RelaxedHodgeIndexAtLevel (profileConfig hL hP d hd0 hd1) θ a := by
  have hℓ : 0 < L / P := div_pos hL (by exact_mod_cast hP)
  obtain ⟨a₀, ha₀⟩ := (profileCoshData (L := L) hP d hd0 hpos).toeplitz_floor_eventually_of_gt hℓ hθ
  refine ⟨a₀, fun a ha => ?_⟩
  have hall : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      -(Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2) ≤ ((profileConfig hL hP d hd0 hd1).W f f).re := by
    intro f hf hfs
    have h := weil_floor_of_toeplitz_floor _ hℓ _ (fun _ hf hfs =>
      W_profileConfig_lag hL hP d hd0 hd1 hf (hasCompactSupport_of_tsupport_subset_Icc hfs)) _
      (ha₀ a ha) hf hfs
    rw [show L / P * -(Real.exp (θ * a) / (L / P)) = -Real.exp (θ * a) by field_simp] at h
    linarith
  exact ⟨hall, fun f hf hfs _ _ => hall f hf hfs⟩

/-- **Relaxed exponent of a profile, from below.** -/
theorem profileConfig_not_relaxedHodge_eventually_of_lt {L : ℝ} (hL : 0 < L) {P : ℕ}
    (hP : 0 < P) (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hpos : ∃ r, 0 < d r) {θ C : ℝ}
    (hθ : θ < 2 * (profileCoshData (L := L) hP d hd0 hpos).dmax) (hC : 0 < C) :
    ∃ a₀ : ℝ, ∀ a ≥ a₀, ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
        ((profileConfig hL hP d hd0 hd1).W f f).re < -(C * Real.exp (θ * a) * ∫ u, ‖f u‖ ^ 2) := by
  have hℓ : 0 < L / P := div_pos hL (by exact_mod_cast hP)
  obtain ⟨a₀, ha₀⟩ :=
    (profileCoshData (L := L) hP d hd0 hpos).not_toeplitz_floor_eventually_of_lt hℓ hθ hC
  refine ⟨max a₀ 1, fun a ha => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ha)
  by_contra hcon
  push Not at hcon
  apply ha₀ a (le_trans (le_max_left _ _) ha)
  refine toeplitz_floor_of_hodge_floor _ hℓ _ (fun _ hf hfs =>
    W_profileConfig_lag hL hP d hd0 hd1 hf (hasCompactSupport_of_tsupport_subset_Icc hfs)) ha0 _
    fun f hf hfs hp hm => ?_
  have := hcon f hf hfs hp hm
  rw [show L / P * -(C * Real.exp (θ * a) / (L / P)) = -(C * Real.exp (θ * a)) by field_simp]
  linarith

end GaloisForLFunctions.SquareRootThreshold
