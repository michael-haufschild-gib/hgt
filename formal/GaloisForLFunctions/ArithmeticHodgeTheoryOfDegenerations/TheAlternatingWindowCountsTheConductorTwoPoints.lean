import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsPositive

/-!
# The alternating window counts the conductor-two points

The alternating sign `(−1)^n` is the Ramanujan sum `c₂(n)`. A horizon window twisted by it,
`x_n = (−1)^n h(log(n/N))/√n`, sees no zero (`tendsto_twistedLedger`) and is positive
(`twisted_horizon_form_ge`). This file computes its second-order term exactly.

* **Alternating lattice sums** (`tsum_altSign_shellAutocorr`): Poisson summation on `ℤ/a` and on
  `2ℤ/a` give `Σ_j (−1)^j G(j/a) = 2a (a_φ(a/2) − a_φ(a))`: the alternating sign keeps exactly the
  odd half-harmonics of the atom grid and removes its zero mode.
* **Energy of the alternating block** (`abs_altEnergy_sub_le`): Plancherel and the linearized rows
  give `E_N = 2π (𝒜_N(c/2) − 𝒜_N(c)) + O(c/N)`, with no Riemann-sum main term.
* **Quiet below the first resonance** (`norm_dirichletPoly_alt_le`): the phase increments of
  `(−1)^n n^{iτ}` stay in `[1/4, 1/2]` for `|τ| ≤ (π/2) N e^{−A}`, so Kuzmin–Landau and summation by
  parts give `|D_x(τ)| ≤ 7 (L e^{3A/2} + B e^{A/2})/√N` there.
* **The second-order term** (`alternating_layer_sharp`): along `c → ∞`, `c (log N)²/N → 0`,
  `c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²)(𝒜_N(c/2) − 𝒜_N(c)) → 0`. No Weil term appears.
* **At the critical curve** (`alternating_layer_criticalCurve_of_regularBulk`,
  `alternating_layer_criticalCurve_exact`): for a bulk limit `s^β E₁(s) → J`,
  `c⁻¹⟨W x, x⟩/∫g² → (2^{β+1} − 1) β J/K ∫ e^{−(β+1)y} H²`; for the tilted spline this is
  `7 J(2)/K ∫ e^{−8y} H²` with `J(2) = J(1) #ℙ⁷(𝔽₂) = 255 J(1)` (`jordanCoefficient_two`).

The second-order term of the conductor-two window is the first-order count of conductor two: the
count of the degeneration reappears at second order on the twisted directions.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- The alternating sign `(−1)^n = c₂(n)`, the Ramanujan sum of conductor `2`. -/
def altSign (n : ℕ) : ℝ := (-1) ^ n

theorem meanZeroTwist_altSign : MeanZeroTwist altSign 2 where
  pos := by norm_num
  periodic n := by simp [altSign, pow_add]
  mean_zero := by simp [altSign, Finset.sum_range_succ]

theorem altSign_sq (n : ℕ) : altSign n ^ 2 = 1 := by
  rw [altSign, ← pow_mul, mul_comm, pow_mul]; norm_num

theorem abs_altSign (n : ℕ) : |altSign n| = 1 := by
  rw [altSign, abs_pow, abs_neg, abs_one, one_pow]

/-- The parity of `|m − n|` is the parity of `m + n`. -/
theorem neg_one_pow_natAbs_sub (m n : ℕ) :
    (-1 : ℝ) ^ ((m : ℤ) - n).natAbs = altSign m * altSign n := by
  rw [altSign, altSign, ← pow_add]
  rcases le_total n m with hnm | hmn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have e : ((n + d : ℕ) : ℤ) - n = d := by push_cast; ring
    rw [e, Int.natAbs_natCast, show n + d + n = d + 2 * n by ring, pow_add, pow_mul]
    norm_num
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have e : (m : ℤ) - ((m + d : ℕ) : ℤ) = -d := by push_cast; ring
    rw [e, Int.natAbs_neg, Int.natAbs_natCast, show m + (m + d) = d + 2 * m by ring, pow_add,
      pow_mul]
    norm_num

/-- The aliasing functional of the alternating window: `𝒜_N(c/2) − 𝒜_N(c)`. -/
def altAlias (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  horizonAlias φ h (c / 2) N - horizonAlias φ h c N

/-! ### Alternating lattice sums -/

/-- **Alternating Poisson summation**: `Σ_j (−1)^j G(j/a) = 2a (a_φ(a/2) − a_φ(a))`. -/
theorem tsum_altSign_shellAutocorr (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {a : ℝ} (ha : 0 < a) :
    ∑' j : ℤ, (-1 : ℝ) ^ j.natAbs * shellAutocorr φ (j * a⁻¹) =
      2 * a * (aliasDensity φ (a / 2) - aliasDensity φ a) := by
  set f : ℤ → ℝ := fun j => shellAutocorr φ (j * a⁻¹) with hf
  have hfin : (Function.support f).Finite := by
    refine (Set.finite_Icc (-⌈a⌉) ⌈a⌉).subset fun j hj => ?_
    by_contra hout
    apply hj
    refine shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ?_
    rw [abs_mul, abs_inv, abs_of_pos ha, le_mul_inv_iff₀ ha, one_mul]
    have hca : 0 < ⌈a⌉ := Int.ceil_pos.mpr ha
    have hj' : ⌈a⌉ < |j| := by
      rcases not_and_or.mp hout with h1 | h1
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_pos (by omega)]; omega
    have : (⌈a⌉ : ℝ) < |(j : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hj'
    linarith [Int.le_ceil a]
  have hs : Summable f := summable_of_hasFiniteSupport hfin
  have hs' : Summable fun j : ℤ => (-1 : ℝ) ^ j.natAbs * f j :=
    summable_of_hasFiniteSupport (hfin.subset fun j hj => by
      simp only [Function.mem_support] at hj ⊢
      exact right_ne_zero_of_mul hj)
  -- the even part
  set g : ℤ → ℝ := fun j => if Even j then f j else 0 with hg
  have heven : ∑' i : ℤ, f (2 * i) = ∑' j : ℤ, g j := by
    have hinj : Function.Injective (fun i : ℤ => 2 * i) := fun i k hik => by
      simp only at hik; omega
    rw [← hinj.tsum_eq (f := g)]
    · refine tsum_congr fun i => ?_
      simp only [hg, even_two_mul, if_true]
    · intro j hj
      simp only [Function.mem_support, hg, ne_eq, ite_eq_right_iff, not_forall] at hj
      obtain ⟨⟨k, hk⟩, -⟩ := hj
      exact ⟨k, by simp only; omega⟩
  have hsplit : ∀ j : ℤ, (-1 : ℝ) ^ j.natAbs * f j = 2 * g j - f j := by
    intro j
    simp only [hg]
    split_ifs with hj
    · rw [(Int.natAbs_even.mpr hj).neg_one_pow]; ring
    · rw [(Int.natAbs_odd.mpr (Int.not_even_iff_odd.mp hj)).neg_one_pow]; ring
  have hgs : Summable g := summable_of_hasFiniteSupport (hfin.subset fun j hj => by
    simp only [Function.mem_support, hg, ne_eq, ite_eq_right_iff, not_forall] at hj
    exact hj.2)
  rw [tsum_congr hsplit, (hgs.mul_left 2).tsum_sub hs, tsum_mul_left, ← heven]
  have h1 := tsum_shellAutocorr_eq hφ hφsupp ha
  have h2 := tsum_shellAutocorr_eq hφ hφsupp (half_pos ha)
  have e : ∀ i : ℤ, f (2 * i) = shellAutocorr φ (i * (a / 2)⁻¹) := fun i => by
    simp only [hf]
    congr 1
    push_cast
    field_simp
  rw [tsum_congr e, h2, show (∑' j : ℤ, f j) = ∑' m : ℤ, shellAutocorr φ (m * a⁻¹) from rfl, h1]
  ring

/-! ### Plancherel for arbitrary weights -/

theorem hasCompactSupport_centredAtomicTest {φ : ℝ → ℝ}
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ}
    (hN : 1 ≤ N) : HasCompactSupport (centredAtomicTest φ x c N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := fun u hu => by
    unfold atomDilate
    refine hφsupp _ fun hm => hu ?_
    obtain ⟨h0, h1⟩ := hm
    exact ⟨by rw [le_div_iff₀ hw, zero_mul] at h0; exact h0,
      by rw [div_le_one hw] at h1; exact h1⟩
  exact (hasCompactSupport_atomicTest hg N _).comp_homeomorph (Homeomorph.addRight _)

/-- **Plancherel for an atomic block**: `∫ |φ̂(wτ)|² |D_x(τ)|²/N = (2π/c) Σ x_m x_n G(N log(m/n)/c)`. -/
theorem atomEnergy_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    ∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N x τ‖ ^ 2 / N) =
      2 * Real.pi / c * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        x m * x n * shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  set T := centredAtomicTest φ x c N with hT
  have hT2 : ContDiff ℝ 2 (cx T) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_centredAtomicTest hφ x c N)
  have hTc : HasCompactSupport (cx T) :=
    (hasCompactSupport_centredAtomicTest hφsupp x hc hN).comp_left Complex.ofReal_zero
  have hpl := RHTower.LebesgueAtomWeil.integral_norm_sq_paperFT_eq hT2 hTc
  have hint : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N x τ‖ ^ 2 / N) = ((c / N) ^ 2 * N)⁻¹ * ‖paperFT (cx T) τ‖ ^ 2 := by
    intro τ
    rw [hT, norm_sq_paperFT_centredAtomicTest hφ.continuous hφc x hc hN τ]
    field_simp
  have hsq : ∫ r : ℝ, ‖paperFT (cx T) r‖ ^ 2 = 2 * Real.pi * ∫ u, T u ^ 2 := by
    have e : ∫ u : ℝ, ‖cx T u‖ ^ 2 = ∫ u, T u ^ 2 := by
      congr 1; funext u; simp [cx, Complex.norm_real, sq_abs]
    rw [← e, ← hpl]
    field_simp
  set g := atomDilate φ (c / N) with hg
  have hgcont : Continuous g := hφ.continuous.comp (continuous_id.div_const _)
  have hgc : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := c / N)) fun u hu => ?_
    simp only [hg, atomDilate]
    refine hφsupp _ fun hm => hu ?_
    obtain ⟨h0, h1⟩ := hm
    exact ⟨by rw [le_div_iff₀ hw, zero_mul] at h0; exact h0,
      by rw [div_le_one hw] at h1; exact h1⟩
  have htr : ∫ u, T u ^ 2 = ∫ u, atomicTest N x g u * atomicTest N x g (u + 0) := by
    have := integral_add_right_eq_self (μ := volume) (fun u => atomicTest N x g u ^ 2) (Real.log N)
    simp only [hT, centredAtomicTest, add_zero, ← hg]
    rw [this]
    congr 1; funext u; ring
  simp_rw [hint]
  rw [integral_const_mul, hsq, htr, integral_atomicTest_mul_shift hgcont hgc N _ 0, ← mul_assoc,
    mul_sum, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [hg, bumpCorr_atomDilate_eq' hw]
  have e : (0 - (Real.log n - Real.log m)) / (c / N) = N * (Real.log m - Real.log n) / c := by
    field_simp; ring
  rw [e]
  field_simp

/-! ### The energy of the alternating block -/

/-- **One alternating row**: `Σ_m (−1)^m k_m G(N log(m/n)/c) = (−1)^n k_n Σ_j (−1)^j G(j/a_n)` up to
`O(c² N^{−3/2})`, `a_n = cn/N`. -/
theorem abs_altRow_sub_le {k G : ℝ → ℝ} {Bk Lk BG LG : ℝ} (hk : ∀ y, |k y| ≤ Bk)
    (hkL : ∀ u v, |k u - k v| ≤ Lk * |u - v|) (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hG1 : ∀ t, 1 ≤ |t| → G t = 0)
    (hk0 : ∀ y, 0 < y → k y = 0) (hLk : 0 ≤ Lk) (hBk : 0 ≤ Bk) (hLG : 0 ≤ LG) (hBG : 0 ≤ BG)
    {c : ℝ} (hc : 1 ≤ c) {N : ℕ} (hcN : 4 * c ≤ N) {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    |∑ m ∈ Icc 1 N, altSign m * (k (Real.log m - Real.log N) / Real.sqrt N) *
        G (N * (Real.log m - Real.log n) / c) -
      altSign n * (k (Real.log n - Real.log N) / Real.sqrt N) *
        ∑' j : ℤ, (-1 : ℝ) ^ j.natAbs * G (j * (c * n / N)⁻¹)| ≤
      5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N) := by
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  set a := c * n / N with ha
  have ha0 : 0 < a := by positivity
  have hac : a ≤ c := by
    rw [ha, div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN' hc0.le
  -- the alternating lattice sum is a finite sum over `1 ≤ m ≤ 2N`
  have hlat : ∑' j : ℤ, (-1 : ℝ) ^ j.natAbs * G (j * a⁻¹) =
      ∑ m ∈ Icc 1 (2 * N), altSign m * altSign n * G (((m : ℝ) - n) * a⁻¹) := by
    rw [tsum_eq_sum (s := (Icc 1 (2 * N)).image (fun m : ℕ => (m : ℤ) - n))]
    · rw [Finset.sum_image]
      · refine sum_congr rfl fun m _ => ?_
        rw [neg_one_pow_natAbs_sub]
        push_cast; rfl
      · intro x _ y _ hxy
        simp only at hxy
        omega
    · intro j hj
      rw [hG1 _ ?_, mul_zero]
      rw [abs_mul, abs_inv, abs_of_pos ha0, le_mul_inv_iff₀ ha0, one_mul]
      have hj' : ¬ (1 ≤ j + n ∧ j + n ≤ 2 * N) := by
        rintro ⟨h1, h2⟩
        apply hj
        rw [Finset.mem_image]
        exact ⟨(j + n).toNat, by rw [Finset.mem_Icc]; omega, by omega⟩
      have han : 4 * a ≤ n := by
        rw [ha, show 4 * (c * n / N) = 4 * c / N * n by ring]
        exact mul_le_of_le_one_left hn0.le ((div_le_one hN0).mpr hcN)
      rcases not_and_or.mp hj' with h | h
      · have : (j : ℝ) ≤ -n := by exact_mod_cast (by omega : j ≤ -(n : ℤ))
        rw [abs_of_neg (by linarith)]; linarith
      · have : (2 * N + 1 : ℝ) - n ≤ j := by
          exact_mod_cast (by omega : (2 * N + 1 : ℤ) - n ≤ j)
        rw [abs_of_pos (by linarith)]; linarith
  -- the row extends by zero to `1 ≤ m ≤ 2N`
  have hrow : ∑ m ∈ Icc 1 N, altSign m * (k (Real.log m - Real.log N) / Real.sqrt N) *
      G (N * (Real.log m - Real.log n) / c) = ∑ m ∈ Icc 1 (2 * N),
        altSign m * (k (Real.log m - Real.log N) / Real.sqrt N) *
          G (N * (Real.log m - Real.log n) / c) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) fun m hm hmN => ?_
    have hm1 : N < m := by
      rw [Finset.mem_Icc] at hm hmN; omega
    have hlog : 0 < Real.log m - Real.log N := by
      rw [sub_pos]; exact Real.log_lt_log hN0 (by exact_mod_cast hm1)
    rw [hk0 _ hlog, zero_div, mul_zero, zero_mul]
  rw [hlat, hrow, mul_sum, ← sum_sub_distrib]
  set X := (Lk * BG + 8 * Bk * LG) * c / (N * Real.sqrt N) with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ m ∈ Icc 1 (2 * N), |altSign m * (k (Real.log m - Real.log N) / Real.sqrt N) *
      G (N * (Real.log m - Real.log n) / c) - altSign n * (k (Real.log n - Real.log N) /
        Real.sqrt N) * (altSign m * altSign n * G (((m : ℝ) - n) * a⁻¹))| ≤
      if |(m : ℝ) - n| ≤ 2 * a then X else 0 := fun m hm => by
    have e : altSign m * (k (Real.log m - Real.log N) / Real.sqrt N) *
        G (N * (Real.log m - Real.log n) / c) - altSign n * (k (Real.log n - Real.log N) /
          Real.sqrt N) * (altSign m * altSign n * G (((m : ℝ) - n) * a⁻¹)) =
        altSign m * (k (Real.log m - Real.log N) / Real.sqrt N *
          G (N * (Real.log m - Real.log n) / c) -
            k (Real.log n - Real.log N) / Real.sqrt N * G (((m : ℝ) - n) * (c * n / N)⁻¹)) := by
      have := altSign_sq n
      rw [ha]
      linear_combination (-(altSign m * (k (Real.log n - Real.log N) / Real.sqrt N) *
        G (((m : ℝ) - n) * (c * n / N)⁻¹))) * this
    rw [e, abs_mul, abs_altSign, one_mul]
    exact abs_entry_le hk hkL hG hGL hG1 hLk hBk hLG hBG hc0 hcN hn (Finset.mem_Icc.mp hm).1
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard := card_filter_near_le n N ha0.le
  calc (((Icc 1 (2 * N)).filter fun m : ℕ => |(m : ℝ) - n| ≤ 2 * a).card : ℝ) * X
      ≤ (4 * a + 1) * X := mul_le_mul_of_nonneg_right hcard hX0
    _ ≤ 5 * c * X := mul_le_mul_of_nonneg_right (by linarith) hX0
    _ = 5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N) := by rw [hX]; ring

/-- **The energy of the alternating block**: `E_N = 2π (𝒜_N(c/2) − 𝒜_N(c)) + O(c/N)` for
`1 ≤ c ≤ N/4`. -/
theorem abs_altEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h altSign N) τ‖ ^ 2 / N)) -
        2 * Real.pi * altAlias φ h c N| ≤ K * c / N := by
  obtain ⟨Bk, Lk, hk, hkL⟩ := exists_bound_lipschitz (contDiff_taperedProfile hh)
    (A := A) fun y hy => taperedProfile_eq_zero hsupp hy
  have hG2 := contDiff_shellAutocorr hφ hφsupp
  have hG1 : ∀ t, 1 ≤ |t| → shellAutocorr φ t = 0 := fun t ht =>
    shellAutocorr_eq_zero_of_one_le_abs hφ hφsupp ht
  have hGc : HasCompactSupport (shellAutocorr φ) :=
    HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun t ht => by
      refine hG1 t ?_
      by_contra hlt
      exact ht (abs_le.mp (not_le.mp hlt).le)
  obtain ⟨BG, hBG⟩ := hGc.exists_bound_of_continuous hG2.continuous
  obtain ⟨LG, hLG⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGc hG2 (by norm_num)
  have hGb : ∀ t, |shellAutocorr φ t| ≤ |BG| := fun t =>
    (by simpa [Real.norm_eq_abs] using hBG t : |shellAutocorr φ t| ≤ BG).trans (le_abs_self _)
  have hGL : ∀ s t, |shellAutocorr φ s - shellAutocorr φ t| ≤ (LG : ℝ) * |s - t| := fun s t => by
    simpa [Real.dist_eq] using hLG.dist_le_mul s t
  have hkb : ∀ y, |taperedProfile h y| ≤ |Bk| := fun y => (hk y).trans (le_abs_self _)
  have hkL' : ∀ u v, |taperedProfile h u - taperedProfile h v| ≤ |Lk| * |u - v| := fun u v =>
    (hkL u v).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
  have hk0 : ∀ y, 0 < y → taperedProfile h y = 0 := fun y hy =>
    taperedProfile_eq_zero hsupp fun hm => by linarith [hm.2]
  set X := 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ)) with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨2 * Real.pi * |Bk| * X, by positivity, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  rw [atomEnergy_eq hφ hφsupp _ hc0 hN, Finset.sum_comm]
  have hxw : ∀ m, 1 ≤ m → twistedWeights h altSign N m =
      altSign m * (taperedProfile h (Real.log m - Real.log N) / Real.sqrt N) := fun m hm => by
    rw [twistedWeights, horizonWeights_eq_tapered h hN hm, mul_comm]
  -- each row against its Poisson value
  have hrow : ∀ n ∈ Icc 1 N, |∑ m ∈ Icc 1 N, twistedWeights h altSign N m *
      twistedWeights h altSign N n * shellAutocorr φ (N * (Real.log m - Real.log n) / c) -
        twistedWeights h altSign N n * (altSign n * horizonWeights h N n *
          (2 * (c * n / N) * (aliasDensity φ (c * n / N / 2) - aliasDensity φ (c * n / N))))| ≤
        |Bk| / Real.sqrt N * (X * c ^ 2 / (N * Real.sqrt N)) := by
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnN := (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpoi := tsum_altSign_shellAutocorr hφ hφsupp (a := c * n / N) (by positivity)
    have hr := abs_altRow_sub_le hkb hkL' hGb hGL hG1 hk0 (abs_nonneg _) (abs_nonneg _)
      (NNReal.coe_nonneg _) (abs_nonneg _) hc hcN hn1 hnN
    rw [hpoi] at hr
    have hxn : horizonWeights h N n = taperedProfile h (Real.log n - Real.log N) / Real.sqrt N :=
      horizonWeights_eq_tapered h hN hn1
    have hsum : ∑ m ∈ Icc 1 N, twistedWeights h altSign N m * twistedWeights h altSign N n *
        shellAutocorr φ (N * (Real.log m - Real.log n) / c) = twistedWeights h altSign N n *
          ∑ m ∈ Icc 1 N, altSign m * (taperedProfile h (Real.log m - Real.log N) / Real.sqrt N) *
            shellAutocorr φ (N * (Real.log m - Real.log n) / c) := by
      rw [mul_sum]
      refine sum_congr rfl fun m hm => ?_
      rw [hxw m (Finset.mem_Icc.mp hm).1]
      ring
    rw [hsum, ← mul_sub, abs_mul]
    have hxb : |twistedWeights h altSign N n| ≤ |Bk| / Real.sqrt N := by
      rw [hxw n hn1, abs_mul, abs_altSign, one_mul, abs_div, abs_of_pos hsN]
      exact div_le_div_of_nonneg_right (hkb _) hsN.le
    rw [← hxn] at hr
    have hX' : 5 * (|Lk| * |BG| + 8 * |Bk| * (LG : ℝ)) * c ^ 2 / (N * Real.sqrt N) =
        X * c ^ 2 / (N * Real.sqrt N) := by rw [hX]
    rw [hX'] at hr
    have e : altSign n * horizonWeights h N n * (2 * (c * n / N) *
        (aliasDensity φ (c * n / N / 2) - aliasDensity φ (c * n / N))) =
        altSign n * horizonWeights h N n * (2 * (c * n / N) *
          (aliasDensity φ ((c * n / N) / 2) - aliasDensity φ (c * n / N))) := rfl
    rw [e]
    exact mul_le_mul hxb hr (abs_nonneg _) (by positivity)
  -- the Poisson values add up to the alternating aliasing functional
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, twistedWeights h altSign N n *
      (altSign n * horizonWeights h N n *
        (2 * (c * n / N) * (aliasDensity φ (c * n / N / 2) - aliasDensity φ (c * n / N)))) =
      2 * Real.pi * altAlias φ h c N := by
    unfold altAlias horizonAlias
    rw [mul_sum, ← mul_sub, ← sum_sub_distrib, mul_sum, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hx2 : twistedWeights h altSign N n * (altSign n * horizonWeights h N n) =
        h (Real.log n - Real.log N) ^ 2 / n := by
      rw [twistedWeights, show horizonWeights h N n * altSign n * (altSign n *
        horizonWeights h N n) = altSign n ^ 2 * (horizonWeights h N n * horizonWeights h N n) by
        ring, altSign_sq, one_mul, horizonWeights, div_mul_div_comm, Real.mul_self_sqrt hn0.le, sq]
    rw [show c / 2 * n / N = c * n / N / 2 by ring]
    rw [show 2 * Real.pi / c * (twistedWeights h altSign N n * (altSign n * horizonWeights h N n *
      (2 * (c * n / N) * (aliasDensity φ (c * n / N / 2) - aliasDensity φ (c * n / N))))) =
      2 * Real.pi / c * (twistedWeights h altSign N n * (altSign n * horizonWeights h N n)) *
      (2 * (c * n / N) * (aliasDensity φ (c * n / N / 2) - aliasDensity φ (c * n / N))) by ring,
      hx2]
    field_simp
  rw [← hmain, ← mul_sub, ← sum_sub_distrib, abs_mul,
    abs_of_pos (by positivity : 0 < 2 * Real.pi / c)]
  have hsumb := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hrow)
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsumb
  calc 2 * Real.pi / c * |∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 N, twistedWeights h altSign N m *
        twistedWeights h altSign N n * shellAutocorr φ (N * (Real.log m - Real.log n) / c) -
          twistedWeights h altSign N n * (altSign n * horizonWeights h N n *
            (2 * (c * n / N) * (aliasDensity φ (c * n / N / 2) - aliasDensity φ (c * n / N)))))|
      ≤ 2 * Real.pi / c * (N * (|Bk| / Real.sqrt N * (X * c ^ 2 / (N * Real.sqrt N)))) :=
        mul_le_mul_of_nonneg_left hsumb (by positivity)
    _ = 2 * Real.pi * |Bk| * X * c / N := by
        field_simp
        rw [Real.sq_sqrt hN0.le]
        ring

/-! ### The alternating block is quiet below the first resonance -/

/-- **Kuzmin–Landau for `(−1)^n n^{iτ}`.** For `0 ≤ τ ≤ (π/2) n₀`, every partial sum
`Σ_{m ≤ k} (−1)^{n₀+m} (n₀ + m)^{iτ}` has norm at most `7`: the phase increments stay in
`[1/4, 1/2]`. -/
theorem norm_partial_altSign_cpow_le {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (k : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτn : τ ≤ Real.pi / 2 * n₀) :
    ‖∑ m ∈ range (k + 1), (altSign (n₀ + m) : ℂ) *
        Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I)‖ ≤ 7 := by
  set φ : ℕ → ℝ := fun m => m / 2 - τ * Real.log (n₀ + m) / (2 * Real.pi) with hφ
  have hterm : ∀ m : ℕ, (altSign (n₀ + m) : ℂ) *
      Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I) = (altSign n₀ : ℂ) *
        (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    intro m
    have key : (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I) = (m : ℂ) * (Real.pi * Complex.I) +
        (-(((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I)) := by
      simp only [hφ]; push_cast; field_simp; ring
    rw [key, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I, map_mul, map_pow,
      map_neg, map_one, ← Complex.exp_conj]
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg, altSign]
    push_cast
    ring
  have hconj : ∑ m ∈ range (k + 1), (altSign (n₀ + m) : ℂ) *
      Complex.exp (((τ * Real.log (n₀ + m) : ℝ) : ℂ) * Complex.I) = (altSign n₀ : ℂ) *
        (starRingEnd ℂ) (∑ m ∈ range (k + 1),
          Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    rw [map_sum, mul_sum]
    exact sum_congr rfl fun m _ => hterm m
  rw [hconj, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_altSign, one_mul]
  have hdiff : ∀ m : ℕ, φ (m + 1) - φ m =
      1 / 2 - τ / (2 * Real.pi) * Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) := by
    intro m
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    simp only [hφ]
    push_cast
    rw [Real.log_div (by linarith) h1.ne', show ((n₀ : ℝ) + (m + 1)) = (n₀ + m) + 1 by ring]
    field_simp
    ring
  have hlog_le : ∀ m : ℕ, Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) ≤ 1 / (n₀ + m) := by
    intro m
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    have := Real.log_le_sub_one_of_pos (show 0 < ((n₀ + m : ℝ) + 1) / (n₀ + m) by positivity)
    rw [show ((n₀ + m : ℝ) + 1) / (n₀ + m) - 1 = 1 / (n₀ + m) by field_simp; ring] at this
    exact this
  have hlog0 : ∀ m : ℕ, 0 ≤ Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) := fun m => by
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    exact Real.log_nonneg (by rw [le_div_iff₀ h1]; linarith)
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hτpos : 0 ≤ τ / (2 * Real.pi) := by positivity
  refine (RHTower.Sieve.kuzminLandau_band φ k (δ := 1 / 4) (by norm_num) (fun m hm => ?_)
    (fun m hm => ?_) (fun m hm => ?_)).trans (by norm_num)
  · rw [hdiff]
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    have : τ / (2 * Real.pi) * Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) ≤ 1 / 4 := by
      calc τ / (2 * Real.pi) * Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m))
          ≤ τ / (2 * Real.pi) * (1 / (n₀ + m)) := mul_le_mul_of_nonneg_left (hlog_le m) hτpos
        _ ≤ τ / (2 * Real.pi) * (1 / n₀) := by
            gcongr
            exact_mod_cast Nat.le_add_right n₀ m
        _ ≤ 1 / 4 := by
            rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [Real.pi_pos]
    linarith
  · rw [hdiff]
    have := mul_nonneg hτpos (hlog0 m)
    linarith
  · rw [hdiff, hdiff]
    have h1 : (0 : ℝ) < n₀ + m := by positivity
    have h2 : Real.log (((n₀ + (m + 1 : ℕ) : ℝ) + 1) / (n₀ + (m + 1 : ℕ))) ≤
        Real.log (((n₀ + m : ℝ) + 1) / (n₀ + m)) := by
      push_cast
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) h1]
      nlinarith
    nlinarith

theorem norm_dirichletPoly_neg (N : ℕ) (x : ℕ → ℝ) (τ : ℝ) :
    ‖dirichletPoly N x ((-τ : ℝ) : ℂ)‖ = ‖dirichletPoly N x τ‖ := by
  have e : dirichletPoly N x ((-τ : ℝ) : ℂ) = (starRingEnd ℂ) (dirichletPoly N x τ) := by
    unfold dirichletPoly
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [e, RCLike.norm_conj]

/-- The alternating Dirichlet polynomial lives on the window. -/
theorem dirichletPoly_alt_eq_range (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    dirichletPoly N (twistedWeights h altSign N) τ =
      ∑ m ∈ range (N - windowStart A N + 1), (horizonWeights h N (windowStart A N + m) : ℂ) *
        ((altSign (windowStart A N + m) : ℂ) *
          Complex.exp (((τ * Real.log (windowStart A N + m) : ℝ) : ℂ) * Complex.I)) := by
  set n₀ := windowStart A N with hn₀
  have h1 := one_le_windowStart hN A
  have h2 : n₀ ≤ N := windowStart_le hA
  unfold dirichletPoly
  have hsplit : Icc 1 N = Ico 1 n₀ ∪ Ico n₀ (N + 1) := by
    ext n; simp only [mem_Icc, mem_union, mem_Ico]; omega
  rw [hsplit, sum_union (disjoint_left.mpr fun n ha hb => by
    simp only [mem_Ico] at ha hb; omega)]
  rw [sum_eq_zero (fun n hn => by
    simp only [mem_Ico] at hn
    rw [twistedWeights, horizonWeights_eq_zero_of_lt hsupp hn.1 hn.2, zero_mul,
      Complex.ofReal_zero, zero_mul]), zero_add,
    sum_Ico_eq_sum_range, show N + 1 - n₀ = N - n₀ + 1 by omega]
  refine sum_congr rfl fun m _ => ?_
  rw [twistedWeights]
  push_cast
  ring_nf

/-- **The alternating block is quiet below the first resonance**: for `|τ| ≤ N e^{−A}`,
`|D_x(τ)| ≤ 7 (L e^{3A/2} + B e^{A/2})/√N`. -/
theorem norm_dirichletPoly_alt_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {N : ℕ}
    (hN : 1 ≤ N) {τ : ℝ} (hτ : |τ| ≤ (N : ℝ) * Real.exp (-A)) :
    ‖dirichletPoly N (twistedWeights h altSign N) τ‖ ≤
      7 * ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
  have key : ∀ t : ℝ, 0 ≤ t → t ≤ (N : ℝ) * Real.exp (-A) →
      ‖dirichletPoly N (twistedWeights h altSign N) t‖ ≤
        7 * ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
    intro t ht0 htN
    set n₀ := windowStart A N with hn₀
    have h1 := one_le_windowStart hN A
    have htn : t ≤ Real.pi / 2 * n₀ := by
      have := le_windowStart A N
      have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
      nlinarith [Real.pi_gt_three]
    rw [dirichletPoly_alt_eq_range hsupp hA hN]
    refine (norm_sum_mul_le_of_partial (fun m => horizonWeights h N (n₀ + m))
      (fun m => (altSign (n₀ + m) : ℂ) * Complex.exp (((t * Real.log (n₀ + m) : ℝ) : ℂ) *
        Complex.I)) (N - n₀) (B := 7) fun k _ => ?_).trans ?_
    · have := norm_partial_altSign_cpow_le h1 k ht0 htn
      push_cast at this ⊢
      exact this
    · exact mul_le_mul_of_nonneg_left (variation_horizonWeights_le hsupp hA hB hL hN)
        (by norm_num)
  rcases le_total 0 τ with h0 | h0
  · exact key τ h0 (le_trans (le_abs_self τ) hτ)
  · have := key (-τ) (by linarith) (by rw [abs_of_nonpos h0] at hτ; exact hτ)
    rwa [norm_dirichletPoly_neg] at this

/-! ### The symbol above the cut, for arbitrary weights -/

section RemainderW

variable {Cφ p : ℝ} {ν : ℝ → ℝ}

/-- The aliasing integrand of a block with weights `x`. -/
def aliasIntegrandW (φ ν : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ) (w sgn τ : ℝ) : ℝ :=
  ‖paperFT (cx φ) ((w : ℂ) * ((sgn * τ : ℝ) : ℂ))‖ ^ 2 *
    (‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) * |ν (sgn * τ)|

/-- One dyadic block `[U, 2U]` of the aliasing tail of a block with weights `x`. -/
theorem integral_aliasIntegrandW_block_le (hCφ : 0 ≤ Cφ) (hp0 : 0 ≤ p)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) {x : ℕ → ℝ} {N : ℕ}
    (hN : 1 ≤ N) {S1 S2 : ℝ} (hS1 : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ S1)
    (hS2 : ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2 ≤ S2) {w : ℝ} (hw0 : 0 < w) {sgn : ℝ}
    (hsgn : sgn = 1 ∨ sgn = -1) {U : ℝ} (hU1 : 1 ≤ U) {W : ℝ}
    (hW : ∀ τ ∈ Set.Icc U (2 * U), |ν (sgn * τ)| ≤ W)
    (hint : IntervalIntegrable (aliasIntegrandW φ ν x N w sgn) volume U (2 * U)) :
    ∫ τ in U..(2 * U), aliasIntegrandW φ ν x N w sgn τ ≤
      Cφ * (w * U) ^ (-p) * W * ((U * S1 + 208 * S2) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU0 : 0 < U := by linarith
  have hUle : U ≤ 2 * U := by linarith
  have hsgn1 : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> simp
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW U ⟨le_rfl, hUle⟩)
  set Wt : ℝ := Cφ * (w * U) ^ (-p) * W with hWt
  have hWt0 : 0 ≤ Wt := by positivity
  have hpt : ∀ τ ∈ Set.Icc U (2 * U), aliasIntegrandW φ ν x N w sgn τ ≤
      Wt * (‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le hU0 hτ.1
    have habs : |sgn * τ| = τ := by rw [abs_mul, hsgn1, one_mul, abs_of_pos hτ0]
    have h1 := hdecay (w * (sgn * τ))
    rw [show ((w * (sgn * τ) : ℝ) : ℂ) = (w : ℂ) * ((sgn * τ : ℝ) : ℂ) by push_cast; ring] at h1
    have hwτ : |w * (sgn * τ)| = w * τ := by rw [abs_mul, abs_of_pos hw0, habs]
    rw [hwτ] at h1
    have h2 : (1 + w * τ) ^ (-p) ≤ (w * U) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [hτ.1]) (by linarith)
    have hD0 : 0 ≤ ‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N := by positivity
    unfold aliasIntegrandW
    calc ‖paperFT (cx φ) ((w : ℂ) * ((sgn * τ : ℝ) : ℂ))‖ ^ 2 *
          (‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) * |ν (sgn * τ)|
        ≤ (Cφ * (w * U) ^ (-p)) * (‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) * W :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (h1.trans (mul_le_mul_of_nonneg_left h2 hCφ)) hD0) (hW τ hτ) (abs_nonneg _)
            (by positivity)
      _ = Wt * (‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N) := by rw [hWt]; ring
  have hcontD : Continuous fun τ : ℝ => ‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 / N :=
    ((continuous_norm_sq_dirichletPoly N x).comp (continuous_const.mul continuous_id)).div_const _
  have hmono := intervalIntegral.integral_mono_on hUle hint
    ((continuous_const.mul hcontD).intervalIntegrable U (2 * U)) hpt
  simp only [Pi.mul_apply] at hmono
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  have hMV : ∫ τ in U..(2 * U), ‖dirichletPoly N x ((sgn * τ : ℝ) : ℂ)‖ ^ 2 ≤ U * S1 + 208 * S2 := by
    rcases hsgn with rfl | rfl
    · simp only [one_mul]
      refine (integral_window_le N x U).trans ?_
      gcongr
    · simp only [neg_one_mul]
      refine (integral_window_neg_le N x U).trans ?_
      gcongr
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hMV hN0.le) hWt0

/-- The aliasing tail of a block with weights `x` and block weights `V + j`. -/
theorem integral_aliasingW_le_of_blocks (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) {V : ℝ} (hV : 1 ≤ V)
    (hA : 0 ≤ A) {Bh : ℝ} {x : ℕ → ℝ} {N : ℕ} (hNA : Real.exp A ≤ N)
    (hS1 : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ Bh ^ 2 * Real.exp A)
    (hS2 : ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2 ≤ N * Bh ^ 2) {c : ℝ} (hc : 0 < c) {sgn : ℝ}
    (hsgn : sgn = 1 ∨ sgn = -1)
    (hν : ∀ j : ℕ, ∀ τ ∈ Set.Icc (2 ^ j * ((N : ℝ) * Real.exp (-A)))
      (2 * (2 ^ j * ((N : ℝ) * Real.exp (-A)))), |ν (sgn * τ)| ≤ V + j)
    (hint : MeasureTheory.IntegrableOn (aliasIntegrandW φ ν x N (c / N) sgn)
      (Set.Ioi ((N : ℝ) * Real.exp (-A)))) :
    ∫ τ in Set.Ioi ((N : ℝ) * Real.exp (-A)), aliasIntegrandW φ ν x N (c / N) sgn τ ≤
      aliasConst Cφ p A Bh * V / c ^ p := by
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hT₀1 : 1 ≤ (N : ℝ) * Real.exp (-A) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos A), one_mul]; exact hNA
  obtain ⟨hsum, htsum⟩ := tsum_blocks_le (A := A) (Bh := Bh) hp hCφ hc (a := V) hV
  refine (integral_Ioi_le_of_dyadic (by linarith) hint hsum (fun j => by positivity)
    fun j => ?_).trans htsum
  have hU1 : 1 ≤ 2 ^ j * ((N : ℝ) * Real.exp (-A)) := by
    nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := j)]
  have hintb : IntervalIntegrable (aliasIntegrandW φ ν x N (c / N) sgn) volume
      (2 ^ j * ((N : ℝ) * Real.exp (-A))) (2 * (2 ^ j * ((N : ℝ) * Real.exp (-A)))) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr (hint.mono_set ?_)
    intro τ hτ
    have : (N : ℝ) * Real.exp (-A) ≤ 2 ^ j * ((N : ℝ) * Real.exp (-A)) :=
      le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    exact lt_of_le_of_lt this hτ.1
  refine (integral_aliasIntegrandW_block_le hCφ (by linarith) hdecay hN hS1 hS2
    (div_pos hc hN0) hsgn hU1 (hν j) hintb).trans ?_
  exact block_bound_le' hCφ (by linarith) hA hNA hc j

end RemainderW

/-- The symbol integrand of a block with weights `x`. -/
def symbolW (φ : ℝ → ℝ) (x : ℕ → ℝ) (c : ℝ) (N : ℕ) (X τ : ℝ) : ℝ :=
  ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N x τ‖ ^ 2 / N) * nuSymbol X τ

theorem integrable_symbolW (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (L : ℝ) :
    Integrable (symbolW φ x c N (Real.exp L)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hi := integrable_normSq_paperFT_mul_nuSymbol (contDiff_centredAtomicTest hφ x c N)
    (hasCompactSupport_centredAtomicTest hφsupp x hc hN) L
  refine (hi.const_mul ((c / N) ^ 2 * N)⁻¹).congr (Eventually.of_forall fun τ => ?_)
  simp only [symbolW]
  rw [norm_sq_paperFT_centredAtomicTest hφ.continuous hφc x hc hN τ]
  field_simp

theorem integrable_energyW (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    Integrable fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N x τ‖ ^ 2 / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hT : Continuous (cx (centredAtomicTest φ x c N)) :=
    Complex.continuous_ofReal.comp (contDiff_centredAtomicTest hφ x c N).continuous
  have hTc : HasCompactSupport (cx (centredAtomicTest φ x c N)) :=
    (hasCompactSupport_centredAtomicTest hφsupp x hc hN).comp_left Complex.ofReal_zero
  have hi := RHTower.KernelStrip.integrable_norm_sq_paperFT (hT.integrable_of_hasCompactSupport hTc)
    (hT.memLp_of_hasCompactSupport hTc)
  refine (hi.const_mul ((c / N) ^ 2 * N)⁻¹).congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [norm_sq_paperFT_centredAtomicTest hφ.continuous hφc x hc hN τ]
  field_simp

/-- **The remainder above the cut** for a block with weights `x`: replacing the symbol by
`log N/2π` above `N e^{−A}` costs `O(c^{−p})`. -/
theorem abs_remainderW_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, 2 ≤ |τ| → |mu τ - Real.log |τ| / (2 * Real.pi)| ≤ C) (L : ℝ) (hA : 0 ≤ A)
    {Bh : ℝ} {x : ℕ → ℝ} {N : ℕ} (hNA : Real.exp A ≤ N)
    (hS1 : ∑ n ∈ Icc 1 N, x n ^ 2 ≤ Bh ^ 2 * Real.exp A)
    (hS2 : ∑ n ∈ Icc 1 N, (n : ℝ) * x n ^ 2 ≤ N * Bh ^ 2) (hT2 : 2 ≤ (N : ℝ) * Real.exp (-A))
    {c : ℝ} (hc : 0 < c) :
    |∫ τ in (Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)))ᶜ,
        (symbolW φ x c N (Real.exp L) τ -
          Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N x τ‖ ^ 2 / N)))| ≤
      2 * (aliasConst Cφ p A Bh * (C + Real.exp L ^ 2 / Real.pi + A + 1) / c ^ p) := by
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp hA).trans hNA
  have hN : 1 ≤ N := by exact_mod_cast hN1
  set T₀ : ℝ := (N : ℝ) * Real.exp (-A) with hT₀
  set ν' : ℝ → ℝ := fun τ => nuSymbol (Real.exp L) τ - Real.log N / (2 * Real.pi) with hν'
  set S : ℝ → ℝ := fun τ => symbolW φ x c N (Real.exp L) τ -
    Real.log N / (2 * Real.pi) * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N x τ‖ ^ 2 / N)) with hS
  have hSi : Integrable S := (integrable_symbolW hφ hφsupp x hc hN L).sub
    ((integrable_energyW hφ hφsupp x hc hN).const_mul _)
  have hSeq : ∀ τ, S τ = ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N x τ‖ ^ 2 / N) * ν' τ := fun τ => by
    simp only [hS, hν', symbolW]; ring
  refine (abs_integral_le_integral_abs).trans ?_
  have hunion : (Set.Icc (-T₀) T₀)ᶜ = Set.Iio (-T₀) ∪ Set.Ioi T₀ := by
    ext τ; simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hτ; by_contra hc'; push Not at hc'; exact hτ ⟨hc'.1, hc'.2⟩
    · rintro (hτ | hτ) ⟨h1, h2⟩ <;> linarith
  have habsi : Integrable fun τ => |S τ| := hSi.abs
  rw [hunion, setIntegral_union (Set.disjoint_left.mpr fun τ h1 h2 => by
      simp only [Set.mem_Iio, Set.mem_Ioi] at h1 h2
      have : 0 ≤ T₀ := by positivity
      linarith) measurableSet_Ioi habsi.integrableOn habsi.integrableOn]
  have hpos : ∀ τ, |S τ| = aliasIntegrandW φ ν' x N (c / N) 1 τ := by
    intro τ
    rw [hSeq, aliasIntegrandW, one_mul, abs_mul, abs_of_nonneg (by positivity)]
  have hneg : ∀ τ, |S (-τ)| = aliasIntegrandW φ ν' x N (c / N) (-1) τ := by
    intro τ
    rw [hSeq, aliasIntegrandW, neg_one_mul, abs_mul, abs_of_nonneg (by positivity)]
  set V := C + Real.exp L ^ 2 / Real.pi + A + 1 with hV
  have hV1 : 1 ≤ V := by
    have : 0 ≤ Real.exp L ^ 2 / Real.pi := by positivity
    rw [hV]; linarith
  have hblocks : ∀ sgn : ℝ, |sgn| = 1 → ∀ j : ℕ, ∀ τ ∈ Set.Icc (2 ^ j * T₀) (2 * (2 ^ j * T₀)),
      |ν' (sgn * τ)| ≤ V + j := fun sgn hsgn j τ hτ =>
    abs_nuSymbol_sub_log_le hC L hA hT2 j hsgn hτ
  have hI1 : ∫ τ in Set.Ioi T₀, |S τ| ≤ aliasConst Cφ p A Bh * V / c ^ p := by
    have hfun : aliasIntegrandW φ ν' x N (c / N) 1 = fun τ => |S τ| :=
      funext fun τ => (hpos τ).symm
    have := integral_aliasingW_le_of_blocks hp hCφ hdecay hV1 hA hNA hS1 hS2 hc (Or.inl rfl)
      (hblocks 1 (by norm_num)) (by rw [hfun]; exact habsi.integrableOn)
    rwa [hfun] at this
  have hI2 : ∫ τ in Set.Iio (-T₀), |S τ| ≤ aliasConst Cφ p A Bh * V / c ^ p := by
    have hcomp : Integrable fun τ => |S (-τ)| := habsi.comp_neg
    have hfun : aliasIntegrandW φ ν' x N (c / N) (-1) = fun τ => |S (-τ)| :=
      funext fun τ => (hneg τ).symm
    have := integral_aliasingW_le_of_blocks hp hCφ hdecay hV1 hA hNA hS1 hS2 hc (Or.inr rfl)
      (hblocks (-1) (by norm_num)) (by rw [hfun]; exact hcomp.integrableOn)
    rw [hfun] at this
    simp only [integral_comp_neg_Ioi (f := fun τ => |S τ|)] at this
    rw [← integral_Iic_eq_integral_Iio]
    exact this
  linarith

/-- **The form of a block with window weights**: `c⁻¹⟨W x, x⟩/∫g² = pole/(c w ∫φ²) + (∫φ²)⁻¹ ∫ S_x`. -/
theorem atomForm_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {x : ℕ → ℝ} {N : ℕ}
    (hx : ∀ n : ℕ, 1 ≤ n → Real.log n - Real.log N ∉ Set.Icc (-A) 0 → x n = 0) (hA : 0 ≤ A)
    {c : ℝ} (hc : 0 < c) (hN : 1 ≤ N) (hcN : c ≤ N) :
    c⁻¹ * (weilQuad (atomicTest N x (atomDilate φ (c / N))) / ∫ u, atomDilate φ (c / N) u ^ 2) =
      (paperFT (EF.weilTest (cx (centredAtomicTest φ x c N)) (cx (centredAtomicTest φ x c N)))
          (Complex.I / 2) + paperFT (EF.weilTest (cx (centredAtomicTest φ x c N))
            (cx (centredAtomicTest φ x c N))) (-Complex.I / 2)).re /
          (c * (c / N * ∫ u, φ u ^ 2)) +
        (∫ u, φ u ^ 2)⁻¹ * ∫ τ, symbolW φ x c N (Real.exp (2 * (A + 1))) τ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hts : tsupport (centredAtomicTest φ x c N) ⊆ Set.Icc (-(A + 1)) (A + 1) :=
    (tsupport_centredAtomicTest_subset hφsupp hx hc hN).trans
      (Set.Icc_subset_Icc (by linarith) (by linarith))
  rw [← weilQuad_centredAtomicTest, weilQuad_eq_pole_add_symbol
    (contDiff_centredAtomicTest hφ x c N) hts, integral_atomDilate_sq φ hw]
  have hint : ∫ τ : ℝ, ‖paperFT (cx (centredAtomicTest φ x c N)) τ‖ ^ 2 *
      nuSymbol (Real.exp (2 * (A + 1))) τ =
      (c / N) ^ 2 * N * ∫ τ : ℝ, symbolW φ x c N (Real.exp (2 * (A + 1))) τ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [symbolW]
    rw [norm_sq_paperFT_centredAtomicTest hφ.continuous hφc x hc hN]
    field_simp
  rw [hint]
  have hM : 0 < ∫ u, φ u ^ 2 := hφ2
  field_simp

/-! ### The second-order term of the alternating window -/

/-- The pole terms of a real test are at most `2 |f̂(i/2)| |f̂(−i/2)|`. -/
theorem abs_re_pole_le {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    |(paperFT (EF.weilTest (cx f) (cx f)) (Complex.I / 2) +
        paperFT (EF.weilTest (cx f) (cx f)) (-Complex.I / 2)).re| ≤
      2 * (‖paperFT (cx f) (Complex.I / 2)‖ * ‖paperFT (cx f) (-Complex.I / 2)‖) := by
  have hcx : Continuous (cx f) := Complex.continuous_ofReal.comp hf
  have hcxc : HasCompactSupport (cx f) := hfc.comp_left Complex.ofReal_zero
  rw [EF.paperFT_weilTest hcx hcx hcxc hcxc, EF.paperFT_weilTest hcx hcx hcxc hcxc]
  have hc1 : conj (Complex.I / 2) = -Complex.I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-Complex.I / 2) = Complex.I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [hc1, hc2]
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (le_of_eq ?_))
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  ring

/-- The pole values of a recentred block: `|T̂(i/2)| |T̂(−i/2)| = w² |φ̂(wi/2)||φ̂(−wi/2)| |D_x(i/2)||D_x(−i/2)|`. -/
theorem norm_mul_norm_paperFT_centredAtomicTest {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (x : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    ‖paperFT (cx (centredAtomicTest φ x c N)) (Complex.I / 2)‖ *
        ‖paperFT (cx (centredAtomicTest φ x c N)) (-Complex.I / 2)‖ =
      (c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖) *
          (‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N x (-Complex.I / 2)‖) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  rw [paperFT_centredAtomicTest hφ hφc x hc hN, paperFT_centredAtomicTest hφ hφc x hc hN]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
  have e1 : -(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)) = ((Real.log N / 2 : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : -(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)) = ((-(Real.log N / 2) : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have he : ‖Complex.exp (-(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)))‖ *
      ‖Complex.exp (-(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)))‖ = 1 := by
    rw [e1, e2, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero]
  calc _ = (‖Complex.exp (-(Complex.I * (Complex.I / 2) * (Real.log N : ℂ)))‖ *
        ‖Complex.exp (-(Complex.I * (-Complex.I / 2) * (Real.log N : ℂ)))‖) *
        ((c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
          ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖) *
            (‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N x (-Complex.I / 2)‖)) := by ring
    _ = _ := by rw [he, one_mul]

/-- The pole terms of the alternating window are `O(N^{−2})` after normalization. -/
theorem exists_abs_altPole_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ N →
      |(paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h altSign N) c N))
          (cx (centredAtomicTest φ (twistedWeights h altSign N) c N))) (Complex.I / 2) +
        paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h altSign N) c N))
          (cx (centredAtomicTest φ (twistedWeights h altSign N) c N))) (-Complex.I / 2)).re /
          (c * (c / N * ∫ u, φ u ^ 2))| ≤ Cp / (N : ℝ) ^ 2 := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_norm_paperFT_le hφ.continuous hφc 1
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set S := ∑ j ∈ range 2, |altSign j| with hS
  set K := ((Lh : ℝ) + 1 * Bh) * Real.exp (2 * A) with hK
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * Φ ^ 2 * (2 * S * K) ^ 2 / ∫ u, φ u ^ 2, by positivity, fun N hN c hc hcN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hw1 : c / N ≤ 1 := (div_le_one hN0).mpr hcN
  set x := twistedWeights h altSign N with hx
  have hD : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → ‖s - 1‖ ≤ 1 →
      ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N x (gammaOf s)‖ ≤ 2 * S * K / N := by
    intro s h0 h2 h1
    refine (norm_twistedRiemannSum_le hh hA hsupp hB hLh meanZeroTwist_altSign h0 h2 hN).trans ?_
    rw [hK]
    gcongr
  have hD0 : ‖dirichletPoly N x (Complex.I / 2)‖ ≤ 2 * S * K / N := by
    have := hD 0 (by simp) (by simp) (by simp)
    rwa [neg_zero, Complex.cpow_zero, one_mul, gammaOf_zero] at this
  have hD1 : ‖dirichletPoly N x (-Complex.I / 2)‖ ≤ N * (2 * S * K / N) := by
    have := hD 1 (by simp) (by simp) (by simp)
    rw [Complex.cpow_neg_one, gammaOf_one, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hN0, inv_mul_le_iff₀ hN0] at this
    exact this
  have hφ1 : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ ≤ Φ := by
    refine hΦ _ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, norm_div, Complex.norm_I]
    norm_num
    nlinarith
  have hφ2' : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖ ≤ Φ := by
    refine hΦ _ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, norm_div, norm_neg,
      Complex.norm_I]
    norm_num
    nlinarith
  have hT := contDiff_centredAtomicTest hφ x c N
  have hTc := hasCompactSupport_centredAtomicTest hφsupp x hc hN
  have hpole := abs_re_pole_le hT.continuous hTc
  rw [norm_mul_norm_paperFT_centredAtomicTest hφ.continuous hφc x hc hN] at hpole
  have hprod : (c / N) ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (Complex.I / 2))‖ *
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * (-Complex.I / 2))‖) *
        (‖dirichletPoly N x (Complex.I / 2)‖ * ‖dirichletPoly N x (-Complex.I / 2)‖) ≤
      (c / N) ^ 2 * (Φ * Φ) * ((2 * S * K / N) * (N * (2 * S * K / N))) := by
    gcongr
  have hpos : 0 < c * (c / N * ∫ u, φ u ^ 2) := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  have key : 2 * ((c / N) ^ 2 * (Φ * Φ) * ((2 * S * K / N) * (N * (2 * S * K / N)))) *
      (N : ℝ) ^ 2 = 2 * Φ ^ 2 * (2 * S * K) ^ 2 / (∫ u, φ u ^ 2) *
        (c * (c / N * ∫ u, φ u ^ 2)) := by
    field_simp
  nlinarith [hpole, hprod, key]

/-- On the quiet region `|τ| ≤ N e^{−A}` the alternating symbol and energy integrands are
`O(log N/N²)` and `O(N^{−2})`. -/
theorem altLow_bounds {Cφ p : ℝ} (hp : 0 ≤ p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh)
    (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {Aν : ℝ}
    (hν : ∀ τ, |nuSymbol (Real.exp (2 * (A + 1))) τ| ≤ Aν + Real.log (2 + |τ|)) {N : ℕ}
    (hN : 1 ≤ N) {c : ℝ} {τ : ℝ} (hτ : |τ| ≤ (N : ℝ) * Real.exp (-A)) :
    ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h altSign N) τ‖ ^ 2 / N) ≤
      Cφ * (49 * (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / (N : ℝ) ^ 2) ∧
    |symbolW φ (twistedWeights h altSign N) c N (Real.exp (2 * (A + 1))) τ| ≤
      Cφ * (49 * (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / (N : ℝ) ^ 2) *
        (Aν + Real.log (2 + N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  set V := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) with hV
  have hD := norm_dirichletPoly_alt_le hsupp hA hB hL hN hτ
  have hD2 : ‖dirichletPoly N (twistedWeights h altSign N) τ‖ ^ 2 / N ≤ 49 * V ^ 2 / (N : ℝ) ^ 2 := by
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
    rw [div_le_iff₀ hN0]
    calc ‖dirichletPoly N (twistedWeights h altSign N) τ‖ ^ 2 ≤ (7 * (V / Real.sqrt N)) ^ 2 := h2
      _ = 49 * V ^ 2 / (N : ℝ) ^ 2 * N := by
          rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]; field_simp; ring
  have hφτ : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ Cφ := by
    have := hdecay (c / N * τ)
    rw [show ((c / N * τ : ℝ) : ℂ) = ((c / N : ℝ) : ℂ) * (τ : ℂ) by push_cast; ring] at this
    refine this.trans ?_
    have : (1 + |(c / N * τ)|) ^ (-p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (c / N * τ)]) (by linarith)
    nlinarith
  have hE : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (twistedWeights h altSign N) τ‖ ^ 2 / N) ≤ Cφ * (49 * V ^ 2 / (N : ℝ) ^ 2) :=
    mul_le_mul hφτ hD2 (by positivity) hCφ
  refine ⟨hE, ?_⟩
  have hlog : Real.log (2 + |τ|) ≤ Real.log (2 + N) := by
    have : |τ| ≤ N := hτ.trans (by
      have := Real.exp_le_one_iff.mpr (show -A ≤ 0 by linarith)
      nlinarith)
    exact Real.log_le_log (by positivity) (by linarith)
  unfold symbolW
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul hE ((hν τ).trans (by linarith)) (abs_nonneg _) (by positivity)

/-- **The second-order term of the alternating window.** For a `C²` profile on `[0, 1]` with
`|φ̂(u)|² ≤ C_φ (1 + |u|)^{−p}`, `p > 1`, a `C²` window profile `h` on `[−A, 0]`, and every schedule
with `c_N ≥ 1`, `c_N → ∞`, `c_N (log N)²/N → 0`:
`c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²)(𝒜_N(c/2) − 𝒜_N(c)) → 0` for `x_n = (−1)^n h(log(n/N))/√n`.
There is no Weil term: the alternating window is blind to the zeros. -/
theorem alternating_layer_sharp (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h altSign N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / (∫ u, φ u ^ 2) * altAlias φ h (c N) N) atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcN := tendsto_div_of_log_sq hc1 hclog
  obtain ⟨Cp, hCp0, hCp⟩ := exists_abs_altPole_le hφ hφsupp hφ2 hh hA hsupp
  obtain ⟨KE, hKE0, hKE⟩ := abs_altEnergy_sub_le hφ hφsupp hh hsupp (A := A)
  obtain ⟨C, hC0, hC⟩ := exists_abs_mu_sub_log_le
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (Real.exp_pos (2 * (A + 1))).le
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set M := ∫ u, φ u ^ 2 with hM
  set A' := A + 1 with hA'
  set V := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) with hV
  set x : ℕ → ℕ → ℝ := fun N => twistedWeights h altSign N with hx
  set T₀ : ℕ → ℝ := fun N => (N : ℝ) * Real.exp (-A') with hT₀
  set S : ℕ → ℝ → ℝ := fun N => symbolW φ (x N) (c N) N (Real.exp (2 * (A + 1))) with hS
  set E : ℕ → ℝ → ℝ := fun N τ => ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (x N) τ‖ ^ 2 / N) with hE
  set P : ℕ → ℝ := fun N =>
    (paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h altSign N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h altSign N) (c N) N))) (Complex.I / 2) +
    paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h altSign N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h altSign N) (c N) N))) (-Complex.I / 2)).re /
        (c N * (c N / N * M)) with hP
  set Rm : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ,
    (S N τ - Real.log N / (2 * Real.pi) * E N τ) with hRm
  set Lo : ℕ → ℝ := fun N => ∫ τ in Set.Icc (-T₀ N) (T₀ N), S N τ with hLo
  set LoE : ℕ → ℝ := fun N => Real.log N * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ with hLoE
  set Df : ℕ → ℝ := fun N => Real.log N * ((∫ τ, E N τ) - 2 * Real.pi * altAlias φ h (c N) N)
    with hDf
  -- eventual conditions
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := hlogN.eventually (eventually_ge_atTop 1)
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  have hevA := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp A'))
  have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A')) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
  have hevT := hT.eventually (eventually_ge_atTop 2)
  -- the pole terms
  have hPt : Tendsto P atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => Cp / (N : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    rw [Real.norm_eq_abs]
    exact hCp N hN (c N) (hc0 N) (by linarith [hc0 N])
  -- the quiet region
  have hquiet : ∀ N : ℕ, 1 ≤ N → ∀ τ ∈ Set.Icc (-T₀ N) (T₀ N), |τ| ≤ (N : ℝ) * Real.exp (-A) := by
    intro N hN τ hτ
    have h1 : |τ| ≤ T₀ N := abs_le.mpr hτ
    refine h1.trans ?_
    simp only [hT₀, hA']
    have : Real.exp (-(A + 1)) ≤ Real.exp (-A) := Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hvol : ∀ N : ℕ, volume.real (Set.Icc (-T₀ N) (T₀ N)) ≤ 2 * N := by
    intro N
    rw [Real.volume_real_Icc, max_eq_left (by
      simp only [hT₀]
      have : (0 : ℝ) ≤ N * Real.exp (-A') := by positivity
      linarith)]
    simp only [hT₀, hA']
    have : Real.exp (-(A + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  have hLot : Tendsto Lo atTop (𝓝 0) := by
    set W := Cφ * (49 * V ^ 2) with hW
    have hlim : Tendsto (fun N : ℕ => 2 * W * ((Aν + Real.log 3) / N + Real.log N / N)) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (Aν + Real.log 3) / (N : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_log_pow_div_natCast 1
      simpa using (h1.add h2).const_mul (2 * W)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hbd : ∀ τ ∈ Set.Icc (-T₀ N) (T₀ N), ‖S N τ‖ ≤ W / (N : ℝ) ^ 2 * (Aν + Real.log (2 + N)) :=
      fun τ hτ => by
        rw [Real.norm_eq_abs]
        have := (altLow_bounds (by linarith) hCφ hdecay hsupp hA hB hL hν hN (c := c N)
          (hquiet N hN τ hτ)).2
        show |symbolW φ (twistedWeights h altSign N) (c N) N (Real.exp (2 * (A + 1))) τ| ≤ _
        refine this.trans (le_of_eq ?_)
        rw [hW]; ring
    have hI := norm_setIntegral_le_of_norm_le_const
      (measure_Icc_lt_top : volume (Set.Icc (-T₀ N) (T₀ N)) < ⊤) hbd
    refine hI.trans ?_
    have hlog3 : Real.log (2 + N) ≤ Real.log 3 + Real.log N := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log (by positivity) (by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith)
    have hW0 : 0 ≤ W := by rw [hW]; positivity
    have hA0 : 0 ≤ Aν + Real.log (2 + N) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + N by linarith); linarith
    calc W / (N : ℝ) ^ 2 * (Aν + Real.log (2 + N)) * volume.real (Set.Icc (-T₀ N) (T₀ N))
        ≤ W / (N : ℝ) ^ 2 * (Aν + Real.log (2 + N)) * (2 * N) :=
          mul_le_mul_of_nonneg_left (hvol N) (by positivity)
      _ = 2 * W * ((Aν + Real.log (2 + N)) / N) := by field_simp
      _ ≤ 2 * W * ((Aν + Real.log 3) / N + Real.log N / N) := by
          gcongr
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by linarith) hN0.le
  have hLoEt : Tendsto LoE atTop (𝓝 0) := by
    set W := Cφ * (49 * V ^ 2) with hW
    have hlim : Tendsto (fun N : ℕ => 2 * W * (Real.log N / N)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
        simpa using tendsto_log_pow_div_natCast 1
      simpa using h2.const_mul (2 * W)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hbd : ∀ τ ∈ Set.Icc (-T₀ N) (T₀ N), ‖E N τ‖ ≤ W / (N : ℝ) ^ 2 := fun τ hτ => by
      have := (altLow_bounds (by linarith) hCφ hdecay hsupp hA hB hL hν hN (c := c N)
        (hquiet N hN τ hτ)).1
      show ‖‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h altSign N) τ‖ ^ 2 / N)‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine this.trans (le_of_eq ?_)
      rw [hW]; ring
    have hI := norm_setIntegral_le_of_norm_le_const
      (measure_Icc_lt_top : volume (Set.Icc (-T₀ N) (T₀ N)) < ⊤) hbd
    simp only [hLoE]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have hW0 : 0 ≤ W := by rw [hW]; positivity
    calc Real.log N * ‖∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ‖
        ≤ Real.log N * (W / (N : ℝ) ^ 2 * volume.real (Set.Icc (-T₀ N) (T₀ N))) :=
          mul_le_mul_of_nonneg_left hI hlog0
      _ ≤ Real.log N * (W / (N : ℝ) ^ 2 * (2 * N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hvol N) (by positivity)) hlog0
      _ = 2 * W * (Real.log N / N) := by field_simp
  -- the remainder above the cut
  have hRmt : Tendsto Rm atTop (𝓝 0) := by
    set VV := C + Real.exp (2 * (A + 1)) ^ 2 / Real.pi + A' + 1 with hVV
    have hcp : Tendsto (fun N : ℕ => c N ^ p) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hcinf
    have hlim : Tendsto (fun N : ℕ => 2 * (aliasConst Cφ p A' Bh * VV / c N ^ p)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := aliasConst Cφ p A' Bh * VV)).div_atTop hcp
      simpa using this.const_mul 2
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hevA, hevT, eventually_ge_atTop 1] with N h1 h2 hN
    rw [Real.norm_eq_abs]
    have hS1 : ∑ n ∈ Icc 1 N, x N n ^ 2 ≤ Bh ^ 2 * Real.exp A' := by
      have hsq : ∑ n ∈ Icc 1 N, x N n ^ 2 = ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 :=
        sum_congr rfl fun n _ => by
          simp only [hx, twistedWeights, mul_pow, altSign_sq, mul_one]
      rw [hsq]
      refine (sum_horizonWeights_sq_le hsupp hB hN).trans ?_
      gcongr
      linarith
    have hS2 : ∑ n ∈ Icc 1 N, (n : ℝ) * x N n ^ 2 ≤ N * Bh ^ 2 := by
      have hsq : ∑ n ∈ Icc 1 N, (n : ℝ) * x N n ^ 2 =
          ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 :=
        sum_congr rfl fun n _ => by
          simp only [hx, twistedWeights, mul_pow, altSign_sq, mul_one]
      rw [hsq]
      exact sum_mul_horizonWeights_sq_le hB N
    exact abs_remainderW_le hφ hφsupp hp hCφ hdecay hC0 hC (2 * (A + 1)) (by linarith) h1 hS1 hS2
      h2 (hc0 N)
  -- the energy defect
  have hDft : Tendsto Df atTop (𝓝 0) := by
    have t1 : Tendsto (fun N : ℕ => Real.log N * (c N / N)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hclog
      · have := hc1 N
        have := Real.log_natCast_nonneg N
        positivity
      · filter_upwards [hev3] with N hN
        have hc0' : 0 ≤ c N / N := by have := hc1 N; positivity
        calc Real.log N * (c N / N) ≤ Real.log N * Real.log N * (c N / N) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hN) hc0'
          _ = c N * Real.log N ^ 2 / N := by ring
    have hlim := t1.const_mul KE
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [Real.norm_eq_abs]
    simp only [hDf]
    rw [abs_mul, abs_of_nonneg hlog0]
    have := hKE (c N) (hc1 N) N h4
    calc Real.log N * |(∫ τ, E N τ) - 2 * Real.pi * altAlias φ h (c N) N|
        ≤ Real.log N * (KE * c N / N) := mul_le_mul_of_nonneg_left this hlog0
      _ = KE * (Real.log N * (c N / N)) := by ring
  -- the identity
  have hid : ∀ᶠ N : ℕ in atTop, P N + M⁻¹ * Lo N + M⁻¹ * Rm N - M⁻¹ * (2 * Real.pi)⁻¹ * LoE N +
      M⁻¹ * (2 * Real.pi)⁻¹ * Df N =
      (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h altSign N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / M * altAlias φ h (c N) N := by
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hcle : c N ≤ N := by linarith [hc0 N]
    rw [atomForm_eq hφ hφsupp hφ2 (twistedWeights_eq_zero hsupp altSign N) hA (hc0 N) hN hcle,
      ← hM]
    have hSi : Integrable (S N) := integrable_symbolW hφ hφsupp (x N) (hc0 N) hN (2 * (A + 1))
    have hEi : Integrable (E N) := integrable_energyW hφ hφsupp (x N) (hc0 N) hN
    have hsplitS := (integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hSi).symm
    have hsplitE := integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hEi
    have hcompl : ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, S N τ = Rm N +
        Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, E N τ := by
      simp only [hRm]
      rw [integral_sub hSi.integrableOn (hEi.const_mul _).integrableOn, integral_const_mul]
      ring
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hM0 : M ≠ 0 := hφ2.ne'
    have hSeq : (∫ τ, symbolW φ (twistedWeights h altSign N) (c N) N
        (Real.exp (2 * (A + 1))) τ) = ∫ τ, S N τ := rfl
    rw [hSeq, hsplitS, hcompl]
    simp only [hP, hLo, hLoE, hDf]
    rw [← hsplitE]
    have hpi' : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
    linear_combination (-(M⁻¹ * Real.log N * altAlias φ h (c N) N)) * hpi'
  refine Tendsto.congr' hid ?_
  have := (((hPt.add (hLot.const_mul M⁻¹)).add (hRmt.const_mul M⁻¹)).sub
    (hLoEt.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))).add (hDft.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))
  simpa using this

/-! ### At the critical curve: the conductor-two count -/

/-- **The alternating window at the critical curve.** For every profile whose bulk energy has the
rescaled limit `s^β E₁(s) → J`, along `c^{β+1}/log N → K`:
`c⁻¹⟨W x, x⟩/∫g² → (2^{β+1} − 1) β J/K ∫ e^{−(β+1)y} H²`. The half-overlap aliasing counts
`2^{β+1}` times the full one, and the alternating sign removes one copy. -/
theorem alternating_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h altSign N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (((2 : ℝ) ^ (β + 1) - 1) * β * J / K *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, hcN⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  rw [show β + 1 + 1 = β + 2 by ring] at hcN
  have hsharp := alternating_layer_sharp hφ hφsupp hφ2 (by linarith : (1 : ℝ) < p) hCφ hdecay hh hA
    hsupp hc1 hcinf hclog
  set M := ∫ u, φ u ^ 2 with hM
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  -- the full overlap
  have h1 := tendsto_rpow_mul_horizonAlias_of_regularBulk hφ hφsupp hφ2 hp hCφ hdecay hbulk
    hh hA hsupp hc1 hcinf hcN
  -- the half overlap, along `c' = max(c/2, 1)`
  set c' : ℕ → ℝ := fun N => max (c N / 2) 1 with hc'
  have hc'1 : ∀ N, 1 ≤ c' N := fun N => le_max_right _ _
  have hc'le : ∀ N, c' N ≤ c N := fun N => max_le (by linarith [hc1 N]) (hc1 N)
  have hc'inf : Tendsto c' atTop atTop :=
    tendsto_atTop_mono (fun N => le_max_left _ _) (hcinf.atTop_div_const (by norm_num))
  have hc'N : Tendsto (fun N : ℕ => c' N ^ (β + 2) / N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by have := hc'1 N; positivity) (fun N => ?_) hcN
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (by linarith [hc'1 N]) (hc'le N)
      (by linarith)) (Nat.cast_nonneg _)
  have h2 := tendsto_rpow_mul_horizonAlias_of_regularBulk hφ hφsupp hφ2 hp hCφ hdecay hbulk
    hh hA hsupp hc'1 hc'inf hc'N
  have hev : ∀ᶠ N : ℕ in atTop, c' N = c N / 2 := by
    filter_upwards [hcinf.eventually (eventually_ge_atTop 2)] with N hN
    exact max_eq_left (by linarith)
  have hinv : Tendsto (fun N : ℕ => Real.log N / c N ^ (β + 1)) atTop (𝓝 K⁻¹) :=
    (hcrit.inv₀ hK.ne').congr fun N => by rw [inv_div]
  have hterm : Tendsto (fun N : ℕ => Real.log N / M * altAlias φ h (c N) N) atTop
      (𝓝 (K⁻¹ * ((2 : ℝ) ^ (β + 1) * (J * (β * I)) - J * (β * I)))) := by
    refine (hinv.mul ((h2.const_mul ((2 : ℝ) ^ (β + 1))).sub h1)).congr' ?_
    filter_upwards [hev] with N hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hcp : 0 < c N ^ (β + 1) := Real.rpow_pos_of_pos hc0 _
    have hM0 : M ≠ 0 := hφ2.ne'
    have hsplit : (2 : ℝ) ^ (β + 1) * (c N / 2) ^ (β + 1) = c N ^ (β + 1) := by
      rw [Real.div_rpow hc0.le (by norm_num), mul_div_cancel₀ _ (by positivity)]
    simp only [altAlias, hN]
    rw [← hsplit, ← hM]
    field_simp
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : K⁻¹ * ((2 : ℝ) ^ (β + 1) * (J * (β * I)) - J * (β * I)) =
      ((2 : ℝ) ^ (β + 1) - 1) * β * J / K * I := by
    field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

/-- The conductor-two Jordan coefficient counts `#ℙ⁷(𝔽₂) = 255` points: `J(2) = 255 J(1)`. -/
theorem jordanCoefficient_two :
    ArithmeticDegenerationTheory.jordanCoefficient 2 = 255 * tiltedJordanOne := by
  have hJ := ArithmeticDegenerationTheory.jordanTotient_prime_pow Nat.prime_two 8 (a := 1) le_rfl
  rw [pow_one] at hJ
  unfold ArithmeticDegenerationTheory.jordanCoefficient tiltedJordanOne
  rw [hJ, Nat.totient_two]
  norm_num
  ring

/-- **The alternating window counts the conductor-two points.** For the tilted spline and a `C²`
window profile on `[−A, 0]`, along `c⁸/log N → K`: the window `x_n = (−1)^n h(log(n/N))/√n` has
`c⁻¹⟨W x, x⟩/∫g² → (7 J(2)/K) ∫ e^{−8y} H²`, `J(2) = J(1) #ℙ⁷(𝔽₂)`. The second-order term of the
conductor-two window is the first-order count of conductor two; there is no Weil term. -/
theorem alternating_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h altSign N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2))
      atTop (𝓝 (7 * ArithmeticDegenerationTheory.jordanCoefficient 2 / K *
        ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := alternating_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA hsupp hc1 hK hcrit'
  have h256 : (2 : ℝ) ^ ((7 : ℝ) + 1) = 256 := by
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hint : ∫ y, Real.exp (-(((7 : ℝ) + 1) * y)) * halfWeight h y ^ 2 =
      ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
    congr 1; funext y; norm_num
  rw [h256, hint] at hlim
  rw [jordanCoefficient_two]
  convert hlim using 2
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
