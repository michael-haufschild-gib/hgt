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
      |∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h altSign N) τ‖ ^ 2 / N) -
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
    rw [mul_sum, ← mul_sub, ← mul_sub, ← sum_sub_distrib, mul_sum, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hx2 : twistedWeights h altSign N n * (altSign n * horizonWeights h N n) =
        h (Real.log n - Real.log N) ^ 2 / n := by
      rw [twistedWeights, show horizonWeights h N n * altSign n * (altSign n *
        horizonWeights h N n) = altSign n ^ 2 * (horizonWeights h N n * horizonWeights h N n) by
        ring, altSign_sq, one_mul, horizonWeights, div_mul_div_comm, Real.mul_self_sqrt hn0.le, sq]
    rw [show c / 2 * n / N = c * n / N / 2 by ring, ← mul_assoc, hx2]
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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
