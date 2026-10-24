import GaloisForLFunctions.BezoutValuationIncidence.MinorArcSumsAtCompositeRootsOfUnity

/-!
# The dual norm at composite moduli below the diagonal

The receiver's small-scale rows live on squarefree moduli, so the cross-scale dual norm is needed
at every modulus `d`, not only at primes. At a composite `d` the spectral law contains roots of
unity of every order `k ∣ d`, and roots of small order are major arcs. They carry little weight.

* **Coprime reduction.** With `g = gcd(j, d)`, `Φ_d(jn) - (g² - 1)/12 = g² Φ_{d/g}((j/g) n)`
  (`residuePotential_mul_mul`), and `j/g` is coprime to `d/g`; so the `j`-th harmonic is
  `g² Σ_{η ∈ T_{d/g}} |η - 1|^{-2} S₂(η^{j/g})`, and `η^{j/g}` is a primitive root of the same
  order as `η`.
* **Split by order.** Roots of order `k ≤ R` number at most `R²` and have weight
  `|η - 1|^{-2} ≤ R²/16`; they contribute `≤ R⁴ T/16` with `T` the trivial bound for `S₂`. Roots of
  order `k > R` are minor arcs at denominator `k`, with total weight `≤ (d/g)²/12`.
* **Summing the harmonics** with `Σ_j gcd(j, d)²/j² ≤ 2d` gives the all-moduli law
  `|Λ_d(c')| ≤ R⁴ T d/8 + π² d² M/72 + π² d³ T₃/144` (`abs_kernelStatisticAll_le_of_orderSplit`).

With `R = ⌊Q^{3δ/16}⌋`, `U = ⌊Q^{δ/16}⌋` and the composite minor-arc laws, both actual rows have a
power saving at every modulus `Q^δ ≤ d ≤ Q^{1-δ}`
(`abs_kernelStatisticAll_moebiusWindowRow_le_rpow`,
`exists_abs_kernelStatisticAll_centredPrimeBlock_le_rpow`): the cross-scale form of the actual rows
has a power saving below the diagonal for arbitrary bounded small-scale rows on all moduli
(`abs_rowBilinear_moebiusWindowRow_sub_kernelMeanMain_le_rpow`).
-/

open Finset Filter Topology ArithmeticFunction RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The coprime reduction of a harmonic -/

/-- `Φ_{gd'}(gx) = g² Φ_{d'}(x) + (g² - 1)/12`. -/
theorem residuePotential_mul_mul (g d' x : ℕ) :
    residuePotential (g * d') (g * x) = (g : ℝ) ^ 2 * residuePotential d' x + ((g : ℝ) ^ 2 - 1) / 12 := by
  unfold residuePotential
  rw [Nat.mul_mod_mul_left]
  push_cast
  ring

/-- **The coprime reduction.** `Σ_n (c'(n)/n²)(Φ_d(jn) - (g² - 1)/12) = g² Σ_n (c'(n)/n²) Φ_{d/g}((j/g)n)`
with `g = gcd(j, d)`. -/
theorem sum_mul_residuePotential_sub_gcd_eq_coprime (d j N : ℕ) (c' : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        (residuePotential d (j * n) - (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12) =
      ((Nat.gcd j d : ℕ) : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
        residuePotential (d / Nat.gcd j d) ((j / Nat.gcd j d) * n) := by
  rw [mul_sum]
  refine sum_congr rfl fun n _ => ?_
  have key : residuePotential d (j * n) = ((Nat.gcd j d : ℕ) : ℝ) ^ 2 *
      residuePotential (d / Nat.gcd j d) ((j / Nat.gcd j d) * n) +
        (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12 := by
    rw [← residuePotential_mul_mul, ← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left j d),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right j d)]
  rw [key]
  ring

/-! ## §2. Splitting the spectral sum by the order of the root -/

/-- At most `R²` roots of unity have order at most `R`. -/
theorem card_filter_orderOf_le (d R : ℕ) :
    (((nontrivialRoots d).filter (fun η => orderOf η ≤ R)).card : ℝ) ≤ (R : ℝ) ^ 2 := by
  classical
  have hsub : (nontrivialRoots d).filter (fun η => orderOf η ≤ R) ⊆
      (Icc 1 R).biUnion (fun k => Polynomial.nthRootsFinset k (1 : ℂ)) := by
    intro η hη
    obtain ⟨hηd, hR⟩ := mem_filter.mp hη
    rw [nontrivialRoots, mem_erase] at hηd
    obtain ⟨_, hroot⟩ := hηd
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp at hroot
      · exact h
    have hfin : 0 < orderOf η := by
      have h1 : η ^ d = 1 := (Polynomial.mem_nthRootsFinset hd 1).mp hroot
      exact orderOf_pos_iff.mpr ((isOfFinOrder_iff_pow_eq_one).mpr ⟨d, hd, h1⟩)
    refine mem_biUnion.mpr ⟨orderOf η, mem_Icc.mpr ⟨hfin, hR⟩, ?_⟩
    exact (Polynomial.mem_nthRootsFinset hfin 1).mpr (pow_orderOf_eq_one η)
  have hcard := (card_le_card hsub).trans card_biUnion_le
  have hroots : ∀ k ∈ Icc 1 R, (Polynomial.nthRootsFinset k (1 : ℂ)).card = k := fun k hk =>
    (Complex.isPrimitiveRoot_exp k (by have := (mem_Icc.mp hk).1; omega)).card_nthRootsFinset
  rw [sum_congr rfl hroots] at hcard
  have hsum : ∑ k ∈ Icc 1 R, k ≤ R * R := by
    calc ∑ k ∈ Icc 1 R, k ≤ ∑ _k ∈ Icc 1 R, R := sum_le_sum fun k hk => (mem_Icc.mp hk).2
      _ = R * R := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
  have : ((nontrivialRoots d).filter (fun η => orderOf η ≤ R)).card ≤ R * R := hcard.trans hsum
  rw [sq]
  exact_mod_cast this

/-- **The order split.** Let `j'` be coprime to `d'`. If `‖S₂(w)‖ ≤ T` on the unit circle and
`‖S₂(w)‖ ≤ M` at every primitive root of order `R < k ≤ d'`, then
`|Σ_n (c'(n)/n²) Φ_{d'}(j' n)| ≤ R⁴ T/16 + (d'² - 1) M/12`. -/
theorem abs_sum_residuePotential_coprime_le {d' j' N R : ℕ} (hd' : 0 < d')
    (hj' : Nat.Coprime j' d') (c' : ℕ → ℝ) {T M : ℝ} (hT0 : 0 ≤ T) (hM0 : 0 ≤ M)
    (hT : ∀ w : ℂ, ‖w‖ = 1 → ‖rowTransform N c' w‖ ≤ T)
    (hM : ∀ k : ℕ, R < k → k ≤ d' → ∀ w : ℂ, IsPrimitiveRoot w k → ‖rowTransform N c' w‖ ≤ M) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential d' (j' * n)| ≤
      (R : ℝ) ^ 4 / 16 * T + ((d' : ℝ) ^ 2 - 1) / 12 * M := by
  classical
  rw [← Real.norm_eq_abs, ← Complex.norm_real, sum_mul_residuePotential_eq_spectral hd' N j' c']
  set a : ℂ → ℝ := fun η => (‖η - 1‖ ^ 2)⁻¹
  have hterm : ∀ η ∈ nontrivialRoots d', ‖((a η : ℝ) : ℂ) * rowTransform N c' (η ^ j')‖ ≤
      (if orderOf η ≤ R then (R : ℝ) ^ 2 / 16 * T else 0) + a η * M := by
    intro η hη
    obtain ⟨hne, hpow⟩ := (mem_nontrivialRoots hd').mp hη
    have hnorm := norm_eq_one_of_mem_nontrivialRoots hd' hη
    have hdvd : orderOf η ∣ d' := orderOf_dvd_of_pow_eq_one hpow
    have hk0 : 0 < orderOf η := Nat.pos_of_ne_zero fun h => by
      rw [h] at hdvd; exact hd'.ne' (Nat.eq_zero_of_zero_dvd hdvd)
    have ha0 : 0 ≤ a η := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
    split_ifs with hkR
    · -- small order: `|η - 1| ≥ 4/k ≥ 4/R` and the trivial bound
      have hw : ‖η ^ j'‖ = 1 := by rw [norm_pow, hnorm, one_pow]
      have h4 : 4 / (orderOf η : ℝ) ≤ ‖η - 1‖ := by
        have ht := one_div_le_toIntDist_rootAngle_of_pow hk0 hnorm (pow_orderOf_eq_one η) hne
        have h4' := four_mul_toIntDist_rootAngle_le hnorm
        calc 4 / (orderOf η : ℝ) = 4 * (1 / orderOf η) := by ring
          _ ≤ 4 * toIntDist (rootAngle η) := by linarith
          _ ≤ _ := h4'
      have hkR' : (orderOf η : ℝ) ≤ R := by exact_mod_cast hkR
      have hk0' : (0 : ℝ) < orderOf η := by exact_mod_cast hk0
      have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hk0' hkR'
      have hpos : 0 < ‖η - 1‖ := lt_of_lt_of_le (div_pos (by norm_num) hk0') h4
      have hab : a η ≤ (R : ℝ) ^ 2 / 16 := by
        simp only [a]
        rw [inv_le_comm₀ (by positivity) (by positivity)]
        calc ((R : ℝ) ^ 2 / 16)⁻¹ = (4 / (R : ℝ)) ^ 2 := by field_simp; ring
          _ ≤ (4 / (orderOf η : ℝ)) ^ 2 := by gcongr
          _ ≤ ‖η - 1‖ ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      have := mul_le_mul hab (hT _ hw) (norm_nonneg _) (by positivity)
      have : 0 ≤ a η * M := mul_nonneg ha0 hM0
      linarith
    · -- large order: `η^{j'}` is a primitive root of order `ord η ∈ (R, d']`
      push Not at hkR
      have hcop : Nat.Coprime j' (orderOf η) := Nat.Coprime.coprime_dvd_right hdvd hj'
      have hprim : IsPrimitiveRoot (η ^ j') (orderOf η) :=
        (IsPrimitiveRoot.orderOf η).pow_of_coprime j' hcop
      have h := hM (orderOf η) hkR (Nat.le_of_dvd hd' hdvd) _ hprim
      rw [zero_add]
      exact mul_le_mul_of_nonneg_left h ha0
  have hsum : ∑ η ∈ nontrivialRoots d', ((if orderOf η ≤ R then (R : ℝ) ^ 2 / 16 * T else 0) +
      a η * M) ≤ (R : ℝ) ^ 4 / 16 * T + ((d' : ℝ) ^ 2 - 1) / 12 * M := by
    rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul, ← sum_mul]
    have hcard := card_filter_orderOf_le d' R
    have hW : ∑ η ∈ nontrivialRoots d', a η = ((d' : ℝ) ^ 2 - 1) / 12 :=
      sum_nontrivialRoots_inv_norm_sq hd'
    rw [hW]
    have hRT : 0 ≤ (R : ℝ) ^ 2 / 16 * T := by positivity
    calc (((nontrivialRoots d').filter (fun η => orderOf η ≤ R)).card : ℝ) * ((R : ℝ) ^ 2 / 16 * T) +
          ((d' : ℝ) ^ 2 - 1) / 12 * M
        ≤ (R : ℝ) ^ 2 * ((R : ℝ) ^ 2 / 16 * T) + ((d' : ℝ) ^ 2 - 1) / 12 * M := by
          gcongr
      _ = (R : ℝ) ^ 4 / 16 * T + ((d' : ℝ) ^ 2 - 1) / 12 * M := by ring
  exact (norm_sum_le _ _).trans ((sum_le_sum hterm).trans hsum)

/-! ## §3. Summing the harmonics -/

/-- `Σ_{j < K} gcd(j+1, d)²/(j+1)² ≤ 2d`. -/
theorem sum_range_gcd_sq_div_sq_le {d : ℕ} (hd : 1 ≤ d) (K : ℕ) :
    ∑ j ∈ range K, ((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 / ((j : ℝ) + 1) ^ 2 ≤ 2 * (d : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hterm : ∀ j ∈ range K, ((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 / ((j : ℝ) + 1) ^ 2 ≤
      (if j < d then 1 else 0) + (if d ≤ j then (d : ℝ) ^ 2 * (1 / ((j : ℝ) + 1) ^ 2) else 0) := by
    intro j _
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hg1 : ((Nat.gcd (j + 1) d : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.le_of_dvd (Nat.succ_pos j) (Nat.gcd_dvd_left _ _)
    have hg2 : ((Nat.gcd (j + 1) d : ℕ) : ℝ) ≤ d := by
      exact_mod_cast Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
    have hg0 : (0 : ℝ) ≤ ((Nat.gcd (j + 1) d : ℕ) : ℝ) := Nat.cast_nonneg _
    by_cases hjd : j < d
    · rw [if_pos hjd, if_neg (by omega), add_zero, div_le_one (by positivity)]
      exact pow_le_pow_left₀ hg0 hg1 2
    · rw [if_neg hjd, if_pos (by omega), zero_add, mul_one_div]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hg0 hg2 2) (by positivity)
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← mul_sum]
  have h1 : (((range K).filter (fun j => j < d)).card : ℝ) ≤ d := by
    have : (range K).filter (fun j => j < d) ⊆ range d := fun j hj => by
      simp only [mem_filter, mem_range] at hj ⊢; exact hj.2
    exact_mod_cast (card_le_card this).trans (card_range d).le
  have hfilt : (range K).filter (fun j => d ≤ j) = Ico d K := by
    ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hfilt]
  have h2 := sum_Ico_one_div_succ_sq_le hd K
  have h3 : (d : ℝ) ^ 2 * ∑ j ∈ Ico d K, 1 / ((j : ℝ) + 1) ^ 2 ≤ d := by
    calc (d : ℝ) ^ 2 * ∑ j ∈ Ico d K, 1 / ((j : ℝ) + 1) ^ 2 ≤ (d : ℝ) ^ 2 * (1 / (d : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = d := by field_simp
  linarith

/-- **The quadratic layer at any modulus.** Under the hypotheses of the order split for every
`d' ∣ d`, `|Σ_n (c'(n)/n²)(𝔅(d, n) - m_d)| ≤ R⁴ T d/8 + π² d² M/72`. -/
theorem abs_quadraticLayer_le_of_orderSplit {d N R : ℕ} (hd : 1 ≤ d) (c' : ℕ → ℝ) {T M : ℝ}
    (hT0 : 0 ≤ T) (hM0 : 0 ≤ M) (hT : ∀ w : ℂ, ‖w‖ = 1 → ‖rowTransform N c' w‖ ≤ T)
    (hM : ∀ k : ℕ, R < k → k ≤ d → ∀ w : ℂ, IsPrimitiveRoot w k → ‖rowTransform N c' w‖ ≤ M) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * (bernoulliKernel d n - kernelMean d)| ≤
      (R : ℝ) ^ 4 * T * d / 8 + Real.pi ^ 2 * (d : ℝ) ^ 2 * M / 72 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hz : HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have ht := hasSum_sum_mul_bernoulliKernel_sub_kernelMean (by omega : 0 < d) N c'
  refine le_of_tendsto' ht.tendsto_sum_nat.abs fun K => ?_
  -- each harmonic: `|H_j| ≤ g² R⁴ T/16 + d² M/12`
  have hH : ∀ j : ℕ, |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
      (residuePotential d ((j + 1) * n) - (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12)| ≤
      ((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 * ((R : ℝ) ^ 4 / 16 * T) + (d : ℝ) ^ 2 / 12 * M := by
    intro j
    set g := Nat.gcd (j + 1) d with hgdef
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
    have hgd : g ∣ d := Nat.gcd_dvd_right _ _
    have hd' : 0 < d / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgd) hg0
    have hcop : Nat.Coprime ((j + 1) / g) (d / g) := Nat.coprime_div_gcd_div_gcd hg0
    rw [sum_mul_residuePotential_sub_gcd_eq_coprime, abs_mul, abs_of_nonneg (by positivity)]
    have hsplit := abs_sum_residuePotential_coprime_le hd' hcop c' hT0 hM0 hT
      (fun k hk hkd w hw => hM k hk (hkd.trans (Nat.div_le_self d g)) w hw)
    have hdg : ((d / g : ℕ) : ℝ) * g = d := by
      exact_mod_cast Nat.div_mul_cancel hgd
    have hgR : (0 : ℝ) < g := by exact_mod_cast hg0
    calc (g : ℝ) ^ 2 * |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 * residuePotential (d / g) ((j + 1) / g * n)|
        ≤ (g : ℝ) ^ 2 * ((R : ℝ) ^ 4 / 16 * T + (((d / g : ℕ) : ℝ) ^ 2 - 1) / 12 * M) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ ≤ (g : ℝ) ^ 2 * ((R : ℝ) ^ 4 / 16 * T) + (d : ℝ) ^ 2 / 12 * M := by
          have e : (g : ℝ) ^ 2 * (((d / g : ℕ) : ℝ) ^ 2 - 1) / 12 * M =
              ((d : ℝ) ^ 2 - (g : ℝ) ^ 2) / 12 * M := by rw [← hdg]; ring
          have : 0 ≤ (g : ℝ) ^ 2 / 12 * M := by positivity
          nlinarith [e]
  have hg := sum_range_gcd_sq_div_sq_le hd K
  have hz' : ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum _ (fun j _ => by positivity) hz
  calc |∑ j ∈ range K, (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2 *
          (residuePotential d ((j + 1) * n) - (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 - 1) / 12)) *
          (1 / ((j : ℝ) + 1) ^ 2)|
      ≤ ∑ j ∈ range K, ((R : ℝ) ^ 4 / 16 * T *
          (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 / ((j : ℝ) + 1) ^ 2) +
          (d : ℝ) ^ 2 / 12 * M * (1 / ((j : ℝ) + 1) ^ 2)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1) ^ 2)]
        calc _ ≤ (((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 * ((R : ℝ) ^ 4 / 16 * T) +
              (d : ℝ) ^ 2 / 12 * M) * (1 / ((j : ℝ) + 1) ^ 2) :=
              mul_le_mul_of_nonneg_right (hH j) (by positivity)
          _ = _ := by ring
    _ = (R : ℝ) ^ 4 / 16 * T * ∑ j ∈ range K, ((Nat.gcd (j + 1) d : ℕ) : ℝ) ^ 2 / ((j : ℝ) + 1) ^ 2 +
          (d : ℝ) ^ 2 / 12 * M * ∑ j ∈ range K, 1 / ((j : ℝ) + 1) ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ (R : ℝ) ^ 4 / 16 * T * (2 * d) + (d : ℝ) ^ 2 / 12 * M * (Real.pi ^ 2 / 6) := by
        gcongr
    _ = (R : ℝ) ^ 4 * T * d / 8 + Real.pi ^ 2 * (d : ℝ) ^ 2 * M / 72 := by ring

/-- The cubic layer, trivially: `|Σ_n (c'(n)/n³) 𝔅₃(d, n)| ≤ π² d³ T₃/144` when `‖S₃‖ ≤ T₃`. -/
theorem abs_cubicLayer_le {d N : ℕ} (hd : 1 ≤ d) (c' : ℕ → ℝ) {T₃ : ℝ} (hT₃0 : 0 ≤ T₃)
    (hT₃ : ∀ w : ℂ, ‖w‖ = 1 → ‖cubicRowTransform N c' w‖ ≤ T₃) :
    |∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 3 * cubicKernel d n| ≤ Real.pi ^ 2 * (d : ℝ) ^ 3 * T₃ / 144 := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hmax : cubicRowTransformMax N c' d ≤ T₃ :=
    cubicRowTransformMax_le_of_forall hT₃0 fun ζ hζ => hT₃ ζ (norm_eq_one_of_mem_nontrivialRoots hd0 hζ)
  have hW3 : ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3 ≤ (d : ℝ) ^ 3 / 48 := by
    calc ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3
        ≤ ∑ η ∈ nontrivialRoots d, (d : ℝ) / 4 * (‖η - 1‖ ^ 2)⁻¹ := by
          refine sum_le_sum fun η hη => ?_
          have h4 := four_div_le_norm_sub_one_of_mem_nontrivialRoots hd0 hη
          have hpos : 0 < ‖η - 1‖ := lt_of_lt_of_le (by positivity) h4
          have hinv : 1 / ‖η - 1‖ ≤ (d : ℝ) / 4 := by
            rw [div_le_div_iff₀ hpos (by norm_num)]
            rw [div_le_iff₀ hdR] at h4
            linarith
          calc 1 / ‖η - 1‖ ^ 3 = 1 / ‖η - 1‖ * (‖η - 1‖ ^ 2)⁻¹ := by field_simp
            _ ≤ (d : ℝ) / 4 * (‖η - 1‖ ^ 2)⁻¹ := by gcongr
      _ = (d : ℝ) / 4 * (((d : ℝ) ^ 2 - 1) / 12) := by
          rw [← mul_sum, sum_nontrivialRoots_inv_norm_sq hd0]
      _ ≤ (d : ℝ) ^ 3 / 48 := by nlinarith
  refine (abs_sum_mul_cubicKernel_le_fourier hd0 N c').trans ?_
  have h0 : 0 ≤ ∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3 := sum_nonneg fun _ _ => by positivity
  have h1 := cubicRowTransformMax_nonneg N c' d
  calc Real.pi ^ 2 / 3 * (∑ η ∈ nontrivialRoots d, 1 / ‖η - 1‖ ^ 3) * cubicRowTransformMax N c' d
      ≤ Real.pi ^ 2 / 3 * ((d : ℝ) ^ 3 / 48) * T₃ := by gcongr
    _ = Real.pi ^ 2 * (d : ℝ) ^ 3 * T₃ / 144 := by ring

/-- **The all-moduli law.** `|Λ_d(c')| ≤ R⁴ T d/8 + π² d² M/72 + π² d³ T₃/144`, where `T`, `T₃`
bound the twists on the unit circle and `M` bounds `S₂` at primitive roots of order `R < k ≤ d`. -/
theorem abs_kernelStatisticAll_le_of_orderSplit {d N R : ℕ} (hd : 1 ≤ d) (c' : ℕ → ℝ)
    {T T₃ M : ℝ} (hT0 : 0 ≤ T) (hT₃0 : 0 ≤ T₃) (hM0 : 0 ≤ M)
    (hT : ∀ w : ℂ, ‖w‖ = 1 → ‖rowTransform N c' w‖ ≤ T)
    (hT₃ : ∀ w : ℂ, ‖w‖ = 1 → ‖cubicRowTransform N c' w‖ ≤ T₃)
    (hM : ∀ k : ℕ, R < k → k ≤ d → ∀ w : ℂ, IsPrimitiveRoot w k → ‖rowTransform N c' w‖ ≤ M) :
    |kernelStatisticAll N c' d| ≤
      (R : ℝ) ^ 4 * T * d / 8 + Real.pi ^ 2 * (d : ℝ) ^ 2 * M / 72 +
        Real.pi ^ 2 * (d : ℝ) ^ 3 * T₃ / 144 := by
  rw [kernelStatisticAll, sum_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add (abs_quadraticLayer_le_of_orderSplit hd c' hT0 hM0 hT hM)
    (abs_cubicLayer_le hd c' hT₃0 hT₃))

end

end GaloisForLFunctions.BezoutValuationIncidence
