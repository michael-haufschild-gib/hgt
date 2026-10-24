import GaloisForLFunctions.BezoutValuationIncidence.MinorArcSumsAtCompositeRootsOfUnity

/-!
# The dual norm at every modulus

The receiver's small-scale rows live on squarefree moduli, so the cross-scale dual norm is needed
at every modulus `d`, not only at primes. At a composite `d` the spectral law contains roots of
unity of every order `k ∣ d`; the roots of small order are the major arcs, and they carry little
weight.

* **Coprime reduction.** With `g = gcd(j, d)`, `Φ_d(jn) - (g² - 1)/12 = g² Φ_{d/g}((j/g) n)`
  (`residuePotential_mul_mul`), and `j/g` is coprime to `d/g`; so the `j`-th harmonic is
  `g² Σ_{η ∈ T_{d/g}} |η - 1|^{-2} S₂(η^{j/g})`, and `η^{j/g}` is a primitive root of the same
  order as `η`.
* **Split by order.** Roots of order `k ≤ R` number at most `R²` and have weight
  `|η - 1|^{-2} ≤ R²/16`; they contribute `≤ R⁴ T/16` with `T` the trivial bound for `S₂`. Roots of
  order `k > R` are minor arcs at denominator `k`, with total weight `≤ (d/g)²/12`.
* **Summing the harmonics** with `Σ_j gcd(j, d)²/j² ≤ 2d` gives the all-moduli law
  `|Λ_d(c')| ≤ R⁴ T d/8 + π² d² M/72 + π² d³ T₃/144` (`abs_kernelStatisticAll_le_of_orderSplit`).

At the cutoff `R = ⌊z⁶⌋`, `U = ⌊z²⌋` with `z³² ≤ d`, `d z³² ≤ Q`, the composite minor-arc laws give
`|Λ_d(c')| ≤ 11 (1 + log 2Q)⁴ (d²/Q)/z` for both actual rows `c' = μ𝟙_{(Q,2Q]}`, `(Λ - 1)𝟙_{(Q,2Q]}`.

* **Below the diagonal** (`z = Q^{δ/32}`): a power saving at every modulus `Q^δ ≤ d ≤ Q^{1-δ}`
  (`abs_kernelStatisticAll_moebius_and_centredPrime_le_rpow`), hence for the dual norm and for the
  cross-scale form with arbitrary bounded small-scale rows on all moduli
  (`crossScale_allModuli_moebius_and_centredPrime_le_rpow`).
* **Every modulus** `Q^δ ≤ d ≤ 2Q`: with `K = e^{64c√(log Q)}` the archimedean law (linear in `K`)
  covers `Q ≤ K d` and the minor-arc law at `z = K^{1/32}` covers `K d < Q`, so both rows have the
  zero-free-region saving `C (d²/Q) e^{-c√(log Q)}` uniformly
  (`exists_kernelStatisticAll_moebius_and_centredPrime_le_everyModulus`).
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

/-! ## §4. Trivial bounds for window rows -/

theorem norm_rowTransform_le_sum_abs (N : ℕ) (c' : ℕ → ℝ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖rowTransform N c' w‖ ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 2 := by
  unfold rowTransform
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
  rw [norm_mul, norm_pow, hw, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]

theorem norm_cubicRowTransform_le_sum_abs (N : ℕ) (c' : ℕ → ℝ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖cubicRowTransform N c' w‖ ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  unfold cubicRowTransform
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun n _ => ?_))
  rw [norm_mul, norm_pow, hw, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)]

/-! ## §5. The cutoff estimates -/

/-- With `z ≥ 1`, `U ≥ z²/2`, `z⁶ ≤ k`, `k z³² ≤ Q` and `L = 1 + log 2Q`:
`(log₂ 2Q + 1) √(typeIIBlockBound k U 2Q) ≤ 30 L³ Q/z`. -/
theorem log2_sqrt_typeIIBlockBound_le_cutoff {Q k U : ℕ} {z : ℝ} (hQ : 2 ≤ Q) (hz1 : 1 ≤ z)
    (hUz : z ^ 2 / 2 ≤ U) (hk : z ^ 6 ≤ k) (hkq : (k : ℝ) * z ^ 32 ≤ Q) :
    ((Nat.log 2 (2 * Q) : ℝ) + 1) * Real.sqrt (typeIIBlockBound k U (2 * Q)) ≤
      30 * (1 + Real.log (2 * Q)) ^ 3 * ((Q : ℝ) / z) := by
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  set q : ℝ := (Q : ℝ)
  have hz0 : 0 < z := by linarith
  have hz2 : 1 ≤ z ^ 2 := one_le_pow₀ hz1
  have hz26 : z ^ 2 ≤ z ^ 6 := pow_le_pow_right₀ hz1 (by norm_num)
  have hz232 : z ^ 2 ≤ z ^ 32 := pow_le_pow_right₀ hz1 (by norm_num)
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
  have hkq' : (k : ℝ) ≤ q / z ^ 32 := by rw [le_div_iff₀ (by positivity)]; exact hkq
  have hkq2 : (k : ℝ) ≤ q / z ^ 2 := hkq'.trans (div_le_div_of_nonneg_left hq0.le (by positivity) hz232)
  have hkqq : (k : ℝ) ≤ q := hkq2.trans (div_le_self hq0.le hz2)
  set L : ℝ := 1 + Real.log (2 * q) with hLdef
  have hlog2q : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hcast : ((2 * Q : ℕ) : ℝ) = 2 * q := by push_cast; ring
  have hW : rootHarmonicSum k ≤ k * L := by
    refine (rootHarmonicSum_le k).trans (mul_le_mul_of_nonneg_left ?_ hk0.le)
    have : Real.log k ≤ Real.log (2 * q) := Real.log_le_log hk0 (by linarith)
    rw [hLdef]; linarith
  have hWnn := rootHarmonicSum_nonneg k
  have hH : invSum (2 * Q) ≤ L := by
    have h := invSum_le_one_add_log (by omega : 1 ≤ 2 * Q)
    rwa [hcast] at h
  have hH0 : 0 ≤ invSum (2 * Q) := invSum_nonneg _
  have hlogtwo : (Nat.log 2 (2 * Q) : ℝ) + 1 ≤ 3 * L := by
    have h := natLog_two_add_one_le (2 * Q) (by omega)
    rwa [hcast] at h
  have hUpos : (0 : ℝ) < U := lt_of_lt_of_le (by positivity) hUz
  have a1 : (2 * q) ^ 2 / k ≤ 4 * (q ^ 2 / z ^ 2) := by
    calc (2 * q) ^ 2 / k ≤ (2 * q) ^ 2 / z ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (hz26.trans hk)
      _ = 4 * (q ^ 2 / z ^ 2) := by ring
  have a2 : (2 * q) ^ 2 / U ≤ 8 * (q ^ 2 / z ^ 2) := by
    calc (2 * q) ^ 2 / U ≤ (2 * q) ^ 2 / (z ^ 2 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hUz
      _ = 8 * (q ^ 2 / z ^ 2) := by field_simp; ring
  have a3 : (2 * q) ^ 2 * rootHarmonicSum k / (U * k) ≤ 8 * L * (q ^ 2 / z ^ 2) := by
    calc (2 * q) ^ 2 * rootHarmonicSum k / (U * k) ≤ (2 * q) ^ 2 * (k * L) / (U * k) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) (by positivity)
      _ = (2 * q) ^ 2 * L / U := by field_simp
      _ ≤ (2 * q) ^ 2 * L / (z ^ 2 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hUz
      _ = 8 * L * (q ^ 2 / z ^ 2) := by field_simp; ring
  have a4 : 2 * q * rootHarmonicSum k ≤ 2 * L * (q ^ 2 / z ^ 2) := by
    calc 2 * q * rootHarmonicSum k ≤ 2 * q * (k * L) := mul_le_mul_of_nonneg_left hW (by positivity)
      _ ≤ 2 * q * (q / z ^ 2 * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkq2 (by linarith)) (by positivity)
      _ = 2 * L * (q ^ 2 / z ^ 2) := by ring
  have hTB : typeIIBlockBound k U (2 * Q) ≤ 88 * L ^ 4 * (q ^ 2 / z ^ 2) := by
    unfold typeIIBlockBound
    rw [hcast]
    have hsum : (2 * q) ^ 2 / k + (2 * q) ^ 2 / U + (2 * q) ^ 2 * rootHarmonicSum k / (U * k) +
        2 * q * rootHarmonicSum k ≤ 22 * L * (q ^ 2 / z ^ 2) := by
      linarith [mul_le_mul_of_nonneg_right hL1 (by positivity : (0 : ℝ) ≤ q ^ 2 / z ^ 2)]
    have hH3 : 1 + invSum (2 * Q) ^ 3 ≤ 2 * L ^ 3 := by
      have : invSum (2 * Q) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hH0 hH 3
      have : 1 ≤ L ^ 3 := one_le_pow₀ hL1
      linarith
    have hs0 : 0 ≤ (2 * q) ^ 2 / k + (2 * q) ^ 2 / U + (2 * q) ^ 2 * rootHarmonicSum k / (U * k) +
        2 * q * rootHarmonicSum k := by positivity
    calc 2 * (1 + invSum (2 * Q) ^ 3) * ((2 * q) ^ 2 / k + (2 * q) ^ 2 / U +
          (2 * q) ^ 2 * rootHarmonicSum k / (U * k) + 2 * q * rootHarmonicSum k)
        ≤ 2 * (2 * L ^ 3) * (22 * L * (q ^ 2 / z ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hH3 (by norm_num)) hsum hs0 (by positivity)
      _ = 88 * L ^ 4 * (q ^ 2 / z ^ 2) := by ring
  have hsqrt : Real.sqrt (typeIIBlockBound k U (2 * Q)) ≤ 10 * L ^ 2 * (q / z) := by
    have h0 : 0 ≤ 10 * L ^ 2 * (q / z) := by positivity
    calc Real.sqrt (typeIIBlockBound k U (2 * Q)) ≤ Real.sqrt ((10 * L ^ 2 * (q / z)) ^ 2) := by
          refine Real.sqrt_le_sqrt (hTB.trans ?_)
          have : (10 * L ^ 2 * (q / z)) ^ 2 = 100 * L ^ 4 * (q ^ 2 / z ^ 2) := by ring
          rw [this]
          have : 0 ≤ L ^ 4 * (q ^ 2 / z ^ 2) := by positivity
          linarith
      _ = 10 * L ^ 2 * (q / z) := Real.sqrt_sq h0
  calc ((Nat.log 2 (2 * Q) : ℝ) + 1) * Real.sqrt (typeIIBlockBound k U (2 * Q))
      ≤ 3 * L * (10 * L ^ 2 * (q / z)) :=
        mul_le_mul hlogtwo hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = 30 * L ^ 3 * (q / z) := by ring

/-- The basic size facts of the cutoff `U ≤ z²`, `z⁶ ≤ k`, `k z³² ≤ Q`. -/
theorem cutoff_facts {Q k U : ℕ} {z : ℝ} (hQ : 2 ≤ Q) (hz1 : 1 ≤ z) (hUz2 : (U : ℝ) ≤ z ^ 2)
    (hk : z ^ 6 ≤ k) (hkq : (k : ℝ) * z ^ 32 ≤ Q) :
    (U : ℝ) ≤ Q / z ∧ (U : ℝ) * U * (2 * Q) / k ≤ 2 * (Q / z) ∧ (U : ℝ) * U ≤ Q / z ∧
      (U : ℝ) * k ≤ Q / z ∧ (k : ℝ) ≤ Q / z ∧ Real.log k ≤ Real.log (2 * Q) ∧
      Real.log U ≤ Real.log (2 * Q) := by
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hz0 : 0 < z := by linarith
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg U
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
  have hz6q : z ^ 6 ≤ Q := by
    calc z ^ 6 ≤ z ^ 6 * z ^ 32 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hz1)
      _ ≤ k * z ^ 32 := mul_le_mul_of_nonneg_right hk (by positivity)
      _ ≤ Q := hkq
  have hz3 : z ^ 3 ≤ Q := (pow_le_pow_right₀ hz1 (by norm_num)).trans hz6q
  have hz5 : z ^ 5 ≤ Q := (pow_le_pow_right₀ hz1 (by norm_num)).trans hz6q
  have hkz : (k : ℝ) * z ≤ Q := by
    calc (k : ℝ) * z ≤ k * z ^ 32 := mul_le_mul_of_nonneg_left
          (by simpa using pow_le_pow_right₀ hz1 (by norm_num : 1 ≤ 32)) hk0.le
      _ ≤ Q := hkq
  have hkz3 : (k : ℝ) * z ^ 3 ≤ Q := by
    calc (k : ℝ) * z ^ 3 ≤ k * z ^ 32 := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hz1 (by norm_num)) hk0.le
      _ ≤ Q := hkq
  have hUU : (U : ℝ) * U ≤ z ^ 4 := by
    calc (U : ℝ) * U ≤ z ^ 2 * z ^ 2 := mul_le_mul hUz2 hUz2 hU0 (by positivity)
      _ = z ^ 4 := by ring
  have hkQ : (k : ℝ) ≤ Q := (le_mul_of_one_le_right hk0.le hz1).trans hkz
  have hUQ : (U : ℝ) ≤ Q := hUz2.trans ((pow_le_pow_right₀ hz1 (by norm_num : 2 ≤ 6)).trans hz6q)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hz0]
    calc (U : ℝ) * z ≤ z ^ 2 * z := mul_le_mul_of_nonneg_right hUz2 hz0.le
      _ = z ^ 3 := by ring
      _ ≤ Q := hz3
  · rw [div_le_iff₀ hk0]
    have hz4k : z ^ 4 * z ≤ z ^ 6 := by
      calc z ^ 4 * z = z ^ 5 := by ring
        _ ≤ z ^ 6 := pow_le_pow_right₀ hz1 (by norm_num)
    calc (U : ℝ) * U * (2 * Q) ≤ z ^ 4 * (2 * Q) := mul_le_mul_of_nonneg_right hUU (by positivity)
      _ = 2 * (Q / z) * (z ^ 4 * z) := by field_simp
      _ ≤ 2 * (Q / z) * k := mul_le_mul_of_nonneg_left (hz4k.trans hk) (by positivity)
  · rw [le_div_iff₀ hz0]
    calc (U : ℝ) * U * z ≤ z ^ 4 * z := mul_le_mul_of_nonneg_right hUU hz0.le
      _ = z ^ 5 := by ring
      _ ≤ Q := hz5
  · rw [le_div_iff₀ hz0]
    calc (U : ℝ) * k * z ≤ z ^ 2 * k * z := by gcongr
      _ = k * z ^ 3 := by ring
      _ ≤ Q := hkz3
  · rw [le_div_iff₀ hz0]; exact hkz
  · exact Real.log_le_log hk0 (by linarith)
  · rcases (Nat.cast_nonneg U : (0 : ℝ) ≤ U).eq_or_lt with h | h
    · rw [← h, Real.log_zero]; exact Real.log_nonneg (by linarith)
    · exact Real.log_le_log h (by linarith)

theorem compositeMinorArcBound_mono (r U : ℕ) {M N : ℕ} (h : M ≤ N) :
    compositeMinorArcBound r U M ≤ compositeMinorArcBound r U N := by
  unfold compositeMinorArcBound
  have hlog : (Nat.log 2 M : ℝ) ≤ Nat.log 2 N := by exact_mod_cast Nat.log_mono_right h
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast h
  have hsq := Real.sqrt_le_sqrt (typeIIBlockBound_mono r U h)
  have := Real.log_natCast_nonneg r
  gcongr

theorem compositePrimeMinorArcBound_mono (r U : ℕ) {M N : ℕ} (h : M ≤ N) :
    compositePrimeMinorArcBound r U M ≤ compositePrimeMinorArcBound r U N := by
  unfold compositePrimeMinorArcBound
  have hlog : (Nat.log 2 M : ℝ) ≤ Nat.log 2 N := by exact_mod_cast Nat.log_mono_right h
  have hMN : (M : ℝ) ≤ N := by exact_mod_cast h
  have hsq := Real.sqrt_le_sqrt (typeIIBlockBound_mono r U h)
  have hlogMN := real_log_natCast_mono h
  have := Real.log_natCast_nonneg r
  have := Real.log_natCast_nonneg U
  have := Real.log_natCast_nonneg M
  have := rootHarmonicSum_nonneg r
  gcongr

/-- **The Möbius majorant at the cutoff:** `compositeMinorArcBound k U 2Q ≤ 36 L³ Q/z`. -/
theorem compositeMinorArcBound_le_cutoff {Q k U : ℕ} {z : ℝ} (hQ : 2 ≤ Q) (hz1 : 1 ≤ z)
    (hUz2 : (U : ℝ) ≤ z ^ 2) (hUz : z ^ 2 / 2 ≤ U) (hk : z ^ 6 ≤ k) (hkq : (k : ℝ) * z ^ 32 ≤ Q) :
    compositeMinorArcBound k U (2 * Q) ≤ 36 * (1 + Real.log (2 * Q)) ^ 3 * ((Q : ℝ) / z) := by
  obtain ⟨h1, h2, h3, h4, _, hlogk, _⟩ := cutoff_facts hQ hz1 hUz2 hk hkq
  have h5 := log2_sqrt_typeIIBlockBound_le_cutoff hQ hz1 hUz hk hkq
  set L := 1 + Real.log (2 * (Q : ℝ)) with hLdef
  have hlog2q : 0 ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_nonneg (by have : (2 : ℝ) ≤ Q := (by exact_mod_cast hQ); linarith)
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
  have hlogk1 : 1 + Real.log k ≤ L := by rw [hLdef]; linarith
  have hlogk0 : 0 ≤ 1 + Real.log k := by have := Real.log_natCast_nonneg k; linarith
  have hqz : (0 : ℝ) ≤ Q / z := by positivity
  have hcast : ((2 * Q : ℕ) : ℝ) = 2 * (Q : ℝ) := by push_cast; ring
  unfold compositeMinorArcBound
  rw [hcast]
  have t : (U : ℝ) * ((U : ℝ) * (2 * Q) / k + (U + k) * (1 + Real.log k)) ≤ 2 * (Q / z) +
      2 * L * (Q / z) := by
    have e : (U : ℝ) * ((U : ℝ) * (2 * Q) / k + (U + k) * (1 + Real.log k)) =
        (U : ℝ) * U * (2 * Q) / k + ((U : ℝ) * U + U * k) * (1 + Real.log k) := by ring
    rw [e]
    have : ((U : ℝ) * U + U * k) * (1 + Real.log k) ≤ (Q / z + Q / z) * L :=
      mul_le_mul (add_le_add h3 h4) hlogk1 hlogk0 (by positivity)
    linarith
  have hL3 : L ≤ L ^ 3 := le_self_pow₀ hL1 (by norm_num)
  have hL31 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  linarith [mul_le_mul_of_nonneg_right hL3 hqz, mul_le_mul_of_nonneg_right hL31 hqz]

/-- **The von Mangoldt majorant at the cutoff:** `compositePrimeMinorArcBound k U 2Q ≤ 37 L⁴ Q/z`. -/
theorem compositePrimeMinorArcBound_le_cutoff {Q k U : ℕ} {z : ℝ} (hQ : 2 ≤ Q) (hz1 : 1 ≤ z)
    (hUz2 : (U : ℝ) ≤ z ^ 2) (hUz : z ^ 2 / 2 ≤ U) (hk : z ^ 6 ≤ k) (hkq : (k : ℝ) * z ^ 32 ≤ Q) :
    compositePrimeMinorArcBound k U (2 * Q) ≤ 37 * (1 + Real.log (2 * Q)) ^ 4 * ((Q : ℝ) / z) := by
  obtain ⟨h1, h2, h3, h4, h5, hlogk, hlogU⟩ := cutoff_facts hQ hz1 hUz2 hk hkq
  have h6 := log2_sqrt_typeIIBlockBound_le_cutoff hQ hz1 hUz hk hkq
  set L := 1 + Real.log (2 * (Q : ℝ)) with hLdef
  have hlog2q : 0 ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_nonneg (by have : (2 : ℝ) ≤ Q := (by exact_mod_cast hQ); linarith)
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
  have hlogk1 : 1 + Real.log k ≤ L := by rw [hLdef]; linarith
  have hlogk0 : 0 ≤ 1 + Real.log k := by have := Real.log_natCast_nonneg k; linarith
  have hlogUL : Real.log U ≤ L := by rw [hLdef]; linarith
  have hlogU0 : 0 ≤ Real.log U := Real.log_natCast_nonneg U
  have hlog2L : Real.log (2 * (Q : ℝ)) ≤ L := by rw [hLdef]; linarith
  have hqz : (0 : ℝ) ≤ Q / z := by positivity
  have hW : rootHarmonicSum k ≤ k * L := by
    refine (rootHarmonicSum_le k).trans (mul_le_mul_of_nonneg_left hlogk1 hk0.le)
  have hcast : ((2 * Q : ℕ) : ℝ) = 2 * (Q : ℝ) := by push_cast; ring
  unfold compositePrimeMinorArcBound
  rw [hcast]
  have tA : (U : ℝ) * Real.log U ≤ L * (Q / z) := by
    calc (U : ℝ) * Real.log U ≤ (Q / z) * L := mul_le_mul h1 hlogUL hlogU0 hqz
      _ = L * (Q / z) := by ring
  have tB : (U : ℝ) * Real.log U * ((U : ℝ) * (2 * Q) / k + (U + k) * (1 + Real.log k)) ≤
      2 * L ^ 2 * (Q / z) + 2 * L ^ 2 * (Q / z) := by
    have e : (U : ℝ) * Real.log U * ((U : ℝ) * (2 * Q) / k + (U + k) * (1 + Real.log k)) =
        Real.log U * ((U : ℝ) * U * (2 * Q) / k) +
          Real.log U * (((U : ℝ) * U + U * k) * (1 + Real.log k)) := by ring
    rw [e]
    have p1 : Real.log U * ((U : ℝ) * U * (2 * Q) / k) ≤ L * (2 * (Q / z)) :=
      mul_le_mul hlogUL h2 (by positivity) (by linarith)
    have p2 : Real.log U * (((U : ℝ) * U + U * k) * (1 + Real.log k)) ≤
        L * ((Q / z + Q / z) * L) :=
      mul_le_mul hlogUL (mul_le_mul (add_le_add h3 h4) hlogk1 hlogk0 (by positivity))
        (by positivity) (by linarith)
    have hLL : L ≤ L ^ 2 := le_self_pow₀ hL1 (by norm_num)
    linarith [mul_le_mul_of_nonneg_right hLL hqz]
  have tC : 2 * Real.log (2 * (Q : ℝ)) * rootHarmonicSum k ≤ 2 * L ^ 2 * (Q / z) := by
    have := mul_le_mul hlog2L (hW.trans (mul_le_mul_of_nonneg_right h5 (by linarith)))
      (rootHarmonicSum_nonneg k) (by linarith)
    linarith
  have tD : ((Nat.log 2 (2 * Q) : ℝ) + 1) * (1 + Real.log (2 * (Q : ℝ))) *
      Real.sqrt (typeIIBlockBound k U (2 * Q)) ≤ 30 * L ^ 4 * (Q / z) := by
    calc ((Nat.log 2 (2 * Q) : ℝ) + 1) * (1 + Real.log (2 * (Q : ℝ))) *
          Real.sqrt (typeIIBlockBound k U (2 * Q))
        = L * (((Nat.log 2 (2 * Q) : ℝ) + 1) * Real.sqrt (typeIIBlockBound k U (2 * Q))) := by
          rw [hLdef]; ring
      _ ≤ L * (30 * L ^ 3 * (Q / z)) := mul_le_mul_of_nonneg_left h6 (by linarith)
      _ = 30 * L ^ 4 * (Q / z) := by ring
  have hL2 : L ≤ L ^ 4 := le_self_pow₀ hL1 (by norm_num)
  have hL24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  linarith [mul_le_mul_of_nonneg_right hL2 hqz, mul_le_mul_of_nonneg_right hL24 hqz]

/-! ## §6. The all-moduli law at the cutoff `z` -/

/-- **The all-moduli law at the cutoff.** Let `Q ≥ 2`, `z ≥ 1`, `z³² ≤ d` and `d z³² ≤ Q`. If
`‖S₂(w)‖ ≤ A/Q` and `‖S₃(w)‖ ≤ A/Q²` on the unit circle, and `‖S₂(w)‖ ≤ G/(Q z)` at every primitive
root of order `z⁶ < k ≤ d`, then `|Λ_d(c')| ≤ (A/8 + π² G/72 + π² A/144) (d²/Q)/z`. The roots of
order `≤ z⁶` are the major arcs; they are paid for by `R⁴ ≤ z²⁴ ≤ d/z`. -/
theorem abs_kernelStatisticAll_le_of_cutoff {Q d N : ℕ} (hQ : 2 ≤ Q) {z : ℝ} (hz1 : 1 ≤ z)
    (hzd : z ^ 32 ≤ d) (hdz : (d : ℝ) * z ^ 32 ≤ Q) (c' : ℕ → ℝ) {A G : ℝ} (hA : 0 ≤ A)
    (hG : 0 ≤ G) (hT : ∀ w : ℂ, ‖w‖ = 1 → ‖rowTransform N c' w‖ ≤ A / Q)
    (hT₃ : ∀ w : ℂ, ‖w‖ = 1 → ‖cubicRowTransform N c' w‖ ≤ A / (Q : ℝ) ^ 2)
    (hM : ∀ k : ℕ, z ^ 6 < k → k ≤ d → ∀ w : ℂ, IsPrimitiveRoot w k →
      ‖rowTransform N c' w‖ ≤ G / (Q * z)) :
    |kernelStatisticAll N c' d| ≤
      (A / 8 + Real.pi ^ 2 * G / 72 + Real.pi ^ 2 * A / 144) * ((d : ℝ) ^ 2 / Q / z) := by
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hz0 : 0 < z := by linarith
  have hz32 : 1 ≤ z ^ 32 := one_le_pow₀ hz1
  have hd1R : (1 : ℝ) ≤ d := hz32.trans hzd
  have hd1 : 1 ≤ d := by exact_mod_cast hd1R
  have hR : ((⌊z ^ 6⌋₊ : ℕ) : ℝ) ≤ z ^ 6 := Nat.floor_le (by positivity)
  have hM' : ∀ k : ℕ, ⌊z ^ 6⌋₊ < k → k ≤ d → ∀ w : ℂ, IsPrimitiveRoot w k →
      ‖rowTransform N c' w‖ ≤ G / (Q * z) := fun k hk hkd w hw =>
    hM k ((Nat.floor_lt (by positivity)).mp hk) hkd w hw
  have h := abs_kernelStatisticAll_le_of_orderSplit hd1 c' (div_nonneg hA hq0.le)
    (div_nonneg hA (by positivity)) (div_nonneg hG (by positivity)) hT hT₃ hM'
  refine h.trans ?_
  -- the major arcs: `R⁴ d ≤ z²⁴ d ≤ d²/z`
  have hR4 : ((⌊z ^ 6⌋₊ : ℕ) : ℝ) ^ 4 * d ≤ (d : ℝ) ^ 2 / z := by
    rw [le_div_iff₀ hz0]
    have hR4' : ((⌊z ^ 6⌋₊ : ℕ) : ℝ) ^ 4 ≤ z ^ 24 := by
      calc ((⌊z ^ 6⌋₊ : ℕ) : ℝ) ^ 4 ≤ (z ^ 6) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hR 4
        _ = z ^ 24 := by ring
    have hz25 : z ^ 25 ≤ d := (pow_le_pow_right₀ hz1 (by norm_num)).trans hzd
    calc ((⌊z ^ 6⌋₊ : ℕ) : ℝ) ^ 4 * d * z ≤ z ^ 24 * d * z := by gcongr
      _ = z ^ 25 * d := by ring
      _ ≤ (d : ℝ) * d := mul_le_mul_of_nonneg_right hz25 (by positivity)
      _ = (d : ℝ) ^ 2 := by ring
  -- the cubic layer: `d³/Q² ≤ (d²/Q)/z` since `d z ≤ Q`
  have hd3 : (d : ℝ) ^ 3 / (Q : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 / Q / z := by
    have hdzQ : (d : ℝ) * z ≤ Q :=
      (mul_le_mul_of_nonneg_left (le_self_pow₀ hz1 (by norm_num)) (by positivity)).trans hdz
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (d : ℝ) ^ 3 * (Q * z) = (d : ℝ) ^ 2 * Q * (d * z) := by ring
      _ ≤ (d : ℝ) ^ 2 * Q * Q := mul_le_mul_of_nonneg_left hdzQ (by positivity)
      _ = (d : ℝ) ^ 2 * (Q : ℝ) ^ 2 := by ring
  have t1 : ((⌊z ^ 6⌋₊ : ℕ) : ℝ) ^ 4 * (A / Q) * d / 8 ≤ A / 8 * ((d : ℝ) ^ 2 / Q / z) := by
    have := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hR4 hq0.le)
      (by positivity : (0 : ℝ) ≤ A / 8)
    calc ((⌊z ^ 6⌋₊ : ℕ) : ℝ) ^ 4 * (A / Q) * d / 8 =
          A / 8 * (((⌊z ^ 6⌋₊ : ℕ) : ℝ) ^ 4 * d / Q) := by ring
      _ ≤ A / 8 * ((d : ℝ) ^ 2 / z / Q) := this
      _ = A / 8 * ((d : ℝ) ^ 2 / Q / z) := by rw [div_right_comm]
  have t2 : Real.pi ^ 2 * (d : ℝ) ^ 2 * (G / (Q * z)) / 72 =
      Real.pi ^ 2 * G / 72 * ((d : ℝ) ^ 2 / Q / z) := by
    ring
  have t3 : Real.pi ^ 2 * (d : ℝ) ^ 3 * (A / (Q : ℝ) ^ 2) / 144 ≤
      Real.pi ^ 2 * A / 144 * ((d : ℝ) ^ 2 / Q / z) := by
    calc Real.pi ^ 2 * (d : ℝ) ^ 3 * (A / (Q : ℝ) ^ 2) / 144 =
          Real.pi ^ 2 * A / 144 * ((d : ℝ) ^ 3 / (Q : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd3 (by positivity)
  calc _ ≤ A / 8 * ((d : ℝ) ^ 2 / Q / z) + Real.pi ^ 2 * G / 72 * ((d : ℝ) ^ 2 / Q / z) +
        Real.pi ^ 2 * A / 144 * ((d : ℝ) ^ 2 / Q / z) := by linarith
    _ = _ := by ring

/-! ## §7. The actual rows at every modulus below the diagonal -/

/-- The window rows `μ𝟙_{(Q,2Q]}` and `(Λ - 1)𝟙_{(Q,2Q]}` have `Σ_n |c'(n)|/nʳ ≤ A Q/Qʳ` when
`|c'| ≤ A`. -/
theorem sum_Icc_abs_window_div_pow_le {Q N : ℕ} (hQ : 1 ≤ Q) {c' : ℕ → ℝ} {A : ℝ}
    (hsupp : ∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) (hA : ∀ n, |c' n| ≤ A) (r : ℕ) :
    ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ r ≤ A * Q / (Q : ℝ) ^ r := by
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hterm : ∀ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ r ≤
      if Q < n ∧ n ≤ 2 * Q then A / (Q : ℝ) ^ r else 0 := by
    intro n _
    by_cases h : c' n = 0
    · rw [h, abs_zero, zero_div]
      split_ifs
      exacts [div_nonneg hA0 (by positivity), le_rfl]
    · have hn := hsupp n h
      rw [if_pos hn]
      have hnQ : (Q : ℝ) ≤ n := by exact_mod_cast hn.1.le
      calc |c' n| / (n : ℝ) ^ r ≤ A / (n : ℝ) ^ r :=
            div_le_div_of_nonneg_right (hA n) (by positivity)
        _ ≤ A / (Q : ℝ) ^ r :=
            div_le_div_of_nonneg_left hA0 (by positivity) (pow_le_pow_left₀ hq0.le hnQ r)
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hcard : (((Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q)).card : ℝ) ≤ Q := by
    have hsub : (Icc 1 N).filter (fun n => Q < n ∧ n ≤ 2 * Q) ⊆ Ioc Q (2 * Q) := fun n hn => by
      simp only [mem_filter, mem_Ioc] at hn ⊢; exact hn.2
    have := card_le_card hsub
    rw [Nat.card_Ioc, show 2 * Q - Q = Q by omega] at this
    exact_mod_cast this
  calc _ ≤ (Q : ℝ) * (A / (Q : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_right hcard (div_nonneg hA0 (by positivity))
    _ = A * Q / (Q : ℝ) ^ r := by ring

/-- **The Möbius row at every modulus below the diagonal.** For `Q ≥ 2`, `z ≥ 1`, `z³² ≤ d`,
`d z³² ≤ Q` and `N ≥ 2Q`: `|Λ_d(μ𝟙_{(Q,2Q]})| ≤ 11 (1 + log 2Q)³ (d²/Q)/z`. -/
theorem abs_kernelStatisticAll_moebiusWindowRow_le_cutoff {Q d N : ℕ} (hQ : 2 ≤ Q) {z : ℝ}
    (hz1 : 1 ≤ z) (hzd : z ^ 32 ≤ d) (hdz : (d : ℝ) * z ^ 32 ≤ Q) (hQN : 2 * Q ≤ N) :
    |kernelStatisticAll N (moebiusWindowRow Q) d| ≤
      11 * (1 + Real.log (2 * Q)) ^ 3 * ((d : ℝ) ^ 2 / Q / z) := by
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hz0 : 0 < z := by linarith
  set L := 1 + Real.log (2 * (Q : ℝ)) with hLdef
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Q); rw [hLdef]; linarith
  have hz2 : 1 ≤ z ^ 2 := one_le_pow₀ hz1
  have hU1 : 1 ≤ ⌊z ^ 2⌋₊ := Nat.le_floor (by exact_mod_cast hz2)
  have hUz2 : ((⌊z ^ 2⌋₊ : ℕ) : ℝ) ≤ z ^ 2 := Nat.floor_le (by positivity)
  have hUz : z ^ 2 / 2 ≤ ((⌊z ^ 2⌋₊ : ℕ) : ℝ) := half_le_natFloor hz2
  have hsupp : ∀ n, moebiusWindowRow Q n ≠ 0 → Q < n ∧ n ≤ 2 * Q :=
    fun n h => moebiusWindowRow_ne_zero_imp h
  have hab : ∀ n, |moebiusWindowRow Q n| ≤ 1 := fun n => by
    unfold moebiusWindowRow
    split_ifs
    · unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · simp
  have hT2 : ∀ w : ℂ, ‖w‖ = 1 → ‖rowTransform N (moebiusWindowRow Q) w‖ ≤ 1 / Q := fun w hw => by
    refine (norm_rowTransform_le_sum_abs N _ hw).trans ?_
    have h := sum_Icc_abs_window_div_pow_le (N := N) (by omega : 1 ≤ Q) hsupp hab 2
    rwa [show 1 * (Q : ℝ) / (Q : ℝ) ^ 2 = 1 / Q by field_simp] at h
  have hT3 : ∀ w : ℂ, ‖w‖ = 1 →
      ‖cubicRowTransform N (moebiusWindowRow Q) w‖ ≤ 1 / (Q : ℝ) ^ 2 := fun w hw => by
    refine (norm_cubicRowTransform_le_sum_abs N _ hw).trans ?_
    have h := sum_Icc_abs_window_div_pow_le (N := N) (by omega : 1 ≤ Q) hsupp hab 3
    rwa [show 1 * (Q : ℝ) / (Q : ℝ) ^ 3 = 1 / (Q : ℝ) ^ 2 by field_simp] at h
  have hM : ∀ k : ℕ, z ^ 6 < k → k ≤ d → ∀ w : ℂ, IsPrimitiveRoot w k →
      ‖rowTransform N (moebiusWindowRow Q) w‖ ≤ 72 * L ^ 3 / (Q * z) := by
    intro k hk hkd w hw
    have hk0 : 0 < k := by
      have : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
      exact_mod_cast this
    have hkq : (k : ℝ) * z ^ 32 ≤ Q :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hkd) (by positivity)).trans hdz
    have hB := compositeMinorArcBound_le_cutoff hQ hz1 hUz2 hUz hk.le hkq
    have hB0 : 0 ≤ compositeMinorArcBound k ⌊z ^ 2⌋₊ (2 * Q) :=
      (norm_nonneg _).trans (norm_sum_moebius_mul_pow_le_of_isPrimitiveRoot hk0 hw hU1 (2 * Q))
    have h := norm_sum_moebiusWindowRow_div_pow_le Q N 2 hQN w (fun x hx =>
      (norm_sum_moebius_mul_pow_le_of_isPrimitiveRoot hk0 hw hU1 x).trans
        (compositeMinorArcBound_mono k _ hx))
    refine h.trans ?_
    calc 2 * compositeMinorArcBound k ⌊z ^ 2⌋₊ (2 * Q) / ((Q : ℝ) + 1) ^ 2
        ≤ 2 * compositeMinorArcBound k ⌊z ^ 2⌋₊ (2 * Q) / (Q : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by linarith) (by positivity)
            (pow_le_pow_left₀ hq0.le (by linarith) 2)
      _ ≤ 2 * (36 * L ^ 3 * ((Q : ℝ) / z)) / (Q : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 72 * L ^ 3 / (Q * z) := by field_simp; ring
  have h := abs_kernelStatisticAll_le_of_cutoff hQ hz1 hzd hdz (moebiusWindowRow Q) zero_le_one
    (by positivity : (0 : ℝ) ≤ 72 * L ^ 3) hT2 hT3 hM
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hpi : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
  have h1 : Real.pi ^ 2 * L ^ 3 ≤ 9.87 * L ^ 3 := mul_le_mul_of_nonneg_right hpi.le (by positivity)
  linarith

/-- **The centred prime row at every modulus below the diagonal.** For `Q ≥ 2`, `z ≥ 1`, `z³² ≤ d`,
`d z³² ≤ Q` and `N ≥ 2Q`: `|Λ_d((Λ - 1)𝟙_{(Q,2Q]})| ≤ 11 (1 + log 2Q)⁴ (d²/Q)/z`. -/
theorem abs_kernelStatisticAll_centredPrimeBlock_le_cutoff {Q d N : ℕ} (hQ : 2 ≤ Q) {z : ℝ}
    (hz1 : 1 ≤ z) (hzd : z ^ 32 ≤ d) (hdz : (d : ℝ) * z ^ 32 ≤ Q) (hQN : 2 * Q ≤ N) :
    |kernelStatisticAll N (centredPrimeBlock Q) d| ≤
      11 * (1 + Real.log (2 * Q)) ^ 4 * ((d : ℝ) ^ 2 / Q / z) := by
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hz0 : 0 < z := by linarith
  set L := 1 + Real.log (2 * (Q : ℝ)) with hLdef
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Q); rw [hLdef]; linarith
  have hz2 : 1 ≤ z ^ 2 := one_le_pow₀ hz1
  have hU1 : 1 ≤ ⌊z ^ 2⌋₊ := Nat.le_floor (by exact_mod_cast hz2)
  have hUz2 : ((⌊z ^ 2⌋₊ : ℕ) : ℝ) ≤ z ^ 2 := Nat.floor_le (by positivity)
  have hUz : z ^ 2 / 2 ≤ ((⌊z ^ 2⌋₊ : ℕ) : ℝ) := half_le_natFloor hz2
  have hsupp : ∀ n, centredPrimeBlock Q n ≠ 0 → Q < n ∧ n ≤ 2 * Q :=
    fun n h => centredPrimeBlock_ne_zero_imp h
  have hab : ∀ n, |centredPrimeBlock Q n| ≤ L := fun n =>
    (abs_centredPrimeBlock_le (by omega) n).trans (by rw [hLdef]; linarith)
  have hT2 : ∀ w : ℂ, ‖w‖ = 1 → ‖rowTransform N (centredPrimeBlock Q) w‖ ≤ L / Q := fun w hw => by
    refine (norm_rowTransform_le_sum_abs N _ hw).trans ?_
    have h := sum_Icc_abs_window_div_pow_le (N := N) (by omega : 1 ≤ Q) hsupp hab 2
    rwa [show L * (Q : ℝ) / (Q : ℝ) ^ 2 = L / Q by field_simp] at h
  have hT3 : ∀ w : ℂ, ‖w‖ = 1 →
      ‖cubicRowTransform N (centredPrimeBlock Q) w‖ ≤ L / (Q : ℝ) ^ 2 := fun w hw => by
    refine (norm_cubicRowTransform_le_sum_abs N _ hw).trans ?_
    have h := sum_Icc_abs_window_div_pow_le (N := N) (by omega : 1 ≤ Q) hsupp hab 3
    rwa [show L * (Q : ℝ) / (Q : ℝ) ^ 3 = L / (Q : ℝ) ^ 2 by field_simp] at h
  have hM : ∀ k : ℕ, z ^ 6 < k → k ≤ d → ∀ w : ℂ, IsPrimitiveRoot w k →
      ‖rowTransform N (centredPrimeBlock Q) w‖ ≤ 75 * L ^ 4 / (Q * z) := by
    intro k hk hkd w hw
    have hkR : (1 : ℝ) < k := lt_of_le_of_lt (one_le_pow₀ hz1) hk
    have hk1 : 1 < k := by exact_mod_cast hkR
    have hk0 : 0 < k := by omega
    have hkq : (k : ℝ) * z ^ 32 ≤ Q :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hkd) (by positivity)).trans hdz
    have hUk : ⌊z ^ 2⌋₊ < k := by
      have : ((⌊z ^ 2⌋₊ : ℕ) : ℝ) < k :=
        lt_of_le_of_lt (hUz2.trans (pow_le_pow_right₀ hz1 (by norm_num))) hk
      exact_mod_cast this
    have hkQz : (k : ℝ) ≤ Q / z := by
      rw [le_div_iff₀ hz0]
      calc (k : ℝ) * z ≤ k * z ^ 32 :=
            mul_le_mul_of_nonneg_left (le_self_pow₀ hz1 (by norm_num)) (by positivity)
        _ ≤ Q := hkq
    have hB := compositePrimeMinorArcBound_le_cutoff hQ hz1 hUz2 hUz hk.le hkq
    set P := compositePrimeMinorArcBound k ⌊z ^ 2⌋₊ (2 * Q)
    have hP0 : 0 ≤ P :=
      (norm_nonneg _).trans (norm_sum_vonMangoldt_mul_pow_le_of_isPrimitiveRoot hk0 hw hU1 hUk (2 * Q))
    -- the twisted partial sums of the centred window: `Λ`-sums minus a geometric sum
    have hmem : w ∈ nontrivialRoots k := (mem_nontrivialRoots hk0).mpr ⟨hw.ne_one hk1, hw.pow_eq_one⟩
    have hnorm := norm_eq_one_of_mem_nontrivialRoots hk0 hmem
    have htw : ∀ m ≤ Q, ‖∑ i ∈ range m, ((centredPrimeBlock Q (Q + 1 + i) : ℝ) : ℂ) *
        w ^ (Q + 1 + i)‖ ≤ 2 * P + (k : ℝ) / 2 := by
      intro m hm
      set S : ℕ → ℂ := fun x => ∑ n ∈ Icc 1 x, ((vonMangoldt n : ℝ) : ℂ) * w ^ n
      have hdiff : ∑ i ∈ range m, ((centredPrimeBlock Q (Q + 1 + i) : ℝ) : ℂ) * w ^ (Q + 1 + i) =
          (S (Q + m) - S Q) - w ^ Q * ∑ i ∈ range m, w ^ (i + 1) := by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, ih (by omega), Finset.sum_range_succ,
            show Q + (m + 1) = (Q + m) + 1 by ring]
          simp only [S]
          rw [sum_Icc_succ_top (by omega : 1 ≤ Q + m + 1), show Q + 1 + m = Q + m + 1 by ring,
            centredPrimeBlock, if_pos (by omega)]
          push_cast
          ring
      have hgeo : ‖w ^ Q * ∑ i ∈ range m, w ^ (i + 1)‖ ≤ (k : ℝ) / 2 := by
        have h4 := four_div_le_norm_sub_one_of_mem_nontrivialRoots hk0 hmem
        have hpos : 0 < ‖w - 1‖ :=
          lt_of_lt_of_le (div_pos (by norm_num) (by exact_mod_cast hk0)) h4
        rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]
        refine (GaloisForLFunctions.HTGeometry.norm_sum_pow_succ_le hnorm.le
          (hw.ne_one hk1) m).trans ?_
        rw [div_le_div_iff₀ hpos (by norm_num)]
        have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
        rw [div_le_iff₀ hk0'] at h4
        linarith
      have hS : ∀ x ≤ 2 * Q, ‖S x‖ ≤ P := fun x hx =>
        (norm_sum_vonMangoldt_mul_pow_le_of_isPrimitiveRoot hk0 hw hU1 hUk x).trans
          (compositePrimeMinorArcBound_mono k _ hx)
      rw [hdiff]
      calc ‖S (Q + m) - S Q - w ^ Q * ∑ i ∈ range m, w ^ (i + 1)‖
          ≤ ‖S (Q + m)‖ + ‖S Q‖ + ‖w ^ Q * ∑ i ∈ range m, w ^ (i + 1)‖ := by
            refine (norm_sub_le _ _).trans ?_
            gcongr
            exact norm_sub_le _ _
        _ ≤ P + P + (k : ℝ) / 2 :=
            add_le_add (add_le_add (hS _ (by omega)) (hS _ (by omega))) hgeo
        _ = 2 * P + (k : ℝ) / 2 := by ring
    have h := norm_sum_window_div_pow_le_of_twisted Q N 2 hQN hsupp w htw
    refine h.trans ?_
    have hqz : (0 : ℝ) ≤ Q / z := by positivity
    have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
    have hk0' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hB' : 2 * P + (k : ℝ) / 2 ≤ 75 * L ^ 4 * (Q / z) := by
      linarith [mul_le_mul_of_nonneg_right hL4 hqz]
    calc (2 * P + (k : ℝ) / 2) / ((Q : ℝ) + 1) ^ 2 ≤ (2 * P + (k : ℝ) / 2) / (Q : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by linarith) (by positivity)
            (pow_le_pow_left₀ hq0.le (by linarith) 2)
      _ ≤ 75 * L ^ 4 * (Q / z) / (Q : ℝ) ^ 2 := div_le_div_of_nonneg_right hB' (by positivity)
      _ = 75 * L ^ 4 / (Q * z) := by field_simp
  have h := abs_kernelStatisticAll_le_of_cutoff hQ hz1 hzd hdz (centredPrimeBlock Q)
    (by linarith : (0 : ℝ) ≤ L) (by positivity : (0 : ℝ) ≤ 75 * L ^ 4) hT2 hT3 hM
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hpi : Real.pi ^ 2 < 9.87 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  have hL4 : L ≤ L ^ 4 := le_self_pow₀ hL1 (by norm_num)
  have h1 : Real.pi ^ 2 * L ^ 4 ≤ 9.87 * L ^ 4 := mul_le_mul_of_nonneg_right hpi.le (by positivity)
  have h2 : Real.pi ^ 2 * L ≤ 9.87 * L := mul_le_mul_of_nonneg_right hpi.le (by linarith)
  linarith

/-- With `z = Q^{δ/32}`, a modulus `Q^δ ≤ d ≤ Q^{1-δ}` has `z ≥ 1`, `z³² ≤ d` and `d z³² ≤ Q`. -/
theorem rpow_cutoff_facts {δ : ℝ} (hδ : 0 < δ) {Q d : ℕ} (hQ : 1 ≤ Q) (hdl : (Q : ℝ) ^ δ ≤ d)
    (hdu : (d : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) :
    1 ≤ (Q : ℝ) ^ (δ / 32) ∧ ((Q : ℝ) ^ (δ / 32)) ^ 32 ≤ d ∧
      (d : ℝ) * ((Q : ℝ) ^ (δ / 32)) ^ 32 ≤ Q := by
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hz : ((Q : ℝ) ^ (δ / 32)) ^ 32 = (Q : ℝ) ^ δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
  refine ⟨Real.one_le_rpow hq1 (by positivity), by rw [hz]; exact hdl, ?_⟩
  rw [hz]
  calc (d : ℝ) * (Q : ℝ) ^ δ ≤ (Q : ℝ) ^ (1 - δ) * (Q : ℝ) ^ δ :=
        mul_le_mul_of_nonneg_right hdu (by positivity)
    _ = Q := by rw [← Real.rpow_add hq0, sub_add_cancel, Real.rpow_one]

/-- **The power saving at every modulus below the diagonal.** For `Q ≥ 2`, `δ > 0`, every modulus
`Q^δ ≤ d ≤ Q^{1-δ}` (prime or composite) and `N ≥ 2Q`, both actual rows have
`|Λ_d(c')| ≤ 11 (1 + log 2Q)⁴ (d²/Q) Q^{-δ/32}`. -/
theorem abs_kernelStatisticAll_moebius_and_centredPrime_le_rpow {δ : ℝ} (hδ : 0 < δ) {Q : ℕ}
    (hQ : 2 ≤ Q) {d : ℕ} (hdl : (Q : ℝ) ^ δ ≤ d) (hdu : (d : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) {N : ℕ}
    (hQN : 2 * Q ≤ N) :
    |kernelStatisticAll N (moebiusWindowRow Q) d| ≤
        11 * (1 + Real.log (2 * Q)) ^ 4 * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 32)) ∧
      |kernelStatisticAll N (centredPrimeBlock Q) d| ≤
        11 * (1 + Real.log (2 * Q)) ^ 4 * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 32)) := by
  obtain ⟨hz1, hzd, hdz⟩ := rpow_cutoff_facts hδ (by omega) hdl hdu
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hL1 : 1 ≤ 1 + Real.log (2 * (Q : ℝ)) := by
    have := Real.log_nonneg (by
      have : (2 : ℝ) ≤ Q := (by exact_mod_cast hQ); linarith : (1 : ℝ) ≤ 2 * Q)
    linarith
  have hz : (d : ℝ) ^ 2 / Q / (Q : ℝ) ^ (δ / 32) = (d : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 32)) := by
    rw [Real.rpow_neg hq0.le, div_eq_mul_inv]
  have hD : 0 ≤ (d : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 32)) := by positivity
  have hL34 : (1 + Real.log (2 * (Q : ℝ))) ^ 3 ≤ (1 + Real.log (2 * (Q : ℝ))) ^ 4 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  constructor
  · refine (abs_kernelStatisticAll_moebiusWindowRow_le_cutoff hQ hz1 hzd hdz hQN).trans ?_
    calc 11 * (1 + Real.log (2 * (Q : ℝ))) ^ 3 * ((d : ℝ) ^ 2 / Q / (Q : ℝ) ^ (δ / 32))
        = 11 * ((1 + Real.log (2 * (Q : ℝ))) ^ 3 * ((d : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 32)))) := by
          rw [hz]; ring
      _ ≤ 11 * ((1 + Real.log (2 * (Q : ℝ))) ^ 4 * ((d : ℝ) ^ 2 / Q * (Q : ℝ) ^ (-(δ / 32)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL34 hD) (by norm_num)
      _ = _ := by ring
  · refine (abs_kernelStatisticAll_centredPrimeBlock_le_cutoff hQ hz1 hzd hdz hQN).trans
      (le_of_eq ?_)
    rw [hz]; ring

/-! ## §8. The dual norm and the cross-scale form at all moduli -/

/-- **From the dual norm to the cross-scale form.** If `|Λ_d(c')| ≤ E d²/Q` for every `d ∈ S`, where
`S ⊆ [1, Q^{1-δ}]`, `0 ≤ δ`, and `Σ_n |c'(n)|/n⁴ ≤ A/Q³`, then every row `c` with `|c| ≤ 1`
supported on `S` has `|B + m R' + β H' - S' Σ_d (c(d)/d) m_d| ≤ (E + 6A Q^{-2δ}) Σ_{d ∈ S} d/Q`. -/
theorem abs_rowBilinear_sub_kernelMeanMain_le_of_dualNorm {δ : ℝ} (hδ : 0 ≤ δ) {Q N : ℕ}
    (hQ : 1 ≤ Q) (hQN : Q ≤ N) {S : Finset ℕ}
    (hS : ∀ d ∈ S, 1 ≤ d ∧ (d : ℝ) ≤ (Q : ℝ) ^ (1 - δ)) {c' : ℕ → ℝ} {E A : ℝ} (hA : 0 ≤ A)
    (hstat : ∀ d ∈ S, |kernelStatisticAll N c' d| ≤ E * ((d : ℝ) ^ 2 / Q))
    (hfour : ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 ≤ A / (Q : ℝ) ^ 3)
    {c : ℕ → ℝ} (hc : ∀ d, |c d| ≤ 1) (hcS : ∀ d, c d ≠ 0 → d ∈ S) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
      (E + 6 * A * (Q : ℝ) ^ (-(2 * δ))) * ∑ d ∈ S, (d : ℝ) / Q := by
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hdQ : ∀ d ∈ S, (d : ℝ) ≤ (Q : ℝ) ^ (1 - δ) := fun d hd => (hS d hd).2
  have hdQ' : ∀ d ∈ S, (d : ℝ) ≤ Q := fun d hd => (hdQ d hd).trans (by
    calc (Q : ℝ) ^ (1 - δ) ≤ (Q : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = Q := Real.rpow_one _)
  have hSI : S ⊆ Icc 1 N := fun d hd => by
    have h2 : d ≤ Q := by exact_mod_cast hdQ' d hd
    exact mem_Icc.mpr ⟨(hS d hd).1, by omega⟩
  have hzero : ∀ d ∈ Icc 1 N, d ∉ S → c d = 0 := fun d _ hd => by
    by_contra h; exact hd (hcS d h)
  have hstatsum : |∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d| ≤
      E * ∑ d ∈ S, (d : ℝ) / Q := by
    rw [← sum_subset hSI fun d hd hdS => by rw [hzero d hd hdS, zero_div, zero_mul], mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (hS d hd).1
    rw [abs_mul, abs_div, abs_of_pos hd0]
    calc |c d| / d * |kernelStatisticAll N c' d| ≤ 1 / d * (E * ((d : ℝ) ^ 2 / Q)) :=
          mul_le_mul (div_le_div_of_nonneg_right (hc d) hd0.le) (hstat d hd) (abs_nonneg _)
            (by positivity)
      _ = E * ((d : ℝ) / Q) := by field_simp
  have hcube : (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) ≤ ∑ d ∈ S, (d : ℝ) ^ 3 := by
    rw [← sum_subset hSI fun d hd hdS => by rw [hzero d hd hdS, abs_zero, zero_mul]]
    exact sum_le_sum fun d _ => by
      have := hc d
      have : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
      nlinarith [abs_nonneg (c d)]
  have hcube_le : (∑ d ∈ S, (d : ℝ) ^ 3) * (A / (Q : ℝ) ^ 3) ≤
      A * (Q : ℝ) ^ (-(2 * δ)) * ∑ d ∈ S, (d : ℝ) / Q := by
    rw [sum_mul, mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hratio : (d : ℝ) / Q ≤ (Q : ℝ) ^ (-δ) := by
      rw [div_le_iff₀ hq0]
      calc (d : ℝ) ≤ (Q : ℝ) ^ (1 - δ) := hdQ d hd
        _ = (Q : ℝ) ^ (-δ) * Q := by
            rw [sub_eq_add_neg, add_comm, Real.rpow_add hq0, Real.rpow_one]
    have hsq : ((d : ℝ) / Q) ^ 2 ≤ (Q : ℝ) ^ (-(2 * δ)) := by
      calc ((d : ℝ) / Q) ^ 2 ≤ ((Q : ℝ) ^ (-δ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hratio 2
        _ = (Q : ℝ) ^ (-(2 * δ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
    calc (d : ℝ) ^ 3 * (A / (Q : ℝ) ^ 3) = A * (((d : ℝ) / Q) ^ 2 * ((d : ℝ) / Q)) := by
          field_simp
      _ ≤ A * ((Q : ℝ) ^ (-(2 * δ)) * ((d : ℝ) / Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq (by positivity)) hA
      _ = A * (Q : ℝ) ^ (-(2 * δ)) * ((d : ℝ) / Q) := by ring
  have h6 : 6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 ≤
      6 * (∑ d ∈ S, (d : ℝ) ^ 3) * (A / (Q : ℝ) ^ 3) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcube (by norm_num)) hfour
      (sum_nonneg fun _ _ => by positivity) (by positivity)
  have hlaw := abs_rowBilinear_sub_kernelStatisticAll_le N c c'
  have key := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c')
    (∑ d ∈ Icc 1 N, c d / d * kernelStatisticAll N c' d)
  rw [add_mul]
  linarith

/-- **The dual norm and the cross-scale form of the actual rows, all moduli.** Let `Q ≥ 2`, `δ > 0`
and `S` a set of moduli in `[Q^δ, Q^{1-δ}]`, prime or composite. For `c' = μ𝟙_{(Q,2Q]}` and
`c' = (Λ - 1)𝟙_{(Q,2Q]}`, with `L = 1 + log 2Q`:
`Σ_{d ∈ S} |Λ_d(c')|/d ≤ 11 L⁴ Q^{-δ/32} Σ_{d ∈ S} d/Q`, and every row `c` with `|c| ≤ 1` supported
on `S` has `|B + m R' + β H' - S' Σ_d (c(d)/d) m_d| ≤ (11 L⁴ Q^{-δ/32} + 6L Q^{-2δ}) Σ_{d ∈ S} d/Q`. -/
theorem crossScale_allModuli_moebius_and_centredPrime_le_rpow {δ : ℝ} (hδ : 0 < δ) {Q : ℕ}
    (hQ : 2 ≤ Q) {S : Finset ℕ} (hS : ∀ d ∈ S, (Q : ℝ) ^ δ ≤ d ∧ (d : ℝ) ≤ (Q : ℝ) ^ (1 - δ))
    {N : ℕ} (hQN : 2 * Q ≤ N) :
    (∀ c' ∈ ({moebiusWindowRow Q, centredPrimeBlock Q} : Set (ℕ → ℝ)),
      ∑ d ∈ S, |kernelStatisticAll N c' d| / d ≤
          11 * (1 + Real.log (2 * Q)) ^ 4 * (Q : ℝ) ^ (-(δ / 32)) * ∑ d ∈ S, (d : ℝ) / Q ∧
      ∀ c : ℕ → ℝ, (∀ d, |c d| ≤ 1) → (∀ d, c d ≠ 0 → d ∈ S) →
        |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
            rowBeta N c * finiteHarmonicSum N c' - kernelMeanMain N c c'| ≤
          (11 * (1 + Real.log (2 * Q)) ^ 4 * (Q : ℝ) ^ (-(δ / 32)) +
            6 * (1 + Real.log (2 * Q)) * (Q : ℝ) ^ (-(2 * δ))) * ∑ d ∈ S, (d : ℝ) / Q) := by
  have hq2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hq0 : (0 : ℝ) < Q := by linarith
  have hq1 : (1 : ℝ) ≤ Q := by linarith
  set L := 1 + Real.log (2 * (Q : ℝ)) with hLdef
  have hL1 : 1 ≤ L := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Q); rw [hLdef]; linarith
  set E := 11 * L ^ 4 * (Q : ℝ) ^ (-(δ / 32))
  have hS1 : ∀ d ∈ S, 1 ≤ d ∧ (d : ℝ) ≤ (Q : ℝ) ^ (1 - δ) := fun d hd => by
    have : (1 : ℝ) ≤ d := (Real.one_le_rpow hq1 hδ.le).trans (hS d hd).1
    exact ⟨by exact_mod_cast this, (hS d hd).2⟩
  -- the two rows are bounded windows with `|c'| ≤ L`
  have hrows : ∀ c' ∈ ({moebiusWindowRow Q, centredPrimeBlock Q} : Set (ℕ → ℝ)),
      (∀ d ∈ S, |kernelStatisticAll N c' d| ≤ E * ((d : ℝ) ^ 2 / Q)) ∧
        ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 ≤ L / (Q : ℝ) ^ 3 := by
    intro c' hc'
    have hstat : ∀ d ∈ S, |kernelStatisticAll N c' d| ≤ E * ((d : ℝ) ^ 2 / Q) := by
      intro d hd
      have h := abs_kernelStatisticAll_moebius_and_centredPrime_le_rpow hδ hQ (hS d hd).1
        (hS d hd).2 hQN
      have e : 11 * L ^ 4 * ((d : ℝ) ^ 2 / Q) * (Q : ℝ) ^ (-(δ / 32)) = E * ((d : ℝ) ^ 2 / Q) := by
        simp only [E]; ring
      rcases hc' with rfl | hc'
      · exact h.1.trans (le_of_eq e)
      · rw [Set.mem_singleton_iff] at hc'; subst hc'; exact h.2.trans (le_of_eq e)
    refine ⟨hstat, ?_⟩
    have hwin : (∀ n, c' n ≠ 0 → Q < n ∧ n ≤ 2 * Q) ∧ ∀ n, |c' n| ≤ L := by
      rcases hc' with rfl | hc'
      · refine ⟨fun n h => moebiusWindowRow_ne_zero_imp h, fun n => ?_⟩
        unfold moebiusWindowRow
        split_ifs
        · have : |moebiusReal n| ≤ 1 := by
            unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          linarith
        · rw [abs_zero]; linarith
      · rw [Set.mem_singleton_iff] at hc'; subst hc'
        exact ⟨fun n h => centredPrimeBlock_ne_zero_imp h, fun n =>
          (abs_centredPrimeBlock_le (by omega) n).trans (by rw [hLdef]; linarith)⟩
    have h := sum_Icc_abs_window_div_pow_le (N := N) (by omega : 1 ≤ Q) hwin.1 hwin.2 4
    rwa [show L * (Q : ℝ) / (Q : ℝ) ^ 4 = L / (Q : ℝ) ^ 3 by field_simp] at h
  intro c' hc'
  obtain ⟨hstat, hfour⟩ := hrows c' hc'
  refine ⟨?_, fun c hc hcS => ?_⟩
  · rw [mul_sum]
    refine sum_le_sum fun d hd => ?_
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (hS1 d hd).1
    calc |kernelStatisticAll N c' d| / d ≤ E * ((d : ℝ) ^ 2 / Q) / d :=
          div_le_div_of_nonneg_right (hstat d hd) hd0.le
      _ = E * ((d : ℝ) / Q) := by field_simp
  · have h := abs_rowBilinear_sub_kernelMeanMain_le_of_dualNorm hδ.le (by omega : 1 ≤ Q)
      (by omega : Q ≤ N) hS1 (by linarith : (0 : ℝ) ≤ L) hstat hfour hc hcS
    refine h.trans (le_of_eq ?_)
    ring

/-! ## §9. Every modulus: the minor arcs meet the archimedean place -/

/-- `(2 + s)⁸ ≤ (8!/b⁸) e^{2b} e^{bs}` for `b > 0`, `s ≥ 0`. -/
theorem pow_eight_le_exp {b s : ℝ} (hb : 0 < b) (hs : 0 ≤ s) :
    (2 + s) ^ 8 ≤ 40320 / b ^ 8 * Real.exp (2 * b) * Real.exp (b * s) := by
  have h := Real.pow_div_factorial_le_exp (b * (2 + s)) (by positivity) 8
  have hf : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  have he : Real.exp (b * (2 + s)) = Real.exp (2 * b) * Real.exp (b * s) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hf, he, div_le_iff₀ (by norm_num), mul_pow] at h
  rw [show 40320 / b ^ 8 * Real.exp (2 * b) * Real.exp (b * s) =
    Real.exp (2 * b) * Real.exp (b * s) * 40320 / b ^ 8 by ring, le_div_iff₀ (by positivity)]
  linarith

/-- `e^{64bs} e^{-c's} ≤ e^{-bs}` for `0 ≤ b`, `128 b ≤ c'`, `s ≥ 0`. -/
theorem exp_mul_exp_neg_le {b c' s : ℝ} (hb : 0 ≤ b) (hc : 128 * b ≤ c') (hs : 0 ≤ s) :
    Real.exp (64 * b * s) * Real.exp (-(c' * s)) ≤ Real.exp (-(b * s)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 := mul_le_mul_of_nonneg_right hc hs
  have h2 := mul_nonneg hb hs
  linarith

/-- `e^{64b√(log Q)} ≤ Q^δ` once `Q ≥ e^{(64b/δ)²}`. -/
theorem exp_cutoff_le_rpow {b δ : ℝ} (hδ : 0 < δ) {Q : ℝ} (hQ : 1 ≤ Q)
    (hQe : Real.exp ((64 * b / δ) ^ 2) ≤ Q) :
    Real.exp (64 * b * Real.sqrt (Real.log Q)) ≤ Q ^ δ := by
  have hq0 : 0 < Q := by linarith
  have h1 : (64 * b / δ) ^ 2 ≤ Real.log Q := by
    rw [← Real.log_exp ((64 * b / δ) ^ 2)]; exact Real.log_le_log (Real.exp_pos _) hQe
  have h2 : 64 * b / δ ≤ Real.sqrt (Real.log Q) := (le_abs_self _).trans (Real.abs_le_sqrt h1)
  set s := Real.sqrt (Real.log Q) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlogQ : Real.log Q = s ^ 2 := (Real.sq_sqrt (Real.log_nonneg hQ)).symm
  rw [div_le_iff₀ hδ] at h2
  rw [Real.rpow_def_of_pos hq0, Real.exp_le_exp, hlogQ]
  have := mul_le_mul_of_nonneg_right h2 hs0
  nlinarith

/-- `(1 + log 2Q)⁴ e^{-2bs} ≤ (8!/b⁸) e^{2b} e^{-bs}` with `s = √(log Q)`, `Q ≥ 1`. -/
theorem logPow_mul_exp_neg_le {b : ℝ} (hb : 0 < b) {Q : ℝ} (hQ : 1 ≤ Q) :
    (1 + Real.log (2 * Q)) ^ 4 * Real.exp (-(2 * b * Real.sqrt (Real.log Q))) ≤
      40320 / b ^ 8 * Real.exp (2 * b) * Real.exp (-(b * Real.sqrt (Real.log Q))) := by
  have hq0 : 0 < Q := by linarith
  have hL0 : 0 ≤ 1 + Real.log (2 * Q) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Q); linarith
  set s := Real.sqrt (Real.log Q) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlogQ : Real.log Q = s ^ 2 := (Real.sq_sqrt (Real.log_nonneg hQ)).symm
  have hL : 1 + Real.log (2 * Q) ≤ (2 + s) ^ 2 := by
    rw [Real.log_mul (by norm_num) hq0.ne', hlogQ]
    have := Real.log_two_lt_d9
    nlinarith
  have hL4 : (1 + Real.log (2 * Q)) ^ 4 ≤ 40320 / b ^ 8 * Real.exp (2 * b) * Real.exp (b * s) :=
    calc (1 + Real.log (2 * Q)) ^ 4 ≤ ((2 + s) ^ 2) ^ 4 := pow_le_pow_left₀ hL0 hL 4
      _ = (2 + s) ^ 8 := by ring
      _ ≤ _ := pow_eight_le_exp hb hs0
  have he : Real.exp (b * s) * Real.exp (-(2 * b * s)) = Real.exp (-(b * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (1 + Real.log (2 * Q)) ^ 4 * Real.exp (-(2 * b * s))
      ≤ 40320 / b ^ 8 * Real.exp (2 * b) * Real.exp (b * s) * Real.exp (-(2 * b * s)) :=
        mul_le_mul_of_nonneg_right hL4 (Real.exp_pos _).le
    _ = 40320 / b ^ 8 * Real.exp (2 * b) * Real.exp (-(b * s)) := by rw [mul_assoc, he]

/-- **The minor-arc branch.** For `Q ≥ 2`, `b > 0` and a modulus with `K ≤ d`, `K d ≤ Q`,
`K = e^{64b√(log Q)}`, both actual rows have `|Λ_d(c')| ≤ 11 (8!/b⁸) e^{2b} (d²/Q) e^{-b√(log Q)}`:
the minor-arc law at the cutoff `z = K^{1/32}`. -/
theorem abs_kernelStatisticAll_le_exp_cutoff {Q d N : ℕ} (hQ : 2 ≤ Q) {b : ℝ} (hb : 0 < b)
    (hKd : Real.exp (64 * b * Real.sqrt (Real.log Q)) ≤ d)
    (hdK : (d : ℝ) * Real.exp (64 * b * Real.sqrt (Real.log Q)) ≤ Q) (hQN : 2 * Q ≤ N) :
    |kernelStatisticAll N (moebiusWindowRow Q) d| ≤
        11 * (40320 / b ^ 8 * Real.exp (2 * b)) * ((d : ℝ) ^ 2 / Q) *
          Real.exp (-(b * Real.sqrt (Real.log Q))) ∧
      |kernelStatisticAll N (centredPrimeBlock Q) d| ≤
        11 * (40320 / b ^ 8 * Real.exp (2 * b)) * ((d : ℝ) ^ 2 / Q) *
          Real.exp (-(b * Real.sqrt (Real.log Q))) := by
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hB := logPow_mul_exp_neg_le hb hq1
  have hL1 : 1 ≤ 1 + Real.log (2 * (Q : ℝ)) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Q); linarith
  have hs0 : 0 ≤ Real.sqrt (Real.log Q) := Real.sqrt_nonneg _
  have hz1 : 1 ≤ Real.exp (2 * b * Real.sqrt (Real.log Q)) := Real.one_le_exp (by positivity)
  have hz0 : 0 < Real.exp (2 * b * Real.sqrt (Real.log Q)) := Real.exp_pos _
  have hz32 : Real.exp (2 * b * Real.sqrt (Real.log Q)) ^ 32 =
      Real.exp (64 * b * Real.sqrt (Real.log Q)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hzd : Real.exp (2 * b * Real.sqrt (Real.log Q)) ^ 32 ≤ d := by rw [hz32]; exact hKd
  have hdz : (d : ℝ) * Real.exp (2 * b * Real.sqrt (Real.log Q)) ^ 32 ≤ Q := by
    rw [hz32]; exact hdK
  have hD : 0 ≤ (d : ℝ) ^ 2 / Q := by positivity
  have hfin : 11 * (1 + Real.log (2 * (Q : ℝ))) ^ 4 *
      ((d : ℝ) ^ 2 / Q / Real.exp (2 * b * Real.sqrt (Real.log Q))) ≤
      11 * (40320 / b ^ 8 * Real.exp (2 * b)) * ((d : ℝ) ^ 2 / Q) *
        Real.exp (-(b * Real.sqrt (Real.log Q))) := by
    calc 11 * (1 + Real.log (2 * (Q : ℝ))) ^ 4 *
          ((d : ℝ) ^ 2 / Q / Real.exp (2 * b * Real.sqrt (Real.log Q)))
        = 11 * ((d : ℝ) ^ 2 / Q) * ((1 + Real.log (2 * (Q : ℝ))) ^ 4 *
            Real.exp (-(2 * b * Real.sqrt (Real.log Q)))) := by
          rw [Real.exp_neg]; ring
      _ ≤ 11 * ((d : ℝ) ^ 2 / Q) * (40320 / b ^ 8 * Real.exp (2 * b) *
            Real.exp (-(b * Real.sqrt (Real.log Q)))) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hL34 : (1 + Real.log (2 * (Q : ℝ))) ^ 3 ≤ (1 + Real.log (2 * (Q : ℝ))) ^ 4 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  constructor
  · refine (abs_kernelStatisticAll_moebiusWindowRow_le_cutoff hQ hz1 hzd hdz hQN).trans
      (le_trans ?_ hfin)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL34 (by norm_num))
      (div_nonneg hD hz0.le)
  · exact (abs_kernelStatisticAll_centredPrimeBlock_le_cutoff hQ hz1 hzd hdz hQN).trans hfin

/-- **The zero-free-region saving at every modulus.** For every `δ > 0` there are `c > 0`, `C ≥ 0`
and `Q₀` such that for `Q ≥ Q₀`, every modulus `Q^δ ≤ d ≤ 2Q` (prime or composite) and every
`N ≥ 2Q`, both actual rows `μ𝟙_{(Q,2Q]}` and `(Λ - 1)𝟙_{(Q,2Q]}` have
`|Λ_d(c')| ≤ C (d²/Q) e^{-c√(log Q)}`.

With `K = e^{64c√(log Q)}`: where `Q ≤ K d` the archimedean law, linear in `K`, applies; where
`K d < Q` the minor-arc law applies at the cutoff `z = K^{1/32}`, admissible since `K ≤ Q^δ` for
large `Q`. The two regimes cover every modulus. -/
theorem exists_kernelStatisticAll_moebius_and_centredPrime_le_everyModulus {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → ∀ d : ℕ, (Q : ℝ) ^ δ ≤ d →
      d ≤ 2 * Q → ∀ N, 2 * Q ≤ N →
        |kernelStatisticAll N (moebiusWindowRow Q) d| ≤
            C * ((d : ℝ) ^ 2 / Q) * Real.exp (-(c * Real.sqrt (Real.log Q))) ∧
        |kernelStatisticAll N (centredPrimeBlock Q) d| ≤
            C * ((d : ℝ) ^ 2 / Q) * Real.exp (-(c * Real.sqrt (Real.log Q))) := by
  obtain ⟨C₁, hC₁, Q₁, h₁⟩ := exists_balanced_kernelStatisticAll_moebiusWindowRow_le
  obtain ⟨c₂, hc₂, C₂, hC₂, Q₂, h₂⟩ := exists_balanced_kernelStatisticAll_centredPrimeBlock_le
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = min (1 / 24) (c₂ / 2) / 128 := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; exact div_pos (lt_min (by norm_num) (by positivity)) (by norm_num)
  have hb1 : 128 * b ≤ 1 / 24 := by rw [hbdef]; linarith [min_le_left (1 / 24 : ℝ) (c₂ / 2)]
  have hb2 : 128 * b ≤ c₂ / 2 := by rw [hbdef]; linarith [min_le_right (1 / 24 : ℝ) (c₂ / 2)]
  obtain ⟨CM, hCMdef⟩ : ∃ CM : ℝ, CM = 11 * (40320 / b ^ 8 * Real.exp (2 * b)) := ⟨_, rfl⟩
  have hCM : 0 ≤ CM := by rw [hCMdef]; positivity
  have hCM' : CM ≤ max (max C₁ C₂) CM := le_max_right _ _
  refine ⟨b, hb, max (max C₁ C₂) CM, hCM.trans hCM',
    max (max Q₁ Q₂) (max 2 ⌈Real.exp ((64 * b / δ) ^ 2)⌉₊), fun Q hQ d hdl hd2 N hQN => ?_⟩
  have hQ12 : max Q₁ Q₂ ≤ Q := le_of_max_le_left hQ
  have hQ3 : max 2 ⌈Real.exp ((64 * b / δ) ^ 2)⌉₊ ≤ Q := le_of_max_le_right hQ
  have hQ2' : 2 ≤ Q := le_of_max_le_left hQ3
  have hq1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQe : Real.exp ((64 * b / δ) ^ 2) ≤ Q :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hQ3)
  have hKQ := exp_cutoff_le_rpow hδ hq1 hQe
  have hs0 : 0 ≤ Real.sqrt (Real.log Q) := Real.sqrt_nonneg _
  have hK1 : 1 ≤ Real.exp (64 * b * Real.sqrt (Real.log Q)) := Real.one_le_exp (by positivity)
  have hD : 0 ≤ (d : ℝ) ^ 2 / Q := by positivity
  have hd1 : 1 ≤ d := by
    have : (1 : ℝ) ≤ d := (Real.one_le_rpow hq1 hδ.le).trans hdl
    exact_mod_cast this
  have hE : 0 ≤ Real.exp (-(b * Real.sqrt (Real.log Q))) := (Real.exp_pos _).le
  by_cases hQd : (Q : ℝ) ≤ Real.exp (64 * b * Real.sqrt (Real.log Q)) * d
  · -- near the diagonal: the archimedean law with `K = e^{64bs}`
    have hfin : ∀ C' e : ℝ, 0 ≤ C' → C' ≤ max (max C₁ C₂) CM → 0 ≤ e →
        Real.exp (64 * b * Real.sqrt (Real.log Q)) * e ≤ Real.exp (-(b * Real.sqrt (Real.log Q))) →
        C' * Real.exp (64 * b * Real.sqrt (Real.log Q)) * ((d : ℝ) ^ 2 / Q) * e ≤
          max (max C₁ C₂) CM * ((d : ℝ) ^ 2 / Q) * Real.exp (-(b * Real.sqrt (Real.log Q))) := by
      intro C' e hC' hCle he hKe
      calc C' * Real.exp (64 * b * Real.sqrt (Real.log Q)) * ((d : ℝ) ^ 2 / Q) * e =
            C' * ((d : ℝ) ^ 2 / Q) * (Real.exp (64 * b * Real.sqrt (Real.log Q)) * e) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hCle hD) hKe
            (mul_nonneg (by linarith) he) (mul_nonneg (hCM.trans hCM') hD)
    have hKe1 : Real.exp (64 * b * Real.sqrt (Real.log Q)) *
        Real.exp (-(Real.sqrt (Real.log Q) / 24)) ≤ Real.exp (-(b * Real.sqrt (Real.log Q))) := by
      have h := exp_mul_exp_neg_le hb.le hb1 hs0
      rwa [show -(1 / 24 * Real.sqrt (Real.log Q)) = -(Real.sqrt (Real.log Q) / 24) by ring] at h
    constructor
    · exact (h₁ _ hK1 Q (le_of_max_le_left hQ12) d hd1 hQd hd2 N hQN).trans
        (hfin C₁ _ hC₁ ((le_max_left _ _).trans (le_max_left _ _)) (Real.exp_pos _).le hKe1)
    · exact (h₂ _ hK1 Q (le_of_max_le_right hQ12) d hd1 hQd hd2 N hQN).trans
        (hfin C₂ _ hC₂ ((le_max_right _ _).trans (le_max_left _ _)) (Real.exp_pos _).le
          (exp_mul_exp_neg_le hb.le hb2 hs0))
  · -- below the diagonal: the minor-arc law at the cutoff `z = K^{1/32}`
    push Not at hQd
    obtain ⟨h1, h2⟩ := abs_kernelStatisticAll_le_exp_cutoff hQ2' hb (hKQ.trans hdl)
      (by linarith) hQN
    rw [← hCMdef] at h1 h2
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM' hD) hE),
      h2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM' hD) hE)⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
