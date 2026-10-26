import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneLefschetzSequenceGrowsAtTheZeroWidth

/-!
# Off-line zeros are Lefschetz ratios

Over `𝔽_q` the eigenvalues of Frobenius are read off the Lefschetz numbers: `N_m − q^m − 1 =
−Σ_i α_i^m`, and an eigenvalue that dominates the others is the limit of `a_{m+1}/a_m`. Over `ℤ`
the Lefschetz sequence of a test `g` at scale `ℓ` is
`c_m = W(T_{mℓ} g, g) = Σ_τ X_τ conj X_{1−τ̄} β_τ^m` (`towerMoment`), an infinite power sum.

* **A lone eigenvalue dominates** (`tendsto_tsum_mul_pow_div_pow`, `tendsto_towerMoment_div_pow`).
  If every node of nonzero weight other than `b` has modulus at most `r < |b|`, then
  `c_m/b^m → W_b`, the Frobenius weight at `b`, with error `O((r/|b|)^m)`.
* **Each off-line zero is a ratio** (`deepSparse_exists_test_lefschetz_ratio`). For a deep-sparse
  configuration and a right zero `ρ`, the test keeping `ρ` alone among the right zeros of at least
  half its depth has, at every scale, `W_b ≠ 0`, `c_m ~ W_b e^{mℓ(ρ − ½)}`,
  `c_{m+1}/c_m → e^{ℓ(ρ − ½)}` and `|c_m| → ∞`: Weil's inequality `|c_m| ≤ c_0` fails at every
  large `m`.
* **Two primes determine the zero** (`zeta_exists_test_lefschetz_ratio`). For `ζ` the test does not
  depend on the prime, its ratios at `p` tend to `p^{ρ−½}`, and any `z` whose eigenvalues at two
  distinct primes are these limits is `ρ`: prime logarithms are independent, so there is no period.

Over `𝔽_q` the Lefschetz data of all primes determine a zero only modulo `2πi/log q`
(`TheTowersOfACurveAreItsBaseChanges`); over `ℤ` two primes determine it exactly.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. A lone eigenvalue dominates -/

/-- **A lone node dominates an infinite power sum.** If `Σ |q_τ| < ∞`, the nodes are bounded, and
every node of nonzero weight other than `b` has modulus at most `r < |b|`, then
`(Σ_τ q_τ c_τ^m)/b^m` tends to the weight of `b`. -/
theorem tendsto_tsum_mul_pow_div_pow {T : Type*} {q c : T → ℂ} (hq : Summable fun τ => ‖q τ‖)
    {M : ℝ} (hcM : ∀ τ, ‖c τ‖ ≤ M) {b : ℂ} (hb0 : b ≠ 0) {r : ℝ} (hr0 : 0 ≤ r) (hrb : r < ‖b‖)
    (hsep : ∀ τ, c τ ≠ b → q τ ≠ 0 → ‖c τ‖ ≤ r) :
    Tendsto (fun m : ℕ => (∑' τ, q τ * c τ ^ m) / b ^ m) atTop
      (𝓝 (∑' τ, if c τ = b then q τ else 0)) := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set t : ℝ := r / ‖b‖ with ht
  have ht0 : 0 ≤ t := div_nonneg hr0 hbpos.le
  have ht1 : t < 1 := (div_lt_one hbpos).mpr hrb
  have hterm : ∀ (m : ℕ) τ,
      ‖q τ * (c τ / b) ^ m - (if c τ = b then q τ else 0)‖ ≤ ‖q τ‖ * t ^ m := by
    intro m τ
    by_cases hcb : c τ = b
    · rw [if_pos hcb, hcb, div_self hb0, one_pow, mul_one, sub_self, norm_zero]
      positivity
    · rw [if_neg hcb, sub_zero, norm_mul, norm_pow, norm_div]
      by_cases hq0 : q τ = 0
      · rw [hq0, norm_zero, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right (hsep τ hcb hq0) hbpos.le) m) (norm_nonneg _)
  have hs1 : ∀ m : ℕ, Summable fun τ => q τ * (c τ / b) ^ m := fun m =>
    Summable.of_norm_bounded (hq.mul_right ((M / ‖b‖) ^ m)) fun τ => by
      rw [norm_mul, norm_pow, norm_div]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (hcM τ) hbpos.le) m) (norm_nonneg _)
  have hs2 : Summable fun τ => if c τ = b then q τ else 0 :=
    Summable.of_norm_bounded hq fun τ => by split_ifs <;> simp
  have hdiff : ∀ m : ℕ, (∑' τ, q τ * c τ ^ m) / b ^ m - ∑' τ, (if c τ = b then q τ else 0) =
      ∑' τ, (q τ * (c τ / b) ^ m - if c τ = b then q τ else 0) := by
    intro m
    rw [(hs1 m).tsum_sub hs2, ← tsum_div_const]
    congr 1
    exact tsum_congr fun τ => by rw [div_pow, mul_div_assoc]
  have hlim : Tendsto (fun m : ℕ => (∑' τ, ‖q τ‖) * t ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul (∑' τ, ‖q τ‖)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hlim
  have hs3 : Summable fun τ => ‖q τ * (c τ / b) ^ m - if c τ = b then q τ else 0‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hterm m) (hq.mul_right _)
  rw [hdiff m, ← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hs3).trans (hs3.tsum_le_tsum (hterm m) (hq.mul_right _))

/-- **A lone eigenvalue dominates the Lefschetz sequence.** If every zero of nonzero weight whose
eigenvalue is not `b` has `|β_τ| ≤ r < |b|`, then `c_m/b^m` tends to the Frobenius weight at `b`. -/
theorem tendsto_towerMoment_div_pow (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℂ}
    (hb0 : b ≠ 0) {r : ℝ} (hr0 : 0 ≤ r) (hrb : r < ‖b‖)
    (hsep : ∀ τ : Z.carrier, frobEig ℓ τ ≠ b →
      zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) ≠ 0 → ‖frobEig ℓ τ‖ ≤ r) :
    Tendsto (fun m : ℕ => towerMoment Z g ℓ m / b ^ m) atTop (𝓝 (frobWeight Z g ℓ b)) := by
  simp only [towerMoment_natCast]
  exact tendsto_tsum_mul_pow_div_pow (summable_zeroCoord_mul_reflect Z hZ hg hgc)
    (c := fun τ : Z.carrier => frobEig ℓ τ) (fun τ => by
      simpa only [Complex.norm_conj] using norm_conj_frobEig_le Z hℓ τ) hb0 hr0 hrb hsep

/-! ### 2. Each off-line zero is a ratio -/

/-- **Each off-line zero is a Lefschetz ratio.** For a deep-sparse configuration and a right zero
`ρ`, one test, keeping `ρ` alone among the right zeros of at least half its depth, has at every
scale `ℓ > 0`, with `b = e^{ℓ(ρ − ½)}`: nonzero Frobenius weight `W_b`, `c_m/b^m → W_b`,
`c_{m+1}/c_m → b`, and `|c_m| → ∞`. -/
theorem deepSparse_exists_test_lefschetz_ratio (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ρ : ℂ} (hρ : ρ ∈ rightZeros Z) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ ℓ : ℝ, 0 < ℓ →
      frobWeight Z g ℓ (frobEig ℓ ρ) ≠ 0 ∧
      Tendsto (fun m : ℕ => towerMoment Z g ℓ m / frobEig ℓ ρ ^ m) atTop
        (𝓝 (frobWeight Z g ℓ (frobEig ℓ ρ))) ∧
      Tendsto (fun m : ℕ => towerMoment Z g ℓ (m + 1 : ℕ) / towerMoment Z g ℓ m) atTop
        (𝓝 (frobEig ℓ ρ)) ∧
      Tendsto (fun m : ℕ => ‖towerMoment Z g ℓ m‖) atTop atTop := by
  set δ : ℝ := ρ.re - 1 / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith [hρ.2]
  have hσ : 1 / 2 < 1 / 2 + δ / 2 := by linarith
  obtain ⟨g, hg, hgc, hkill, hkeep⟩ :=
    exists_test_killing_deep_zeros Z hsp hσ {ρ} fun τ hτ => by
      rw [Set.mem_singleton_iff.mp hτ]; exact hρ
  refine ⟨g, hg, hgc, fun ℓ hℓ => ?_⟩
  set b := frobEig ℓ ρ with hb
  have hb0 : b ≠ 0 := frobEig_ne_zero ℓ ρ
  have hb1 : 1 < ‖b‖ := (one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2
  -- the weight at `b` is the single term of `ρ`
  have hW : frobWeight Z g ℓ b ≠ 0 := by
    refine frobWeight_ne_zero_of_single Z hρ rfl (hkeep ρ (Set.mem_singleton ρ))
      fun τ hτ hne he => ?_
    have hre : τ.re = ρ.re := re_eq_of_norm_frobEig_eq hℓ (congrArg norm he)
    exact (hkill τ ⟨hτ, by rw [hre]; exact hρ.2⟩ (by rw [hre]; linarith) hne).1
  -- every other zero of nonzero weight lies below depth `δ/2`
  have hrb : Real.exp (ℓ * (δ / 2)) < ‖b‖ := by
    rw [hb, norm_frobEig, Real.exp_lt_exp, ← hδdef]
    exact mul_lt_mul_of_pos_left (half_lt_self hδ) hℓ
  have hsep : ∀ τ : Z.carrier, frobEig ℓ τ ≠ b →
      zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) ≠ 0 →
        ‖frobEig ℓ τ‖ ≤ Real.exp (ℓ * (δ / 2)) := by
    intro τ hτb hw
    have hX : paperFT g (gammaOf τ) ≠ 0 := fun h0 => hw (by simp [zeroCoord, h0])
    rw [norm_frobEig, Real.exp_le_exp]
    refine mul_le_mul_of_nonneg_left ?_ hℓ.le
    by_contra hlt
    push Not at hlt
    have hτr : (τ : ℂ) ∈ rightZeros Z := ⟨τ.2, by linarith⟩
    have hτρ : (τ : ℂ) ≠ ρ := fun h => hτb (by rw [h])
    exact hX (hkill τ hτr (by linarith) hτρ).1
  have hu := tendsto_towerMoment_div_pow Z hZ hg hgc hℓ hb0 (Real.exp_pos _).le hrb hsep
  -- the ratio
  have hratio : ∀ m : ℕ, towerMoment Z g ℓ (m + 1 : ℕ) / towerMoment Z g ℓ m =
      b * ((towerMoment Z g ℓ (m + 1 : ℕ) / b ^ (m + 1)) / (towerMoment Z g ℓ m / b ^ m)) := by
    intro m
    by_cases hc : towerMoment Z g ℓ m = 0
    · simp [hc]
    · field_simp
      ring
  have hu1 : Tendsto (fun m : ℕ => towerMoment Z g ℓ (m + 1 : ℕ) / b ^ (m + 1)) atTop
      (𝓝 (frobWeight Z g ℓ b)) :=
    hu.comp (tendsto_add_atTop_nat 1)
  refine ⟨hW, hu, ?_, ?_⟩
  · simp only [hratio]
    have h := (hu1.div hu hW).const_mul b
    rwa [div_self hW, mul_one] at h
  · -- `|c_m| = |c_m/b^m| |b|^m` with `|c_m/b^m| → |W_b| > 0`
    have hnorm : ∀ m : ℕ, ‖towerMoment Z g ℓ m‖ = ‖towerMoment Z g ℓ m / b ^ m‖ * ‖b‖ ^ m :=
      fun m => by
        rw [norm_div, norm_pow, div_mul_cancel₀ _ (pow_ne_zero m (norm_pos_iff.mpr hb0).ne')]
    simp only [hnorm]
    exact (hu.norm).pos_mul_atTop (norm_pos_iff.mpr hW)
      (tendsto_pow_atTop_atTop_of_one_lt hb1)

/-! ### 3. `ζ`: two primes determine the zero -/

/-- At `ℓ = log p` the Frobenius eigenvalue of `ρ` is `p^{ρ − ½}`. -/
theorem frobEig_log_eq_cpow {p : ℕ} (hp : 0 < p) (ρ : ℂ) :
    frobEig (Real.log p) ρ = (p : ℂ) ^ (ρ - 1 / 2) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [frobEig, Complex.cpow_def_of_ne_zero hp0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (by positivity)]

/-- **Each off-line zero of `ζ` is a Lefschetz ratio, and two primes determine it.** For every zero
`ρ` of `ζ` right of the line there is one test `g` with, at every prime `p`,
`W(T_{p^{m+1}} g, g)/W(T_{p^m} g, g) → p^{ρ−½}` and `|W(T_{p^m} g, g)| → ∞`; and any `z` whose
eigenvalues at two distinct primes are these limits is `ρ`. -/
theorem zeta_exists_test_lefschetz_ratio {ρ : ℂ} (hρ : ρ ∈ rightZeros zetaZeroConfig) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ p : ℕ, p.Prime →
        Tendsto (fun m : ℕ => towerMoment zetaZeroConfig g (Real.log p) (m + 1 : ℕ) /
          towerMoment zetaZeroConfig g (Real.log p) m) atTop (𝓝 ((p : ℂ) ^ (ρ - 1 / 2))) ∧
        Tendsto (fun m : ℕ => ‖towerMoment zetaZeroConfig g (Real.log p) m‖) atTop atTop) ∧
      ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ∀ z : ℂ,
        Tendsto (fun m : ℕ => towerMoment zetaZeroConfig g (Real.log p) (m + 1 : ℕ) /
          towerMoment zetaZeroConfig g (Real.log p) m) atTop (𝓝 ((p : ℂ) ^ (z - 1 / 2))) →
        Tendsto (fun m : ℕ => towerMoment zetaZeroConfig g (Real.log q) (m + 1 : ℕ) /
          towerMoment zetaZeroConfig g (Real.log q) m) atTop (𝓝 ((q : ℂ) ^ (z - 1 / 2))) →
        z = ρ := by
  obtain ⟨g, hg, hgc, hlaw⟩ := deepSparse_exists_test_lefschetz_ratio _
    temperedConfig_zetaZeroConfig deepSparse_zeta hρ
  have hlaw' : ∀ p : ℕ, p.Prime →
      Tendsto (fun m : ℕ => towerMoment zetaZeroConfig g (Real.log p) (m + 1 : ℕ) /
        towerMoment zetaZeroConfig g (Real.log p) m) atTop (𝓝 ((p : ℂ) ^ (ρ - 1 / 2))) ∧
      Tendsto (fun m : ℕ => ‖towerMoment zetaZeroConfig g (Real.log p) m‖) atTop atTop :=
    fun p hp => by
      obtain ⟨-, -, h3, h4⟩ := hlaw (Real.log p) (Real.log_pos (by exact_mod_cast hp.one_lt))
      rw [frobEig_log_eq_cpow hp.pos] at h3
      exact ⟨h3, h4⟩
  refine ⟨g, hg, hgc, hlaw', fun p q hp hq hpq z hzp hzq => ?_⟩
  have ep : frobEig (Real.log p) z = frobEig (Real.log p) ρ := by
    rw [frobEig_log_eq_cpow hp.pos, frobEig_log_eq_cpow hp.pos]
    exact tendsto_nhds_unique hzp (hlaw' p hp).1
  have eqq : frobEig (Real.log q) z = frobEig (Real.log q) ρ := by
    rw [frobEig_log_eq_cpow hq.pos, frobEig_log_eq_cpow hq.pos]
    exact tendsto_nhds_unique hzq (hlaw' q hq).1
  by_contra hne
  exact hpq (subsingleton_resonantPrimes hne ⟨hp, ep⟩ ⟨hq, eqq⟩)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
