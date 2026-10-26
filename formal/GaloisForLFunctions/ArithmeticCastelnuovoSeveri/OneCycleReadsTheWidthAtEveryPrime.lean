import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneLefschetzSequenceGrowsAtTheZeroWidth
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowersOfACurveAreItsBaseChanges

/-!
# One cycle reads the zero width at every prime

`OneLefschetzSequenceGrowsAtTheZeroWidth` gives, for each prime `p`, a test whose Lefschetz sequence
`c_m^{(p)} = W(T_{p^m} g, g)` grows exactly like `p^{wm}`, `w` the zero width. Here one test serves
every prime at once.

* **Attained tops** (`tsum_ite_eq_zero_of_moments_tendsto`, `not_towerMoment_isBigO_of_top`). If a
  visible eigenvalue `b` has the largest modulus among the outer eigenvalues, then `c_m ≠ O(R^m)`
  for `R < |b|`: the Cesàro means of `c_m b^{−m}` tend to the Frobenius weight at `b`. No isolation
  of `b⁻¹` is needed, so when the top real part of the right zeros is attained one probe reads it
  at every prime, for every tempered configuration (`exists_probe_lefschetz_growth_of_top`).
* **Non-attained tops** (`exists_universal_test_growth_of_no_top`). The cofinal sequence of right
  zeros does not depend on the prime; a subsequence convergent in `∏_p ℂ` makes its folded points
  converge at every prime, and the test keeping it is the same for all primes.
* **One cycle for `ζ`** (`zeta_exists_universal_lefschetz_growth`,
  `zeta_riemannHypothesis_iff_universal_minors`). One test `g` has, at every prime `p`,
  `c_m^{(p)} = O(R^m)` (`R ≥ 1`) iff `R ≥ p^w`; RH holds iff `|c_m^{(p)}| ≤ c_0` for all `m`, at any
  single prime.
* **Curves** (`CurveDatum.curve_exists_probe_lefschetz_growth`). The top of a curve is attained, so
  at every scale one probe's Lefschetz sequence grows at the largest outer eigenvalue, although the
  zeros of a curve are not deep-sparse.
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate Classical
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  zetaZeroWidth)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Attained tops -/

/-- **Extraction of a class from null moments.** If `Σ_τ r_τ z_τ^n → 0`, with `Σ |r_τ| < ∞` and
`|z_τ| ≤ 1` wherever `r_τ ≠ 0`, the total weight at `z_τ = 1` vanishes: it is the limit of the
Cesàro means of the moments. -/
theorem tsum_ite_eq_zero_of_moments_tendsto {T : Type*} {r z : T → ℂ}
    (hr : Summable fun τ => ‖r τ‖) (hz : ∀ τ, r τ ≠ 0 → ‖z τ‖ ≤ 1)
    (hm : Tendsto (fun n : ℕ => ∑' τ, r τ * z τ ^ n) atTop (𝓝 0)) :
    ∑' τ, (if z τ = 1 then r τ else 0) = 0 := by
  have hsum : ∀ n : ℕ, Summable fun τ => r τ * z τ ^ n := fun n =>
    Summable.of_norm_bounded hr fun τ => by
      by_cases h0 : r τ = 0
      · simp [h0]
      · rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz τ h0))
  have hc : ∀ N : ℕ, ∑' τ, r τ * cesaro N (z τ) =
      ((N : ℝ)⁻¹ : ℝ) • ∑ n ∈ Finset.range N, ∑' τ, r τ * z τ ^ n := fun N => by
    have e : ∀ τ, r τ * cesaro N (z τ) =
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, r τ * z τ ^ n := fun τ => by
      rw [cesaro, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    simp only [e]
    rw [tsum_mul_left, Summable.tsum_finsetSum fun n _ => hsum n, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  have hlim0 : Tendsto (fun N : ℕ => ∑' τ, r τ * cesaro N (z τ)) atTop (𝓝 0) := by
    simp only [hc]
    exact hm.cesaro_smul
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun N τ => r τ * cesaro N (z τ)) (g := fun τ => if z τ = 1 then r τ else 0)
    (bound := fun τ => ‖r τ‖) hr (fun τ => ?_) (Eventually.of_forall fun N τ => ?_)
  · exact tendsto_nhds_unique hlim hlim0
  · by_cases hr0 : r τ = 0
    · simp only [hr0, zero_mul, ite_self]; exact tendsto_const_nhds
    · have h := (tendsto_cesaro (hz τ hr0)).const_mul (r τ)
      convert h using 2
      split_ifs <;> simp
  · by_cases hr0 : r τ = 0
    · simp [hr0]
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_cesaro_le (hz τ hr0) N)

/-- **An attained top is read by the growth.** If `b` is visible and every outer eigenvalue has
modulus at most `|b|`, the Lefschetz sequence of `g` is not `O(R^m)` for any `0 ≤ R < |b|`. -/
theorem not_towerMoment_isBigO_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℂ}
    (hb : b ∈ visibleSet Z g ℓ) (htop : ∀ ρ ∈ rightZeros Z, ‖frobEig ℓ ρ‖ ≤ ‖b‖) {R : ℝ}
    (hR : 0 ≤ R) (hRb : R < ‖b‖) :
    ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k := by
  rintro ⟨C, hC⟩
  obtain ⟨⟨ρ₀, hρ₀, rfl⟩, hvis⟩ := hb
  have hb1 : 1 < ‖frobEig ℓ ρ₀‖ := (one_lt_norm_frobEig_iff hℓ ρ₀).mpr hρ₀.2
  have hb0 : frobEig ℓ ρ₀ ≠ 0 := frobEig_ne_zero ℓ ρ₀
  have hw : Summable fun τ : Z.carrier =>
      ‖zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ))‖ :=
    summable_zeroCoord_mul_reflect Z hZ hg hgc
  have hβ : ∀ τ : Z.carrier, ‖frobEig ℓ τ / frobEig ℓ ρ₀‖ ≤ 1 := fun τ => by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hb0)]
    by_cases hτ : 1 / 2 < (τ : ℂ).re
    · exact htop τ ⟨τ.2, hτ⟩
    · rw [norm_frobEig]
      exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hℓ.le
        (by linarith [not_lt.mp hτ]))).trans hb1.le
  have hmom : ∀ n : ℕ, ∑' τ : Z.carrier,
      zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) *
        (frobEig ℓ τ / frobEig ℓ ρ₀) ^ n = towerMoment Z g ℓ n / frobEig ℓ ρ₀ ^ n := fun n => by
    rw [towerMoment_natCast, ← tsum_div_const]
    exact tsum_congr fun τ => by rw [div_pow, mul_div_assoc]
  have hq : R / ‖frobEig ℓ ρ₀‖ < 1 := (div_lt_one (by linarith)).mpr hRb
  have hlim : Tendsto (fun n : ℕ => ∑' τ : Z.carrier,
      zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) *
        (frobEig ℓ τ / frobEig ℓ ρ₀) ^ n) atTop (𝓝 0) := by
    simp only [hmom]
    have h' : Tendsto (fun n : ℕ => C * (R / ‖frobEig ℓ ρ₀‖) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq).const_mul C
    refine squeeze_zero_norm (fun n => ?_) h'
    rw [norm_div, norm_pow, div_pow, mul_div_assoc']
    exact div_le_div_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg _) n)
  have h := tsum_ite_eq_zero_of_moments_tendsto hw (fun τ _ => hβ τ) hlim
  refine hvis ((tsum_congr fun τ => ?_).trans h)
  simp only [div_eq_one_iff_eq hb0]

/-- **One probe reads an attained top at every prime.** If the real parts of the right zeros attain
their largest value at `ρ₀`, one probe has, at every prime `p`, `c_m = O(R^m)` (`R ≥ 1`) iff
`R ≥ |β_ρ|` for every right zero `ρ`. -/
theorem exists_probe_lefschetz_growth_of_top (Z : ZeroConfig) (hZ : TemperedConfig Z) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ rightZeros Z) (htop : ∀ ρ ∈ rightZeros Z, ρ.re ≤ ρ₀.re) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime → ∀ R : ℝ, 1 ≤ R →
      ((∃ C, ∀ k : ℕ, ‖towerMoment Z g (Real.log p) k‖ ≤ C * R ^ k) ↔
        ∀ ρ ∈ rightZeros Z, ‖frobEig (Real.log p) ρ‖ ≤ R) := by
  obtain ⟨s, hs⟩ := exists_probe_frobWeight_ne_zero Z hZ
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun p hp R hR => ?_⟩
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  refine ⟨fun hO ρ hρ => ?_, exists_norm_towerMoment_le Z hZ (probe_contDiff s 0)
    (probe_hasCompactSupport s 0) hℓ hR⟩
  by_contra hlt
  have hdom : ∀ ρ ∈ rightZeros Z, ‖frobEig (Real.log p) ρ‖ ≤ ‖frobEig (Real.log p) ρ₀‖ :=
    fun ρ hρ => (norm_frobEig_le_iff hℓ ρ₀ ρ).mpr (htop ρ hρ)
  exact not_towerMoment_isBigO_of_top Z hZ (probe_contDiff s 0) (probe_hasCompactSupport s 0) hℓ
    ⟨⟨ρ₀, hρ₀, rfl⟩, hs p hp _ ⟨ρ₀, hρ₀, rfl⟩⟩ hdom (by linarith)
    ((not_le.mp hlt).trans_le (hdom ρ hρ)) hO

/-- **One probe reads an attained top at one scale.** -/
theorem exists_probe_lefschetz_growth_of_top_at (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ rightZeros Z) (htop : ∀ ρ ∈ rightZeros Z, ρ.re ≤ ρ₀.re) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ R : ℝ, 1 ≤ R →
      ((∃ C, ∀ k : ℕ, ‖towerMoment Z g ℓ k‖ ≤ C * R ^ k) ↔
        ∀ ρ ∈ rightZeros Z, ‖frobEig ℓ ρ‖ ≤ R) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s ∉ {s : ℝ | frobWeight Z (probe s 0) ℓ (frobEig ℓ ρ₀) = 0} := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real
      ((countable_badModulation Z hZ hℓ ⟨ρ₀, hρ₀, rfl⟩).mono fun s _ => h s)
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun R hR =>
    ⟨fun hO ρ hρ => ?_, exists_norm_towerMoment_le Z hZ (probe_contDiff s 0)
      (probe_hasCompactSupport s 0) hℓ hR⟩⟩
  by_contra hlt
  have hdom : ∀ ρ ∈ rightZeros Z, ‖frobEig ℓ ρ‖ ≤ ‖frobEig ℓ ρ₀‖ :=
    fun ρ hρ => (norm_frobEig_le_iff hℓ ρ₀ ρ).mpr (htop ρ hρ)
  exact not_towerMoment_isBigO_of_top Z hZ (probe_contDiff s 0) (probe_hasCompactSupport s 0) hℓ
    ⟨⟨ρ₀, hρ₀, rfl⟩, hs⟩ hdom (by linarith) ((not_le.mp hlt).trans_le (hdom ρ hρ)) hO

/-! ### 2. Non-attained tops at every prime -/

/-- **A non-attained top is reached at every prime by one test.** The cofinal sequence of right
zeros is chosen once; a subsequence along which the folded points converge at every prime (a
convergent subsequence in `∏_p ℂ`) is kept by one killing test, which then has `c_m ≠ O(R^m)` at
every prime `p` for every `0 < R < |β_ρ|`. -/
theorem exists_universal_test_growth_of_no_top (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) (hne : (rightZeros Z).Nonempty)
    (hnotop : ∀ ρ ∈ rightZeros Z, ∃ ρ' ∈ rightZeros Z, ρ.re < ρ'.re) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime →
      ∀ ρ ∈ rightZeros Z, ∀ R : ℝ, 0 < R → R < ‖frobEig (Real.log p) ρ‖ →
        ¬ ∃ C, ∀ k : ℕ, ‖towerMoment Z g (Real.log p) k‖ ≤ C * R ^ k := by
  obtain ⟨ρs, hmem, hmono, hcof⟩ := exists_strictMono_cofinal_seq Z hne hnotop
  -- the folded points at all primes, as points of `∏_p ℂ`
  set X : ℕ → Nat.Primes → ℂ := fun n p => (frobEig (Real.log (p : ℕ)) (ρs n))⁻¹ with hX
  have hX1 : ∀ n, X n ∈ Set.pi Set.univ fun _ : Nat.Primes => closedBall (0 : ℂ) 1 :=
    fun n p _ => by
      have hℓ : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
      show (frobEig (Real.log (p : ℕ)) (ρs n))⁻¹ ∈ closedBall (0 : ℂ) 1
      rw [mem_closedBall_zero_iff, norm_inv]
      exact (inv_lt_one_of_one_lt₀ ((one_lt_norm_frobEig_iff hℓ _).mpr (hmem n).2)).le
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hX1
  have hmono' : StrictMono fun n => (ρs (φ n)).re := hmono.comp hφ
  have hσ : 1 / 2 < 1 / 2 + ((ρs (φ 0)).re - 1 / 2) / 2 := by linarith [(hmem (φ 0)).2]
  obtain ⟨g, hg, hgc, hkill, hkeep⟩ :=
    exists_test_killing_deep_zeros Z hsp hσ (Set.range fun n => ρs (φ n)) fun τ ⟨n, hn⟩ => by
      rw [← show ρs (φ n) = τ from hn]; exact hmem (φ n)
  refine ⟨g, hg, hgc, fun p hp ρ hρ R hR hRρ => ?_⟩
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlimp : Tendsto (fun n => (frobEig (Real.log p) (ρs (φ n)))⁻¹) atTop (𝓝 (a ⟨p, hp⟩)) :=
    tendsto_pi_nhds.mp hlim ⟨p, hp⟩
  obtain ⟨n, hn⟩ := hcof ρ hρ
  have hφn : (ρs n).re ≤ (ρs (φ n)).re := hmono.monotone (hφ.id_le n)
  exact not_towerMoment_isBigO_of_kept_seq Z hZ (ρ' := fun n => ρs (φ n)) (fun n => hmem (φ n))
    hmono' hg hgc hkill hkeep hℓ hlimp n hR
    (hRρ.trans (norm_frobEig_lt_norm_frobEig hℓ (hn.trans_le hφn)))

/-! ### 3. One cycle -/

/-- **One cycle reads the top at every prime.** For a deep-sparse configuration one `C²` compactly
supported test has, at every prime `p`, `c_m^{(p)} = O(R^m)` (`R ≥ 1`) iff `R ≥ |β_ρ|` for every
right zero `ρ`. -/
theorem deepSparse_exists_universal_lefschetz_growth (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime → ∀ R : ℝ, 1 ≤ R →
      ((∃ C, ∀ k : ℕ, ‖towerMoment Z g (Real.log p) k‖ ≤ C * R ^ k) ↔
        ∀ ρ ∈ rightZeros Z, ‖frobEig (Real.log p) ρ‖ ≤ R) := by
  rcases (rightZeros Z).eq_empty_or_nonempty with he | hne
  · refine ⟨0, contDiff_const, HasCompactSupport.zero, fun p hp R hR =>
      ⟨fun _ ρ hρ => ?_, exists_norm_towerMoment_le Z hZ contDiff_const HasCompactSupport.zero
        (Real.log_pos (by exact_mod_cast hp.one_lt)) hR⟩⟩
    rw [he] at hρ
    exact absurd hρ (Set.notMem_empty _)
  · by_cases htop : ∃ ρ₀ ∈ rightZeros Z, ∀ ρ ∈ rightZeros Z, ρ.re ≤ ρ₀.re
    · obtain ⟨ρ₀, hρ₀, htop⟩ := htop
      exact exists_probe_lefschetz_growth_of_top Z hZ hρ₀ htop
    · push Not at htop
      obtain ⟨g, hg, hgc, hlow⟩ := exists_universal_test_growth_of_no_top Z hZ hsp hne htop
      refine ⟨g, hg, hgc, fun p hp R hR => ⟨fun hO ρ hρ => ?_, exists_norm_towerMoment_le Z hZ
        hg hgc (Real.log_pos (by exact_mod_cast hp.one_lt)) hR⟩⟩
      by_contra hlt
      exact hlow p hp ρ hρ R (by linarith) (not_le.mp hlt) hO

/-- **One cycle reads the zero width of `ζ` at every prime.** One test `g` has, at every prime `p`,
`|W(T_{p^m} g, g)| = O(R^m)`, `R ≥ 1`, iff `R ≥ p^w`. -/
theorem zeta_exists_universal_lefschetz_growth :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime → ∀ R : ℝ, 1 ≤ R →
      ((∃ C, ∀ k : ℕ, ‖towerMoment zetaZeroConfig g (Real.log p) k‖ ≤ C * R ^ k) ↔
        (p : ℝ) ^ zetaZeroWidth ≤ R) := by
  obtain ⟨g, hg, hgc, hlaw⟩ := deepSparse_exists_universal_lefschetz_growth _
    temperedConfig_zetaZeroConfig deepSparse_zeta
  exact ⟨g, hg, hgc, fun p hp R hR =>
    (hlaw p hp R hR).trans (zeta_forall_norm_frobEig_le_iff hp hR)⟩

/-- **One cycle, Weil's windows, any prime.** One test `g` has, for every prime `p`: RH holds iff
`|W(T_{p^m} g, g)| ≤ W(g, g)` for every `m ≥ 0`. -/
theorem zeta_riemannHypothesis_iff_universal_minors :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ p : ℕ, p.Prime →
      (RiemannHypothesis ↔ ∀ k : ℕ, ‖towerMoment zetaZeroConfig g (Real.log p) k‖ ≤
        (towerMoment zetaZeroConfig g (Real.log p) 0).re) := by
  obtain ⟨g, hg, hgc, hlaw⟩ := deepSparse_exists_universal_lefschetz_growth _
    temperedConfig_zetaZeroConfig deepSparse_zeta
  refine ⟨g, hg, hgc, fun p hp => ?_⟩
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [← rightZeros_zeta_eq_empty_iff]
  constructor
  · exact fun hR k => norm_towerMoment_le_of_rightZeros_eq_empty _
      temperedConfig_zetaZeroConfig hg hgc _ hR k
  · intro hmin
    have hdom := (hlaw p hp 1 le_rfl).mp ⟨(towerMoment zetaZeroConfig g (Real.log p) 0).re,
      fun k => by rw [one_pow, mul_one]; exact hmin k⟩
    refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ => ?_
    exact absurd (hdom ρ hρ) (not_le.mpr ((one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2))

/-! ### 4. Curves -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- **The growth of a curve's Lefschetz sequences at every scale.** For a curve datum in the strip
and every `ℓ > 0` one probe has `c_m = O(R^m)`, `R ≥ 1`, iff `R ≥ |β_ρ|` for every right zero: the
largest outer eigenvalue `max_i |β_i|^{ℓ/log q}`. -/
theorem curve_exists_probe_lefschetz_growth {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ R : ℝ, 1 ≤ R →
      ((∃ C, ∀ k : ℕ, ‖towerMoment (D.curveConfig hD) g ℓ k‖ ≤ C * R ^ k) ↔
        ∀ ρ ∈ rightZeros (D.curveConfig hD), ‖frobEig ℓ ρ‖ ≤ R) := by
  have hZ := D.temperedConfig_curveConfig hD
  by_cases hU : ∃ i, 1 < ‖D.β i‖
  · -- the eigenvalue of largest modulus gives the top zero
    obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => 1 < ‖D.β i‖)
      (fun i => ‖D.β i‖) (by obtain ⟨i, hi⟩ := hU; exact ⟨i, by simpa using hi⟩)
    have hi₀' : 1 < ‖D.β i₀‖ := (Finset.mem_filter.mp hi₀).2
    have hρ₀ : D.zetaZero i₀ 0 ∈ rightZeros (D.curveConfig hD) :=
      ⟨⟨⟨i₀, 0⟩, rfl⟩, (D.re_zetaZero_gt_iff i₀ 0).mpr hi₀'⟩
    refine exists_probe_lefschetz_growth_of_top_at _ hZ hρ₀ ?_ hℓ
    rintro _ ⟨⟨⟨i, k⟩, rfl⟩, hre⟩
    have hi : 1 < ‖D.β i‖ := (D.re_zetaZero_gt_iff i k).mp hre
    have hle : ‖D.β i‖ ≤ ‖D.β i₀‖ := hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    rw [D.re_zetaZero, D.re_zetaZero]
    have := Real.log_le_log (by linarith) hle
    have hl := D.log_q_pos
    have : Real.log ‖D.β i‖ / Real.log D.q ≤ Real.log ‖D.β i₀‖ / Real.log D.q :=
      div_le_div_of_nonneg_right this hl.le
    linarith
  · push Not at hU
    have he : rightZeros (D.curveConfig hD) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro _ ⟨⟨⟨i, k⟩, rfl⟩, hre⟩
      exact absurd ((D.re_zetaZero_gt_iff i k).mp hre) (not_lt.mpr (hU i))
    refine ⟨0, contDiff_const, HasCompactSupport.zero, fun R hR =>
      ⟨fun _ ρ hρ => ?_,
        exists_norm_towerMoment_le _ hZ contDiff_const HasCompactSupport.zero hℓ hR⟩⟩
    rw [he] at hρ
    exact absurd hρ (Set.notMem_empty _)

end CurveDatum

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
