import GaloisForLFunctions.RHTower.LiUpperQuadraticCriterion
import GaloisForLFunctions.RHTower.LiSignBohrRecurrence
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet
import GaloisForLFunctions.RHTower.LiSignAlongSquares

/-!
# The upper Li criterion thins along Bohr-dense sets, not along recurrence sets

Li's criterion is pinned from both sides: RH holds iff `0 ≤ Re 2λ_n ≤ n² Re 2λ_1` for every `n`
(`riemannHypothesis_iff_re_xiLiPaired_le_sq_mul_one`). The lower side thins exactly along sets of
Bohr recurrence (`liThinning_iff_isBohrRecurrent`), because its failures sit at the identity phase
`nθ ≈ 0` of the top Cayley roots. The upper side fails at the phases where the dominant cosine
polynomial `P(n) = Σ_{i∈D} m_i Re(u_iⁿ)` is negative, which need not be near the identity.

**Theorem** (`liUpperThinning_of_isBohrDense`). If `A` meets every translate `n₀ + B(φ, η)` of every
Bohr neighbourhood beyond every bound (`IsBohrDense`), then along `A` every abstract Li family with
non-real Cayley roots and a root off the unit circle has `Σ m_i Re(1 − v_iⁿ) > Cn²` infinitely often,
for every `C`. For `ξ` this gives: RH holds iff `Re 2λ_n ≤ n² Re 2λ_1` for all large `n ∈ A`
(`riemannHypothesis_iff_eventually_re_xiLiPaired_le_of_isBohrDense`).

**Countermodel** (`not_liUpperThinning_squares`). The squares are not enough. For the family
`v = ±2i` the dominant phases are `±π/2`, and `j² mod 4 ∈ {0, 1}` gives `Re((±2i)^{j²}) ≥ 0`, so
the paired term `Re(2 − (2i)^{j²} − (2i)^{−j²}) ≤ 2` for every `j`. The lower criterion, by
contrast, thins along the squares for every abstract family (`liThinning_squares`, from the quadratic
Weyl-sum density of `LiSignAlongSquares`), so the squares are a set of Bohr recurrence
(`isBohrRecurrent_squares`). The two halves of Li's criterion therefore have different thinning laws
(`exists_liThinning_not_liUpperThinning`): the lower half needs recurrence to the identity, the upper
half needs density in the Bohr compactification. The natural numbers are Bohr dense
(`isBohrDense_univ`, simultaneous Dirichlet approximation).

**Progressions** (`liUpperThinning_multiples_iff`, `liThinning_multiples`). Along `sℕ` the lower
criterion always thins, while the upper one thins iff `s ≤ 2`. Along `2ℕ` the dominant phases become
`u_i²`, never `1` for non-real `u_i`, and a positive combination of non-trivial unit-root cosines is
negative somewhere (`exists_re_sum_unit_pow_neg`: zero mean, mean square at least `½Σm_i²`). For
`s ≥ 3` the root `2e^{2πi/s}` is real along `sℕ`. The general law behind all cases is
`liUpperThinning_of_returns`: negativity somewhere on `T` plus Bohr returns of `A` to `T`.

**Complete progression table** (`liThinning_progression_iff`, `liUpperThinning_progression_iff`).
Along `qk + r` the lower half thins iff `q ∣ r`; the upper half thins iff `q ∣ r` and `q ≤ 2`. Off
the residue `0` the `q` equal-weight roots `2e^{iπ(1+8j)/(4q)}` have vanishing power sums along the
class (`sum_exp_two_pi_mul_div_eq_zero`).

**For `ξ`** (`riemannHypothesis_iff_eventually_re_xiLiPaired_mul_le`). The top Cayley roots of `ξ`
have `|arg| ≤ 7/100`, so their `a`-th powers are never `1` for `a ≤ 89`. Hence RH holds iff
`Re 2λ_{ak} ≤ (ak)² Re 2λ_1` for all large `k`, for every `a ≤ 89`, although the abstract upper half
fails along `aℕ` for every `a ≥ 3`.

**Proof of the theorem.** The top layer `D` of Cayley roots is finite with modulus `R > 1`
(`abs_re_tsum_liTerm_add_dominant_le`). The unit roots `u_i = v_i/R` are non-real, so the cosine
polynomial `P` is negative at some `n₀` (`exists_card_filter_gt_and_lt`). Bohr density returns `nφ`
to within `η` of `n₀φ` (`φ_i = arg u_i`) for arbitrarily large `n ∈ A`, where `P(n) ≤ P(n₀)/2`, and
then the sum is at least `(ε/4)Rⁿ`, which beats `Cn²`.
-/

open Complex Filter Finset Topology

namespace RHTower

noncomputable section

/-- `A` meets every translate `n₀ + B(φ, η)` of every Bohr neighbourhood beyond every bound. -/
def IsBohrDense (A : Set ℕ) : Prop :=
  ∀ (k : ℕ) (φ : Fin k → ℝ) (n₀ : ℕ) (η : ℝ), 0 < η → ∀ N : ℕ, ∃ n ∈ A, N ≤ n ∧
    ∀ i, ∃ z : ℤ, |(n : ℝ) * φ i - n₀ * φ i - z * (2 * Real.pi)| < η

/-- Bohr density implies Bohr recurrence (take `n₀ = 0`). -/
theorem IsBohrDense.isBohrRecurrent {A : Set ℕ} (h : IsBohrDense A) : IsBohrRecurrent A := by
  intro k φ η hη N
  obtain ⟨n, hnA, hnN, hrec⟩ := h k φ 0 η hη N
  refine ⟨n, hnA, hnN, fun i => ?_⟩
  obtain ⟨z, hz⟩ := hrec i
  exact ⟨z, by simpa using hz⟩

/-- The upper Li thinning property: along `A`, every abstract Li family with non-real Cayley
roots and a root off the unit circle exceeds every quadratic ceiling infinitely often. -/
def LiUpperThinning (A : Set ℕ) : Prop :=
  ∀ (ι : Type) (v : ι → ℂ) (m : ι → ℝ) (M : ℝ), (∀ i, 1 ≤ m i) → (∀ i, 1 ≤ ‖v i‖) →
    (∀ i, ‖v i‖ ≤ M) → Summable (fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) →
    (∀ i, (v i).im ≠ 0) → (∃ i₀, 1 < ‖v i₀‖) →
    ∀ C : ℝ, ∃ᶠ n in atTop, n ∈ A ∧ C * (n : ℝ) ^ 2 < ∑' i, m i * (liTerm (v i) n).re


/-! ## Positive cosine sums are negative somewhere -/

/-- A unit-root lower bound for the real part of a geometric sum. -/
theorem le_re_geom_sum {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    (if z = 1 then (N : ℝ) else 0) - (if z = 1 then 0 else 2 / ‖z - 1‖) ≤
      (∑ k ∈ range N, z ^ k).re := by
  by_cases h1 : z = 1
  · subst h1; simp
  · simp only [h1, if_false, zero_sub]
    have hb := norm_geom_sum_le_of_ne_one hz h1 N
    have := Complex.abs_re_le_norm (∑ k ∈ range N, z ^ k)
    have := neg_abs_le (∑ k ∈ range N, z ^ k).re
    linarith

/-- **A positive combination of non-trivial unit-root cosines is negative somewhere.** Its mean
over `k` is `0`, while its mean square is at least `½ Σ m_i²`; a nonnegative sequence with
vanishing mean has vanishing mean square. -/
theorem exists_re_sum_unit_pow_neg {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ → ℂ) (m : κ → ℝ)
    (hw : ∀ i, ‖w i‖ = 1) (hw1 : ∀ i, w i ≠ 1) (hm : ∀ i, 0 < m i) :
    ∃ k : ℕ, ∑ i, m i * (w i ^ k).re < 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set P : ℕ → ℝ := fun k => ∑ i, m i * (w i ^ k).re with hP
  set S : ℝ := ∑ i, m i with hS
  have hS0 : 0 < S := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  set c : ℂ → ℝ := fun z => if z = 1 then 0 else 2 / ‖z - 1‖ with hc
  have hc0 : ∀ z, 0 ≤ c z := fun z => by
    simp only [hc]; split_ifs <;> positivity
  set B₁ : ℝ := ∑ i, m i * c (w i) with hB₁
  set B₂ : ℝ := ∑ i, ∑ j, m i * m j * (c (w i * w j) + c (w i * (starRingEnd ℂ) (w j)))
    with hB₂
  set Q : ℝ := ∑ i, m i ^ 2 with hQ
  have hQ0 : 0 < Q := Finset.sum_pos (fun i _ => by have := hm i; positivity)
    Finset.univ_nonempty
  -- the mean of `P`
  have hmean : ∀ N : ℕ, ∑ k ∈ range N, P k ≤ B₁ := by
    intro N
    simp only [hP]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.mul_sum, ← Complex.re_sum]
    apply mul_le_mul_of_nonneg_left _ (hm i).le
    have h := le_re_geom_sum (hw i) N
    simp only [hw1 i, if_false, zero_sub] at h
    have hb := norm_geom_sum_le_of_ne_one (hw i) (hw1 i) N
    have := Complex.re_le_norm (∑ k ∈ range N, w i ^ k)
    simp only [hc, hw1 i, if_false]
    linarith
  -- `0 ≤ P ≤ S`
  have hPle : ∀ k, P k ≤ S := by
    intro k
    simp only [hP, hS]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (w i ^ k).re ≤ 1 := by
      have := Complex.re_le_norm (w i ^ k)
      rw [norm_pow, hw i, one_pow] at this
      exact this
    nlinarith [hm i]
  have hsq_le : ∀ N : ℕ, ∑ k ∈ range N, P k ^ 2 ≤ S * B₁ := by
    intro N
    calc ∑ k ∈ range N, P k ^ 2 ≤ ∑ k ∈ range N, S * P k :=
          Finset.sum_le_sum fun k _ => by
            have := hcon k
            rw [sq]
            exact mul_le_mul_of_nonneg_right (hPle k) this
      _ = S * ∑ k ∈ range N, P k := by rw [Finset.mul_sum]
      _ ≤ S * B₁ := mul_le_mul_of_nonneg_left (hmean N) hS0.le
  -- the mean square of `P`
  have hsq_ge : ∀ N : ℕ, (N : ℝ) * Q / 2 - B₂ / 2 ≤ ∑ k ∈ range N, P k ^ 2 := by
    intro N
    have hexp : ∀ k, P k ^ 2 = ∑ i, ∑ j, m i * m j *
        ((((w i * w j) ^ k).re + ((w i * (starRingEnd ℂ) (w j)) ^ k).re) / 2) := by
      intro k
      simp only [hP]
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, mul_pow, ← map_pow]
      have := re_mul_re_eq_half_sum (w i ^ k) (w j ^ k)
      linear_combination (m i * m j) * this
    simp only [hexp]
    have hinner : ∀ i, ∑ j, ∑ k ∈ range N, m i * m j *
        ((((w i * w j) ^ k).re + ((w i * (starRingEnd ℂ) (w j)) ^ k).re) / 2) ≥
        ∑ j, m i * m j * (((if i = j then (N : ℝ) else 0)
          - (c (w i * w j) + c (w i * (starRingEnd ℂ) (w j)))) / 2) := by
      intro i
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, ← Complex.re_sum,
        ← Complex.re_sum]
      apply mul_le_mul_of_nonneg_left _ (by have := hm i; have := hm j; positivity)
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hu1 : ‖w i * w j‖ = 1 := by rw [norm_mul, hw i, hw j, one_mul]
      have hu2 : ‖w i * (starRingEnd ℂ) (w j)‖ = 1 := by
        rw [norm_mul, Complex.norm_conj, hw i, hw j, one_mul]
      have h1 := le_re_geom_sum hu1 N
      have h2 := le_re_geom_sum hu2 N
      have hz1 : (if w i * w j = 1 then (N : ℝ) else 0) ≥ 0 := by split_ifs <;> positivity
      by_cases hij : i = j
      · subst hij
        have hone : w i * (starRingEnd ℂ) (w i) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw i]; norm_num
        rw [hone] at h2 ⊢
        simp only [if_true, sub_zero] at h2 ⊢
        simp only [hc] at h1 ⊢
        simp only [if_true, add_zero]
        linarith
      · simp only [hij, if_false, zero_sub]
        simp only [hc] at h1 h2 ⊢
        have hz2 : (if w i * (starRingEnd ℂ) (w j) = 1 then (N : ℝ) else 0) ≥ 0 := by
          split_ifs <;> positivity
        linarith
    have h1 : ∑ i, ∑ j, m i * m j * (if i = j then (N : ℝ) else 0) = N * Q := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hQ,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hval : ∑ i, ∑ j, m i * m j * (((if i = j then (N : ℝ) else 0)
        - (c (w i * w j) + c (w i * (starRingEnd ℂ) (w j)))) / 2) = (N * Q - B₂) / 2 := by
      have hsplit : ∀ i j, m i * m j * (((if i = j then (N : ℝ) else 0)
          - (c (w i * w j) + c (w i * (starRingEnd ℂ) (w j)))) / 2) =
          (m i * m j * (if i = j then (N : ℝ) else 0)) / 2 -
            (m i * m j * (c (w i * w j) + c (w i * (starRingEnd ℂ) (w j)))) / 2 :=
        fun i j => by ring
      simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.sum_div]
      rw [h1, hB₂]
      ring
    have hswap : ∑ k ∈ range N, ∑ i, ∑ j, m i * m j *
        ((((w i * w j) ^ k).re + ((w i * (starRingEnd ℂ) (w j)) ^ k).re) / 2) =
        ∑ i, ∑ j, ∑ k ∈ range N, m i * m j *
        ((((w i * w j) ^ k).re + ((w i * (starRingEnd ℂ) (w j)) ^ k).re) / 2) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hswap, show (N : ℝ) * Q / 2 - B₂ / 2 = (N * Q - B₂) / 2 by ring, ← hval]
    exact Finset.sum_le_sum fun i _ => hinner i
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * (S * B₁) + B₂) / Q)
  have h1 := hsq_ge N
  have h2 := hsq_le N
  rw [div_lt_iff₀ hQ0] at hN
  nlinarith

/-! ## Returns and the general upper thinning law -/

/-- `A` returns to every Bohr neighbourhood of `n₀` beyond every bound. -/
def BohrReturnsTo (A : Set ℕ) (n₀ : ℕ) : Prop :=
  ∀ (k : ℕ) (φ : Fin k → ℝ) (η : ℝ), 0 < η → ∀ N : ℕ, ∃ n ∈ A, N ≤ n ∧
    ∀ i, ∃ z : ℤ, |(n : ℝ) * φ i - n₀ * φ i - z * (2 * Real.pi)| < η

/-- Every positive combination of non-real unit-root cosines is negative somewhere on `T`. -/
def NegativeSomewhereOn (T : Set ℕ) : Prop :=
  ∀ (κ : Type) [Fintype κ] [Nonempty κ] (u : κ → ℂ) (m : κ → ℝ), (∀ i, ‖u i‖ = 1) →
    (∀ i, (u i).im ≠ 0) → (∀ i, 0 < m i) → ∃ n₀ ∈ T, ∑ i, m i * (u i ^ n₀).re < 0

/-- **Upper violations for one family.** If the dominant cosine polynomial of a Li family is
negative at some `n₀ ∈ T` and `A` returns to every Bohr neighbourhood of every point of `T`, the paired
Li sum exceeds every quadratic ceiling infinitely often along `A`. -/
theorem frequently_quadratic_lt_re_tsum_liTerm_of_returns {A T : Set ℕ} {ι : Type*} {v : ι → ℂ}
    {m : ι → ℝ} {M : ℝ} (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) {i₀ : ι} (hlt : 1 < ‖v i₀‖)
    (hneg : ∀ (D : Finset ι) (R : ℝ), D.Nonempty → 1 < R → (∀ i, i ∈ D ↔ ‖v i‖ = R) →
      ∃ n₀ ∈ T, ∑ i ∈ D, m i * ((v i / R) ^ n₀).re < 0)
    (hA : ∀ n₀ ∈ T, BohrReturnsTo A n₀) (C : ℝ) :
    ∃ᶠ n in atTop, n ∈ A ∧ C * (n : ℝ) ^ 2 < ∑' i, m i * (liTerm (v i) n).re := by
  classical
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm i).mp i.2,
      div_self hR0.ne']
  obtain ⟨n₀, hn₀T, hn₀'⟩ := hneg D R hDne hR1 hDnorm
  have hn₀ : ∑ i : {x // x ∈ D}, m i * (u i ^ n₀).re < 0 := by
    rw [Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n₀).re)]
    exact hn₀'
  set ε : ℝ := -∑ i : {x // x ∈ D}, m i * (u i ^ n₀).re with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set S : ℝ := ∑ i : {x // x ∈ D}, m i with hS
  have hS0 : 0 < S := Finset.sum_pos (fun i _ => by linarith [hm i]) Finset.univ_nonempty
  set e := D.equivFin with he
  set φ : Fin D.card → ℝ := fun j => Complex.arg (u (e.symm j)) with hφ
  have hη : 0 < ε / (2 * S) := by positivity
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 4) (by linarith)
  have htend := tendsto_pow_const_div_const_pow_of_one_lt 2 hR1
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 / R ^ n < ε / (8 * (|C| + 1)) :=
    htend.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hsmall
  rw [Filter.frequently_atTop]
  intro N₂
  obtain ⟨n, hnA, hnN, hrec⟩ := hA n₀ hn₀T D.card φ (ε / (2 * S)) hη (max (max N₁ N₂) N₃)
  have hn₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN
  have hn₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN
  have hn₃ : N₃ ≤ n := le_trans (le_max_right _ _) hnN
  refine ⟨n, hn₂, hnA, ?_⟩
  have hclose : ∀ i : {x // x ∈ D}, (u i ^ n).re ≤ (u i ^ n₀).re + ε / (2 * S) := by
    intro i
    obtain ⟨z, hz⟩ := hrec (e i)
    have hφi : φ (e i) = Complex.arg (u i) := by simp [hφ]
    rw [hφi] at hz
    have hexp := eq_exp_arg_mul_I_of_norm_eq_one (hunit i)
    have hre : ∀ k : ℕ, (u i ^ k).re = Real.cos (k * Complex.arg (u i)) := by
      intro k
      rw [hexp, ← Complex.exp_nat_mul]
      have e1 : (k : ℂ) * ((Complex.arg (u i) : ℂ) * I) =
          (((k : ℝ) * Complex.arg (u i) : ℝ) : ℂ) * I := by push_cast; ring
      rw [e1, Complex.exp_ofReal_mul_I_re]
      congr 1
      rw [← hexp]
    rw [hre n, hre n₀]
    have hcos : Real.cos (n * Complex.arg (u i)) =
        Real.cos (n * Complex.arg (u i) - z * (2 * Real.pi)) := by
      rw [show (n : ℝ) * Complex.arg (u i) =
        (n * Complex.arg (u i) - z * (2 * Real.pi)) + (z : ℤ) * (2 * Real.pi) by ring,
        Real.cos_add_int_mul_two_pi]
      ring_nf
    rw [hcos]
    have hlip := Real.abs_cos_sub_cos_le (n * Complex.arg (u i) - z * (2 * Real.pi))
      (n₀ * Complex.arg (u i))
    have : |n * Complex.arg (u i) - z * (2 * Real.pi) - n₀ * Complex.arg (u i)| < ε / (2 * S) := by
      have : (n : ℝ) * Complex.arg (u i) - z * (2 * Real.pi) - n₀ * Complex.arg (u i) =
          (n : ℝ) * Complex.arg (u i) - n₀ * Complex.arg (u i) - z * (2 * Real.pi) := by ring
      rw [this]; exact hz
    have := (abs_le.mp (hlip.trans this.le)).2
    linarith
  have hdom : ∑ i : {x // x ∈ D}, m i * (u i ^ n).re ≤ -ε / 2 := by
    calc ∑ i : {x // x ∈ D}, m i * (u i ^ n).re
        ≤ ∑ i : {x // x ∈ D}, m i * ((u i ^ n₀).re + ε / (2 * S)) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hclose i) (by linarith [hm i])
      _ = ∑ i : {x // x ∈ D}, m i * (u i ^ n₀).re + S * (ε / (2 * S)) := by
          rw [hS, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ -ε / 2 := by
          have : S * (ε / (2 * S)) = ε / 2 := by field_simp
          linarith
  have hf : ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re :=
    Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  rw [hf] at hdom
  have hd := hN₁ n hn₁
  have hRn : (0 : ℝ) < R ^ n := pow_pos hR0 n
  have h2 := (abs_le.mp hd).1
  have hq := hN₃ n hn₃
  rw [div_lt_iff₀ hRn] at hq
  have hC : C * (n : ℝ) ^ 2 ≤ (|C| + 1) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (sq_nonneg _)
  have hq' : (|C| + 1) * (n : ℝ) ^ 2 < ε / 8 * R ^ n := by
    have := mul_lt_mul_of_pos_left hq (by positivity : (0 : ℝ) < |C| + 1)
    calc (|C| + 1) * (n : ℝ) ^ 2 < (|C| + 1) * (ε / (8 * (|C| + 1)) * R ^ n) := this
      _ = ε / 8 * R ^ n := by field_simp
  nlinarith

/-- **General upper thinning law.** If the dominant cosine polynomials are negative somewhere on
`T`, and `A` returns to every Bohr neighbourhood of every point of `T`, the upper Li criterion thins
along `A`. -/
theorem liUpperThinning_of_returns {A T : Set ℕ} (hT : NegativeSomewhereOn T)
    (hA : ∀ n₀ ∈ T, BohrReturnsTo A n₀) : LiUpperThinning A := by
  intro ι v m M hm hv hM hs hnr ⟨i₀, hlt⟩ C
  classical
  refine frequently_quadratic_lt_re_tsum_liTerm_of_returns hm hv hM hs hlt ?_ hA C
  intro D R hD hR1 hDnorm
  · haveI : Nonempty {x // x ∈ D} := ⟨⟨hD.choose, hD.choose_spec⟩⟩
    have hR0 : (0 : ℝ) < R := by linarith
    obtain ⟨n₀, hn₀T, hn₀⟩ := hT {x // x ∈ D} (fun i => v i / R) (fun i => m i)
      (fun i => by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm i).mp i.2,
          div_self hR0.ne'])
      (fun i => by
        rw [Complex.div_ofReal_im]
        exact div_ne_zero (hnr i) hR0.ne')
      (fun i => by linarith [hm i])
    refine ⟨n₀, hn₀T, ?_⟩
    rw [← Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n₀).re)]
    exact hn₀

/-- Every point of `ℕ` is a negativity point of some non-trivial cosine polynomial. -/
theorem negativeSomewhereOn_univ : NegativeSomewhereOn (Set.univ : Set ℕ) := by
  intro κ _ _ u m hu him hm
  obtain ⟨k, hk⟩ := exists_re_sum_unit_pow_neg u m hu
    (fun i h => him i (by rw [h]; simp)) hm
  exact ⟨k, Set.mem_univ _, hk⟩

/-- **Upper Li thinning along Bohr-dense sets.** -/
theorem liUpperThinning_of_isBohrDense {A : Set ℕ} (hA : IsBohrDense A) : LiUpperThinning A :=
  liUpperThinning_of_returns negativeSomewhereOn_univ fun n₀ _ k φ η hη N => hA k φ n₀ η hη N

/-! ## Arithmetic progressions through `0` -/

/-- The multiples of `s` return to every Bohr neighbourhood of every multiple of `s`. -/
theorem bohrReturnsTo_multiples {s : ℕ} (hs : 0 < s) {n₀ : ℕ} (hn₀ : s ∣ n₀) :
    BohrReturnsTo {n : ℕ | s ∣ n} n₀ := by
  intro k φ η hη N
  have hpi : 0 < 2 * Real.pi := by positivity
  obtain ⟨Q, hQ⟩ := exists_nat_gt ((s : ℝ) * (N + 1) * (2 * Real.pi) / η)
  have hQpos : 0 < Q := by
    have : (0 : ℝ) < Q := lt_of_le_of_lt (by positivity) hQ
    exact_mod_cast this
  obtain ⟨q, hq1, -, hclose⟩ := GaloisForLFunctions.HTGeometry.exists_simultaneous_dirichlet
    (fun i => φ i / (2 * Real.pi)) hQpos
  have hbig : N ≤ n₀ + s * ((N + 1) * q) := by
    have h1 : N + 1 ≤ (N + 1) * q := Nat.le_mul_of_pos_right _ hq1
    have h2 : (N + 1) * q ≤ s * ((N + 1) * q) := Nat.le_mul_of_pos_left _ hs
    omega
  refine ⟨n₀ + s * ((N + 1) * q), dvd_add hn₀ (dvd_mul_right _ _), hbig, fun i => ?_⟩
  obtain ⟨p, hp⟩ := hclose i
  refine ⟨s * (N + 1) * p, ?_⟩
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hkey : (((n₀ + s * ((N + 1) * q) : ℕ) : ℝ) * φ i - n₀ * φ i -
      ((s * (N + 1) * p : ℤ) : ℝ) * (2 * Real.pi))
      = s * (N + 1) * (2 * Real.pi) * ((q : ℝ) * (φ i / (2 * Real.pi)) - p) := by
    push_cast
    field_simp
    ring
  rw [hkey, abs_mul, abs_of_pos (by positivity)]
  have h1 : |(q : ℝ) * (φ i / (2 * Real.pi)) - p| < 1 / Q := hp
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  calc (s : ℝ) * (N + 1) * (2 * Real.pi) * |(q : ℝ) * (φ i / (2 * Real.pi)) - p|
      < s * (N + 1) * (2 * Real.pi) * (1 / Q) :=
        mul_lt_mul_of_pos_left h1 (by positivity)
    _ < η := by
        rw [mul_one_div, div_lt_iff₀ hQ0]
        rw [div_lt_iff₀ hη] at hQ
        linarith

/-- The natural numbers are Bohr dense. -/
theorem isBohrDense_univ : IsBohrDense (Set.univ : Set ℕ) := by
  intro k φ n₀ η hη N
  obtain ⟨n, -, hnN, hrec⟩ := bohrReturnsTo_multiples one_pos (one_dvd n₀) k φ η hη N
  exact ⟨n, Set.mem_univ _, hnN, hrec⟩

/-- **The lower Li criterion thins along every progression `sℕ`.** -/
theorem liThinning_multiples {s : ℕ} (hs : 0 < s) : LiThinning {n : ℕ | s ∣ n} := by
  apply liThinning_of_isBohrRecurrent
  intro k φ η hη N
  obtain ⟨n, hnA, hnN, hrec⟩ := bohrReturnsTo_multiples hs (dvd_zero s) k φ η hη N
  exact ⟨n, hnA, hnN, fun i => by obtain ⟨z, hz⟩ := hrec i; exact ⟨z, by simpa using hz⟩⟩

/-- **The upper Li criterion thins along the even numbers.** Along `2k` the dominant phases are
`u_i²`, which are never `1` for non-real `u_i`. -/
theorem liUpperThinning_multiples_of_le_two {s : ℕ} (hs : 0 < s) (hs2 : s ≤ 2) :
    LiUpperThinning {n : ℕ | s ∣ n} := by
  refine liUpperThinning_of_returns (T := {n : ℕ | s ∣ n}) ?_
    fun n₀ hn₀ => bohrReturnsTo_multiples hs hn₀
  intro κ _ _ u m hu him hm
  have hw : ∀ i, ‖u i ^ s‖ = 1 := fun i => by rw [norm_pow, hu i, one_pow]
  have hw1 : ∀ i, u i ^ s ≠ 1 := by
    intro i h
    interval_cases s
    · exact him i (by rw [pow_one] at h; rw [h]; simp)
    · have : u i = 1 ∨ u i = -1 := by
        have h' : (u i - 1) * (u i + 1) = 0 := by ring_nf; rw [h]; ring
        rcases mul_eq_zero.mp h' with h1 | h1
        · exact Or.inl (sub_eq_zero.mp h1)
        · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
      rcases this with h1 | h1 <;> exact him i (by rw [h1]; simp)
  obtain ⟨k, hk⟩ := exists_re_sum_unit_pow_neg (fun i => u i ^ s) m hw hw1 hm
  refine ⟨s * k, dvd_mul_right _ _, ?_⟩
  simpa [pow_mul] using hk

/-- **Beyond `2` the upper criterion fails along `sℕ`.** For `v = 2e^{2πi/s}` the powers `v^{sk}`
are positive reals, so the paired Li term along `sℕ` is `2 − 2ⁿ − 2⁻ⁿ ≤ 0`. -/
theorem not_liUpperThinning_multiples {s : ℕ} (hs : 3 ≤ s) :
    ¬ LiUpperThinning {n : ℕ | s ∣ n} := by
  intro h
  set v : ℂ := 2 * Complex.exp (((2 * Real.pi / s : ℝ) : ℂ) * I) with hv
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hnorm : ‖v‖ = 2 := by
    rw [hv, norm_mul, Complex.norm_exp_ofReal_mul_I]; norm_num
  have him : v.im ≠ 0 := by
    have hvim : v.im = 2 * Real.sin (2 * Real.pi / s) := by
      rw [hv, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      norm_num
    rw [hvim]
    have hlt : 2 * Real.pi / s < Real.pi := by
      rw [div_lt_iff₀ hs0]
      have : (3 : ℝ) ≤ s := by exact_mod_cast hs
      nlinarith [Real.pi_pos]
    have := Real.sin_pos_of_pos_of_lt_pi (by positivity) hlt
    positivity
  have hfreq := h Unit (fun _ => v) (fun _ => 1) 2 (fun _ => le_rfl)
    (fun _ => by rw [hnorm]; norm_num) (fun _ => by rw [hnorm]) (Summable.of_finite)
    (fun _ => him) ⟨(), by rw [hnorm]; norm_num⟩ 0
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨n, -, ⟨k, rfl⟩, hlt⟩ := hfreq 0
  rw [tsum_fintype, Fintype.sum_unique] at hlt
  simp only [one_mul, zero_mul] at hlt
  have hpow : v ^ (s * k) = ((2 ^ (s * k) : ℝ) : ℂ) := by
    rw [hv, mul_pow, ← Complex.exp_nat_mul]
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
    have : ((s * k : ℕ) : ℂ) * (((2 * Real.pi / s : ℝ) : ℂ) * I) =
        ((k : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    push_cast; ring
  have hre : (liTerm v (s * k)).re ≤ 0 := by
    rw [liTerm, inv_pow, hpow]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.inv_re, Complex.normSq_ofReal]
    have h3 : (2 : ℂ).re = 2 := by norm_num
    rw [h3]
    set X : ℝ := 2 ^ (s * k) with hX
    have h2 : (1 : ℝ) ≤ X := one_le_pow₀ (by norm_num)
    have hX0 : 0 < X := by linarith
    have h4 : X / (X * X) = 1 / X := by field_simp
    have h5 : 0 ≤ X + 1 / X - 2 := by
      have : X + 1 / X - 2 = (X - 1) ^ 2 / X := by field_simp; ring
      rw [this]; positivity
    rw [h4]
    linarith
  linarith

/-- **Thinning along `sℕ`: the two halves disagree.** For `s ≥ 1` the lower criterion always thins
along `sℕ`, while the upper one thins iff `s ≤ 2`. -/
theorem liUpperThinning_multiples_iff {s : ℕ} (hs : 0 < s) :
    LiUpperThinning {n : ℕ | s ∣ n} ↔ s ≤ 2 := by
  constructor
  · intro h
    by_contra hs2
    exact not_liUpperThinning_multiples (by omega) h
  · exact liUpperThinning_multiples_of_le_two hs

/-! ## The squares are not enough -/

theorem re_two_I_pow_sq_nonneg (j : ℕ) : 0 ≤ ((2 * I) ^ (j ^ 2)).re := by
  rcases Nat.even_or_odd j with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have : (a + a) ^ 2 = 4 * (a ^ 2) := by ring
    rw [this, pow_mul, show (2 * I) ^ 4 = 16 by rw [mul_pow, Complex.I_pow_four]; norm_num]
    rw [show (16 : ℂ) ^ a ^ 2 = ((16 ^ a ^ 2 : ℕ) : ℝ) by push_cast; ring]
    rw [Complex.ofReal_re]
    positivity
  · have : (2 * a + 1) ^ 2 = 4 * (a ^ 2 + a) + 1 := by ring
    rw [this, pow_succ, pow_mul, show (2 * I) ^ 4 = 16 by rw [mul_pow, Complex.I_pow_four]; norm_num]
    rw [show (16 : ℂ) ^ (a ^ 2 + a) = ((16 ^ (a ^ 2 + a) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
    simp

theorem re_two_I_inv_pow_sq_nonneg (j : ℕ) : 0 ≤ (((2 * I)⁻¹) ^ (j ^ 2)).re := by
  rw [inv_pow]
  have h := re_two_I_pow_sq_nonneg j
  set w := (2 * I) ^ (j ^ 2)
  rw [Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg _)

/-- **The squares do not thin the upper Li criterion.** For the one-root family `v = 2i` the
paired Li term along `j²` is at most `2`, since `j² mod 4 ∈ {0, 1}` keeps `Re((2i)^{±j²}) ≥ 0`. -/
theorem not_liUpperThinning_squares : ¬ LiUpperThinning {k : ℕ | ∃ j, k = j ^ 2} := by
  intro h
  have hfreq := h Unit (fun _ => 2 * I) (fun _ => 1) 2 (fun _ => le_rfl)
    (fun _ => by simp) (fun _ => by simp) (Summable.of_finite) (fun _ => by simp)
    ⟨(), by simp⟩ 2
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨n, hn1, ⟨j, rfl⟩, hlt⟩ := hfreq 1
  rw [tsum_fintype, Fintype.sum_unique] at hlt
  simp only [one_mul, liTerm, Complex.sub_re] at hlt
  have h1 := re_two_I_pow_sq_nonneg j
  have h2 := re_two_I_inv_pow_sq_nonneg j
  have hj : (1 : ℝ) ≤ ((j ^ 2 : ℕ) : ℝ) := by exact_mod_cast hn1
  have : (2 : ℂ).re = 2 := by norm_num
  rw [this] at hlt
  nlinarith

/-- **The squares thin the lower Li criterion** for every abstract family: along `(Tk)²` the
paired Li sum is negative for a positive proportion of `k` (`exists_density_sq_re_tsum_liTerm_neg`). -/
theorem liThinning_squares : LiThinning {k : ℕ | ∃ j, k = j ^ 2} := by
  classical
  intro ι v m M hm hv hM hs ⟨i₀, hlt⟩
  obtain ⟨T, hT, c, hc, N₀, hcount⟩ := exists_density_sq_re_tsum_liTerm_neg hm hv hM hs hlt
  rw [Filter.frequently_atTop]
  intro N₁
  obtain ⟨N, hN⟩ := exists_nat_gt ((N₁ : ℝ) / c + N₀)
  have hN₁0 : (0 : ℝ) ≤ (N₁ : ℝ) / c := by positivity
  have hNN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) < N := by linarith
    exact_mod_cast this.le
  have h1 := hcount N hNN₀
  have hbig : N₁ < ((range N).filter
      (fun k => ∑' i, m i * (liTerm (v i) ((T * k) ^ 2)).re < 0)).card := by
    have hcN : (N₁ : ℝ) < c * N := by
      have : (N₁ : ℝ) / c < N := by linarith
      rwa [div_lt_iff₀ hc, mul_comm] at this
    have : (N₁ : ℝ) < (((range N).filter
        (fun k => ∑' i, m i * (liTerm (v i) ((T * k) ^ 2)).re < 0)).card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨k, hk, hkN⟩ : ∃ k ∈ (range N).filter
      (fun k => ∑' i, m i * (liTerm (v i) ((T * k) ^ 2)).re < 0), N₁ ≤ k := by
    by_contra hno
    push Not at hno
    have hsub : (range N).filter (fun k => ∑' i, m i * (liTerm (v i) ((T * k) ^ 2)).re < 0)
        ⊆ range N₁ := fun k hk => mem_range.mpr (hno k hk)
    have := card_le_card hsub
    rw [card_range] at this
    omega
  exact ⟨(T * k) ^ 2, le_trans hkN (le_mul_sq_of_pos hT), ⟨T * k, rfl⟩, (mem_filter.mp hk).2⟩

/-- **The two halves of Li's criterion have different thinning laws.** The squares thin the
lower criterion (they are a set of Bohr recurrence) but not the upper one. -/
theorem exists_liThinning_not_liUpperThinning : ∃ A : Set ℕ, LiThinning A ∧ ¬ LiUpperThinning A :=
  ⟨_, liThinning_squares, not_liUpperThinning_squares⟩

/-- The squares are a set of Bohr recurrence. -/
theorem isBohrRecurrent_squares : IsBohrRecurrent {k : ℕ | ∃ j, k = j ^ 2} :=
  (liThinning_iff_isBohrRecurrent _).mp liThinning_squares

/-- The even numbers are not Bohr dense: they never come within `1` of the half-turn `1·π`. -/
theorem not_isBohrDense_evens : ¬ IsBohrDense {n : ℕ | 2 ∣ n} := by
  intro h
  obtain ⟨n, ⟨t, rfl⟩, -, hrec⟩ := h 1 (fun _ => Real.pi) 1 1 one_pos 0
  obtain ⟨z, hz⟩ := hrec 0
  have hkey : ((2 * t : ℕ) : ℝ) * Real.pi - (1 : ℕ) * Real.pi - z * (2 * Real.pi) =
      Real.pi * ((2 * (t - z) - 1 : ℤ) : ℝ) := by push_cast; ring
  rw [hkey, abs_mul, abs_of_pos Real.pi_pos] at hz
  have hodd : (1 : ℝ) ≤ |((2 * (t - z) - 1 : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    have : (1 : ℤ) ≤ |2 * (t - z) - 1| := by
      rcases le_or_gt (t - z : ℤ) 0 with h0 | h0
      · rw [abs_of_neg (by omega)]; omega
      · rw [abs_of_pos (by omega)]; omega
    exact_mod_cast this
  nlinarith [Real.pi_gt_three]

/-- **Bohr density is sufficient but not necessary for upper thinning.** -/
theorem exists_liUpperThinning_not_isBohrDense :
    ∃ A : Set ℕ, LiUpperThinning A ∧ ¬ IsBohrDense A :=
  ⟨_, liUpperThinning_multiples_of_le_two two_pos le_rfl, not_isBohrDense_evens⟩

/-! ## The complete progression table -/

/-- The arithmetic progression `{qk + r}`. -/
def natProgression (q r : ℕ) : Set ℕ := {n | ∃ k, n = q * k + r}

theorem liUpperThinning_mono {A B : Set ℕ} (hAB : ∀ᶠ n in atTop, n ∈ A → n ∈ B)
    (hA : LiUpperThinning A) : LiUpperThinning B := by
  intro ι v m M hm hv hM hs hnr hex C
  have h := hA ι v m M hm hv hM hs hnr hex C
  exact (h.and_eventually hAB).mono fun n hn => ⟨hn.2 hn.1.1, hn.1.2⟩

theorem liThinning_mono {A B : Set ℕ} (hAB : ∀ᶠ n in atTop, n ∈ A → n ∈ B)
    (hA : LiThinning A) : LiThinning B := by
  intro ι v m M hm hv hM hs hex
  have h := hA ι v m M hm hv hM hs hex
  exact (h.and_eventually hAB).mono fun n hn => ⟨hn.2 hn.1.1, hn.1.2⟩

/-- The tail of `qℕ` beyond `r` lies in the progression `qk + r` when `q ∣ r`. -/
theorem eventually_mem_progression_of_dvd {q r : ℕ} (hq : 0 < q) (hqr : q ∣ r) :
    ∀ᶠ n in atTop, n ∈ {n : ℕ | q ∣ n} → n ∈ natProgression q r := by
  refine eventually_atTop.mpr ⟨r, fun n hn hqn => ?_⟩
  obtain ⟨a, rfl⟩ := hqr
  obtain ⟨b, rfl⟩ := hqn
  have hab : a ≤ b := Nat.le_of_mul_le_mul_left hn hq
  exact ⟨b - a, by rw [Nat.mul_sub, Nat.sub_add_cancel (Nat.mul_le_mul_left q hab)]⟩

/-- A nontrivial sum of `q`-th roots of unity vanishes. -/
theorem sum_exp_two_pi_mul_div_eq_zero {q n : ℕ} (hq : 0 < q) (hn : ¬ q ∣ n) :
    ∑ j : Fin q, Complex.exp (2 * Real.pi * I * (j * n / q)) = 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * I * (n / q)) with hζ
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow : ∀ j : ℕ, Complex.exp (2 * Real.pi * I * (j * n / q)) = ζ ^ j := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hζq : ζ ^ q = 1 := by
    rw [← hpow q, show (2 * Real.pi * I * ((q : ℂ) * n / q)) = (n : ℂ) * (2 * Real.pi * I) by
      field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I n
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [hζ, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have h2 : (n : ℂ) / q = m := by
      have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have := mul_left_cancel₀ hpi (by rw [hm]; ring : (2 * Real.pi * I) * ((n : ℂ) / q) =
        (2 * Real.pi * I) * (m : ℂ))
      exact this
    have h3 : (n : ℂ) = q * m := by rw [← h2]; field_simp
    apply hn
    have h4 : ((n : ℤ) : ℂ) = ((q * m : ℤ) : ℂ) := by push_cast; exact h3
    have h5 : (n : ℤ) = q * m := by exact_mod_cast h4
    exact Int.natCast_dvd_natCast.mp ⟨m, h5⟩
  rw [show (∑ j : Fin q, Complex.exp (2 * Real.pi * I * (j * n / q))) =
      ∑ j ∈ Finset.range q, ζ ^ j by
    rw [← Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) q]
    exact Finset.sum_congr rfl fun j _ => hpow j]
  rw [geom_sum_eq hζ1, hζq, sub_self, zero_div]

/-- **Off the residue `0` the upper half fails.** For `q ∤ r`, the `q` equal-weight roots
`v_j = 2e^{iπ(1+8j)/(4q)}` have `Σ_j v_jⁿ = 0` along `n ≡ r (mod q)`, so the paired Li sum is `2q`. -/
theorem not_liUpperThinning_progression_of_not_dvd {q r : ℕ} (hq : 0 < q) (hr : ¬ q ∣ r) :
    ¬ LiUpperThinning (natProgression q r) := by
  intro h
  set θ : Fin q → ℝ := fun j => Real.pi * (1 + 8 * j) / (4 * q) with hθ
  set v : Fin q → ℂ := fun j => 2 * Complex.exp ((θ j : ℂ) * I) with hv
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hnorm : ∀ j, ‖v j‖ = 2 := fun j => by
    rw [hv, norm_mul, Complex.norm_exp_ofReal_mul_I]; norm_num
  have him : ∀ j, (v j).im ≠ 0 := by
    intro j hj
    have hvim : (v j).im = 2 * Real.sin (θ j) := by
      rw [hv, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      norm_num
    rw [hvim] at hj
    have hs : Real.sin (θ j) = 0 := by linarith
    obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hs
    rw [hθ] at hz
    simp only at hz
    have hz' : (z : ℝ) * (4 * q) = 1 + 8 * (j : ℝ) := by
      field_simp at hz
      nlinarith [Real.pi_pos]
    have hzint : z * (4 * q) = 1 + 8 * (j : ℤ) := by exact_mod_cast hz'
    have h3 : (z * (4 * (q : ℤ))) % 2 = 0 := by
      rw [show z * (4 * (q : ℤ)) = 2 * (2 * z * q) by ring]
      exact Int.mul_emod_right 2 _
    rw [hzint] at h3
    omega
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  -- the root sums vanish along the class
  have hsum : ∀ n : ℕ, ¬ q ∣ n → ∑ j, v j ^ n = 0 ∧ ∑ j, (v j)⁻¹ ^ n = 0 := by
    intro n hn
    have hrot := sum_exp_two_pi_mul_div_eq_zero hq hn
    have hsplit : ∀ j : Fin q, v j ^ n = (2 : ℂ) ^ n * Complex.exp ((n : ℂ) *
        (((Real.pi / (4 * q) : ℝ) : ℂ) * I)) *
        Complex.exp (2 * Real.pi * I * (j * n / q)) := by
      intro j
      rw [hv, mul_pow, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
      congr 2
      rw [hθ]
      push_cast
      field_simp
      ring
    constructor
    · rw [Finset.sum_congr rfl fun j _ => hsplit j, ← Finset.mul_sum, hrot, mul_zero]
    · have hBinv : ∀ j : Fin q, (Complex.exp (2 * Real.pi * I * (j * n / q)))⁻¹ =
          (starRingEnd ℂ) (Complex.exp (2 * Real.pi * I * (j * n / q))) := by
        intro j
        rw [← Complex.exp_neg, ← Complex.exp_conj]
        congr 1
        simp only [map_mul, map_div₀, map_natCast, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
        ring
      have hconj : ∀ j : Fin q, (v j)⁻¹ ^ n = (((2 : ℂ) ^ n * Complex.exp ((n : ℂ) *
          (((Real.pi / (4 * q) : ℝ) : ℂ) * I)))⁻¹) *
          (starRingEnd ℂ) (Complex.exp (2 * Real.pi * I * (j * n / q))) := by
        intro j
        rw [inv_pow, hsplit j, mul_inv, hBinv j]
      rw [Finset.sum_congr rfl fun j _ => hconj j, ← Finset.mul_sum, ← map_sum, hrot, map_zero,
        mul_zero]
  have hfreq := h (Fin q) v (fun _ => 1) 2 (fun _ => le_rfl)
    (fun j => by rw [hnorm]; norm_num) (fun j => by rw [hnorm]) (Summable.of_finite)
    him ⟨⟨0, hq⟩, by rw [hnorm]; norm_num⟩ (2 * q)
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨n, hn1, ⟨k, rfl⟩, hlt⟩ := hfreq 1
  have hndvd : ¬ q ∣ q * k + r := by
    intro hd
    exact hr ((Nat.dvd_add_right (dvd_mul_right q k)).mp hd)
  obtain ⟨h1, h2⟩ := hsum _ hndvd
  rw [tsum_fintype] at hlt
  simp only [one_mul] at hlt
  have hval : ∑ j, (liTerm (v j) (q * k + r)).re = 2 * q := by
    rw [← Complex.re_sum]
    simp only [liTerm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, h1, h2, sub_zero]
    simp
    ring
  rw [hval] at hlt
  have hn1' : (1 : ℝ) ≤ ((q * k + r : ℕ) : ℝ) := by exact_mod_cast hn1
  have hsq1 : (1 : ℝ) ≤ ((q * k + r : ℕ) : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hsq1 (by positivity : (0 : ℝ) ≤ 2 * q)
  linarith

/-- **Lower half along progressions.** `qk + r` thins the lower criterion iff `q ∣ r`. -/
theorem liThinning_progression_iff {q r : ℕ} (hq : 0 < q) :
    LiThinning (natProgression q r) ↔ q ∣ r := by
  constructor
  · intro h
    have hrec := isBohrRecurrent_of_liThinning h
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    obtain ⟨n, ⟨k, rfl⟩, -, hclose⟩ := hrec 1 (fun _ => 2 * Real.pi / q) (Real.pi / q)
      (by positivity) 0
    obtain ⟨z, hz⟩ := hclose 0
    have hkey : ((q * k + r : ℕ) : ℝ) * (2 * Real.pi / q) - z * (2 * Real.pi) =
        2 * Real.pi * (((r : ℤ) - q * (z - k) : ℤ) : ℝ) / q := by
      push_cast; field_simp; ring
    rw [hkey, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
      abs_of_pos hq0, div_lt_div_iff_of_pos_right hq0] at hz
    have hint : |(((r : ℤ) - q * (z - k) : ℤ) : ℝ)| < 1 := by
      have := Real.pi_pos
      nlinarith
    have hint' : |((r : ℤ) - q * (z - k))| < 1 := by exact_mod_cast hint
    have h0 : (r : ℤ) - q * (z - k) = 0 := by
      rw [abs_lt] at hint'
      omega
    have : (q : ℤ) ∣ (r : ℤ) := ⟨z - k, by linarith⟩
    exact Int.natCast_dvd_natCast.mp this
  · intro hqr
    exact liThinning_mono (eventually_mem_progression_of_dvd hq hqr) (liThinning_multiples hq)

/-- **Upper half along progressions.** `qk + r` thins the upper criterion iff `q ∣ r` and
`q ≤ 2`. -/
theorem liUpperThinning_progression_iff {q r : ℕ} (hq : 0 < q) :
    LiUpperThinning (natProgression q r) ↔ q ∣ r ∧ q ≤ 2 := by
  constructor
  · intro h
    by_cases hqr : q ∣ r
    · refine ⟨hqr, ?_⟩
      by_contra hq2
      push Not at hq2
      apply not_liUpperThinning_multiples (s := q) (by omega)
      refine liUpperThinning_mono (Eventually.of_forall fun n hn => ?_) h
      obtain ⟨k, rfl⟩ := hn
      exact dvd_add (dvd_mul_right q k) hqr
    · exact absurd h (not_liUpperThinning_progression_of_not_dvd hq hqr)
  · rintro ⟨hqr, hq2⟩
    exact liUpperThinning_mono (eventually_mem_progression_of_dvd hq hqr)
      (liUpperThinning_multiples_of_le_two hq hq2)

/-! ## The case of `ξ` -/

/-- **The upper Li criterion along a Bohr-dense set.** -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_le_of_isBohrDense {A : Set ℕ}
    (hA : IsBohrDense A) :
    RiemannHypothesis ↔
      ∀ᶠ n in atTop, n ∈ A → (xiLiPaired n).re ≤ (n : ℝ) ^ 2 * (xiLiPaired 1).re := by
  constructor
  · intro hRH
    exact Eventually.of_forall fun n _ => re_xiLiPaired_le_sq_mul_one_of_rh hRH n
  · intro h
    by_contra hRH
    obtain ⟨M, hmult, hvnorm, hvM, hsum, hnr, hbad⟩ := xiLi_family_facts
    obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
    have hf := liUpperThinning_of_isBohrDense hA XiDivisorSupport (fun ρ => xiRootV (ρ : ℂ))
      (fun ρ => ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ)) M hmult hvnorm hvM hsum hnr
      ⟨ρ₀, hρ₀⟩ ((xiLiPaired 1).re)
    obtain ⟨n, ⟨hnA, hlt⟩, hle⟩ := (hf.and_eventually h).exists
    rw [← re_xiLiPaired_eq_tsum_mult] at hlt
    have := hle hnA
    linarith

/-- **For `ξ` the upper half thins along every `aℕ` with `a ≤ 89`.** The top Cayley roots have
`|arg| ≤ 7/100`, so their `a`-th powers are never `1`, and the dominant cosine polynomial along `aℕ`
is negative somewhere. Abstractly this fails for every `a ≥ 3` (`not_liUpperThinning_multiples`). -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_mul_le {a : ℕ} (ha : 1 ≤ a) (ha89 : a ≤ 89) :
    RiemannHypothesis ↔
      ∀ᶠ k in atTop, (xiLiPaired (a * k)).re ≤ ((a * k : ℕ) : ℝ) ^ 2 * (xiLiPaired 1).re := by
  constructor
  · intro hRH
    exact Eventually.of_forall fun k => re_xiLiPaired_le_sq_mul_one_of_rh hRH _
  · intro h
    by_contra hRH
    classical
    obtain ⟨M, hmult, hvnorm, hvM, hsum, hnr, hbad⟩ := xiLi_family_facts
    obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
    have hneg : ∀ (D : Finset XiDivisorSupport) (R : ℝ), D.Nonempty → 1 < R →
        (∀ ρ, ρ ∈ D ↔ ‖xiRootV (ρ : ℂ)‖ = R) →
        ∃ n₀ ∈ {n : ℕ | a ∣ n}, ∑ ρ ∈ D,
          ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ((xiRootV (ρ : ℂ) / R) ^ n₀).re < 0 := by
      intro D R hD hR1 hDnorm
      haveI : Nonempty {x // x ∈ D} := ⟨⟨hD.choose, hD.choose_spec⟩⟩
      have hR0 : (0 : ℝ) < R := by linarith
      have hunit : ∀ ρ : {x // x ∈ D}, ‖xiRootV (ρ : ℂ) / R‖ = 1 := fun ρ => by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm ρ).mp ρ.2,
          div_self hR0.ne']
      have hw : ∀ ρ : {x // x ∈ D}, ‖(xiRootV (ρ : ℂ) / R) ^ a‖ = 1 := fun ρ => by
        rw [norm_pow, hunit ρ, one_pow]
      have hw1 : ∀ ρ : {x // x ∈ D}, (xiRootV (ρ : ℂ) / R) ^ a ≠ 1 := by
        intro ρ
        have hone : 1 < ‖xiRootV ((ρ : XiDivisorSupport) : ℂ)‖ := by
          rw [(hDnorm ρ).mp ρ.2]; exact hR1
        have harg : |Complex.arg (xiRootV (ρ : ℂ) / R)| ≤ 7 / 100 := by
          rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.arg_mul_real (inv_pos.mpr hR0)]
          exact abs_arg_xiRootV_le_of_one_lt ρ hone
        have him : (xiRootV (ρ : ℂ) / R).im ≠ 0 := by
          rw [Complex.div_ofReal_im]
          exact div_ne_zero (hnr ρ) hR0.ne'
        exact pow_ne_one_of_abs_arg_le (hunit ρ) him harg ha ha89
      obtain ⟨k, hk⟩ := exists_re_sum_unit_pow_neg (fun ρ : {x // x ∈ D} => (xiRootV (ρ : ℂ) / R) ^ a)
        (fun ρ => ((MeromorphicOn.divisor xi Set.univ) ((ρ : XiDivisorSupport) : ℂ) : ℝ)) hw hw1
        (fun ρ => by linarith [hmult ρ])
      refine ⟨a * k, dvd_mul_right _ _, ?_⟩
      rw [← Finset.sum_coe_sort D]
      simpa [pow_mul] using hk
    have hf := frequently_quadratic_lt_re_tsum_liTerm_of_returns (A := {n : ℕ | a ∣ n})
      (T := {n : ℕ | a ∣ n}) hmult hvnorm hvM hsum hρ₀ hneg
      (fun n₀ hn₀ => bohrReturnsTo_multiples (by omega) hn₀) ((xiLiPaired 1).re)
    have h' : ∀ᶠ n in atTop, n ∈ {n : ℕ | a ∣ n} →
        (xiLiPaired n).re ≤ (n : ℝ) ^ 2 * (xiLiPaired 1).re := by
      obtain ⟨K, hK⟩ := eventually_atTop.mp h
      refine eventually_atTop.mpr ⟨a * K, fun n hn hnA => ?_⟩
      obtain ⟨k, rfl⟩ := hnA
      have hkK : K ≤ k := by
        by_contra hlt
        push Not at hlt
        have : a * k < a * K := Nat.mul_lt_mul_of_pos_left hlt (by omega)
        omega
      exact hK k hkK
    obtain ⟨n, ⟨hnA, hlt⟩, hle⟩ := (hf.and_eventually h').exists
    rw [← re_xiLiPaired_eq_tsum_mult] at hlt
    have := hle hnA
    linarith

end

end RHTower
