import GaloisForLFunctions.RHTower.Sieve.GuthMaynardAffineFejer
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.HTGeometry.LorentzOrderedSums
import GaloisForLFunctions.RHTower.XiWardEdgeMassQuantization

set_option autoImplicit false

/-!
# Dilated Fejér weights and the divisor bound

The Fejér weight `P_K(θ) = |Σ_{a<K} e(aθ)|²` satisfies `P_K ≤ K²` and `P_K(θ) · 4‖θ‖² ≤ 1`
(`‖θ‖` the distance to `ℤ`). Both together give `P_K ≤ 2K² f_{τ}` at scale `τ = M/K` for the
Lorentzian `f_τ(t) = τ²/(τ² + t²)` (`HTGeometry.lorentzF`). For the Fourier transform of the Fejér
majorant one needs, at a frequency `ξ`, the dilated sum `Σ_{n ∼ M₁} P_K(ξ/n)`:

* for `|ξ| ≤ M₁/2` every `ξ/n` lies in `(−1/2, 1/2)`, so `P_K(ξ/n) ≤ 2K² f_{M₁/K}(ξ)`
  (`fejerWeight_div_le_low`);
* for `M₁/2 < |ξ| ≤ Ξ` (`sum_fejerWeight_div_le`): writing `ℓ = round(ξ/n)`, the terms with
  `ℓ = 0` are `≤ 4`, and the others are `≤ 2K² f_{M₁/K}(ξ − s)` with `s = ℓ n ≠ 0`. Each nonzero
  integer `s` arises from at most `d(|s|) ≤ C_ε (3Ξ)^ε` values `n ∣ s`, and a Lorentzian summed
  over a set of integers is `≤ 2 + πτ` (`HTGeometry.sum_lorentz_sparse_le`), so

  `Σ_{n ∼ M₁} P_K(ξ/n) ≤ 12 M₁ + C_ε (3Ξ)^ε (4K² + 2π K M₁)`.

This is the only place where arithmetic enters Guth–Maynard's Lemma 9.2: the number of
factorisations `s = ℓ m₁`.
-/

open MeasureTheory Finset Real

namespace RHTower.GuthMaynard

noncomputable section

open RHTower.Sieve (finitePhaseProgression unitPhaseDistance divisorBoundConst)
open GaloisForLFunctions.HTGeometry (lorentzF lorentzF_nonneg)

/-- The Fejér weight `P_K(θ) = |D_K(θ)|²`. -/
def fejerWeight (K : ℕ) (θ : ℝ) : ℝ :=
  ‖finitePhaseProgression K θ‖ ^ 2

theorem fejerWeight_nonneg (K : ℕ) (θ : ℝ) : 0 ≤ fejerWeight K θ := sq_nonneg _

theorem fejerWeight_le (K : ℕ) (θ : ℝ) : fejerWeight K θ ≤ (K : ℝ) ^ 2 := by
  unfold fejerWeight
  have := RHTower.Sieve.norm_finitePhaseProgression_le_length K θ
  gcongr

/-- `P_K(θ) · 4 ‖θ‖² ≤ 1`, with `‖θ‖ = |θ − round θ|`. -/
theorem fejerWeight_mul_dist_le (K : ℕ) (θ : ℝ) :
    fejerWeight K θ * (4 * |θ - round θ| ^ 2) ≤ 1 := by
  rw [← RHTower.Sieve.unitPhaseDistance_eq_abs_sub_round]
  have hd0 : 0 ≤ unitPhaseDistance θ := norm_nonneg _
  rcases hd0.eq_or_lt with hd | hd
  · rw [← hd]
    norm_num
  · have h := RHTower.Sieve.norm_finitePhaseProgression_le_inv_distance K hd.ne'
    rw [le_div_iff₀ (by positivity)] at h
    have hx0 : 0 ≤ ‖finitePhaseProgression K θ‖ * (2 * unitPhaseDistance θ) := by positivity
    calc fejerWeight K θ * (4 * unitPhaseDistance θ ^ 2)
        = (‖finitePhaseProgression K θ‖ * (2 * unitPhaseDistance θ)) ^ 2 := by
          unfold fejerWeight
          ring
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ hx0 h 2
      _ = 1 := one_pow 2

/-- `f_τ` integrates to `πτ` over the line (from `RHTower.lorentzian_integral`). -/
theorem integral_lorentzF_univ {τ : ℝ} (hτ : 0 < τ) : ∫ u, lorentzF τ u = π * τ := by
  have hfun : (fun u => lorentzF τ u) = fun u => τ / 2 * (2 * τ / (τ ^ 2 + u ^ 2)) := by
    funext u
    have : 0 < τ ^ 2 + u ^ 2 := by positivity
    unfold lorentzF
    field_simp
  rw [hfun, integral_const_mul, RHTower.lorentzian_integral hτ]
  ring

theorem integrable_lorentzF {τ : ℝ} (hτ : 0 < τ) : Integrable (lorentzF τ) := by
  refine ((RHTower.lorentzian_integrable0 hτ).const_mul (τ / 2)).congr
    (Filter.Eventually.of_forall fun u => ?_)
  have : 0 < τ ^ 2 + u ^ 2 := by positivity
  show τ / 2 * (2 * τ / (τ ^ 2 + u ^ 2)) = τ ^ 2 / (τ ^ 2 + u ^ 2)
  field_simp

/-- **Harmonic-mean bound.** `P ≤ K²` and `P t² ≤ M²` give `P ≤ 2K² f_{M/K}(t)`. -/
theorem le_two_mul_lorentzF {P K M t : ℝ} (hPK : P ≤ K ^ 2) (hPt : P * t ^ 2 ≤ M ^ 2)
    (hK : 0 < K) (hM : 0 < M) : P ≤ 2 * K ^ 2 * lorentzF (M / K) t := by
  have hl : lorentzF (M / K) t = M ^ 2 / (M ^ 2 + K ^ 2 * t ^ 2) := by
    unfold lorentzF
    rw [div_pow, div_add' _ _ _ (by positivity), div_div_div_cancel_right₀ (by positivity)]
    ring_nf
  rw [hl, mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hPK (sq_nonneg M),
    mul_le_mul_of_nonneg_left hPt (sq_nonneg K)]

/-- `Σ_{t ∈ S} f_τ(x − t) ≤ 2 + πτ` for a finite set of integers (`sum_lorentz_sparse_le` with
gaps one). -/
theorem sum_lorentzF_int_le {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (S : Finset ℤ) :
    ∑ t ∈ S, lorentzF τ (x - t) ≤ 2 + π * τ := by
  set N : ℕ := S.sup Int.natAbs
  have hsub : S ⊆ (Finset.Icc 0 (2 * N)).image (fun n : ℕ => (n : ℤ) - N) := by
    intro t ht
    have hN : t.natAbs ≤ N := Finset.le_sup (f := Int.natAbs) ht
    refine Finset.mem_image.mpr ⟨(t + N).toNat, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  have hinj : Set.InjOn (fun n : ℕ => (n : ℤ) - N) ↑(Finset.Icc 0 (2 * N)) := fun a _ b _ h => by
    simp only at h
    omega
  have hsparse := GaloisForLFunctions.HTGeometry.sum_lorentz_sparse_le hτ one_pos
    (y := fun n : ℕ => (n : ℝ) - N) (a := 0) (b := 2 * N) (fun n _ _ => by push_cast; linarith) x
  calc ∑ t ∈ S, lorentzF τ (x - t)
      ≤ ∑ t ∈ (Finset.Icc 0 (2 * N)).image (fun n : ℕ => (n : ℤ) - N), lorentzF τ (x - t) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => lorentzF_nonneg _ _
    _ = ∑ n ∈ Finset.Icc 0 (2 * N), lorentzF τ (x - ((n : ℝ) - N)) := by
        rw [Finset.sum_image hinj]
        push_cast
        rfl
    _ ≤ 2 + π * τ / 1 := hsparse
    _ = 2 + π * τ := by rw [div_one]

/-! ### The dilated Fejér sums -/

/-- **Low frequencies.** For `|ξ| ≤ M₁/2` and `n ∼ M₁`: `P_K(ξ/n) ≤ 2K² f_{M₁/K}(ξ)`. -/
theorem fejerWeight_div_le_low (K : ℕ) {M₁ ξ : ℝ} {n : ℕ} (hn : n ∈ dyadicNat M₁)
    (hK : 1 ≤ K) (hξ : |ξ| ≤ M₁ / 2) :
    fejerWeight K (ξ / n) ≤ 2 * (K : ℝ) ^ 2 * lorentzF (M₁ / K) ξ := by
  obtain ⟨hn1, hn2⟩ := mem_dyadicNat.mp hn
  have hM₁ := half_le_of_mem_dyadicNat hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ : |ξ / n| < 1 / 2 := by
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    linarith
  have hround : round (ξ / n) = 0 :=
    round_eq_zero_iff.mpr ⟨by linarith [neg_abs_le (ξ / n)], by linarith [le_abs_self (ξ / n)]⟩
  have hmain := fejerWeight_mul_dist_le K (ξ / n)
  rw [hround, Int.cast_zero, sub_zero, sq_abs, div_pow] at hmain
  refine le_two_mul_lorentzF (fejerWeight_le _ _) ?_ (by exact_mod_cast hK) (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hmain (sq_nonneg (n : ℝ))
  have h2 : fejerWeight K (ξ / n) * (4 * (ξ ^ 2 / (n : ℝ) ^ 2)) * (n : ℝ) ^ 2 =
      4 * (fejerWeight K (ξ / n) * ξ ^ 2) := by
    field_simp
  have h3 : (n : ℝ) ^ 2 ≤ (2 * M₁) ^ 2 := by gcongr
  nlinarith

theorem divisorBoundConst_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ divisorBoundConst ε := by
  have h1 := RHTower.Sieve.card_divisors_le_rpow hε (n := 1) one_ne_zero
  simp only [Nat.divisors_one, Finset.card_singleton, Nat.cast_one, Real.one_rpow,
    mul_one] at h1
  linarith

/-- The divisor bound in the form used here: `d(n) ≤ C_ε X^ε` for `1 ≤ n ≤ X`. -/
theorem card_divisors_le_of_le {ε X : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≠ 0) (hX : (n : ℝ) ≤ X) :
    (n.divisors.card : ℝ) ≤ divisorBoundConst ε * X ^ ε :=
  (RHTower.Sieve.card_divisors_le_rpow hε hn).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hX hε.le)
      (divisorBoundConst_nonneg hε))

/-- **High frequencies.** For `M₁/2 < |ξ| ≤ Ξ`:
`Σ_{n ∼ M₁} P_K(ξ/n) ≤ 12 M₁ + C_ε (3Ξ)^ε (4K² + 2π K M₁)`. -/
theorem sum_fejerWeight_div_le {K : ℕ} (hK : 1 ≤ K) {M₁ ξ Ξ ε : ℝ} (hM₁ : 1 / 2 ≤ M₁)
    (hε : 0 < ε) (hξ1 : M₁ / 2 < |ξ|) (hξ2 : |ξ| ≤ Ξ) :
    ∑ n ∈ dyadicNat M₁, fejerWeight K (ξ / n) ≤
      12 * M₁ + divisorBoundConst ε * (3 * Ξ) ^ ε * (4 * (K : ℝ) ^ 2 + 2 * π * K * M₁) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hM0 : 0 < M₁ := by linarith
  have hΞ0 : 0 < Ξ := by linarith [abs_nonneg ξ]
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℤ, s = fun n : ℕ => round (ξ / (n : ℝ)) * (n : ℤ) := ⟨_, rfl⟩
  have hn0 : ∀ n ∈ dyadicNat M₁, (0 : ℝ) < n := fun n hn => by
    exact_mod_cast one_le_of_mem_dyadicNat hn
  have hsn : ∀ n : ℕ, ((s n : ℤ) : ℝ) = (round (ξ / n) : ℝ) * n := fun n => by
    rw [hs]
    push_cast
    ring
  -- `P(ξ/n) · (ξ − s n)² ≤ M₁²`, from `P(θ) · 4‖θ‖² ≤ 1`
  have hdist : ∀ n ∈ dyadicNat M₁, fejerWeight K (ξ / n) * (ξ - s n) ^ 2 ≤ M₁ ^ 2 := by
    intro n hn
    have hn' := hn0 n hn
    have hn'' : (n : ℝ) ≠ 0 := hn'.ne'
    have h2 := (mem_dyadicNat.mp hn).2
    have hmain := fejerWeight_mul_dist_le K (ξ / n)
    have heq : 4 * |ξ / n - round (ξ / n)| ^ 2 = 4 * (ξ - s n) ^ 2 / (n : ℝ) ^ 2 := by
      rw [sq_abs, hsn]
      field_simp
    rw [heq, mul_div_assoc', div_le_one (by positivity)] at hmain
    have h3 : (n : ℝ) ^ 2 ≤ (2 * M₁) ^ 2 := by gcongr
    nlinarith
  rw [← Finset.sum_filter_add_sum_filter_not (dyadicNat M₁) (fun n : ℕ => round (ξ / (n : ℝ)) = 0)]
  -- `round(ξ/n) = 0`: the weight is at most `4`
  have hfour : ∀ n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0),
      fejerWeight K (ξ / n) ≤ 4 := by
    intro n hn
    obtain ⟨hn, hr⟩ := Finset.mem_filter.mp hn
    have hd := hdist n hn
    rw [hsn, hr, Int.cast_zero, zero_mul, sub_zero] at hd
    have hP0 := fejerWeight_nonneg K (ξ / n)
    have hξ2' : M₁ ^ 2 < 4 * ξ ^ 2 := by
      have : (M₁ / 2) ^ 2 < |ξ| ^ 2 := by gcongr
      rw [sq_abs] at this
      linarith
    by_contra hcon
    have hξpos : 0 < ξ ^ 2 := by nlinarith
    have := mul_lt_mul_of_pos_right (not_le.mp hcon) hξpos
    linarith
  have hzero : ∑ n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0), fejerWeight K (ξ / n) ≤
      12 * M₁ := by
    calc ∑ n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0), fejerWeight K (ξ / n)
        ≤ ∑ _n ∈ (dyadicNat M₁).filter (fun n : ℕ => round (ξ / (n : ℝ)) = 0), (4 : ℝ) :=
          Finset.sum_le_sum hfour
      _ ≤ ∑ _n ∈ dyadicNat M₁, (4 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by norm_num
      _ = (dyadicNat M₁).card * 4 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * M₁ * 4 := by gcongr; exact card_dyadicNat_le_three_mul hM₁
      _ = 12 * M₁ := by ring
  -- `round(ξ/n) ≠ 0`: group by `s = round(ξ/n) · n` and count divisors
  set dmax := divisorBoundConst ε * (3 * Ξ) ^ ε with hdmax
  have hdmax0 : 0 ≤ dmax := mul_nonneg (divisorBoundConst_nonneg hε) (Real.rpow_nonneg (by linarith) _)
  set A := (dyadicNat M₁).filter (fun n : ℕ => ¬ round (ξ / (n : ℝ)) = 0) with hA
  have hAmem : ∀ n ∈ A, n ∈ dyadicNat M₁ ∧ round (ξ / n) ≠ 0 := fun n hn => Finset.mem_filter.mp hn
  have hsbound : ∀ n ∈ A, s n ≠ 0 ∧ |((s n : ℤ) : ℝ)| ≤ 3 * Ξ := by
    intro n hn
    obtain ⟨hn, hr⟩ := hAmem n hn
    have hn' := hn0 n hn
    have h2 := (mem_dyadicNat.mp hn).2
    refine ⟨?_, ?_⟩
    · rw [hs]
      exact mul_ne_zero hr (by exact_mod_cast hn'.ne')
    · have hround := abs_sub_round (ξ / n)
      have h3 : |(s n : ℝ) - ξ| ≤ n / 2 := by
        have : (s n : ℝ) - ξ = -((ξ / n - round (ξ / n)) * n) := by
          rw [hsn]
          field_simp
          ring
        rw [this, abs_neg, abs_mul, abs_of_pos hn']
        nlinarith [abs_nonneg (ξ / n - round (ξ / n))]
      have := abs_sub_abs_le_abs_sub (s n : ℝ) ξ
      linarith
  have hterm : ∀ n ∈ A, fejerWeight K (ξ / n) ≤ 2 * (K : ℝ) ^ 2 * lorentzF (M₁ / K) (ξ - s n) :=
    fun n hn => le_two_mul_lorentzF (fejerWeight_le _ _) (hdist n (hAmem n hn).1) hK0 hM0
  have hfib : ∀ t ∈ A.image s, ((A.filter fun n => s n = t).card : ℝ) ≤ dmax := by
    intro t ht
    obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hs0, hsb⟩ := hsbound n₀ hn₀
    have hsub : A.filter (fun n => s n = s n₀) ⊆ (s n₀).natAbs.divisors := by
      intro n hn
      obtain ⟨-, hns⟩ := Finset.mem_filter.mp hn
      rw [Nat.mem_divisors]
      refine ⟨?_, Int.natAbs_ne_zero.mpr hs0⟩
      rw [← hns, hs]
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      exact Dvd.intro_left _ rfl
    refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (card_divisors_le_of_le hε (Int.natAbs_ne_zero.mpr hs0) ?_)
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hsb
  have hnonzero : ∑ n ∈ A, fejerWeight K (ξ / n) ≤ dmax * (4 * (K : ℝ) ^ 2 + 2 * π * K * M₁) := by
    calc ∑ n ∈ A, fejerWeight K (ξ / n)
        ≤ ∑ n ∈ A, 2 * (K : ℝ) ^ 2 * lorentzF (M₁ / K) (ξ - s n) := Finset.sum_le_sum hterm
      _ = ∑ t ∈ A.image s, (A.filter fun n => s n = t).card •
            (2 * (K : ℝ) ^ 2 * lorentzF (M₁ / K) (ξ - t)) :=
          Finset.sum_comp (fun t : ℤ => 2 * (K : ℝ) ^ 2 * lorentzF (M₁ / K) (ξ - t)) s
      _ ≤ ∑ t ∈ A.image s, dmax * (2 * (K : ℝ) ^ 2 * lorentzF (M₁ / K) (ξ - t)) := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hfib t ht)
            (mul_nonneg (by positivity) (lorentzF_nonneg _ _))
      _ = dmax * (2 * (K : ℝ) ^ 2) * ∑ t ∈ A.image s, lorentzF (M₁ / K) (ξ - t) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ ≤ dmax * (2 * (K : ℝ) ^ 2) * (2 + π * (M₁ / K)) :=
          mul_le_mul_of_nonneg_left (sum_lorentzF_int_le (div_pos hM0 hK0) ξ _)
            (mul_nonneg hdmax0 (by positivity))
      _ = dmax * (4 * (K : ℝ) ^ 2 + 2 * π * K * M₁) := by
          field_simp
          ring
  linarith

end

end RHTower.GuthMaynard
